"""Run all 4 computational experiments for Paper 08 and emit certified exact-Q artifacts.

Outputs:
  results/certificates/<cert_id>.cert.json       (13 exact-Q NORMAL-CONE-SOS-CERT-1.0 files across all 4 sound modes)
  results/exp1_certified_atlas.json
  results/exp2_octagon_geometry_and_collapse.json
  results/exp3_npa_hierarchy_phase_map.json
  results/exp4_visibility_optimality_landscape.json
"""

from __future__ import annotations

import json
import sys
import time
import warnings
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

import cvxpy as cp
import numpy as np
from scipy.optimize import linprog, minimize

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src import (
    BELL_WORDS,
    LOCAL_VERTICES,
    OPS_1AB,
    OPS_2,
    RationalExtremePoint,
    add_poly,
    bell_functional_poly,
    bell_vector_at,
    build_annihilators_1ab,
    build_annihilators_npa2,
    build_bob_tilted_sos,
    build_certificate_from_witnesses,
    build_npa_word_map,
    build_rational_extreme_point,
    build_tilted_chsh_sos,
    canonical_fraction_str,
    compute_octagon_vertices,
    compute_visibility_dual_weights,
    dag_poly,
    exact_ldlt_pd,
    exact_ldlt_psd,
    mul_poly,
    verify_normal_cone_certificate_exact,
)
from src.nc_sos import NCPoly, Word, poly_I, scale_poly

_WORD_MAP_1AB = build_npa_word_map(OPS_1AB)
_WORD_MAP_2 = build_npa_word_map(OPS_2)


def solve_npa_primal_sdp(
    ops: Sequence[Word],
    word_map: Dict[Word, List[Tuple[int, int]]],
    b_vec_f: Sequence[float],
) -> Tuple[float, np.ndarray]:
    """Solve the primal NPA moment-matrix SDP maximize B . gamma(Gamma) s.t. Gamma >= 0, Gamma_00 = 1."""
    n = len(ops)
    G = cp.Variable((n, n), symmetric=True)
    cons = [G >> 0, G[0, 0] == 1.0]
    for w, cells in word_map.items():
        if w == ((), ()):
            for i, j in cells:
                if (i, j) != (0, 0):
                    cons.append(G[i, j] == 1.0)
        else:
            r0, c0 = cells[0]
            for i, j in cells[1:]:
                if i <= j:
                    cons.append(G[i, j] == G[r0, c0])
    obj_expr = 0
    for idx, bw in enumerate(BELL_WORDS):
        r0, c0 = word_map[bw][0]
        obj_expr += b_vec_f[idx] * G[r0, c0]
    prob = cp.Problem(cp.Maximize(obj_expr), cons)
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        prob.solve(solver=cp.CLARABEL, tol_gap_abs=1e-11, tol_gap_rel=1e-11, tol_feas=1e-11)
    return float(prob.value), np.asarray(G.value, dtype=float)


def build_exact_q_moment_gap(
    ep: RationalExtremePoint,
    eta: Fraction,
    zeta: Fraction,
    ops: Sequence[Word],
    word_map: Dict[Word, List[Tuple[int, int]]],
) -> Tuple[List[List[Fraction]], List[Fraction], Fraction]:
    """Construct an exact-Q strictly PD NPA moment matrix Gamma = L D L^T with B . gamma(Gamma) > beta_Q."""
    b_vec, beta_q, _ = bell_vector_at(ep, eta, zeta)
    b_vec_f = [float(x) for x in b_vec]
    val_num, G_num = solve_npa_primal_sdp(ops, word_map, b_vec_f)
    if val_num <= float(beta_q) + 1e-7:
        raise RuntimeError(f"No positive NPA gap at (eta={eta}, zeta={zeta}): val={val_num}, bq={float(beta_q)}")

    n = len(ops)
    for denom in (10000, 100000, 1000000):
        for eps in (1e-4, 5e-4, 1e-3, 5e-3, 1e-2):
            Gm = (1.0 - eps) * G_num + eps * np.eye(n)
            word_vals: Dict[Word, Fraction] = {}
            for w, cells in word_map.items():
                if w == ((), ()):
                    word_vals[w] = Fraction(1, 1)
                else:
                    avg = float(np.mean([Gm[i, j] for i, j in cells]))
                    word_vals[w] = Fraction(int(round(avg * denom)), denom)
            M = [[Fraction(0, 1) for _ in range(n)] for _ in range(n)]
            for w, cells in word_map.items():
                for i, j in cells:
                    M[i][j] = word_vals[w]
            mval = sum(b_vec[idx] * word_vals[bw] for idx, bw in enumerate(BELL_WORDS))
            if mval > beta_q:
                L, D = exact_ldlt_pd(M)
                if L is not None and D is not None:
                    return L, D, mval
    raise RuntimeError(f"Failed to round exact-Q PD moment matrix at (eta={eta}, zeta={zeta})")


def build_exact_q_sos_via_rref(
    ep: RationalExtremePoint,
    eta: Fraction,
    zeta: Fraction,
    Ns: Sequence[NCPoly],
    denom: int = 10000,
) -> List[Tuple[Fraction, NCPoly]]:
    """Construct an exact-Q SOS decomposition sum_j w_j P_j^dag P_j == beta_Q*I - B
    via exact rational RREF projection of Clarabel's max-min-eigenvalue Gram matrix.
    """
    n = len(Ns)
    basis_polys: List[NCPoly] = []
    idx_pairs: List[Tuple[int, int]] = []
    for i in range(n):
        for j in range(i, n):
            pij = mul_poly(dag_poly(Ns[i]), Ns[j])
            if i != j:
                pij = add_poly(pij, mul_poly(dag_poly(Ns[j]), Ns[i]))
            basis_polys.append(pij)
            idx_pairs.append((i, j))

    b_vec, beta_q, _ = bell_vector_at(ep, eta, zeta)
    T = add_poly(scale_poly(poly_I(), beta_q), bell_functional_poly(b_vec), Fraction(-1, 1))
    words = sorted(set(T.keys()).union(*(p.keys() for p in basis_polys)))

    m_rows = len(words)
    n_vars = len(idx_pairs)
    M = [
        [basis_polys[c].get(words[r], Fraction(0, 1)) for c in range(n_vars)]
        + [T.get(words[r], Fraction(0, 1))]
        for r in range(m_rows)
    ]
    r = 0
    pivs: List[Tuple[int, int]] = []
    for c in range(n_vars):
        piv = next((i for i in range(r, m_rows) if M[i][c] != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = Fraction(1, 1) / M[r][c]
        M[r] = [x * inv for x in M[r]]
        for i in range(m_rows):
            if i != r and M[i][c] != 0:
                fac = M[i][c]
                M[i] = [M[i][j] - fac * M[r][j] for j in range(n_vars + 1)]
        pivs.append((r, c))
        r += 1
    for i in range(r, m_rows):
        if M[i][n_vars] != 0:
            raise RuntimeError(f"Linear system inconsistent at (eta={eta}, zeta={zeta})")

    piv_cols = {c for _, c in pivs}
    free_cols = [c for c in range(n_vars) if c not in piv_cols]

    z = cp.Variable(len(free_cols))
    t = cp.Variable()
    x_expr: List[Any] = [None] * n_vars
    for idx_f, fc in enumerate(free_cols):
        x_expr[fc] = z[idx_f]
    for rr, pc in pivs:
        expr: Any = float(M[rr][n_vars])
        for idx_f, fc in enumerate(free_cols):
            if M[rr][fc] != 0:
                expr = expr - float(M[rr][fc]) * z[idx_f]
        x_expr[pc] = expr
    G_rows: List[List[Any]] = [[None] * n for _ in range(n)]
    for k_idx, (i, j) in enumerate(idx_pairs):
        G_rows[i][j] = x_expr[k_idx]
        G_rows[j][i] = x_expr[k_idx]
    G_mat = cp.bmat(G_rows)
    prob = cp.Problem(cp.Maximize(t), [G_mat >> t * np.eye(n), t <= 1.0])
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        prob.solve(solver=cp.CLARABEL, tol_gap_abs=1e-11, tol_gap_rel=1e-11, tol_feas=1e-11)
    if prob.value is None or prob.value <= 0:
        raise RuntimeError(f"SOS infeasible at (eta={eta}, zeta={zeta}): lmin={prob.value}")

    for d_try in (denom, denom * 10, denom * 100):
        z_q = [Fraction(int(round(float(zv) * d_try)), d_try) for zv in z.value]
        x_q = [Fraction(0, 1)] * n_vars
        for idx_f, fc in enumerate(free_cols):
            x_q[fc] = z_q[idx_f]
        for rr, pc in pivs:
            val = M[rr][n_vars]
            for idx_f, fc in enumerate(free_cols):
                val -= M[rr][fc] * z_q[idx_f]
            x_q[pc] = val
        G_q = [[Fraction(0, 1) for _ in range(n)] for _ in range(n)]
        for k_idx, (i, j) in enumerate(idx_pairs):
            G_q[i][j] = x_q[k_idx]
            G_q[j][i] = x_q[k_idx]
        L, D = exact_ldlt_psd(G_q)
        if L is not None and D is not None:
            squares: List[Tuple[Fraction, NCPoly]] = []
            for j in range(n):
                if D[j] == 0:
                    continue
                Pj: NCPoly = {}
                for i in range(j, n):
                    if L[i][j] != 0:
                        Pj = add_poly(Pj, Ns[i], L[i][j])
                if Pj:
                    squares.append((D[j], Pj))
            return squares
    raise RuntimeError(f"Failed exact-Q LDL^T SOS rounding at (eta={eta}, zeta={zeta})")


def exact_qubit_max_check(b_vec: Tuple[Fraction, ...], beta_q: Fraction) -> float:
    """Independent 2-qubit Jordan-block numerical check of max eigenvalue over (phi_A, phi_B)."""
    B = [float(x) for x in b_vec]
    Z = np.array([[1.0, 0.0], [0.0, -1.0]])
    X = np.array([[0.0, 1.0], [1.0, 0.0]])
    I2 = np.eye(2)
    phis = np.linspace(0.0, np.pi, 61)
    best_val = -1e9
    best_ab = (0.0, 0.0)
    for pa in phis:
        A1m = np.cos(pa) * Z + np.sin(pa) * X
        for pb in phis:
            B1m = np.cos(pb) * Z + np.sin(pb) * X
            H = (
                B[0] * np.kron(Z, I2)
                + B[1] * np.kron(A1m, I2)
                + B[2] * np.kron(I2, Z)
                + B[3] * np.kron(I2, B1m)
                + B[4] * np.kron(Z, Z)
                + B[5] * np.kron(Z, B1m)
                + B[6] * np.kron(A1m, Z)
                + B[7] * np.kron(A1m, B1m)
            )
            e = float(np.linalg.eigvalsh(H)[-1])
            if e > best_val:
                best_val = e
                best_ab = (pa, pb)

    def neg_max_eig(ab: np.ndarray) -> float:
        pa, pb = float(ab[0]), float(ab[1])
        A1m = np.cos(pa) * Z + np.sin(pa) * X
        B1m = np.cos(pb) * Z + np.sin(pb) * X
        H = (
            B[0] * np.kron(Z, I2)
            + B[1] * np.kron(A1m, I2)
            + B[2] * np.kron(I2, Z)
            + B[3] * np.kron(I2, B1m)
            + B[4] * np.kron(Z, Z)
            + B[5] * np.kron(Z, B1m)
            + B[6] * np.kron(A1m, Z)
            + B[7] * np.kron(A1m, B1m)
        )
        return -float(np.linalg.eigvalsh(H)[-1])

    res = minimize(neg_max_eig, np.array(best_ab), method="Nelder-Mead", options={"xatol": 1e-12, "fatol": 1e-12})
    refined = -float(res.fun)
    return abs(refined - float(beta_q))


def run_exp1_certified_atlas(cert_dir: Path) -> Dict[str, Any]:
    """Build & independently replay 13 exact-Q certificates covering all 4 sound modes & all 4 NPA tiers."""
    cert_dir.mkdir(parents=True, exist_ok=True)
    for old in cert_dir.glob("*.cert.json"):
        old.unlink()

    ep2 = build_rational_extreme_point(Fraction(2, 1))
    ep32 = build_rational_extreme_point(Fraction(3, 2))
    ep54 = build_rational_extreme_point(Fraction(5, 4))
    Ns1_2 = build_annihilators_1ab(ep2)
    Ns2_2 = build_annihilators_npa2(ep2)
    verts2 = compute_octagon_vertices(ep2)
    # V1=(7/10, 0), V2=(21/65, 49/65), V3=(7/59, 49/59), V5=(-14/15, 0)
    V1, V2, V5 = verts2[0], verts2[1], verts2[4]

    built_specs: List[Tuple[str, Fraction, Fraction, Fraction, str, Dict[str, Any]]] = [
        # Tier 2a: exact 2-square SOS on S_4-subspace core
        ("k2_alice_tilted", Fraction(2, 1), Fraction(0, 1), Fraction(0, 1), "level_1ab_sos_exact",
         {"sos_squares": build_tilted_chsh_sos(ep2)}),
        ("k2_bob_tilted", Fraction(2, 1), ep2.eta_s4_min, Fraction(0, 1), "level_1ab_sos_exact",
         {"sos_squares": build_bob_tilted_sos(ep2)}),
        ("k3_2_alice_tilted", Fraction(3, 2), Fraction(0, 1), Fraction(0, 1), "level_1ab_sos_exact",
         {"sos_squares": build_tilted_chsh_sos(ep32)}),
        ("k5_4_alice_tilted", Fraction(5, 4), Fraction(0, 1), Fraction(0, 1), "level_1ab_sos_exact",
         {"sos_squares": build_tilted_chsh_sos(ep54)}),
        # Tier 2b: exact 5-square Level-(1+AB) SOS across the 2D spectrahedral interior
        ("k2_1ab_pos_eta", Fraction(2, 1), Fraction(1, 2), Fraction(0, 1), "level_1ab_sos_exact",
         {"sos_squares": build_exact_q_sos_via_rref(ep2, Fraction(1, 2), Fraction(0, 1), Ns1_2, denom=1000)}),
        ("k2_1ab_zeta_pos", Fraction(2, 1), Fraction(0, 1), Fraction(1, 2), "level_1ab_sos_exact",
         {"sos_squares": build_exact_q_sos_via_rref(ep2, Fraction(0, 1), Fraction(1, 2), Ns1_2, denom=1000)}),
        ("k2_1ab_diag", Fraction(2, 1), Fraction(1, 5), Fraction(1, 5), "level_1ab_sos_exact",
         {"sos_squares": build_exact_q_sos_via_rref(ep2, Fraction(1, 5), Fraction(1, 5), Ns1_2, denom=1000)}),
        # Tier 3: Dual-certified strict separation (9x9 PD 1+AB moment gap AND 9-square NPA-2 SOS!)
        ("k2_tier3_pos_eta", Fraction(2, 1), Fraction(13, 20), Fraction(0, 1), "level_2_tight_1ab_gap",
         {
             "moment_ldlt": build_exact_q_moment_gap(ep2, Fraction(13, 20), Fraction(0, 1), OPS_1AB, _WORD_MAP_1AB),
             "sos_squares": build_exact_q_sos_via_rref(ep2, Fraction(13, 20), Fraction(0, 1), Ns2_2, denom=10000),
         }),
        ("k2_tier3_neg_eta", Fraction(2, 1), Fraction(-9, 10), Fraction(0, 1), "level_2_tight_1ab_gap",
         {
             "moment_ldlt": build_exact_q_moment_gap(ep2, Fraction(-9, 10), Fraction(0, 1), OPS_1AB, _WORD_MAP_1AB),
             "sos_squares": build_exact_q_sos_via_rref(ep2, Fraction(-9, 10), Fraction(0, 1), Ns2_2, denom=10000),
         }),
        ("k2_tier3_zeta_pos", Fraction(2, 1), Fraction(0, 1), Fraction(7, 10), "level_2_tight_1ab_gap",
         {
             "moment_ldlt": build_exact_q_moment_gap(ep2, Fraction(0, 1), Fraction(7, 10), OPS_1AB, _WORD_MAP_1AB),
             "sos_squares": build_exact_q_sos_via_rref(ep2, Fraction(0, 1), Fraction(7, 10), Ns2_2, denom=10000),
         }),
        # Tier 3 boundary apex V1: 9x9 PD 1+AB moment gap (where NPA-2 is numerically tight!)
        ("k2_tier3_vertex_V1", Fraction(2, 1), V1[0], V1[1], "level_1ab_moment_gap",
         {"moment_ldlt": build_exact_q_moment_gap(ep2, V1[0], V1[1], OPS_1AB, _WORD_MAP_1AB)}),
        # Tier 4: Strict NPA-2 gap at extreme octagon vertices V2 and V5 (13x13 PD NPA-2 moment matrix!)
        ("k2_tier4_vertex_V2", Fraction(2, 1), V2[0], V2[1], "level_2_moment_gap",
         {"moment_ldlt": build_exact_q_moment_gap(ep2, V2[0], V2[1], OPS_2, _WORD_MAP_2)}),
        ("k2_tier4_vertex_V5", Fraction(2, 1), V5[0], V5[1], "level_2_moment_gap",
         {"moment_ldlt": build_exact_q_moment_gap(ep2, V5[0], V5[1], OPS_2, _WORD_MAP_2)}),
    ]

    rows: List[Dict[str, Any]] = []
    max_q_err = 0.0
    for cid, k, eta, zeta, mode, kwargs in built_specs:
        cert = build_certificate_from_witnesses(cid, k, eta, zeta, mode, **kwargs)
        cpath = cert_dir / f"{cid}.cert.json"
        cpath.write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")

        t0 = time.perf_counter()
        loaded = json.loads(cpath.read_text(encoding="utf-8"))
        ver = verify_normal_cone_certificate_exact(loaded)
        v_ms = (time.perf_counter() - t0) * 1000.0

        ep = build_rational_extreme_point(k)
        b_vec, beta_q, beta_loc = bell_vector_at(ep, eta, zeta)
        q_err = exact_qubit_max_check(b_vec, beta_q)
        max_q_err = max(max_q_err, q_err)
        if q_err > 1e-7:
            raise RuntimeError(f"2-qubit max discrepancy on {cid}: {q_err}")

        gap_str: Optional[str] = None
        if mode in ("level_1ab_moment_gap", "level_2_moment_gap"):
            gap_str = cert["certificate_payload"]["npa_gap"]
        elif mode == "level_2_tight_1ab_gap":
            gap_str = cert["certificate_payload"]["level_1ab_moment_gap"]["npa_gap"]

        num_sq: Optional[int] = None
        if mode == "level_1ab_sos_exact":
            num_sq = cert["certificate_payload"]["num_squares"]
        elif mode == "level_2_tight_1ab_gap":
            num_sq = cert["certificate_payload"]["level_2_sos_exact"]["num_squares"]

        rows.append(
            {
                "cert_id": cid,
                "k": canonical_fraction_str(k),
                "alpha": canonical_fraction_str(ep.alpha),
                "beta": canonical_fraction_str(ep.beta),
                "eta": canonical_fraction_str(eta),
                "zeta": canonical_fraction_str(zeta),
                "beta_Q": canonical_fraction_str(beta_q),
                "beta_loc": canonical_fraction_str(beta_loc),
                "visibility_ratio": canonical_fraction_str(beta_loc / beta_q),
                "visibility_ratio_float": float(beta_loc / beta_q),
                "mode": ver["mode"],
                "num_squares": num_sq,
                "certified_npa_gap": gap_str,
                "certified_npa_gap_float": float(Fraction(gap_str)) if gap_str is not None else 0.0,
                "qubit_crosscheck_err": q_err,
                "verify_ms": round(v_ms, 3),
                "verified": True,
            }
        )

    return {
        "experiment": "exp1_certified_atlas",
        "num_certificates": len(rows),
        "all_verified": all(r["verified"] for r in rows),
        "max_qubit_crosscheck_err": max_q_err,
        "certificates": rows,
    }


def _polygon_area_exact(verts: List[Tuple[Fraction, Fraction]]) -> Fraction:
    n = len(verts)
    acc = Fraction(0, 1)
    for i in range(n):
        x1, y1 = verts[i]
        x2, y2 = verts[(i + 1) % n]
        acc += x1 * y2 - x2 * y1
    return abs(acc) / 2


def _bisect_npa_ray(
    ep: RationalExtremePoint,
    d_eta: float,
    d_zeta: float,
    r_max: float,
    ops: Sequence[Word],
    word_map: Dict[Word, List[Tuple[int, int]]],
    steps: int = 12,
) -> float:
    """Binary search along ray r*(d_eta, d_zeta) for tight NPA boundary (gap <= 1e-6)."""
    vI = [float(x) for x in ep.v_I]
    vS = [float(x) for x in ep.v_S]
    vD = [float(x) for x in ep.v_D]
    bf = float(ep.beta)
    abf4 = float(ep.alpha * ep.beta / 4)

    def gap_at(r: float) -> float:
        et, ze = r * d_eta, r * d_zeta
        bv = [vI[i] + et * vS[i] + ze * vD[i] for i in range(8)]
        bq = bf + abf4 * et
        val, _ = solve_npa_primal_sdp(ops, word_map, bv)
        return val - bq

    if gap_at(r_max) <= 1e-6:
        return r_max
    lo, hi = 0.0, r_max
    for _ in range(steps):
        mid = 0.5 * (lo + hi)
        if gap_at(mid) <= 1e-6:
            lo = mid
        else:
            hi = mid
    return lo


def run_exp2_octagon_geometry() -> Dict[str, Any]:
    """Exact normal-cone polygon combinatorics across the Tribonacci transition + symmetric-axis spans."""
    # Exact Tribonacci constant k_trib (unique real root of k^3 - k^2 - k - 1 = 0)
    roots = np.roots([1.0, -1.0, -1.0, -1.0])
    k_trib = float(np.real(next(r for r in roots if abs(np.imag(r)) < 1e-12)))
    alpha_trib = 2.0 * (1.0 + 2.0 * k_trib - k_trib * k_trib) / (k_trib * k_trib + 2.0 * k_trib - 1.0)

    ks = [Fraction(11, 5), Fraction(2, 1), Fraction(7, 4), Fraction(3, 2), Fraction(5, 4)]
    records: List[Dict[str, Any]] = []
    for k in ks:
        ep = build_rational_extreme_point(k)
        verts = compute_octagon_vertices(ep)
        area = _polygon_area_exact(verts)
        eta_lo = Fraction(-1000, 1)
        eta_hi = Fraction(1000, 1)
        zeta_hi = Fraction(1000, 1)
        for L in LOCAL_VERTICES:
            c0 = sum(ep.v_I[i] * (L[i] - ep.p_star[i]) for i in range(8))
            c1 = sum(ep.v_S[i] * (L[i] - ep.p_star[i]) for i in range(8))
            c2 = sum(ep.v_D[i] * (L[i] - ep.p_star[i]) for i in range(8))
            if c1 > 0:
                eta_hi = min(eta_hi, -c0 / c1)
            elif c1 < 0:
                eta_lo = max(eta_lo, -c0 / c1)
            if c2 > 0:
                zeta_hi = min(zeta_hi, -c0 / c2)

        # True Level-(1+AB) symmetric-axis endpoints via Clarabel bisection
        eta_1ab_pos = _bisect_npa_ray(ep, 1.0, 0.0, float(eta_hi), OPS_1AB, _WORD_MAP_1AB, steps=12)
        eta_1ab_neg = -_bisect_npa_ray(ep, -1.0, 0.0, float(-eta_lo), OPS_1AB, _WORD_MAP_1AB, steps=12)

        s4_len = -ep.eta_s4_min
        sym_span = eta_hi - eta_lo

        records.append(
            {
                "k": canonical_fraction_str(k),
                "alpha": canonical_fraction_str(ep.alpha),
                "alpha_float": float(ep.alpha),
                "beta": canonical_fraction_str(ep.beta),
                "beta_float": float(ep.beta),
                "p_star": [canonical_fraction_str(x) for x in ep.p_star],
                "num_polygon_vertices": len(verts),
                "polygon_vertices": [
                    [canonical_fraction_str(x), canonical_fraction_str(y)] for x, y in verts
                ],
                "polygon_area_exact": canonical_fraction_str(area),
                "polygon_area_float": float(area),
                "eta_loc_min": canonical_fraction_str(eta_lo),
                "eta_loc_max": canonical_fraction_str(eta_hi),
                "zeta_loc_max": canonical_fraction_str(zeta_hi),
                "eta_s4_min": canonical_fraction_str(ep.eta_s4_min),
                "eta_s4_max": "0",
                "s4_segment_fraction_of_eta_axis": float(s4_len / sym_span),
                "eta_1ab_full_min_approx": round(eta_1ab_neg, 5),
                "eta_1ab_full_max_approx": round(eta_1ab_pos, 5),
                "full_1ab_fraction_of_eta_axis": round((eta_1ab_pos - eta_1ab_neg) / float(sym_span), 5),
                "optimal_visibility_ratio": canonical_fraction_str((2 + ep.alpha) / ep.beta),
                "optimal_visibility_float": float((2 + ep.alpha) / ep.beta),
            }
        )

    return {
        "experiment": "exp2_octagon_geometry_and_collapse",
        "num_extreme_points": len(records),
        "vertex_counts_by_k": {r["k"]: r["num_polygon_vertices"] for r in records},
        "tribonacci_transition_k_approx": k_trib,
        "tribonacci_transition_alpha_approx": alpha_trib,
        "records": records,
    }


def _ray_polygon_limit(ep: RationalExtremePoint, d_eta: float, d_zeta: float) -> float:
    r_max = 1e9
    for L in LOCAL_VERTICES:
        c0 = float(sum(ep.v_I[i] * (L[i] - ep.p_star[i]) for i in range(8)))
        c1 = float(sum(ep.v_S[i] * (L[i] - ep.p_star[i]) for i in range(8)))
        c2 = float(sum(ep.v_D[i] * (L[i] - ep.p_star[i]) for i in range(8)))
        slope = c1 * d_eta + c2 * d_zeta
        if slope > 1e-14:
            r_max = min(r_max, -c0 / slope)
    return r_max


def run_exp3_npa_hierarchy_phase_map() -> Dict[str, Any]:
    """Quantify the strict 4-tier NPA hierarchy (NPA-1 < NPA-(1+AB) < NPA-2 < N_Q(p*(2)))
    via Clarabel primal SDPs + radial spectrahedral boundary contours.
    """
    ep = build_rational_extreme_point(Fraction(2, 1))
    verts = compute_octagon_vertices(ep)
    probes = [
        ("alice_tilted_origin", Fraction(0, 1), Fraction(0, 1)),
        ("bob_tilted_s4_edge", ep.eta_s4_min, Fraction(0, 1)),
        ("pos_eta_1_2", Fraction(1, 2), Fraction(0, 1)),
        ("neg_eta_4_5", Fraction(-4, 5), Fraction(0, 1)),
        ("zeta_1_2", Fraction(0, 1), Fraction(1, 2)),
        ("diag_1_5", Fraction(1, 5), Fraction(1, 5)),
        ("tier3_pos_eta_13_20", Fraction(13, 20), Fraction(0, 1)),
        ("tier3_neg_eta_9_10", Fraction(-9, 10), Fraction(0, 1)),
        ("tier3_zeta_7_10", Fraction(0, 1), Fraction(7, 10)),
        ("zeta_boundary_7_9", Fraction(0, 1), Fraction(7, 9)),
    ]
    for idx, (vx, vy) in enumerate(verts):
        probes.append((f"octagon_V{idx + 1}", vx, vy))

    results: List[Dict[str, Any]] = []
    for label, et, ze in probes:
        b_vec, beta_q, _ = bell_vector_at(ep, et, ze)
        b_vec_f = [float(x) for x in b_vec]
        bq_f = float(beta_q)
        v1, _ = solve_npa_primal_sdp(OPS_1AB, _WORD_MAP_1AB, b_vec_f)
        v2, _ = solve_npa_primal_sdp(OPS_2, _WORD_MAP_2, b_vec_f)
        g1 = max(0.0, v1 - bq_f)
        g2 = max(0.0, v2 - bq_f)
        t1 = g1 <= 1e-6
        t2 = g2 <= 1e-6
        in_s4 = (ze == 0) and (ep.eta_s4_min <= et <= 0)
        tier = "Tier2_1AB_tight" if t1 else ("Tier3_NPA2_only" if t2 else "Tier4_NPA2_gap")
        results.append(
            {
                "label": label,
                "eta": canonical_fraction_str(et),
                "zeta": canonical_fraction_str(ze),
                "eta_float": float(et),
                "zeta_float": float(ze),
                "in_s4_core": in_s4,
                "level_1_feasible": False,
                "npa_1ab_gap": g1,
                "npa_1ab_tight": t1,
                "npa_2_gap": g2,
                "npa_2_tight": t2,
                "tier": tier,
            }
        )

    # Radial boundary contours of N_SOS^(1+AB)(p*(2)) and N_SOS^(2)(p*(2)) across 36 angles (18 symmetric + mirror)
    n_half = 19  # 0 to pi inclusive
    angles = np.linspace(0.0, np.pi, n_half)
    c1_top: List[Tuple[float, float]] = []
    c2_top: List[Tuple[float, float]] = []
    for ang in angles:
        dx, dy = float(np.cos(ang)), float(np.sin(ang))
        rmax = _ray_polygon_limit(ep, dx, dy)
        r1 = _bisect_npa_ray(ep, dx, dy, rmax, OPS_1AB, _WORD_MAP_1AB, steps=11)
        r2 = _bisect_npa_ray(ep, dx, dy, rmax, OPS_2, _WORD_MAP_2, steps=11)
        c1_top.append((round(r1 * dx, 5), round(r1 * dy, 5)))
        c2_top.append((round(r2 * dx, 5), round(r2 * dy, 5)))
    contour_1ab = c1_top + [(x, -y) for x, y in reversed(c1_top[1:-1])]
    contour_npa2 = c2_top + [(x, -y) for x, y in reversed(c2_top[1:-1])]

    def poly_area_f(pts: List[Tuple[float, float]]) -> float:
        acc = 0.0
        n = len(pts)
        for i in range(n):
            x1, y1 = pts[i]
            x2, y2 = pts[(i + 1) % n]
            acc += x1 * y2 - x2 * y1
        return abs(acc) * 0.5

    area_oct = float(_polygon_area_exact(verts))
    area_1ab = poly_area_f(contour_1ab)
    area_npa2 = poly_area_f(contour_npa2)

    return {
        "experiment": "exp3_npa_hierarchy_phase_map",
        "k": "2",
        "alpha": canonical_fraction_str(ep.alpha),
        "beta": canonical_fraction_str(ep.beta),
        "num_probes": len(results),
        "area_octagon": round(area_oct, 5),
        "area_1ab_spectrahedron_approx": round(area_1ab, 5),
        "area_npa2_spectrahedron_approx": round(area_npa2, 5),
        "area_fraction_1ab": round(area_1ab / area_oct, 5),
        "area_fraction_npa2": round(area_npa2 / area_oct, 5),
        "contour_1ab": [[x, y] for x, y in contour_1ab],
        "contour_npa2": [[x, y] for x, y in contour_npa2],
        "probes": results,
    }


def run_exp4_visibility_optimality() -> Dict[str, Any]:
    """Verify Theorem 3.4 globally across 5 rational k values (LP + exact 4-vertex dual + 2D grid)."""
    ks = [Fraction(11, 5), Fraction(2, 1), Fraction(7, 4), Fraction(3, 2), Fraction(5, 4)]
    lp_checks: List[Dict[str, Any]] = []
    for k in ks:
        ep = build_rational_extreme_point(k)
        dual = compute_visibility_dual_weights(ep)
        opt_vis = (2 + ep.alpha) / ep.beta

        a_f, b_f = float(ep.alpha), float(ep.beta)
        vI = [float(x) for x in ep.v_I]
        vS = [float(x) for x in ep.v_S]
        vD = [float(x) for x in ep.v_D]
        A_ub = [
            [
                sum(vI[i] * L[i] for i in range(8)),
                sum(vS[i] * L[i] for i in range(8)),
                sum(vD[i] * L[i] for i in range(8)),
                -1.0,
            ]
            for L in LOCAL_VERTICES
        ]
        res = linprog(
            [0.0, 0.0, 0.0, 1.0],
            A_ub=A_ub,
            b_ub=[0.0] * 16,
            A_eq=[[b_f, a_f * b_f / 4.0, 0.0, 0.0]],
            b_eq=[1.0],
            bounds=[(0, None), (None, None), (None, None), (None, None)],
            method="highs",
        )
        y0, y1, y2, t_lp = res.x
        lp_checks.append(
            {
                "k": canonical_fraction_str(k),
                "alpha": canonical_fraction_str(ep.alpha),
                "beta": canonical_fraction_str(ep.beta),
                "exact_dual_min_vis": canonical_fraction_str(opt_vis),
                "exact_dual_min_vis_float": float(opt_vis),
                "lp_min_vis": float(t_lp),
                "lp_diff": abs(float(t_lp) - float(opt_vis)),
                "lp_eta_opt": float(y1 / y0),
                "lp_zeta_opt": float(y2 / y0),
                "dual_weights": [canonical_fraction_str(w) for _, w in dual],
            }
        )

    ep2 = build_rational_extreme_point(Fraction(2, 1))
    opt2 = (2 + ep2.alpha) / ep2.beta
    grid_pts: List[Dict[str, Any]] = []
    violations = 0
    for i in range(-19, 15):
        et = Fraction(i, 20)
        for j in range(-17, 18):
            ze = Fraction(j, 20)
            _, bq, bl = bell_vector_at(ep2, et, ze)
            if bq > 0 and bl <= bq:
                vis = bl / bq
                if vis < opt2:
                    violations += 1
                grid_pts.append({"eta": float(et), "zeta": float(ze), "vis": float(vis)})

    return {
        "experiment": "exp4_visibility_optimality_landscape",
        "lp_checks": lp_checks,
        "k2_interior_grid_points": len(grid_pts),
        "k2_visibility_bound_violations": violations,
        "k2_grid": grid_pts,
    }


def main() -> None:
    res_dir = ROOT / "results"
    res_dir.mkdir(parents=True, exist_ok=True)
    cert_dir = res_dir / "certificates"

    t0 = time.perf_counter()
    e1 = run_exp1_certified_atlas(cert_dir)
    (res_dir / "exp1_certified_atlas.json").write_text(json.dumps(e1, indent=2) + "\n", encoding="utf-8")

    e2 = run_exp2_octagon_geometry()
    (res_dir / "exp2_octagon_geometry_and_collapse.json").write_text(json.dumps(e2, indent=2) + "\n", encoding="utf-8")

    e3 = run_exp3_npa_hierarchy_phase_map()
    (res_dir / "exp3_npa_hierarchy_phase_map.json").write_text(json.dumps(e3, indent=2) + "\n", encoding="utf-8")

    e4 = run_exp4_visibility_optimality()
    (res_dir / "exp4_visibility_optimality_landscape.json").write_text(json.dumps(e4, indent=2) + "\n", encoding="utf-8")

    dt = time.perf_counter() - t0
    print(f"All 4 Paper 08 experiments completed in {dt:.2f}s:")
    print(f"  Exp 1: {e1['num_certificates']} exact-Q certs verified={e1['all_verified']}, max_qubit_err={e1['max_qubit_crosscheck_err']:.2e}")
    print(f"  Exp 2: {e2['num_extreme_points']} extreme points, vertex counts={e2['vertex_counts_by_k']}")
    print(f"  Exp 3: {e3['num_probes']} probes, areas oct={e3['area_octagon']}, 1+AB={e3['area_1ab_spectrahedron_approx']} ({100*e3['area_fraction_1ab']:.1f}%), NPA2={e3['area_npa2_spectrahedron_approx']} ({100*e3['area_fraction_npa2']:.1f}%)")
    print(f"  Exp 4: {len(e4['lp_checks'])} LP checks + {e4['k2_interior_grid_points']} grid pts, violations={e4['k2_visibility_bound_violations']}")


if __name__ == "__main__":
    main()
