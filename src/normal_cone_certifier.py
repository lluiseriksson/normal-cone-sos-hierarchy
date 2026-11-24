r"""Zero-floating-point-trust exact-Q certificate builder and verifier for Paper 08.

Schema: NORMAL-CONE-SOS-CERT-1.0 (Weak-SDP-Duality-Sound Edition)
Security & Soundness Guarantees:
  - ZERO third-party imports in the verifier: pure Python stdlib + exact `fractions.Fraction`.
  - Strict recursive type whitelisting (`type(x) is ...`): ONLY plain JSON dict (str keys),
    list, str, strict int (bool rejected BEFORE int), None. ZERO floats/bools/Decimals/tuples/subclasses.
  - Anchored ASCII-only canonical rational parsing (`\A...\Z` + `re.ASCII`): rejects trailing
    newlines, Unicode digits, unreduced fractions, `"/1"`, `"-0"`, leading `"+"`, leading zeros.
  - Exact key-set enforcement at ALL dictionary levels (zero missing or rogue keys).
  - Strict word-basis membership (`OPS_1AB_SET` for Level 1+AB, `OPS_2_SET` for Level 2) and
    rejection of empty/zero squares (`len(P) >= 1`).
  - Mathematically guaranteed mutual exclusivity between SOS tightness certificates and NPA
    moment-gap certificates by Weak SDP Duality (Lean 4 Theorem 20):
      1. `level_1ab_sos_exact`: replays sum_j w_j P_j^dag P_j == beta_Q*I - B over Q with
         w_j > 0 and P_j in span(OPS_1AB) \ {0}.
      2. `level_2_tight_1ab_gap`: replays BOTH (i) an exact 9x9 PD NPA-(1+AB) moment matrix
         Gamma_1 = L D L^T (unit lower-triangular L, D_i > 0, all 81 word-equivalences, Gamma[0,0]=1,
         B . gamma(Gamma_1) > beta_Q) AND (ii) an exact NPA-2 SOS sum_j w_j P_j^dag P_j == beta_Q*I - B
         with w_j > 0 and P_j in span(OPS_2) \ {0}.
      3. `level_1ab_moment_gap`: replays an exact 9x9 PD NPA-(1+AB) moment matrix Gamma_1 = L D L^T
         with B . gamma(Gamma_1) > beta_Q.
      4. `level_2_moment_gap`: replays an exact 13x13 PD NPA-2 moment matrix Gamma_2 = L D L^T
         (all 169 word-equivalences, Gamma[0,0]=1, B . gamma(Gamma_2) > beta_Q).
  - All 4 modes additionally replay the Theorem 3.4 universal 4-vertex visibility LP dual certificate
    and all 16 local-vertex normal-cone inequalities.
"""

from __future__ import annotations

import math
import re
from fractions import Fraction
from typing import Any, Dict, FrozenSet, List, Sequence, Tuple

from .nc_sos import (
    BELL_WORDS,
    LOCAL_VERTICES,
    OPS_1AB,
    OPS_1AB_SET,
    OPS_2,
    OPS_2_SET,
    NCPoly,
    Word,
    add_poly,
    bell_functional_poly,
    bell_vector_at,
    build_rational_extreme_point,
    build_npa_word_map,
    compute_visibility_dual_weights,
    dag_poly,
    mul_poly,
    poly_I,
    reconstruct_ldlt_exact,
    reduce_party_word,
    scale_poly,
)

SCHEMA_VERSION = "NORMAL-CONE-SOS-CERT-1.0"
_INT_RE = re.compile(r"\A(?:0|-?[1-9][0-9]*)\Z", re.ASCII)
_FRAC_RE = re.compile(r"\A(?P<num>-?[1-9][0-9]*)/(?P<den>[1-9][0-9]*)\Z", re.ASCII)

_TOP_KEYS = frozenset({
    "schema_version",
    "cert_id",
    "k",
    "alpha",
    "beta",
    "eta",
    "zeta",
    "p_star",
    "bell_vector",
    "beta_Q",
    "beta_loc",
    "visibility_ratio",
    "optimal_visibility_ratio",
    "in_normal_cone",
    "certificate_mode",
    "certificate_payload",
    "visibility_dual",
})

_VIS_DUAL_KEYS = frozenset({"active_vertices", "weights", "bound_ratio"})
_SOS_PAYLOAD_KEYS = frozenset({"level", "num_squares", "squares"})
_MOMENT_PAYLOAD_KEYS = frozenset({"level", "dim", "L", "D", "moment_value", "npa_gap"})
_TIER3_DUAL_PAYLOAD_KEYS = frozenset({"level_1ab_moment_gap", "level_2_sos_exact"})

_WORD_MAP_1AB = build_npa_word_map(OPS_1AB)
_WORD_MAP_2 = build_npa_word_map(OPS_2)


def _assert_strict_json_types(obj: Any, path: str = "$") -> None:
    """Recursively reject floats, bools, Decimals, tuples, subclasses, or non-str dict keys."""
    if obj is None:
        return
    if type(obj) is bool:
        raise ValueError(f"Forbidden bool at {path}: {obj!r}")
    if type(obj) is int:
        return
    if type(obj) is str:
        return
    if type(obj) is list:
        for idx, item in enumerate(obj):
            _assert_strict_json_types(item, f"{path}[{idx}]")
        return
    if type(obj) is dict:
        for k, v in obj.items():
            if type(k) is not str:
                raise ValueError(f"Non-string dict key at {path}: {k!r}")
            _assert_strict_json_types(v, f"{path}.{k}")
        return
    raise ValueError(f"Forbidden type {type(obj).__name__} at {path}: {obj!r}")


def canonical_fraction_str(x: Fraction) -> str:
    if not isinstance(x, Fraction):
        raise TypeError(f"Expected Fraction, got {type(x).__name__}")
    if x.denominator == 1:
        return str(x.numerator)
    return f"{x.numerator}/{x.denominator}"


def parse_canonical_fraction(s: Any, field_name: str = "rational") -> Fraction:
    if type(s) is not str:
        raise ValueError(f"{field_name} must be a canonical str, got {type(s).__name__}")
    if _INT_RE.match(s):
        return Fraction(int(s), 1)
    m = _FRAC_RE.match(s)
    if not m:
        raise ValueError(f"Non-canonical rational string for {field_name}: {s!r}")
    num = int(m.group("num"))
    den = int(m.group("den"))
    if den < 2:
        raise ValueError(f"Denominator must be >= 2 for {field_name}: {s!r}")
    if math.gcd(abs(num), den) != 1:
        raise ValueError(f"Unreduced rational string for {field_name}: {s!r}")
    return Fraction(num, den)


def _encode_poly(p: NCPoly) -> List[List[Any]]:
    return [
        [list(a_w), list(b_w), canonical_fraction_str(coef)]
        for (a_w, b_w), coef in sorted(p.items())
        if coef != 0
    ]


def _decode_poly(
    raw: Any,
    field_name: str,
    allowed_words: FrozenSet[Word],
) -> NCPoly:
    """Strictly parse a non-empty canonical serialized NCPoly supported on `allowed_words`."""
    if type(raw) is not list or len(raw) == 0:
        raise ValueError(f"{field_name} must be a non-empty list of [a_word, b_word, coeff] terms")
    out: NCPoly = {}
    prev_word: Word | None = None
    for idx, term in enumerate(raw):
        if type(term) is not list or len(term) != 3:
            raise ValueError(f"Malformed term {field_name}[{idx}]: {term!r}")
        aw_raw, bw_raw, c_raw = term
        if type(aw_raw) is not list or type(bw_raw) is not list:
            raise ValueError(f"Word lists must be lists in {field_name}[{idx}]")
        for g in aw_raw + bw_raw:
            if type(g) is not int or g not in (0, 1):
                raise ValueError(f"Non-binary generator {g!r} in {field_name}[{idx}]")
        aw = tuple(aw_raw)
        bw = tuple(bw_raw)
        if reduce_party_word(aw) != aw or reduce_party_word(bw) != bw:
            raise ValueError(f"Unreduced word {(aw, bw)} in {field_name}[{idx}]")
        w: Word = (aw, bw)
        if w not in allowed_words:
            raise ValueError(f"Word {w} outside allowed NPA basis in {field_name}[{idx}]")
        if prev_word is not None and w <= prev_word:
            raise ValueError(f"Non-ascending or duplicate word {w} in {field_name}[{idx}]")
        coef = parse_canonical_fraction(c_raw, f"{field_name}[{idx}].coeff")
        if coef == 0:
            raise ValueError(f"Explicit zero coefficient forbidden in {field_name}[{idx}]")
        out[w] = coef
        prev_word = w
    return out


def _encode_sos_payload(level: str, squares: Sequence[Tuple[Fraction, NCPoly]]) -> Dict[str, Any]:
    return {
        "level": level,
        "num_squares": len(squares),
        "squares": [[canonical_fraction_str(w), _encode_poly(P)] for w, P in squares],
    }


def _encode_moment_payload(
    level: str,
    L: Sequence[Sequence[Fraction]],
    D: Sequence[Fraction],
    moment_value: Fraction,
    beta_q: Fraction,
) -> Dict[str, Any]:
    return {
        "level": level,
        "dim": len(D),
        "L": [[canonical_fraction_str(x) for x in row] for row in L],
        "D": [canonical_fraction_str(x) for x in D],
        "moment_value": canonical_fraction_str(moment_value),
        "npa_gap": canonical_fraction_str(moment_value - beta_q),
    }


def build_certificate_from_witnesses(
    cert_id: str,
    k: Fraction,
    eta: Fraction,
    zeta: Fraction,
    mode: str,
    *,
    sos_squares: Sequence[Tuple[Fraction, NCPoly]] | None = None,
    moment_ldlt: Tuple[Sequence[Sequence[Fraction]], Sequence[Fraction], Fraction] | None = None,
) -> Dict[str, Any]:
    """Assemble a self-contained zero-float NORMAL-CONE-SOS-CERT-1.0 certificate from exact-Q witnesses."""
    if type(cert_id) is not str or not cert_id.strip():
        raise ValueError("cert_id must be a non-empty non-whitespace string")
    ep = build_rational_extreme_point(k)
    b_vec, beta_q, beta_loc = bell_vector_at(ep, eta, zeta)
    if beta_q <= 0 or beta_loc > beta_q:
        raise ValueError(
            f"Ray (eta={eta}, zeta={zeta}) lies outside normal cone N_Q(p*({k})): "
            f"beta_Q={beta_q}, beta_loc={beta_loc}"
        )

    vis_ratio = beta_loc / beta_q
    opt_vis = (2 + ep.alpha) / ep.beta
    dual_pairs = compute_visibility_dual_weights(ep)

    if mode == "level_1ab_sos_exact":
        if sos_squares is None:
            raise ValueError("sos_squares required for level_1ab_sos_exact")
        payload: Dict[str, Any] = _encode_sos_payload("1+AB", sos_squares)
    elif mode == "level_1ab_moment_gap":
        if moment_ldlt is None:
            raise ValueError("moment_ldlt required for level_1ab_moment_gap")
        L, D, mval = moment_ldlt
        payload = _encode_moment_payload("1+AB", L, D, mval, beta_q)
    elif mode == "level_2_moment_gap":
        if moment_ldlt is None:
            raise ValueError("moment_ldlt required for level_2_moment_gap")
        L, D, mval = moment_ldlt
        payload = _encode_moment_payload("2", L, D, mval, beta_q)
    elif mode == "level_2_tight_1ab_gap":
        if sos_squares is None or moment_ldlt is None:
            raise ValueError("Both sos_squares (NPA-2) and moment_ldlt (1+AB) required for level_2_tight_1ab_gap")
        L, D, mval = moment_ldlt
        payload = {
            "level_1ab_moment_gap": _encode_moment_payload("1+AB", L, D, mval, beta_q),
            "level_2_sos_exact": _encode_sos_payload("2", sos_squares),
        }
    else:
        raise ValueError(f"Unsupported certificate mode: {mode!r}")

    cert: Dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "cert_id": cert_id,
        "k": canonical_fraction_str(ep.k),
        "alpha": canonical_fraction_str(ep.alpha),
        "beta": canonical_fraction_str(ep.beta),
        "eta": canonical_fraction_str(eta),
        "zeta": canonical_fraction_str(zeta),
        "p_star": [canonical_fraction_str(x) for x in ep.p_star],
        "bell_vector": [canonical_fraction_str(x) for x in b_vec],
        "beta_Q": canonical_fraction_str(beta_q),
        "beta_loc": canonical_fraction_str(beta_loc),
        "visibility_ratio": canonical_fraction_str(vis_ratio),
        "optimal_visibility_ratio": canonical_fraction_str(opt_vis),
        "in_normal_cone": 1,
        "certificate_mode": mode,
        "certificate_payload": payload,
        "visibility_dual": {
            "active_vertices": [list(v) for v, _ in dual_pairs],
            "weights": [canonical_fraction_str(w) for _, w in dual_pairs],
            "bound_ratio": canonical_fraction_str(opt_vis),
        },
    }
    _assert_strict_json_types(cert)
    return cert


def _verify_sos_payload(
    payload: Dict[str, Any],
    expected_level: str,
    allowed_words: FrozenSet[Word],
    target_poly: NCPoly,
) -> None:
    if type(payload) is not dict or set(payload.keys()) != _SOS_PAYLOAD_KEYS:
        raise ValueError("SOS payload key mismatch")
    if payload["level"] != expected_level:
        raise ValueError(f"SOS payload level must be {expected_level!r}")
    squares_raw = payload["squares"]
    if type(squares_raw) is not list or len(squares_raw) == 0:
        raise ValueError("SOS squares must be a non-empty list")
    if payload["num_squares"] != len(squares_raw):
        raise ValueError("num_squares mismatch")
    recon: NCPoly = {}
    for idx, sq in enumerate(squares_raw):
        if type(sq) is not list or len(sq) != 2:
            raise ValueError(f"Malformed square entry squares[{idx}]")
        w_sq = parse_canonical_fraction(sq[0], f"squares[{idx}].weight")
        if w_sq <= 0:
            raise ValueError(f"SOS weight must be strictly positive at squares[{idx}]")
        P = _decode_poly(sq[1], f"squares[{idx}].poly", allowed_words=allowed_words)
        recon = add_poly(recon, mul_poly(dag_poly(P), P), w_sq)
    if recon != target_poly:
        raise ValueError(
            f"Non-commutative SOS polynomial replay FAILED at level {expected_level}: "
            "sum w_j P_j^dag P_j != beta_Q*I - B"
        )


def _verify_moment_gap_payload(
    payload: Dict[str, Any],
    expected_level: str,
    expected_dim: int,
    word_map: Dict[Word, List[Tuple[int, int]]],
    b_vec_actual: Tuple[Fraction, ...],
    beta_q_actual: Fraction,
) -> Fraction:
    if type(payload) is not dict or set(payload.keys()) != _MOMENT_PAYLOAD_KEYS:
        raise ValueError("Moment-gap payload key mismatch")
    if payload["level"] != expected_level or payload["dim"] != expected_dim:
        raise ValueError(f"Moment-gap payload metadata mismatch (expected level={expected_level}, dim={expected_dim})")

    L_raw = payload["L"]
    D_raw = payload["D"]
    if type(L_raw) is not list or len(L_raw) != expected_dim:
        raise ValueError(f"L must be a {expected_dim}x{expected_dim} list")
    if type(D_raw) is not list or len(D_raw) != expected_dim:
        raise ValueError(f"D must have length {expected_dim}")

    D = [parse_canonical_fraction(x, f"D[{i}]") for i, x in enumerate(D_raw)]
    if any(d <= 0 for d in D):
        raise ValueError("All LDL^T diagonal pivots D[i] must be strictly positive (strict PD)")

    L: List[List[Fraction]] = []
    for i, row_raw in enumerate(L_raw):
        if type(row_raw) is not list or len(row_raw) != expected_dim:
            raise ValueError(f"L[{i}] must have length {expected_dim}")
        row = [parse_canonical_fraction(x, f"L[{i}][{j}]") for j, x in enumerate(row_raw)]
        if row[i] != Fraction(1, 1):
            raise ValueError(f"L must be unit lower-triangular: L[{i}][{i}] = {row[i]} != 1")
        for j in range(i + 1, expected_dim):
            if row[j] != Fraction(0, 1):
                raise ValueError(f"L must be lower-triangular: L[{i}][{j}] = {row[j]} != 0")
        L.append(row)

    # Reconstruct exact Gamma = L D L^T over Q (guaranteed strictly PD!)
    Gamma = reconstruct_ldlt_exact(L, D)

    # Verify all NPA moment-matrix word-equivalence constraints across all dim^2 entries!
    word_val: Dict[Word, Fraction] = {}
    for w, cells in word_map.items():
        r0, c0 = cells[0]
        v0 = Gamma[r0][c0]
        if w == ((), ()):
            if v0 != Fraction(1, 1):
                raise ValueError(f"Identity moment must equal 1, got {v0}")
        for r, c in cells[1:]:
            if Gamma[r][c] != v0:
                raise ValueError(
                    f"NPA moment-matrix symmetry violated for word {w}: "
                    f"Gamma[{r0},{c0}]={v0} != Gamma[{r},{c}]={Gamma[r][c]}"
                )
        word_val[w] = v0

    # Evaluate Bell functional on Gamma and verify strict gap > 0!
    moment_val_actual = sum(b_vec_actual[idx] * word_val[bw] for idx, bw in enumerate(BELL_WORDS))
    gap_actual = moment_val_actual - beta_q_actual
    if parse_canonical_fraction(payload["moment_value"], "moment_value") != moment_val_actual:
        raise ValueError("Claimed moment_value mismatch")
    if parse_canonical_fraction(payload["npa_gap"], "npa_gap") != gap_actual:
        raise ValueError("Claimed npa_gap mismatch")
    if gap_actual <= 0:
        raise ValueError(f"Moment matrix fails to strictly exceed beta_Q: gap={gap_actual} <= 0")
    return gap_actual


def verify_normal_cone_certificate_exact(cert: Dict[str, Any]) -> Dict[str, Any]:
    """Independently verify a NORMAL-CONE-SOS-CERT-1.0 certificate with ZERO floating-point trust.

    Raises ValueError on any type, schema, algebraic, SOS, moment-matrix, or visibility violation.
    """
    if type(cert) is not dict:
        raise ValueError("Certificate must be a dict")
    _assert_strict_json_types(cert)

    if cert.get("schema_version") != SCHEMA_VERSION:
        raise ValueError(f"Unsupported schema_version: {cert.get('schema_version')!r}")
    if set(cert.keys()) != _TOP_KEYS:
        raise ValueError(
            f"Top-level key mismatch: missing={sorted(_TOP_KEYS - set(cert.keys()))}, "
            f"extra={sorted(set(cert.keys()) - _TOP_KEYS)}"
        )

    cert_id = cert["cert_id"]
    if type(cert_id) is not str or not cert_id.strip():
        raise ValueError(f"cert_id must be a non-empty non-whitespace str, got {cert_id!r}")
    if cert["in_normal_cone"] != 1:
        raise ValueError(f"in_normal_cone must be strict int 1, got {cert['in_normal_cone']!r}")

    k = parse_canonical_fraction(cert["k"], "k")
    eta = parse_canonical_fraction(cert["eta"], "eta")
    zeta = parse_canonical_fraction(cert["zeta"], "zeta")
    ep = build_rational_extreme_point(k)

    # 1. Verify rational extreme point and Bell functional parameters
    if parse_canonical_fraction(cert["alpha"], "alpha") != ep.alpha:
        raise ValueError("alpha mismatch")
    if parse_canonical_fraction(cert["beta"], "beta") != ep.beta:
        raise ValueError("beta mismatch")

    p_claimed = cert["p_star"]
    if type(p_claimed) is not list or len(p_claimed) != 8:
        raise ValueError("p_star must be a list of 8 canonical rationals")
    if tuple(parse_canonical_fraction(x, f"p_star[{i}]") for i, x in enumerate(p_claimed)) != ep.p_star:
        raise ValueError("p_star mismatch")

    b_vec_actual, beta_q_actual, beta_loc_actual = bell_vector_at(ep, eta, zeta)
    if beta_q_actual <= 0 or beta_loc_actual > beta_q_actual:
        raise ValueError("Ray (eta, zeta) fails 16-local-vertex normal-cone inequalities")

    b_claimed = cert["bell_vector"]
    if type(b_claimed) is not list or len(b_claimed) != 8:
        raise ValueError("bell_vector must be a list of 8 canonical rationals")
    if tuple(parse_canonical_fraction(x, f"bell_vector[{i}]") for i, x in enumerate(b_claimed)) != b_vec_actual:
        raise ValueError("bell_vector mismatch")

    if parse_canonical_fraction(cert["beta_Q"], "beta_Q") != beta_q_actual:
        raise ValueError("beta_Q mismatch")
    if parse_canonical_fraction(cert["beta_loc"], "beta_loc") != beta_loc_actual:
        raise ValueError("beta_loc mismatch")
    if parse_canonical_fraction(cert["visibility_ratio"], "visibility_ratio") != beta_loc_actual / beta_q_actual:
        raise ValueError("visibility_ratio mismatch")
    opt_vis = (2 + ep.alpha) / ep.beta
    if parse_canonical_fraction(cert["optimal_visibility_ratio"], "optimal_visibility_ratio") != opt_vis:
        raise ValueError("optimal_visibility_ratio mismatch")

    # 2. Independently replay Theorem 3.4 universal 4-vertex visibility LP dual certificate
    vd = cert["visibility_dual"]
    if type(vd) is not dict or set(vd.keys()) != _VIS_DUAL_KEYS:
        raise ValueError("visibility_dual schema mismatch")
    av = vd["active_vertices"]
    ws = vd["weights"]
    if type(av) is not list or type(ws) is not list or len(av) != 4 or len(ws) != 4:
        raise ValueError("visibility_dual must contain 4 active vertices and 4 weights")
    dual_w = [parse_canonical_fraction(w, f"visibility_dual.weights[{i}]") for i, w in enumerate(ws)]
    if any(w <= 0 for w in dual_w) or sum(dual_w) != Fraction(1, 1):
        raise ValueError("visibility_dual weights must be strictly positive and sum to 1")
    seen_v = set()
    dual_b_sum = Fraction(0, 1)
    dual_I_sum = Fraction(0, 1)
    dual_S_sum = Fraction(0, 1)
    dual_D_sum = Fraction(0, 1)
    for idx, (v_raw, w) in enumerate(zip(av, dual_w)):
        if type(v_raw) is not list or len(v_raw) != 8 or any(type(x) is not int or x not in (-1, 1) for x in v_raw):
            raise ValueError(f"Malformed local vertex in visibility_dual.active_vertices[{idx}]")
        vt = tuple(v_raw)
        if vt not in LOCAL_VERTICES or vt in seen_v:
            raise ValueError(f"Invalid or duplicate local vertex in visibility_dual[{idx}]")
        seen_v.add(vt)
        val_l = sum(b_vec_actual[i] * vt[i] for i in range(8))
        if val_l > beta_loc_actual:
            raise ValueError("Local vertex exceeds claimed beta_loc")
        dual_b_sum += w * val_l
        dual_I_sum += w * sum(ep.v_I[i] * vt[i] for i in range(8))
        dual_S_sum += w * sum(ep.v_S[i] * vt[i] for i in range(8))
        dual_D_sum += w * sum(ep.v_D[i] * vt[i] for i in range(8))
    bound_ratio = parse_canonical_fraction(vd["bound_ratio"], "visibility_dual.bound_ratio")
    if bound_ratio != opt_vis:
        raise ValueError("visibility_dual.bound_ratio mismatch")
    if dual_I_sum != bound_ratio * ep.beta:
        raise ValueError("Theorem 3.4 universal dual I_alpha matching failed")
    if dual_S_sum != bound_ratio * (ep.alpha * ep.beta / 4):
        raise ValueError("Theorem 3.4 universal dual S_alpha matching failed")
    if dual_D_sum != Fraction(0, 1):
        raise ValueError("Theorem 3.4 universal dual D_alpha cancellation failed")
    if dual_b_sum != bound_ratio * beta_q_actual:
        raise ValueError("Theorem 3.4 dual equality sum_j w_j B(L_j) != ((2+a)/b)*beta_Q failed")
    if beta_loc_actual < dual_b_sum:
        raise ValueError("Visibility lower bound violated")

    # 3. Independently verify the exact mode payload
    mode = cert["certificate_mode"]
    payload = cert["certificate_payload"]
    if type(payload) is not dict:
        raise ValueError("certificate_payload must be a dict")

    target_poly = add_poly(
        scale_poly(poly_I(), beta_q_actual),
        bell_functional_poly(b_vec_actual),
        Fraction(-1, 1),
    )

    if mode == "level_1ab_sos_exact":
        _verify_sos_payload(payload, "1+AB", OPS_1AB_SET, target_poly)
    elif mode == "level_1ab_moment_gap":
        _verify_moment_gap_payload(payload, "1+AB", 9, _WORD_MAP_1AB, b_vec_actual, beta_q_actual)
    elif mode == "level_2_moment_gap":
        _verify_moment_gap_payload(payload, "2", 13, _WORD_MAP_2, b_vec_actual, beta_q_actual)
    elif mode == "level_2_tight_1ab_gap":
        if set(payload.keys()) != _TIER3_DUAL_PAYLOAD_KEYS:
            raise ValueError("Tier-3 dual payload key mismatch")
        _verify_moment_gap_payload(
            payload["level_1ab_moment_gap"], "1+AB", 9, _WORD_MAP_1AB, b_vec_actual, beta_q_actual
        )
        _verify_sos_payload(payload["level_2_sos_exact"], "2", OPS_2_SET, target_poly)
    else:
        raise ValueError(f"Unsupported certificate_mode: {mode!r}")

    return {
        "verified": True,
        "cert_id": cert_id,
        "k": str(k),
        "eta": str(eta),
        "zeta": str(zeta),
        "mode": mode,
    }
