"""Exact-Q non-commutative polynomial algebra, rational extreme-point geometry,
Wu-Xie-Ramanathan normal-cone polygons, exact NPA-(1+AB)/NPA-2 moment-map & LDL^T
arithmetic, and 4-vertex white-noise visibility LP duality over Q_{2222}.

All algebraic computations in this module operate strictly over exact Python Fractions (Q)
with ZERO floating-point arithmetic and ZERO third-party dependencies.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Dict, List, Optional, Sequence, Tuple

# Word in Q<A0, A1, B0, B1> / <Ax^2 = 1, By^2 = 1, [Ax, By] = 0>
# Represented as (alice_word, bob_word) where each is a tuple of ints in {0, 1}
# with no adjacent identical entries.
Word = Tuple[Tuple[int, ...], Tuple[int, ...]]
NCPoly = Dict[Word, Fraction]

# All 16 local deterministic strategies (a0, a1, b0, b1) in {-1, +1}^4
# mapped to behaviour vectors [a0, a1, b0, b1, a0*b0, a0*b1, a1*b0, a1*b1].
LOCAL_VERTICES: Tuple[Tuple[int, ...], ...] = tuple(
    (a0, a1, b0, b1, a0 * b0, a0 * b1, a1 * b0, a1 * b1)
    for a0 in (-1, 1)
    for a1 in (-1, 1)
    for b0 in (-1, 1)
    for b1 in (-1, 1)
)

# Canonical NPA-(1+AB) (9 operators) and NPA-2 (13 operators) monomial bases
OPS_1AB: Tuple[Word, ...] = (
    ((), ()),
    ((0,), ()),
    ((1,), ()),
    ((), (0,)),
    ((), (1,)),
    ((0,), (0,)),
    ((0,), (1,)),
    ((1,), (0,)),
    ((1,), (1,)),
)
OPS_2: Tuple[Word, ...] = OPS_1AB + (
    ((0, 1), ()),
    ((1, 0), ()),
    ((), (0, 1)),
    ((), (1, 0)),
)
OPS_1AB_SET = frozenset(OPS_1AB)
OPS_2_SET = frozenset(OPS_2)

# Ordered 8 correlator words corresponding to [A0, A1, B0, B1, A0B0, A0B1, A1B0, A1B1]
BELL_WORDS: Tuple[Word, ...] = (
    ((0,), ()),
    ((1,), ()),
    ((), (0,)),
    ((), (1,)),
    ((0,), (0,)),
    ((0,), (1,)),
    ((1,), (0,)),
    ((1,), (1,)),
)


def reduce_party_word(w: Sequence[int]) -> Tuple[int, ...]:
    """Reduce a single-party word modulo A_x^2 = 1 (or B_y^2 = 1)."""
    out: List[int] = []
    for c in w:
        if c not in (0, 1):
            raise ValueError(f"Invalid generator index {c!r}; must be 0 or 1")
        if out and out[-1] == c:
            out.pop()
        else:
            out.append(c)
    return tuple(out)


def mul_poly(p1: NCPoly, p2: NCPoly) -> NCPoly:
    """Exact multiplication in Q<A0, A1, B0, B1> / <Ax^2=1, By^2=1, [Ax, By]=0>."""
    out: Dict[Word, Fraction] = {}
    for (a1, b1), v1 in p1.items():
        for (a2, b2), v2 in p2.items():
            key = (reduce_party_word(a1 + a2), reduce_party_word(b1 + b2))
            out[key] = out.get(key, Fraction(0, 1)) + v1 * v2
    return {k: v for k, v in out.items() if v != 0}


def dag_poly(p: NCPoly) -> NCPoly:
    """Hermitian adjoint P^dag (reverses both party words; coefficients in Q)."""
    return {(a[::-1], b[::-1]): v for (a, b), v in p.items() if v != 0}


def add_poly(p1: NCPoly, p2: NCPoly, scale: Fraction = Fraction(1, 1)) -> NCPoly:
    """Exact linear combination p1 + scale * p2."""
    out = dict(p1)
    for k, v in p2.items():
        nv = out.get(k, Fraction(0, 1)) + scale * v
        if nv == 0:
            out.pop(k, None)
        else:
            out[k] = nv
    return out


def scale_poly(p: NCPoly, s: Fraction) -> NCPoly:
    if s == 0:
        return {}
    return {k: v * s for k, v in p.items() if v != 0}


def poly_I() -> NCPoly:
    return {((), ()): Fraction(1, 1)}


def poly_A(x: int) -> NCPoly:
    return {((x,), ()): Fraction(1, 1)}


def poly_B(y: int) -> NCPoly:
    return {((), (y,)): Fraction(1, 1)}


def bell_functional_poly(vec: Sequence[Fraction]) -> NCPoly:
    """Convert an 8-tuple [a0, a1, b0, b1, c00, c01, c10, c11] to an exact NCPoly."""
    if len(vec) != 8:
        raise ValueError(f"Bell vector must have length 8, got {len(vec)}")
    A0, A1, B0, B1 = poly_A(0), poly_A(1), poly_B(0), poly_B(1)
    ops = [
        A0,
        A1,
        B0,
        B1,
        mul_poly(A0, B0),
        mul_poly(A0, B1),
        mul_poly(A1, B0),
        mul_poly(A1, B1),
    ]
    out: NCPoly = {}
    for coef, op in zip(vec, ops):
        if coef != 0:
            out = add_poly(out, op, coef)
    return out


def canonical_sym_word(w: Word) -> Word:
    """Canonical representative under Hermitian adjoint w <-> w^dag for real symmetric moment matrices."""
    wa, wb = w
    wd = (wa[::-1], wb[::-1])
    return w if w <= wd else wd


def build_npa_word_map(ops: Sequence[Word]) -> Dict[Word, List[Tuple[int, int]]]:
    """Map every canonical symmetrized moment word to all (i, j) cells of Gamma_{ij} = <ops[i]^dag ops[j]>."""
    word_to_cells: Dict[Word, List[Tuple[int, int]]] = {}
    n = len(ops)
    for i in range(n):
        ai, bi = ops[i]
        ad, bd = ai[::-1], bi[::-1]
        for j in range(n):
            aj, bj = ops[j]
            wa = reduce_party_word(ad + aj)
            wb = reduce_party_word(bd + bj)
            cw = canonical_sym_word((wa, wb))
            word_to_cells.setdefault(cw, []).append((i, j))
    return word_to_cells


def exact_ldlt_pd(
    M: Sequence[Sequence[Fraction]],
) -> Tuple[Optional[List[List[Fraction]]], Optional[List[Fraction]]]:
    """Exact rational LDL^T factorization for a strictly positive-definite symmetric matrix M."""
    n = len(M)
    L = [[Fraction(0, 1) for _ in range(n)] for _ in range(n)]
    D = [Fraction(0, 1) for _ in range(n)]
    for i in range(n):
        L[i][i] = Fraction(1, 1)
        s = M[i][i] - sum(L[i][j] * L[i][j] * D[j] for j in range(i))
        if s <= 0:
            return None, None
        D[i] = s
        for r in range(i + 1, n):
            num = M[r][i] - sum(L[r][j] * L[i][j] * D[j] for j in range(i))
            L[r][i] = num / D[i]
    return L, D


def exact_ldlt_psd(
    M: Sequence[Sequence[Fraction]],
) -> Tuple[Optional[List[List[Fraction]]], Optional[List[Fraction]]]:
    """Exact rational LDL^T factorization for a PSD symmetric matrix M (allowing zero pivots)."""
    n = len(M)
    L = [[Fraction(0, 1) for _ in range(n)] for _ in range(n)]
    D = [Fraction(0, 1) for _ in range(n)]
    for i in range(n):
        L[i][i] = Fraction(1, 1)
        s = M[i][i] - sum(L[i][j] * L[i][j] * D[j] for j in range(i))
        if s < 0:
            return None, None
        D[i] = s
        if s == 0:
            for r in range(i + 1, n):
                num = M[r][i] - sum(L[r][j] * L[i][j] * D[j] for j in range(i))
                if num != 0:
                    return None, None
                L[r][i] = Fraction(0, 1)
        else:
            for r in range(i + 1, n):
                num = M[r][i] - sum(L[r][j] * L[i][j] * D[j] for j in range(i))
                L[r][i] = num / D[i]
    return L, D


def reconstruct_ldlt_exact(
    L: Sequence[Sequence[Fraction]], D: Sequence[Fraction]
) -> List[List[Fraction]]:
    """Compute M = L diag(D) L^T in exact rational arithmetic."""
    n = len(D)
    M = [[Fraction(0, 1) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(i, n):
            val = sum(L[i][k] * D[k] * L[j][k] for k in range(min(i, j) + 1))
            M[i][j] = val
            M[j][i] = val
    return M


@dataclass(frozen=True)
class RationalExtremePoint:
    """Exact rational tilted-CHSH nonlocal extreme point p*(k) in Q^8 cap ext(Q_{2222}).

    Generated by Theorem 3.1 for any rational k in (1, 1 + sqrt(2)):
      alpha = 2*(1 + 2k - k^2) / (k^2 + 2k - 1) in (0, 2)
      beta  = 4*(k^2 + 1) / (k^2 + 2k - 1)      in (2*sqrt(2), 4),  beta^2 = 8 + 2*alpha^2.
    """

    k: Fraction
    alpha: Fraction
    beta: Fraction
    p_star: Tuple[Fraction, ...]
    v_I: Tuple[Fraction, ...]
    v_S: Tuple[Fraction, ...]
    v_D: Tuple[Fraction, ...]
    eta_s4_min: Fraction  # Exact S_4-subspace (Bob-tilted) left boundary -8*alpha / beta^2


def build_rational_extreme_point(k: Fraction) -> RationalExtremePoint:
    """Construct exact rational extreme point p*(k) and its 3D normal-cone tangent basis."""
    if not isinstance(k, Fraction):
        raise TypeError(f"k must be a Fraction, got {type(k).__name__}")
    denom = k * k + 2 * k - 1
    num_u = 1 + 2 * k - k * k
    if k <= 1 or num_u <= 0 or denom <= 0:
        raise ValueError(f"k must lie in (1, 1 + sqrt(2)), got {k}")
    alpha = Fraction(2, 1) * num_u / denom
    beta = Fraction(4, 1) * (k * k + 1) / denom
    if not (0 < alpha < 2):
        raise ValueError(f"alpha={alpha} out of (0, 2)")
    if beta * beta != 8 + 2 * alpha * alpha:
        raise RuntimeError("Pythagorean-Pell identity violated")

    p_star = (
        2 * alpha / beta,
        Fraction(0, 1),
        alpha / 2,
        alpha / 2,
        beta / 4,
        beta / 4,
        (4 - alpha * alpha) / (2 * beta),
        -(4 - alpha * alpha) / (2 * beta),
    )
    v_I = (
        alpha,
        Fraction(0, 1),
        Fraction(0, 1),
        Fraction(0, 1),
        Fraction(1, 1),
        Fraction(1, 1),
        Fraction(1, 1),
        Fraction(-1, 1),
    )
    v_S = (
        beta * beta / 8,
        Fraction(0, 1),
        -beta / 4,
        -beta / 4,
        alpha / 2,
        alpha / 2,
        Fraction(0, 1),
        Fraction(0, 1),
    )
    v_D = (
        Fraction(0, 1),
        -beta * beta / 8,
        beta / 4,
        -beta / 4,
        Fraction(0, 1),
        Fraction(0, 1),
        alpha / 2,
        alpha / 2,
    )
    eta_s4_min = -8 * alpha / (beta * beta)
    return RationalExtremePoint(
        k=k,
        alpha=alpha,
        beta=beta,
        p_star=p_star,
        v_I=v_I,
        v_S=v_S,
        v_D=v_D,
        eta_s4_min=eta_s4_min,
    )


def bell_vector_at(
    ep: RationalExtremePoint, eta: Fraction, zeta: Fraction
) -> Tuple[Tuple[Fraction, ...], Fraction, Fraction]:
    """Return (B_vec, beta_Q, beta_loc) for B(eta, zeta) = I_alpha + eta*S_alpha + zeta*D_alpha."""
    b_vec = tuple(
        ep.v_I[i] + eta * ep.v_S[i] + zeta * ep.v_D[i] for i in range(8)
    )
    beta_q = sum(b_vec[i] * ep.p_star[i] for i in range(8))
    beta_loc = max(sum(b_vec[i] * L[i] for i in range(8)) for L in LOCAL_VERTICES)
    return b_vec, beta_q, beta_loc


def compute_octagon_vertices(ep: RationalExtremePoint) -> List[Tuple[Fraction, Fraction]]:
    """Compute the exact vertices (8 for k > k_trib, 6 for k < k_trib) of the 2D normal-cone
    cross-section P(k) in (eta, zeta), sorted counterclockwise in exact rational arithmetic.
    """
    ineqs: List[Tuple[Fraction, Fraction, Fraction]] = []
    for L in LOCAL_VERTICES:
        c0 = sum(ep.v_I[i] * (L[i] - ep.p_star[i]) for i in range(8))
        c1 = sum(ep.v_S[i] * (L[i] - ep.p_star[i]) for i in range(8))
        c2 = sum(ep.v_D[i] * (L[i] - ep.p_star[i]) for i in range(8))
        ineqs.append((c0, c1, c2))

    verts: List[Tuple[Fraction, Fraction]] = []
    for i in range(len(ineqs)):
        c0i, c1i, c2i = ineqs[i]
        for j in range(i + 1, len(ineqs)):
            c0j, c1j, c2j = ineqs[j]
            det = c1i * c2j - c2i * c1j
            if det == 0:
                continue
            eta = (-c0i * c2j + c2i * c0j) / det
            zeta = (-c1i * c0j + c0i * c1j) / det
            if all(c0 + c1 * eta + c2 * zeta <= 0 for c0, c1, c2 in ineqs):
                pt = (eta, zeta)
                if pt not in verts:
                    verts.append(pt)

    top = sorted([p for p in verts if p[1] >= 0], key=lambda p: (-p[0], p[1]))
    bot = sorted([p for p in verts if p[1] < 0], key=lambda p: (p[0], p[1]))
    return top + bot


def build_annihilators_1ab(ep: RationalExtremePoint) -> List[NCPoly]:
    """Return the exact 5-dimensional rational annihilator basis {N1..N5} of |psi_theta>
    inside the 9-dimensional Level-(1+AB) monomial space (all 5 satisfy ||N_i |psi_theta>|| == 0).
    """
    a, b = ep.alpha, ep.beta
    I, A0, A1, B0, B1 = poly_I(), poly_A(0), poly_A(1), poly_B(0), poly_B(1)
    Bp = add_poly(B0, B1)
    Bm = add_poly(B0, B1, Fraction(-1, 1))

    N1 = add_poly(A0, Bp, -Fraction(2, 1) / b)
    N2 = add_poly(I, mul_poly(A0, Bp), -Fraction(2, 1) / b)
    N3 = add_poly(
        add_poly(scale_poly(Bm, Fraction(1, 2)), A1, -(4 - a * a) / (2 * b)),
        mul_poly(A0, Bm),
        -a / b,
    )
    N4 = add_poly(add_poly(mul_poly(A1, Bp), A1, -a), mul_poly(A0, Bm))
    N5 = add_poly(add_poly(scale_poly(I, b / 2), A0, -a), mul_poly(A1, Bm), Fraction(-1, 1))
    return [N1, N2, N3, N4, N5]


def build_annihilators_npa2(ep: RationalExtremePoint) -> List[NCPoly]:
    """Return the exact 9-dimensional rational annihilator basis {N1..N9} of |psi_theta>
    inside the 13-monomial NPA Level-2 space (all 9 satisfy ||N_i |psi_theta>|| == 0).
    """
    b = ep.beta
    I, A0, A1, B0, B1 = poly_I(), poly_A(0), poly_A(1), poly_B(0), poly_B(1)
    Bp = add_poly(B0, B1)
    Bm = add_poly(B0, B1, Fraction(-1, 1))

    N6 = add_poly(mul_poly(A0, A1), mul_poly(A1, Bp), Fraction(2, 1) / b)
    N7 = add_poly(mul_poly(A0, A1), mul_poly(A1, A0))
    N8 = add_poly(add_poly(mul_poly(B0, B1), I, -(b * b / 8 - 1)), mul_poly(A0, Bm), -b / 4)
    N9 = add_poly(add_poly(mul_poly(B0, B1), mul_poly(B1, B0)), I, -(b * b / 4 - 2))
    return build_annihilators_1ab(ep) + [N6, N7, N8, N9]


def build_tilted_chsh_sos(ep: RationalExtremePoint) -> List[Tuple[Fraction, NCPoly]]:
    """Theorem 3.1 exact 2-square rational SOS for Alice-tilted CHSH (eta = 0, zeta = 0):
      beta*I - I_alpha = (1/(2*beta)) * (beta*I - I_alpha)^2 + (1/(2*beta)) * Q_alpha^2.
    """
    a, b = ep.alpha, ep.beta
    I, A0, A1, B0, B1 = poly_I(), poly_A(0), poly_A(1), poly_B(0), poly_B(1)
    Bp = add_poly(B0, B1)
    Bm = add_poly(B0, B1, Fraction(-1, 1))
    I_a = bell_functional_poly(ep.v_I)
    P1 = add_poly(scale_poly(I, b), I_a, Fraction(-1, 1))
    P2 = add_poly(add_poly(mul_poly(A1, Bp), A1, -a), mul_poly(A0, Bm))
    w = Fraction(1, 1) / (2 * b)
    return [(w, P1), (w, P2)]


def build_bob_tilted_sos(ep: RationalExtremePoint) -> List[Tuple[Fraction, NCPoly]]:
    """Theorem 3.3(a) exact 2-square rational SOS for Bob-tilted CHSH (eta = -8*alpha/beta^2, zeta = 0):
      (8/beta)*I - B_Bob = (beta/4)*(N1 + (4*alpha/beta^2)*N5)^2 + ((8 - 2*alpha^2)/beta^3)*N5^2.
    """
    a, b = ep.alpha, ep.beta
    N1, _, _, _, N5 = build_annihilators_1ab(ep)
    P1 = add_poly(N1, N5, 4 * a / (b * b))
    w1 = b / 4
    w2 = (8 - 2 * a * a) / (b * b * b)
    return [(w1, P1), (w2, N5)]


def build_convex_segment_sos(
    ep: RationalExtremePoint, eta: Fraction
) -> List[Tuple[Fraction, NCPoly]]:
    """Exact rational S_4-subspace SOS (2 or 4 squares, zero slack) for any eta in [-8*alpha/beta^2, 0], zeta = 0."""
    if eta < ep.eta_s4_min or eta > 0:
        raise ValueError(f"eta={eta} outside S_4-subspace segment [{ep.eta_s4_min}, 0]")
    if eta == 0:
        return build_tilted_chsh_sos(ep)
    if eta == ep.eta_s4_min:
        return build_bob_tilted_sos(ep)
    tau = eta / ep.eta_s4_min
    one_minus_tau = Fraction(1, 1) - tau
    sq_alice = [(one_minus_tau * w, P) for w, P in build_tilted_chsh_sos(ep)]
    sq_bob = [(tau * w, P) for w, P in build_bob_tilted_sos(ep)]
    return sq_alice + sq_bob


def compute_visibility_dual_weights(
    ep: RationalExtremePoint,
) -> Tuple[Tuple[Tuple[int, ...], Fraction], ...]:
    """Return the exact 4 active local vertices and strictly positive rational dual weights
    proving Theorem 3.4: v(B) = beta_loc / beta_Q >= (2 + alpha) / beta uniquely at (0, 0).
    """
    a, b = ep.alpha, ep.beta
    denom = 2 * (b - 2 * a)
    w12 = (2 - a) / denom
    w34 = (b - 2 - a) / denom
    if w12 <= 0 or w34 <= 0:
        raise RuntimeError("Visibility dual weights must be strictly positive")
    verts = (
        (1, 1, 1, 1, 1, 1, 1, 1),
        (1, -1, 1, 1, 1, 1, -1, -1),
        (1, 1, 1, -1, 1, -1, 1, -1),
        (1, -1, -1, 1, -1, 1, 1, -1),
    )
    return (
        (verts[0], w12),
        (verts[1], w12),
        (verts[2], w34),
        (verts[3], w34),
    )
