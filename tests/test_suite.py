"""Comprehensive test & 42-attack adversarial red-team suite for Paper 08."""

from __future__ import annotations

import copy
import json
from decimal import Decimal
from fractions import Fraction
from pathlib import Path

import numpy as np
import pytest

from src import (
    LOCAL_VERTICES,
    OPS_1AB,
    OPS_2,
    add_poly,
    bell_functional_poly,
    bell_vector_at,
    build_annihilators_1ab,
    build_annihilators_npa2,
    build_bob_tilted_sos,
    build_convex_segment_sos,
    build_npa_word_map,
    build_rational_extreme_point,
    build_tilted_chsh_sos,
    compute_octagon_vertices,
    compute_visibility_dual_weights,
    dag_poly,
    mul_poly,
    parse_canonical_fraction,
    verify_normal_cone_certificate_exact,
)
from src.nc_sos import poly_I, scale_poly

ROOT = Path(__file__).resolve().parent.parent
CERT_DIR = ROOT / "results" / "certificates"


def _eval_poly_on_qubit(ep, poly) -> np.ndarray:
    af, bf = float(ep.alpha), float(ep.beta)
    sin2t = np.sqrt((4.0 - af * af) / (4.0 + af * af))
    mu = np.arctan(sin2t)
    sz = np.array([[1.0, 0.0], [0.0, -1.0]])
    sx = np.array([[0.0, 1.0], [1.0, 0.0]])
    I2 = np.eye(2)
    A0 = np.kron(sz, I2)
    A1 = np.kron(sx, I2)
    B0 = np.kron(I2, np.cos(mu) * sz + np.sin(mu) * sx)
    B1 = np.kron(I2, np.cos(mu) * sz - np.sin(mu) * sx)
    M = np.zeros((4, 4))
    for (aw, bw), coef in poly.items():
        P = np.eye(4)
        for x in aw:
            P = P @ (A0 if x == 0 else A1)
        for y in bw:
            P = P @ (B0 if y == 0 else B1)
        M += float(coef) * P
    return M


def test_rational_extreme_point_and_all_9_annihilators_exact() -> None:
    """Verify Theorem 3.1 rational parameterization, 2-square SOS, and all 9 exact annihilators on |psi_theta>."""
    for ks in ("11/5", "2", "7/4", "3/2", "5/4"):
        ep = build_rational_extreme_point(Fraction(ks))
        assert ep.beta * ep.beta == 8 + 2 * ep.alpha * ep.alpha
        af = float(ep.alpha)
        sin2t = np.sqrt((4.0 - af * af) / (4.0 + af * af))
        theta = 0.5 * np.arcsin(sin2t)
        psi = np.array([np.cos(theta), 0.0, 0.0, np.sin(theta)])

        # All 9 annihilators (5 for 1+AB, +4 for NPA-2) MUST annihilate |psi_theta> to machine precision!
        Ns9 = build_annihilators_npa2(ep)
        assert len(Ns9) == 9
        for idx, N in enumerate(Ns9):
            norm = float(np.linalg.norm(_eval_poly_on_qubit(ep, N) @ psi))
            assert norm < 1e-14, f"Annihilator N{idx+1} failed to annihilate |psi> at k={ks}: norm={norm}"

        # Linear rank 5 for 1+AB in 9-op space, rank 9 for NPA-2 in 13-op space
        M1 = np.array([[float(N.get(w, 0)) for w in OPS_1AB] for N in build_annihilators_1ab(ep)])
        M2 = np.array([[float(N.get(w, 0)) for w in OPS_2] for N in Ns9])
        assert np.linalg.matrix_rank(M1) == 5
        assert np.linalg.matrix_rank(M2) == 9

        # Universal 2-square SOS for Alice-tilted and Bob-tilted endpoints
        for eta, builder in ((Fraction(0, 1), build_tilted_chsh_sos), (ep.eta_s4_min, build_bob_tilted_sos)):
            b_vec, bq, _ = bell_vector_at(ep, eta, Fraction(0, 1))
            target = add_poly(scale_poly(poly_I(), bq), bell_functional_poly(b_vec), Fraction(-1, 1))
            sq = builder(ep)
            assert len(sq) == 2
            recon = {}
            for w, P in sq:
                assert w > 0
                recon = add_poly(recon, mul_poly(dag_poly(P), P), w)
            assert recon == target

        # Midpoint convex combination on S_4 core
        mid = ep.eta_s4_min / 2
        b_vec, bq, _ = bell_vector_at(ep, mid, Fraction(0, 1))
        target = add_poly(scale_poly(poly_I(), bq), bell_functional_poly(b_vec), Fraction(-1, 1))
        recon = {}
        for w, P in build_convex_segment_sos(ep, mid):
            recon = add_poly(recon, mul_poly(dag_poly(P), P), w)
        assert recon == target


def test_tribonacci_octagon_hexagon_transition_and_visibility_dual() -> None:
    """Verify Theorem 3.2 octagon-to-hexagon transition at k_trib and Theorem 3.4 universal 4-vertex dual."""
    expected_counts = {"11/5": 8, "2": 8, "184/100": 8, "183/100": 6, "7/4": 6, "3/2": 6, "5/4": 6}
    for ks, exp_n in expected_counts.items():
        ep = build_rational_extreme_point(Fraction(ks))
        verts = compute_octagon_vertices(ep)
        assert len(verts) == exp_n

        dual = compute_visibility_dual_weights(ep)
        assert sum(w for _, w in dual) == Fraction(1, 1)
        assert all(w > 0 for _, w in dual)
        v_star = (2 + ep.alpha) / ep.beta
        assert sum(w * sum(ep.v_I[i] * v[i] for i in range(8)) for v, w in dual) == v_star * ep.beta
        assert sum(w * sum(ep.v_S[i] * v[i] for i in range(8)) for v, w in dual) == v_star * (ep.alpha * ep.beta / 4)
        assert sum(w * sum(ep.v_D[i] * v[i] for i in range(8)) for v, w in dual) == Fraction(0, 1)


def test_all_shipped_certificates_verify_independently() -> None:
    """Verify all 13 shipped exact-Q certificates across all 4 sound modes."""
    certs = sorted(CERT_DIR.glob("*.cert.json"))
    assert len(certs) == 13
    modes_seen = set()
    for cp in certs:
        data = json.loads(cp.read_text(encoding="utf-8"))
        res = verify_normal_cone_certificate_exact(data)
        assert res["verified"] is True
        modes_seen.add(res["mode"])
    assert modes_seen == {
        "level_1ab_sos_exact",
        "level_2_tight_1ab_gap",
        "level_1ab_moment_gap",
        "level_2_moment_gap",
    }


def test_42_live_adversarial_red_team_attacks_rejected() -> None:
    """Every single adversarial corruption across all 4 certificate modes MUST be rejected."""
    c_sos = json.loads((CERT_DIR / "k2_alice_tilted.cert.json").read_text(encoding="utf-8"))
    c_t3 = json.loads((CERT_DIR / "k2_tier3_pos_eta.cert.json").read_text(encoding="utf-8"))
    c_m1 = json.loads((CERT_DIR / "k2_tier3_vertex_V1.cert.json").read_text(encoding="utf-8"))
    c_m2 = json.loads((CERT_DIR / "k2_tier4_vertex_V2.cert.json").read_text(encoding="utf-8"))

    attacks = []

    def add_attack(name, mut_fn, base=c_sos):
        cand = copy.deepcopy(base)
        mut_fn(cand)
        attacks.append((name, cand))

    # 1-10: Schema, type, key-set, and identifier attacks
    add_attack("01_bad_schema", lambda c: c.__setitem__("schema_version", "FAKE-1.0"))
    add_attack("02_missing_top_key", lambda c: c.pop("beta_Q"))
    add_attack("03_extra_top_key", lambda c: c.__setitem__("rogue", 1))
    add_attack("04_whitespace_cert_id", lambda c: c.__setitem__("cert_id", "   "))
    add_attack("05_bool_in_normal_cone", lambda c: c.__setitem__("in_normal_cone", True))
    add_attack("06_float_injection", lambda c: c.__setitem__("eta", 0.0))
    add_attack("07_decimal_injection", lambda c: c.__setitem__("eta", Decimal("0")))
    add_attack("08_tuple_injection", lambda c: c.__setitem__("p_star", tuple(c["p_star"])))
    add_attack("09_non_str_dict_key", lambda c: c.__setitem__(123, "bad"))
    add_attack("10_unknown_mode", lambda c: c.__setitem__("certificate_mode", "level_1ab_obstructed_farkas"))

    # 11-18: Canonical rational string parser attacks
    add_attack("11_unreduced_fraction", lambda c: c.__setitem__("alpha", "4/14"))
    add_attack("12_denom_one", lambda c: c.__setitem__("k", "2/1"))
    add_attack("13_negative_zero", lambda c: c.__setitem__("eta", "-0"))
    add_attack("14_leading_plus", lambda c: c.__setitem__("k", "+2"))
    add_attack("15_leading_zero", lambda c: c.__setitem__("k", "02"))
    add_attack("16_trailing_newline", lambda c: c.__setitem__("k", "2\n"))
    add_attack("17_unicode_digit", lambda c: c.__setitem__("k", "\u0662"))
    add_attack("18_k_out_of_domain", lambda c: c.__setitem__("k", "3"))

    # 19-24: Extreme point, Bell vector, and normal-cone boundary attacks
    add_attack("19_tampered_p_star", lambda c: c["p_star"].__setitem__(0, "1/4"))
    add_attack("20_tampered_bell_vector", lambda c: c["bell_vector"].__setitem__(0, "3/7"))
    add_attack("21_tampered_beta_Q", lambda c: c.__setitem__("beta_Q", "21/7"))
    add_attack("22_tampered_beta_loc", lambda c: c.__setitem__("beta_loc", "15/7"))
    add_attack("23_ray_outside_normal_cone", lambda c: c.__setitem__("eta", "4/5"))
    add_attack("24_tampered_vis_ratio", lambda c: c.__setitem__("visibility_ratio", "3/4"))

    # 25-32: SOS payload attacks (including zero-square & out-of-basis word attacks!)
    add_attack("25_sos_extra_key", lambda c: c["certificate_payload"].__setitem__("extra", 1))
    add_attack("26_sos_negative_weight", lambda c: c["certificate_payload"]["squares"][0].__setitem__(0, "-7/40"))
    add_attack("27_sos_zero_weight", lambda c: c["certificate_payload"]["squares"][0].__setitem__(0, "0"))
    add_attack("28_sos_zero_square_empty_poly", lambda c: (
        c["certificate_payload"]["squares"].append(["1", []]),
        c["certificate_payload"].__setitem__("num_squares", len(c["certificate_payload"]["squares"])),
    ))
    add_attack("29_sos_tampered_poly_coeff", lambda c: c["certificate_payload"]["squares"][0][1][0].__setitem__(2, "1"))
    add_attack("30_sos_unreduced_word", lambda c: c["certificate_payload"]["squares"][0][1].append([[0, 0], [], "1"]))
    add_attack("31_sos_1ab_degree2_word_escape", lambda c: c["certificate_payload"]["squares"][0][1].append([[0, 1], [], "1"]))
    add_attack("32_sos_npa2_degree4_word_escape", lambda c: c["certificate_payload"]["level_2_sos_exact"]["squares"][0][1].append([[0, 1], [0, 1], "1"]), base=c_t3)

    # 33-38: Exact LDL^T NPA moment-matrix attacks (9x9 and 13x13!)
    add_attack("33_moment_negative_pivot", lambda c: c["certificate_payload"]["D"].__setitem__(2, "-1/10"), base=c_m1)
    add_attack("34_moment_zero_pivot", lambda c: c["certificate_payload"]["D"].__setitem__(8, "0"), base=c_m1)
    add_attack("35_moment_nonunit_L_diag", lambda c: c["certificate_payload"]["L"][1].__setitem__(1, "2"), base=c_m1)
    add_attack("36_moment_upper_tri_L", lambda c: c["certificate_payload"]["L"][0].__setitem__(1, "1/10"), base=c_m1)
    add_attack("37_moment_broken_word_symmetry", lambda c: c["certificate_payload"]["L"][5].__setitem__(0, "1/2"), base=c_m1)
    add_attack("38_moment_npa2_tampered_gap", lambda c: c["certificate_payload"].__setitem__("npa_gap", "1"), base=c_m2)

    # 39-42: Universal 4-vertex visibility dual & Tier-3 dual attacks
    add_attack("39_vis_dual_uniform_weights", lambda c: c["visibility_dual"].__setitem__("weights", ["1/4", "1/4", "1/4", "1/4"]))
    add_attack("40_vis_dual_duplicate_vertex", lambda c: c["visibility_dual"]["active_vertices"].__setitem__(1, c["visibility_dual"]["active_vertices"][0]))
    add_attack("41_vis_dual_invalid_vertex", lambda c: c["visibility_dual"]["active_vertices"][0].__setitem__(7, -1))
    add_attack("42_tier3_missing_subpayload", lambda c: c["certificate_payload"].pop("level_2_sos_exact"), base=c_t3)

    assert len(attacks) == 42
    for name, cand in attacks:
        with pytest.raises(ValueError, match="."):
            verify_normal_cone_certificate_exact(cand)
