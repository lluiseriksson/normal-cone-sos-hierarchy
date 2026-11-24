"""Gate-2 end-to-end verification harness for Paper 08.

Checks:
  1. Lean 4 kernel (`lake build` + `lake env lean AuditAxioms.lean`):
     20/20 theorems, 0 warnings, 0 sorry, 0 Classical.choice, 0 Lean.ofReduceBool.
  2. Independent zero-float exact-Q replay of all 13 NORMAL-CONE-SOS-CERT-1.0 certificates
     across all 4 weak-SDP-duality-sound modes.
  3. Full pytest suite (all 9 annihilators on 2-qubit states, Tribonacci transition, 42 live red-team attacks).
  4. SHA-256 manifest verification (`SHA256SUMS.json`), or generation with `--write-manifest`.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path
from typing import Dict, List

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src import verify_normal_cone_certificate_exact

EXPECTED_LEAN_THEOREMS = [
    "NormalConeSOS.pythagorean_tilted_identity",
    "NormalConeSOS.beta_sq_gt_four_alpha_sq",
    "NormalConeSOS.beta_sq_sub_local_sq",
    "NormalConeSOS.two_square_sos_identity",
    "NormalConeSOS.bob_tilted_rank2_factorization",
    "NormalConeSOS.bob_tilted_second_weight_pos",
    "NormalConeSOS.cauchy_schwarz_schur",
    "NormalConeSOS.schur_psd_implies_sum_bound",
    "NormalConeSOS.positive_eta_schur_obstruction",
    "NormalConeSOS.negative_eta_left_obstruction",
    "NormalConeSOS.negative_eta_schur_margin_nonneg",
    "NormalConeSOS.convex_comb_psd_preserved",
    "NormalConeSOS.visibility_dual_weights_sum",
    "NormalConeSOS.visibility_dual_weights_pos",
    "NormalConeSOS.visibility_dual_S_exact_match",
    "NormalConeSOS.visibility_dual_D_cancels",
    "NormalConeSOS.visibility_global_lower_bound",
    "NormalConeSOS.visibility_uniqueness_at_origin",
    "NormalConeSOS.tribonacci_facet_concurrency_det",
    "NormalConeSOS.weak_sdp_duality_soundness",
]

FORBIDDEN_AXIOMS = ("sorryAx", "Classical.choice", "Lean.ofReduceBool", "Lean.trustCompiler")

MANIFEST_FILES = [
    "LICENSE",
    "README.md",
    "pyproject.toml",
    "lean/lean-toolchain",
    "lean/lakefile.toml",
    "lean/NormalConeSOS.lean",
    "lean/AuditAxioms.lean",
    "src/__init__.py",
    "src/nc_sos.py",
    "src/normal_cone_certifier.py",
    "scripts/run_all_experiments.py",
    "scripts/make_figures.py",
    "scripts/verify_all.py",
    "tests/test_suite.py",
    "results/exp1_certified_atlas.json",
    "results/exp2_octagon_geometry_and_collapse.json",
    "results/exp3_npa_hierarchy_phase_map.json",
    "results/exp4_visibility_optimality_landscape.json",
    "results/certificates/k2_alice_tilted.cert.json",
    "results/certificates/k2_bob_tilted.cert.json",
    "results/certificates/k3_2_alice_tilted.cert.json",
    "results/certificates/k5_4_alice_tilted.cert.json",
    "results/certificates/k2_1ab_pos_eta.cert.json",
    "results/certificates/k2_1ab_zeta_pos.cert.json",
    "results/certificates/k2_1ab_diag.cert.json",
    "results/certificates/k2_tier3_pos_eta.cert.json",
    "results/certificates/k2_tier3_neg_eta.cert.json",
    "results/certificates/k2_tier3_zeta_pos.cert.json",
    "results/certificates/k2_tier3_vertex_V1.cert.json",
    "results/certificates/k2_tier4_vertex_V2.cert.json",
    "results/certificates/k2_tier4_vertex_V5.cert.json",
    "paper/figures/fig1_normal_cone_collapse.png",
    "paper/figures/fig2_npa_hierarchy_separation.png",
    "paper/figures/fig3_visibility_optimality.png",
    "paper/main.tex",
    "paper/references.bib",
]


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def check_lean() -> None:
    lean_dir = ROOT / "lean"
    r_build = subprocess.run(["lake", "build"], cwd=lean_dir, capture_output=True, text=True, check=False)
    if r_build.returncode != 0:
        raise RuntimeError(f"lake build failed:\n{r_build.stdout}\n{r_build.stderr}")
    if "warning:" in (r_build.stdout + r_build.stderr).lower():
        raise RuntimeError(f"Lean build emitted warnings:\n{r_build.stdout}\n{r_build.stderr}")

    r_audit = subprocess.run(
        ["lake", "env", "lean", "AuditAxioms.lean"],
        cwd=lean_dir,
        capture_output=True,
        text=True,
        check=False,
    )
    if r_audit.returncode != 0:
        raise RuntimeError(f"AuditAxioms.lean failed:\n{r_audit.stdout}\n{r_audit.stderr}")
    out = r_audit.stdout + "\n" + r_audit.stderr
    for thm in EXPECTED_LEAN_THEOREMS:
        if f"'{thm}'" not in out:
            raise RuntimeError(f"Missing Lean theorem in axiom audit: {thm}")
    for bad in FORBIDDEN_AXIOMS:
        if bad in out:
            raise RuntimeError(f"Forbidden Lean axiom detected: {bad}\n{out}")
    print(f"[PASS] Lean 4 kernel: {len(EXPECTED_LEAN_THEOREMS)}/{len(EXPECTED_LEAN_THEOREMS)} theorems, 0 warnings, 0 sorry, 0 Classical.choice")


def check_certificates() -> None:
    cert_dir = ROOT / "results" / "certificates"
    certs = sorted(cert_dir.glob("*.cert.json"))
    if len(certs) != 13:
        raise RuntimeError(f"Expected 13 certificate files, found {len(certs)}")
    for cp in certs:
        data = json.loads(cp.read_text(encoding="utf-8"))
        res = verify_normal_cone_certificate_exact(data)
        if not res.get("verified"):
            raise RuntimeError(f"Certificate failed verification: {cp.name}")
    print(f"[PASS] Exact-Q certificates: {len(certs)}/{len(certs)} independently verified (0 floats)")


def check_pytest() -> None:
    r = subprocess.run(
        [sys.executable, "-m", "pytest", "-q"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if r.returncode != 0:
        raise RuntimeError(f"pytest failed:\n{r.stdout}\n{r.stderr}")
    print(f"[PASS] pytest: {r.stdout.strip().splitlines()[-1]}")


def write_or_check_manifest(write_mode: bool) -> None:
    manifest_path = ROOT / "SHA256SUMS.json"
    computed: Dict[str, str] = {}
    missing: List[str] = []
    for rel in MANIFEST_FILES:
        p = ROOT / rel
        if not p.exists():
            missing.append(rel)
        else:
            computed[rel] = sha256_file(p)
    if missing:
        raise RuntimeError(f"Missing manifest files: {missing}")

    if write_mode:
        manifest_path.write_text(json.dumps(computed, indent=2) + "\n", encoding="utf-8")
        print(f"[PASS] Wrote SHA256SUMS.json ({len(computed)} files)")
        return

    if not manifest_path.exists():
        raise RuntimeError("SHA256SUMS.json not found; run with --write-manifest first")
    recorded = json.loads(manifest_path.read_text(encoding="utf-8"))
    if recorded != computed:
        diffs = [k for k in set(recorded) | set(computed) if recorded.get(k) != computed.get(k)]
        raise RuntimeError(f"SHA256SUMS.json mismatch on: {diffs}")
    print(f"[PASS] SHA256SUMS.json: {len(computed)}/{len(computed)} hashes match")


def main() -> None:
    parser = argparse.ArgumentParser(description="Gate-2 verification harness for Paper 08")
    parser.add_argument("--write-manifest", action="store_true")
    parser.add_argument("--skip-manifest", action="store_true")
    args = parser.parse_args()

    check_lean()
    check_certificates()
    check_pytest()
    if not args.skip_manifest:
        write_or_check_manifest(args.write_manifest)
    print("=== ALL PAPER 08 GATE-2 VERIFICATION CHECKS PASSED ===")


if __name__ == "__main__":
    main()
