"""Generate 3 publication-quality figures for Paper 08 from exact JSON outputs."""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.patches import Polygon

ROOT = Path(__file__).resolve().parent.parent
RES_DIR = ROOT / "results"
FIG_DIR = ROOT / "paper" / "figures"


def style_axes(ax: plt.Axes) -> None:
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    ax.grid(True, linestyle="--", alpha=0.35, linewidth=0.7)


def make_fig1(exp2: dict, exp3: dict) -> None:
    """Fig 1: Nested exact spectrahedra S_4-core < N_SOS^(1+AB) < N_SOS^(2) < P(2) & symmetric-axis spans."""
    fig, axes = plt.subplots(1, 2, figsize=(11.8, 5.1))

    # Panel (a): k = 2 nested spectrahedra inside 8-vertex octagon
    ax = axes[0]
    style_axes(ax)
    rec2 = next(r for r in exp2["records"] if r["k"] == "2")
    verts = [(float(Fraction(x)), float(Fraction(y))) for x, y in rec2["polygon_vertices"]]
    c2 = [(pt[0], pt[1]) for pt in exp3["contour_npa2"]]
    c1 = [(pt[0], pt[1]) for pt in exp3["contour_1ab"]]

    poly_oct = Polygon(verts, closed=True, facecolor="#dce8f7", edgecolor="#1f4e78", linewidth=2.0, alpha=0.72,
                       label=r"True 8-vertex octagon $\mathcal{P}(2)$ (area $1.812$)")
    poly_npa2 = Polygon(c2, closed=True, facecolor="#c7ebd1", edgecolor="#1b7837", linewidth=1.7, alpha=0.75,
                        label=rf"NPA-2 spectrahedron $\mathcal{{N}}_{{\mathrm{{SOS}}}}^{{(2)}}$ ({100*exp3['area_fraction_npa2']:.1f}% area)")
    poly_1ab = Polygon(c1, closed=True, facecolor="#fde0b8", edgecolor="#d95f02", linewidth=1.7, alpha=0.82,
                       label=rf"Full Level-$(1+AB)$ $\mathcal{{N}}_{{\mathrm{{SOS}}}}^{{(1+AB)}}$ ({100*exp3['area_fraction_1ab']:.1f}% area)")
    ax.add_patch(poly_oct)
    ax.add_patch(poly_npa2)
    ax.add_patch(poly_1ab)

    ax.scatter([p[0] for p in verts], [p[1] for p in verts], color="#1f4e78", s=34, zorder=5)

    # 1D S_4-subspace rank-2 core [-7/25, 0] x {0}
    eta_s4_min = float(Fraction(rec2["eta_s4_min"]))
    ax.plot([eta_s4_min, 0.0], [0.0, 0.0], color="#c91818", linewidth=4.0, solid_capstyle="round", zorder=8,
            label=r"$\mathcal{S}_4$-subspace 1D core $[-\frac{8\alpha}{\beta^2}, 0]\times\{0\}$ (rank-2)")
    ax.scatter([0.0], [0.0], color="#c91818", marker="*", s=165, edgecolor="#111111", linewidth=0.7, zorder=10,
               label=r"$I_\alpha$ $(0,0)$ & $\mathcal{B}_{\mathrm{Bob}}$ $(-\frac{7}{25},0)$ (2-sq SOS)")
    ax.scatter([eta_s4_min], [0.0], color="#ff7f0e", marker="D", s=60, edgecolor="#111111", linewidth=0.7, zorder=10)

    # Overlay exact-Q certified Tier-2 (5-sq), Tier-3 (dual-certified), and Tier-4 (NPA-2 gap) markers
    ax.scatter([0.5, 0.0, 0.2], [0.0, 0.5, 0.2], color="#d95f02", marker="o", s=46, edgecolor="#111111", linewidth=0.6, zorder=9,
               label=r"Exact-$\mathbb{Q}$ 5-sq Level-$(1+AB)$ SOS")
    ax.scatter([13/20, -9/10, 0.0], [0.0, 0.0, 7/10], color="#1b7837", marker="^", s=62, edgecolor="#111111", linewidth=0.6, zorder=9,
               label=r"Dual-certified Tier-3 ($1+AB$ gap + NPA-2 SOS)")
    ax.scatter([21/65, -14/15], [49/65, 0.0], color="#7b3294", marker="X", s=64, edgecolor="#111111", linewidth=0.6, zorder=9,
               label=r"Exact-$\mathbb{Q}$ Tier-4 ($13\times 13$ NPA-2 gap)")

    ax.axhline(0.0, color="#666666", linewidth=0.7, linestyle=":")
    ax.axvline(0.0, color="#666666", linewidth=0.7, linestyle=":")
    ax.set_xlabel(r"Symmetric tangent coordinate $\eta$ ($S_\alpha$)", fontsize=10)
    ax.set_ylabel(r"Antisymmetric tangent coordinate $\zeta$ ($D_\alpha$)", fontsize=10)
    ax.set_title(r"(a) Nested Exact Spectrahedra Inside $\mathcal{P}(2)$ ($\alpha=\frac{2}{7}$)", fontsize=10.2, fontweight="bold")
    ax.set_xlim(-1.06, 0.84)
    ax.set_ylim(-0.96, 0.96)
    ax.legend(loc="upper center", bbox_to_anchor=(0.5, -0.16), ncol=1, fontsize=7.3, frameon=True, framealpha=0.95)

    # Panel (b): Symmetric-axis spans across alpha(k) (S_4 1D core vs full 1+AB vs full polygon)
    ax = axes[1]
    style_axes(ax)
    alphas = [r["alpha_float"] for r in exp2["records"]]
    eta_lo = [float(Fraction(r["eta_loc_min"])) for r in exp2["records"]]
    eta_hi = [float(Fraction(r["eta_loc_max"])) for r in exp2["records"]]
    eta_1ab_lo = [r["eta_1ab_full_min_approx"] for r in exp2["records"]]
    eta_1ab_hi = [r["eta_1ab_full_max_approx"] for r in exp2["records"]]
    eta_s4_lo = [float(Fraction(r["eta_s4_min"])) for r in exp2["records"]]

    ax.fill_between(alphas, eta_lo, eta_hi, color="#dce8f7", alpha=0.80,
                    label=r"Full normal-cone $\eta$-span $[\eta_{\mathrm{loc}}^-, \eta_{\mathrm{loc}}^+]$")
    ax.plot(alphas, eta_lo, color="#1f4e78", linewidth=1.6, linestyle="--")
    ax.plot(alphas, eta_hi, color="#1f4e78", linewidth=1.6, linestyle="--")

    ax.fill_between(alphas, eta_1ab_lo, eta_1ab_hi, color="#fde0b8", alpha=0.85,
                    label=r"Full 5-op Level-$(1+AB)$ span (with $N_3$)")
    ax.plot(alphas, eta_1ab_lo, color="#d95f02", marker="s", linewidth=1.8, markersize=4.8)
    ax.plot(alphas, eta_1ab_hi, color="#d95f02", marker="s", linewidth=1.8, markersize=4.8)

    ax.fill_between(alphas, eta_s4_lo, [0.0] * len(alphas), color="#f4b6b6", alpha=0.85,
                    label=r"$\mathcal{S}_4$-subspace 1D collapse $[-\frac{8\alpha}{\beta^2}, 0]$ (without $N_3$)")
    ax.plot(alphas, eta_s4_lo, color="#c91818", marker="o", linewidth=1.8, markersize=5.0)
    ax.plot(alphas, [0.0] * len(alphas), color="#c91818", linewidth=1.8)

    alpha_trib = exp2["tribonacci_transition_alpha_approx"]
    ax.axvline(alpha_trib, color="#333333", linestyle=":", linewidth=1.2)
    ax.text(alpha_trib + 0.025, 0.72, r"Tribonacci $\alpha_{\mathrm{trib}} \approx 0.4275$" + "\n(octagon $\\to$ hexagon)",
            fontsize=7.8, color="#222222", bbox=dict(boxstyle="round,pad=0.2", fc="white", ec="#cccccc", alpha=0.85))

    ax.set_xlabel(r"Tilted-CHSH parameter $\alpha(k) \in (0, 2)$", fontsize=10)
    ax.set_ylabel(r"Symmetric coordinate $\eta$ (at $\zeta = 0$)", fontsize=10)
    ax.set_title(r"(b) $\mathcal{S}_4$ Collapse vs. Full $(1+AB)$ Inflation Across $\alpha$", fontsize=10.2, fontweight="bold")
    ax.set_xlim(0.05, 1.38)
    ax.set_ylim(-1.18, 0.94)
    ax.legend(loc="upper center", bbox_to_anchor=(0.5, -0.16), ncol=1, fontsize=7.6, frameon=True, framealpha=0.95)

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig1_normal_cone_collapse.png", dpi=260, bbox_inches="tight")
    plt.close(fig)


def make_fig2(exp3: dict) -> None:
    """Fig 2: Quantitative 4-tier Clarabel NPA-(1+AB) vs NPA-2 gaps across P(2)."""
    fig, ax = plt.subplots(figsize=(10.6, 4.5))
    style_axes(ax)

    probes = exp3["probes"]
    keep = [
        "alice_tilted_origin",
        "bob_tilted_s4_edge",
        "pos_eta_1_2",
        "neg_eta_4_5",
        "zeta_1_2",
        "tier3_pos_eta_13_20",
        "tier3_neg_eta_9_10",
        "tier3_zeta_7_10",
        "octagon_V1",
        "zeta_boundary_7_9",
        "octagon_V5",
        "octagon_V2",
    ]
    label_map = {
        "alice_tilted_origin": r"$I_\alpha$" + "\n(0,0)",
        "bob_tilted_s4_edge": r"$\mathcal{B}_{\mathrm{Bob}}$" + "\n(-7/25,0)",
        "pos_eta_1_2": r"Interior" + "\n(1/2,0)",
        "neg_eta_4_5": r"Interior" + "\n(-4/5,0)",
        "zeta_1_2": r"Interior" + "\n(0,1/2)",
        "tier3_pos_eta_13_20": r"Tier-3" + "\n(13/20,0)",
        "tier3_neg_eta_9_10": r"Tier-3" + "\n(-9/10,0)",
        "tier3_zeta_7_10": r"Tier-3" + "\n(0,7/10)",
        "octagon_V1": r"Vertex" + "\n$V_1$",
        "zeta_boundary_7_9": r"Edge" + "\n(0,7/9)",
        "octagon_V5": r"Vertex" + "\n$V_5$",
        "octagon_V2": r"Vertex" + "\n$V_2$",
    }
    selected = [next(p for p in probes if p["label"] == k) for k in keep]
    x = np.arange(len(selected))
    w = 0.36
    g1 = [max(1e-10, p["npa_1ab_gap"]) for p in selected]
    g2 = [max(1e-10, p["npa_2_gap"]) for p in selected]

    ax.bar(x - w / 2, g1, width=w, color="#d95f02", edgecolor="#222222", linewidth=0.75,
           label=r"NPA-$(1+AB)$ primal gap $\max(10^{-10}, \beta_{\mathrm{NPA}}^{(1+AB)} - \beta_Q)$")
    ax.bar(x + w / 2, g2, width=w, color="#1b7837", edgecolor="#222222", linewidth=0.75,
           label=r"NPA-2 primal gap $\max(10^{-10}, \beta_{\mathrm{NPA}}^{(2)} - \beta_Q)$")

    ax.set_yscale("log")
    ax.axhline(1e-6, color="#444444", linestyle="--", linewidth=1.0, label=r"Tightness threshold ($10^{-6}$)")
    ax.axvline(4.5, color="#888888", linestyle=":", linewidth=1.0)
    ax.axvline(8.5, color="#888888", linestyle=":", linewidth=1.0)

    ax.text(2.0, 9.5e-2, "Tier 2: 1+AB & NPA-2 tight", ha="center", fontsize=8.3, fontweight="bold", color="#b34d00")
    ax.text(6.5, 9.5e-2, "Tier 3: 1+AB gap, NPA-2 tight", ha="center", fontsize=8.3, fontweight="bold", color="#1b7837")
    ax.text(10.0, 9.5e-2, "Tier 4: NPA-2 gap", ha="center", fontsize=8.3, fontweight="bold", color="#6a1b9a")

    ax.set_xticks(x)
    ax.set_xticklabels([label_map[k] for k in keep], fontsize=7.9)
    ax.set_ylabel(r"NPA relaxation gap $\beta_{\mathrm{NPA}} - \beta_Q$", fontsize=9.8)
    ax.set_ylim(4e-11, 2.6e-1)
    ax.set_title(r"Strict 4-Tier NPA Separation Across $\mathcal{P}(2)$ ($\alpha = 2/7, \beta = 20/7$)",
                 fontsize=10.4, fontweight="bold")
    ax.legend(loc="upper left", bbox_to_anchor=(0.01, 0.87), fontsize=7.9, frameon=True, framealpha=0.95)

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig2_npa_hierarchy_separation.png", dpi=260, bbox_inches="tight")
    plt.close(fig)


def make_fig3(exp2: dict, exp4: dict) -> None:
    """Fig 3: Theorem 3.4 white-noise visibility landscape inside octagon + optimal curve across alpha."""
    fig, axes = plt.subplots(1, 2, figsize=(11.6, 4.5))

    ax = axes[0]
    style_axes(ax)
    grid = exp4["k2_grid"]
    xs = [pt["eta"] for pt in grid]
    ys = [pt["zeta"] for pt in grid]
    vs = [pt["vis"] for pt in grid]
    sc = ax.scatter(xs, ys, c=vs, cmap="viridis_r", s=24, vmin=0.80, vmax=1.00, edgecolors="none")
    cbar = plt.colorbar(sc, ax=ax, pad=0.02)
    cbar.set_label(r"White-noise visibility $v(\eta,\zeta) = \beta_{\mathrm{loc}}/\beta_Q$", fontsize=9.2)

    rec2 = next(r for r in exp2["records"] if r["k"] == "2")
    verts = [(float(Fraction(x)), float(Fraction(y))) for x, y in rec2["polygon_vertices"]]
    poly = Polygon(verts, closed=True, facecolor="none", edgecolor="#111111", linewidth=1.8)
    ax.add_patch(poly)
    ax.scatter([0.0], [0.0], color="#ff2222", marker="*", s=190, edgecolor="#ffffff", linewidth=0.8, zorder=8,
               label=r"Unique global min $I_\alpha$: $v^* = \frac{4}{5} = 0.80$")
    ax.set_xlabel(r"Symmetric tangent coordinate $\eta$", fontsize=10)
    ax.set_ylabel(r"Antisymmetric tangent coordinate $\zeta$", fontsize=10)
    ax.set_title(r"(a) Exact Visibility Landscape on $\mathcal{N}_{\mathcal{Q}}(p^*(2))$", fontsize=10.2, fontweight="bold")
    ax.set_xlim(-1.05, 0.82)
    ax.set_ylim(-0.95, 0.95)
    ax.legend(loc="lower left", fontsize=8.0, frameon=True, framealpha=0.94)

    ax = axes[1]
    style_axes(ax)
    a_dense = np.linspace(0.0, 1.98, 200)
    v_dense = (2.0 + a_dense) / np.sqrt(8.0 + 2.0 * a_dense * a_dense)
    ax.plot(a_dense, v_dense, color="#1f77b4", linewidth=2.2,
            label=r"Theorem 3.4 exact lower bound $v^*(\alpha) = \frac{2+\alpha}{\sqrt{8+2\alpha^2}}$")

    lp_a = [float(Fraction(r["alpha"])) for r in exp4["lp_checks"]]
    lp_v = [r["lp_min_vis"] for r in exp4["lp_checks"]]
    ax.scatter(lp_a, lp_v, color="#d62728", marker="o", s=58, zorder=6,
               label=r"Certified rational $p^*(k)$ LP + 4-vertex dual optimum")

    bob_v = []
    for r in exp4["lp_checks"]:
        a = Fraction(r["alpha"])
        b = Fraction(r["beta"])
        bq_bob = Fraction(8, 1) / b
        bl_bob = max(Fraction(2, 1), (4 * a * b + 16 - 4 * a * a) / (b * b))
        bob_v.append(float(bl_bob / bq_bob))
    ax.scatter(lp_a, bob_v, color="#ff7f0e", marker="^", s=62, zorder=6,
               label=r"Bob-tilted endpoint $\mathcal{B}_{\mathrm{Bob}}$ ($\eta = -8\alpha/\beta^2$, strictly worse)")

    ax.axhline(1.0 / np.sqrt(2.0), color="#666666", linestyle=":", linewidth=1.0,
               label=r"CHSH limit $1/\sqrt{2} \approx 0.7071$ ($\alpha \to 0$)")
    ax.set_xlabel(r"Tilted-CHSH parameter $\alpha \in (0, 2)$", fontsize=10)
    ax.set_ylabel(r"White-noise visibility threshold $v = \beta_{\mathrm{loc}} / \beta_Q$", fontsize=10)
    ax.set_title(r"(b) Unique Global Visibility Optimality Across $\alpha \in (0, 2)$", fontsize=10.2, fontweight="bold")
    ax.set_xlim(-0.04, 2.02)
    ax.set_ylim(0.69, 1.02)
    ax.legend(loc="lower right", fontsize=7.6, frameon=True, framealpha=0.94)

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig3_visibility_optimality.png", dpi=260, bbox_inches="tight")
    plt.close(fig)


def main() -> None:
    FIG_DIR.mkdir(parents=True, exist_ok=True)
    exp2 = json.loads((RES_DIR / "exp2_octagon_geometry_and_collapse.json").read_text(encoding="utf-8"))
    exp3 = json.loads((RES_DIR / "exp3_npa_hierarchy_phase_map.json").read_text(encoding="utf-8"))
    exp4 = json.loads((RES_DIR / "exp4_visibility_optimality_landscape.json").read_text(encoding="utf-8"))

    make_fig1(exp2, exp3)
    make_fig2(exp3)
    make_fig3(exp2, exp4)
    print(f"Generated 3 Paper 08 figures in {FIG_DIR}")


if __name__ == "__main__":
    main()
