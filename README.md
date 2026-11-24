# Exact-Q Sum-of-Squares Hierarchy on the Normal Cone of Q2222

Machine-checked Lean 4 formalization, zero-floating-point-trust exact-$\mathbb{Q}$ certificate verifier (guaranteed sound by Weak SDP Duality), and reproducible computational benchmarks for:

> **Exact-$\mathbb{Q}$ Sum-of-Squares Hierarchy on the Normal Cone of $\mathcal{Q}_{2222}$: Rational Extreme-Point Parameterization, Four-Tier NPA Separation, and Machine-Checked Visibility Optimality**

Directly advancing Wu, Xie, and Ramanathan (`arXiv:2611.27413`, Nov 2026) and Bamps & Pironio (*Phys. Rev. A* **91**, 052111, 2015).

## Key Results

1. **Dense Rational Extreme-Point Atlas & Universal 2-Square SOS (Theorem 3.1):**
   For every $k \in \mathbb{Q} \cap (1, 1+\sqrt{2})$, $\alpha(k) = \frac{2(1+2k-k^2)}{k^2+2k-1}$ and $\beta(k) = \frac{4(k^2+1)}{k^2+2k-1}$ satisfy $\beta^2 = 8 + 2\alpha^2$ identically, placing $p^*(k) \in \operatorname{ext}(\mathcal{Q}_{2222})$, $\{I_\alpha, S_\alpha, D_\alpha\}$, and every extreme ray of $\mathcal{N}_{\mathcal{Q}}(p^*(k))$ strictly in $\mathbb{Q}$. The universal identity $I_\alpha^2 + Q_\alpha^2 \equiv (8+2\alpha^2)I$ compresses Bamps--Pironio's 5-square SOS to an exact 2-square rational SOS.
2. **Tribonacci Octagon-to-Hexagon Phase Transition (Theorem 3.2):**
   The cleared-denominator $3\times 3$ facet concurrency determinant factors identically as $2(k^2+2k-1)^2(k^3-k^2-k-1)$, proving that the 2D normal-cone cross-section transitions sharply from an 8-vertex octagon ($k > k_{\mathrm{trib}}$) to a 6-vertex hexagon ($k < k_{\mathrm{trib}}$) at the Tribonacci constant $k_{\mathrm{trib}} \approx 1.839287$.
3. **$\mathcal{S}_4$-Subspace Collapse vs. Exact-$\mathbb{Q}$ Four-Tier NPA Separation (Theorem 3.3):**
   Restricting Level-$(1+AB)$ to the 4-operator $N_3$-free subspace $\mathcal{S}_4 = \operatorname{span}\{N_1, N_2, N_4, N_5\}$ collapses the SOS cone strictly onto the 1D rank-2 segment $\operatorname{conv}\{I_\alpha, \mathcal{B}_{\mathrm{Bob}}(\alpha)\} = [-8\alpha/\beta^2, 0]\times\{0\}$. Restoring the 5th annihilator $N_3$ inflates $\mathcal{N}_{\mathrm{SOS}}^{(1+AB)}(p^*(2))$ to a 2D curved spectrahedron ($80.0\%$ area), strictly inside $\mathcal{N}_{\mathrm{SOS}}^{(2)}(p^*(2))$ ($97.9\%$ area) and the octagon $\mathcal{P}(2)$. Every strict inclusion in $\emptyset = \mathcal{N}_{\mathrm{SOS}}^{(1)} \subsetneq \mathcal{N}_{\mathrm{SOS}}^{(1+AB)} \subsetneq \mathcal{N}_{\mathrm{SOS}}^{(2)} \subsetneq \mathcal{N}_{\mathcal{Q}}(p^*(2))$ is certified in exact $\mathbb{Q}$ via mutually exclusive SOS replays and strictly positive-definite $LDL^\top$ NPA moment matrices (Weak SDP Duality formalized in Lean 4 Theorem 20).
4. **Unique Global White-Noise Visibility Optimality (Theorem 3.4):**
   An explicit strictly positive 4-vertex rational LP dual certificate proves $v(\mathcal{B}) = \beta_{\mathrm{loc}}(\mathcal{B})/\beta_Q(\mathcal{B}) \ge (2+\alpha)/\beta$ throughout $\mathcal{N}_{\mathcal{Q}}(p^*(k))$, with equality uniquely at $(\eta,\zeta) = (0,0)$.

## Verification & Reproducibility

```bash
# 1. Re-run all 4 experiments and regenerate all 3 figures (~21s)
python scripts/run_all_experiments.py
python scripts/make_figures.py

# 2. Run the full Gate-2 verification harness:
#    - Lean 4 v4.35.0 kernel (20/20 theorems, 0 warnings, 0 sorry, 0 Classical.choice)
#    - 13/13 standalone exact-Q certificates (zero float trust, 4 sound modes)
#    - pytest suite (all 9 annihilators on 2-qubit states + 42 live adversarial attacks)
#    - SHA-256 artifact integrity manifest (36 files)
python scripts/verify_all.py
```

## License

MIT License (see `LICENSE`).
