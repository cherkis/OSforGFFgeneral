# Stage 2 (tentative) — the d = 3 Yukawa instance, planned for this branch

> **Status: tentative.** Written 2026-07-03 (design recon done on `dimension-generic`; no Stage-2
> Lean code exists yet). Stage 2 is to be executed **on this branch (`dimensions432`)** because it
> retains the build-enforced guards — `OSforGFF/Guardrails.lean` (`#guard_msgs` axiom/statement
> freeze) and `scripts/check-guardrails.sh` — which were removed from `dimension-generic` at
> `cb34bc1`. Companion project docs: top-level `plan.md` / `progress.md` (outside this repo).

## Before starting (resume-time decisions)

- Base here is `11ed3fb` (full dimension-generic library, verbatim 4D recovery, guards active).
  `dimension-generic` moved ahead with **documentation-only** commits: `ba63746` (README,
  import-graph `.dot`, `formalization.yaml`, ~20 `summary/*.md` rewrites) and any later summary-
  sweep commits. Decide whether to cherry-pick those doc commits onto this branch — but **never**
  `cb34bc1` (the scaffolding removal; the guards stay here). If cherry-picked, reconcile the
  README/docs sentences about guarding (manual on `dimension-generic`, build-enforced here).
- Toolchain/deps unchanged: `leanprover/lean4:v4.29.0`, deps pinned; the existing `.lake` caches
  remain valid per branch content.

## Design (settled by recon 2026-07-03; details in top-level `progress.md`)

**Obligation.** The class (`Covariance/Propagator.lean`) has exactly two fields; the d = 3
instance owes `Cprofile` and one evaluation:
`∀ r > 0, Cprofile r = properTimeCovariance 3 m r`, with
`properTimeCovariance d m r = ∫ t in Ioi 0, exp (-t·m²) · (4πt)^(-(d:ℝ)/2) · exp (-r²/(4t))`
and `Cprofile r = e^{-mr}/(4πr)` (Yukawa) away from `r = 0`.

**Route.** The read-only reference `OSforGFF2D3D/OSforGFFin3D` does NOT contain this evaluation in
elementary form: its Schwinger evaluation stops at symbolic `besselKhalf`
(`Momentum.lean:506`, its `BesselFunction.lean:1085`), and `K_{1/2}(z) = √(π/(2z))·e^{-z}` is
proven nowhere in that tree. So the evaluation is written fresh, mirroring this repo's own K₁
pattern (`General/BesselFunction.lean`: `bessel_symmetry_integral`, `schwingerIntegral_eq_besselK1`
— substitution `t = c·eᵘ` via `integral_image_eq_integral_deriv_smul_of_monotoneOn`, split-and-
reflect folding, `integrable_of_isBigO_exp_neg` estimates), **not** ported from the reference.

**Mathlib ingredients verified at the pin:** `integral_gaussian_Ioi`
(`∫_{Ioi 0} e^{-b·x²} = √(π/b)/2`), `Real.hasDerivAt_sinh`, `Real.cosh_sq` / `cosh_two_mul` /
`cosh_eq` / `sinh_eq`, `integral_image_eq_integral_deriv_smul_of_monotoneOn`,
`intervalIntegral.integral_Iic_add_Ioi`, `integral_comp_neg_Iic`, `integrable_of_isBigO_exp_neg`.

**Constant checks** (done): `√(2m/r)·2·√(π/(2mr)) = 2√π/r` and
`(4π)^{-3/2}·(2√π/r) = 1/(4πr)`.

All new code goes in a self-contained `OSforGFF/Instances/Dim3.lean` (split a support file only if
it balloons past ~450 lines). Exact statement shapes and tactic scripts are pinned
compiler-guided (`lean_multi_attempt` prototyping) at implementation time.

## Sub-steps (≈ equal effort; commit at the end of each green sub-step)

- [ ] **2a — fold lemma + integrability.**
      `∫_ℝ e^{-u/2}·e^{-z·cosh u} du = 2·∫_{Ioi 0} cosh(u/2)·e^{-z·cosh u} du` by split-at-0 +
      reflect + `cosh_eq` (mirror `bessel_symmetry_integral`); u-side integrability via
      `integrable_of_isBigO_exp_neg` — the weight satisfies `e^{u/2} ≤ e^u` on `u ≥ 0`, so the
      existing K₁ estimates (the `2u ≤ z·cosh u` bound) dominate a fortiori.
- [ ] **2b — Gaussian reduction.**
      `∫_{Ioi 0} cosh(u/2)·e^{-z·cosh u} du = √(π/(2z))·e^{-z}` via
      `cosh u = 1 + 2·sinh(u/2)²` (`Real.cosh_two_mul` + `cosh_sq`) and the change of variables
      `w = sinh(u/2)` (image of `Ioi 0` is `Ioi 0`), closed by `integral_gaussian_Ioi`.
- [ ] **2c — Schwinger → Yukawa + constant extraction.**
      COV `t = (r/2m)·eᵘ` (mirror `schwingerIntegral_eq_besselK1`; jacobian algebra in rpow since
      the weight is `t^{-3/2}`, not 4D's `t⁻²`):
      `∫_{Ioi 0} t^{-3/2}·e^{-m²t - r²/(4t)} dt = (2√π/r)·e^{-mr}`; then a
      `heatKernelProfile_3D` constant-extraction lemma and
      `properTimeCovariance_dim3_eq : properTimeCovariance 3 m r = e^{-mr}/(4πr)` for `r > 0`
      (`(4π)^{3/2} = 8π√π`).
- [ ] **2d — instance, headline, UV analog, wiring, guards.**
      `instance : Fact ((2:ℕ) ≤ 3)` and `Fact ((3:ℕ) ≤ 5)` (only the `STDimension = 4` versions
      exist, in `Spacetime/Basic.lean`); `instGFFPropagatorDim3` with
      `Cprofile r := if r = 0 then 0 else exp (-(m·r)) / (4·π·r)` and `schwinger_eq` from 2c
      (mirror `Instances/Dim4.lean`); `abbrev μ_GFF3 m := gaussianFreeField_free (d := 3) m`;
      headline in `OS/Master.lean` (additive change to a frozen-statement file — flag as
      intentional in the diff review):
      `theorem gaussianFreeField_satisfies_all_OS_axioms_dim3 (m) [Fact (0 < m)] :
         SatisfiesAllOS (μ_GFF3 m) := gaussianFreeField_satisfies_all_OS_axioms_generic m`;
      register `import «OSforGFF».Instances.Dim3` in root `OSforGFF.lean`; the d = 3
      UV-divergence analog (`e^{-mr}/(4πr) → ∞` as `r → 0⁺`, mirroring
      `freeCovariance_tendsto_atTop`); README + `docs/dimension_generic.md` rows +
      `summary/OSforGFF/Instances/Dim3.md`.
      **Guards (build-enforced on this branch):** add a frozen `#guard_msgs in #print axioms`
      block for the d = 3 headline to `OSforGFF/Guardrails.lean` (expected list: exactly
      `propext, Classical.choice, Quot.sound`), re-confirm the generic + 4D blocks, and run
      `scripts/check-guardrails.sh`.

## Stage-level verification

- `lake build` clean; no new `axiom`/`sorry`/`admit` (`grep -rn "axiom \|sorry\|admit" OSforGFF/`).
- Guardrails build green with the new d = 3 block (this replaces the manual scratch-file
  `#print axioms` discipline used on `dimension-generic`).
- `git diff pre-unification-baseline -- OSforGFF/OS/Axioms.lean OSforGFF/OS/Master.lean`:
  `Axioms.lean` unchanged from the reviewed d-threading; `Master.lean` changes purely additive;
  `μ_GFF m` still the goal of the 4D theorem.
- `OSforGFF2D3D/` remains untouched (permanent read-only reference).
- Update top-level `plan.md` (tick Stage 2) and `progress.md` (session log) at completion.
