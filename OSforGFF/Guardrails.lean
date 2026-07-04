/-
Build-enforced guardrails for the dimension-generic refactor.

This file is compiled as part of the library, so `lake build` is the enforcer: the build FAILS
here (via `#guard_msgs`) if any change

  * introduces a new `axiom` reachable from the master theorem, or
  * lets a `sorry` leak into the goal (surfaces as `sorryAx` in the axiom list), or
  * changes the master theorem's statement type.

## Status: ACTIVATED at Stage 0 (2026-07-02).

The frozen axiom footprint below is the *actual* footprint of the pristine 4D baseline
(`pre-unification-baseline`, commit 60ab679), built against the pinned deps
BochnerMinlos @ 1b56973 / GaussianField @ 36ae6dd: **only Lean's three core axioms**
(`propext`, `Classical.choice`, `Quot.sound`).

Note — this is cleaner than the earlier docs anticipated (they expected three inherited custom
axioms `schwartz_nuclear` / `minlos_theorem` / `differentiable_analyticAt_finDim`). At the pinned
revs none are reachable: `minlos_theorem` is a proven `theorem` (BochnerMinlos/Minlos/Main.lean),
the `schwartz_*` nuclear axioms live only in BochnerMinlos' `Test/` tree (off the import path),
and `differentiable_analyticAt_finDim` no longer exists. The guard freezes reality, so it will now
also fail if any of those dependency axioms ever creep back onto the import path.

Add an analogous frozen block per dimension (`OS_holds_2`, `OS_holds_3`, `OS_holds_4`) as those
headline theorems appear (Stage 1b onward).
-/
import «OSforGFF».OS.Master

-- ── Axiom-footprint guard (ACTIVATED) ────────────────────────────────────────
/-- info: 'OSforGFF.gaussianFreeField_satisfies_all_OS_axioms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OSforGFF.gaussianFreeField_satisfies_all_OS_axioms

-- ── Axiom-footprint guard for the dimension-generic master theorem ───────────
/-- info: 'OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_generic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_generic

-- ── Goal-type guard: pins the master theorem's statement (ACTIVATED) ──────────
/-- info: OSforGFF.gaussianFreeField_satisfies_all_OS_axioms : ∀ (m : ℝ) [inst : Fact (0 < m)], SatisfiesAllOS (μ_GFF m) -/
#guard_msgs in
#check @OSforGFF.gaussianFreeField_satisfies_all_OS_axioms

-- ── Axiom-footprint guard for the three-dimensional instance ─────────────────
/-- info: 'OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim3

-- ── Goal-type guard: pins the three-dimensional headline's statement ─────────
/-- info: OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim3 : ∀ (m : ℝ) [inst : Fact (0 < m)],
  SatisfiesAllOS (OSforGFF.μ_GFF3 m) -/
#guard_msgs in
#check @OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim3

-- ── Axiom-footprint guard for the two-dimensional instance ───────────────────
/-- info: 'OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim2

-- ── Goal-type guard: pins the two-dimensional headline's statement ───────────
/-- info: OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim2 : ∀ (m : ℝ) [inst : Fact (0 < m)],
  SatisfiesAllOS (OSforGFF.μ_GFF2 m) -/
#guard_msgs in
#check @OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim2

-- ── Axiom-footprint guard for the all-dimensions corollary ───────────────────
/-- info: 'OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_of_dim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_of_dim

-- ── Goal-type guard: pins the all-dimensions corollary's statement ───────────
/-- info: OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_of_dim : ∀ (d : ℕ) [inst : Fact (2 ≤ d)] (m : ℝ)
  [inst_1 : Fact (0 < m)] [Fact (d ≤ 5)], SatisfiesAllOS (gaussianFreeField_free m) -/
#guard_msgs in
#check @OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_of_dim
