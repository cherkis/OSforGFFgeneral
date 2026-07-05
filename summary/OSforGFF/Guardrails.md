# `Guardrails.lean` — Informal Summary

> **Source**: [`OSforGFF/Guardrails.lean`](../OSforGFF/Guardrails.lean)
> **Generated**: 2026-07-05 (regenerated from current source)

## Overview

This file is the build-enforced guardrail for the dimension-generic refactor. It contains no
`def` or `theorem` declarations: it is a flat sequence of `#guard_msgs` blocks, each wrapping a
`#print axioms` or `#check` command whose expected compiler output is frozen in the preceding
`/-- info: ... -/` docstring. Because the file is imported into the library and compiled by
`lake build`, any drift in a guarded fact makes the recorded message disagree with the actual
message, `#guard_msgs` reports a mismatch, and the build FAILS. It therefore mechanically
enforces two invariants for all six headline theorems at once:

1. **Axiom footprint.** Each `#print axioms` guard freezes the reachable-axiom list to exactly
   Lean's three core axioms — `propext`, `Classical.choice`, `Quot.sound` — and nothing else.
   A new custom `axiom` reachable from a headline, or a leaked `sorry` (which surfaces as
   `sorryAx`), would add an entry and break the guard.
2. **Statement type.** Each `#check` guard freezes the elaborated type of a headline theorem,
   so a change to its statement (measure, hypotheses, or conclusion) breaks the guard.

The single `import «OSforGFF».OS.Master` ([`OS/Master.lean`](../OSforGFF/OS/Master.lean)) brings
all six headlines into scope: the concrete `d = 4` master theorem, the dimension-generic master
theorem `_generic`, the all-dimensions corollary `_of_dim` (every `2 ≤ d ≤ 5`), and the concrete
`_dim3`, `_dim2`, `_dim5` instances. The opening comment records that the footprint being frozen
is the *actual* footprint of the pristine baseline, cleaner than earlier docs anticipated: the
previously-expected inherited axioms (`schwartz_nuclear`, `minlos_theorem`,
`differentiable_analyticAt_finDim`) are not reachable at the pinned dependency revisions, so the
guard freezes reality and will fail if any of them ever creeps back onto the import path.

## Status

**Main result**: Build-enforced freeze of the axiom footprint and statement type of all six
headline theorems; `lake build` fails on any drift.

**Length**: 85 lines, 11 guard commands (6 `#print axioms` axiom-footprint guards + 5 `#check`
statement-type guards), 0 declarations, 0 sorries.

---

### [Axiom-footprint guard — `d = 4` master theorem](../OSforGFF/Guardrails.lean#L32)

Freezes the reachable-axiom list of `OSforGFF.gaussianFreeField_satisfies_all_OS_axioms` (the
concrete `d = 4` headline) to Lean's three core axioms:

```lean
/-- info: 'OSforGFF.gaussianFreeField_satisfies_all_OS_axioms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Any additional axiom or a leaked `sorryAx` breaks the `#guard_msgs`.

---

### [Axiom-footprint guard — dimension-generic master theorem](../OSforGFF/Guardrails.lean#L37)

Freezes the reachable-axiom list of `OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_generic`
(the dimension-generic master theorem) to the same three core axioms
`[propext, Classical.choice, Quot.sound]`. This is the only headline with an axiom-footprint
guard but no separate `#check` type guard.

---

### [Goal-type guard — `d = 4` master theorem](../OSforGFF/Guardrails.lean#L42)

Pins the elaborated statement type of `OSforGFF.gaussianFreeField_satisfies_all_OS_axioms`:

```lean
/-- info: OSforGFF.gaussianFreeField_satisfies_all_OS_axioms : ∀ (m : ℝ) [inst : Fact (0 < m)], SatisfiesAllOS (μ_GFF 4 m) -/
```

The frozen conclusion is `SatisfiesAllOS (μ_GFF 4 m)` — the unified `μ_GFF d` measure at `d = 4`.

---

### [Axiom-footprint guard — three-dimensional instance](../OSforGFF/Guardrails.lean#L47)

Freezes the reachable-axiom list of `OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim3` to
`[propext, Classical.choice, Quot.sound]`.

---

### [Goal-type guard — three-dimensional headline](../OSforGFF/Guardrails.lean#L52)

Pins the statement type of `OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim3`:

```lean
/-- info: OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim3 : ∀ (m : ℝ) [inst : Fact (0 < m)], SatisfiesAllOS (μ_GFF 3 m) -/
```

Frozen conclusion: `SatisfiesAllOS (μ_GFF 3 m)`.

---

### [Axiom-footprint guard — two-dimensional instance](../OSforGFF/Guardrails.lean#L57)

Freezes the reachable-axiom list of `OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim2` to
`[propext, Classical.choice, Quot.sound]`.

---

### [Goal-type guard — two-dimensional headline](../OSforGFF/Guardrails.lean#L62)

Pins the statement type of `OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim2`:

```lean
/-- info: OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim2 : ∀ (m : ℝ) [inst : Fact (0 < m)], SatisfiesAllOS (μ_GFF 2 m) -/
```

Frozen conclusion: `SatisfiesAllOS (μ_GFF 2 m)`.

---

### [Axiom-footprint guard — five-dimensional instance](../OSforGFF/Guardrails.lean#L67)

Freezes the reachable-axiom list of `OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim5` to
`[propext, Classical.choice, Quot.sound]`.

---

### [Goal-type guard — five-dimensional headline](../OSforGFF/Guardrails.lean#L72)

Pins the statement type of `OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim5`:

```lean
/-- info: OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim5 : ∀ (m : ℝ) [inst : Fact (0 < m)], SatisfiesAllOS (μ_GFF 5 m) -/
```

Frozen conclusion: `SatisfiesAllOS (μ_GFF 5 m)`.

---

### [Axiom-footprint guard — all-dimensions corollary](../OSforGFF/Guardrails.lean#L77)

Freezes the reachable-axiom list of `OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_of_dim`
(the corollary covering every `2 ≤ d ≤ 5`) to `[propext, Classical.choice, Quot.sound]`.

---

### [Goal-type guard — all-dimensions corollary](../OSforGFF/Guardrails.lean#L82)

Pins the statement type of `OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_of_dim`, the only
headline quantified over the dimension `d`:

```lean
/-- info: OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_of_dim : ∀ (d : ℕ) [inst : Fact (2 ≤ d)] (m : ℝ)
  [inst_1 : Fact (0 < m)] [Fact (d ≤ 5)], SatisfiesAllOS (gaussianFreeField_free m) -/
```

The frozen conclusion is stated with the underlying `gaussianFreeField_free m` (the `μ_GFF`
simp-alias unfolded), under the dimension hypotheses `Fact (2 ≤ d)` and `Fact (d ≤ 5)`.

---

*This file has **0** definitions and **0** theorems/lemmas; it is **11** `#guard_msgs` guard
blocks (6 `#print axioms` + 5 `#check`) enforcing the axiom footprint and statement type of the
six headline theorems (0 with sorry).*
