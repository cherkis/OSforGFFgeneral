/-
Build-enforced guardrails for the dimension-generic refactor.

This file is compiled as part of the library, so `lake build` becomes the enforcer: once the
frozen blocks below are activated (Stage 0), the build FAILS here if any change

  * introduces a new `axiom` reachable from the master theorem, or
  * lets a `sorry` leak into the goal (surfaces as `sorryAx` in the axiom list), or
  * changes the master theorem's statement type.

## Activation (Stage 0 — needs the first clean build)

The exact axiom list is only known after building. At Stage 0:
  1. Build; read the `#print axioms` output produced below.
  2. Paste that exact line into the `/-- info: … -/` docstring of the frozen block.
  3. Uncomment `#guard_msgs in`. From then on, the compiler enforces it.

Until activated, the commands merely *print* — they do not fail the build.

Add an analogous frozen block per dimension (`OS_holds_2`, `OS_holds_3`, `OS_holds_4`) as those
headline theorems appear (Stage 1b onward).
-/
import «OSforGFF».OS.Master

-- ── Axiom-footprint guard (Stage 0: wrap with `#guard_msgs in`) ──────────────
#print axioms OSforGFF.gaussianFreeField_satisfies_all_OS_axioms

-- ── Goal-type guard: pins the master theorem's statement ─────────────────────
#check @OSforGFF.gaussianFreeField_satisfies_all_OS_axioms

/-
FROZEN FORM — activate at Stage 0 by filling the exact list, then delete this comment wrapper:

/-- info: 'OSforGFF.gaussianFreeField_satisfies_all_OS_axioms' depends on axioms:
[propext, Classical.choice, Quot.sound, <inherited BochnerMinlos axioms>] -/
#guard_msgs in
#print axioms OSforGFF.gaussianFreeField_satisfies_all_OS_axioms
-/
