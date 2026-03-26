# Refactoring Milestones for OSforGFFin3D

This is the short-form tracker for the full backlog in
`docs/refactoringTaskList.md`.

Use it to track batch-level progress and refactor outcomes without updating the
full file-by-file checklist every time.

## Status Legend

- [ ] not started
- [~] in progress
- [x] completed

## Milestones

### M0: Refactor conventions

- [x] Agree on the standard refactor pattern for long Lean proofs.
- [x] Keep theorem statements stable unless a rename is explicitly justified.
- [x] Use targeted file checks after each edited file.
- [x] Use full `lake build` after each completed milestone.

Working rules:

- Prefer `private lemma` / local helper extraction over rewriting a public proof
  end-to-end.
- Keep public theorem statements unchanged unless a rename or statement cleanup
  has a clear downstream reason.
- Move helper lemmas downward in the import graph whenever possible.
- Keep assembly files thin; avoid storing low-level technical lemmas in
  `OS*_GFF.lean`, `GaussianFreeField.lean`, or `GFFmaster.lean`.
- Replace migration-history prose with current 3D mathematical descriptions,
  keeping provenance notes only when they are still useful.

Per-file refactor sequence:

1. Read the file and identify repeated proof blocks, long local calculations,
   and misplaced helper lemmas.
2. Extract small helper lemmas with narrow scope first.
3. Shorten public theorem bodies to a readable proof skeleton.
4. Retain compatibility aliases only if they are still used downstream.
5. Run a targeted check on the edited file before moving on.

Validation sequence:

1. After each edited file, run a targeted check for that file.
2. After each completed milestone batch, run full `lake build`.
3. Only mark a milestone complete once both the doc cleanup and validation pass.

Exit criteria:

- A consistent pattern is being used for helper extraction, section layout,
  compatibility notes, and validation.

### M1: Covariance and mixed-representation core

Status: [x] completed on 2026-03-25.

Files:

- `OS3_MixedRepInfra.lean`
- `OS3_MixedRep.lean`
- `CovarianceMomentum.lean`
- `OS4_Clustering.lean`

Goals:

- [x] Split long proofs into named helper lemmas.
- [x] Centralize repeated domination, measurability, and prefactor bounds.
- [x] Replace migration-history prose with current mathematical descriptions.
- [x] Keep public theorems short and auditable.

Exit criteria:

- These four files no longer contain the largest copy-pasted proof blocks in the
  project.

### M2: Covariance spine and decomposition helpers

Status: [x] completed on 2026-03-25.

Files:

- `Parseval.lean`
- `Covariance.lean`
- `CovarianceR.lean`
- `OS1_GFF.lean`
- `OS3_CovarianceRP.lean`
- `SchwartzProdIntegrable.lean`
- `SpacetimeDecomp.lean`
- `L2TimeIntegral.lean`

Goals:

- [x] Factor reusable bilinear and integral-manipulation lemmas.
- [x] Reduce local proof setup duplication.
- [x] Make time/space decomposition utilities easier to reuse downstream.

Exit criteria:

- The covariance-facing files read as interface layers rather than proof dumps.

### M3: Axiom boundary cleanup

Status: [x] completed on 2026-03-25.

Files:

- `OS0_GFF.lean`
- `Minlos.lean`
- `NuclearSpace.lean`
- `MinlosAnalytic.lean`
- `SchwingerTwoPointFunction.lean`
- `OS_Axioms.lean`
- `GFFMconstruct.lean`
- `GaussianMoments.lean`
- `GFFIsGaussian.lean`

Goals:

- [x] Isolate genuine axioms in the smallest possible surface.
- [x] Move derived helper lemmas out of interface files when appropriate.
- [x] Shorten historical or compatibility-heavy commentary.

Exit criteria:

- The remaining axioms are easy to locate, minimal in scope, and clearly
  separated from derived infrastructure.

### M4: OS theorem assembly cleanup

Status: [x] completed on 2026-03-25.

Files:

- `OS2_GFF.lean`
- `OS3_GFF.lean`
- `OS4_MGF.lean`
- `OS4_Ergodicity.lean`
- `GaussianFreeField.lean`
- `GFFmaster.lean`

Goals:

- [x] Keep assembly files thin.
- [x] Push low-level helper lemmas back down the dependency graph.
- [x] Make each top-level theorem file read as a short proof assembly.

Exit criteria:

- Top-level theorem files are mostly orchestration and final statements.

### M5: Foundation and API consistency sweep

Status: [x] completed on 2026-03-25.

Files:

- `Basic.lean`
- `BesselFunction.lean`
- `ComplexTestFunction.lean`
- `DiscreteSymmetry.lean`
- `Euclidean.lean`
- `FourierTransforms.lean`
- `FrobeniusPositivity.lean`
- `FunctionalAnalysis.lean`
- `GaussianRBF.lean`
- `HadamardExp.lean`
- `LaplaceIntegral.lean`
- `PositiveDefinite.lean`
- `PositiveTimeTestFunction_real.lean`
- `QuantitativeDecay.lean`
- `SchurProduct.lean`
- `SchwartzTonelli.lean`
- `SchwartzTranslationDecay.lean`
- `Schwinger.lean`
- `TimeTranslation.lean`

Goals:

- [x] Normalize section layout and doc-comment style.
- [x] Consolidate small helper lemmas into the right foundational files.
- [x] Remove stale compatibility wording where the API is now stable.

Exit criteria:

- The lower-level library files expose a cleaner and more predictable API.

## Cross-Milestone Checks

- [ ] No new compatibility alias is introduced unless there is a concrete
      downstream need.
- [x] No public theorem file accumulates low-level technical helper lemmas.
- [x] The remaining axioms are only `differentiable_analyticAt_finDim`,
      `minlos_theorem`, and `schwartz_nuclear`, unless a new boundary is
      deliberately introduced.
- [x] Full `lake build` passes after each completed milestone.

## Current Suggested Next Step

- [x] Refactoring milestone sweep M0–M5 is complete.