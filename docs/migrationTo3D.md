# Migration Plan to 3D

This document turns the high-level goal in [changingTo3D.md](changingTo3D.md) into a concrete
work plan for the `OSforGFFin3D` tree.

## Goal

The target state is:

- **Standalone branch:** `OSforGFFin3D` stands on its own and does not depend on `OSforGFF` for active
  definitions, proofs, or imports.
- **Essential (d = 3):** formulas that evaluate dimensionally are correct for spacetime dimension `3`.
- **Spatial (d - 1 = 2):** proofs that depend on the spatial dimension use dimension `2` explicitly,
  or are rewritten to use `SpatialCoords` / `STDimension - 1` generically.
- **Structural:** files that should be dimension-agnostic depend only on `OSforGFFin3D.*` and do not
  silently reuse the original 4D development.

In particular, a successful migration is **not** just “the workspace builds with `STDimension := 3`”.
It must build as a self-contained 3D project whose mathematical content is carried by the
`OSforGFFin3D` tree itself.

## Current Verified Status

These items are already in place:

- `Basic.lean` sets `STDimension := 3`.
- The Bessel layer has been ported to the half-order kernel via `besselKhalf`.
- `CovarianceMomentum.lean` now contains a 3D covariance core, including the 3D Bessel formula,
  exponential decay, polynomial decay, and kernel integrability statements.
- `lake build` currently succeeds for the whole workspace.

However, the project is **not yet semantically migrated**. Many downstream files still import
`OSforGFF.*`, still describe the 4D `K₁` kernel, or still hard-code `Fin 4` / `Fin 3` decompositions.

The main standing requirement is therefore:

- remove the dependency of `OSforGFFin3D` on `OSforGFF` as an implementation crutch;
- re-prove or port the needed results inside `OSforGFFin3D`;
- ensure that a future reader can treat `OSforGFFin3D` as an independent project rather than a thin
  wrapper around the original 4D branch.

## Main Remaining Gaps

### 1. Downstream import graph still points to 4D modules

Representative files:

- `Parseval.lean`
- `Covariance.lean`
- `CovarianceR.lean`
- `OS3_MixedRepInfra.lean`
- `OS3_MixedRep.lean`
- `OS3_CovarianceRP.lean`
- `OS1_GFF.lean`
- `OS4_Clustering.lean`
- `OS4_MGF.lean`
- `OS4_Ergodicity.lean`
- assembly modules such as `OS3_GFF.lean`, `GaussianFreeField.lean`, `GFFmaster.lean`

As long as these files import `OSforGFF.*`, the 3D branch is building partly by reusing the original
4D proofs rather than proving the 3D branch end-to-end. This is the main reason the project does not
yet stand on its own.

### 2. Hard-coded spacetime/spatial coordinates remain

Representative files:

- `SchwartzProdIntegrable.lean` still defines `SpatialCoords3 := EuclideanSpace ℝ (Fin 3)` and builds
  spacetime points using `Fin 4`.
- `SpacetimeDecomp.lean` still expands norms using `Fin.sum_univ_four`.
- `OS4_Clustering.lean` still uses `Fin.sum_univ_four` in time-shift norm lemmas.

These are incompatible with the intended spacetime dimension `3` and spatial dimension `2`.

### 3. Several files still encode 4D mathematics in statements, proofs, or documentation

Representative symptoms:

- references to the `K₁` kernel instead of `besselKhalf`
- comments or theorem docs stating “4D spacetime”
- formulas specialized to `(2π)^4`, `1/(16π² t²)`, or `Fin 4`

This is most relevant in:

- `Parseval.lean`
- `OS3_MixedRepInfra.lean`
- `OS3_MixedRep.lean`
- `OS3_CovarianceRP.lean`
- `OS1_GFF.lean`
- `OS4_Clustering.lean`

## Migration Principles

- Do not modify files in `OSforGFF/`.
- Prefer migrating the 3D import graph rather than adding compatibility shims.
- Treat every `import OSforGFF.*` inside `OSforGFFin3D` as technical debt to be eliminated.
- If a 3D file currently depends on a theorem that only exists in `OSforGFF`, the default action is to
  port or reconstruct that theorem inside `OSforGFFin3D`, not to preserve the old import indefinitely.
- Preserve theorem names only when they are already used downstream and renaming would create churn.
  If a compatibility name is kept, its statement and docstring must still be mathematically correct.
- Stabilize lower layers first, then migrate downstream consumers.
- Rebuild after each phase or sub-phase rather than attempting a single large rewrite.

## Recommended Phase Order

### Phase 1: Finish the core covariance dependency spine

Objective: make the files immediately downstream of `CovarianceMomentum.lean` depend on the 3D branch.

Target files:

- `Parseval.lean`
- `Covariance.lean`
- `CovarianceR.lean`

Tasks:

- Replace `import OSforGFF.*` with `import OSforGFFin3D.*` where the corresponding 3D file exists.
- Replace stale textual references to the 4D `K₁` form with the 3D `besselKhalf` / `K_{1/2}` form.
- Recheck any normalization lemmas involving `(2π)^d` to ensure they are stated via `STDimension` or are
  explicitly correct for `d = 3`.
- Confirm that `Covariance.lean` uses the 3D `freeCovariance` and not the old branch via imports.

Acceptance criteria:

- These three files import only `OSforGFFin3D.*` and `Mathlib.*`.
- Their key theorems compile unchanged or with minimal proof repair.
- `lake build OSforGFFin3D.Parseval`, `lake build OSforGFFin3D.Covariance`, and
  `lake build OSforGFFin3D.CovarianceR` all succeed.
- No theorem in this phase is justified by re-importing the 4D branch behind the scenes.

### Phase 2: Port the mixed-representation branch

Objective: migrate the OS3 analytic/reflection-positivity bridge away from the 4D branch.

Target files:

- `OS3_MixedRepInfra.lean`
- `OS3_MixedRep.lean`
- `OS3_CovarianceRP.lean`

Tasks:

- Replace old imports with `OSforGFFin3D.*`.
- Update any 4D heat-kernel simplifications to the 3D form.
- Recheck the Schwinger-to-Laplace reductions so they match the already-ported 3D covariance core.
- Fix any explicit references to 4D codimension or 4D momentum decompositions in comments and proofs.

Expected difficulty:

- High. These files contain explicit dimension-dependent simplifications and are the most likely source of
  nontrivial proof repair.

Acceptance criteria:

- All three files compile against the 3D branch only.
- No formulas in these files still rely on 4D heat-kernel constants or `K₁`.
- Their imports come exclusively from `OSforGFFin3D.*` and `Mathlib.*`.

### Phase 3: Replace hard-coded spatial/spacetime decompositions

Objective: remove the remaining `Fin 4` / `Fin 3` assumptions from the spatial helper layer.

Target files:

- `SpacetimeDecomp.lean`
- `SchwartzProdIntegrable.lean`
- any downstream file using `Fin.sum_univ_four` or `SpatialCoords3`

Tasks:

- Replace `SpatialCoords3` with either:
  - `SpatialCoords := EuclideanSpace ℝ (Fin (STDimension - 1))`, or
  - a new local alias based on `STDimension - 1`.
- Rewrite `spacetimeOfTimeSpace` and related lemmas so they target the current `STDimension`.
- Replace `Fin.sum_univ_four` expansions with dimension-correct decompositions, ideally expressed through
  `spatialPart`, `getTimeComponent`, or a dimension-agnostic helper.
- Recheck all spatial integrability lemmas so they are correct for spatial dimension `2`.

Expected difficulty:

- Medium to high. Some proofs will become easier if they are refactored to avoid componentwise sums.

Acceptance criteria:

- No remaining use of `Fin.sum_univ_four` in the 3D branch except possibly in clearly quarantined,
  obsolete comments that should then be deleted.
- No remaining `SpatialCoords3` alias.
- The spacetime/spatial helper layer no longer presupposes the old 4D project layout.

### Phase 4: Port OS1 and OS4 downstream consequences

Objective: make the theorem-level AQFT consequences use the 3D covariance branch.

Target files:

- `OS1_GFF.lean`
- `OS4_Clustering.lean`
- `OS4_MGF.lean`
- `OS4_Ergodicity.lean`

Tasks for `OS1_GFF.lean`:

- Switch imports to the 3D branch.
- Replace any 4D `K₁` language with the 3D kernel story.
- Verify that the local-integrability arguments are still correct for `d = 3`.

Tasks for `OS4_Clustering.lean`:

- Switch imports to `OSforGFFin3D.*`.
- Replace old covariance formula comments and any explicit 4D kernel constants.
- Update the translation-decay argument so it depends on the new 3D kernel decay theorem.
- Remove `Fin.sum_univ_four` and any 4D-specific time-shift geometry.

Tasks for `OS4_MGF.lean` and `OS4_Ergodicity.lean`:

- Migrate imports only after `OS4_Clustering.lean` is stable.
- Confirm that they depend on the migrated 3D OS4 infrastructure rather than the old branch.

Acceptance criteria:

- These files no longer import `OSforGFF.*`.
- Their statements and docstrings no longer describe 4D covariance behavior.
- Their proofs rely on 3D files in this branch, not old-branch theorem reuse.

### Phase 5: Port assembly and measure-construction files

Objective: make the branch self-contained at the top level.

Target files:

- `OS0_GFF.lean`
- `OS2_GFF.lean`
- `OS3_GFF.lean`
- `GaussianFreeField.lean`
- `GFFIsGaussian.lean`
- `GFFMconstruct.lean`
- `GaussianMoments.lean`
- `GFFmaster.lean`

Tasks:

- Replace old-branch imports with 3D imports once the lower layers are stable.
- Remove any residual references to `OSforGFF.*` symbols where 3D analogues now exist.
- Rebuild the aggregate theorem files only after all lower dependencies are migrated.

Acceptance criteria:

- A repo-wide search finds no remaining `import OSforGFF.` in `OSforGFFin3D/*.lean` except in comments that
  explicitly discuss the original project.
- `GFFmaster.lean` closes over the 3D branch only.
- The project can be read as an independent development without consulting `OSforGFF/*` for active proof
  dependencies.

### Phase 6: Documentation and naming cleanup

Objective: align prose and compatibility names with the actual 3D mathematics.

Tasks:

- Review files for stale references to:
  - “4D spacetime”
  - `K₁`
  - `Fin 4`
  - 4D heat-kernel constants
- Keep compatibility theorem names only when useful, but ensure their docstrings are truthful.
- Update `dimension_dependence.md` after the migration is done so it becomes a historical map rather than a
  list of active blockers.

Acceptance criteria:

- Comments and docstrings no longer describe 4D formulas in the migrated branch.

## Suggested Execution Order

The recommended order is:

1. `Parseval.lean`
2. `Covariance.lean`
3. `CovarianceR.lean`
4. `OS3_MixedRepInfra.lean`
5. `OS3_MixedRep.lean`
6. `OS3_CovarianceRP.lean`
7. `SpacetimeDecomp.lean`
8. `SchwartzProdIntegrable.lean`
9. `OS1_GFF.lean`
10. `OS4_Clustering.lean`
11. `OS4_MGF.lean`
12. `OS4_Ergodicity.lean`
13. top-level assembly files
14. documentation cleanup

This order minimizes backtracking:

- covariance consumers first
- then mixed-representation / OS3 files
- then hard-coded spatial helpers
- then OS1/OS4 consequences
- then final assembly

## Verification Checklist

After each file or small cluster:

1. Run file-local Lean diagnostics.
2. Build the affected module directly with `lake build OSforGFFin3D.<ModuleName>`.
3. Re-run a grep for:
   - `import OSforGFF.`
   - `BesselK1|besselK1|K₁`
   - `Fin.sum_univ_four`
   - stale `4D` wording
4. Only after a phase completes, run `lake build` for the full project.

## Exit Criteria

The migration is complete when all of the following hold:

- `lake build` succeeds.
- The `OSforGFFin3D` tree is self-contained and does not import `OSforGFF.*` for active mathematics.
- The essential formulas are correct for spacetime dimension `3`.
- Spatial estimates use dimension `2` explicitly or through generic abstractions.
- No active comments or docstrings still claim the branch is proving the original 4D `K₁` theory.
- A grep over `OSforGFFin3D/*.lean` finds no remaining `import OSforGFF.` lines.
- The project is understandable as a standalone 3D development rather than a compatibility layer over the
  4D project.

## Notes on Scope

- This plan does **not** require changing files under `OSforGFF/`.
- But it **does** require removing the logical dependency of `OSforGFFin3D` on those files.
- It is acceptable to keep some compatibility theorem names if changing them would cause large downstream
  churn, but the mathematics and documentation must still be correct for the 3D branch.