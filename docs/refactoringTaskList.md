# Refactoring Task List for OSforGFFin3D

This document is a behavior-preserving refactor backlog for the entire
`OSforGFFin3D` Lean tree.

For a shorter progress view, see `docs/refactoringMilestones.md`.

It is intentionally separate from the completed migration plan:

- the 3D branch now builds standalone;
- the remaining work is to improve proof structure, reduce duplication,
  isolate axiomatic boundaries, and clean public APIs and comments;
- tasks below should preserve theorem statements unless a rename or statement
  cleanup is explicitly justified and coordinated downstream.

## Refactor Goals

- keep `lake build` green after each batch;
- prefer extracting `private` helper lemmas over rewriting public theorems;
- reduce long proof scripts by factoring recurring algebra, measurability, and
  integrability arguments;
- quarantine genuine axioms in the smallest possible set of files;
- remove stale "formerly axiom" / "compatibility" wording once no longer
  needed;
- preserve the standalone `OSforGFFin3D` dependency structure.

## Refactor Conventions

- Prefer extracting small `private` helper lemmas before changing the structure
      of a public theorem.
- Keep public theorem statements stable unless a rename or statement cleanup is
      explicitly justified by downstream API needs.
- Move technical lemmas downward in the import graph when possible, rather than
      leaving them in theorem-assembly files.
- Keep migration-history commentary out of proof bodies and file headers; retain
      only concise provenance notes when they still help explain the code.
- Validate each edited file immediately, then run full `lake build` after each
      completed dependency batch.

## Standard File Refactor Sequence

1. Identify repeated proof fragments, local algebra chains, and helper lemmas
       that should be extracted.
2. Extract narrow-scope helper lemmas first, preferring `private` or local
       definitions.
3. Simplify the public theorem body so the top-level proof reads as a short
       outline.
4. Remove stale compatibility wording and keep only aliases that are still used
       downstream.
5. Run a targeted check for the edited file.

## Global Checklist

- [x] Define a standard refactor pattern for long proofs: local helper lemmas,
      `section`-scoped utilities, and shorter theorem bodies.
- [x] Standardize file headers so each file states only current mathematical
      scope, not migration history.
- [x] Replace repeated "formerly axiom" commentary with concise provenance notes
      only where that history is still useful.
- [x] Centralize compatibility aliases and remove duplicate explanatory comments
      about them.
- [x] Run `lake build` after each dependency-layer batch, not only at the end.

## Priority Order

### Batch 1: Highest proof-complexity modules

- [x] `OS3_MixedRepInfra.lean`
- [x] `OS3_MixedRep.lean`
- [x] `CovarianceMomentum.lean`
- [x] `OS4_Clustering.lean`

### Batch 2: Core interfaces built on the covariance spine

- [x] `Parseval.lean`
- [x] `Covariance.lean`
- [x] `CovarianceR.lean`
- [x] `OS1_GFF.lean`
- [x] `OS3_CovarianceRP.lean`
- [x] `SchwartzProdIntegrable.lean`
- [x] `SpacetimeDecomp.lean`
- [x] `L2TimeIntegral.lean`

### Batch 3: Axiom boundary and measure-construction cleanup

- [x] `OS0_GFF.lean`
- [x] `Minlos.lean`
- [x] `NuclearSpace.lean`
- [x] `MinlosAnalytic.lean`
- [x] `SchwingerTwoPointFunction.lean`
- [x] `OS_Axioms.lean`
- [x] `GFFMconstruct.lean`
- [x] `GaussianMoments.lean`
- [x] `GFFIsGaussian.lean`

### Batch 4: Public theorem assembly and OS consequence files

- [x] `OS2_GFF.lean`
- [x] `OS3_GFF.lean`
- [x] `OS4_MGF.lean`
- [x] `OS4_Ergodicity.lean`
- [x] `GaussianFreeField.lean`
- [x] `GFFmaster.lean`

### Batch 5: Lower-level cleanup and API consistency sweep

- [x] `Basic.lean`
- [x] `BesselFunction.lean`
- [x] `ComplexTestFunction.lean`
- [x] `DiscreteSymmetry.lean`
- [x] `Euclidean.lean`
- [x] `FourierTransforms.lean`
- [x] `FrobeniusPositivity.lean`
- [x] `FunctionalAnalysis.lean`
- [x] `GaussianRBF.lean`
- [x] `HadamardExp.lean`
- [x] `LaplaceIntegral.lean`
- [x] `PositiveDefinite.lean`
- [x] `PositiveTimeTestFunction_real.lean`
- [x] `QuantitativeDecay.lean`
- [x] `SchurProduct.lean`
- [x] `SchwartzTonelli.lean`
- [x] `SchwartzTranslationDecay.lean`
- [x] `Schwinger.lean`
- [x] `TimeTranslation.lean`

## File-by-File Tasks

### Foundation and shared notation

- [x] `Basic.lean`: keep the dimension API minimal; factor any repeated aliases
      or coercion lemmas used across many files into one place.
- [x] `BesselFunction.lean`: split the file into clearly marked blocks
      (definition layer, asymptotics, positivity, decay); extract helper lemmas
      reused by `CovarianceMomentum.lean`; reduce long normalization proofs.
- [x] `ComplexTestFunction.lean`: trim redundant wrapper lemmas and group API
      results by algebraic structure, topology, and support properties.
- [x] `DiscreteSymmetry.lean`: factor repeated action/linearity proofs into
      generic helper lemmas for reflection and conjugation operators.
- [x] `Euclidean.lean`: separate group-theoretic facts from function-space
      action lemmas; shorten long doc comments that explain already-formalized
      facts.
- [x] `FunctionalAnalysis.lean`: rename or regroup dimension-specific helper
      lemmas so the 3D/2D role is obvious; extract reusable integrability bounds
      used by covariance and clustering files.
- [x] `Schwinger.lean`: audit namespace layout and consolidate repeated notation
      or simple algebraic identities into compact helper sections.

### Positive-definite and kernel algebra layer

- [x] `PositiveDefinite.lean`: collapse repeated matrix-kernel boilerplate into
      helper lemmas; review theorem ordering so later files import a cleaner API.
- [x] `SchurProduct.lean`: isolate any proof skeletons that still carry
      historical "sorry" commentary; factor Kronecker/Hadamard helper lemmas into
      a dedicated subsection.
- [x] `HadamardExp.lean`: refactor to reuse shared positive-definite closure
      lemmas instead of re-proving structural steps inline.
- [x] `GaussianRBF.lean`: streamline the chain from radial basis positivity to
      downstream kernel results; remove any compatibility-only wrappers that are
      no longer needed.
- [x] `FrobeniusPositivity.lean`: audit theorem granularity and extract helper
      lemmas for repeated finite-sum positivity arguments.

### Fourier and covariance spine

- [x] `FourierTransforms.lean`: separate transform identities, measurability, and
      normalization lemmas; reduce any legacy commentary that still mirrors the
      old development structure.
- [x] `Parseval.lean`: refactor proof flow around explicit local helper lemmas for
      Schwartz integrability and bilinear pairing manipulations.
- [x] `CovarianceMomentum.lean`: split into sections for heat kernel,
      Schwinger representation, explicit Bessel formula, continuity, and decay;
      centralize compatibility aliases; factor repeated positivity and prefactor
      bounds used in several decay proofs.
- [x] `Covariance.lean`: extract common bilinear and reflection-invariance proof
      steps; shorten axiom-explanation prose that no longer matches the current
      implementation state.
- [x] `CovarianceR.lean`: factor the continuous-linear-map construction into
      helper definitions; keep the real/complex bridge lemmas compact and local.
- [x] `PositiveTimeTestFunction_real.lean`: regroup the API around positivity,
      support, and reflection behavior so downstream OS3 files need fewer local
      helper rewrites.

### Spacetime decomposition and integrability infrastructure

- [x] `SchwartzProdIntegrable.lean`: extract the time-space decomposition lemmas
      from the integrability estimates; keep product-measure arguments short and
      composable.
- [x] `SpacetimeDecomp.lean`: isolate geometry identities about time/spatial
      splitting; remove any remaining proof clutter caused by explicit component
      manipulations.
- [x] `SchwartzTonelli.lean`: consolidate Tonelli/Fubini helper lemmas into a
      smaller exported API so large downstream proofs do not need ad hoc local
      wrappers.
- [x] `SchwartzTranslationDecay.lean`: factor common translation estimates and
      seminorm bookkeeping into reusable helper lemmas.
- [x] `QuantitativeDecay.lean`: separate abstract decay machinery from the
      concrete covariance application lemmas used by `OS4_Clustering.lean`.
- [x] `L2TimeIntegral.lean`: group theorems by measurable, integrable, and norm
      bounds; remove repeated parameter setup from theorem statements and proofs.
- [x] `LaplaceIntegral.lean`: extract the standard half-power integral lemmas and
      simplify the interface consumed by mixed-representation files.

### Mixed-representation and reflection-positivity branch

- [x] `OS3_MixedRepInfra.lean`: break very long proofs into named local stages
      for Gaussian FT, measurability, domination, and Fubini swaps; replace
      historical axiom narration with precise statements of remaining technical
      dependencies.
- [x] `OS3_MixedRep.lean`: extract reusable bilinear-form conversion lemmas;
      reduce duplication between heat-kernel, mixed-representation, and Bessel
      representation arguments.
- [x] `OS3_CovarianceRP.lean`: refactor the reflection-positivity proof into
      explicit phases so the mixed-representation inputs and positivity steps are
      easy to audit.

### Axiom interface and Schwinger-function boundary

- [x] `OS_Axioms.lean`: keep only canonical bundled definitions and notation;
      move derived convenience lemmas to downstream files unless they are truly
      foundational.
- [x] `SchwingerTwoPointFunction.lean`: clean historical commentary about delta
      functions and distributional intuition; make the abstract/concrete bridge
      API as small as possible.
- [x] `TimeTranslation.lean`: separate operator definitions from measure/action
      lemmas; extract any repeated algebra used by OS2 and OS4 files.

### Measure construction and Gaussian machinery

- [x] `Minlos.lean`: isolate the actual global axiom (`minlos_theorem`) from the
      surrounding derived lemmas; make the non-axiomatic API easy to import
      without carrying extra narrative.
- [x] `NuclearSpace.lean`: similarly isolate `schwartz_nuclear`; keep the rest of
      the file focused on the interface actually used by `Minlos.lean`.
- [x] `MinlosAnalytic.lean`: shorten compatibility and historical notes; extract
      helper lemmas bridging characteristic functionals and analyticity.
- [x] `GFFMconstruct.lean`: split construction, covariance identification, and
      characteristic-functional lemmas into clear subsections.
- [x] `GaussianMoments.lean`: factor Wick-expansion combinatorics and Gaussian
      expectation lemmas into reusable local helpers.
- [x] `GFFIsGaussian.lean`: trim compatibility wrappers at the root level and
      separate theorem transport from genuinely new Gaussian arguments.
- [x] `GaussianFreeField.lean`: keep only public theorem assembly and move any
      technical helper lemmas back into lower files where they belong.

### OS axiom proof files

- [x] `OS0_GFF.lean`: isolate the true analyticity axiom boundary
      (`differentiable_analyticAt_finDim`) from derived proof infrastructure;
      group holomorphicity, integrability, and final OS0 assembly separately.
- [x] `OS1_GFF.lean`: continue extracting private helper lemmas for covariance
      identification, measurability, and mass-dependent constants; keep the final
      OS1 theorem bodies short.
- [x] `OS2_GFF.lean`: factor Euclidean-invariance transport lemmas from the final
      theorem assembly so the file reads as a concise OS2 proof.
- [x] `OS3_GFF.lean`: trim assembly-level duplication and keep only the final
      reduction from covariance reflection positivity to OS3.
- [x] `OS4_MGF.lean`: reduce purely infrastructural commentary and keep the file
      focused on the OS4 moment-generating-function inputs used downstream.
- [x] `OS4_Clustering.lean`: split the file into covariance decay, bilinear test
      function estimates, and Gaussian clustering assembly; extract time-shift
      bound helpers that are currently threaded through large proofs.
- [x] `OS4_Ergodicity.lean`: keep only the ergodicity reduction and theorem
      assembly; move any duplicated clustering prerequisites into lower modules.

### Top-level aggregation

- [x] `GFFmaster.lean`: reduce it to a thin import-and-export surface with no
      proof content beyond the final assembly theorem.

## Suggested Execution Rules

1. Refactor one dependency batch at a time.
2. After each edited file, run a targeted check on that file.
3. After each completed batch, run full `lake build`.
4. Only remove compatibility aliases after confirming no downstream use remains.
5. Prefer moving helper lemmas downward in the import graph, not upward.

## Completion Criteria

- [x] No large proof-heavy file depends on repeated copy-pasted algebraic or
      measurability blocks.
- [x] The only remaining axioms are intentional top-level mathematical boundary
      assumptions, each isolated in the narrowest appropriate file.
- [x] Public theorem files (`OS0_GFF` through `OS4_Ergodicity`, `GaussianFreeField`,
      `GFFmaster`) are mostly assembly, not storage for low-level helper lemmas.
- [x] File headers and doc comments describe the current 3D development rather
      than the migration path from the 4D branch.
- [x] The full project still passes `lake build`.