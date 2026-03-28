@OSforGFFin3D/ is a modification of @OSforGFF/
Description of the dimension dependence is in @dimension_dependence.md.

`lake build OSforGFFin3D` builds OSforGFFin3D as a Lean library.



# Changing to 3D
@OSforGFFin3D/ should have
**Essential (d=3)**: Formulas that evaluate reflect that  $d=3$.
**Spatial (d=2)**: Uses the spatial dimension $d-1=2$ explicitly, typically for integrability estimates.
**Structural:** References `STDimension` or `SpaceTime` but the proof works for any $d$ without change (beyond updating the abbreviation).

## Same-Named File Comparison With @OSforGFF/

The lists below compare the top-level `.lean` files in `@OSforGFFin3D/` with the same-named
files in `@OSforGFF/`. Every top-level `.lean` file in `@OSforGFFin3D/` has a same-named
counterpart in `@OSforGFF/`.

### Identical Files

These 5 files are currently identical to their same-named counterparts in `@OSforGFF/`:

- `FrobeniusPositivity.lean`
- `LaplaceIntegral.lean`
- `NuclearSpace.lean`
- `PositiveDefinite.lean`
- `SchwartzTranslationDecay.lean`

### Changed Files

These 41 files differ from their same-named counterparts in `@OSforGFF/`:

- `Basic.lean`
- `BesselFunction.lean`
- `ComplexTestFunction.lean`
- `Covariance.lean`
- `CovarianceMomentum.lean`
- `CovarianceR.lean`
- `DiscreteSymmetry.lean`
- `Euclidean.lean`
- `FourierTransforms.lean`
- `FunctionalAnalysis.lean`
- `GFFIsGaussian.lean`
- `GFFMconstruct.lean`
- `GFFmaster.lean`
- `GaussianFreeField.lean`
- `GaussianMoments.lean`
- `GaussianRBF.lean`
- `HadamardExp.lean`
- `L2TimeIntegral.lean`
- `Minlos.lean`
- `MinlosAnalytic.lean`
- `OS0_GFF.lean`
- `OS1_GFF.lean`
- `OS2_GFF.lean`
- `OS3_CovarianceRP.lean`
- `OS3_GFF.lean`
- `OS3_MixedRep.lean`
- `OS3_MixedRepInfra.lean`
- `OS4_Clustering.lean`
- `OS4_Ergodicity.lean`
- `OS4_MGF.lean`
- `OS_Axioms.lean`
- `Parseval.lean`
- `PositiveTimeTestFunction_real.lean`
- `QuantitativeDecay.lean`
- `SchurProduct.lean`
- `SchwartzProdIntegrable.lean`
- `SchwartzTonelli.lean`
- `Schwinger.lean`
- `SchwingerTwoPointFunction.lean`
- `SpacetimeDecomp.lean`
- `TimeTranslation.lean`

