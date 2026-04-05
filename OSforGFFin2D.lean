/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
-- This module serves as the root of the `Aqft2` library.
-- Import modules here that should be built as part of the library.

-- Core infrastructure
import OSforGFFin2D.FunctionalAnalysis
import OSforGFFin2D.Basic
import OSforGFFin2D.QuantitativeDecay
import OSforGFFin2D.ComplexTestFunction
import OSforGFFin2D.SpacetimeDecomp
import OSforGFFin2D.TimeTranslation

-- Euclidean group and symmetries
import OSforGFFin2D.Euclidean
import OSforGFFin2D.DiscreteSymmetry

-- Fourier analysis
import OSforGFFin2D.FourierTransforms
import OSforGFFin2D.Parseval
import OSforGFFin2D.BesselFunction
import OSforGFFin2D.BesselK0Proofs
import OSforGFFin2D.LaplaceIntegral

-- Covariance theory
import OSforGFFin2D.CovarianceMomentum
import OSforGFFin2D.Covariance
import OSforGFFin2D.CovarianceR
import OSforGFFin2D.GaussianRBF
import OSforGFFin2D.PositiveDefinite

-- Reflection positivity
import OSforGFFin2D.PositiveTimeTestFunction_real
import OSforGFFin2D.FrobeniusPositivity
import OSforGFFin2D.SchurProduct
import OSforGFFin2D.HadamardExp

-- Schwinger functions
import OSforGFFin2D.Schwinger
import OSforGFFin2D.SchwingerTwoPointFunction

-- Measure construction (Minlos)
import OSforGFFin2D.Minlos
import OSforGFFin2D.MinlosAnalytic

-- GFF construction
import OSforGFFin2D.GFFMconstruct
import OSforGFFin2D.GaussianMoments
import OSforGFFin2D.GFFIsGaussian
import OSforGFFin2D.GaussianFreeField

-- Integrability and analysis
import OSforGFFin2D.L2TimeIntegral
import OSforGFFin2D.SchwartzTonelli
import OSforGFFin2D.SchwartzTranslationDecay
import OSforGFFin2D.SchwartzProdIntegrable

-- OS Axioms
import OSforGFFin2D.OS_Axioms
import OSforGFFin2D.OS0_GFF
import OSforGFFin2D.OS1_GFF
import OSforGFFin2D.OS2_GFF
import OSforGFFin2D.OS3_MixedRep
import OSforGFFin2D.OS3_MixedRepInfra
import OSforGFFin2D.OS3_CovarianceRP
import OSforGFFin2D.OS3_GFF
import OSforGFFin2D.OS4_MGF
import OSforGFFin2D.OS4_Clustering
import OSforGFFin2D.OS4_Ergodicity

-- Master theorem
import OSforGFFin2D.GFFmaster

-- Generic QFT framework and alternative spacetimes
import OSforGFFin2D.QFTFramework
import OSforGFFin2D.OS_Axioms_Generic
import OSforGFFin2D.LatticeSpacetime
import OSforGFFin2D.QFTFramework.Instances
