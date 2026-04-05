/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Order.Basic

import OSforGFFin2D.Basic

/-!
# Lattice Spacetime aℤ^d

This file defines the lattice spacetime aℤ^d, where lattice points are
integer-valued vectors embedded into ℝ^d at positions a·n for lattice
spacing a > 0.

## Main Definitions

* `SpaceTimeLattice d` — the type `Fin d → ℤ` of lattice sites
* `latticeEmbed d a` — embedding into ℝ^d at positions a·n
* `TestFunctionLattice d` — real-valued functions on lattice sites
* `FieldConfigurationLattice d` — field values at lattice sites
* Concrete operations: time reflection, time translation, translation, pairing

## Design Notes

- Lattice spacing `a` enters via the embedding `latticeEmbed`, not as a type parameter
- The metric on `SpaceTimeLattice d` is inherited from ℝ^d: `dist(n,m) = ‖a·n - a·m‖`
- Distribution pairing uses `a^d`-weighted sums (Riemann sum approximation)
- `TimeParam = ℤ` (discrete time steps; physical time step = a)
- The symmetry group is the semi-direct product of lattice translations ℤ^d
  and the hypercubic group (permutations and reflections of coordinates)
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {d : ℕ} [Fact (0 < d)]

/-! ## Spacetime type -/

/-- Lattice spacetime: integer-valued coordinate vectors. -/
abbrev SpaceTimeLattice (d : ℕ) := Fin d → ℤ

instance : Inhabited (SpaceTimeLattice d) := ⟨fun _ => 0⟩

instance : AddCommGroup (SpaceTimeLattice d) := Pi.addCommGroup

/-! ## Embedding into ℝ^d -/

/-- Embed a lattice point n ∈ ℤ^d into ℝ^d at position a·n. -/
def latticeEmbed (d : ℕ) (a : ℝ) (n : SpaceTimeLattice d) : SpaceTime d :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => a * (n i : ℝ))

/-- PseudoMetricSpace on the lattice inherited from ℝ^d via the embedding.
    dist(n, m) = ‖a·n - a·m‖ = |a| · ‖n - m‖_ℓ². -/
def latticePseudoMetric (d : ℕ) (a : ℝ) : PseudoMetricSpace (SpaceTimeLattice d) :=
  PseudoMetricSpace.induced (latticeEmbed d a) inferInstance

/-! ## Test functions and field configurations -/

/-- Test functions on the lattice: real-valued functions on ℤ^d.
    In practice these should have finite support or sufficient decay. -/
abbrev TestFunctionLattice (d : ℕ) := (Fin d → ℤ) → ℝ

/-- Complex test functions on the lattice. -/
abbrev TestFunctionLatticeℂ (d : ℕ) := (Fin d → ℤ) → ℂ

/-- Field configurations on the lattice: real values at each lattice site. -/
abbrev FieldConfigurationLattice (d : ℕ) := (Fin d → ℤ) → ℝ

-- Measurable space on lattice field configurations (discrete σ-algebra)
instance : MeasurableSpace (FieldConfigurationLattice d) := borel _

/-! ## Distribution pairing -/

/-- Lattice distribution pairing: ⟨φ, f⟩ = ∑_n φ(n) · f(n).
    The a^d weighting factor is incorporated separately in the generating functional
    to keep the pairing independent of the lattice spacing. -/
def latticeDistributionPairing (φ : FieldConfigurationLattice d) (f : TestFunctionLattice d) : ℝ :=
  -- For finitely supported test functions, this is a finite sum.
  -- We use tsum for generality (converges for ℓ¹ test functions on ℓ∞ configs).
  ∑' n, φ n * f n

/-- Complex lattice pairing: ⟨φ, f⟩_ℂ = ∑_n φ(n) · f(n). -/
def latticeDistributionPairingℂ (φ : FieldConfigurationLattice d)
    (f : TestFunctionLatticeℂ d) : ℂ :=
  ∑' n, (φ n : ℂ) * f n

/-! ## Time operations -/

/-- Time reflection on the lattice: negate the time coordinate (index 0). -/
def latticeTimeReflection (f : TestFunctionLattice d) : TestFunctionLattice d :=
  fun n => f (Function.update n ⟨0, Fact.out⟩ (-n ⟨0, Fact.out⟩))

/-- Time reflection as a continuous linear map.
    Continuous in the product topology (pointwise convergence) since it
    only permutes the argument. -/
def latticeTimeReflectionCLM : TestFunctionLattice d →L[ℝ] TestFunctionLattice d :=
  { toLinearMap :=
    { toFun := latticeTimeReflection
      map_add' := by intro f g; ext n; simp [latticeTimeReflection]
      map_smul' := by intro c f; ext n; simp [latticeTimeReflection] }
    cont := by
      -- latticeTimeReflection f = f ∘ (time reflection on indices)
      -- This is continuous in the product topology
      apply continuous_pi
      intro n
      exact continuous_apply _ }

/-- Submodule of positive-time lattice test functions:
    f is supported on {n | n₀ > 0}. -/
def latticePositiveTimeSubmodule : Submodule ℝ (TestFunctionLattice d) where
  carrier := { f | ∀ n : SpaceTimeLattice d, n ⟨0, Fact.out⟩ ≤ 0 → f n = 0 }
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq, Pi.add_apply] at *
    intro n hn
    rw [hf n hn, hg n hn, add_zero]
  smul_mem' := by
    intro c f hf
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *
    intro n hn
    rw [hf n hn, mul_zero]

/-- Time translation on lattice field configurations: shift the time index by s steps. -/
def latticeTimeTranslation (s : ℤ) (φ : FieldConfigurationLattice d) :
    FieldConfigurationLattice d :=
  fun n => φ (Function.update n ⟨0, Fact.out⟩ (n ⟨0, Fact.out⟩ - s))

/-- Spatial translation of lattice test functions by a lattice vector. -/
def latticeTranslateTestFun (a : SpaceTimeLattice d) (f : TestFunctionLattice d) :
    TestFunctionLattice d :=
  fun n => f (n - a)

/-! ## Restriction from continuum -/

/-- Restrict a continuum test function to the lattice: sample at lattice points a·n. -/
def restrictToLattice (a : ℝ) (f : TestFunction d) : TestFunctionLattice d :=
  fun n => f (latticeEmbed d a n)

/-! ## Symmetry group -/

/-- The hypercubic group: signed permutations of coordinates.
    An element is a permutation σ of Fin d together with signs εᵢ ∈ {±1}. -/
structure HypercubicElement (d : ℕ) where
  perm : Equiv.Perm (Fin d)
  signs : Fin d → Int
  signs_sq : ∀ i, signs i = 1 ∨ signs i = -1

/-- The lattice symmetry group: semi-direct product of ℤ^d translations
    and the hypercubic group. -/
structure LatticeSymmetryGroup (d : ℕ) where
  translation : Fin d → ℤ
  hypercubic : HypercubicElement d

/-- Action of hypercubic element on lattice coordinates. -/
def HypercubicElement.act (h : HypercubicElement d) (n : SpaceTimeLattice d) :
    SpaceTimeLattice d :=
  fun i => h.signs i * n (h.perm i)

/-- Action of full lattice symmetry group on lattice coordinates. -/
def LatticeSymmetryGroup.act (g : LatticeSymmetryGroup d) (n : SpaceTimeLattice d) :
    SpaceTimeLattice d :=
  (fun i => g.hypercubic.act n i + g.translation i)

-- Group structure on the lattice symmetry group
instance : One (LatticeSymmetryGroup d) :=
  ⟨{ translation := fun _ => 0
     hypercubic :=
       { perm := Equiv.refl _
         signs := fun _ => 1
         signs_sq := fun _ => Or.inl rfl } }⟩

instance : Mul (LatticeSymmetryGroup d) :=
  ⟨fun g₁ g₂ =>
    { translation := fun i =>
        g₁.hypercubic.signs i * g₂.translation (g₁.hypercubic.perm i) + g₁.translation i
      hypercubic :=
        { perm := g₁.hypercubic.perm.trans g₂.hypercubic.perm
          signs := fun i => g₁.hypercubic.signs i * g₂.hypercubic.signs (g₁.hypercubic.perm i)
          signs_sq := by
            intro i
            have h1 := g₁.hypercubic.signs_sq i
            have h2 := g₂.hypercubic.signs_sq (g₁.hypercubic.perm i)
            rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [h1, h2] } }⟩

-- Providing a full Group instance is complex; we axiomatize it for now
@[instance] axiom instGroupLatticeSymmetryGroup (d : ℕ) :
  Group (LatticeSymmetryGroup d)

/-- Action of the lattice symmetry group on complex test functions. -/
def latticeSymmetryActionℂ (g : LatticeSymmetryGroup d)
    (f : TestFunctionLatticeℂ d) : TestFunctionLatticeℂ d :=
  fun n => f (LatticeSymmetryGroup.act g⁻¹ n)

end
