# `Basic.lean` — Informal Summary

> **Source**: [`OSforGFF/Spacetime/Basic.lean`](../../OSforGFF/Spacetime/Basic.lean)
> **Generated**: 2026-07-05 (regenerated from current source)

## Overview

This file sets up the core type definitions of the formalization, all generic in the spacetime
dimension `d : ℕ`. It introduces Euclidean spacetime `SpaceTime d = EuclideanSpace ℝ (Fin d)`,
the real/complex Schwartz test functions `SchwartzTestFunction d` / `SchwartzTestFunctionℂ d`, and the
field-configuration space `FieldConfiguration d = WeakDual ℝ (SchwartzMap (SpaceTime d) ℝ)` of
tempered distributions $\mathscr{S}'(\mathbb{R}^d)$. On top of these it builds the Glimm-Jaffe
distribution framework: the real and complex pairings $\langle \omega, f\rangle$, the generating
functionals $Z[J] = \int \exp(i\langle\omega, J\rangle)\, d\mu(\omega)$, the mean field, a
real/imaginary decomposition of complex test functions, and a small amount of spatial geometry
(spatial coordinates $\mathbb{R}^{d-1}$, the spatial $L^2$ space, and the relativistic energy
$E(k) = \sqrt{\lVert k\rVert^2 + m^2}$). The time/space split relies on `[Fact (2 ≤ d)]` so that
the time index `(0 : Fin d)` is available.

## Status

**Main result**: Core spacetime / test-function / distribution definitions plus the Glimm-Jaffe
pairing and generating-functional framework. Fully proven (0 sorries; no `sorry`/`admit`).

**Length**: 276 lines, 22 definition(s) + 10 theorem(s)/lemma(s)

---

### [`SpaceTime`](../../OSforGFF/Spacetime/Basic.lean#L56) — Definition *(abbrev)*

**Lean signature**
```lean
abbrev SpaceTime (d : ℕ) := EuclideanSpace ℝ (Fin d)
```

**Informal**: Euclidean spacetime of dimension $d$: $\mathbb{R}^d$ with its Euclidean
inner-product structure.

---

### [`instance : NeZero d`](../../OSforGFF/Spacetime/Basic.lean#L59) — Definition *(instance)*

**Lean signature**
```lean
instance {d : ℕ} [Fact (2 ≤ d)] : NeZero d
```

**Informal**: Dimensions admitting a time/space split ($d \geq 2$) are nonzero, so `(0 : Fin d)`
is a valid index.

---

### [`instance : InnerProductSpace ℝ (SpaceTime d)`](../../OSforGFF/Spacetime/Basic.lean#L61) — Definition *(instance)*

**Lean signature**
```lean
noncomputable instance (d : ℕ) : InnerProductSpace ℝ (SpaceTime d)
```

**Informal**: The real inner-product-space structure on `SpaceTime d`, obtained by instance
resolution.

---

### [`getTimeComponent`](../../OSforGFF/Spacetime/Basic.lean#L64) — Definition *(abbrev)*

**Lean signature**
```lean
abbrev getTimeComponent {d : ℕ} [Fact (2 ≤ d)] (x : SpaceTime d) : ℝ :=
  x ⟨0, by have h : 2 ≤ d := Fact.out; omega⟩
```

**Informal**: The time component $x_0$ of a spacetime point, i.e. the coordinate at index $0$
(the time/space split needs $d \geq 2$).

---

### [`SchwartzTestFunction`](../../OSforGFF/Spacetime/Basic.lean#L80) — Definition *(abbrev)*

**Lean signature**
```lean
abbrev SchwartzTestFunction (d : ℕ) : Type := SchwartzMap (SpaceTime d) ℝ
```

**Informal**: Real-valued Schwartz test functions $\mathscr{S}(\mathbb{R}^d, \mathbb{R})$.

---

### [`SchwartzTestFunction𝕜`](../../OSforGFF/Spacetime/Basic.lean#L81) — Definition *(abbrev)*

**Lean signature**
```lean
abbrev SchwartzTestFunction𝕜 (d : ℕ) : Type := SchwartzMap (SpaceTime d) 𝕜
```

**Informal**: $𝕜$-valued Schwartz functions on $\mathbb{R}^d$, for a field `[RCLike 𝕜]`.

---

### [`SchwartzTestFunctionℂ`](../../OSforGFF/Spacetime/Basic.lean#L82) — Definition *(abbrev)*

**Lean signature**
```lean
abbrev SchwartzTestFunctionℂ (d : ℕ) := SchwartzTestFunction𝕜 (𝕜 := ℂ) d
```

**Informal**: Complex-valued Schwartz test functions $\mathscr{S}(\mathbb{R}^d, \mathbb{C})$.

---

### [`pointwiseMulCLM`](../../OSforGFF/Spacetime/Basic.lean#L89) — Definition

**Lean signature**
```lean
def pointwiseMulCLM : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ
```

**Informal**: Complex multiplication as a continuous $\mathbb{C}$-bilinear map.

---

### [`schwartzMul`](../../OSforGFF/Spacetime/Basic.lean#L92) — Definition

**Lean signature**
```lean
def schwartzMul (g : (SchwartzTestFunctionℂ d)) : (SchwartzTestFunctionℂ d) →L[ℂ] (SchwartzTestFunctionℂ d) :=
  (SchwartzMap.bilinLeftCLM pointwiseMulCLM (SchwartzMap.hasTemperateGrowth_general g))
```

**Informal**: Pointwise multiplication by a fixed complex test function $g$, lifted to a
continuous linear operator on the complex Schwartz space via `SchwartzMap.bilinLeftCLM`.

---

### [`FieldConfiguration`](../../OSforGFF/Spacetime/Basic.lean#L110) — Definition *(abbrev)*

**Lean signature**
```lean
abbrev FieldConfiguration (d : ℕ) := WeakDual ℝ (SchwartzMap (SpaceTime d) ℝ)
```

**Informal**: Field configurations as tempered distributions $\mathscr{S}'(\mathbb{R}^d)$ (the
weak-* dual of the real Schwartz space), following the Glimm-Jaffe approach where the field
measure is supported on distributions. It carries the cylinder σ-algebra provided by the Bochner
library, and the weak-* topology makes evaluation maps continuous.

---

### [`distributionPairing`](../../OSforGFF/Spacetime/Basic.lean#L120) — Definition

**Lean signature**
```lean
def distributionPairing (ω : (FieldConfiguration d)) (f : (SchwartzTestFunction d)) : ℝ := ω f
```

**Informal**: The fundamental pairing $\langle \omega, f\rangle = \omega(f)$ between a
distribution and a real test function.

---

### [`distributionPairing_add`](../../OSforGFF/Spacetime/Basic.lean#L122) — Lemma *(simp)*

**Statement**: $\langle \omega_1 + \omega_2, a\rangle = \langle \omega_1, a\rangle + \langle \omega_2, a\rangle$ (WeakDual addition is pointwise; by `rfl`).

---

### [`distributionPairing_smul`](../../OSforGFF/Spacetime/Basic.lean#L125) — Lemma *(simp)*

**Statement**: $\langle s \cdot \omega, a\rangle = s\,\langle \omega, a\rangle$ for $s \in \mathbb{R}$ (WeakDual scalar action is pointwise; by `rfl`).

---

### [`pairing_smul_real`](../../OSforGFF/Spacetime/Basic.lean#L130) — Lemma *(simp)*

**Statement**: $\omega(s \cdot a) = s\,\omega(a)$, linearity of the pairing in the test-function argument.

**Proof uses**: `map_smul`

---

### [`distributionPairingCLM`](../../OSforGFF/Spacetime/Basic.lean#L135) — Definition *(simp)*

**Lean signature**
```lean
@[simp] def distributionPairingCLM (a : (SchwartzTestFunction d)) : (FieldConfiguration d) →L[ℝ] ℝ
```

**Informal**: The pairing with a fixed test function $a$, packaged as a continuous
$\mathbb{R}$-linear functional $\omega \mapsto \langle \omega, a\rangle$; continuity is
`WeakDual.eval_continuous`.

---

### [`distributionPairingCLM_apply`](../../OSforGFF/Spacetime/Basic.lean#L147) — Lemma *(simp)*

**Statement**: `distributionPairingCLM a ω = distributionPairing ω a` (by `rfl`).

---

### [`GJGeneratingFunctional`](../../OSforGFF/Spacetime/Basic.lean#L159) — Definition

**Lean signature**
```lean
def GJGeneratingFunctional (dμ_config : ProbabilityMeasure (FieldConfiguration d))
  (J : (SchwartzTestFunction d)) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * (distributionPairing ω J : ℂ)) ∂dμ_config.toMeasure
```

**Informal**: The Glimm-Jaffe generating functional
$$Z[J] = \int \exp\bigl(i\langle\omega, J\rangle\bigr)\, d\mu(\omega),$$
the fundamental object in constructive QFT.

---

### [`schwartz_comp_clm`](../../OSforGFF/Spacetime/Basic.lean#L165) — Definition

**Lean signature**
```lean
def schwartz_comp_clm (f : (SchwartzTestFunctionℂ d)) (L : ℂ →L[ℝ] ℝ) : (SchwartzTestFunction d)
```

**Informal**: Post-composition of a complex test function $f$ with a continuous
$\mathbb{R}$-linear map $L : \mathbb{C} \to \mathbb{R}$, yielding the real test function
$x \mapsto L(f(x))$; smoothness and the polynomial-growth (Schwartz) bounds are verified using
$\lVert L(z)\rVert \le \lVert L\rVert\,\lVert z\rVert$.

---

### [`schwartz_comp_clm_apply`](../../OSforGFF/Spacetime/Basic.lean#L195) — Lemma *(simp)*

**Statement**: $(\mathrm{schwartz\_comp\_clm}\, f\, L)(x) = L(f(x))$ (by `rfl`).

---

### [`complex_testfunction_decompose`](../../OSforGFF/Spacetime/Basic.lean#L200) — Definition

**Lean signature**
```lean
def complex_testfunction_decompose (f : (SchwartzTestFunctionℂ d)) : (SchwartzTestFunction d) × (SchwartzTestFunction d) :=
  (schwartz_comp_clm f Complex.reCLM, schwartz_comp_clm f Complex.imCLM)
```

**Informal**: Decompose a complex test function into its real and imaginary parts as a pair of
real test functions, applying `schwartz_comp_clm` with `Complex.reCLM` / `Complex.imCLM`.

---

### [`complex_testfunction_decompose_fst_apply`](../../OSforGFF/Spacetime/Basic.lean#L204) — Lemma *(simp)*

**Statement**: $(\mathrm{complex\_testfunction\_decompose}\, f).1\, x = \mathrm{Re}(f(x))$.

---

### [`complex_testfunction_decompose_snd_apply`](../../OSforGFF/Spacetime/Basic.lean#L210) — Lemma *(simp)*

**Statement**: $(\mathrm{complex\_testfunction\_decompose}\, f).2\, x = \mathrm{Im}(f(x))$.

---

### [`complex_testfunction_decompose_fst_apply_coe`](../../OSforGFF/Spacetime/Basic.lean#L216) — Lemma *(simp)*

**Statement**: Coerced-to-$\mathbb{C}$ real part: $((\mathrm{decompose}\, f).1\, x : \mathbb{C}) = (\mathrm{Re}(f(x)) : \mathbb{C})$.

---

### [`complex_testfunction_decompose_snd_apply_coe`](../../OSforGFF/Spacetime/Basic.lean#L222) — Lemma *(simp)*

**Statement**: Coerced-to-$\mathbb{C}$ imaginary part: $((\mathrm{decompose}\, f).2\, x : \mathbb{C}) = (\mathrm{Im}(f(x)) : \mathbb{C})$.

---

### [`complex_testfunction_decompose_recompose`](../../OSforGFF/Spacetime/Basic.lean#L228) — Lemma

**Statement**: Recomposition at a point via the decomposition:
$$f(x) = \bigl((\mathrm{decompose}\, f).1\, x : \mathbb{C}\bigr) + i\,\bigl((\mathrm{decompose}\, f).2\, x : \mathbb{C}\bigr),$$
reducing to the identity $z = \mathrm{Re}\, z + i\,\mathrm{Im}\, z$.

---

### [`distributionPairingℂ_real`](../../OSforGFF/Spacetime/Basic.lean#L243) — Definition

**Lean signature**
```lean
def distributionPairingℂ_real (ω : (FieldConfiguration d)) (f : (SchwartzTestFunctionℂ d)) : ℂ
```

**Informal**: Complex pairing of a real field configuration with a complex test function,
defined via the real/imaginary decomposition:
$\langle\omega, f\rangle = \langle\omega, f_{\mathrm{re}}\rangle + i\,\langle\omega, f_{\mathrm{im}}\rangle$.

---

### [`GJGeneratingFunctionalℂ`](../../OSforGFF/Spacetime/Basic.lean#L250) — Definition

**Lean signature**
```lean
def GJGeneratingFunctionalℂ (dμ_config : ProbabilityMeasure (FieldConfiguration d))
  (J : (SchwartzTestFunctionℂ d)) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * (distributionPairingℂ_real ω J)) ∂dμ_config.toMeasure
```

**Informal**: The complex version of the generating functional, integrating
$\exp(i\langle\omega, J\rangle_{\mathbb{C}})$ over field configurations.

---

### [`GJMean`](../../OSforGFF/Spacetime/Basic.lean#L255) — Definition

**Lean signature**
```lean
def GJMean (dμ_config : ProbabilityMeasure (FieldConfiguration d))
  (φ : (SchwartzTestFunction d)) : ℝ :=
  ∫ ω, distributionPairing ω φ ∂dμ_config.toMeasure
```

**Informal**: The mean field $\int \langle\omega, \varphi\rangle\, d\mu(\omega)$ in the
Glimm-Jaffe framework.

---

### [`SpatialCoords`](../../OSforGFF/Spacetime/Basic.lean#L262) — Definition *(abbrev)*

**Lean signature**
```lean
abbrev SpatialCoords (d : ℕ) := EuclideanSpace ℝ (Fin (d - 1))
```

**Informal**: Spatial coordinates $\mathbb{R}^{d-1}$ (space without time), as a Euclidean space
for the $L^2$ norm.

---

### [`SpatialL2`](../../OSforGFF/Spacetime/Basic.lean#L265) — Definition *(abbrev)*

**Lean signature**
```lean
abbrev SpatialL2 (d : ℕ) := Lp ℝ 2 (volume : Measure (SpatialCoords d))
```

**Informal**: The real-valued $L^2$ space on spatial slices $\mathbb{R}^{d-1}$.

---

### [`spatialPart`](../../OSforGFF/Spacetime/Basic.lean#L268) — Definition

**Lean signature**
```lean
def spatialPart (x : SpaceTime d) : SpatialCoords d
```

**Informal**: Extract the spatial part (coordinates $1, \dots, d-1$) of a spacetime point, via
the Euclidean-space equivalence.

---

### [`E`](../../OSforGFF/Spacetime/Basic.lean#L273) — Definition

**Lean signature**
```lean
def E (m : ℝ) (k : SpatialCoords d) : ℝ :=
  Real.sqrt (‖k‖^2 + m^2)
```

**Informal**: The relativistic energy function $E(k) = \sqrt{\lVert k\rVert^2 + m^2}$ on spatial
momentum space.

---

*This file has **22** definitions and **10** theorems/lemmas (0 with sorry).*
