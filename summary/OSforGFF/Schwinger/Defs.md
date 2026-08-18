# `Defs.lean` — Informal Summary

> **Source**: [`OSforGFF/Schwinger/Defs.lean`](../../OSforGFF/Schwinger/Defs.lean)
> **Generated**: 2026-07-05 (regenerated from current source)

## Overview

This file defines the **Schwinger functions** (Euclidean $n$-point correlation functions) of a
probability measure on field configurations, together with the surrounding generating-functional
framework. For a measure $\mu$ on $\mathscr{S}'(\mathbb{R}^d)$ the $n$-point function is
$S_n(f_1,\dots,f_n) = \int \langle \omega, f_1\rangle \cdots \langle \omega, f_n\rangle\, d\mu(\omega)$,
the $n$-th moment of the field operators $\varphi(f) = \langle \omega, f\rangle$. Everything is
generic in the spacetime dimension: the section variables are `{d : ℕ}` (and `{𝕜 : Type} [RCLike 𝕜]`),
and the field lives on `FieldConfiguration d` paired with real test functions `SchwartzTestFunction d` or
complex test functions `SchwartzTestFunctionℂ d`. The file provides the real Schwinger functions and their
1- and 2-point specializations, the complex-test-function versions, a bilinearity predicate for the
complex 2-point function (with a proof that integrability implies bilinearity), a predicate
`IsGaussianMeasure` capturing the exponential-of-quadratic generating functional, and a private
`AQFT_exponential_series` namespace developing the Taylor-partial-sum machinery
$Z[J] = \sum_n (i)^n/n!\, S_n(J,\dots,J)$ needed to connect $Z[J]$ to the moments. It closes with two
abbreviations for test functions on product spacetimes. No new axioms are declared here.

## Status

**Main result**: Fully proven (0 sorries).

**Length**: 408 lines, 10 definition(s) + 8 theorem(s)/lemma(s)

---

## Schwinger Functions

### [`SchwingerFunction`](../../OSforGFF/Schwinger/Defs.lean#L58) — Definition

**Lean signature**
```lean
def SchwingerFunction (dμ_config : ProbabilityMeasure (FieldConfiguration d)) (n : ℕ)
  (f : Fin n → (SchwartzTestFunction d)) : ℝ :=
  ∫ ω, (∏ i, distributionPairing ω (f i)) ∂dμ_config.toMeasure
```

**Informal**: The $n$-th Schwinger function, the $n$-point correlation of field operators
$$S_n(f_1,\dots,f_n) = \int \langle \omega, f_1\rangle\, \langle \omega, f_2\rangle \cdots \langle \omega, f_n\rangle \; d\mu(\omega),$$
the fundamental object of constructive QFT.

---

### [`SchwingerFunction₁`](../../OSforGFF/Schwinger/Defs.lean#L63) — Definition

**Lean signature**
```lean
def SchwingerFunction₁ (dμ_config : ProbabilityMeasure (FieldConfiguration d))
  (f : (SchwartzTestFunction d)) : ℝ :=
  SchwingerFunction dμ_config 1 ![f]
```

**Informal**: The 1-point Schwinger function (the mean field), i.e. $S_1(f)$.

---

### [`SchwingerFunction₂`](../../OSforGFF/Schwinger/Defs.lean#L68) — Definition

**Lean signature**
```lean
def SchwingerFunction₂ (dμ_config : ProbabilityMeasure (FieldConfiguration d))
  (f g : (SchwartzTestFunction d)) : ℝ :=
  SchwingerFunction dμ_config 2 ![f, g]
```

**Informal**: The 2-point Schwinger function (the covariance), i.e. $S_2(f, g)$.

---

### [`schwinger_eq_mean`](../../OSforGFF/Schwinger/Defs.lean#L74) — Lemma

**Statement**: The 1-point Schwinger function equals the Glimm-Jaffe mean:
$$S_1(f) = \mathrm{GJMean}(\mu, f).$$

**Proof uses**: `SchwingerFunction₁`, `SchwingerFunction`, `GJMean`, `simp` on the singleton product over `Fin 1`

---

### [`schwinger_eq_covariance`](../../OSforGFF/Schwinger/Defs.lean#L83) — Lemma

**Statement**: The 2-point Schwinger function equals the direct covariance integral:
$$S_2(f, g) = \int \langle \omega, f\rangle\, \langle \omega, g\rangle \; d\mu(\omega).$$

**Proof uses**: `SchwingerFunction₂`, `SchwingerFunction`, `Fin.prod_univ_two`

---

### [`schwinger_vanishes_centered`](../../OSforGFF/Schwinger/Defs.lean#L91) — Lemma

**Statement**: For a centered measure (with $\mathrm{GJMean}(\mu, f) = 0$ for all real test functions $f$), the 1-point function vanishes: $S_1(f) = 0$.

**Proof uses**: [`schwinger_eq_mean`](../../OSforGFF/Schwinger/Defs.lean#L74), the centering hypothesis

---

### [`SchwingerFunctionℂ`](../../OSforGFF/Schwinger/Defs.lean#L98) — Definition

**Lean signature**
```lean
def SchwingerFunctionℂ (dμ_config : ProbabilityMeasure (FieldConfiguration d)) (n : ℕ)
  (f : Fin n → (SchwartzTestFunctionℂ d)) : ℂ :=
  ∫ ω, (∏ i, distributionPairingℂ_real ω (f i)) ∂dμ_config.toMeasure
```

**Informal**: The complex-valued Schwinger function for complex test functions, using the
complex-linear real pairing $\mathrm{distributionPairingℂ\_real}$ in place of the real pairing.

---

### [`SchwingerFunctionℂ₂`](../../OSforGFF/Schwinger/Defs.lean#L104) — Definition

**Lean signature**
```lean
def SchwingerFunctionℂ₂ (dμ_config : ProbabilityMeasure (FieldConfiguration d))
  (φ ψ : (SchwartzTestFunctionℂ d)) : ℂ :=
  SchwingerFunctionℂ dμ_config 2 ![φ, ψ]
```

**Informal**: The complex 2-point Schwinger function $S_2^{\mathbb{C}}(\varphi, \psi)$, the natural
extension of `SchwingerFunction₂` to complex test functions.

---

### [`CovarianceBilinear`](../../OSforGFF/Schwinger/Defs.lean#L110) — Definition

**Lean signature**
```lean
def CovarianceBilinear (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (c : ℂ) (φ₁ φ₂ ψ : (SchwartzTestFunctionℂ d)),
    SchwingerFunctionℂ₂ dμ_config (c • φ₁) ψ = c * SchwingerFunctionℂ₂ dμ_config φ₁ ψ ∧
    SchwingerFunctionℂ₂ dμ_config (φ₁ + φ₂) ψ = SchwingerFunctionℂ₂ dμ_config φ₁ ψ + SchwingerFunctionℂ₂ dμ_config φ₂ ψ ∧
    SchwingerFunctionℂ₂ dμ_config φ₁ (c • ψ) = c * SchwingerFunctionℂ₂ dμ_config φ₁ ψ ∧
    SchwingerFunctionℂ₂ dμ_config φ₁ (ψ + φ₂) = SchwingerFunctionℂ₂ dμ_config φ₁ ψ + SchwingerFunctionℂ₂ dμ_config φ₁ φ₂
```

**Informal**: The predicate that $S_2^{\mathbb{C}}$ is $\mathbb{C}$-bilinear in each argument
(scalar and additive in both slots) — a key property for Gaussian measures and essential for OS0
analyticity.

---

### [`CovarianceBilinear_of_integrable`](../../OSforGFF/Schwinger/Defs.lean#L119) — Lemma

**Statement**: If for all complex test functions $\varphi, \psi$ the product pairing
$\omega \mapsto \mathrm{distributionPairingℂ\_real}(\omega, \varphi)\,\mathrm{distributionPairingℂ\_real}(\omega, \psi)$
is integrable under $\mu$, then $S_2^{\mathbb{C}}$ is $\mathbb{C}$-bilinear, i.e.
`CovarianceBilinear dμ_config` holds.

**Proof uses**: `pairing_linear_combo`, `integral_smul`, `integral_add`, `Fin.prod_univ_two`, unfolding `SchwingerFunctionℂ₂`/`SchwingerFunctionℂ`

---

## Exponential Series Connection to Generating Functional

### [`IsGaussianMeasure`](../../OSforGFF/Schwinger/Defs.lean#L259) — Definition

**Lean signature**
```lean
def IsGaussianMeasure (dμ : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∃ (Cov : (SchwartzTestFunction d) → (SchwartzTestFunction d) → ℝ),
    ∀ J : (SchwartzTestFunction d),
      GJGeneratingFunctional dμ J = Complex.exp ((-(1 : ℂ) / 2) * (Cov J J : ℂ))
```

**Informal**: A (centered) Gaussian field measure: there exists a covariance form $\mathrm{Cov}$ such
that the generating functional is the exponential of a quadratic form,
$$Z[J] = \exp\!\bigl(-\tfrac{1}{2}\,\mathrm{Cov}(J, J)\bigr) \quad \text{for all real test functions } J.$$

---

### [`expIPartial`](../../OSforGFF/Schwinger/Defs.lean#L282) — Definition *(private)*

**Lean signature**
```lean
private def expIPartial (N : ℕ) (x : ℝ) : ℂ :=
  (Finset.range (N+1)).sum (fun n =>
    (Complex.I : ℂ) ^ n * (x : ℂ) ^ n / (n.factorial : ℂ))
```

**Informal**: The finite Taylor partial sum of $\exp(i x)$ (complex valued),
$\sum_{n=0}^{N} i^n x^n / n!$, in the `AQFT_exponential_series` namespace.

---

### [`expIPartial_tendsto`](../../OSforGFF/Schwinger/Defs.lean#L287) — Lemma *(private)*

**Statement**: The partial sums converge pointwise to the exponential:
$$\lim_{N \to \infty} \mathrm{expIPartial}(N, x) = \exp(i\,x).$$

**Proof uses**: `NormedSpace.exp_series_hasSum_exp'`, `HasSum.tendsto_sum_nat`, `Filter.tendsto_add_atTop_nat`

---

### [`expIPartial_norm_le`](../../OSforGFF/Schwinger/Defs.lean#L318) — Lemma *(private)*

**Statement**: The partial sums are uniformly dominated:
$$\lVert \mathrm{expIPartial}(N, x) \rVert \le \exp(\lvert x \rvert).$$

**Proof uses**: `norm_sum_le`, `Finset.sum_le_sum`, `NormedSpace.exp_series_hasSum_exp'`, `Summable.sum_le_tsum`

---

### [`prod_const_pow`](../../OSforGFF/Schwinger/Defs.lean#L374) — Lemma *(private)*

**Statement**: The product over `Fin n` of a constant is its $n$-th power:
$$\prod_{i : \mathrm{Fin}\, n} x = x^n.$$

**Proof uses**: `Fin.prod_const`

---

### [`schwinger_eq_integral_pow`](../../OSforGFF/Schwinger/Defs.lean#L379) — Lemma *(private)*

**Statement**: For a measure on `FieldConfiguration 4` and test function `J : SchwartzTestFunction 4`, the
diagonal Schwinger function equals the integral of the $n$-th power of the pairing:
$$S_n(J,\dots,J) = \int \langle \omega, J\rangle^n \; d\mu(\omega).$$
(This private lemma is specialized to dimension $d = 4$.)

**Proof uses**: `SchwingerFunction`, [`prod_const_pow`](../../OSforGFF/Schwinger/Defs.lean#L374)

---

## Basic Distribution Framework

### [`SpaceTimeProduct`](../../OSforGFF/Schwinger/Defs.lean#L404) — Abbreviation

**Lean signature**
```lean
abbrev SpaceTimeProduct (d n : ℕ) := (Fin n) → (SpaceTime d)
```

**Informal**: The product space of $n$ copies of spacetime $\mathbb{R}^d$.

---

### [`TestFunctionProduct`](../../OSforGFF/Schwinger/Defs.lean#L407) — Abbreviation

**Lean signature**
```lean
abbrev TestFunctionProduct (d n : ℕ) := SchwartzMap (SpaceTimeProduct d n) ℝ
```

**Informal**: The space of real Schwartz test functions on the $n$-fold product spacetime, used for
viewing Schwinger functions as distributions on product spaces.

---

*This file has **10** definitions and **8** theorems/lemmas (0 with sorry).*
