# `Dim4.lean` — Informal Summary

> **Source**: [`OSforGFF/Instances/Dim4.lean`](../../OSforGFF/Instances/Dim4.lean)
> **Generated**: 2026-07-05 (regenerated from current source)

## Overview

This file supplies the **four-dimensional** instance of the `GFFPropagator` typeclass. The radial
profile of the free covariance in $d = 4$ is the Bessel closed form $(m/(4\pi^2 r))\,K_1(mr)$. The
core work is evaluating the generic proper-time (Schwinger) integral
[`properTimeCovariance`](../../OSforGFF/Covariance/Propagator.lean#L48) in closed form as the order
$\nu = -1$ case of the master identity
[`schwingerIntegral_eq_besselK1`](../../OSforGFF/General/BesselK.lean#L246). The file packages the
closed form as [`instGFFPropagatorDim4`](../../OSforGFF/Instances/Dim4.lean#L56), supplies the `Fact`
order bounds $2 \le 4$ (time/space split) and $4 \le 5$ (OS3 proper-time Fubini domination), and
also gives the explicit position-space kernel [`freeCovarianceBessel`](../../OSforGFF/Instances/Dim4.lean#L65)
(with its abbreviation [`freeCovariance4`](../../OSforGFF/Instances/Dim4.lean#L71)) together with the
definitional identity [`freeCovariance_dim4_eq`](../../OSforGFF/Instances/Dim4.lean#L75) showing that
at $d = 4$ the generic kernel [`freeCovariance`](../../OSforGFF/Covariance/Propagator.lean#L478)
coincides with the Bessel kernel.

## Status

**Main result**: Fully proven (0 sorries).

**Length**: 78 lines, 5 definition(s) + 2 theorem(s)/lemma(s)

---

### [`properTimeCovariance_dim4_eq`](../../OSforGFF/Instances/Dim4.lean#L29) — Theorem

**Statement**: For mass $m > 0$ and separation $r > 0$, the generic proper-time covariance in four
dimensions collapses to the Bessel-$K_1$ profile:
$$\mathrm{properTimeCovariance}\;4\;m\;r = \frac{m}{4\pi^2 r}\,K_1(mr).$$

**Informal**: Rewrites the proper-time integral with the constant-pull-out lemma, recognizes the
$d = 4$ exponent $t^{-4/2} = t^{-2} = 1/t^2$, applies the master Schwinger–$K_1$ identity, and
finishes with `field_simp`.

**Proof uses**: [`properTimeCovariance_const_mul`](../../OSforGFF/Covariance/Propagator.lean#L70),
[`schwingerIntegral_eq_besselK1`](../../OSforGFF/General/BesselK.lean#L246),
`Real.rpow_neg`, `Real.rpow_two`, `Real.pi_ne_zero`

---

### [`instFactTwoLeFour`](../../OSforGFF/Instances/Dim4.lean#L49) — Definition *(instance)*

**Lean signature**
```lean
instance instFactTwoLeFour : Fact ((2 : ℕ) ≤ 4)
```

**Informal**: The order bound $2 \le 4$, needed for the time/space split in the generic covariance
construction.

---

### [`instFactFourLeFive`](../../OSforGFF/Instances/Dim4.lean#L52) — Definition *(instance)*

**Lean signature**
```lean
instance instFactFourLeFive : Fact ((4 : ℕ) ≤ 5)
```

**Informal**: The order bound $4 \le 5$, entering the OS3 proper-time Fubini domination.

---

### [`instGFFPropagatorDim4`](../../OSforGFF/Instances/Dim4.lean#L56) — Definition *(instance)*

**Lean signature**
```lean
noncomputable instance instGFFPropagatorDim4 (m : ℝ) [Fact (0 < m)] :
    GFFPropagator 4 m where
  Cprofile r := if r = 0 then 0 else (m / (4 * Real.pi ^ 2 * r)) * besselK1 (m * r)
  schwinger_eq r hr := ...
```

**Informal**: The four-dimensional free propagator. Its radial profile `Cprofile` is the Bessel
closed form $(m/(4\pi^2 r))\,K_1(mr)$, regularized to $0$ at $r = 0$; the required `schwinger_eq`
bridge identifies it with the generic
[`properTimeCovariance`](../../OSforGFF/Covariance/Propagator.lean#L48) for $r > 0$ via
[`properTimeCovariance_dim4_eq`](../../OSforGFF/Instances/Dim4.lean#L29).

**Proof uses**: [`properTimeCovariance_dim4_eq`](../../OSforGFF/Instances/Dim4.lean#L29),
[`GFFPropagator`](../../OSforGFF/Covariance/Propagator.lean#L405),
[`besselK1`](../../OSforGFF/General/BesselFunction.lean#L27)

---

### [`freeCovarianceBessel`](../../OSforGFF/Instances/Dim4.lean#L65) — Definition

**Lean signature**
```lean
noncomputable def freeCovarianceBessel (m : ℝ) (x y : SpaceTime 4) : ℝ :=
  let r := ‖x - y‖
  if r = 0 then 0
  else (m / (4 * Real.pi ^ 2 * r)) * besselK1 (m * r)
```

**Informal**: The free covariance in position space via the Bessel representation,
$C(x, y) = (m/(4\pi^2\,\lVert x - y \rVert))\,K_1(m\,\lVert x - y \rVert)$, regularized to $0$ at
coincident points. This is the explicit massive scalar field propagator in four dimensions.

---

### [`freeCovariance4`](../../OSforGFF/Instances/Dim4.lean#L71) — Abbreviation

**Lean signature**
```lean
noncomputable abbrev freeCovariance4 (m : ℝ) (x y : SpaceTime 4) : ℝ :=
  freeCovarianceBessel m x y
```

**Informal**: The free covariance in position space, an abbreviation for the Bessel representation
[`freeCovarianceBessel`](../../OSforGFF/Instances/Dim4.lean#L65).

---

### [`freeCovariance_dim4_eq`](../../OSforGFF/Instances/Dim4.lean#L75) — Lemma

**Statement**: At $d = 4$ the generic position-space kernel is definitionally the Bessel kernel: for
all $x, y \in$ `SpaceTime 4`,
$$\mathrm{freeCovariance}\;4\;m\;x\;y = \mathrm{freeCovariance4}\;m\;x\;y.$$

**Proof uses**: *(definitional — `rfl`)*

---

*This file has **5** definitions and **2** theorems/lemmas (0 with sorry).*
