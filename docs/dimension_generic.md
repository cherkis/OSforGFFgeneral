# The dimension-generic architecture

How one library proves the Osterwalder–Schrader axioms for the free field in every
dimension `2 ≤ d ≤ 5` at once, and what a new dimension has to supply.

## The idea in one paragraph

Almost nothing in the OS proofs is about four dimensions. The free covariance is a radial
kernel `C(x,y) = C_d(|x−y|)`, and every axiom consumes it through a handful of analytic
facts — integrability, positivity of its Fourier transform, exponential decay, continuity
away from the origin — all of which follow from the **proper-time (Schwinger)
representation**

    C_d(r) = ∫₀^∞ e^{−s m²} · (4πs)^{−d/2} e^{−r²/4s} ds,

one uniform formula for every `d`. What genuinely varies with the dimension is only the
*closed form* of this integral: `(m/4π²r)K₁(mr)` in 4D, the Yukawa potential
`e^{−mr}/4πr` in 3D, `(1/2π)K₀(mr)` in 2D. The library therefore isolates the dimension
behind a two-field typeclass (`Covariance/Propagator.lean`):

```
class GFFPropagator (d : ℕ) (m : ℝ) [Fact (0 < m)] [Fact (2 ≤ d)] where
  Cprofile     : ℝ → ℝ                                      -- the closed form
  schwinger_eq : ∀ r > 0, Cprofile r = properTimeCovariance d m r
```

An instance for a new dimension owes exactly one computation: evaluating the proper-time
integral to its closed form. Everything else — the measure construction, all of OS0–OS4,
non-triviality — is proved once, generically, from `properTimeCovariance`.

## The engine

Facts proved uniformly in `d` and transported to `Cprofile` through `schwinger_eq`:

| Fact | Statement | Consumed by |
|------|-----------|-------------|
| `GFFPropagator.integrable` | `x ↦ C_d(‖x‖)` is L¹ | OS1 local integrability |
| `GFFPropagator.fourier_eq` | `𝓕[C_d(‖·‖)] = 1/((2π)²‖k‖²+m²)` | Parseval bridge, Minlos |
| `GFFPropagator.decayBound` | `C_d(r) ≤ A e^{−(m/2)r}` for `r ≥ 1` | OS4 clustering |
| `properTimeCovariance_continuousOn` | continuity on `(0,∞)` | two-point kernel, OS1 |

On top of these, `Covariance/ParsevalGeneric.lean` derives the momentum-space form of the
covariance pairing (`⟨f, C f̄⟩ = ∫ ‖𝓕f‖²·P`, hence positivity), its bilinear algebra and
reflection/Euclidean invariance, and `Covariance/RealForm.lean` realizes `C(f,f) = ‖Tf‖²`
via the square-root propagator embedding `T = √P ∘ 𝓕` — the continuity and positivity
hypotheses of the Minlos theorem, by which the measure exists on `S′(ℝ^d)`.

## Where the dimension actually shows up

- **Everywhere `d` is a silent parameter.** Types (`SpaceTime d = ℝ^d`, spatial slice
  `ℝ^{d−1}`), Plancherel factors `(2π)^d`, `(2π)^{d−1}`, heat-kernel prefactors
  `(4πs)^{−d/2}`, Schwartz decay exponents. These thread through mechanically.
- **OS3 and the bound `d ≤ 5`.** The mixed representation requires exchanging the
  proper-time integral with the spatial momentum integral. The dominating function comes
  from first-order vanishing of positive-time test functions at the time boundary, giving
  `s^{3/2} e^{−s(‖k‖²+m²)}` (the power is dimension-independent: the heat-kernel prefactor
  `(4πs)^{−d/2}` cancels against the `(4πs)^{(d−1)/2}` of the spatial Fourier transform).
  Its `k`-integral is `∼ s^{(4−d)/2} e^{−sm²}`, integrable near `s = 0` iff `d ≤ 5`. The
  hypothesis `[Fact (d ≤ 5)]` enters only there (`OS3_MixedRepInfra.integrable_dominate_G`)
  and propagates to the OS3 axiom and the master theorem. Higher-order boundary vanishing
  would remove the bound; `d ∈ {2,3,4}` does not need it.
- **The UV statement.** `C(x,y) → ∞` as `x → y` (`OS/NonTrivial.lean`) is proved from the
  Bessel closed form and is a statement about the 4D instance; non-degeneracy of the
  measure (injectivity of `T`, positive variance of every pairing) is generic.

## The instance layer

`Instances/Dim4Bessel.lean` holds the four-dimensional momentum/Bessel analysis (the
evaluation `∫₀^∞ e^{−sm²}(4πs)^{−2}e^{−r²/4s} ds = (m/4π²r)K₁(mr)` and its supporting
special-function theory); `Instances/Dim4.lean` packages it as `GFFPropagator 4 m`, and at
this instance the generic kernel is *definitionally* the Bessel kernel. `Instances/Dim3.lean`
provides the three-dimensional instance: the Yukawa kernel `e^{−mr}/(4πr)`, obtained by
reducing the proper-time integral to the `K_{1/2}` Laplace identity
`LaplaceIntegral.laplace_integral_half_power` via the reciprocal substitution `t = 1/s`
(`integral_comp_rpow_Ioi` at `p = −1`) — no new Bessel theory is needed. The master theorem

    gaussianFreeField_satisfies_all_OS_axioms_generic :
      ∀ {d} [Fact (2 ≤ d)] (m) [Fact (0 < m)] [GFFPropagator d m] [Fact (d ≤ 5)],
        SatisfiesAllOS (gaussianFreeField_free d m)

specializes to the original four-dimensional statement `SatisfiesAllOS (μ_GFF m)` and to the
three-dimensional `SatisfiesAllOS (μ_GFF3 m)`, each with the same axiom footprint
(`propext`, `Classical.choice`, `Quot.sound` — nothing else); `Guardrails.lean` freezes those
facts (generic, `d = 4`, `d = 3`) into the build. A `d = 2` headline theorem requires only the
`K₀` evaluation of the proper-time integral.
