-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import Mathlib

/-!
# The DOZZ formula

A standalone, Mathlib-only statement of the theorem of Kupiainen, Rhodes and Vargas: the
three-point structure constants of Liouville conformal field theory on the Riemann sphere, defined
through the Gaussian free field and its Gaussian multiplicative chaos, are given by the formula of
Dorn–Otto and Zamolodchikov–Zamolodchikov. Source: A. Kupiainen, R. Rhodes and V. Vargas,
*Integrability of Liouville theory: proof of the DOZZ formula*, Ann. of Math. 191 (2020), 81–166,
cited as [KRV], with the numbering of arXiv:1707.08785; and F. David, A. Kupiainen, R. Rhodes and
V. Vargas, *Liouville quantum gravity on the Riemann sphere*, Comm. Math. Phys. 342 (2016),
869–907, cited as [DKRV].

* `dozz_formula` ([KRV, Theorem 2.4]). For `0 < γ < 2`, `μ > 0` and real charges `α₁, α₂, α₃`
  satisfying the extended Seiberg bounds with `s ∉ {0, -1, -2, …}`, the structure constant
  `C_γ(α₁, α₂, α₃) = 2 μ^{-s} γ^{-1} Γ(s) E[ρ(α₁, α₂, α₃)^{-s}]` equals the DOZZ formula.
* `dozz_unitVolume`: on the whole extended Seiberg domain, including the poles `s ∈ -ℕ` of
  `Γ(s)`, the unit-volume structure constant `C̄_γ = (2/γ) E[ρ^{-s}]` is the limit of
  `μ^s C^{DOZZ}_γ / Γ(s)` along the points of the domain where `s ∉ -ℕ`.
* `dozz_existence`: for `0 < γ < 2` there are a function `Υ_{γ/2}` and a probability space
  carrying an equator-pinned Gaussian free field and its chaos, so the theorems are not vacuous.
* `IsUpsilon.unique`, `isCircleAverage_law`, `equatorGFF_GMC_unique_ae`,
  `equatorGFF_GMC_nontrivial`, `equatorGFF_GMC_law_transport`: the objects defined by
  characterizations are determined by them. `Υ_{γ/2}` is unique; every circle-average process is
  the centered Gaussian process with the covariance of the circle averages of the field; the chaos
  is almost surely unique and not almost surely zero; and the joint law of the field and its chaos
  is the same in every model.
* `equatorGFF_extendedSeiberg_rho_moment`: under the extended Seiberg bounds the moment
  `E[ρ^{-s}]` is positive and finite.

The field and its chaos are characterized by their laws ([KRV, §2.1]), so the theorems hold on
every probability space carrying them. At `s ∈ -ℕ` [KRV, §2.2] sets the structure constant to `+∞`
(Mathlib's `Gamma` is `0` there): `dozz_formula` excludes these points, and `dozz_unitVolume`
covers them. `ENNReal.toReal` would send an infinite expectation to `0`, which
`equatorGFF_extendedSeiberg_rho_moment` rules out on the extended Seiberg domain.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZChallenge

/-! ## Constants and special functions -/

/-- `Q = 2/γ + γ/2` ([KRV, §1.1]). -/
def Q (γ : ℝ) : ℝ := 2 / γ + γ / 2

/-- The exponent `s = (α₁ + α₂ + α₃ - 2Q)/γ` of three charges ([KRV, §2.2]). -/
def sExp (γ : ℝ) (α₁ α₂ α₃ : ℝ) : ℝ := (α₁ + α₂ + α₃ - 2 * Q γ) / γ

/-- The extended Seiberg bounds for three charges ([KRV, §2.2]): `αₖ < Q` for each `k` and
`-s < min (4/γ², minₖ 2(Q - αₖ)/γ)`. -/
def ExtendedSeiberg3 (γ α₁ α₂ α₃ : ℝ) : Prop :=
  α₁ < Q γ ∧ α₂ < Q γ ∧ α₃ < Q γ ∧
    -sExp γ α₁ α₂ α₃ <
      min (4 / γ ^ 2) (min (2 / γ * (Q γ - α₁)) (min (2 / γ * (Q γ - α₂)) (2 / γ * (Q γ - α₃))))

/-- `|x|₊ = max(1, |x|)` ([KRV, §2.1]). -/
def normPlus (x : ℂ) : ℝ := max 1 ‖x‖

/-- `l(x) = Γ(x)/Γ(1 - x)` ([KRV, §1.2]). -/
def lFun (x : ℂ) : ℂ := Complex.Gamma x / Complex.Gamma (1 - x)

/-- The integrand of `log Υ_{γ/2}(z) = ∫₀^∞ ((Q/2 - z)² e^{-t} - sinh²((Q/2 - z) t/2) /
(sinh(tγ/4) sinh(t/γ))) dt/t` ([KRV, §1.2]), as a function of `t`. -/
def upsilonLogIntegrand (γ : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  ((Q γ / 2 - z) ^ 2 * Real.exp (-t)
    - Complex.sinh ((Q γ / 2 - z) * (t / 2)) ^ 2
      / (Real.sinh (t * γ / 4) * Real.sinh (t / γ))) / t

/-- `log Υ_{γ/2}(z)` as the integral over `t > 0` ([KRV, §1.2]); it is meaningful on the strip
`0 < Re z < Q`. -/
def upsilonLog (γ : ℝ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), upsilonLogIntegrand γ z t

/-- `U` is the function `Υ_{γ/2}` ([KRV, §1.2]): it is entire, and `U z = exp (log Υ_{γ/2}(z))`
on the strip `0 < Re z < Q`. -/
def IsUpsilon (γ : ℝ) (U : ℂ → ℂ) : Prop :=
  Differentiable ℂ U ∧
    ∀ z : ℂ, 0 < z.re → z.re < Q γ → U z = Complex.exp (upsilonLog γ z)

/-- `Υ_{γ/2}` is unique: two functions satisfying `IsUpsilon γ` coincide. -/
theorem IsUpsilon.unique {γ : ℝ} {U V : ℂ → ℂ} (hγ : 0 < γ) (hU : IsUpsilon γ U)
    (hV : IsUpsilon γ V) : U = V := by
  sorry

/-- The base `π μ l(γ²/4)` of the DOZZ formula ([KRV, §1.2]); `l(γ²/4)` is real for real `γ`. -/
def dozzBase (γ μ : ℝ) : ℝ := Real.pi * μ * (lFun ((γ : ℂ) ^ 2 / 4)).re

/-- The DOZZ formula `C^{DOZZ}_γ(α₁, α₂, α₃)` ([KRV, §1.2]) with `Υ_{γ/2} = U` and
`ᾱ = α₁ + α₂ + α₃`:
`(π μ l(γ²/4) (γ/2)^{2 - γ²/2})^{(2Q - ᾱ)/γ} Υ'(0) Υ(α₁) Υ(α₂) Υ(α₃) /
(Υ((ᾱ - 2Q)/2) Υ(ᾱ/2 - α₁) Υ(ᾱ/2 - α₂) Υ(ᾱ/2 - α₃))`. -/
def dozzFormula (γ μ : ℝ) (U : ℂ → ℂ) (α₁ α₂ α₃ : ℂ) : ℂ :=
  ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ) ^ ((2 * Q γ - (α₁ + α₂ + α₃)) / γ) *
    (deriv U 0 * U α₁ * U α₂ * U α₃) /
    (U ((α₁ + α₂ + α₃ - 2 * Q γ) / 2) * U ((α₁ + α₂ + α₃) / 2 - α₁) *
      U ((α₁ + α₂ + α₃) / 2 - α₂) * U ((α₁ + α₂ + α₃) / 2 - α₃))

/-! ## The Gaussian free field pinned on the equator -/

/-- Smooth compactly supported real test functions on `ℂ`. -/
abbrev TestFn := 𝓓((⊤ : Opens ℂ), ℝ)

/-- Real distributions on `ℂ`. -/
abbrev Distr := 𝓓'((⊤ : Opens ℂ), ℝ)

/-- The covariance kernel `G(x, y) = log(1/|x - y|) + log|x|₊ + log|y|₊` ([KRV, §2.1]). On the
diagonal, a null set for every measure used below, `Real.log 0 = 0`. -/
def gffKernel (x y : ℂ) : ℝ :=
  -Real.log ‖x - y‖ + Real.log (normPlus x) + Real.log (normPlus y)

/-- The covariance form `∬ f(x) G(x, y) g(y) dx dy` on test functions. -/
def gffCov (f g : TestFn) : ℝ := ∫ x, ∫ y, f x * gffKernel x y * g y

/-- `X` is the Gaussian free field pinned on the equator under `P` ([KRV, §2.1]): every test
evaluation `X(f)` is measurable and centered Gaussian with variance `gffCov f f`. Since each `X ω`
is linear, this fixes every finite-dimensional law. -/
def IsEquatorGFF {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) : Prop :=
  IsProbabilityMeasure P ∧
    ∀ f : TestFn, Measurable (fun ω => X ω f) ∧
      ∃ v : ℝ≥0, (v : ℝ) = gffCov f f ∧ P.map (fun ω => X ω f) = gaussianReal 0 v

/-! ## Circle averages and Gaussian multiplicative chaos -/

/-- The uniform probability measure `σ_{x,r}` on the circle of center `x` and radius `e^{-r}`. -/
def circleMeasure (x : ℂ) (r : ℝ) : Measure ℂ :=
  ENNReal.ofReal (2 * Real.pi)⁻¹ •
    (volume.restrict (Ioc 0 (2 * Real.pi))).map (circleMap x (Real.exp (-r)))

/-- The cross energy `∬ f(y) G(y, z) dy dσ_{x,r}(z)`. -/
def circleCross (x : ℂ) (r : ℝ) (f : TestFn) : ℝ :=
  ∫ y, f y * ∫ z, gffKernel y z ∂circleMeasure x r

/-- The energy `∬ G dσ_{x,r} dσ_{x,r}` of the circle measure. -/
def circleSelfEnergy (x : ℂ) (r : ℝ) : ℝ :=
  ∫ z, ∫ w, gffKernel z w ∂circleMeasure x r ∂circleMeasure x r

/-- The energy `∬ G d(f dx - σ_{x,r}) d(f dx - σ_{x,r})` of the signed measure
`f dx - σ_{x,r}`. -/
def circleEnergyGap (x : ℂ) (r : ℝ) (f : TestFn) : ℝ :=
  gffCov f f - 2 * circleCross x r f + circleSelfEnergy x r

/-- `Xc ω x r` is the circle average `X_r(x)` of `X` over the circle of center `x` and radius
`e^{-r}` ([KRV, §2.1]): it is jointly measurable in `(ω, x)`, square integrable, and the `L²(P)`
limit of `X(fₙ)` along every sequence of test functions `fₙ` whose energy distance to the circle
measure tends to `0`. -/
def IsCircleAverage {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) : Prop :=
  (∀ r : ℝ, Measurable (fun p : Ω × ℂ => Xc p.1 p.2 r)) ∧
    (∀ (x : ℂ) (r : ℝ), MemLp (fun ω => Xc ω x r) 2 P) ∧
    ∀ (x : ℂ) (r : ℝ) (f : ℕ → TestFn),
      Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 0) →
        Tendsto (fun n => eLpNorm (fun ω => X ω (f n) - Xc ω x r) 2 P) atTop (𝓝 0)

/-- Circle averages are determined in law: a circle-average process of the field is a centered
Gaussian process with covariance `E[X_r(x) X_s(y)] = ∬ G dσ_{x,r} dσ_{y,s}`. -/
theorem isCircleAverage_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) :
    IsGaussianProcess (fun p : ℂ × ℝ => fun ω => Xc ω p.1 p.2) P ∧
      (∀ (x : ℂ) (r : ℝ), ∫ ω, Xc ω x r ∂P = 0) ∧
      ∀ (x y : ℂ) (r s : ℝ), ∫ ω, Xc ω x r * Xc ω y s ∂P =
        ∫ u, ∫ v, gffKernel u v ∂circleMeasure y s ∂circleMeasure x r := by
  sorry

/-- The regularized chaos `M_{γ,r}(d²x) = e^{γ X_r(x) - γ² E[X_r(x)²]/2} |x|₊^{-4} d²x`
([KRV, §2.1]). -/
def regularizedGMC {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Xc : Ω → ℂ → ℝ → ℝ) (γ r : ℝ) (ω : Ω) : Measure ℂ :=
  volume.withDensity fun x =>
    ENNReal.ofReal (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P)
      * normPlus x ^ (-4 : ℝ))

/-- `M` is the Gaussian multiplicative chaos `M_γ` of `X` ([KRV, §2.1]): each `M ω` is a finite
measure and, for a circle-average process of `X`, `∫ f dM_{γ,r} → ∫ f dM_γ` in probability as
`r → ∞` for every bounded continuous `f`. -/
def IsGMCOf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (γ : ℝ)
    (M : Ω → Measure ℂ) : Prop :=
  (∀ ω, IsFiniteMeasure (M ω)) ∧
    ∃ Xc : Ω → ℂ → ℝ → ℝ, IsCircleAverage P X Xc ∧
      ∀ f : BoundedContinuousFunction ℂ ℝ,
        TendstoInMeasure P (fun r ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) atTop
          (fun ω => ∫ x, f x ∂M ω)

/-- The chaos is almost surely unique: two random measures that are chaoses of the same field
with the same parameter agree almost surely. -/
theorem equatorGFF_GMC_unique_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (M N : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hN : IsGMCOf P X γ N) :
    ∀ᵐ ω ∂P, M ω = N ω := by
  sorry

/-- The chaos is not trivial: for `0 < γ < 2` it is not almost surely the zero measure. -/
theorem equatorGFF_GMC_nontrivial {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    ¬ ∀ᵐ ω ∂P, M ω = 0 := by
  sorry

/-- The joint law of the field and its chaos does not depend on the model: for `0 < γ < 2` and
two models on arbitrary probability spaces, the test evaluations and the chaos have the same
joint law. -/
theorem equatorGFF_GMC_law_transport {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (P' : Measure Ω') (X' : Ω' → Distr) (hX' : IsEquatorGFF P' X')
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (M' : Ω' → Measure ℂ) (hM' : IsGMCOf P' X' γ M')
    (H : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : (TestFn → ℝ) × Measure ℂ => H q.1 q.2)) :
    ∫⁻ ω, H (fun f => X ω f) (M ω) ∂P = ∫⁻ ω', H (fun f => X' ω' f) (M' ω') ∂P' := by
  sorry

/-! ## Structure constants -/

/-- `ρ(α₁, α₂, α₃) = ∫ |x|₊^{γ(α₁ + α₂ + α₃)} |x|^{-γα₁} |x - 1|^{-γα₂} M_γ(d²x)`
([KRV, §2.3]). -/
def rho (γ : ℝ) (M : Measure ℂ) (α₁ α₂ α₃ : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (normPlus x ^ (γ * (α₁ + α₂ + α₃))
    / (‖x‖ ^ (γ * α₁) * ‖x - 1‖ ^ (γ * α₂))) ∂M

/-- The structure constant `C_γ(α₁, α₂, α₃) = 2 μ^{-s} γ^{-1} Γ(s) E[ρ(α₁, α₂, α₃)^{-s}]`
([KRV, §2.3]). -/
def structureConstant {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) (γ μ α₁ α₂ α₃ : ℝ) : ℝ :=
  2 * μ ^ (-sExp γ α₁ α₂ α₃) / γ * Real.Gamma (sExp γ α₁ α₂ α₃) *
    (∫⁻ ω, rho γ (M ω) α₁ α₂ α₃ ^ (-sExp γ α₁ α₂ α₃) ∂P).toReal

/-- Under the extended Seiberg bounds the moment `E[ρ^{-s}]` in the structure constants is
positive and finite ([DKRV, Lemma 3.10]; [KRV, §2.2]). -/
theorem equatorGFF_extendedSeiberg_rho_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hα : ExtendedSeiberg3 γ α₁ α₂ α₃) :
    0 < ∫⁻ ω, rho γ (M ω) α₁ α₂ α₃ ^ (-sExp γ α₁ α₂ α₃) ∂P ∧
      ∫⁻ ω, rho γ (M ω) α₁ α₂ α₃ ^ (-sExp γ α₁ α₂ α₃) ∂P < ⊤ := by
  sorry

/-- The unit-volume structure constant `C̄_γ = μ^s C_γ / Γ(s) = (2/γ) E[ρ^{-s}]` ([KRV, §2.2]). -/
def unitVolumeStructureConstant {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ) : ℝ :=
  2 / γ * (∫⁻ ω, rho γ (M ω) α₁ α₂ α₃ ^ (-sExp γ α₁ α₂ α₃) ∂P).toReal

/-! ## The DOZZ formula -/

/-- **The DOZZ formula** ([KRV, Theorem 2.4]). For `0 < γ < 2`, `μ > 0` and real charges
satisfying the extended Seiberg bounds with `s ∉ {0, -1, -2, …}`, the structure constant equals
the DOZZ formula, in every model of the field and its chaos. -/
theorem dozz_formula (γ μ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (α₁ α₂ α₃ : ℝ) (hα : ExtendedSeiberg3 γ α₁ α₂ α₃)
    (hs : ∀ n : ℕ, sExp γ α₁ α₂ α₃ ≠ -(n : ℝ))
    (U : ℂ → ℂ) (hU : IsUpsilon γ U)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    (structureConstant P M γ μ α₁ α₂ α₃ : ℂ) = dozzFormula γ μ U α₁ α₂ α₃ := by
  sorry

/-- **The DOZZ formula at every point** (unit-volume form). On the whole extended Seiberg domain,
including the poles `s ∈ {0, -1, -2, …}` of `Γ(s)`, the unit-volume structure constant is the limit
of `μ^s C^{DOZZ}_γ / Γ(s)` along the points of the domain where `s ∉ -ℕ`. -/
theorem dozz_unitVolume (γ μ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (α₁ α₂ α₃ : ℝ) (hα : ExtendedSeiberg3 γ α₁ α₂ α₃)
    (U : ℂ → ℂ) (hU : IsUpsilon γ U)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    Tendsto
      (fun a : ℝ × ℝ × ℝ =>
        ((μ : ℂ) ^ (sExp γ a.1 a.2.1 a.2.2 : ℂ) / Complex.Gamma (sExp γ a.1 a.2.1 a.2.2)) *
          dozzFormula γ μ U a.1 a.2.1 a.2.2)
      (𝓝[{a | ExtendedSeiberg3 γ a.1 a.2.1 a.2.2 ∧
              ∀ n : ℕ, sExp γ a.1 a.2.1 a.2.2 ≠ -(n : ℝ)}] (α₁, α₂, α₃))
      (𝓝 (unitVolumeStructureConstant P M γ α₁ α₂ α₃ : ℂ)) := by
  sorry

/-- **Existence.** For `0 < γ < 2` there are a function `Υ_{γ/2}` and a probability space carrying
an equator-pinned Gaussian free field and its chaos. -/
theorem dozz_existence (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) :
    (∃ U : ℂ → ℂ, IsUpsilon γ U) ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ),
        IsEquatorGFF P X ∧ IsGMCOf P X γ M := by
  sorry

end DOZZChallenge
