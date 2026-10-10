-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import Mathlib

/-!
# The reflection coefficient of Liouville theory

A standalone, Mathlib-only statement of the theorem of Kupiainen, Rhodes and Vargas identifying the
probabilistic reflection coefficient of Liouville conformal field theory with the formula of
Zamolodchikov and Zamolodchikov. Source: A. Kupiainen, R. Rhodes and V. Vargas, *Integrability of
Liouville theory: proof of the DOZZ formula*, Ann. of Math. 191 (2020), 81–166, cited as [KRV],
with the numbering of arXiv:1707.08785.

For `0 < γ < 2` and `γ/2 < α < Q` put `p = 2(Q - α)/γ`. Let `𝓑` be the two-sided path made of two
independent Brownian motions with drift `-(Q - α)` conditioned to stay negative, and let `Z` be an
independent lateral chaos: the image of the chaos of the equator-pinned Gaussian free field under
`x ↦ -log|x|`, with the radial Brownian factor removed. Following [KRV, §3.1],
`R̄(α) = E[(∫ e^{γ𝓑_s} Z(ds))^p]` and `R(α) = μ^p Γ(-p) p R̄(α)`.

* `reflection_Rtheor_off_poles` ([KRV, Theorem 3.5]). For `0 < γ < 2`, `μ > 0` and
  `γ/2 < α < Q` with `p ∉ {1, 2, …}`, `R(α) = R^{DOZZ}(α)`.
* `reflection_Rtheor_punctured`: at the excluded points `R - R^{DOZZ}` tends to `0`, for every
  family of reflection data on one probability space.
* `negativeConditionedBrownianLaw_exists`, `isLateralGMCOf_map_eq`, `reflectionData_exists`,
  `reflectionBarR_eq_of_isReflectionData`, `reflectionR_eq_of_isReflectionData`,
  `reflectionBarR_positive_finite`: the objects defined by characterizations are well defined. The
  conditioned law exists and is unique; all lateral chaoses have the same law; reflection data for
  every `α < Q` exist on one probability space; `R̄` and `R` do not depend on the data; and on
  `γ/2 < α < Q` the moment defining `R̄` is positive and finite.

`R` is not defined at the poles `p ∈ {1, 2, …}` of `Γ(-p)` ([KRV, §3.1]), where Mathlib's `Gamma`
takes the value `0`: `reflection_Rtheor_off_poles` excludes these points, and
`reflection_Rtheor_punctured` covers them as a limit.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace ReflectionChallenge

/-! ## Constants and the formula `R^{DOZZ}` -/

/-- `Q = 2/γ + γ/2` ([KRV, §1.1]). -/
def Q (γ : ℝ) : ℝ := 2 / γ + γ / 2

/-- `|x|₊ = max(1, |x|)` ([KRV, §2.1]). -/
def normPlus (x : ℂ) : ℝ := max 1 ‖x‖

/-- `l(x) = Γ(x)/Γ(1 - x)` ([KRV, §1.2]). -/
def lFun (x : ℂ) : ℂ := Complex.Gamma x / Complex.Gamma (1 - x)

/-- The base `π μ l(γ²/4)` ([KRV, §1.2]); `l(γ²/4)` is real for real `γ`. -/
def dozzBase (γ μ : ℝ) : ℝ := Real.pi * μ * (lFun ((γ : ℂ) ^ 2 / 4)).re

/-- The formula `R^{DOZZ}(α) = -(π μ l(γ²/4))^{2(Q - α)/γ} Γ(-γ(Q - α)/2)/Γ(γ(Q - α)/2) ·
Γ(-2(Q - α)/γ)/Γ(2(Q - α)/γ)` of Zamolodchikov and Zamolodchikov ([KRV, §1.2]). -/
def reflectionDOZZ (γ μ : ℝ) (α : ℂ) : ℂ :=
  -(((dozzBase γ μ : ℝ) : ℂ) ^ (2 * (Q γ - α) / γ)) *
    (Complex.Gamma (-(γ * (Q γ - α) / 2)) / Complex.Gamma (γ * (Q γ - α) / 2)) *
    (Complex.Gamma (-(2 * (Q γ - α) / γ)) / Complex.Gamma (2 * (Q γ - α) / γ))

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

/-! ## Brownian motion conditioned to stay negative -/

/-- Continuous real paths on `t ≥ 0`, with the Borel σ-algebra of the compact-open topology. -/
abbrev BrownianPath := C(ℝ≥0, ℝ)

/-- Continuous real paths on `ℝ`, with the Borel σ-algebra of the compact-open topology. -/
abbrev TwoSidedPath := C(ℝ, ℝ)

/-- The density `e^{-x²/(2t)}/√(2πt)` of a Brownian increment over a time `t > 0`. -/
def brownianHeatDensity (t x : ℝ) : ℝ :=
  if 0 < t then Real.exp (-(x ^ 2) / (2 * t)) / Real.sqrt (2 * Real.pi * t) else 0

/-- The positive harmonic function `1 - e^{-2νx}` of Brownian motion with drift `ν > 0`, vanishing
at `0`; it is `x` for `ν = 0`. -/
def conditionedH (ν x : ℝ) : ℝ :=
  if ν = 0 then x else 1 - Real.exp (-2 * ν * x)

/-- The transition density of Brownian motion with drift `ν ≥ 0` conditioned to stay positive: the
Doob transform by `conditionedH ν` of the drifted motion killed at `0` (the three-dimensional Bessel
process for `ν = 0`), [KRV, §12.4]. -/
def conditionedPositiveTransitionDensity (ν t x y : ℝ) : ℝ :=
  if 0 ≤ ν ∧ 0 < t ∧ 0 < x ∧ 0 < y then
    Real.exp (ν * (y - x) - ν ^ 2 * t / 2) *
      (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x)) *
      conditionedH ν y / conditionedH ν x
  else 0

/-- The density at time `t > 0` of the same process started at `0`; for `ν = 0` it is the Maxwell
density of the three-dimensional Bessel process. -/
def conditionedPositiveEntranceDensity (ν t y : ℝ) : ℝ :=
  if 0 ≤ ν ∧ 0 < t ∧ 0 < y then
    if ν = 0 then
      Real.sqrt (2 / Real.pi) * y ^ 2 / t ^ (3 / 2 : ℝ) * Real.exp (-y ^ 2 / (2 * t))
    else
      Real.sqrt (2 / Real.pi) * t ^ (-(3 / 2 : ℝ)) * (y * Real.sinh (ν * y) / ν) *
        Real.exp (-y ^ 2 / (2 * t) - ν ^ 2 * t / 2)
  else 0

/-- The transition density of Brownian motion with drift `-ν` conditioned to stay negative, the
negative of the process above. -/
def negativeConditionedTransitionDensity (ν t x y : ℝ) : ℝ :=
  conditionedPositiveTransitionDensity ν t (-x) (-y)

/-- The joint density at the points `xs` and times `ts` of the negative conditioned process at `x₀`
at time `t₀`: the product of its transition densities. -/
def negativeConditionedTransitionChainDensity (ν t₀ x₀ : ℝ) : List ℝ → List ℝ → ℝ
  | [], [] => 1
  | t :: ts, x :: xs =>
      negativeConditionedTransitionDensity ν (t - t₀) x₀ x *
        negativeConditionedTransitionChainDensity ν t x ts xs
  | _, _ => 0

/-- The joint density at the points `xs` and increasing times `ts` of the negative conditioned
process started at `0`: the entrance density at the first time, then the transition densities. -/
def negativeConditionedFDDDensity (ν : ℝ) : List ℝ → List ℝ → ℝ
  | [], [] => 1
  | t :: ts, x :: xs =>
      conditionedPositiveEntranceDensity ν t (-x) *
        negativeConditionedTransitionChainDensity ν t x ts xs
  | _, _ => 0

/-- `P` is the law of Brownian motion with drift `-ν` conditioned to stay negative, started at `0`
([KRV, §3.1 and §12.4]): a probability measure on paths, almost surely `0` at time `0`, whose
finite-dimensional laws at increasing positive times have the densities above. -/
def IsNegativeConditionedBrownianLaw (ν : ℝ) (P : Measure BrownianPath) : Prop :=
  0 ≤ ν ∧ IsProbabilityMeasure P ∧
    (∀ᵐ p ∂P, p 0 = 0) ∧
      ∀ (n : ℕ), 0 < n →
        ∀ times : Fin n → ℝ≥0,
          (∀ i, 0 < (times i : ℝ)) → StrictMono times →
            P.map (fun p i => p (times i)) =
              (volume : Measure (Fin n → ℝ)).withDensity
                (fun x => ENNReal.ofReal
                  (max 0 (negativeConditionedFDDDensity ν
                    (List.ofFn fun i => (times i : ℝ)) (List.ofFn fun i => x i))))

/-- The conditioned law exists and is unique, for every drift `ν ≥ 0`. -/
theorem negativeConditionedBrownianLaw_exists (ν : ℝ) (hν : 0 ≤ ν) :
    ∃! P : Measure BrownianPath, IsNegativeConditionedBrownianLaw ν P := by
  sorry

/-- `B` is a random path whose law is the conditioned law. -/
def IsNegativeConditionedBrownianProcess {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : Ω → BrownianPath) (ν : ℝ) : Prop :=
  AEMeasurable B P ∧ IsNegativeConditionedBrownianLaw ν (P.map B)

/-- `B = (B⁺, B⁻)` is a pair of independent conditioned paths with drift `-ν`. -/
def IsTwoSidedConditionedBrownianProcess {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : Ω → BrownianPath × BrownianPath) (ν : ℝ) : Prop :=
  IsNegativeConditionedBrownianProcess P (fun ω => (B ω).1) ν ∧
    IsNegativeConditionedBrownianProcess P (fun ω => (B ω).2) ν ∧
      IndepFun (fun ω => (B ω).1) (fun ω => (B ω).2) P

/-- The two-sided path `𝓑_s` of [KRV, §3.1]: `B⁺_s` for `s ≥ 0` and `B⁻_{-s}` for `s < 0`. -/
def twoSidedConditionedValue {Ω : Type*}
    (B : Ω → BrownianPath × BrownianPath) (ω : Ω) (s : ℝ) : ℝ :=
  if hs : 0 ≤ s then (B ω).1 ⟨s, hs⟩ else (B ω).2 ⟨-s, neg_nonneg.mpr (not_le.mp hs).le⟩

/-! ## The lateral chaos -/

/-- The lateral projection of a measure `M` on `ℂ` along a two-sided path `A`: the image under
`x ↦ -log|x|` of `e^{-γ A(-log|x|) + γQ|log|x||} M(d²x)`. For the chaos `M` of the equator-pinned
field and `A_s = X_s(0)` its circle averages at the origin, this is the measure `Z_s ds` of the
polar decomposition of [KRV, §3.1]. -/
def lateralProjectedGMC (γ : ℝ) (A : TwoSidedPath) (M : Measure ℂ) : Measure ℝ :=
  (M.withDensity fun x =>
    ENNReal.ofReal (if ‖x‖ = 0 then 0 else
      Real.exp (-γ * A (-Real.log ‖x‖) +
        γ * Q γ * |Real.log ‖x‖|))).map (fun x => -Real.log ‖x‖)

/-- `Z` is the lateral projection of the chaos `M` of an equator-pinned field `X`: along a
two-sided path `A` with `A_s = X_s(0)` almost surely for each `s`, `A_0 = 0`, whose two halves
`s ↦ A_{±s}` are independent standard Brownian motions, and which is independent of the projected
measure. -/
def IsSourceLateralProjection {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (γ : ℝ) (M : Ω → Measure ℂ)
    (Z : Ω → Measure ℝ) : Prop :=
  IsEquatorGFF P X ∧ IsGMCOf P X γ M ∧
    ∃ A : Ω → TwoSidedPath,
      (∃ Xc : Ω → ℂ → ℝ → ℝ, IsCircleAverage P X Xc ∧
        ∀ s : ℝ, ∀ᵐ ω ∂P, A ω s = Xc ω 0 s) ∧
      AEMeasurable A P ∧ (∀ᵐ ω ∂P, A ω 0 = 0) ∧
        ProbabilityTheory.IsBrownianReal (fun t ω => A ω (t : ℝ)) P ∧
        ProbabilityTheory.IsBrownianReal (fun t ω => A ω (-(t : ℝ))) P ∧
        IndepFun (fun ω => fun t : ℝ≥0 => A ω (t : ℝ))
          (fun ω => fun t : ℝ≥0 => A ω (-(t : ℝ))) P ∧
        AEMeasurable
          (fun ω => lateralProjectedGMC γ (A ω) (M ω)) P ∧
        IndepFun (fun ω => A ω)
          (fun ω => lateralProjectedGMC γ (A ω) (M ω)) P ∧
        (∀ᵐ ω ∂P, Z ω = lateralProjectedGMC γ (A ω) (M ω))

/-- `Z` is a lateral chaos ([KRV, §3.1]): a random locally finite measure on `ℝ` whose law is
invariant under translations and under `s ↦ -s`, with intensity `2π ds`, and which is the lateral
projection of the chaos of an equator-pinned field. -/
def IsLateralGMCOf {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) (Z : Ω → Measure ℝ) : Prop :=
  0 < γ ∧ γ < 2 ∧ IsProbabilityMeasure P ∧ AEMeasurable Z P ∧
    (∀ᵐ ω ∂P, ∀ a b : ℝ, Z ω (Set.Icc a b) < ⊤) ∧
      (∀ t : ℝ,
        P.map (fun ω => (Z ω).map (fun s => s + t)) = P.map Z) ∧
      P.map (fun ω => (Z ω).map (fun s => -s)) = P.map Z ∧
        (∀ a b : ℝ, a < b →
          ∫⁻ ω, Z ω (Set.Ioc a b) ∂P = ENNReal.ofReal (2 * Real.pi * (b - a))) ∧
        ∃ X : Ω → Distr, ∃ M : Ω → Measure ℂ,
          IsSourceLateralProjection P X γ M Z

/-- All lateral chaoses with the same parameter have the same law. -/
theorem isLateralGMCOf_map_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') (γ : ℝ) (Z : Ω → Measure ℝ) (Z' : Ω' → Measure ℝ)
    (hZ : IsLateralGMCOf P γ Z) (hZ' : IsLateralGMCOf P' γ Z') :
    P.map Z = P'.map Z' := by
  sorry

/-! ## The reflection coefficient -/

/-- The reflection exponent `p = 2(Q - α)/γ`. -/
def reflectionExponent (γ α : ℝ) : ℝ := 2 * (Q γ - α) / γ

/-- The mass `∫ e^{γ𝓑_s} Z(ds)` of the lateral chaos weighted by the two-sided path. -/
def twoSidedReflectionMass {Ω : Type*} (γ : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ s, ENNReal.ofReal (Real.exp (γ * twoSidedConditionedValue B ω s)) ∂Z ω

/-- Reflection data for `α` ([KRV, §3.1]): the halves of `𝓑` are independent Brownian motions with
drift `-(Q - α)` conditioned to stay negative, `Z` is a lateral chaos, and `𝓑` and `Z` are
independent. -/
def IsReflectionData {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ α : ℝ) (B : Ω → BrownianPath × BrownianPath)
    (Z : Ω → Measure ℝ) : Prop :=
  IsTwoSidedConditionedBrownianProcess P B (Q γ - α) ∧
    IsLateralGMCOf P γ Z ∧ IndepFun B Z P

/-- For `0 < γ < 2`, reflection data for every `α < Q` exist on one probability space, with one
lateral chaos. -/
theorem reflectionData_exists (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ),
      ∀ α, α < Q γ → IsReflectionData P γ α (B α) Z := by
  sorry

/-- The unit-volume reflection coefficient `R̄(α) = E[(∫ e^{γ𝓑_s} Z(ds))^p]` ([KRV, §3.1]). -/
def reflectionBarR {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ α : ℝ) (B : Ω → BrownianPath × BrownianPath)
    (Z : Ω → Measure ℝ) : ℝ :=
  (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ B Z ω) (reflectionExponent γ α) ∂P).toReal

/-- The reflection coefficient `R(α) = μ^p Γ(-p) p R̄(α)` ([KRV, §3.1]). -/
def reflectionR {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ μ α : ℝ) (B : Ω → BrownianPath × BrownianPath)
    (Z : Ω → Measure ℝ) : ℝ :=
  μ ^ (reflectionExponent γ α) * Real.Gamma (-(reflectionExponent γ α)) *
    reflectionExponent γ α * reflectionBarR P γ α B Z

/-- `p ∉ {1, 2, …}`: `α` is not a pole of `Γ(-p)`. -/
def ReflectionPoleFree (γ α : ℝ) : Prop :=
  ∀ n : ℕ, reflectionExponent γ α ≠ (n + 1 : ℕ)

/-- `R̄(α)` does not depend on the reflection data. -/
theorem reflectionBarR_eq_of_isReflectionData
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') (γ α : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (B' : Ω' → BrownianPath × BrownianPath) (Z' : Ω' → Measure ℝ)
    (hData : IsReflectionData P γ α B Z) (hData' : IsReflectionData P' γ α B' Z') :
    reflectionBarR P γ α B Z = reflectionBarR P' γ α B' Z' := by
  sorry

/-- `R(α)` does not depend on the reflection data. -/
theorem reflectionR_eq_of_isReflectionData
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') (γ μ α : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (B' : Ω' → BrownianPath × BrownianPath) (Z' : Ω' → Measure ℝ)
    (hData : IsReflectionData P γ α B Z) (hData' : IsReflectionData P' γ α B' Z') :
    reflectionR P γ μ α B Z = reflectionR P' γ μ α B' Z' := by
  sorry

/-- On `γ/2 < α < Q` the moment defining `R̄(α)` is positive and finite ([KRV, Lemma 3.3]). -/
theorem reflectionBarR_positive_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : γ / 2 < α ∧ α < Q γ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α B Z) :
    0 < reflectionBarR P γ α B Z ∧
      (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ B Z ω)
        (reflectionExponent γ α) ∂P) < ⊤ := by
  sorry

/-- **The reflection coefficient** ([KRV, Theorem 3.5]). For `0 < γ < 2`, `μ > 0` and
`γ/2 < α < Q` with `p ∉ {1, 2, …}`, `R(α) = R^{DOZZ}(α)` for all reflection data. -/
theorem reflection_Rtheor_off_poles
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ μ α : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα : γ / 2 < α ∧ α < Q γ) (hPole : ReflectionPoleFree γ α)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α B Z) :
    (reflectionR P γ μ α B Z : ℂ) = reflectionDOZZ γ μ (α : ℂ) := by
  sorry

/-- **The reflection coefficient at the poles.** At a point `α₀` with `p = n + 1`,
`R(α) - R^{DOZZ}(α) → 0` as `α → α₀`, `α ≠ α₀`, for every family of reflection data on one
probability space. -/
theorem reflection_Rtheor_punctured
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ μ α₀ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα₀ : γ / 2 < α₀ ∧ α₀ < Q γ)
    (n : ℕ) (hn : reflectionExponent γ α₀ = n + 1)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : ∀ α, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z) :
    Tendsto (fun α : ℝ =>
      (reflectionR P γ μ α (B α) Z : ℂ) - reflectionDOZZ γ μ (α : ℂ))
        (𝓝[≠] α₀) (𝓝 0) := by
  sorry

end ReflectionChallenge
