/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.ChaosLawFDD

/-! A finite-dimensional-law transfer specialized to chaos integrals alone. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Filter
open scoped NNReal ENNReal

namespace DOZZ.Proofs

/-- If two jointly measurable Gaussian fields have the same finite-dimensional laws, then
finite lists of their weighted Wick integrals have the same law. This is the no-auxiliary-vector
form of `chaosLawFDD_of_integrable`, useful when the comparison field is a field plus an
independent scalar. -/
theorem chaosLawFDD_integral_map_eq
    {Ω Ω' S : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace S]
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (ν : Measure S) [IsProbabilityMeasure ν] {m : ℕ}
    (X : Ω → S → ℝ) (Y : Ω' → S → ℝ)
    (variance : S → ℝ≥0) (weight : Fin m → S → ℝ) (γ : ℝ)
    (hX : Measurable (fun p : Ω × S => X p.1 p.2))
    (hY : Measurable (fun p : Ω' × S => Y p.1 p.2))
    (hvariance : Measurable variance)
    (hweight : ∀ j, Measurable (weight j))
    (hintX : ∀ j, ∀ᵐ ω ∂P, Integrable (fun x => weight j x *
      Real.exp (γ * X ω x - γ ^ 2 / 2 * (variance x : ℝ))) ν)
    (hintY : ∀ j, ∀ᵐ ω ∂P', Integrable (fun x => weight j x *
      Real.exp (γ * Y ω x - γ ^ 2 / 2 * (variance x : ℝ))) ν)
    (hFDD : ∀ (r : ℕ) (xs : Fin r → S),
      Measure.map (fun ω => fun i => X ω (xs i)) P =
        Measure.map (fun ω => fun i => Y ω (xs i)) P') :
    Measure.map (fun ω => fun j => ∫ x, weight j x *
      Real.exp (γ * X ω x - γ ^ 2 / 2 * (variance x : ℝ)) ∂ν) P =
    Measure.map (fun ω => fun j => ∫ x, weight j x *
      Real.exp (γ * Y ω x - γ ^ 2 / 2 * (variance x : ℝ)) ∂ν) P' := by
  classical
  let v0 : Fin 0 → ℝ := fun i => Fin.elim0 i
  let V : Ω → Fin 0 → ℝ := fun _ => v0
  let V' : Ω' → Fin 0 → ℝ := fun _ => v0
  let z : Fin m → S → ℝ → ℝ := fun j x t =>
    weight j x * Real.exp (γ * t - γ ^ 2 / 2 * (variance x : ℝ))
  have hV : Measurable V := measurable_const
  have hV' : Measurable V' := measurable_const
  have hz : ∀ j, Measurable (fun p : S × ℝ => z j p.1 p.2) := by
    intro j
    dsimp [z]
    fun_prop
  have hXint : ∀ j, ∀ᵐ ω ∂P, Integrable (fun x => z j x (X ω x)) ν := by
    simpa [z] using hintX
  have hYint : ∀ j, ∀ᵐ ω ∂P', Integrable (fun x => z j x (Y ω x)) ν := by
    simpa [z] using hintY
  have hXtransform : ∀ j, Measurable (fun p : Ω × S => z j p.2 (X p.1 p.2)) := by
    intro j
    exact (hz j).comp (measurable_snd.prodMk hX)
  have hYtransform : ∀ j, Measurable (fun p : Ω' × S => z j p.2 (Y p.1 p.2)) := by
    intro j
    exact (hz j).comp (measurable_snd.prodMk hY)
  let LX : Ω → (Fin 0 → ℝ) × (Fin m → ℝ) := fun ω =>
    (V ω, fun j => ∫ x, z j x (X ω x) ∂ν)
  let LY : Ω' → (Fin 0 → ℝ) × (Fin m → ℝ) := fun ω =>
    (V' ω, fun j => ∫ x, z j x (Y ω x) ∂ν)
  have hLX : Measurable LX := by
    apply Measurable.prodMk hV
    apply measurable_pi_iff.2
    intro j
    exact (hXtransform j).stronglyMeasurable.integral_prod_right'.measurable
  have hLY : Measurable LY := by
    apply Measurable.prodMk hV'
    apply measurable_pi_iff.2
    intro j
    exact (hYtransform j).stronglyMeasurable.integral_prod_right'.measurable
  have hFDD' : ∀ (r : ℕ) (xs : Fin r → S),
      Measure.map (fun ω => (V ω, fun i => X ω (xs i))) P =
        Measure.map (fun ω => (V' ω, fun i => Y ω (xs i))) P' := by
    intro r xs
    let lift : (Fin r → ℝ) → (Fin 0 → ℝ) × (Fin r → ℝ) := fun u => (v0, u)
    have hlift : Measurable lift := by fun_prop
    have hfieldX : Measurable (fun ω => fun i : Fin r => X ω (xs i)) := by
      apply measurable_pi_iff.2
      intro i
      exact hX.comp (measurable_id.prodMk measurable_const)
    have hfieldY : Measurable (fun ω => fun i : Fin r => Y ω (xs i)) := by
      apply measurable_pi_iff.2
      intro i
      exact hY.comp (measurable_id.prodMk measurable_const)
    have hleft : Measure.map (fun ω => (V ω, fun i => X ω (xs i))) P =
        (Measure.map (fun ω => fun i => X ω (xs i)) P).map lift := by
      change Measure.map (lift ∘ (fun ω => fun i => X ω (xs i))) P = _
      rw [← Measure.map_map hlift hfieldX]
    have hright : Measure.map (fun ω => (V' ω, fun i => Y ω (xs i))) P' =
        (Measure.map (fun ω => fun i => Y ω (xs i)) P').map lift := by
      change Measure.map (lift ∘ (fun ω => fun i => Y ω (xs i))) P' = _
      rw [← Measure.map_map hlift hfieldY]
    rw [hleft, hright, hFDD r xs]
  have hpair := (chaosLawFDD_of_integrable ν X Y V V' z hV hV' hX hY hz
    hXint hYint hFDD' (0 : BoundedContinuousFunction
      ((Fin 0 → ℝ) × (Fin m → ℝ)) ℝ)).1
  have hleft : Measure.map (fun ω => fun j => ∫ x, z j x (X ω x) ∂ν) P =
      (Measure.map LX P).map Prod.snd := by
    change Measure.map (Prod.snd ∘ LX) P = _
    rw [← Measure.map_map measurable_snd hLX]
  have hright : Measure.map (fun ω => fun j => ∫ x, z j x (Y ω x) ∂ν) P' =
      (Measure.map LY P').map Prod.snd := by
    change Measure.map (Prod.snd ∘ LY) P' = _
    rw [← Measure.map_map measurable_snd hLY]
  calc
    Measure.map (fun ω => fun j => ∫ x, weight j x *
        Real.exp (γ * X ω x - γ ^ 2 / 2 * (variance x : ℝ)) ∂ν) P =
      (Measure.map LX P).map Prod.snd := by
        simpa [z, LX] using hleft
    _ = (Measure.map LY P').map Prod.snd := by
        rw [hpair]
    _ = Measure.map (fun ω => fun j => ∫ x, weight j x *
        Real.exp (γ * Y ω x - γ ^ 2 / 2 * (variance x : ℝ)) ∂ν) P' := by
          simpa [z, LY] using hright.symm

/-- A common independent Gaussian shift factors out of the Wick integrals in law. This no-auxiliary
vector version is the exact finite-cutoff scaling step: the fields need only agree in finite
dimensional law, while the normalizations differ by the scalar variance. -/
theorem chaosLawFDD_independent_scalar_shift
    {Ω Ω' S : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace S]
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (ν : Measure S) [IsProbabilityMeasure ν] {m : ℕ}
    (X : Ω → S → ℝ) (Y : Ω' → S → ℝ) (W : Ω' → ℝ)
    (varianceBase varianceTotal : S → ℝ≥0) (σ γ : ℝ)
    (weight : Fin m → S → ℝ)
    (hX : Measurable (fun p : Ω × S => X p.1 p.2))
    (hY : Measurable (fun p : Ω' × S => Y p.1 p.2))
    (hW : Measurable W)
    (hvarianceBase : Measurable varianceBase) (hvarianceTotal : Measurable varianceTotal)
    (hweight : ∀ j, Measurable (weight j))
    (hweight_nonneg : ∀ j x, 0 ≤ weight j x)
    (hweight_int : ∀ j, Integrable (weight j) ν)
    (hVariance : ∀ x, (varianceBase x : ℝ) + σ = (varianceTotal x : ℝ))
    (hXlaw : ∀ x, HasLaw (fun ω => X ω x)
      (gaussianReal 0 (varianceTotal x)) P)
    (hYlaw : ∀ x, HasLaw (fun ω => Y ω x)
      (gaussianReal 0 (varianceBase x)) P')
    (hShiftLaw : ∀ x, HasLaw (fun ω => Y ω x + W ω)
      (gaussianReal 0 (varianceTotal x)) P')
    (hFDD : ∀ (r : ℕ) (xs : Fin r → S),
      Measure.map (fun ω i => X ω (xs i)) P =
        Measure.map (fun ω i => Y ω (xs i) + W ω) P') :
    Measure.map (fun ω => fun j => ∫ x, weight j x *
      Real.exp (γ * X ω x - γ ^ 2 / 2 * (varianceTotal x : ℝ)) ∂ν) P =
    Measure.map (fun ω => fun j => Real.exp (γ * W ω - γ ^ 2 / 2 * σ) *
      ∫ x, weight j x * Real.exp
        (γ * Y ω x - γ ^ 2 / 2 * (varianceBase x : ℝ)) ∂ν) P' := by
  let Yshift : Ω' → S → ℝ := fun ω x => Y ω x + W ω
  let factor : Ω' → ℝ := fun ω => Real.exp (γ * W ω - γ ^ 2 / 2 * σ)
  have hYshift : Measurable (fun p : Ω' × S => Yshift p.1 p.2) := by
    dsimp [Yshift]
    fun_prop
  have hBaseInt : ∀ j, ∀ᵐ ω ∂P', Integrable (fun x => weight j x *
      Real.exp (γ * Y ω x - γ ^ 2 / 2 * (varianceBase x : ℝ))) ν := by
    intro j
    exact ae_integrable_weighted_wick_sections ν Y varianceBase (weight j) γ hY
      hvarianceBase (hweight j) hYlaw (hweight_nonneg j) (hweight_int j)
  have hTargetInt : ∀ j, ∀ᵐ ω ∂P, Integrable (fun x => weight j x *
      Real.exp (γ * X ω x - γ ^ 2 / 2 * (varianceTotal x : ℝ))) ν := by
    intro j
    exact ae_integrable_weighted_wick_sections ν X varianceTotal (weight j) γ hX
      hvarianceTotal (hweight j) hXlaw (hweight_nonneg j) (hweight_int j)
  have hShiftInt : ∀ j, ∀ᵐ ω ∂P', Integrable (fun x => weight j x *
      Real.exp (γ * Yshift ω x - γ ^ 2 / 2 * (varianceTotal x : ℝ))) ν := by
    intro j
    exact ae_integrable_weighted_wick_sections ν Yshift varianceTotal (weight j) γ hYshift
      hvarianceTotal (hweight j) hShiftLaw (hweight_nonneg j) (hweight_int j)
  have hLaw := chaosLawFDD_integral_map_eq ν X Yshift varianceTotal weight γ hX hYshift
    hvarianceTotal hweight hTargetInt hShiftInt (by simpa [Yshift] using hFDD)
  have hFactor (ω : Ω') (j : Fin m)
      (hω : Integrable (fun x => weight j x * Real.exp
        (γ * Y ω x - γ ^ 2 / 2 * (varianceBase x : ℝ))) ν) :
      (∫ x, weight j x * Real.exp
        (γ * Yshift ω x - γ ^ 2 / 2 * (varianceTotal x : ℝ)) ∂ν) =
      factor ω * ∫ x, weight j x * Real.exp
        (γ * Y ω x - γ ^ 2 / 2 * (varianceBase x : ℝ)) ∂ν := by
    calc
      (∫ x, weight j x * Real.exp
          (γ * Yshift ω x - γ ^ 2 / 2 * (varianceTotal x : ℝ)) ∂ν) =
          ∫ x, factor ω * (weight j x * Real.exp
            (γ * Y ω x - γ ^ 2 / 2 * (varianceBase x : ℝ))) ∂ν := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          dsimp [Yshift, factor]
          have hexp : Real.exp (γ * (Y ω x + W ω) - γ ^ 2 / 2 *
              (varianceTotal x : ℝ)) =
              Real.exp (γ * W ω - γ ^ 2 / 2 * σ) *
                Real.exp (γ * Y ω x - γ ^ 2 / 2 * (varianceBase x : ℝ)) := by
            rw [← Real.exp_add]
            congr 1
            rw [← hVariance x]
            ring
          rw [hexp]
          ring
      _ = factor ω * ∫ x, weight j x * Real.exp
          (γ * Y ω x - γ ^ 2 / 2 * (varianceBase x : ℝ)) ∂ν := by
        rw [integral_const_mul]
  have hmapFactor : Measure.map (fun ω => fun j => ∫ x, weight j x *
      Real.exp (γ * Yshift ω x - γ ^ 2 / 2 * (varianceTotal x : ℝ)) ∂ν) P' =
    Measure.map (fun ω => fun j => factor ω * ∫ x, weight j x *
      Real.exp (γ * Y ω x - γ ^ 2 / 2 * (varianceBase x : ℝ)) ∂ν) P' := by
    apply Measure.map_congr
    filter_upwards [ae_all_iff.2 hBaseInt] with ω hω
    funext j
    exact hFactor ω j (hω j)
  calc
    Measure.map (fun ω => fun j => ∫ x, weight j x *
        Real.exp (γ * X ω x - γ ^ 2 / 2 * (varianceTotal x : ℝ)) ∂ν) P =
      Measure.map (fun ω => fun j => ∫ x, weight j x *
        Real.exp (γ * Yshift ω x - γ ^ 2 / 2 * (varianceTotal x : ℝ)) ∂ν) P' := hLaw
    _ = Measure.map (fun ω => fun j => factor ω * ∫ x, weight j x *
        Real.exp (γ * Y ω x - γ ^ 2 / 2 * (varianceBase x : ℝ)) ∂ν) P' := hmapFactor

end DOZZ.Proofs
