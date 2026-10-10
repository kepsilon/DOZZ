/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.SeparatedTail.LocalWeights
public import DOZZ.Correlations.SumTail.Ceiling

/-! Prove finiteness before translating the extended-mass sum and the joint events. -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

theorem sumtail_localMass_ae_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (F : ℂ → ℝ) (z : ℂ) (α S : ℝ) (hα : γ/2 < α ∧ α < Q γ)
    (hF : ∀ x, |F x| ≤ S) : ∀ᵐ ω ∂P, localSingularMass M F z γ α ω ≠ ⊤ := by
  obtain ⟨hp,hpT⟩ := residue_critical_order_bounds γ α hγ hα.1 hα.2
  have ha : 0 < reflectionExponent γ α/2 := by positivity
  have hr : reflectionExponent γ α/2 < min (4/γ^2) (reflectionExponent γ α) :=
    lt_min (by linarith only [hp,hpT]) (by linarith only [hp])
  have hf := separatedTail_weighted_mass_ae_finite P X hX γ hγ hγ2 M hM α _ hα.2 ha hr z
  filter_upwards [hf] with ω hω
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω)
    (separatedTail_localSingularMass_le M F z γ α (ENNReal.ofReal S) ENNReal.ofReal_ne_top
      (fun x => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hF x))) ω)

theorem sumtail_extended_event_eq_real
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : Ω → ℝ≥0∞)
    (hf : ∀ᵐ ω ∂P, W ω ≠ ⊤) (x : ℝ) (hx : 0 ≤ x) :
    P.real {ω | ENNReal.ofReal x < W ω} = P.real {ω | x < (W ω).toReal} := by
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hf] with ω hω
  exact propext (ENNReal.ofReal_lt_iff_lt_toReal hx hω)

theorem sumtail_extended_joint_eq_real
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W2 W3 : Ω → ℝ≥0∞)
    (hf2 : ∀ᵐ ω ∂P, W2 ω ≠ ⊤) (hf3 : ∀ᵐ ω ∂P, W3 ω ≠ ⊤)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    P.real {ω | ENNReal.ofReal u < W2 ω ∧ ENNReal.ofReal v < W3 ω} =
      P.real {ω | u < (W2 ω).toReal ∧ v < (W3 ω).toReal} := by
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hf2,hf3] with ω h2 h3
  exact propext (and_congr (ENNReal.ofReal_lt_iff_lt_toReal hu h2)
    (ENNReal.ofReal_lt_iff_lt_toReal hv h3))

theorem sumtail_extended_sum_eq_real
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W2 W3 : Ω → ℝ≥0∞)
    (hf2 : ∀ᵐ ω ∂P, W2 ω ≠ ⊤) (hf3 : ∀ᵐ ω ∂P, W3 ω ≠ ⊤)
    (x : ℝ) (hx : 0 ≤ x) :
    P.real {ω | ENNReal.ofReal x < W2 ω+W3 ω} =
      P.real {ω | x < (W2 ω).toReal+(W3 ω).toReal} := by
  have hf : ∀ᵐ ω ∂P, W2 ω+W3 ω ≠ ⊤ := by
    filter_upwards [hf2,hf3] with ω h2 h3
    exact ENNReal.add_ne_top.mpr ⟨h2,h3⟩
  rw [sumtail_extended_event_eq_real P _ hf x hx]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hf2,hf3] with ω h2 h3
  rw [ENNReal.toReal_add h2 h3]

end DOZZ.Proofs
