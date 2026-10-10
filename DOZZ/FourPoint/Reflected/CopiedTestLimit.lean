/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.CutoffTestLimit
public import DOZZ.FourPoint.Reflected.DecouplingLimit
import Mathlib.Tactic
/-! Actual compact test convergence for the independently copied lateral chaos. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs
open DOZZ.Assembly

/-- Disjoint compact tests in the actual admissible chaos retain their sum limit after one
region is evaluated on an independent source copy. -/
theorem reflected_admissible_copied_test_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ) (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (γ : ℝ)
    (N : Ω → Measure ℂ) (hN : IsAdmissibleGMCVersion P U dens Y γ N)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (A : Set ℂ) (hA : MeasurableSet A)
    (f₀ f₁ : BoundedContinuousFunction ℂ ℝ) (hf₀ : ∀ x, 0 ≤ f₀ x) (hf₁ : ∀ x, 0 ≤ f₁ x)
    (hf₀K : tsupport (f₀ : ℂ → ℝ) ⊆ K) (hf₁K : tsupport (f₁ : ℂ → ℝ) ⊆ K)
    (hf₀A : tsupport (f₀ : ℂ → ℝ) ⊆ A) (hf₁A : tsupport (f₁ : ℂ → ℝ) ⊆ Aᶜ)
    (R₀ : ℝ) (hR₀ : Real.exp (-R₀) ≤ ε₀)
    (hΦ : ∀ r : ℝ, IsCenteredGaussianField P (fun ω x => Y ω (Real.exp (-max r R₀)) x)) :
    TendstoInMeasure (P.prod P)
      (fun r ω => (fieldChaosMass (P.prod P)
        (reflected_decoupled_field (fun ω x => Y ω (Real.exp (-max r R₀)) x) A)
        ((logRegularizationReference U dens).restrict K)
        (fun x => (f₀ x + f₁ x).toNNReal) γ ω).toReal) atTop
      (fun ω : Ω × Ω => (∫ x, f₀ x ∂N ω.1) + ∫ x, f₁ x ∂N ω.2) := by
  let ν := (logRegularizationReference U dens).restrict K
  obtain ⟨hν, hc₀⟩ := reflected_admissible_field_test_limit P U dens ε₀ Y hY γ N hN
    K hK hKU f₀ hf₀ hf₀K R₀ hR₀
  let _ := hν
  have hc₁ := (reflected_admissible_field_test_limit P U dens ε₀ Y hY γ N hN
    K hK hKU f₁ hf₁ hf₁K R₀ hR₀).2
  let Φ := fun r ω x => Y ω (Real.exp (-max r R₀)) x
  have h0 (x : ℂ) (hx : x ∉ A) : f₀ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hf₀A h))
  have h1 (x : ℂ) (hx : x ∈ A) : f₁ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hf₁A h hx)
  have he (r : ℝ) (ω : Ω × Ω) :
      fieldChaosMass (P.prod P) (reflected_decoupled_field (Φ r) A) ν
        (fun x => (f₀ x + f₁ x).toNNReal) γ ω =
      fieldChaosMass P (Φ r) ν (fun x => (f₀ x).toNNReal) γ ω.1 +
        fieldChaosMass P (Φ r) ν (fun x => (f₁ x).toNNReal) γ ω.2 := by
    rw [reflected_decoupled_field_mass P (Φ r) (hΦ r) A hA]
    congr 1
    · unfold fieldChaosMass
      rw [← lintegral_indicator hA]
      apply lintegral_congr
      intro x
      dsimp only
      by_cases hx : x ∈ A
      · rw [indicator_of_mem hx, h1 x hx, add_zero]
      · rw [indicator_of_notMem hx, h0 x hx, Real.toNNReal_zero, ENNReal.coe_zero, zero_mul]
    · unfold fieldChaosMass
      rw [← lintegral_indicator hA.compl]
      apply lintegral_congr
      intro x
      dsimp only
      by_cases hx : x ∈ A
      · rw [indicator_of_notMem (show x ∉ Aᶜ from fun hh => hh hx), h1 x hx,
          Real.toNNReal_zero, ENNReal.coe_zero, zero_mul]
      · rw [indicator_of_mem (show x ∈ Aᶜ from hx), h0 x hx, zero_add]
  have hm₀ := tendstoInMeasure_measurePreserving P (P.prod P) Prod.fst
    measurePreserving_fst _ _ atTop hc₀
  have hm₁ := tendstoInMeasure_measurePreserving P (P.prod P) Prod.snd
    measurePreserving_snd _ _ atTop hc₁
  have hneg := tendstoInMeasure_mul_same_space _ _
    (fun _ : Ω × Ω => (-1 : ℝ)) measurable_const hm₁
  have ht := tendstoInMeasure_sub (P.prod P) _ _ _ _ hm₀ hneg
  simp only [neg_one_mul, sub_neg_eq_add] at ht
  apply TendstoInMeasure.congr _ (Filter.EventuallyEq.refl _ _) ht
  intro r
  have hfinite (f : BoundedContinuousFunction ℂ ℝ) :
      ∀ᵐ ω ∂P, fieldChaosMass P (Φ r) ν (fun x => (f x).toNNReal) γ ω ≠ ⊤ :=
    centeredGaussianField_fieldChaosMass_ne_top_ae P (Φ r) (hΦ r) ⟨ν, inferInstance⟩
      (fun x => (f x).toNNReal) f.continuous.measurable.real_toNNReal
      ⟨‖f‖.toNNReal, fun x => Real.toNNReal_mono (by
        simpa only [Real.norm_eq_abs] using (le_abs_self (f x)).trans (f.norm_coe_le_norm x))⟩ γ
  have hfin₀ : ∀ᵐ ω : Ω × Ω ∂P.prod P,
      fieldChaosMass P (Φ r) ν (fun x => (f₀ x).toNNReal) γ ω.1 ≠ ⊤ :=
    measurePreserving_fst.quasiMeasurePreserving.ae (hfinite f₀)
  have hfin₁ : ∀ᵐ ω : Ω × Ω ∂P.prod P,
      fieldChaosMass P (Φ r) ν (fun x => (f₁ x).toNNReal) γ ω.2 ≠ ⊤ :=
    measurePreserving_snd.quasiMeasurePreserving.ae (hfinite f₁)
  filter_upwards [hfin₀, hfin₁] with ω hω hω'
  rw [he, ENNReal.toReal_add hω hω']

end DOZZ.Proofs
