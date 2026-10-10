/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.RootedMomentIdentity
public import DOZZ.GMC.Construction.RootedMeasureKernel
public import DOZZ.GMC.Annulus.BallCover
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Signed observables under the rooted identity -/

@[expose] public section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Rooted expectations of measurable functionals are measurable in the insertion point. -/
theorem fusion_rooted_expectation_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (G : Measure ℂ → ℝ≥0∞) (hG : Measurable G) :
    Measurable (fun u => ∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P) := by
  let _ : IsProbabilityMeasure P := hX.1
  obtain ⟨N, hN, hf, he⟩ := equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  have hmeas : Measurable (fun u => ∫⁻ ω, G (gmcRootedMeasure γ u (N ω)) ∂P) :=
    (hG.comp (measurable_gmcRootedMeasure_family N hN hf γ)).lintegral_prod_right'
  have heq : (fun u => ∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P) =
      (fun u => ∫⁻ ω, G (gmcRootedMeasure γ u (N ω)) ∂P) := by
    funext u
    exact lintegral_congr_ae (he.mono fun ω h => by dsimp only; rw [h])
  rw [heq]
  exact hmeas

/-- Finite absolute rooted integrals allow the nonnegative identity to be read as a real identity.
Both sides are integrable; no first moment of the Coulomb mass is required. -/
theorem fusion_rooted_nonnegative_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (f : ℂ → ℝ) (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (G : Measure ℂ → ℝ≥0∞) (hG : Measurable G)
    (hb : (∫⁻ u, ENNReal.ofReal (f u) *
      (∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P) ∂gmcReferenceMeasure) < ⊤) :
    Integrable (fun ω => (G (M ω)).toReal * (∫ u, f u ∂M ω)) P ∧
    Integrable (fun u => f u * (∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P).toReal)
      gmcReferenceMeasure ∧
    (∫ ω, (G (M ω)).toReal * (∫ u, f u ∂M ω) ∂P) =
      ∫ u, f u * (∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P).toReal
        ∂gmcReferenceMeasure := by
  let L := fun ω => (∫⁻ u, ENNReal.ofReal (f u) ∂M ω) * G (M ω)
  let R := fun u => ENNReal.ofReal (f u) *
    (∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P)
  have hL : AEMeasurable L P := by
    have hM' := gmc_measure_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM
    exact ((Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hf)).comp_aemeasurable hM').mul
      (hG.comp_aemeasurable hM')
  have hR : Measurable R := (ENNReal.measurable_ofReal.comp hf).mul
    (fusion_rooted_expectation_measurable P X hX γ hγ hγ2 M hM G hG)
  have hid : (∫⁻ ω, L ω ∂P) = ∫⁻ u, R u ∂gmcReferenceMeasure := by
    have h := DOZZ.equatorGFF_rooted_GMC_identity P X hX γ hγ hγ2 M hM
      (fun u _ μ => ENNReal.ofReal (f u) * G μ)
      ((ENNReal.measurable_ofReal.comp (hf.comp measurable_fst)).mul
        (hG.comp (measurable_snd.comp measurable_snd)))
    calc
      _ = ∫⁻ ω, ∫⁻ u, ENNReal.ofReal (f u) * G (M ω) ∂M ω ∂P := by
        apply lintegral_congr
        intro ω
        exact (lintegral_mul_const _ (ENNReal.measurable_ofReal.comp hf)).symm
      _ = _ := h
      _ = _ := by
        apply lintegral_congr
        intro u
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hLb : (∫⁻ ω, L ω ∂P) < ⊤ := hid ▸ hb
  have heL : ∀ ω, (L ω).toReal = (G (M ω)).toReal * (∫ u, f u ∂M ω) := by
    intro ω
    dsimp only [L]
    rw [ENNReal.toReal_mul, mul_comm,
      ← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hf.aestronglyMeasurable]
  have heR : ∀ u, (R u).toReal = f u *
      (∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P).toReal := by
    intro u
    dsimp only [R]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hf0 u)]
  have hLi := integrable_toReal_of_lintegral_ne_top hL hLb.ne
  have hRi := integrable_toReal_of_lintegral_ne_top hR.aemeasurable hb.ne
  refine ⟨hLi.congr (ae_of_all _ heL), hRi.congr (ae_of_all _ heR), ?_⟩
  calc
    _ = ∫ ω, (L ω).toReal ∂P := integral_congr_ae (ae_of_all _ fun ω => (heL ω).symm)
    _ = (∫⁻ ω, L ω ∂P).toReal := integral_toReal hL (ae_lt_top' hL hLb.ne)
    _ = (∫⁻ u, R u ∂gmcReferenceMeasure).toReal := congrArg ENNReal.toReal hid
    _ = ∫ u, (R u).toReal ∂gmcReferenceMeasure :=
      (integral_toReal hR.aemeasurable (ae_lt_top hR hb.ne)).symm
    _ = _ := integral_congr_ae (ae_of_all _ heR)

/-- The signed rooted formula follows by separately integrating the positive and negative parts.
The sole analytic condition is the finite absolute rooted integral. -/
theorem fusion_rooted_real_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (f : ℂ → ℝ) (hf : Measurable f)
    (hfi : ∀ᵐ ω ∂P, Integrable f (M ω))
    (G : Measure ℂ → ℝ≥0∞) (hG : Measurable G)
    (hb : (∫⁻ u, ENNReal.ofReal |f u| *
      (∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P) ∂gmcReferenceMeasure) < ⊤) :
    Integrable (fun ω => (G (M ω)).toReal * (∫ u, f u ∂M ω)) P ∧
    Integrable (fun u => f u * (∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P).toReal)
      gmcReferenceMeasure ∧
    (∫ ω, (G (M ω)).toReal * (∫ u, f u ∂M ω) ∂P) =
      ∫ u, f u * (∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P).toReal
        ∂gmcReferenceMeasure := by
  let fp := fun u => max (f u) 0
  let fn := fun u => max (-f u) 0
  have hfp : Measurable fp := hf.max measurable_const
  have hfn : Measurable fn := hf.neg.max measurable_const
  have hbp : (∫⁻ u, ENNReal.ofReal (fp u) *
      (∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P) ∂gmcReferenceMeasure) < ⊤ := by
    apply lt_of_le_of_lt (lintegral_mono ?_) hb
    intro u
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (max_le (le_abs_self _) (abs_nonneg _))) le_rfl
  have hbn : (∫⁻ u, ENNReal.ofReal (fn u) *
      (∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P) ∂gmcReferenceMeasure) < ⊤ := by
    apply lt_of_le_of_lt (lintegral_mono ?_) hb
    intro u
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (max_le (neg_le_abs _) (abs_nonneg _))) le_rfl
  obtain ⟨hLp, hRp, hep⟩ := fusion_rooted_nonnegative_integral P X hX γ hγ hγ2 M hM
    fp hfp (fun _ => le_max_right _ _) G hG hbp
  obtain ⟨hLn, hRn, hen⟩ := fusion_rooted_nonnegative_integral P X hX γ hγ hγ2 M hM
    fn hfn (fun _ => le_max_right _ _) G hG hbn
  have hsplit : ∀ u, f u = fp u - fn u := by
    intro u
    dsimp only [fp, fn]
    by_cases h : 0 ≤ f u
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
    · have h' : f u ≤ 0 := le_of_not_ge h
      rw [max_eq_right h', max_eq_left (neg_nonneg.mpr h')]
      ring
  have heL : (fun ω => (G (M ω)).toReal * (∫ u, fp u ∂M ω) -
      (G (M ω)).toReal * (∫ u, fn u ∂M ω)) =ᵐ[P]
      (fun ω => (G (M ω)).toReal * (∫ u, f u ∂M ω)) := by
    filter_upwards [hfi] with ω hω
    rw [← mul_sub, ← integral_sub hω.pos_part hω.neg_part]
    congr 1
    exact integral_congr_ae (ae_of_all _ fun u => (hsplit u).symm)
  have heR : (fun u => fp u * (∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P).toReal -
      fn u * (∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P).toReal) =
      (fun u => f u * (∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P).toReal) := by
    funext u
    rw [← sub_mul, ← hsplit u]
  refine ⟨(hLp.sub hLn).congr heL, heR ▸ hRp.sub hRn, ?_⟩
  calc
    _ = ∫ ω, ((G (M ω)).toReal * (∫ u, fp u ∂M ω) -
        (G (M ω)).toReal * (∫ u, fn u ∂M ω)) ∂P := integral_congr_ae heL.symm
    _ = _ := integral_sub hLp hLn
    _ = (∫ u, fp u * (∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P).toReal
        ∂gmcReferenceMeasure) -
      (∫ u, fn u * (∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P).toReal
        ∂gmcReferenceMeasure) := by rw [hep, hen]
    _ = _ := by rw [← integral_sub hRp hRn, heR]

end DOZZ.Proofs
