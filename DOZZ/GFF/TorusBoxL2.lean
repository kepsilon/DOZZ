/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.TorusFourierTestApprox
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# DOZZ.GFF.TorusBoxL2

The local chart identifies the compactly supported plane `L²` norm with the unit-torus norm after
rescaling by the physical box side.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace Topology lp

namespace DOZZ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure GFFUnitTorus2) := by
  infer_instance

private def centeredUnitBox : Set (Fin 2 → ℝ) :=
  {x | ∀ i, x i ∈ Set.Ioc (-1 / 2 : ℝ) ((-1 / 2 : ℝ) + 1)}

private theorem measurableSet_centeredUnitBox : MeasurableSet centeredUnitBox := by
  have hEq : centeredUnitBox =
      ⋂ i : Fin 2, {x : Fin 2 → ℝ |
        x i ∈ Set.Ioc (-1 / 2 : ℝ) ((-1 / 2 : ℝ) + 1)} := by
    ext x
    norm_num [centeredUnitBox]
  rw [hEq]
  exact MeasurableSet.iInter fun i : Fin 2 =>
    measurableSet_Ioc.preimage (measurable_pi_apply i)

private theorem integral_eq_setIntegral_of_support_subset_box
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) {F : α → ℝ} (hF : Function.support F ⊆ s) :
    (∫ x, F x ∂μ) = ∫ x in s, F x ∂μ := by
  calc
    (∫ x, F x ∂μ) = ∫ x, s.indicator F x ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ s
      · simp [hx]
      · have hzero : F x = 0 := by
          by_contra hn
          exact hx (hF hn)
        simp [hx, hzero]
    _ = ∫ x in s, F x ∂μ := by rw [integral_indicator hs]

private theorem torusBoxPoint_rep (L : ℝ)
    (x : {x : Fin 2 → ℝ //
      ∀ i, x i ∈ Set.Ioc (-1 / 2 : ℝ) ((-1 / 2 : ℝ) + 1)}) :
    torusBoxPoint L (fun i => (x.1 i : UnitAddCircle)) =
      L • Complex.measurableEquivPi.symm x.1 := by
  let e := UnitAddTorus.measurableEquivPiIoc
    (fun _ : Fin 2 => (-1 / 2 : ℝ))
  have he : e (fun i => (x.1 i : UnitAddCircle)) = x := by
    calc
      e (fun i => (x.1 i : UnitAddCircle)) = e (e.symm x) := by rfl
      _ = x := e.apply_symm_apply x
  apply Complex.ext
  · simp [torusBoxPoint, e, he, Complex.measurableEquivPi_symm_apply,
      Complex.real_smul]
  · simp [torusBoxPoint, e, he, Complex.measurableEquivPi_symm_apply,
      Complex.real_smul]

/-- A function supported strictly inside the fundamental box has its plane square integral equal
to the torus square integral times the box area. -/
theorem integral_sq_eq_torusBox (L : ℝ) (hL : 0 < L) (g : ℂ → ℝ)
    (hsupp : Function.support g ⊆ ball (0 : ℂ) (L / 2)) :
    (∫ z : ℂ, g z ^ 2) = L ^ 2 *
      ∫ t : GFFUnitTorus2, g (torusBoxPoint L t) ^ 2 := by
  let H : ℂ → ℝ := fun z => g z ^ 2
  let Hpi : (Fin 2 → ℝ) → ℝ := fun x =>
    g (L • Complex.measurableEquivPi.symm x) ^ 2
  have hsuppPi : Function.support Hpi ⊆ centeredUnitBox := by
    intro x hx
    by_contra hxbox
    change ¬ ∀ i, x i ∈ Set.Ioc (-1 / 2 : ℝ) ((-1 / 2 : ℝ) + 1) at hxbox
    push Not at hxbox
    obtain ⟨i, hi⟩ := hxbox
    let z : ℂ := L • Complex.measurableEquivPi.symm x
    have hcoord : L / 2 ≤ ‖z‖ := by
      have hi' : x i ≤ -1 / 2 ∨ 1 / 2 < x i := by
        by_cases hlo : x i ≤ -1 / 2
        · exact Or.inl hlo
        · have hlow : -1 / 2 < x i := lt_of_not_ge hlo
          have hnotUpper : ¬ x i ≤ (-1 / 2 : ℝ) + 1 := by
            intro hu
            exact hi ⟨hlow, hu⟩
          have heq : (-1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
          rw [heq] at hnotUpper
          exact Or.inr (lt_of_not_ge hnotUpper)
      have hcoordAbs : L / 2 ≤ |z.re| ∨ L / 2 ≤ |z.im| := by
        fin_cases i
        · have hi0 : x 0 ≤ -1 / 2 ∨ 1 / 2 < x 0 := by simpa using hi'
          have hzre : z.re = L * x 0 := by
            simp [z, Complex.measurableEquivPi_symm_apply, Complex.real_smul]
          rw [hzre]
          rcases hi0 with hleft | hright
          · left
            rw [abs_of_nonpos (by nlinarith [hL])]
            nlinarith
          · left
            rw [abs_of_pos (by nlinarith [hL])]
            nlinarith
        · have hi1 : x 1 ≤ -1 / 2 ∨ 1 / 2 < x 1 := by simpa using hi'
          have hzim : z.im = L * x 1 := by
            simp [z, Complex.measurableEquivPi_symm_apply, Complex.real_smul]
          rw [hzim]
          rcases hi1 with hleft | hright
          · right
            rw [abs_of_nonpos (by nlinarith [hL])]
            nlinarith
          · right
            rw [abs_of_pos (by nlinarith [hL])]
            nlinarith
      rcases hcoordAbs with h | h
      · exact h.trans (Complex.abs_re_le_norm z)
      · exact h.trans (Complex.abs_im_le_norm z)
    have hnot : z ∉ ball (0 : ℂ) (L / 2) := by
      simpa [z, mem_ball, dist_eq_norm] using hcoord
    have hg_ne : g (L • Complex.measurableEquivPi.symm x) ≠ 0 := by
      intro hgzero
      apply hx
      change g (L • Complex.measurableEquivPi.symm x) ^ 2 = 0
      rw [hgzero]
      norm_num
    have hmem : z ∈ ball (0 : ℂ) (L / 2) := hsupp hg_ne
    exact hnot hmem
  have hscaled : (∫ z : ℂ, g (L • z) ^ 2) =
      (L ^ 2)⁻¹ * ∫ z : ℂ, g z ^ 2 := by
    have h := MeasureTheory.Measure.integral_comp_smul
      (μ := (volume : Measure ℂ)) (fun z : ℂ => g z ^ 2) L
    simpa [Complex.finrank_real_complex, abs_of_pos (inv_pos.mpr (pow_pos hL 2)),
      smul_eq_mul] using h
  have hchange : (∫ z : ℂ, g (L • z) ^ 2) = ∫ x : Fin 2 → ℝ, Hpi x := by
    calc
      (∫ z : ℂ, g (L • z) ^ 2) =
          ∫ z : ℂ, Hpi (Complex.measurableEquivPi z) := by
        apply integral_congr_ae
        filter_upwards [] with z
        change g (L • z) ^ 2 =
          g (L • Complex.measurableEquivPi.symm (Complex.measurableEquivPi z)) ^ 2
        rw [Complex.measurableEquivPi.symm_apply_apply]
      _ = ∫ x : Fin 2 → ℝ, Hpi x :=
        (Complex.volume_preserving_equiv_pi).integral_comp' Hpi
  have hbox : (∫ x : Fin 2 → ℝ, Hpi x) = ∫ x in centeredUnitBox, Hpi x :=
    integral_eq_setIntegral_of_support_subset_box measurableSet_centeredUnitBox hsuppPi
  have hpre := UnitAddTorus.integral_preimage
    (fun t : GFFUnitTorus2 => g (torusBoxPoint L t) ^ 2)
    (fun _ : Fin 2 => (-1 / 2 : ℝ))
  have htorus :
      (∫ t : GFFUnitTorus2, g (torusBoxPoint L t) ^ 2) =
        ∫ x in centeredUnitBox, Hpi x := by
    calc
      (∫ t : GFFUnitTorus2, g (torusBoxPoint L t) ^ 2) =
          ∫ (x : Fin 2 → ℝ) in centeredUnitBox,
            g (torusBoxPoint L (fun i => (x i : UnitAddCircle))) ^ 2 := by
        simpa [centeredUnitBox] using hpre
      _ = ∫ x in centeredUnitBox, Hpi x := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_centeredUnitBox] with x hx
        have hx' : x ∈ {x : Fin 2 → ℝ |
            ∀ i, x i ∈ Set.Ioc (-1 / 2 : ℝ) ((-1 / 2 : ℝ) + 1)} := by
          simpa [centeredUnitBox] using hx
        have hpoint := torusBoxPoint_rep L ⟨x, hx'⟩
        simp [Hpi, hpoint]
  calc
    (∫ z : ℂ, g z ^ 2) = L ^ 2 * (L ^ 2)⁻¹ * ∫ z : ℂ, g z ^ 2 := by
      field_simp [ne_of_gt hL]
    _ = L ^ 2 * ∫ z : ℂ, g (L • z) ^ 2 := by rw [hscaled]; ring
    _ = L ^ 2 * ∫ x : Fin 2 → ℝ, Hpi x := by rw [hchange]
    _ = L ^ 2 * ∫ x in centeredUnitBox, Hpi x := by rw [hbox]
    _ = L ^ 2 * ∫ t : GFFUnitTorus2, g (torusBoxPoint L t) ^ 2 := by rw [← htorus]

end DOZZ

end
