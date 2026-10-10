/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.InverseInterpolation
import Mathlib.MeasureTheory.Integral.Prod
/-! # Fubini for signed inverse-mass interpolation -/
@[expose] public section
open MeasureTheory Set Filter
namespace DOZZ.Proofs
/-- Both the interpolation derivative and its absolute value have finite time integrals. -/
theorem fusion_inverse_interpolation_integrable (a b p : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => -p * (b - a) * (t * b + (1 - t) * a) ^ (-p - 1)) (Icc 0 1) volume ∧
    (∫ t in Icc (0 : ℝ) 1, ‖-p * (b - a) * (t * b + (1 - t) * a) ^ (-p - 1)‖) =
      |b ^ (-p) - a ^ (-p)| := by
  have hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < t * b + (1 - t) * a := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t; simpa using ha
    · have h1 := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) hb
      have h2 := mul_nonneg (sub_nonneg.mpr ht.2) ha.le
      linarith
  have hc : ContinuousOn (fun t : ℝ => (t * b + (1 - t) * a) ^ (-p - 1)) (Icc 0 1) := by
    apply ContinuousOn.rpow_const
    · fun_prop
    · intro t ht; exact Or.inl (hpos t ht).ne'
  have hi : IntegrableOn (fun t : ℝ => -p * (b - a) * (t * b + (1 - t) * a) ^ (-p - 1))
      (Icc 0 1) volume := (hc.integrableOn_Icc).const_mul (-p * (b - a))
  refine ⟨hi, ?_⟩
  have he := fusion_inverse_interpolation a b p ha hb
  have hn : (fun t : ℝ => ‖-p * (b - a) * (t * b + (1 - t) * a) ^ (-p - 1)‖) =ᵐ[volume.restrict (Icc 0 1)]
      (fun t => |-p * (b - a)| * (t * b + (1 - t) * a) ^ (-p - 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg (hpos t ht).le _)]
  have hnonneg : 0 ≤ ∫ t in Icc (0 : ℝ) 1, (t * b + (1 - t) * a) ^ (-p - 1) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact Real.rpow_nonneg (hpos t ht).le _
  rw [integral_congr_ae hn, integral_const_mul, he, abs_mul, abs_mul, abs_of_nonneg hnonneg]
  rw [abs_mul]
/-- Absolute time integration and the two endpoint inverse moments supply the integrability
needed for Fubini. -/
theorem fusion_inverse_expectation_interpolation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (a b : Ω → ℝ) (p : ℝ)
    (ha : AEStronglyMeasurable a P) (hb : AEStronglyMeasurable b P)
    (hpos : ∀ᵐ ω ∂P, 0 < a ω ∧ 0 < b ω)
    (hai : Integrable (fun ω => a ω ^ (-p)) P)
    (hbi : Integrable (fun ω => b ω ^ (-p)) P) :
    (∫ ω, b ω ^ (-p) ∂P) - (∫ ω, a ω ^ (-p) ∂P) =
      ∫ t in Icc (0 : ℝ) 1, ∫ ω, -p * (b ω - a ω) *
        (t * b ω + (1 - t) * a ω) ^ (-p - 1) ∂P := by
  let T := volume.restrict (Icc (0 : ℝ) 1)
  let D := fun q : Ω × ℝ => -p * (b q.1 - a q.1) *
    (q.2 * b q.1 + (1 - q.2) * a q.1) ^ (-p - 1)
  have ham : AEStronglyMeasurable (fun q : Ω × ℝ => a q.1) (P.prod T) :=
    ha.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hbm : AEStronglyMeasurable (fun q : Ω × ℝ => b q.1) (P.prod T) :=
    hb.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have htm : AEStronglyMeasurable (fun q : Ω × ℝ => q.2) (P.prod T) :=
    measurable_snd.aestronglyMeasurable
  have hDm : AEStronglyMeasurable D (P.prod T) :=
    ((hbm.sub ham).const_mul (-p)).mul
      (((htm.mul hbm).add ((aestronglyMeasurable_const.sub htm).mul ham)).aemeasurable.pow_const _).aestronglyMeasurable
  have hDi : Integrable D (P.prod T) := by
    apply (integrable_prod_iff hDm).mpr
    constructor
    · filter_upwards [hpos] with ω hω
      exact (fusion_inverse_interpolation_integrable (a ω) (b ω) p hω.1 hω.2).1
    · apply (hbi.sub hai).norm.congr
      filter_upwards [hpos] with ω hω
      exact (fusion_inverse_interpolation_integrable (a ω) (b ω) p hω.1 hω.2).2.symm
  calc
    _ = ∫ ω, b ω ^ (-p) - a ω ^ (-p) ∂P := (integral_sub hbi hai).symm
    _ = ∫ ω, ∫ t, D (ω, t) ∂T ∂P := by
      apply integral_congr_ae
      filter_upwards [hpos] with ω hω
      rw [fusion_inverse_interpolation (a ω) (b ω) p hω.1 hω.2, ← integral_const_mul]
    _ = _ := integral_integral_swap hDi

end DOZZ.Proofs
