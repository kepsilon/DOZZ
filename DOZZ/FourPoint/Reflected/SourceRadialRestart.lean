/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.CopiedInnerPolar
public import DOZZ.FourPoint.Reflected.LeadingRadialMoment
/-! The actual copied radial inner mass has precisely the source restart scale. -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem reflected_source_copied_radial_restart
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Xc : Ω → ℂ → ℝ → ℝ)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ α h : ℝ) (M N : Ω → Measure ℂ)
    (heq : N =ᵐ[P] (fun ω => (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))))
    (z : ℂ) (hz : z ≠ 0) (T : ℝ≥0) (hcoord : (T : ℝ) = -Real.log ‖z‖+h) :
    ∀ᵐ ω : Ω × Ω ∂P.prod P,
      ENNReal.ofReal (‖z‖^(γ^2/2))*(∫⁻ x in {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < Real.exp (-(T : ℝ))},
        ENNReal.ofReal (‖x‖^(-(γ*α)))*
          ENNReal.ofReal (reflected_global_reinsertionWeight γ (originRadialPath Xc ω.1) x) ∂N ω.2) =
      ENNReal.ofReal (reflected_radial_scale γ (Q γ-α) h Xc z ω.1)*
        ∫⁻ u, (if 0 < u then ENNReal.ofReal (Real.exp
          (γ*(brownianShiftPath T (radialPositiveHalf (originRadialPath Xc ω.1)) (Real.toNNReal u)-
            (Q γ-α)*u))) else 0)
          ∂(lateralProjectedGMC γ (originRadialPath Xc ω.2) (M ω.2)).map (fun s => s-(T : ℝ)) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae (originRadialPath_eval_ae hcont),
    measurePreserving_snd.quasiMeasurePreserving.ae
      (reflected_copied_inner_source_restart P γ α (originRadialPath Xc) M N heq)] with ω hev hi
  rw [hi (originRadialPath Xc ω.1) T,← mul_assoc,← ENNReal.ofReal_mul (Real.rpow_nonneg hn.le _)]
  have hs : ‖z‖^(γ^2/2)*Real.exp (γ*(originRadialPath Xc ω.1 T-(Q γ-α)*(T : ℝ))) =
      reflected_radial_scale γ (Q γ-α) h Xc z ω.1 := by
    rw [hev (T : ℝ),Real.rpow_def_of_pos hn,← Real.exp_add]
    unfold reflected_radial_scale
    rw [hcoord]
    congr 1
    ring
  rw [hs]

end DOZZ.Proofs
