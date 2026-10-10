/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.CopiedInnerPolar
public import DOZZ.FourPoint.Dual.PathLikelihood
import Mathlib.Tactic
/-! Literal copied inner-kernel comparison on the same removed source plane carrier. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The copied plane carrier's projection is the original lateral source. This identifies
the actual kernel bounds simultaneously for every copied radial path. -/
theorem dual_source_copied_inner_kernel_squeeze
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α₁ α₂ α₃ h R : ℝ)
    (hγ : γ ≠ 0) (A : Ω → TwoSidedPath) (M N : Ω → Measure ℂ) (Z : Ω → Measure ℝ)
    (heN : N =ᵐ[P] (fun ω => (M ω).withDensity (lateralRadialWeight γ (A ω))))
    (heZ : Z =ᵐ[P] (fun ω => lateralProjectedGMC γ (A ω) (M ω)))
    (z : ℂ) (hz : z ≠ 0) (T : ℝ≥0) (hT : (T : ℝ) = -Real.log ‖z‖+h)
    (hR : 0 ≤ R) (hR₁ : R < 1) (hη : Real.exp (-(T : ℝ)) < 1)
    (hsep : Real.exp (-(T : ℝ)) ≤ R*‖z‖) :
    ∀ᵐ ω ∂P, ∀ a : TwoSidedPath,
      let η := Real.exp (-(T : ℝ))
      let V := ∫⁻ u, (if 0 < u then ENNReal.ofReal (Real.exp
        (γ*(brownianShiftPath T (radialPositiveHalf a) (Real.toNNReal u)-(Q γ-α₁)*u))) else 0)
        ∂(Z ω).map (fun s => s-(T : ℝ))
      let β := dualPathRadialScale γ (Q γ-α₁) h z a
      let I := ∫⁻ x in reflected_innerRegion η,
        ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)*
          ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂N ω
      ENNReal.ofReal ((1-R)^(2 : ℝ)*(1-η)⁻¹^(-|γ*α₂|)*β)*V ≤ I ∧
        I ≤ ENNReal.ofReal ((1+R)^(2 : ℝ)*(1-η)⁻¹^|γ*α₂| *β)*V := by
  filter_upwards [reflected_removed_carrier_projection P γ A M N heN, heZ] with ω hNω hZω a
  have heβ : dualPathRadialScale γ (Q γ-α₁) h z a =
      ‖z‖^(2 : ℝ)*Real.exp (γ*(a T-(Q γ-α₁)*T)) := by
    have he := dual_radial_scale_eq_restart γ (Q γ-α₁) h
      (fun (_ : Unit) (_ : ℂ) t => a t) z hz ()
    change dualPathRadialScale γ (Q γ-α₁) h z a =
      ‖z‖^(2 : ℝ)*Real.exp (γ*(a (-Real.log ‖z‖+h)-(Q γ-α₁)*(-Real.log ‖z‖+h))) at he
    simpa only [← hT] using he
  have hb := dual_copied_inner_mass_squeeze γ α₁ α₂ α₃ R hγ z a (N ω) hNω.1 T
    hR hR₁ (norm_pos_iff.mpr hz) hη hsep
  dsimp only at hb ⊢
  rw [hNω.2, ← hZω] at hb
  rw [heβ]
  exact hb

end DOZZ.Proofs
