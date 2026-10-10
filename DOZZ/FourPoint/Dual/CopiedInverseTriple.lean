/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.CopyOrdering
public import DOZZ.FourPoint.Dual.SourceDecouplingBound
import Mathlib.Tactic
/-! The literal copied inverse expectation in source radial/outer/inner coordinates. -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Reorder the actual independently reinserted kernel masses before converting their
inverse expectation to real. All parameterized masses are measurable on the lateral carrier. -/
theorem dual_copied_inverse_moment_triple
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Xc : Ω → ℂ → ℝ → ℝ) (hA : AEMeasurable (originRadialPath Xc) P)
    (N : Ω → Measure ℂ) (hN : Measurable N)
    (hfin : ∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤)
    (γ α₁ α₂ α₃ p s r : ℝ) (z : ℂ) :
    dualCopiedSeparatedInverseMoment P Xc N γ α₁ α₂ α₃ p z s r =
      ∫⁻ v : (Ω × Ω) × Ω,
        ((∫⁻ x in reflected_innerRegion s,
          ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)*
            ENNReal.ofReal (reflected_global_reinsertionWeight γ (originRadialPath Xc v.1.1) x) ∂N v.2)+
         (∫⁻ x in reflected_outerRegion r,
          ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)*
            ENNReal.ofReal (reflected_global_reinsertionWeight γ (originRadialPath Xc v.1.1) x) ∂N v.1.2))^(-p)
          ∂(P.prod P).prod P := by
  let J := fun U (a : TwoSidedPath) ω => ∫⁻ x in U,
    ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)*
      ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂N ω
  have hm (U : Set ℂ) (hU : IsOpen U) (hU0 : U ⊆ ({0} : Set ℂ)ᶜ) :
      Measurable (fun v : TwoSidedPath × Ω => J U v.1 v.2) :=
    reflected_chart_parameter_mass_measurable U hU N hN
      (fun ω K hK hKU => hfin ω K hK (hKU.trans hU0))
      (fun v : TwoSidedPath × ℂ => ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z v.2)*
        ENNReal.ofReal (reflected_global_reinsertionWeight γ v.1 v.2))
      (((dual_kernel_measurable γ α₁ α₂ α₃ z).comp measurable_snd).ennreal_ofReal.mul
        (reflected_global_reinsertionWeight_measurable γ).ennreal_ofReal)
  have hi : Measurable (fun v : TwoSidedPath × Ω => J (reflected_innerRegion s) v.1 v.2) := by
    apply hm _ ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const))
    intro x hx hx0
    have he : x = 0 := mem_singleton_iff.mp hx0
    have hxpos : 0 < ‖x‖ := hx.1
    simp only [he, norm_zero, lt_self_iff_false] at hxpos
  have ho : Measurable (fun v : TwoSidedPath × Ω => J (reflected_outerRegion r) v.1 v.2) := by
    apply hm _ ((isOpen_lt continuous_const continuous_norm).inter
      (Set.toFinite ({0,1} : Set ℂ)).isClosed.isOpen_compl)
    intro x hx hx0
    have he : x = 0 := mem_singleton_iff.mp hx0
    exact hx.2 (by simp [he])
  let F : TwoSidedPath × (Ω × Ω) → ℝ≥0∞ := fun v =>
    (J (reflected_innerRegion s) v.1 v.2.1+J (reflected_outerRegion r) v.1 v.2.2)^(-p)
  have hF : Measurable F :=
    ((hi.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).add
      (ho.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))).pow_const (-p)
  exact dual_radial_copy_lintegral_regroup P (originRadialPath Xc) hA F hF

end DOZZ.Proofs
