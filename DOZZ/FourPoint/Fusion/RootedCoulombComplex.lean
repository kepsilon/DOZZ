/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.RootedIntegrability
public import DOZZ.FourPoint.Fusion.RootedLowerBound
public import DOZZ.FourPoint.Fusion.MovingRootFiniteness

/-! # Signed rooting of Coulomb inverse moments with an integrable spatial observable -/

@[expose] public section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The uniform inverse moments `fusion_rootedMass_inverse_moment_uniform` supply the
absolute-integrability condition in complex rooting. All insertion points are in the unit chart. -/
theorem fusion_rooted_coulomb_complex_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {N : ℕ} (α : Fin N → ℝ) (z : Fin N → ℂ) (hz : ∀ j, ‖z j‖ ≤ 1)
    (αinf s : ℝ) (hs : s < 0)
    (hmfin : ∀ᵐ ω ∂P, coulombMass γ (M ω) α z αinf < ⊤)
    (f : ℂ → ℂ) (hf : Measurable f) (hfi : Integrable f gmcReferenceMeasure) :
    (∀ᵐ ω ∂P, Integrable f (M ω)) ∧
    Integrable (fun ω => ((coulombMass γ (M ω) α z αinf ^ s).toReal : ℂ) *
      (∫ u, f u ∂M ω)) P ∧
    Integrable (fun u => f u *
      ((∫⁻ ω, coulombMass γ (gmcRootedMeasure γ u (M ω)) α z αinf ^ s ∂P).toReal : ℂ))
      gmcReferenceMeasure ∧
    (∫ ω, ((coulombMass γ (M ω) α z αinf ^ s).toReal : ℂ) * (∫ u, f u ∂M ω) ∂P) =
      ∫ u, f u *
        ((∫⁻ ω, coulombMass γ (gmcRootedMeasure γ u (M ω)) α z αinf ^ s ∂P).toReal : ℂ)
        ∂gmcReferenceMeasure := by
  let G := fun μ : Measure ℂ => coulombMass γ μ α z αinf ^ s
  have hG : Measurable G := (fusion_measurable_coulombMass γ α z αinf).pow_const s
  obtain ⟨C, hC, hbound⟩ := fusion_rootedMass_inverse_moment_uniform P X hX γ hγ hγ2 M hM
    α αinf s hs.le
  have hb : (∫⁻ u, ENNReal.ofReal ‖f u‖ *
      (∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P) ∂gmcReferenceMeasure) < ⊤ := by
    calc
      _ ≤ ∫⁻ u, ENNReal.ofReal ‖f u‖ * C ∂gmcReferenceMeasure :=
        lintegral_mono fun u => mul_le_mul' le_rfl (hbound u z hz)
      _ = (∫⁻ u, ENNReal.ofReal ‖f u‖ ∂gmcReferenceMeasure) * C :=
        lintegral_mul_const _ (ENNReal.measurable_ofReal.comp hf.norm)
      _ < ⊤ := ENNReal.mul_lt_top ((hasFiniteIntegral_iff_norm _).mp hfi.hasFiniteIntegral) hC
  have hG0 : ∀ᵐ ω ∂P, G (M ω) ≠ 0 := by
    filter_upwards [hmfin] with ω hω
    intro he
    rcases ENNReal.rpow_eq_zero_iff.mp he with ⟨_, hp⟩ | ⟨ht, _⟩
    · exact (not_lt_of_ge hs.le) hp
    · exact hω.ne ht
  have hfM := fusion_rooted_spatial_integrable P X hX γ hγ hγ2 M hM f hf G hG hG0 hb
  exact ⟨hfM, fusion_rooted_complex_integral P X hX γ hγ hγ2 M hM f hf hfM G hG hb⟩

end DOZZ.Proofs
