/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Infinity.WeightTransport
public import DOZZ.GMC.Moments.RhoCoulomb
public import DOZZ.Correlations.Symmetry.InversionSwap
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- The limiting inverted-chart moment is the original moment [KRV, (expression3pointstruct)].
Only the inversion law `equatorGFF_GMC_inversion_law` is used; no symmetry or infinity limit is
assumed. -/
theorem infinity_canonical_moment_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    (∫⁻ ω, (coulombMass γ (M ω) ![α₃, α₂] ![0, 1] α₁) ^ p ∂P) =
      ∫⁻ ω, (rho γ (M ω) α₁ α₂ α₃) ^ p ∂P := by
  have hH := (rho_measure_measurable γ α₁ α₂ α₃).pow_const p
  rw [← equatorGFF_GMC_inversion_law P X hX γ hγ hγ2 M hM _ hH]
  apply lintegral_congr_ae
  filter_upwards [gmc_atomless_of_isGMCOf P X hX γ hγ hγ2 M hM 0,
    gmc_atomless_of_isGMCOf P X hX γ hγ hγ2 M hM 1] with ω h0 h1
  rw [rho_map_inversion γ α₁ α₂ α₃ (M ω) h0 h1,
    rho_eq_coulombMass γ α₃ α₂ α₁ (M ω) h0 h1]

end DOZZ.Proofs
