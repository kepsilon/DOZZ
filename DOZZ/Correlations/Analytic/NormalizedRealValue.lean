/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.NormalizedRealPolynomial

/-! Real restriction of the holomorphic normalized cutoff is the retained Coulomb moment. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- The actual complex cutoff observable, on real charges, equals the literal retained Coulomb
moment with the final charge at infinity. No additional analytic identity is assumed. -/
theorem normalized_vertex_moment_ofReal
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (β : Fin (N + 1) → ℝ) (z : Fin N → ℂ) (r : ℝ) (hr : 0 ≤ r)
    (O : Set ℂ) (ho : IsOpen O) (hb : Bornology.IsBounded O) (hn : O.Nonempty)
    (hO : O ⊆ retainedRegion z r) :
    normalizedVertexMoment P Xc M O γ z r (fun i => (β i : ℂ)) =
      ((∫⁻ ω, (∫⁻ x in O,
        coulombWeight γ (fun i => β i.castSucc) z (β (Fin.last N)) x ∂M ω) ^
          ((2 * Q γ - ∑ i, β i) / γ) ∂P).toReal : ℂ) := by
  let p := (2 * Q γ - ∑ i, β i) / γ
  let L (ω : Ω) := ∑ i, β i * Xc ω (mixedVertexCenters z i) (mixedVertexTimes N r i)
  let F (ω : Ω) := Real.exp (L ω - gaussianVariance P L / 2 -
    p * γ * ∑ i, β i.castSucc * equatorCircleMean (z i) r) * (M ω O).toReal ^ p
  have he (ω : Ω) :
      Complex.exp (normalizedVertexPolynomial P Xc γ z r (fun i => (β i : ℂ)) +
        ∑ i, (β i : ℂ) * (Xc ω (mixedVertexCenters z i) (mixedVertexTimes N r i) : ℂ)) *
        ((M ω O).toReal : ℂ) ^ complexMomentPower γ (fun i => (β i : ℂ)) =
      (F ω : ℂ) := by
    rw [normalizedVertexPolynomial_ofReal P Xc hXc.2.1,
      complexMomentPower_ofReal, ← Complex.ofReal_cpow ENNReal.toReal_nonneg]
    dsimp only [F, L, p]
    push_cast
    congr 2
    ring
  have hLmeas : Measurable L := by
    apply Finset.measurable_sum
    intro i _
    exact (circleAverage_measurable_eval X Xc hXc _ _).const_mul _
  have hm := gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM O ho.measurableSet
  have hF : AEMeasurable F P :=
    ((Real.measurable_exp.comp ((hLmeas.sub_const _).sub_const _)).aemeasurable).mul
      (hm.ennreal_toReal.pow_const p)
  have hFpos : 0 ≤ᵐ[P] F := Filter.Eventually.of_forall (fun ω =>
    mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg ENNReal.toReal_nonneg _))
  have hmass := open_mass_pos_finite_ae P X hX γ hγ hγ2 M hM O ho hb hn
  have hE : (∫⁻ ω, ENNReal.ofReal (F ω) ∂P) =
      ∫⁻ ω, ENNReal.ofReal (Real.exp (L ω - gaussianVariance P L / 2 -
        p * γ * ∑ i, β i.castSucc * equatorCircleMean (z i) r)) * M ω O ^ p ∂P := by
    apply lintegral_congr_ae
    filter_upwards [hmass] with ω hω
    dsimp only [F]
    rw [ENNReal.ofReal_mul (Real.exp_nonneg _),
      ← ENNReal.ofReal_rpow_of_pos (ENNReal.toReal_pos hω.1 hω.2), ENNReal.ofReal_toReal hω.2]
  unfold normalizedVertexMoment
  simp_rw [he]
  have hcast : (∫ ω, (F ω : ℂ) ∂P) = ((∫ ω, F ω ∂P : ℝ) : ℂ) := integral_complex_ofReal
  rw [hcast, integral_eq_lintegral_of_nonneg_ae hFpos hF.aestronglyMeasurable, hE,
    normalized_real_vertex_tilt P X hX γ hγ hγ2 M hM Xc hXc β z r hr O
      ho.measurableSet hO p]

end DOZZ.Proofs
