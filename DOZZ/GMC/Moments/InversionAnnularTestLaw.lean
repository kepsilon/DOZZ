/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionAdmissibleLaw
public import DOZZ.GMC.Moments.ReferenceFinite

/-! Inversion invariance of arbitrary GMC test vectors on annular charts. -/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Distributions ENNReal

namespace DOZZ.Proofs

/-- Every finite vector of compact annular test integrals of an arbitrary GMC has the same
law after inversion. No preferred version of the chaos is used. -/
theorem gmc_inversion_annular_test_vector_law
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (U : Set ℂ) (hUopen : IsOpen U) {m R : ℝ} (hm : 0 < m) (hR : 0 ≤ R)
    (hU : ∀ x ∈ U, 2 * m ≤ ‖x‖ ∧ ‖x‖ ≤ R)
    (f : Fin k → BoundedContinuousFunction ℂ ℝ)
    (hfc : ∀ j, HasCompactSupport (f j : ℂ → ℝ))
    (hfU : ∀ j, tsupport (f j : ℂ → ℝ) ⊆ U) :
    P.map (fun ω j => ∫ x, f j x ∂(M ω).map (fun z : ℂ => z⁻¹)) =
      P.map (fun ω j => ∫ x, f j x ∂M ω) := by
  let : IsProbabilityMeasure P := hX.1
  obtain ⟨Xc, hXc, _hconv⟩ := hM.2
  obtain ⟨g, hg, Z, N, hgap, hmem, hlim, hZ, hN, hNae⟩ :=
    isGMCOf_inversion_annular_version P X hX γ hγ hγ2 M hM Xc hXc U hUopen hm hR hU
  obtain ⟨A, hA, _hAfin, hAae⟩ :=
    isGMCOf_restrict_admissible_version P X hX γ hγ hγ2 M hM Xc hXc U hUopen
  have hY := isCircleAverage_admissible P X hX Xc hXc U hUopen
  let : IsFiniteMeasure gmcReferenceMeasure := ⟨lt_top_iff_ne_top.mpr gmcReferenceMeasure_univ_ne_top⟩
  have href : logRegularizationReference U (fun x => normPlus x ^ (-4 : ℝ)) =
      gmcReferenceMeasure.restrict U := by
    rw [logRegularizationReference_restrict_of_subset univ U
      (fun x => normPlus x ^ (-4 : ℝ)) hUopen.measurableSet (subset_univ _)]
    simp only [logRegularizationReference, Measure.restrict_univ, gmcReferenceMeasure]
  let : IsFiniteMeasure (logRegularizationReference U (fun x => normPlus x ^ (-4 : ℝ))) := by
    rw [href]
    infer_instance
  have hfdd ε (_hε : 0 < ε) (_hεb : ε ≤ min (min (m / 2) 1) 1) n (xs : Fin n → ℂ) :
      P.map (fun ω i => Z ω (xs i) (Real.log (1 / ε))) =
      P.map (fun ω i => Xc ω (xs i) (Real.log (1 / ε))) := by
    exact inversionCircle_fdd_law P X hX P X hX Xc hXc
      (fun i => (xs i, Real.log (1 / ε)))
      (fun i ω => Z ω (xs i) (Real.log (1 / ε))) (fun i => hmem _ _)
      (fun i => g (xs i, Real.log (1 / ε))) (fun i => hg _)
      (fun i => hgap _) (fun i => hlim _)
  have hlaw := admissibleLogChaos_limit_vector_law_of_fdd P P U
    (fun x => normPlus x ^ (-4 : ℝ)) (min (m / 2) 1) 1
    (fun ω ε x => Z ω x (Real.log (1 / ε)))
    (fun ω ε x => Xc ω x (Real.log (1 / ε))) hZ hY γ N A hN hA hfdd f hfc hfU
  have heq (μ : Measure ℂ) (j : Fin k) : ∫ x, f j x ∂μ.restrict U = ∫ x, f j x ∂μ :=
    integral_restrict_eq_integral_of_zero_on_compl μ U hUopen.measurableSet (f j)
      (boundedContinuousFunction_eq_zero_off_tsupport_subset (f j) U (hfU j))
  have hleft : (fun ω j => ∫ x, f j x ∂N ω) =ᵐ[P]
      fun ω j => ∫ x, f j x ∂(M ω).map (fun z : ℂ => z⁻¹) := by
    filter_upwards [hNae] with ω hω
    funext j
    rw [hω, heq]
  have hright : (fun ω j => ∫ x, f j x ∂A ω) =ᵐ[P] fun ω j => ∫ x, f j x ∂M ω := by
    filter_upwards [hAae] with ω hω
    funext j
    rw [← hω, heq]
  exact (Measure.map_congr hleft).symm.trans (hlaw.trans (Measure.map_congr hright))

end DOZZ.Proofs
