/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.GlobalUnpinnedCircleLaw
public import DOZZ.GMC.Moments.InversionAdmissibleLaw
public import DOZZ.GMC.Moments.InversionAdmissibleVersion
public import DOZZ.Statements.GMC.AdmissibleLogRegularizationGMCExists

/-! The canonical GMC of the globally unpinned translated circle field, on the source space.
Its finite compact-test laws are exactly those of the origin equator GMC. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs


/-- Every unpinned translated GMC version has the origin compact-test vector law. -/
theorem unpinned_gmc_test_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun q : Ω × (ℂ × ℝ) => Xc q.1 q.2.1 q.2.2))
    (z : ℂ) (hz : 2 ≤ ‖z‖) (U : Set ℂ) (hU : IsOpen U)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ)
    (hN : IsAdmissibleGMCVersion P U (fun x => normPlus x ^ (-4 : ℝ))
      (fun ω ε x => Xc ω (z+x) (Real.log (1/ε)) - Xc ω z 0) γ N)
    {m : ℕ} (f : Fin m → BoundedContinuousFunction ℂ ℝ)
    (hfc : ∀ j, HasCompactSupport (f j : ℂ → ℝ))
    (hfU : ∀ j, tsupport (f j : ℂ → ℝ) ⊆ U) :
    P.map (fun ω j => ∫ x, f j x ∂N ω) =
      P.map (fun ω j => ∫ x, f j x ∂M ω) := by
  let : IsProbabilityMeasure P := hX.1
  obtain ⟨A, hA, _, hAeq⟩ :=
    isGMCOf_restrict_admissible_version P X hX γ hγ hγ2 M hM Xc hc U hU
  have hY := unpinned_circle_admissible P X Xc hX hc hm z hz U hU
  have hZ := isCircleAverage_admissible P X hX Xc hc U hU
  let : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
  have href : logRegularizationReference U (fun x => normPlus x ^ (-4 : ℝ)) =
      gmcReferenceMeasure.restrict U := by
    rw [logRegularizationReference_restrict_of_subset univ U
      (fun x => normPlus x ^ (-4 : ℝ)) hU.measurableSet (subset_univ _)]
    simp only [logRegularizationReference, Measure.restrict_univ, gmcReferenceMeasure]
  let : IsFiniteMeasure (logRegularizationReference U (fun x => normPlus x ^ (-4 : ℝ))) := by
    rw [href]
    infer_instance
  have hlaw := admissibleLogChaos_limit_vector_law_of_fdd P P U
    (fun x => normPlus x ^ (-4 : ℝ)) 1 1
    (fun ω ε x => Xc ω (z+x) (Real.log (1/ε)) - Xc ω z 0)
    (fun ω ε x => Xc ω x (Real.log (1/ε))) hY hZ γ N A hN hA
    (fun ε _ _ n xs => unpinned_circle_global_fdd P X Xc hX hc z hz
      (fun i => (xs i, Real.log (1/ε)))) f hfc hfU
  apply hlaw.trans
  apply Measure.map_congr
  filter_upwards [hAeq] with ω hω
  funext j
  rw [← hω]
  exact integral_restrict_eq_integral_of_zero_on_compl (M ω) U hU.measurableSet (f j)
    (boundedContinuousFunction_eq_zero_off_tsupport_subset (f j) U (hfU j))


end DOZZ.Proofs
