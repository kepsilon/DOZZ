/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.WilliamsCutProduct
public import Mathlib.Probability.HasLaw

/-! Random-maximum last-cut ordering on an actual conditioned source process. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

theorem source_last_exit_mono_prod_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν c : ℝ) (hν : 0 < ν) (D : Ω → BrownianPath)
    (hD : IsNegativeConditionedBrownianProcess P D ν) :
    ∀ᵐ q : ℝ × Ω ∂(brownianMaximumReferenceLaw ν).prod P,
      c ≤ q.1 → negativeLastExitTime (D q.2) c ≤ negativeLastExitTime (D q.2) q.1 := by
  let μ := brownianMaximumReferenceLaw ν
  let : IsProbabilityMeasure μ := isProbabilityMeasure_brownianMaximumReferenceLaw hν
  have hDL : HasLaw D (P.map D) P := ⟨hD.1,rfl⟩
  have h₁ : HasLaw (fun q : ℝ × Ω => q.1) μ (μ.prod P) := measurePreserving_fst.hasLaw
  have h₂ := hDL.comp (measurePreserving_snd (μ := μ) (ν := P)).hasLaw
  have hl := (indepFun_iff_hasLaw_prodMk_prod h₁ h₂).mp
    (indepFun_prod₀ measurable_id.aemeasurable hD.1)
  have hp := williams_last_exit_mono_prod_ae ν c hν (P.map D) hD.2
  rw [← hl.map_eq] at hp
  exact ae_of_ae_map hl.aemeasurable hp


end DOZZ.Proofs
