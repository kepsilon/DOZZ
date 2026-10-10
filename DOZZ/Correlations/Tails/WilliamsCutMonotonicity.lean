/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitShiftLaw
public import DOZZ.Brownian.ConditionedPathSupport
public import DOZZ.Brownian.Reflection.LastCut

/-! The last-cut ordering required by the lower Williams tail estimate. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- A path that stays below `-d` after its last exit cannot subsequently hit a higher level. -/
theorem last_exit_le_of_post_nonpos (p : BrownianPath) (c d : ℝ) (hcd : c ≤ d)
    (hp : ∀ t : ℝ≥0, negativeConditionedPostLastExitPath d p t ≤ 0) :
    negativeLastExitTime p c ≤ negativeLastExitTime p d := by
  rcases lt_or_eq_of_le hcd with hlt | heq
  · have hhit (u : ℝ≥0) (hu : p u = -c) : u ≤ negativeLastExitTime p d := by
      by_contra hnot
      have hu' : negativeLastExitTime p d < u := lt_of_not_ge hnot
      have h := hp (u-negativeLastExitTime p d)
      change p (negativeLastExitTime p d+(u-negativeLastExitTime p d))+d ≤ 0 at h
      rw [add_tsub_cancel_of_le hu'.le, hu] at h
      linarith
    apply (negativeLastExitTime_le_iff_no_future_visit p c (negativeLastExitTime p d)
      ⟨negativeLastExitTime p d, hhit⟩).mpr
    intro u hu huv
    exact (not_lt_of_ge (hhit u huv)) hu
  · rw [heq]

/-- For each fixed pair of levels the conditioned last exits are ordered almost surely.
Only the proved post-last-exit law and path support are consumed. -/
theorem conditioned_last_exit_mono_ae (ν c d : ℝ) (hν : 0 < ν)
    (hd : 0 < d) (hcd : c ≤ d) (P : Measure BrownianPath)
    (hP : IsNegativeConditionedBrownianLaw ν P) :
    ∀ᵐ p ∂P, negativeLastExitTime p c ≤ negativeLastExitTime p d := by
  have hlaw := negativeConditioned_postLastExit_law ν d hν hd P hP
  have hclosed : IsClosed {p : BrownianPath | ∀ t : ℝ≥0, p t ≤ 0} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro t
    exact isClosed_le (by fun_prop) continuous_const
  have hp : ∀ᵐ p ∂P.map (negativeConditionedPostLastExitPath d), ∀ t : ℝ≥0, p t ≤ 0 := by
    rw [hlaw.2]
    exact ae_negativeConditionedPath_nonpos_all_times hP
  have hs := (ae_map_iff hlaw.1 hclosed.measurableSet).mp hp
  filter_upwards [hs] with p hp
  exact last_exit_le_of_post_nonpos p c d hcd hp

/-- Last-exit ordering implies ordering of the retained reflection masses. -/
theorem reflection_cut_mass_le_of_last_exit_le
    {Ω : Type*} (γ c d : ℝ) (B : Ω → BrownianPath × BrownianPath)
    (Z : Ω → Measure ℝ) (ω : Ω)
    (hcd : negativeLastExitTime (B ω).2 c ≤ negativeLastExitTime (B ω).2 d) :
    twoSidedReflectionCutMass γ c B Z ω ≤ twoSidedReflectionCutMass γ d B Z ω := by
  have ht : (negativeLastExitTime (B ω).2 c : ℝ) ≤
      (negativeLastExitTime (B ω).2 d : ℝ) := hcd
  unfold twoSidedReflectionCutMass
  apply lintegral_mono
  intro s
  beta_reduce
  split_ifs with hc hd
  · exact le_rfl
  · exact False.elim (hd (by linarith))
  · exact zero_le
  · exact le_rfl


end DOZZ.Proofs
