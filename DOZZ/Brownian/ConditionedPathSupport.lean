/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitFDDMarkov

/-!
# Path support from the conditioned entrance FDDs

The explicit entrance density is supported on the strictly negative half-line at every positive
time. Countably many rational evaluations and continuity then imply that a conditioned path stays
in the closed negative half-line for all times. This argument does not assert that the path cannot
touch zero at an irrational time.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- At a deterministic positive time, the one-time marginal of a negative conditioned path is
strictly negative almost surely. -/
theorem ae_negativeConditionedPath_eval_lt_zero
    {ν : ℝ} {P : Measure BrownianPath}
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    ∀ᵐ p ∂P, p t < 0 := by
  let times : Fin 1 → ℝ≥0 := fun _ => t
  let X : BrownianPath → Fin 1 → ℝ := fun p _ => p t
  let A : Set (Fin 1 → ℝ) := {x | 0 ≤ x 0}
  let ρ : (Fin 1 → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal
    (max 0 (negativeConditionedFDDDensity ν [t] [x 0]))
  have htimes : ∀ i, 0 < (times i : ℝ) := fun _ => ht
  have hmono : StrictMono times := by
    intro i j hij
    have hij' : i = j := Subsingleton.elim _ _
    subst j
    exact False.elim (lt_irrefl i hij)
  have hfdd := hP.2.2.2 1 (by norm_num) times htimes hmono
  have hlaw : P.map X = (volume : Measure (Fin 1 → ℝ)).withDensity ρ := by
    simpa [X, times, ρ, negativeConditionedFDDDensity] using hfdd
  have hA : MeasurableSet A := measurableSet_le measurable_const
    (measurable_pi_apply (0 : Fin 1))
  have hρzero : ∀ x ∈ A, ρ x = 0 := by
    intro x hx
    have hx0 : 0 ≤ x 0 := hx
    simp [ρ, negativeConditionedFDDDensity, conditionedPositiveEntranceDensity,
      not_lt.mpr hx0]
  have hRHS : ((volume : Measure (Fin 1 → ℝ)).withDensity ρ) A = 0 := by
    rw [withDensity_apply ρ hA]
    calc
      ∫⁻ x in A, ρ x ∂(volume : Measure (Fin 1 → ℝ)) =
          ∫⁻ x in A, (fun _ : Fin 1 → ℝ => (0 : ℝ≥0∞)) x
            ∂(volume : Measure (Fin 1 → ℝ)) := by
            apply setLIntegral_congr_fun hA
            intro x hx
            exact hρzero x hx
      _ = 0 := by simp
  have hpre : X ⁻¹' A = {p : BrownianPath | 0 ≤ p t} := by
    ext p
    simp [X, A]
  have hX : Measurable X := measurable_pi_iff.mpr fun _ =>
    ContinuousMap.measurable_eval t
  have hbad : P {p : BrownianPath | 0 ≤ p t} = 0 := by
    calc
      P {p : BrownianPath | 0 ≤ p t} = P (X ⁻¹' A) := by rw [hpre]
      _ = (P.map X) A := (Measure.map_apply hX hA).symm
      _ = 0 := by rw [hlaw]; exact hRHS
  rw [measure_eq_zero_iff_ae_notMem] at hbad
  filter_upwards [hbad] with p hp
  exact lt_of_not_ge (by simpa using hp)

/-- A negative conditioned path is nonpositive at every time, almost surely. The proof uses
strict negativity at each positive rational time and continuity; it allows a possible zero touch at
an irrational time. -/
theorem ae_negativeConditionedPath_nonpos_all_times
    {ν : ℝ} {P : Measure BrownianPath}
    (hP : IsNegativeConditionedBrownianLaw ν P) :
    ∀ᵐ p ∂P, ∀ t : ℝ≥0, p t ≤ 0 := by
  let PosRat := {q : ℚ // 0 < (q : ℝ)}
  have hrat : ∀ᵐ p ∂P, ∀ q : PosRat,
      p ⟨(q : ℝ), q.property.le⟩ < 0 := by
    rw [ae_all_iff]
    intro q
    exact ae_negativeConditionedPath_eval_lt_zero hP
      ⟨(q : ℝ), q.property.le⟩ q.property
  filter_upwards [hrat, hP.2.2.1] with p hpRat hp0
  intro t
  by_cases ht : t = 0
  · subst t
    simp [hp0]
  · have htpos : 0 < (t : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr ht)
    have hpositive : ∀ q : ℚ, ∀ hq : 0 < (q : ℝ),
        0 ≤ (-p) ⟨(q : ℝ), hq.le⟩ := by
      intro q hq
      have hq' := hpRat ⟨q, hq⟩
      exact neg_nonneg.mpr hq'.le
    have hcont := (continuous_path_ge_iff_rational_ge (-p) 0 0 (by norm_num)).2
      (by
        intro q hq
        exact hpositive q hq)
    have hval := hcont t htpos
    exact neg_nonneg.mp hval

end DOZZ.Proofs

end
