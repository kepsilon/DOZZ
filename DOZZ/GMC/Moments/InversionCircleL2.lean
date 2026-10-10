/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionCovariance
public import DOZZ.GMC.Moments.InversionPuncturedApproximation
public import DOZZ.GMC.Construction.CircleEnergyGapPositivity
public import DOZZ.GMC.Moments.InversionFieldLaw
public import DOZZ.GMC.Moments.ChaosLawFDDLimit
public import DOZZ.Statements.Defs.IsCircleAverage

/-! Actual random L² limits of circle tests transported through inversion. -/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology Distributions ENNReal

namespace DOZZ.Proofs

/-- Jacobian transport preserves the random L² distance of compact tests in the punctured chart.
-/
theorem equatorGFF_inversion_testL2_dist
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (f g : TestFn)
    (hf : tsupport (f : ℂ → ℝ) ⊆ inversionChart)
    (hg : tsupport (g : ℂ → ℝ) ⊆ inversionChart) :
    dist ((equatorGFF_test_memLp X hX (inversionTest f hf)).toLp
      (fun ω => X ω (inversionTest f hf)))
      ((equatorGFF_test_memLp X hX (inversionTest g hg)).toLp
        (fun ω => X ω (inversionTest g hg))) =
      dist ((equatorGFF_test_memLp X hX f).toLp (fun ω => X ω f))
        ((equatorGFF_test_memLp X hX g).toLp (fun ω => X ω g)) := by
  rw [dist_eq_norm, dist_eq_norm]
  have hi := equatorGFF_testL2_sub_norm_sq X hX (inversionTest f hf) (inversionTest g hg)
  have ho := equatorGFF_testL2_sub_norm_sq X hX f g
  rw [gffCov_sub_self, gffCov_inversionTest, gffCov_inversionTest,
    gffCov_inversionTest] at hi
  rw [gffCov_sub_self] at ho
  nlinarith [norm_nonneg
    ((equatorGFF_test_memLp X hX (inversionTest f hf)).toLp
      (fun ω => X ω (inversionTest f hf)) -
      (equatorGFF_test_memLp X hX (inversionTest g hg)).toLp
        (fun ω => X ω (inversionTest g hg))),
    norm_nonneg ((equatorGFF_test_memLp X hX f).toLp (fun ω => X ω f) -
      (equatorGFF_test_memLp X hX g).toLp (fun ω => X ω g))]


/-- Every circle has an actual L² limit of inverted local test evaluations
on the original field's probability space. -/
theorem exists_equatorGFF_inversion_circle_test_L2_limit_all
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (x : ℂ) (r : ℝ)
    :
    ∃ f : ℕ → TestFn, ∃ hf : ∀ n, tsupport (f n : ℂ → ℝ) ⊆ inversionChart,
      ∃ W : Lp ℝ 2 P,
        Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 0) ∧
        Tendsto (fun n => (equatorGFF_test_memLp X hX
          (inversionTest (f n) (hf n))).toLp
            (fun ω => X ω (inversionTest (f n) (hf n)))) atTop (𝓝 W) := by
  let : IsProbabilityMeasure P := hX.1
  obtain ⟨f, hf, hgap⟩ := exists_testFn_circleEnergyGap_punctured x r
  let U : ℕ → Lp ℝ 2 P := fun n =>
    (equatorGFF_test_memLp X hX (inversionTest (f n) (hf n))).toLp
      (fun ω => X ω (inversionTest (f n) (hf n)))
  have hC := equatorGFF_testL2_cauchy_of_circleEnergyGap X hX x r f hgap
  have hCU : CauchySeq U := by
    rw [Metric.cauchySeq_iff] at hC ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    change dist
      ((equatorGFF_test_memLp X hX (inversionTest (f m) (hf m))).toLp _)
      ((equatorGFF_test_memLp X hX (inversionTest (f n) (hf n))).toLp _) < ε
    rw [equatorGFF_inversion_testL2_dist X hX]
    exact hN m hm n hn
  obtain ⟨W, hW⟩ := cauchySeq_tendsto_of_complete hCU
  exact ⟨f, hf, W, hgap, hW⟩


/-- The coupled inverted circle limit is independent of its chart-supported approximants. -/
theorem equatorGFF_inversion_testL2_tendsto_to_circle_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (x : ℂ) (r : ℝ)
    (f₀ : ℕ → TestFn) (hgap₀ : Tendsto (fun n => circleEnergyGap x r (f₀ n)) atTop (𝓝 0))
    (hf₀ : ∀ n, tsupport (f₀ n : ℂ → ℝ) ⊆ inversionChart)
    (W : Lp ℝ 2 P)
    (hW : Tendsto (fun n => (equatorGFF_test_memLp X hX (inversionTest (f₀ n) (hf₀ n))).toLp
      (fun ω => X ω (inversionTest (f₀ n) (hf₀ n)))) atTop (𝓝 W))
    (f : ℕ → TestFn) (hgap : Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 0))
    (hf : ∀ n, tsupport (f n : ℂ → ℝ) ⊆ inversionChart) :
    Tendsto (fun n => (equatorGFF_test_memLp X hX (inversionTest (f n) (hf n))).toLp
      (fun ω => X ω (inversionTest (f n) (hf n)))) atTop (𝓝 W) := by
  let U n := (equatorGFF_test_memLp X hX (inversionTest (f n) (hf n))).toLp (fun ω => X ω (inversionTest (f n) (hf n)))
  let V n := (equatorGFF_test_memLp X hX (inversionTest (f₀ n) (hf₀ n))).toLp (fun ω => X ω (inversionTest (f₀ n) (hf₀ n)))
  rw [Metric.tendsto_nhds]
  intro ε hε
  let η := ε / 4
  have hη : 0 < η := by dsimp [η]; positivity
  have hδ : 0 < η ^ 2 / 8 := by positivity
  have hq0 : ∀ᶠ m in atTop, circleEnergyGap x r (f₀ m) < η ^ 2 / 8 :=
    hgap₀.eventually (gt_mem_nhds hδ)
  have hnear : ∀ᶠ m in atTop, dist (V m) W < ε / 2 := by
    exact hW.eventually (Metric.ball_mem_nhds W (by positivity))
  obtain ⟨m, hm⟩ := (hq0.and hnear).exists
  have hq : ∀ᶠ n in atTop, circleEnergyGap x r (f n) < η ^ 2 / 8 :=
    hgap.eventually (gt_mem_nhds hδ)
  filter_upwards [hq] with n hqn
  have hnorm : dist (U n) (V m) < η := by
    dsimp [U, V]
    rw [equatorGFF_inversion_testL2_dist X hX, dist_eq_norm]
    have heq := equatorGFF_testL2_sub_norm_sq X hX (f n) (f₀ m)
    have hbound := gffCov_sub_le_circleEnergyGaps x r (f n) (f₀ m)
    have hqm := hm.1
    have hnon := circleEnergyGap_nonneg x r (f n)
    have hnon0 := circleEnergyGap_nonneg x r (f₀ m)
    have hn0 := norm_nonneg
      ((equatorGFF_test_memLp X hX (f n)).toLp (fun ω => X ω (f n)) -
        (equatorGFF_test_memLp X hX (f₀ m)).toLp (fun ω => X ω (f₀ m)))
    nlinarith
  have htriangle : dist (U n) W ≤ dist (U n) (V m) + dist (V m) W :=
    dist_triangle _ _ _
  calc
    dist (U n) W ≤ dist (U n) (V m) + dist (V m) W := htriangle
    _ < ε := by dsimp [η] at hnorm; linarith [hnorm, hm.2]


end DOZZ.Proofs
