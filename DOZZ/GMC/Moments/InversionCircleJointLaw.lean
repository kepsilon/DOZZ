/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionCircleAdmissible

/-! Joint Gaussianity and ordinary finite-dimensional laws of coupled inversion circles. -/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology Distributions

namespace DOZZ.Proofs

/-- Any family of coupled inverted-test limits is jointly Gaussian with the source circle
family. Thus the mixed law required by regularization uniqueness uses the original coupling. -/
theorem inversionCircle_source_jointly_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m : ℕ}
    (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (q : Fin m → Bool × ℂ × ℝ) (Z : Fin m → Ω → ℝ)
    (hmem : ∀ i, MemLp (Z i) 2 P)
    (f : Fin m → ℕ → TestFn)
    (hf : ∀ i n, tsupport (f i n : ℂ → ℝ) ⊆ inversionChart)
    (hlim : ∀ i, Tendsto (fun n => eLpNorm (fun ω =>
      X ω (inversionTest (f i n) (hf i n)) - Z i ω) 2 P) atTop (𝓝 0)) :
    IsCenteredJointlyGaussian P (fun ω i =>
      if (q i).1 then Xc ω (q i).2.1 (q i).2.2 else Z i ω) := by
  let : IsProbabilityMeasure P := hX.1
  have hex i := exists_testFn_circleEnergyGap_tendsto_zero (q i).2.1 (q i).2.2
  choose g _hgs _hga hgap using hex
  let F : Fin m → ℕ → TestFn := fun i n =>
    if (q i).1 then g i n else inversionTest (f i n) (hf i n)
  let V : Fin m → Ω → ℝ := fun i ω =>
    if (q i).1 then Xc ω (q i).2.1 (q i).2.2 else Z i ω
  have hv : ∀ i, MemLp (V i) 2 P := by
    intro i
    dsimp [V]
    split
    · exact hXc.2.1 _ _
    · exact hmem i
  have hl i : Tendsto (fun n => eLpNorm (fun ω => X ω (F i n) - V i ω) 2 P)
      atTop (𝓝 0) := by
    dsimp [F, V]
    split
    · exact hXc.2.2 _ _ (g i) (hgap i)
    · exact hlim i
  have hp : IsGaussianProcess V P := by
    apply isGaussianProcess_of_eLpNorm_sub (fun n i ω => X ω (F i n)) V
    · intro n
      exact equatorGFF_test_family_isGaussianProcess X hX (fun i => F i n)
    · exact hv
    · exact hl
  exact centeredJointlyGaussian_of_isGaussianProcess P V hp (fun i =>
    integral_eq_zero_of_eLpNorm_sub
      (fun n => equatorGFF_test_memLp X hX (F i n)) (hv i)
      (fun n => equatorGFF_test_integral X hX (F i n)) (hl i))

/-- The measurable transformed circles have the ordinary circle law on every finite family,
with no equality assertion for the two source cutoff profiles at a fixed scale. -/
theorem inversionCircle_fdd_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {m : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (P' : Measure Ω') (X' : Ω' → Distr) (hX' : IsEquatorGFF P' X')
    (Xc' : Ω' → ℂ → ℝ → ℝ) (hXc' : IsCircleAverage P' X' Xc')
    (q : Fin m → ℂ × ℝ) (Z : Fin m → Ω → ℝ)
    (hmem : ∀ i, MemLp (Z i) 2 P)
    (f : Fin m → ℕ → TestFn)
    (hf : ∀ i n, tsupport (f i n : ℂ → ℝ) ⊆ inversionChart)
    (hgap : ∀ i, Tendsto (fun n => circleEnergyGap (q i).1 (q i).2 (f i n))
      atTop (𝓝 0))
    (hlim : ∀ i, Tendsto (fun n => eLpNorm (fun ω =>
      X ω (inversionTest (f i n) (hf i n)) - Z i ω) 2 P) atTop (𝓝 0)) :
    P.map (fun ω i => Z i ω) = P'.map (fun ω i => Xc' ω (q i).1 (q i).2) := by
  let : IsProbabilityMeasure P := hX.1
  let : IsProbabilityMeasure P' := hX'.1
  apply gmc_limit_test_vector_law
    (fun n ω i => X ω (inversionTest (f i n) (hf i n)))
    (fun n ω i => X' ω (f i n)) (fun ω i => Z i ω)
    (fun ω i => Xc' ω (q i).1 (q i).2)
  · intro n
    exact (measurable_pi_iff.mpr fun i => (hX.2 _).1).aemeasurable
  · intro n
    exact (measurable_pi_iff.mpr fun i => (hX'.2 _).1).aemeasurable
  · exact AEMeasurable.of_eval (fun i => (hmem i).aemeasurable)
  · exact AEMeasurable.of_eval (fun i => (hXc'.2.1 _ _).aemeasurable)
  · intro n
    exact equatorGFF_inversion_local_test_fdd_law P X hX P' X' hX'
      (fun i => f i n) (fun i => hf i n)
  · intro i
    exact tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (hlim i)
  · intro i
    exact tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
      (hXc'.2.2 _ _ (f i) (hgap i))

end DOZZ.Proofs
