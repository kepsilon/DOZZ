/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.OpenSetScale

/-! Joint affine mass laws, retaining the one common Gaussian for all inner open sets. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Simultaneous affine scaling of every member of a finite family of open sets. The Gaussian
factor is shared by the whole vector; its moment order is the sum of the allocated orders. -/
theorem affine_open_set_vector_law
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {a : ℂ} {c R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hR : 0 < R) (hRsmall : R < 1) (hTsmall : ‖a‖ + c * R < 1)
    (U : Fin m → Set ℂ) (hU : ∀ j, IsOpen (U j))
    (hUR : ∀ j, U j ⊆ Metric.closedBall 0 R) :
    Measure.map (fun ω j => (M ω ((fun y => a + c • y) '' U j)).toReal) P =
      Measure.map (fun p : Ω × ℝ => fun j =>
        c ^ 2 * Real.exp (γ * p.2 - γ ^ 2 / 2 * (-Real.log c)) * (M p.1 (U j)).toReal)
        (P.prod (gaussianReal 0 ⟨-Real.log c,
          neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩)) := by
  have : IsProbabilityMeasure P := hX.1
  let G : Measure ℝ := gaussianReal 0 ⟨-Real.log c,
    neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩
  let s : ℝ → ℝ := fun w => c ^ 2 * Real.exp (γ * w - γ ^ 2 / 2 * (-Real.log c))
  have hs : Measurable s := by dsimp only [s]; fun_prop
  have : IsProbabilityMeasure G := instIsProbabilityMeasureGaussianReal 0 _
  let A : Fin m → Set ℂ := fun j => (fun y => a + c • y) '' U j
  let f : ℕ → Fin m → BoundedContinuousFunction ℂ ℝ :=
    fun n j => openSetAffineApprox (U j) a c n
  let g : ℕ → Fin m → BoundedContinuousFunction ℂ ℝ := fun n j => openSetApprox (U j) n
  have hfs (n : ℕ) (j : Fin m) : tsupport (f n j : ℂ → ℝ) ⊆
      Metric.closedBall a (c * R) :=
    openSetAffineApprox_tsupport_subset hc.ne' Metric.isClosed_closedBall
      (openSetScale_image_subset_closedBall hc a (hUR j)) n
  have hgs (n : ℕ) (j : Fin m) : tsupport (g n j : ℂ → ℝ) ⊆
      Metric.closedBall 0 R :=
    openSetApprox_tsupport_subset Metric.isClosed_closedBall (hUR j) n
  have hf (j : Fin m) := openSetScale_cutoff_tendstoInMeasure P X hX γ M hM
    (z := a) (r := c * R) hTsmall.le (A j) (fun n => f n j) (fun n => hfs n j)
    (fun μ _ => openSetAffineApprox_integral_tendsto (hU j)
      (openSetScale_compl_nonempty (hUR j)) hc.ne' μ)
  have hg (j : Fin m) := openSetScale_cutoff_tendstoInMeasure P X hX γ M hM
    (z := 0) (r := R) (by simpa using hRsmall.le) (U j) (fun n => g n j)
    (fun n => hgs n j) (fun μ _ => openSetApprox_integral_tendsto (hU j)
      (openSetScale_compl_nonempty (hUR j)) μ)
  have hma (j : Fin m) : AEMeasurable (fun ω => (M ω (A j)).toReal) P :=
    ENNReal.measurable_toReal.comp_aemeasurable
      (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM (A j)
        (openSetScale_image_isOpen hc.ne' a (hU j)).measurableSet)
  have hmb (j : Fin m) : AEMeasurable (fun ω => (M ω (U j)).toReal) P :=
    ENNReal.measurable_toReal.comp_aemeasurable
      (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM (U j) (hU j).measurableSet)
  have hsnd : AEMeasurable (fun q : Ω × ℝ => s q.2) (P.prod G) :=
    (hs.comp measurable_snd).aemeasurable
  apply gmc_limit_test_vector_law
    (fun n ω j => ∫ x, f n j x ∂M ω)
    (fun n (q : Ω × ℝ) j => s q.2 * ∫ x, g n j x ∂M q.1)
    (fun ω j => (M ω (A j)).toReal)
    (fun (q : Ω × ℝ) j => s q.2 * (M q.1 (U j)).toReal)
    (fun n => aemeasurable_pi_iff.2 fun j => (hf j).1 n)
    (fun n => aemeasurable_pi_iff.2 fun j => hsnd.mul ((hg j).1 n).comp_fst)
    (aemeasurable_pi_iff.2 hma)
    (aemeasurable_pi_iff.2 fun j => hsnd.mul (hmb j).comp_fst)
  · intro n
    have h := gmc_affine_test_vector_law P X hX γ M hM hc hc1 hR hRsmall hTsmall
      (f n) (fun j x => (openSetApproxFun_bounds (U j) n _).1) (hfs n)
    simpa only [s, f, g, openSetAffineApprox_comp_affine (U _) a hc.ne' n] using h
  · exact fun j => (hf j).2
  · exact fun j => tendstoInMeasure_mul_snd_of_tendstoInMeasure
      (fun n ω => ∫ x, g n j x ∂M ω) (fun ω => (M ω (U j)).toReal) s hs (hg j).2

end DOZZ.Proofs
