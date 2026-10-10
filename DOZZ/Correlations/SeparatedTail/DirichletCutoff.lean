/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.SeparatedTail.CovarianceBound
public import DOZZ.GMC.GaussianInputs
public import DOZZ.GMC.FieldChaosNegativePower
public import Mathlib.Probability.Independence.Integration

/-! Dirichlet circle cutoff masses remain measurable in their own distribution sigma algebras. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Extend the circle field from the unit ball by its central value. This provides a global
measurable Gaussian field without using circles outside the Dirichlet disk. -/
noncomputable def separatedTail_diskPoint (c x : ℂ) : ℂ := by
  classical
  exact if x ∈ ball c 1 then x else c

theorem separatedTail_diskPoint_measurable (c : ℂ) : Measurable (separatedTail_diskPoint c) :=
  Measurable.ite isOpen_ball.measurableSet measurable_id measurable_const

theorem separatedTail_diskPoint_norm_le (c x : ℂ) : ‖separatedTail_diskPoint c x-c‖ ≤ 1 := by
  unfold separatedTail_diskPoint
  split_ifs with h
  · exact (mem_ball_iff_norm.mp h).le
  · simp

theorem separatedTail_dirichletCircle_isCenteredGaussianField
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : Ω → Distr) (Dc : Ω → ℂ → ℝ → ℝ) (c : ℂ)
    (hmD : Measurable (fun ω => fun f : TestFn => D ω f))
    (hm : Measurable[(MeasurableSpace.comap (fun ω => fun f : TestFn => D ω f)
      MeasurableSpace.pi).prod inferInstance] (fun q : Ω × (ℂ × ℝ) => Dc q.1 q.2.1 q.2.2))
    (hg : IsGaussianProcess (fun q : {q : ℂ × ℝ // ‖q.1-c‖+Real.exp (-q.2) < 5/4} =>
      fun ω => Dc ω q.1.1 q.1.2) P)
    (hmean : ∀ x r, ‖x-c‖+Real.exp (-r) < 5/4 → (∫ ω, Dc ω x r ∂P) = 0)
    (r : ℝ) (hr : Real.exp (-r) < 1/4) :
    IsCenteredGaussianField P (fun ω x => Dc ω (separatedTail_diskPoint c x) r) := by
  have hinside (x : ℂ) : ‖separatedTail_diskPoint c x-c‖+Real.exp (-r) < 5/4 := by
    linarith [separatedTail_diskPoint_norm_le c x]
  have hm' : Measurable (fun q : Ω × (ℂ × ℝ) => Dc q.1 q.2.1 q.2.2) :=
    hm.mono (by
      exact sup_le_sup (MeasurableSpace.comap_mono (measurable_iff_comap_le.mp hmD)) le_rfl) le_rfl
  refine ⟨hm'.comp (measurable_fst.prodMk
    ((separatedTail_diskPoint_measurable c).comp measurable_snd |>.prodMk measurable_const)), ?_⟩
  intro n x
  exact centeredJointlyGaussian_of_isGaussianProcess P _
    (hg.comp_right (fun i : Fin n => ⟨(separatedTail_diskPoint c (x i), r), hinside (x i)⟩))
    (fun i => hmean _ _ (hinside _))

/-- A Dirichlet Wick mass is measurable in the raw distribution sigma algebra. Its deterministic
variance correction is spatially measurable in the original probability space. -/
theorem separatedTail_dirichletChaosMass_comap_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (D : Ω → Distr) (Dc : Ω → ℂ → ℝ → ℝ) (c : ℂ)
    (hm : Measurable[(MeasurableSpace.comap (fun ω => fun f : TestFn => D ω f)
      MeasurableSpace.pi).prod inferInstance] (fun q : Ω × (ℂ × ℝ) => Dc q.1 q.2.1 q.2.2))
    (r : ℝ) (hfield : IsCenteredGaussianField P (fun ω x => Dc ω (separatedTail_diskPoint c x) r))
    (ν : Measure ℂ) [SFinite ν] (w : ℂ → ℝ≥0) (hw : Measurable w) (γ : ℝ) :
    Measurable[MeasurableSpace.comap (fun ω => fun f : TestFn => D ω f) MeasurableSpace.pi]
      (fieldChaosMass P (fun ω x => Dc ω (separatedTail_diskPoint c x) r) ν w γ) := by
  have hv := centeredGaussianField_variance_measurable P _ hfield
  have hωx : @Measurable (Ω × ℂ) ℝ
      ((MeasurableSpace.comap (fun ω => fun f : TestFn => D ω f) MeasurableSpace.pi).prod
        inferInstance) _ (fun q => Dc q.1 (separatedTail_diskPoint c q.2) r) :=
    hm.comp (measurable_fst.prodMk
      ((separatedTail_diskPoint_measurable c).comp measurable_snd |>.prodMk measurable_const))
  have hvInt : Measurable (fun x => ∫ ω, Dc ω (separatedTail_diskPoint c x) r ^ 2 ∂P) := by
    simpa only [gaussianVariance, gaussianCovariance, pow_two] using hv
  have hlog : @Measurable (Ω × ℂ) ℝ≥0∞
      ((MeasurableSpace.comap (fun ω => fun f : TestFn => D ω f) MeasurableSpace.pi).prod
        inferInstance) _ (fun q => (w q.2 : ℝ≥0∞) * ENNReal.ofReal
          (Real.exp (γ*Dc q.1 (separatedTail_diskPoint c q.2) r - γ^2/2*
            ∫ ω, Dc ω (separatedTail_diskPoint c q.2) r ^ 2 ∂P))) :=
    (hw.coe_nnreal_ennreal.comp measurable_snd).mul
      (((hωx.const_mul γ).sub ((hvInt.comp measurable_snd).const_mul (γ^2/2))).exp.ennreal_ofReal)
  exact @Measurable.lintegral_prod_right' Ω ℂ
    (MeasurableSpace.comap (fun ω => fun f : TestFn => D ω f) MeasurableSpace.pi)
    inferInstance ν inferInstance _ hlog

/-- Measurability in separate raw distribution sigma algebras preserves independence of the
finite-cutoff Dirichlet masses. -/
theorem separatedTail_indepFun_of_comap_measurable
    {Ω A B C E : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace E] (P : Measure Ω)
    (D2 : Ω → A) (D3 : Ω → B) (W2 : Ω → C) (W3 : Ω → E)
    (hD : IndepFun D2 D3 P)
    (hW2 : Measurable[MeasurableSpace.comap D2 inferInstance] W2)
    (hW3 : Measurable[MeasurableSpace.comap D3 inferInstance] W3) :
    IndepFun W2 W3 P := by
  exact indep_of_indep_of_le hD (measurable_iff_comap_le.mp hW2) (measurable_iff_comap_le.mp hW3)

end DOZZ.Proofs
