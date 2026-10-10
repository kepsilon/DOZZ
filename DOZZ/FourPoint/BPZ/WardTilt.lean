/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardKernel
public import DOZZ.FourPoint.BPZ.Rooting
public import DOZZ.GMC.SharpMoments.TiltCutoff
public import DOZZ.GMC.Construction.GMCVertexTiltInputs
public import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure

/-! # Rooting a joint functional of the cutoff and limit chaos

Tilting by `γ X_r(x)` multiplies the cutoff chaos by `e^{γ² C_r(·, x)}` and the limit chaos by
`e^{γ² G_r(x, ·)}`, where `C_r(y,x) = Λ_r(x - y) + h_r(x) + h_r(y)` is the covariance of two
circle averages and `G_r(x,y) = -log max(e^{-r}, |x - y|) + h_r(x) + log |y|₊` is the circle
average of the Green kernel. Integrating a functional against the cutoff chaos therefore roots it
at the integration point. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The density of the cutoff chaos after rooting at `x`. -/
noncomputable def bpzCutRootDensity (γ r : ℝ) (x y : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (γ ^ 2 * (bpzLam r (x - y) + bpzPin r x + bpzPin r y)))

/-- The density of the limit chaos after rooting at `x` by a circle average. -/
noncomputable def bpzLimRootDensity (γ r : ℝ) (x y : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (γ ^ 2 * (bpzTruncLog r (x - y) + bpzPin r x +
    Real.log (normPlus y))))

theorem bpz_gaussianCovariance_const_mul_right (P : Measure Ω) (Y Z : Ω → ℝ) (c : ℝ) :
    gaussianCovariance P Y (fun ω => c * Z ω) = c * gaussianCovariance P Y Z := by
  unfold gaussianCovariance
  rw [← integral_const_mul]
  congr 1
  funext ω
  ring

/-- The circle-average tilt of a joint functional of the cutoff and limit chaos. -/
theorem bpz_cutoff_root_tilt (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (r : ℝ) (x : ℂ)
    (H : Measure ℂ → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : Measure ℂ × Measure ℂ => H q.1 q.2)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P)) *
        H (regularizedGMC P Xc γ r ω) (M ω) ∂P =
      ∫⁻ ω, H ((regularizedGMC P Xc γ r ω).withDensity (bpzCutRootDensity γ r x))
        ((M ω).withDensity (bpzLimRootDensity γ r x)) ∂P := by
  set L : Ω → ℝ := fun ω => ∑ k : Fin 1, ![γ] k * Xc ω (![x] k) r with hLdef
  have hLeq : L = fun ω => γ * Xc ω x r := by
    funext ω
    simp [hLdef]
  have hL := circleAverage_sum_isGaussianL2Limit P X hX Xc hXc ![γ] ![x] r
  obtain ⟨c, hcx, hc⟩ := circleAverage_sum_covariance_uniform P X hX Xc hXc ![γ] ![x] r
  have hH' : Measurable (fun q : (TestFn → ℝ) × Measure ℂ × Measure ℂ => H q.2.1 q.2.2) :=
    hH.comp (measurable_fst.comp measurable_snd |>.prodMk (measurable_snd.comp measurable_snd))
  have htilt := equatorGFF_GMC_tilt_cutoff P X hX γ hγ hγ2 M hM Xc hXc L hL c hc r
    (fun _ m₁ m₂ => H m₁ m₂) hH'
  rw [hLeq] at htilt
  have hvar : gaussianVariance P (fun ω => γ * Xc ω x r) = γ ^ 2 * ∫ ω', Xc ω' x r ^ 2 ∂P := by
    unfold gaussianVariance gaussianCovariance
    rw [← integral_const_mul]
    congr 1
    funext ω
    ring
  have hlhs : ∀ ω, Real.exp (γ * Xc ω x r - gaussianVariance P (fun ω => γ * Xc ω x r) / 2) =
      Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P) := by
    intro ω
    rw [hvar]
    ring_nf
  simp_rw [hlhs] at htilt
  rw [htilt]
  apply lintegral_congr
  intro ω
  congr 2
  · funext y
    rw [bpzCutRootDensity, bpz_gaussianCovariance_const_mul_right,
      bpz_circle_covariance P X hX Xc hXc y x r, ← bpzLam_neg r (y - x), neg_sub]
    congr 2
    ring
  · funext y
    rw [bpzLimRootDensity, hcx y]
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero]
    rw [show (∫ v, gffKernel y v ∂circleMeasure x r) = ∫ v, gffKernel v y ∂circleMeasure x r by
      simp_rw [gffKernel_comm y], bpz_integral_gffKernel_circle_left x y r]
    congr 2
    ring

/-- The pointwise variance of the circle-average field is measurable. -/
theorem measurable_bpz_circle_variance (P : Measure Ω) [SFinite P] (Xc : Ω → ℂ → ℝ → ℝ)
    (hXc : ∀ r : ℝ, Measurable (fun p : Ω × ℂ => Xc p.1 p.2 r)) (r : ℝ) :
    Measurable (fun x : ℂ => ∫ ω, Xc ω x r ^ 2 ∂P) := by
  have h : Measurable (fun p : ℂ × Ω => Xc p.2 p.1 r ^ 2) :=
    ((hXc r).comp measurable_swap).pow_const 2
  exact (StronglyMeasurable.integral_prod_right' (ν := P) h.stronglyMeasurable).measurable

/-- Integrating a joint functional against the cutoff chaos roots it at the integration point.
Only joint measurability along the two random measures and measurability in the measures at each
fixed point are needed. -/
theorem bpz_cutoff_deroot (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (r : ℝ)
    (H : ℂ → Measure ℂ → Measure ℂ → ℝ≥0∞)
    (hHm : Measurable (fun p : Ω × ℂ => H p.2 (regularizedGMC P Xc γ r p.1) (M p.1)))
    (hHx : ∀ x, Measurable (fun q : Measure ℂ × Measure ℂ => H x q.1 q.2)) :
    ∫⁻ ω, ∫⁻ x, H x (regularizedGMC P Xc γ r ω) (M ω) ∂regularizedGMC P Xc γ r ω ∂P =
      ∫⁻ x, ENNReal.ofReal (normPlus x ^ (-4 : ℝ)) *
        ∫⁻ ω, H x ((regularizedGMC P Xc γ r ω).withDensity (bpzCutRootDensity γ r x))
          ((M ω).withDensity (bpzLimRootDensity γ r x)) ∂P := by
  let _ : IsProbabilityMeasure P := hX.1
  set V : ℂ → ℝ := fun x => ∫ ω, Xc ω x r ^ 2 ∂P with hV
  have hVm : Measurable V := measurable_bpz_circle_variance P Xc hXc.1 r
  set dens : Ω → ℂ → ℝ≥0∞ := fun ω x => ENNReal.ofReal
    (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * V x) * normPlus x ^ (-4 : ℝ)) with hdens
  have hdensm : Measurable (fun p : Ω × ℂ => dens p.1 p.2) := by
    refine ENNReal.measurable_ofReal.comp (Measurable.mul ?_ ?_)
    · exact Real.measurable_exp.comp (((hXc.1 r).const_mul γ).sub
        ((hVm.comp measurable_snd).const_mul _))
    · exact (bpz_measurable_normPlus.comp measurable_snd).pow_const _
  have hstep1 : ∀ ω, ∫⁻ x, H x (regularizedGMC P Xc γ r ω) (M ω) ∂regularizedGMC P Xc γ r ω =
      ∫⁻ x, dens ω x * H x (regularizedGMC P Xc γ r ω) (M ω) := by
    intro ω
    have hd : Measurable (dens ω) :=
      hdensm.comp (f := fun x : ℂ => (ω, x)) (measurable_const.prodMk measurable_id)
    have hg : Measurable fun x => H x (regularizedGMC P Xc γ r ω) (M ω) :=
      hHm.comp (f := fun x : ℂ => (ω, x)) (measurable_const.prodMk measurable_id)
    change ∫⁻ x, H x (regularizedGMC P Xc γ r ω) (M ω) ∂(volume.withDensity (dens ω)) = _
    rw [lintegral_withDensity_eq_lintegral_mul _ hd hg]
    rfl
  simp_rw [hstep1]
  rw [lintegral_lintegral_swap ((hdensm.mul hHm).aemeasurable)]
  apply lintegral_congr
  intro x
  have hsplit : ∀ ω, dens ω x * H x (regularizedGMC P Xc γ r ω) (M ω) =
      ENNReal.ofReal (normPlus x ^ (-4 : ℝ)) *
        (ENNReal.ofReal (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P)) *
          H x (regularizedGMC P Xc γ r ω) (M ω)) := by
    intro ω
    show ENNReal.ofReal (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * V x) * normPlus x ^ (-4 : ℝ)) *
      H x (regularizedGMC P Xc γ r ω) (M ω) = _
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    ring
  simp_rw [hsplit]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  exact bpz_cutoff_root_tilt P X hX hγ hγ2 M hM Xc hXc r x (H x) (hHx x)

/-- A measurable family of finite measures integrates jointly measurable integrands to a jointly
measurable function. -/
theorem bpz_measurable_lintegral_finite_family {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (m : α → Measure ℂ) (hm : Measurable m)
    (hfin : ∀ a, IsFiniteMeasure (m a)) (g : β → ℂ → ℝ≥0∞)
    (hg : Measurable (Function.uncurry g)) :
    Measurable (fun p : α × β => ∫⁻ y, g p.2 y ∂m p.1) := by
  set c : α → ℝ≥0∞ := fun a => m a Set.univ + 1 with hc
  have hcm : Measurable c :=
    (Measure.measurable_coe MeasurableSet.univ |>.comp hm).add measurable_const
  have hc0 : ∀ a, c a ≠ 0 := fun a => by simp [hc]
  have hctop : ∀ a, c a ≠ ⊤ := fun a => by
    simp only [hc, ne_eq, ENNReal.add_eq_top, ENNReal.one_ne_top, or_false]
    exact measure_ne_top _ _
  have hnm : Measurable (fun p : α × β => (c p.1)⁻¹ • m p.1) := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ((hcm.comp measurable_fst).inv).mul
      ((Measure.measurable_coe hs).comp (hm.comp measurable_fst))
  let κ : ProbabilityTheory.Kernel (α × β) ℂ := ⟨fun p => (c p.1)⁻¹ • m p.1, hnm⟩
  have hκfin : ProbabilityTheory.IsFiniteKernel κ := by
    refine ⟨⟨1, ENNReal.one_lt_top, fun p => ?_⟩⟩
    change ((c p.1)⁻¹ • m p.1) Set.univ ≤ 1
    rw [Measure.smul_apply, smul_eq_mul]
    calc (c p.1)⁻¹ * m p.1 Set.univ ≤ (c p.1)⁻¹ * c p.1 := by
          gcongr
          simp [hc]
      _ = 1 := ENNReal.inv_mul_cancel (hc0 _) (hctop _)
  have hint : Measurable fun p : α × β => ∫⁻ y, g p.2 y ∂κ p :=
    Measurable.lintegral_kernel_prod_right (κ := κ) (f := fun p y => g p.2 y)
      (hg.comp (measurable_fst.snd.prodMk measurable_snd))
  have heq : (fun p : α × β => ∫⁻ y, g p.2 y ∂m p.1) =
      fun p => c p.1 * ∫⁻ y, g p.2 y ∂κ p := by
    funext p
    change _ = c p.1 * ∫⁻ y, g p.2 y ∂((c p.1)⁻¹ • m p.1)
    rw [lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel (hc0 _) (hctop _), one_mul]
  rw [heq]
  exact (hcm.comp measurable_fst).mul hint

end DOZZ.Proofs
