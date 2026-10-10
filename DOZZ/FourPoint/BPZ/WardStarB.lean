/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardStar

/-! # The rooted moment of the cutoff Ward data

For the cutoff Ward data, the rooted moment `Ψ(x) = E[J_x^{-q}]` has a line derivative at every
point of the support of the test function, given by `E[-q J_x^{-q-1} S_x]` with the scalar root
derivative `S_x`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]
variable {γ q r δ : ℝ} {ρ kt k₂ φ : ℂ → ℝ} {D : Set ℂ}
variable {P : Measure Ω} {X : Ω → Distr} {M : Ω → Measure ℂ} {Xc : Ω → ℂ → ℝ → ℝ}

/-- The cutoff part of the data is almost surely integrable against the cutoff chaos. -/
theorem bpzWard_cut_integrable (hd : BPZWardData γ q r δ ρ kt k₂ φ D)
    (hp : BPZWardProb P X γ M Xc ρ k₂ D) :
    ∀ᵐ ω ∂P, Integrable (fun y => ρ y * bpzWardCutWeight γ q r kt y *
      Real.exp (γ ^ 2 * bpzPin r y)) (regularizedGMC P Xc γ r ω) := by
  obtain ⟨B, hB0, hB⟩ := bpzWardCutWeight_bdd hd
  filter_upwards [regularizedGMC_finite_ae P X hp.hX Xc hp.hXc γ r] with ω hfin
  refine Integrable.of_bound ?_ B (Eventually.of_forall fun y => ?_)
  · exact ((hd.ρ_meas.mul (measurable_bpzWardCutWeight hd)).mul
      (Real.measurable_exp.comp ((continuous_bpzPin r).measurable.const_mul _))).aestronglyMeasurable
  · have hk := bpzWardCutWeight_nonneg hd y
    have hρ0 := hd.ρ_nonneg y
    have hρ1 := hd.ρ_le_one y
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    by_cases hy : ρ y = 0
    · rw [hy]; simp [hB0]
    · have h := hB y hy
      calc ρ y * bpzWardCutWeight γ q r kt y * Real.exp (γ ^ 2 * bpzPin r y)
          = ρ y * (bpzWardCutWeight γ q r kt y * Real.exp (γ ^ 2 * bpzPin r y)) := by ring
        _ ≤ 1 * B := mul_le_mul hρ1 h (by positivity) zero_le_one
        _ = B := one_mul B

/-- The cutoff chaos has no atoms. -/
theorem regularizedGMC_singleton (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ) (γ r : ℝ) (ω : Ω)
    (x : ℂ) : regularizedGMC P Xc γ r ω {x} = 0 :=
  withDensity_absolutelyContinuous _ _ (measure_singleton x)

/-- The rooted moment has a line derivative on the support of the test function. -/
theorem bpzWard_hasLineDerivAt_Psi (hd : BPZWardData γ q r δ ρ kt k₂ φ D)
    (hp : BPZWardProb P X γ M Xc ρ k₂ D) {x₀ : ℂ} (hx₀ : x₀ ∈ tsupport φ) (v : ℂ) :
    HasLineDerivAt ℝ (fun x => ∫ ω, bpzRootedMixedReal γ r ρ (bpzWardCutWeight γ q r kt) k₂ x
        (regularizedGMC P Xc γ r ω) (M ω) ^ (-q) ∂P)
      (∫ ω, -q * bpzRootedMixedReal γ r ρ (bpzWardCutWeight γ q r kt) k₂ x₀
          (regularizedGMC P Xc γ r ω) (M ω) ^ (-q - 1) *
        bpzRootedMixedDerivApply γ r ρ (bpzWardCutWeight γ q r kt) k₂ x₀ v
          (regularizedGMC P Xc γ r ω) (M ω) ∂P) x₀ v := by
  set k₁ := bpzWardCutWeight γ q r kt with hk₁def
  have hk₁m : Measurable k₁ := measurable_bpzWardCutWeight hd
  have hk₁0 : ∀ y, 0 ≤ k₁ y := bpzWardCutWeight_nonneg hd
  have hsep := hd.sep x₀ hx₀
  have hq0 : 0 ≤ q := le_trans zero_le_one hd.q_ge
  have hI₁ := bpzWard_cut_integrable hd hp
  have hI₂ := hp.k₂_int
  have hJm := measurable_bpzWard_J (γ := γ) (r := r) P X hp.hX M hp.hMm hp.hM.1 Xc hp.hXc
    hd.ρ_meas hk₁m hd.k₂_meas
  have hSm := measurable_bpzWard_S (γ := γ) (r := r) P X hp.hX M hp.hMm hp.hM.1 Xc hp.hXc
    hd.ρ_meas hk₁m hd.k₂_meas v
  obtain ⟨c, hc, hlow⟩ := bpzWard_J_lower (r := r) hd k₁ hk₁0 ‖x₀‖
  have hlowω : ∀ᵐ ω ∂P, c * (M ω D).toReal ≤
      bpzRootedMixedReal γ r ρ k₁ k₂ x₀ (regularizedGMC P Xc γ r ω) (M ω) := by
    filter_upwards [hI₂] with ω hω
    exact hlow _ _ x₀ le_rfl (integrable_bpz_lim_part hd.ρ_meas hd.k₂_meas hd.ρ_le_one
      hd.k₂_nonneg hω hd.δ_pos hd.δ_r hsep (Metric.mem_ball_self hd.δ_pos))
  have hpos : ∀ᵐ ω ∂P, 0 < bpzRootedMixedReal γ r ρ k₁ k₂ x₀ (regularizedGMC P Xc γ r ω) (M ω) := by
    filter_upwards [hlowω, bpzWard_far_mass_pos hp hd.D_meas] with ω h1 h2
    exact lt_of_lt_of_le (mul_pos hc h2) h1
  have hmeas : ∀ t : ℝ, AEStronglyMeasurable (fun ω => bpzRootedMixedReal γ r ρ k₁ k₂
      (x₀ + t • v) (regularizedGMC P Xc γ r ω) (M ω)) P :=
    fun t => (hJm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hDeq : (fun ω => bpzRootedMixedDeriv γ r ρ k₁ k₂ x₀ (regularizedGMC P Xc γ r ω) (M ω) v)
      =ᵐ[P] fun ω => bpzRootedMixedDerivApply γ r ρ k₁ k₂ x₀ v (regularizedGMC P Xc γ r ω)
        (M ω) := by
    filter_upwards [hI₁, hI₂] with ω h1 h2
    exact bpzRootedMixedDeriv_apply hd.ρ_meas hk₁m hd.k₂_meas hd.ρ_nonneg hd.ρ_le_one hk₁0
      hd.k₂_nonneg h1 h2 hd.δ_pos hd.δ_r hsep v
  have hmeasD : AEStronglyMeasurable
      (fun ω => bpzRootedMixedDeriv γ r ρ k₁ k₂ x₀ (regularizedGMC P Xc γ r ω) (M ω) v) P :=
    ((hSm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).congr hDeq.symm
  have hint := bpzWard_integrable_rpow_neg hp hd.D_meas (hmeas 0 |>.congr (by simp)) hc
    hlowω hq0
  have hderiv := hasDerivAt_bpz_rooted_moment (P := P) (γ := γ) (r := r) (δ := δ) (q := q)
    (m₁ := fun ω => regularizedGMC P Xc γ r ω) (m₂ := M) (x₀ := x₀) (v := v)
    hd.ρ_meas hk₁m hd.k₂_meas hd.ρ_nonneg hd.ρ_le_one hk₁0 hd.k₂_nonneg hq0 hd.δ_pos hd.δ_r
    hsep hI₁ hI₂ (Eventually.of_forall fun ω => regularizedGMC_singleton P Xc γ r ω x₀)
    hpos hmeas hmeasD hint
  have hcongr : (fun ω => -q * bpzRootedMixedReal γ r ρ k₁ k₂ x₀ (regularizedGMC P Xc γ r ω)
      (M ω) ^ (-q - 1) * bpzRootedMixedDeriv γ r ρ k₁ k₂ x₀ (regularizedGMC P Xc γ r ω) (M ω) v)
      =ᵐ[P] fun ω => -q * bpzRootedMixedReal γ r ρ k₁ k₂ x₀ (regularizedGMC P Xc γ r ω)
        (M ω) ^ (-q - 1) * bpzRootedMixedDerivApply γ r ρ k₁ k₂ x₀ v
          (regularizedGMC P Xc γ r ω) (M ω) := by
    filter_upwards [hDeq] with ω hω
    rw [hω]
  rw [integral_congr_ae hcongr] at hderiv
  exact hderiv

/-- A pointwise bound by a multiple of an integrable nonnegative weight bounds the lintegral. -/
theorem bpz_lintegral_ofReal_abs_le {m : Measure ℂ} {F w : ℂ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hw : Integrable w m) (hw0 : ∀ y, 0 ≤ w y) (hF : ∀ y, |F y| ≤ C * w y) :
    ∫⁻ y, ENNReal.ofReal |F y| ∂m ≤ ENNReal.ofReal (C * ∫ y, w y ∂m) := by
  calc ∫⁻ y, ENNReal.ofReal |F y| ∂m ≤ ∫⁻ y, ENNReal.ofReal (C * w y) ∂m :=
        lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hF y)
    _ = ENNReal.ofReal (∫ y, C * w y ∂m) :=
        (ofReal_integral_eq_lintegral_ofReal (hw.const_mul C)
          (Eventually.of_forall fun y => mul_nonneg hC (hw0 y))).symm
    _ = ENNReal.ofReal (C * ∫ y, w y ∂m) := by rw [integral_const_mul]

/-- The left test weight vanishes off the support of the test function and is dominated by the
cutoff weight on it. -/
theorem bpzWard_left_weight_bound (hd : BPZWardData γ q r δ ρ kt k₂ φ D) (v : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |bpzWardLeftWeight γ q r kt φ v x| ≤
      C * (ρ x * bpzWardCutWeight γ q r kt x) := by
  set f : ℂ → ℝ := fun x => φ x * kt x with hf
  have hfc : HasCompactSupport f := hd.φ_compact.mul_right
  have hcont : Continuous fun x => fderiv ℝ f x v :=
    (hd.f_C1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hsupp : HasCompactSupport fun x => fderiv ℝ f x v :=
    (hfc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L v) (by simp)
  obtain ⟨Cf, hCf⟩ := hcont.bounded_above_of_compact_support hsupp
  obtain ⟨c, hc, hck⟩ := hd.kt_pos
  refine ⟨max Cf 0 / c, by positivity, fun x => ?_⟩
  by_cases hx : x ∈ tsupport φ
  · have hρx : ρ x = 1 := by
      by_contra hne
      have h := hd.sep x hx x (lt_of_le_of_ne (hd.ρ_le_one x) hne)
      rw [sub_self, norm_zero] at h
      linarith [hd.δ_pos]
    have hkx := hck x hx
    have hkpos : 0 < kt x := lt_of_lt_of_le hc hkx
    unfold bpzWardLeftWeight bpzWardCutWeight
    rw [hρx, one_mul]
    have hn : 0 ≤ normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x) :=
      mul_nonneg (Real.rpow_nonneg (bpz_normPlus_pos x).le _) (Real.exp_pos _).le
    rw [mul_assoc, abs_mul, abs_of_nonneg hn]
    have hfx : |fderiv ℝ f x v| ≤ max Cf 0 := by
      have := hCf x
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
    calc |fderiv ℝ (fun x => φ x * kt x) x v| *
          (normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x))
        ≤ max Cf 0 * (normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x)) :=
          mul_le_mul_of_nonneg_right hfx hn
      _ ≤ max Cf 0 / c * kt x * (normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x)) := by
          apply mul_le_mul_of_nonneg_right _ hn
          rw [div_mul_eq_mul_div, le_div_iff₀ hc]
          exact mul_le_mul_of_nonneg_left hkx (le_max_right _ _)
      _ = max Cf 0 / c * (kt x * normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x)) := by
          ring
  · have hfx : fderiv ℝ f x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun h => hx ((tsupport_fderiv_subset ℝ).trans
        (tsupport_mul_subset_left (f := φ) (g := kt)) h)
    unfold bpzWardLeftWeight
    rw [hfx]
    simp only [zero_apply, zero_mul, abs_zero]
    exact mul_nonneg (by positivity) (mul_nonneg (hd.ρ_nonneg x)
      (bpzWardCutWeight_nonneg hd x))

theorem bpzPin_nonneg (r : ℝ) (x : ℂ) : 0 ≤ bpzPin r x :=
  integral_nonneg fun a => Real.log_nonneg (bpz_one_le_normPlus a)

/-- The cutoff weight alone is almost surely integrable against the cutoff chaos. -/
theorem bpzWard_cut_integrable' (hd : BPZWardData γ q r δ ρ kt k₂ φ D)
    (hp : BPZWardProb P X γ M Xc ρ k₂ D) :
    ∀ᵐ ω ∂P, Integrable (fun y => ρ y * bpzWardCutWeight γ q r kt y)
      (regularizedGMC P Xc γ r ω) := by
  filter_upwards [bpzWard_cut_integrable hd hp] with ω hω
  refine hω.mono' (hd.ρ_meas.mul (measurable_bpzWardCutWeight hd)).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have h0 := mul_nonneg (hd.ρ_nonneg y) (bpzWardCutWeight_nonneg hd y)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact le_mul_of_one_le_right h0
    (Real.one_le_exp (mul_nonneg (sq_nonneg γ) (bpzPin_nonneg r y)))

theorem bpzMixedReal_nonneg {ρ k₁ k₂ : ℂ → ℝ} (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∀ y, ρ y ≤ 1)
    (hk₁0 : ∀ y, 0 ≤ k₁ y) (hk₂0 : ∀ y, 0 ≤ k₂ y) (m₁ m₂ : Measure ℂ) :
    0 ≤ bpzMixedReal ρ k₁ k₂ m₁ m₂ :=
  add_nonneg (integral_nonneg fun y => mul_nonneg (hρ0 y) (hk₁0 y))
    (integral_nonneg fun y => mul_nonneg (by linarith [hρ1 y]) (hk₂0 y))

theorem bpzRootedMixedReal_nonneg {γ r : ℝ} {ρ k₁ k₂ : ℂ → ℝ} (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∀ y, ρ y ≤ 1) (hk₁0 : ∀ y, 0 ≤ k₁ y) (hk₂0 : ∀ y, 0 ≤ k₂ y) (x : ℂ)
    (m₁ m₂ : Measure ℂ) : 0 ≤ bpzRootedMixedReal γ r ρ k₁ k₂ x m₁ m₂ :=
  add_nonneg (integral_nonneg fun y => mul_nonneg (mul_nonneg (hρ0 y) (hk₁0 y))
      (bpzCutRootKernel_pos γ r x y).le)
    (integral_nonneg fun y => mul_nonneg (mul_nonneg (by linarith [hρ1 y]) (hk₂0 y))
      (bpzLimRootKernel_pos γ r x y).le)

theorem bpz_exp_mul_rpow_neg {a J q : ℝ} (hJ : 0 ≤ J) :
    (Real.exp a * J) ^ (-q) = Real.exp (-(q * a)) * J ^ (-q) := by
  rw [Real.mul_rpow (Real.exp_pos _).le hJ, ← Real.exp_mul]
  congr 2
  ring

/-- The left side of the cutoff Ward identity, rooted at the integration point. -/
theorem bpzWard_left_deroot (hd : BPZWardData γ q r δ ρ kt k₂ φ D)
    (hp : BPZWardProb P X γ M Xc ρ k₂ D) (v : ℂ) :
    ∫ ω, bpzMixedReal ρ (bpzWardCutWeight γ q r kt) k₂ (regularizedGMC P Xc γ r ω) (M ω) ^ (-q) *
        ∫ x, bpzWardLeftWeight γ q r kt φ v x ∂regularizedGMC P Xc γ r ω ∂P =
      ∫ x, fderiv ℝ (fun x => φ x * kt x) x v *
        ∫ ω, bpzRootedMixedReal γ r ρ (bpzWardCutWeight γ q r kt) k₂ x
          (regularizedGMC P Xc γ r ω) (M ω) ^ (-q) ∂P := by
  set k₁ := bpzWardCutWeight γ q r kt with hk₁def
  have hk₁m : Measurable k₁ := measurable_bpzWardCutWeight hd
  have hk₁0 : ∀ y, 0 ≤ k₁ y := bpzWardCutWeight_nonneg hd
  have hq0 : 0 ≤ q := le_trans zero_le_one hd.q_ge
  set wL : ℂ → ℝ := bpzWardLeftWeight γ q r kt φ v with hwL
  have hwLc : Continuous wL := by
    have h1 : Continuous fun x => fderiv ℝ (fun x => φ x * kt x) x v :=
      (hd.f_C1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact (h1.mul (bpz_continuous_normPlus.rpow_const fun x => Or.inl
      (bpz_normPlus_pos x).ne')).mul (Real.continuous_exp.comp
        (continuous_const.mul (continuous_bpzPin r)))
  have hMr : Measurable fun ω => regularizedGMC P Xc γ r ω :=
    regularizedGMC_measurable P X hp.hX Xc hp.hXc γ r
  have hImeas : Measurable fun ω => bpzMixedReal ρ k₁ k₂ (regularizedGMC P Xc γ r ω) (M ω) :=
    (measurable_bpzMixedReal hd.ρ_meas hk₁m hd.k₂_meas).comp (hMr.prodMk hp.hMm)
  set F : ℂ → Measure ℂ → Measure ℂ → ℝ := fun x m₁ m₂ =>
    wL x * bpzMixedReal ρ k₁ k₂ m₁ m₂ ^ (-q) with hF
  have hlhs : ∀ ω, bpzMixedReal ρ k₁ k₂ (regularizedGMC P Xc γ r ω) (M ω) ^ (-q) *
      ∫ x, wL x ∂regularizedGMC P Xc γ r ω =
        ∫ x, F x (regularizedGMC P Xc γ r ω) (M ω) ∂regularizedGMC P Xc γ r ω := by
    intro ω
    rw [hF, integral_mul_const, mul_comm]
  simp_rw [hlhs]
  have hFm : Measurable (fun p : Ω × ℂ => F p.2 (regularizedGMC P Xc γ r p.1) (M p.1)) :=
    (hwLc.measurable.comp measurable_snd).mul ((hImeas.comp measurable_fst).pow_const _)
  have hFx : ∀ x, Measurable (fun q' : Measure ℂ × Measure ℂ => F x q'.1 q'.2) :=
    fun x => measurable_const.mul
      ((measurable_bpzMixedReal hd.ρ_meas hk₁m hd.k₂_meas).pow_const _)
  obtain ⟨C, hC0, hC⟩ := bpzWard_left_weight_bound hd v
  obtain ⟨cI, hcI, hlowI⟩ := bpzWard_mixed_lower hd hp k₁ hk₁0 (P := P) (Xc := Xc) (r := r)
  have hInt1 := bpzWard_integrable_rpow_neg hp hd.D_meas hImeas.aestronglyMeasurable hcI hlowI
    (p := q - 1) (by linarith [hd.q_ge])
  have hcut := bpzWard_cut_integrable hd hp
  have hcut' := bpzWard_cut_integrable' hd hp
  have hint : ∫⁻ ω, ∫⁻ x, ENNReal.ofReal |F x (regularizedGMC P Xc γ r ω) (M ω)|
      ∂regularizedGMC P Xc γ r ω ∂P < ⊤ := by
    have hbound : ∀ᵐ ω ∂P, ∫⁻ x, ENNReal.ofReal |F x (regularizedGMC P Xc γ r ω) (M ω)|
        ∂regularizedGMC P Xc γ r ω ≤ ENNReal.ofReal (C *
          bpzMixedReal ρ k₁ k₂ (regularizedGMC P Xc γ r ω) (M ω) ^ (-(q - 1))) := by
      filter_upwards [hcut', hlowI, bpzWard_far_mass_pos hp hd.D_meas, hp.k₂_int] with
        ω hρk hlow hpos hk₂i
      set I := bpzMixedReal ρ k₁ k₂ (regularizedGMC P Xc γ r ω) (M ω) with hIdef
      have hIpos : 0 < I := lt_of_lt_of_le (mul_pos hcI hpos) hlow
      have hIq : 0 ≤ I ^ (-q) := Real.rpow_nonneg hIpos.le _
      have hle := bpz_lintegral_ofReal_abs_le (m := regularizedGMC P Xc γ r ω)
        (F := fun x => F x (regularizedGMC P Xc γ r ω) (M ω)) (w := fun y => ρ y * k₁ y)
        (C := C * I ^ (-q)) (mul_nonneg hC0 hIq) hρk
        (fun y => mul_nonneg (hd.ρ_nonneg y) (hk₁0 y)) (fun x => by
          simp only [hF]
          rw [abs_mul, abs_of_nonneg hIq]
          calc |wL x| * I ^ (-q) ≤ C * (ρ x * k₁ x) * I ^ (-q) :=
                mul_le_mul_of_nonneg_right (hC x) hIq
            _ = C * I ^ (-q) * (ρ x * k₁ x) := by ring)
      refine hle.trans (ENNReal.ofReal_le_ofReal ?_)
      have hsub : ∫ y, ρ y * k₁ y ∂regularizedGMC P Xc γ r ω ≤ I := by
        have h2 := integral_nonneg (μ := M ω) (f := fun y => (1 - ρ y) * k₂ y)
          fun y => mul_nonneg (by linarith [hd.ρ_le_one y]) (hd.k₂_nonneg y)
        show ∫ y, ρ y * k₁ y ∂regularizedGMC P Xc γ r ω ≤
          ∫ y, ρ y * k₁ y ∂regularizedGMC P Xc γ r ω + ∫ y, (1 - ρ y) * k₂ y ∂M ω
        exact le_add_of_nonneg_right h2
      calc C * I ^ (-q) * ∫ y, ρ y * k₁ y ∂regularizedGMC P Xc γ r ω ≤ C * I ^ (-q) * I :=
            mul_le_mul_of_nonneg_left hsub (mul_nonneg hC0 hIq)
        _ = C * I ^ (-(q - 1)) := by
            rw [mul_assoc, ← Real.rpow_add_one hIpos.ne']
            congr 2
            ring
    refine lt_of_le_of_lt (lintegral_mono_ae hbound) ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hInt1.const_mul C)
      (Eventually.of_forall fun ω => mul_nonneg hC0 (Real.rpow_nonneg
        (bpzMixedReal_nonneg hd.ρ_nonneg hd.ρ_le_one hk₁0 hd.k₂_nonneg _ _) _))]
    exact ENNReal.ofReal_lt_top
  rw [bpz_cutoff_deroot_real P X hp.hX hd.γ_pos hp.γ2 M hp.hM hp.hMm Xc hp.hXc r F hFm hFx hint]
  congr 1
  funext x
  have hstep : ∀ ω, F x ((regularizedGMC P Xc γ r ω).withDensity (bpzCutRootDensity γ r x))
      ((M ω).withDensity (bpzLimRootDensity γ r x)) =
        wL x * Real.exp (-(q * (γ ^ 2 * bpzPin r x))) *
          bpzRootedMixedReal γ r ρ k₁ k₂ x (regularizedGMC P Xc γ r ω) (M ω) ^ (-q) := by
    intro ω
    simp only [hF]
    rw [bpzMixedReal_tilt, bpz_exp_mul_rpow_neg (bpzRootedMixedReal_nonneg hd.ρ_nonneg
      hd.ρ_le_one hk₁0 hd.k₂_nonneg x _ _)]
    ring
  simp_rw [hstep]
  rw [integral_const_mul]
  have hn : normPlus x ^ (-4 : ℝ) * normPlus x ^ (4 : ℝ) = 1 := by
    rw [← Real.rpow_add (bpz_normPlus_pos x)]
    norm_num
  have he : Real.exp (γ ^ 2 * q * bpzPin r x) * Real.exp (-(q * (γ ^ 2 * bpzPin r x))) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  simp only [hwL, bpzWardLeftWeight]
  calc normPlus x ^ (-4 : ℝ) * (fderiv ℝ (fun x => φ x * kt x) x v * normPlus x ^ (4 : ℝ) *
        Real.exp (γ ^ 2 * q * bpzPin r x) * Real.exp (-(q * (γ ^ 2 * bpzPin r x))) *
        ∫ ω, bpzRootedMixedReal γ r ρ k₁ k₂ x (regularizedGMC P Xc γ r ω) (M ω) ^ (-q) ∂P)
      = fderiv ℝ (fun x => φ x * kt x) x v *
          (normPlus x ^ (-4 : ℝ) * normPlus x ^ (4 : ℝ)) *
          (Real.exp (γ ^ 2 * q * bpzPin r x) * Real.exp (-(q * (γ ^ 2 * bpzPin r x)))) *
          ∫ ω, bpzRootedMixedReal γ r ρ k₁ k₂ x (regularizedGMC P Xc γ r ω) (M ω) ^ (-q) ∂P := by
        ring
    _ = _ := by rw [hn, he, mul_one, mul_one]

/-- The untilted root-derivative functional is bounded by the mixed mass. -/
theorem abs_bpzMixedDerivReal_le {γ r : ℝ} {ρ k₁ k₂ : ℂ → ℝ} (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∀ y, ρ y ≤ 1) (hk₁0 : ∀ y, 0 ≤ k₁ y) (hk₂0 : ∀ y, 0 ≤ k₂ y) {m₁ m₂ : Measure ℂ}
    (h₁ : Integrable (fun y => ρ y * k₁ y) m₁) (h₂ : Integrable (fun y => (1 - ρ y) * k₂ y) m₂)
    (x v : ℂ) :
    |bpzMixedDerivReal γ r ρ k₁ k₂ x v m₁ m₂| ≤
      γ ^ 2 * Real.exp r * ‖v‖ * bpzMixedReal ρ k₁ k₂ m₁ m₂ := by
  set K : ℝ := γ ^ 2 * Real.exp r * ‖v‖ with hK
  have hK0 : 0 ≤ K := by positivity
  unfold bpzMixedDerivReal bpzMixedReal
  rw [mul_add]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun y => abs_nonneg _) (h₁.const_mul K)
      (Eventually.of_forall fun y => ?_))
    have hw := mul_nonneg (hρ0 y) (hk₁0 y)
    dsimp only
    rw [abs_mul, abs_of_nonneg hw, abs_mul, abs_of_nonneg (sq_nonneg γ)]
    have hL : |bpzLamDeriv r (x - y) v| ≤ Real.exp r * ‖v‖ := by
      rw [← Real.norm_eq_abs]
      exact ((bpzLamDeriv r (x - y)).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (norm_bpzLamDeriv_le_exp r _) (norm_nonneg v))
    calc ρ y * k₁ y * (γ ^ 2 * |bpzLamDeriv r (x - y) v|)
        ≤ ρ y * k₁ y * (γ ^ 2 * (Real.exp r * ‖v‖)) := by gcongr
      _ = K * (ρ y * k₁ y) := by rw [hK]; ring
  · rw [← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun y => abs_nonneg _) (h₂.const_mul K)
      (Eventually.of_forall fun y => ?_))
    have hw : 0 ≤ (1 - ρ y) * k₂ y := mul_nonneg (by linarith [hρ1 y]) (hk₂0 y)
    dsimp only
    rw [abs_mul, abs_of_nonneg hw, abs_mul, abs_of_nonneg (sq_nonneg γ)]
    have hT : |bpzTruncLogDeriv r (x - y) v| ≤ Real.exp r * ‖v‖ := by
      rw [← Real.norm_eq_abs]
      exact ((bpzTruncLogDeriv r (x - y)).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (norm_bpzTruncLogDeriv_le r _).1 (norm_nonneg v))
    calc (1 - ρ y) * k₂ y * (γ ^ 2 * |bpzTruncLogDeriv r (x - y) v|)
        ≤ (1 - ρ y) * k₂ y * (γ ^ 2 * (Real.exp r * ‖v‖)) := by gcongr
      _ = K * ((1 - ρ y) * k₂ y) := by rw [hK]; ring

/-- The rooted root-derivative functional is bounded by the rooted mixed mass. -/
theorem abs_bpzRootedMixedDerivApply_le {γ r : ℝ} {ρ k₁ k₂ : ℂ → ℝ} (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∀ y, ρ y ≤ 1) (hk₁0 : ∀ y, 0 ≤ k₁ y) (hk₂0 : ∀ y, 0 ≤ k₂ y) {m₁ m₂ : Measure ℂ}
    {x : ℂ} (h₁ : Integrable (fun y => ρ y * k₁ y * bpzCutRootKernel γ r x y) m₁)
    (h₂ : Integrable (fun y => (1 - ρ y) * k₂ y * bpzLimRootKernel γ r x y) m₂) (v : ℂ) :
    |bpzRootedMixedDerivApply γ r ρ k₁ k₂ x v m₁ m₂| ≤
      γ ^ 2 * Real.exp r * ‖v‖ * bpzRootedMixedReal γ r ρ k₁ k₂ x m₁ m₂ := by
  set K : ℝ := γ ^ 2 * Real.exp r * ‖v‖ with hK
  unfold bpzRootedMixedDerivApply bpzRootedMixedReal
  rw [mul_add]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun y => abs_nonneg _) (h₁.const_mul K)
      (Eventually.of_forall fun y => ?_))
    have ha : 0 ≤ ρ y * k₁ y * (bpzCutRootKernel γ r x y * γ ^ 2) :=
      mul_nonneg (mul_nonneg (hρ0 y) (hk₁0 y))
        (mul_nonneg (bpzCutRootKernel_pos γ r x y).le (sq_nonneg γ))
    have hL : |bpzLamDeriv r (x - y) v| ≤ Real.exp r * ‖v‖ := by
      rw [← Real.norm_eq_abs]
      exact ((bpzLamDeriv r (x - y)).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (norm_bpzLamDeriv_le_exp r _) (norm_nonneg v))
    dsimp only
    rw [abs_mul, abs_of_nonneg ha]
    calc ρ y * k₁ y * (bpzCutRootKernel γ r x y * γ ^ 2) * |bpzLamDeriv r (x - y) v|
        ≤ ρ y * k₁ y * (bpzCutRootKernel γ r x y * γ ^ 2) * (Real.exp r * ‖v‖) :=
          mul_le_mul_of_nonneg_left hL ha
      _ = K * (ρ y * k₁ y * bpzCutRootKernel γ r x y) := by rw [hK]; ring
  · rw [← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun y => abs_nonneg _) (h₂.const_mul K)
      (Eventually.of_forall fun y => ?_))
    have ha : 0 ≤ (1 - ρ y) * k₂ y * (bpzLimRootKernel γ r x y * γ ^ 2) :=
      mul_nonneg (mul_nonneg (by linarith [hρ1 y]) (hk₂0 y))
        (mul_nonneg (bpzLimRootKernel_pos γ r x y).le (sq_nonneg γ))
    have hT : |bpzTruncLogDeriv r (x - y) v| ≤ Real.exp r * ‖v‖ := by
      rw [← Real.norm_eq_abs]
      exact ((bpzTruncLogDeriv r (x - y)).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (norm_bpzTruncLogDeriv_le r _).1 (norm_nonneg v))
    dsimp only
    rw [abs_mul, abs_of_nonneg ha]
    calc (1 - ρ y) * k₂ y * (bpzLimRootKernel γ r x y * γ ^ 2) * |bpzTruncLogDeriv r (x - y) v|
        ≤ (1 - ρ y) * k₂ y * (bpzLimRootKernel γ r x y * γ ^ 2) * (Real.exp r * ‖v‖) :=
          mul_le_mul_of_nonneg_left hT ha
      _ = K * ((1 - ρ y) * k₂ y * bpzLimRootKernel γ r x y) := by rw [hK]; ring

theorem bpzMixedReal_cut_le {ρ k₁ k₂ : ℂ → ℝ} (hρ1 : ∀ y, ρ y ≤ 1) (hk₂0 : ∀ y, 0 ≤ k₂ y)
    (m₁ m₂ : Measure ℂ) : ∫ y, ρ y * k₁ y ∂m₁ ≤ bpzMixedReal ρ k₁ k₂ m₁ m₂ := by
  have h2 := integral_nonneg (μ := m₂) (f := fun y => (1 - ρ y) * k₂ y)
    fun y => mul_nonneg (by linarith [hρ1 y]) (hk₂0 y)
  show ∫ y, ρ y * k₁ y ∂m₁ ≤ ∫ y, ρ y * k₁ y ∂m₁ + ∫ y, (1 - ρ y) * k₂ y ∂m₂
  exact le_add_of_nonneg_right h2

theorem bpz_mul_rpow_neg_mul_le {C I A q : ℝ} (hC : 0 ≤ C) (hI : 0 < I) (hA : A ≤ I) :
    C * I ^ (-q) * A ≤ C * I ^ (-(q - 1)) := by
  calc C * I ^ (-q) * A ≤ C * I ^ (-q) * I :=
        mul_le_mul_of_nonneg_left hA (mul_nonneg hC (Real.rpow_nonneg hI.le _))
    _ = C * I ^ (-(q - 1)) := by
        rw [mul_assoc, ← Real.rpow_add_one hI.ne']
        congr 2
        ring

/-- A bounded function vanishing off the support of the test function, times the pinned `|x|₊⁴`
factor, is dominated by the cutoff weight. -/
theorem bpzWard_weight_bound_of (hd : BPZWardData γ q r δ ρ kt k₂ φ D) {g : ℂ → ℝ} {B : ℝ}
    (hgB : ∀ x, |g x| ≤ B) (hg0 : ∀ x, x ∉ tsupport φ → g x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |g x * normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x)| ≤
      C * (ρ x * bpzWardCutWeight γ q r kt x) := by
  obtain ⟨c, hc, hck⟩ := hd.kt_pos
  refine ⟨max B 0 / c, by positivity, fun x => ?_⟩
  have hn : 0 ≤ normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x) :=
    mul_nonneg (Real.rpow_nonneg (bpz_normPlus_pos x).le _) (Real.exp_pos _).le
  by_cases hx : x ∈ tsupport φ
  · have hρx : ρ x = 1 := by
      by_contra hne
      have h := hd.sep x hx x (lt_of_le_of_ne (hd.ρ_le_one x) hne)
      rw [sub_self, norm_zero] at h
      linarith [hd.δ_pos]
    have hkx := hck x hx
    unfold bpzWardCutWeight
    rw [hρx, one_mul, mul_assoc, abs_mul, abs_of_nonneg hn]
    calc |g x| * (normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x))
        ≤ max B 0 * (normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x)) :=
          mul_le_mul_of_nonneg_right ((hgB x).trans (le_max_left _ _)) hn
      _ ≤ max B 0 / c * kt x * (normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x)) := by
          apply mul_le_mul_of_nonneg_right _ hn
          rw [div_mul_eq_mul_div, le_div_iff₀ hc]
          exact mul_le_mul_of_nonneg_left hkx (le_max_right _ _)
      _ = max B 0 / c * (kt x * normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x)) := by
          ring
  · rw [hg0 x hx, zero_mul, zero_mul, abs_zero]
    exact mul_nonneg (by positivity) (mul_nonneg (hd.ρ_nonneg x) (bpzWardCutWeight_nonneg hd x))

/-- The right side of the cutoff Ward identity, rooted at the integration point. -/
theorem bpzWard_right_deroot (hd : BPZWardData γ q r δ ρ kt k₂ φ D)
    (hp : BPZWardProb P X γ M Xc ρ k₂ D) (v : ℂ) :
    ∫ ω, bpzMixedReal ρ (bpzWardCutWeight γ q r kt) k₂ (regularizedGMC P Xc γ r ω) (M ω) ^
        (-q - 1) * ∫ x, φ x * bpzWardCutWeight γ q r kt x * bpzMixedDerivReal γ r ρ
          (bpzWardCutWeight γ q r kt) k₂ x v (regularizedGMC P Xc γ r ω) (M ω)
          ∂regularizedGMC P Xc γ r ω ∂P =
      ∫ x, φ x * kt x *
        ∫ ω, bpzRootedMixedReal γ r ρ (bpzWardCutWeight γ q r kt) k₂ x
            (regularizedGMC P Xc γ r ω) (M ω) ^ (-q - 1) *
          bpzRootedMixedDerivApply γ r ρ (bpzWardCutWeight γ q r kt) k₂ x v
            (regularizedGMC P Xc γ r ω) (M ω) ∂P := by
  set k₁ := bpzWardCutWeight γ q r kt with hk₁def
  have hk₁m : Measurable k₁ := measurable_bpzWardCutWeight hd
  have hk₁0 : ∀ y, 0 ≤ k₁ y := bpzWardCutWeight_nonneg hd
  have hk₁x : ∀ x, k₁ x = kt x * normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x) :=
    fun x => rfl
  have hφk : ∀ x, φ x * k₁ x =
      φ x * kt x * normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x) := by
    intro x; rw [hk₁x]; ring
  have hφkc : Continuous fun x => φ x * k₁ x := by
    simp_rw [hφk]
    exact (hd.f_C1.continuous.mul (bpz_continuous_normPlus.rpow_const fun x => Or.inl
      (bpz_normPlus_pos x).ne')).mul (Real.continuous_exp.comp
        (continuous_const.mul (continuous_bpzPin r)))
  have hMr : Measurable fun ω => regularizedGMC P Xc γ r ω :=
    regularizedGMC_measurable P X hp.hX Xc hp.hXc γ r
  have hImeas : Measurable fun ω => bpzMixedReal ρ k₁ k₂ (regularizedGMC P Xc γ r ω) (M ω) :=
    (measurable_bpzMixedReal hd.ρ_meas hk₁m hd.k₂_meas).comp (hMr.prodMk hp.hMm)
  have hYm := measurable_bpzWard_Yhat (γ := γ) (r := r) P X hp.hX M hp.hMm hp.hM.1 Xc hp.hXc
    hd.ρ_meas hk₁m hd.k₂_meas v
  set F : ℂ → Measure ℂ → Measure ℂ → ℝ := fun x m₁ m₂ =>
    φ x * k₁ x * (bpzMixedReal ρ k₁ k₂ m₁ m₂ ^ (-q - 1) *
      bpzMixedDerivReal γ r ρ k₁ k₂ x v m₁ m₂) with hF
  have hlhs : ∀ ω, bpzMixedReal ρ k₁ k₂ (regularizedGMC P Xc γ r ω) (M ω) ^ (-q - 1) *
      ∫ x, φ x * k₁ x * bpzMixedDerivReal γ r ρ k₁ k₂ x v (regularizedGMC P Xc γ r ω) (M ω)
        ∂regularizedGMC P Xc γ r ω =
        ∫ x, F x (regularizedGMC P Xc γ r ω) (M ω) ∂regularizedGMC P Xc γ r ω := by
    intro ω
    rw [← integral_const_mul]
    congr 1
    funext x
    simp only [hF]
    ring
  simp_rw [hlhs]
  have hFm : Measurable (fun p : Ω × ℂ => F p.2 (regularizedGMC P Xc γ r p.1) (M p.1)) :=
    (hφkc.measurable.comp measurable_snd).mul
      (((hImeas.comp measurable_fst).pow_const _).mul hYm)
  have hFx : ∀ x, Measurable (fun q' : Measure ℂ × Measure ℂ => F x q'.1 q'.2) :=
    fun x => measurable_const.mul
      (((measurable_bpzMixedReal hd.ρ_meas hk₁m hd.k₂_meas).pow_const _).mul
        (measurable_bpzMixedDerivReal hd.ρ_meas hk₁m hd.k₂_meas x v))
  -- the weight `φ k₁` is dominated by the cutoff weight
  have hgc : Continuous fun x => φ x * kt x := hd.f_C1.continuous
  obtain ⟨B, hB⟩ := hgc.bounded_above_of_compact_support hd.φ_compact.mul_right
  obtain ⟨C, hC0, hC⟩ := bpzWard_weight_bound_of hd (g := fun x => φ x * kt x) (B := B)
    (fun x => by rw [← Real.norm_eq_abs]; exact hB x)
    (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul])
  have hC' : ∀ x, |φ x * k₁ x| ≤ C * (ρ x * k₁ x) := fun x => by rw [hφk]; exact hC x
  set K : ℝ := γ ^ 2 * Real.exp r * ‖v‖ with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨cI, hcI, hlowI⟩ := bpzWard_mixed_lower hd hp k₁ hk₁0 (P := P) (Xc := Xc) (r := r)
  have hInt1 := bpzWard_integrable_rpow_neg hp hd.D_meas hImeas.aestronglyMeasurable hcI hlowI
    (p := q - 1) (by linarith [hd.q_ge])
  have hcut' := bpzWard_cut_integrable' hd hp
  have hint : ∫⁻ ω, ∫⁻ x, ENNReal.ofReal |F x (regularizedGMC P Xc γ r ω) (M ω)|
      ∂regularizedGMC P Xc γ r ω ∂P < ⊤ := by
    have hbound : ∀ᵐ ω ∂P, ∫⁻ x, ENNReal.ofReal |F x (regularizedGMC P Xc γ r ω) (M ω)|
        ∂regularizedGMC P Xc γ r ω ≤ ENNReal.ofReal (C * K *
          bpzMixedReal ρ k₁ k₂ (regularizedGMC P Xc γ r ω) (M ω) ^ (-(q - 1))) := by
      filter_upwards [hcut', hlowI, bpzWard_far_mass_pos hp hd.D_meas, hp.k₂_int] with
        ω hρk hlow hpos hk₂i
      set I := bpzMixedReal ρ k₁ k₂ (regularizedGMC P Xc γ r ω) (M ω) with hIdef
      have hIpos : 0 < I := lt_of_lt_of_le (mul_pos hcI hpos) hlow
      have hIq : 0 ≤ I ^ (-q) := Real.rpow_nonneg hIpos.le _
      have hIq1 : 0 ≤ I ^ (-q - 1) := Real.rpow_nonneg hIpos.le _
      have hY := abs_bpzMixedDerivReal_le (γ := γ) (r := r) hd.ρ_nonneg hd.ρ_le_one hk₁0
        hd.k₂_nonneg hρk hk₂i
      have hle := bpz_lintegral_ofReal_abs_le (m := regularizedGMC P Xc γ r ω)
        (F := fun x => F x (regularizedGMC P Xc γ r ω) (M ω)) (w := fun y => ρ y * k₁ y)
        (C := C * K * I ^ (-q)) (mul_nonneg (mul_nonneg hC0 hK0) hIq) hρk
        (fun y => mul_nonneg (hd.ρ_nonneg y) (hk₁0 y)) (fun x => by
          simp only [hF]
          have hIY : |I ^ (-q - 1) * bpzMixedDerivReal γ r ρ k₁ k₂ x v
              (regularizedGMC P Xc γ r ω) (M ω)| ≤ K * I ^ (-q) := by
            rw [abs_mul, abs_of_nonneg hIq1]
            calc I ^ (-q - 1) * |bpzMixedDerivReal γ r ρ k₁ k₂ x v
                  (regularizedGMC P Xc γ r ω) (M ω)| ≤ I ^ (-q - 1) * (K * I) :=
                  mul_le_mul_of_nonneg_left (hY x v) hIq1
              _ = K * I ^ (-q - 1 + 1) := by rw [Real.rpow_add_one hIpos.ne']; ring
              _ = K * I ^ (-q) := by rw [show -q - 1 + 1 = -q by ring]
          rw [abs_mul]
          calc |φ x * k₁ x| * |I ^ (-q - 1) * bpzMixedDerivReal γ r ρ k₁ k₂ x v
                (regularizedGMC P Xc γ r ω) (M ω)| ≤ C * (ρ x * k₁ x) * (K * I ^ (-q)) :=
                mul_le_mul (hC' x) hIY (abs_nonneg _)
                  (mul_nonneg hC0 (mul_nonneg (hd.ρ_nonneg x) (hk₁0 x)))
            _ = C * K * I ^ (-q) * (ρ x * k₁ x) := by ring)
      refine hle.trans (ENNReal.ofReal_le_ofReal ?_)
      exact bpz_mul_rpow_neg_mul_le (mul_nonneg hC0 hK0) hIpos
        (bpzMixedReal_cut_le hd.ρ_le_one hd.k₂_nonneg _ _)
    refine lt_of_le_of_lt (lintegral_mono_ae hbound) ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hInt1.const_mul (C * K))
      (Eventually.of_forall fun ω => mul_nonneg (mul_nonneg hC0 hK0) (Real.rpow_nonneg
        (bpzMixedReal_nonneg hd.ρ_nonneg hd.ρ_le_one hk₁0 hd.k₂_nonneg _ _) _))]
    exact ENNReal.ofReal_lt_top
  rw [bpz_cutoff_deroot_real P X hp.hX hd.γ_pos hp.γ2 M hp.hM hp.hMm Xc hp.hXc r F hFm hFx hint]
  congr 1
  funext x
  have hstep : ∀ ω, F x ((regularizedGMC P Xc γ r ω).withDensity (bpzCutRootDensity γ r x))
      ((M ω).withDensity (bpzLimRootDensity γ r x)) =
        φ x * k₁ x * Real.exp (-(q * (γ ^ 2 * bpzPin r x))) *
          (bpzRootedMixedReal γ r ρ k₁ k₂ x (regularizedGMC P Xc γ r ω) (M ω) ^ (-q - 1) *
            bpzRootedMixedDerivApply γ r ρ k₁ k₂ x v (regularizedGMC P Xc γ r ω) (M ω)) := by
    intro ω
    simp only [hF]
    rw [bpzMixedReal_tilt, bpzMixedDerivReal_tilt, show -q - 1 = -(q + 1) by ring,
      bpz_exp_mul_rpow_neg (bpzRootedMixedReal_nonneg hd.ρ_nonneg hd.ρ_le_one hk₁0
        hd.k₂_nonneg x _ _)]
    have hexp : Real.exp (-((q + 1) * (γ ^ 2 * bpzPin r x))) * Real.exp (γ ^ 2 * bpzPin r x) =
        Real.exp (-(q * (γ ^ 2 * bpzPin r x))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← hexp]
    ring
  simp_rw [hstep]
  rw [integral_const_mul]
  have hn : normPlus x ^ (-4 : ℝ) * normPlus x ^ (4 : ℝ) = 1 := by
    rw [← Real.rpow_add (bpz_normPlus_pos x)]
    norm_num
  have he : Real.exp (γ ^ 2 * q * bpzPin r x) * Real.exp (-(q * (γ ^ 2 * bpzPin r x))) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [hk₁x]
  calc normPlus x ^ (-4 : ℝ) * (φ x * (kt x * normPlus x ^ (4 : ℝ) *
        Real.exp (γ ^ 2 * q * bpzPin r x)) * Real.exp (-(q * (γ ^ 2 * bpzPin r x))) *
        ∫ ω, bpzRootedMixedReal γ r ρ k₁ k₂ x (regularizedGMC P Xc γ r ω) (M ω) ^ (-q - 1) *
          bpzRootedMixedDerivApply γ r ρ k₁ k₂ x v (regularizedGMC P Xc γ r ω) (M ω) ∂P)
      = φ x * kt x * (normPlus x ^ (-4 : ℝ) * normPlus x ^ (4 : ℝ)) *
          (Real.exp (γ ^ 2 * q * bpzPin r x) * Real.exp (-(q * (γ ^ 2 * bpzPin r x)))) *
          ∫ ω, bpzRootedMixedReal γ r ρ k₁ k₂ x (regularizedGMC P Xc γ r ω) (M ω) ^ (-q - 1) *
            bpzRootedMixedDerivApply γ r ρ k₁ k₂ x v (regularizedGMC P Xc γ r ω) (M ω) ∂P := by
        ring
    _ = _ := by rw [hn, he, mul_one, mul_one]

end DOZZ.Proofs
