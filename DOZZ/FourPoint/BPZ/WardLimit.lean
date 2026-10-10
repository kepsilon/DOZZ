/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardLimitDom

/-! # The Ward identity in the limit

Along integer cutoffs both sides of the symmetrized cutoff Ward identity converge in probability,
and they are dominated uniformly by a multiple of `(c M(D))^{1-q}`, which is integrable. The
expectations of the limits therefore agree:

  `E[I^{-q} ∫ ∂_v(φ k̃) |x|₊^{4+γ²q} dM]
     = q E[I^{-q-1} γ² (∬ (φ(x)ρ(y) − φ(y)ρ(x)) k k K_v / 2 dM dM + ∫ x, ∫ (1−ρ) k φ k K_v dM dM)]`

with `I = ∫ ρ k dM + ∫ (1 − ρ) k dM`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]
variable {γ q δ : ℝ} {ρ kt k₂ φ : ℂ → ℝ} {D : Set ℂ}
variable {P : Measure Ω} {X : Ω → Distr} {M : Ω → Measure ℂ} {Xc : Ω → ℂ → ℝ → ℝ}

namespace BPZLimitData

theorem measurable_mixTest_joint (hd : BPZLimitData γ q δ ρ kt k₂ φ D)
    (hp : BPZWardProb P X γ M Xc ρ k₂ D) {k L : ℂ → ℝ} (hk : Measurable k)
    (hL : Measurable L) :
    Measurable (fun p : Ω × ℂ => bpzMixTest φ ρ k k₂ L (M p.1) p.2) := by
  unfold bpzMixTest
  exact measurable_integral_finite_family M hp.hMm hp.hM.1
    (fun x y => (1 - ρ y) * k₂ y * (φ x * k x * L (x - y)))
    ((((measurable_const.sub (hd.ρ_meas.comp measurable_snd)).mul
      (hd.k₂_meas.comp measurable_snd)).mul
      (((hd.phi_cont.measurable.comp measurable_fst).mul (hk.comp measurable_fst)).mul
        (hL.comp (measurable_fst.sub measurable_snd)))))

/-- **The Ward identity in the limit.** -/
theorem ward_limit (hd : BPZLimitData γ q δ ρ kt k₂ φ D) (hp : BPZWardProb P X γ M Xc ρ k₂ D)
    (v : ℂ) :
    ∫ ω, (∫ y, ρ y * k₂ y ∂M ω + ∫ y, (1 - ρ y) * k₂ y ∂M ω) ^ (-q) *
        ∫ x, fderiv ℝ (fun x => φ x * kt x) x v * normPlus x ^ (4 + γ ^ 2 * q) ∂M ω ∂P =
      ∫ ω, q * ((∫ y, ρ y * k₂ y ∂M ω + ∫ y, (1 - ρ y) * k₂ y ∂M ω) ^ (-q - 1) *
        (γ ^ 2 * ((∫ x, ∫ y, bpzSymKer φ ρ k₂ (bpzKern v) x y ∂M ω ∂M ω) +
          ∫ x, bpzMixTest φ ρ k₂ k₂ (bpzKern v) (M ω) x ∂M ω))) ∂P := by
  have : IsProbabilityMeasure P := hp.hX.1
  have hμ := bpzWeakConv_gmc P X hp.hX hd.γ_pos hp.γ2 M hp.hM hp.hMm Xc hp.hXc
  have hq0 : 0 ≤ q := le_trans zero_le_one hd.q_ge
  set μ : ℕ → Ω → Measure ℂ := fun n => bpzCutChaos P Xc γ n with hμdef
  set k₁ : ℕ → ℂ → ℝ := fun n => bpzWardCutWeight γ q n kt with hk₁
  -- the random variables
  set A : ℕ → Ω → ℝ := fun n ω => ∫ y, ρ y * k₁ n y ∂μ n ω with hA
  set I₂ : Ω → ℝ := fun ω => ∫ y, (1 - ρ y) * k₂ y ∂M ω with hI₂
  set Lw : ℕ → Ω → ℝ := fun n ω => ∫ x, bpzWardLeftWeight γ q n kt φ v x ∂μ n ω with hLw
  set S : ℕ → Ω → ℝ := fun n ω => ∫ x, ∫ y, bpzSymKer φ ρ (k₁ n) (fun w => bpzLamDeriv n w v) x y
    ∂μ n ω ∂μ n ω with hS
  set Mx : ℕ → Ω → ℝ := fun n ω => ∫ x, bpzMixTest φ ρ (k₁ n) k₂
    (fun w => bpzTruncLogDeriv n w v) (M ω) x ∂μ n ω with hMx
  -- measurability
  have hAm : ∀ n, Measurable (A n) := fun n =>
    (measurable_integral_measure (hd.ρ_meas.mul (hd.measurable_cutWeight n))).comp (hμ.meas n)
  have hI₂m : Measurable I₂ :=
    (measurable_integral_measure ((measurable_const.sub hd.ρ_meas).mul hd.k₂_meas)).comp hp.hMm
  have hLwm : ∀ n, Measurable (Lw n) := by
    intro n
    refine (measurable_integral_measure ?_).comp (hμ.meas n)
    unfold bpzWardLeftWeight
    exact ((hd.continuous_fderiv_apply v).measurable.mul (bpz_measurable_normPlus.pow_const _)).mul
      (Real.measurable_exp.comp ((continuous_bpzPin _).measurable.const_mul _))
  have hLm : ∀ n : ℕ, Measurable fun w => bpzLamDeriv n w v := fun n =>
    (ContinuousLinearMap.apply ℝ ℝ v).continuous.measurable.comp (measurable_bpzLamDeriv n)
  have hTm : ∀ n : ℕ, Measurable fun w => bpzTruncLogDeriv n w v := fun n =>
    (ContinuousLinearMap.apply ℝ ℝ v).continuous.measurable.comp (measurable_bpzTruncLogDeriv n)
  have hSm : ∀ n, Measurable (S n) := fun n =>
    bpz_measurable_double_integral (hμ.meas n) (hμ.fin n) (hμ.meas n) (hμ.fin n) _
      (measurable_bpzSymKer hd.phi_cont.measurable hd.ρ_meas (hd.measurable_cutWeight n) (hLm n))
  have hMxm : ∀ n, Measurable (Mx n) := fun n =>
    BPZWeakConv.measurable_integral_random (hμ.meas n) (hμ.fin n)
      (hd.measurable_mixTest_joint hp (hd.measurable_cutWeight n) (hTm n))
  -- convergences
  have hAconv : TendstoInMeasure P A atTop (fun ω => ∫ y, ρ y * k₂ y ∂M ω) := hd.conv_cut hp
  have hIconv : TendstoInMeasure P (fun n ω => A n ω + I₂ ω) atTop
      (fun ω => ∫ y, ρ y * k₂ y ∂M ω + I₂ ω) :=
    bpz_tendstoInMeasure_add (fun n => (hAm n).aestronglyMeasurable)
      (fun _ => hI₂m.aestronglyMeasurable) hAconv
      (tendstoInMeasure_of_tendsto_ae (fun _ => hI₂m.aestronglyMeasurable)
        (Eventually.of_forall fun _ => tendsto_const_nhds))
  have hLconv := hd.conv_left hp v
  have hSconv := hd.conv_sym hp v
  have hMxconv := hd.conv_mix hp v
  have hSMconv : TendstoInMeasure P (fun n ω => S n ω + Mx n ω) atTop
      (fun ω => (∫ x, ∫ y, bpzSymKer φ ρ k₂ (bpzKern v) x y ∂M ω ∂M ω) +
        ∫ x, bpzMixTest φ ρ k₂ k₂ (bpzKern v) (M ω) x ∂M ω) :=
    bpz_tendstoInMeasure_add (fun n => (hSm n).aestronglyMeasurable)
      (fun n => (hMxm n).aestronglyMeasurable) hSconv hMxconv
  -- positivity of the limit mass
  obtain ⟨c, hc, hlow⟩ := hd.far_mass_lower hp
  have hDpos := bpzWard_far_mass_pos hp hd.D_meas
  have hA0 : ∀ n ω, 0 ≤ A n ω := fun n ω => integral_nonneg fun y =>
    mul_nonneg (hd.ρ_nonneg y) (hd.cutWeight_nonneg n y)
  have hρk0 : ∀ ω, 0 ≤ ∫ y, ρ y * k₂ y ∂M ω := fun ω => integral_nonneg fun y =>
    mul_nonneg (hd.ρ_nonneg y) (hd.k₂_nonneg y)
  have hpos₀ : ∀ᵐ ω ∂P, 0 < ∫ y, ρ y * k₂ y ∂M ω + I₂ ω := by
    filter_upwards [hlow, hDpos] with ω h1 h2
    have := hρk0 ω
    nlinarith [mul_pos hc h2]
  -- the integrands
  have hZconv := bpz_tendstoInMeasure_map₂ (fun n => ((hAm n).add hI₂m).aestronglyMeasurable)
    (fun n => (hLwm n).aestronglyMeasurable) hIconv hLconv (fun a b => a ^ (-q) * b)
    ((measurable_fst.pow_const _).mul measurable_snd)
    (hpos₀.mono fun ω h => (continuousAt_fst.rpow_const (Or.inl h.ne')).mul continuousAt_snd)
  have hWconv := bpz_tendstoInMeasure_map₂ (fun n => ((hAm n).add hI₂m).aestronglyMeasurable)
    (fun n => ((hSm n).add (hMxm n)).aestronglyMeasurable) hIconv hSMconv
    (fun a b => q * (a ^ (-q - 1) * (γ ^ 2 * b)))
    (measurable_const.mul ((measurable_fst.pow_const _).mul (measurable_const.mul measurable_snd)))
    (hpos₀.mono fun ω h => by
      show ContinuousAt (fun p : ℝ × ℝ => q * (p.1 ^ (-q - 1) * (γ ^ 2 * p.2))) _
      exact continuousAt_const.mul ((continuousAt_fst.rpow_const (Or.inl h.ne')).mul
        (continuousAt_const.mul continuousAt_snd)))
  -- domination
  obtain ⟨CL, hCL0, hCL⟩ := hd.abs_leftInt_le v
  obtain ⟨CS, hCS0, hCS⟩ := hd.abs_symInt_le v
  obtain ⟨CM, hCM0, hCM⟩ := hd.abs_mixInt_le v
  set Cd : ℝ := CL + q * γ ^ 2 * (CS + CM) with hCd
  set Bd : Ω → ℝ := fun ω => Cd * (c * (M ω D).toReal) ^ (-(q - 1)) with hBd
  have hmD : Measurable fun ω => (M ω D).toReal :=
    ((Measure.measurable_coe hd.D_meas).comp hp.hMm).ennreal_toReal
  have hBdint : Integrable Bd P :=
    (bpzWard_integrable_rpow_neg hp hd.D_meas (hmD.const_mul c).aestronglyMeasurable hc
      (Eventually.of_forall fun _ => le_rfl) (p := q - 1) (by linarith [hd.q_ge])).const_mul Cd
  have hgood : ∀ᵐ ω ∂P, ∀ n : ℕ, 0 < c * (M ω D).toReal ∧
      c * (M ω D).toReal ≤ A n ω + I₂ ω ∧ Integrable (fun y => (1 - ρ y) * k₂ y) (M ω) := by
    filter_upwards [hlow, hDpos, hp.k₂_int] with ω h1 h2 h3 n
    exact ⟨mul_pos hc h2, by linarith [hA0 n ω], h3⟩
  have hpow : ∀ {I Y : ℝ}, 0 < Y → Y ≤ I → I ^ (1 - q) ≤ Y ^ (-(q - 1)) := by
    intro I Y hY hYI
    rw [show -(q - 1) = 1 - q by ring]
    exact Real.rpow_le_rpow_of_nonpos hY hYI (by linarith [hd.q_ge])
  have hI₂le : ∀ ω, I₂ ω ≤ A 0 ω + I₂ ω := fun ω => by linarith [hA0 0 ω]
  have hZb : ∀ n : ℕ, ∀ᵐ ω ∂P, |(A n ω + I₂ ω) ^ (-q) * Lw n ω| ≤ Bd ω := by
    intro n
    filter_upwards [hgood] with ω hω
    obtain ⟨hY, hYI, -⟩ := hω n
    have hI : 0 < A n ω + I₂ ω := lt_of_lt_of_le hY hYI
    have := hμ.fin n ω
    have hL := hCL n (μ n ω)
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hI.le _)]
    have h1 : A n ω ≤ A n ω + I₂ ω := by
      have : 0 ≤ I₂ ω := integral_nonneg fun y =>
        mul_nonneg (by linarith [hd.ρ_le_one y]) (hd.k₂_nonneg y)
      linarith
    calc (A n ω + I₂ ω) ^ (-q) * |Lw n ω| ≤ (A n ω + I₂ ω) ^ (-q) * (CL * A n ω) :=
          mul_le_mul_of_nonneg_left hL (Real.rpow_nonneg hI.le _)
      _ = CL * ((A n ω + I₂ ω) ^ (-q) * A n ω) := by ring
      _ ≤ CL * (A n ω + I₂ ω) ^ (1 - q) :=
          mul_le_mul_of_nonneg_left (bpz_rpow_neg_mul_le hI h1) hCL0
      _ ≤ CL * (c * (M ω D).toReal) ^ (-(q - 1)) :=
          mul_le_mul_of_nonneg_left (hpow hY hYI) hCL0
      _ ≤ Bd ω := by
          simp only [hBd, hCd]
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hY.le _)
          have : 0 ≤ q * γ ^ 2 * (CS + CM) := by positivity
          linarith
  have hWb : ∀ n : ℕ, ∀ᵐ ω ∂P,
      |q * ((A n ω + I₂ ω) ^ (-q - 1) * (γ ^ 2 * (S n ω + Mx n ω)))| ≤ Bd ω := by
    intro n
    filter_upwards [hgood] with ω hω
    obtain ⟨hY, hYI, hint⟩ := hω n
    have hI : 0 < A n ω + I₂ ω := lt_of_lt_of_le hY hYI
    have := hμ.fin n ω
    have hI₂0 : 0 ≤ I₂ ω := integral_nonneg fun y =>
      mul_nonneg (by linarith [hd.ρ_le_one y]) (hd.k₂_nonneg y)
    have h1 : A n ω ≤ A n ω + I₂ ω := by linarith
    have h2 : I₂ ω ≤ A n ω + I₂ ω := by linarith [hA0 n ω]
    have hSb := hCS n (μ n ω)
    have hMb := hCM n (μ n ω) (M ω) hint
    have hSM : |S n ω + Mx n ω| ≤ CS * (A n ω * A n ω) + CM * (A n ω * I₂ ω) :=
      (abs_add_le _ _).trans (add_le_add hSb hMb)
    have hIp : 0 ≤ (A n ω + I₂ ω) ^ (-q - 1) := Real.rpow_nonneg hI.le _
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hq0, abs_of_nonneg hIp,
      abs_of_nonneg (sq_nonneg γ)]
    calc q * ((A n ω + I₂ ω) ^ (-q - 1) * (γ ^ 2 * |S n ω + Mx n ω|))
        ≤ q * ((A n ω + I₂ ω) ^ (-q - 1) * (γ ^ 2 * (CS * (A n ω * A n ω) +
            CM * (A n ω * I₂ ω)))) := by gcongr
      _ = q * γ ^ 2 * (CS * ((A n ω + I₂ ω) ^ (-q - 1) * (A n ω * A n ω)) +
            CM * ((A n ω + I₂ ω) ^ (-q - 1) * (A n ω * I₂ ω))) := by ring
      _ ≤ q * γ ^ 2 * (CS * (A n ω + I₂ ω) ^ (1 - q) + CM * (A n ω + I₂ ω) ^ (1 - q)) := by
          gcongr
          · exact bpz_rpow_neg_sub_one_mul_le hI h1 (hA0 n ω) h1
          · exact bpz_rpow_neg_sub_one_mul_le hI h1 hI₂0 h2
      _ = q * γ ^ 2 * (CS + CM) * (A n ω + I₂ ω) ^ (1 - q) := by ring
      _ ≤ q * γ ^ 2 * (CS + CM) * (c * (M ω D).toReal) ^ (-(q - 1)) :=
          mul_le_mul_of_nonneg_left (hpow hY hYI) (by positivity)
      _ ≤ Bd ω := by
          simp only [hBd, hCd]
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hY.le _)
          linarith
  -- equal expectations along the sequence
  have heq : ∀ᶠ n in atTop, ∫ ω, (A n ω + I₂ ω) ^ (-q) * Lw n ω ∂P =
      ∫ ω, q * ((A n ω + I₂ ω) ^ (-q - 1) * (γ ^ 2 * (S n ω + Mx n ω))) ∂P := by
    filter_upwards [hd.eventually_wardData] with n hn
    exact hd.cutoff_identity_sym hp v hn
  exact bpz_integral_eq_of_tendstoInMeasure
    (fun n => (((hAm n).add hI₂m).pow_const _ |>.mul (hLwm n)).aestronglyMeasurable)
    (fun n => (measurable_const.mul ((((hAm n).add hI₂m).pow_const _).mul
      (measurable_const.mul ((hSm n).add (hMxm n))))).aestronglyMeasurable)
    hZconv hWconv hBdint hZb hWb heq

end BPZLimitData

end DOZZ.Proofs
