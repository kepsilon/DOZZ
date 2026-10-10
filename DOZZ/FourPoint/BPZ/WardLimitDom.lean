/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardLimitId

/-! # Uniform domination of the symmetrized cutoff Ward identity

Both sides of the symmetrized cutoff Ward identity are bounded, uniformly in the cutoff, by a
multiple of `Î^{1-q}`, where `Î` is the mixed mass: the left integral is at most a multiple of the
cutoff part `∫ ρ k₁ dM_n ≤ Î`, the symmetric double integral at most a multiple of its square, and
the far-region term at most a multiple of `∫ ρ k₁ dM_n · ∫ (1 − ρ) k₂ dM ≤ Î²`. Since `Î` dominates
a multiple of the far-set chaos mass, which has all negative moments, the bound is integrable. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]
variable {γ q δ : ℝ} {ρ kt k₂ φ : ℂ → ℝ} {D : Set ℂ}
variable {P : Measure Ω} {X : Ω → Distr} {M : Ω → Measure ℂ} {Xc : Ω → ℂ → ℝ → ℝ}

theorem bpz_rpow_neg_mul_le {I A q : ℝ} (hI : 0 < I) (hAI : A ≤ I) :
    I ^ (-q) * A ≤ I ^ (1 - q) := by
  calc I ^ (-q) * A ≤ I ^ (-q) * I := mul_le_mul_of_nonneg_left hAI (Real.rpow_nonneg hI.le _)
    _ = I ^ (-q + 1) := (Real.rpow_add_one hI.ne' _).symm
    _ = I ^ (1 - q) := by ring_nf

theorem bpz_rpow_neg_sub_one_mul_le {I A B q : ℝ} (hI : 0 < I) (hAI : A ≤ I) (hB0 : 0 ≤ B)
    (hBI : B ≤ I) : I ^ (-q - 1) * (A * B) ≤ I ^ (1 - q) := by
  have h0 : 0 ≤ I ^ (-q - 1) := Real.rpow_nonneg hI.le _
  calc I ^ (-q - 1) * (A * B) ≤ I ^ (-q - 1) * (I * I) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hAI hBI hB0 hI.le) h0
    _ = I ^ (-q - 1 + 1 + 1) := by
        rw [Real.rpow_add_one hI.ne', Real.rpow_add_one hI.ne']; ring
    _ = I ^ (1 - q) := by ring_nf

namespace BPZLimitData

theorem cutWeight_nonneg (hd : BPZLimitData γ q δ ρ kt k₂ φ D) (r : ℝ) (y : ℂ) :
    0 ≤ bpzWardCutWeight γ q r kt y := by
  unfold bpzWardCutWeight
  have := hd.kt_nonneg y
  have := Real.rpow_nonneg (bpz_normPlus_pos y).le (4 : ℝ)
  positivity

/-- The far mass dominates a multiple of the far-set chaos mass. -/
theorem far_mass_lower (hd : BPZLimitData γ q δ ρ kt k₂ φ D)
    (hp : BPZWardProb P X γ M Xc ρ k₂ D) :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂P, c * (M ω D).toReal ≤ ∫ y, (1 - ρ y) * k₂ y ∂M ω := by
  obtain ⟨c, hc, hck⟩ := hd.D_low
  refine ⟨c, hc, ?_⟩
  filter_upwards [hp.k₂_int] with ω hint
  exact bpz_integral_lower_on_set hd.D_meas hint
    (fun y => mul_nonneg (by linarith [hd.ρ_le_one y]) (hd.k₂_nonneg y))
    (fun y hy => by rw [hd.D_rho y hy, sub_zero, one_mul]; exact hck y hy)

/-- The left integral is bounded by the cutoff part of the mixed mass. -/
theorem abs_leftInt_le (hd : BPZLimitData γ q δ ρ kt k₂ φ D) (v : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (m : Measure ℂ) [IsFiniteMeasure m],
      |∫ x, bpzWardLeftWeight γ q n kt φ v x ∂m| ≤
        C * ∫ x, ρ x * bpzWardCutWeight γ q n kt x ∂m := by
  obtain ⟨K, hK0, hK⟩ := hd.cutWeight_bound
  obtain ⟨c, hc, hck⟩ := hd.kt_pos
  have hf'c := hd.continuous_fderiv_apply v
  obtain ⟨Rφ, hRφ⟩ := hd.φ_compact.isCompact.isBounded.exists_norm_le
  have hf's : ∀ x, max Rφ 0 < ‖x‖ → fderiv ℝ (fun x => φ x * kt x) x v = 0 := fun x hx =>
    bpz_fderiv_mul_zero_of_notMem v (fun h => by
      have := (hRφ x h).trans (le_max_left Rφ 0); linarith)
  obtain ⟨B₁, hB₁⟩ := hf'c.bounded_above_of_compact_support (bpz_hasCompactSupport_of_ball hf's)
  set C : ℝ := max B₁ 0 / c with hCdef
  refine ⟨C, by positivity, fun n m _ => ?_⟩
  have hpt : ∀ x, |bpzWardLeftWeight γ q n kt φ v x| ≤
      C * (ρ x * bpzWardCutWeight γ q n kt x) := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · have hkt : 0 < kt x := lt_of_lt_of_le hc (hck x hx)
      have hrel : bpzWardLeftWeight γ q n kt φ v x = fderiv ℝ (fun x => φ x * kt x) x v / kt x *
          bpzWardCutWeight γ q n kt x := by
        unfold bpzWardLeftWeight bpzWardCutWeight
        field_simp
      rw [hrel, hd.rho_eq_one hx, one_mul, abs_mul, abs_of_nonneg (hd.cutWeight_nonneg n x)]
      apply mul_le_mul_of_nonneg_right _ (hd.cutWeight_nonneg n x)
      rw [abs_div, abs_of_pos hkt, div_le_div_iff₀ hkt hc]
      have h1 : |fderiv ℝ (fun x => φ x * kt x) x v| ≤ max B₁ 0 := by
        rw [← Real.norm_eq_abs]; exact (hB₁ x).trans (le_max_left _ _)
      calc |fderiv ℝ (fun x => φ x * kt x) x v| * c ≤ max B₁ 0 * c :=
            mul_le_mul_of_nonneg_right h1 hc.le
        _ ≤ max B₁ 0 * kt x := mul_le_mul_of_nonneg_left (hck x hx) (le_max_right _ _)
    · unfold bpzWardLeftWeight
      rw [bpz_fderiv_mul_zero_of_notMem v hx]
      simp only [zero_mul, abs_zero]
      exact mul_nonneg (by positivity) (mul_nonneg (hd.ρ_nonneg x) (hd.cutWeight_nonneg n x))
  have hwm : Measurable (bpzWardLeftWeight γ q n kt φ v) := by
    unfold bpzWardLeftWeight
    exact (hf'c.measurable.mul (bpz_measurable_normPlus.pow_const _)).mul
      (Real.measurable_exp.comp ((continuous_bpzPin _).measurable.const_mul _))
  have hρk : ∀ x, |ρ x * bpzWardCutWeight γ q n kt x| ≤ K := fun x => by
    rw [abs_mul, abs_of_nonneg (hd.ρ_nonneg x)]
    exact (hd.rho_abs_cutWeight_le hK hK0 n x).1
  have hIρ : Integrable (fun x => ρ x * bpzWardCutWeight γ q n kt x) m :=
    integrable_of_bdd_finite (hd.ρ_meas.mul (hd.measurable_cutWeight n)) hρk
  rw [← integral_const_mul, ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le (hIρ.const_mul C) (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hpt x)

/-- The symmetric double integral is bounded by the square of the cutoff part. -/
theorem abs_symInt_le (hd : BPZLimitData γ q δ ρ kt k₂ φ D) (v : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (m : Measure ℂ) [IsFiniteMeasure m],
      |∫ x, ∫ y, bpzSymKer φ ρ (bpzWardCutWeight γ q n kt) (fun w => bpzLamDeriv n w v) x y ∂m ∂m|
        ≤ C * ((∫ x, ρ x * bpzWardCutWeight γ q n kt x ∂m) *
          ∫ x, ρ x * bpzWardCutWeight γ q n kt x ∂m) := by
  obtain ⟨K, hK0, hK⟩ := hd.cutWeight_bound
  obtain ⟨B, hB0, hB⟩ := hd.phi_bdd
  obtain ⟨Lφ, hLφ⟩ := hd.φ_lip
  have hδ := hd.δ_pos
  set C : ℝ := 2 * ‖v‖ * ((Lφ : ℝ) + B / δ) with hCdef
  refine ⟨C, by positivity, fun n m _ => ?_⟩
  set w : ℂ → ℝ := fun x => ρ x * bpzWardCutWeight γ q n kt x with hw
  have hw0 : ∀ x, 0 ≤ w x := fun x => mul_nonneg (hd.ρ_nonneg x) (hd.cutWeight_nonneg n x)
  have hwb : ∀ x, |w x| ≤ K := fun x => by
    rw [abs_of_nonneg (hw0 x)]
    have := (hd.rho_abs_cutWeight_le hK hK0 n x).1
    rwa [abs_of_nonneg (hd.cutWeight_nonneg n x)] at this
  have hwm : Measurable w := hd.ρ_meas.mul (hd.measurable_cutWeight n)
  have hLm : Measurable fun w' => bpzLamDeriv n w' v :=
    (ContinuousLinearMap.apply ℝ ℝ v).continuous.measurable.comp (measurable_bpzLamDeriv n)
  have hHm := measurable_bpzSymKer hd.phi_cont.measurable hd.ρ_meas (hd.measurable_cutWeight n)
    hLm
  have hpt : ∀ x y, |bpzSymKer φ ρ (bpzWardCutWeight γ q n kt) (fun w' => bpzLamDeriv n w' v) x y|
      ≤ C * (w x * w y) := by
    intro x y
    have := hd.abs_symKer_le (k := bpzWardCutWeight γ q n kt) (L := fun w' => bpzLamDeriv n w' v)
      hB hLφ zero_le_two v (abs_bpzLamDeriv_apply_le n · v) x y
    simp only [abs_of_nonneg (hd.cutWeight_nonneg n x), abs_of_nonneg (hd.cutWeight_nonneg n y)]
      at this
    exact this
  have hbd : ∀ x y, |bpzSymKer φ ρ (bpzWardCutWeight γ q n kt) (fun w' => bpzLamDeriv n w' v) x y|
      ≤ C * (K * K) := fun x y =>
    (hpt x y).trans (mul_le_mul_of_nonneg_left (mul_le_mul ((le_abs_self _).trans (hwb x))
      ((le_abs_self _).trans (hwb y)) (hw0 y) hK0) (by positivity))
  have hIw : Integrable w m := integrable_of_bdd_finite hwm hwb
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ x, ‖∫ y, bpzSymKer φ ρ (bpzWardCutWeight γ q n kt) (fun w' => bpzLamDeriv n w' v) x y ∂m‖
        ∂m ≤ ∫ x, C * w x * ∫ y, w y ∂m ∂m := by
        refine integral_mono (bpz_integrable_inner hHm hbd).norm
          ((hIw.const_mul C).mul_const _) fun x => ?_
        rw [← integral_const_mul]
        refine (norm_integral_le_integral_norm _).trans (integral_mono
          (bpz_integrable_slice hHm hbd x).norm (hIw.const_mul _) fun y => ?_)
        rw [Real.norm_eq_abs]
        calc |bpzSymKer φ ρ (bpzWardCutWeight γ q n kt) (fun w' => bpzLamDeriv n w' v) x y|
            ≤ C * (w x * w y) := hpt x y
          _ = C * w x * w y := by ring
    _ = C * ((∫ x, w x ∂m) * ∫ x, w x ∂m) := by
        rw [integral_mul_const, integral_const_mul]; ring

/-- The far-region term is bounded by the product of the cutoff part and the far mass. -/
theorem abs_mixInt_le (hd : BPZLimitData γ q δ ρ kt k₂ φ D) (v : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (m₁ m₂ : Measure ℂ) [IsFiniteMeasure m₁],
      Integrable (fun y => (1 - ρ y) * k₂ y) m₂ →
      |∫ x, bpzMixTest φ ρ (bpzWardCutWeight γ q n kt) k₂ (fun w => bpzTruncLogDeriv n w v) m₂ x
          ∂m₁| ≤ C * ((∫ x, ρ x * bpzWardCutWeight γ q n kt x ∂m₁) *
            ∫ y, (1 - ρ y) * k₂ y ∂m₂) := by
  obtain ⟨K, hK0, hK⟩ := hd.cutWeight_bound
  obtain ⟨B, hB0, hB⟩ := hd.phi_bdd
  have hδ := hd.δ_pos
  set C : ℝ := 1 * ‖v‖ / (2 * δ) * B with hCdef
  refine ⟨C, by positivity, fun n m₁ m₂ _ hint => ?_⟩
  set I₂ : ℝ := ∫ y, (1 - ρ y) * k₂ y ∂m₂
  have hI₂0 : 0 ≤ I₂ := integral_nonneg fun y =>
    mul_nonneg (by linarith [hd.ρ_le_one y]) (hd.k₂_nonneg y)
  have hT : ∀ w, |bpzTruncLogDeriv n w v| ≤ 1 * ‖v‖ / ‖w‖ := fun w => by
    rw [one_mul]; exact abs_bpzTruncLogDeriv_apply_le n w v
  have hpt : ∀ x, |bpzMixTest φ ρ (bpzWardCutWeight γ q n kt) k₂
      (fun w => bpzTruncLogDeriv n w v) m₂ x| ≤ C * I₂ * (ρ x * bpzWardCutWeight γ q n kt x) := by
    intro x
    have := hd.abs_mixTest_le (k := bpzWardCutWeight γ q n kt)
      (L := fun w => bpzTruncLogDeriv n w v) hB zero_le_one v hT hint x
    rw [abs_of_nonneg (hd.cutWeight_nonneg n x)] at this
    calc _ ≤ 1 * ‖v‖ / (2 * δ) * B * (ρ x * bpzWardCutWeight γ q n kt x) * I₂ := this
      _ = C * I₂ * (ρ x * bpzWardCutWeight γ q n kt x) := by rw [hCdef]; ring
  have hwb : ∀ x, |ρ x * bpzWardCutWeight γ q n kt x| ≤ K := fun x => by
    rw [abs_mul, abs_of_nonneg (hd.ρ_nonneg x)]
    exact (hd.rho_abs_cutWeight_le hK hK0 n x).1
  have hIw : Integrable (fun x => ρ x * bpzWardCutWeight γ q n kt x) m₁ :=
    integrable_of_bdd_finite (hd.ρ_meas.mul (hd.measurable_cutWeight n)) hwb
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hIw.const_mul (C * I₂))
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hpt x)).trans (le_of_eq ?_)
  rw [integral_const_mul]
  ring

end BPZLimitData

end DOZZ.Proofs
