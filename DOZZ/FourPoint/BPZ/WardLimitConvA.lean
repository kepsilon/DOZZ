/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardLimitBounds

/-! # Limits of the single integrals of the cutoff Ward identity

Along integer cutoffs, the cutoff part `∫ ρ k₁ dM_n` of the mixed mass converges in probability to
`∫ ρ k dM`, and the left integral `∫ ∂_v(φ k̃) |x|₊⁴ e^{γ² q h_n} dM_n` converges to
`∫ ∂_v(φ k̃) |x|₊^{4+γ²q} dM`, where `k = k̃ |x|₊^{4+γ²q}`. Both follow from the convergence of
random test functions, since the pinned weights converge uniformly on the cutoff region. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]
variable {γ q δ : ℝ} {ρ kt k₂ φ : ℂ → ℝ} {D : Set ℂ}
variable {P : Measure Ω} {X : Ω → Distr} {M : Ω → Measure ℂ} {Xc : Ω → ℂ → ℝ → ℝ}

theorem bpz_hasCompactSupport_of_ball {f : ℂ → ℝ} {R : ℝ} (hf : ∀ x, R < ‖x‖ → f x = 0) :
    HasCompactSupport f :=
  HasCompactSupport.intro (isCompact_closedBall 0 R) fun x hx => hf x (by
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    exact hx)

namespace BPZLimitData

theorem rho_k₂_cont (hd : BPZLimitData γ q δ ρ kt k₂ φ D) : Continuous fun y => ρ y * k₂ y := by
  have h : (fun y => ρ y * k₂ y) = fun y => (ρ y * kt y) * normPlus y ^ (4 + γ ^ 2 * q) := by
    funext y; rw [hd.k₂_eq]; ring
  rw [h]
  exact hd.ρkt_cont.mul (bpz_continuous_normPlus.rpow_const fun x => Or.inl
    (bpz_normPlus_pos x).ne')

theorem rho_zero_of_norm (hd : BPZLimitData γ q δ ρ kt k₂ φ D) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y, R < ‖y‖ → ρ y = 0 := by
  obtain ⟨R, hR⟩ := hd.ρ_bdd
  exact ⟨max R 0, le_max_right _ _, fun y hy => hR y (lt_of_le_of_lt (le_max_left _ _) hy)⟩

theorem phi_zero_of_rho_zero (hd : BPZLimitData γ q δ ρ kt k₂ φ D) {x : ℂ} (hx : ρ x = 0) :
    φ x = 0 := by
  by_contra h
  rw [hd.rho_eq_one (subset_tsupport φ h)] at hx
  exact one_ne_zero hx

theorem measurable_cutWeight (hd : BPZLimitData γ q δ ρ kt k₂ φ D) (r : ℝ) :
    Measurable (bpzWardCutWeight γ q r kt) := by
  unfold bpzWardCutWeight
  exact (hd.kt_meas.mul (bpz_measurable_normPlus.pow_const _)).mul
    (Real.measurable_exp.comp ((continuous_bpzPin r).measurable.const_mul _))

/-- The cutoff part of the mixed mass converges. -/
theorem conv_cut (hd : BPZLimitData γ q δ ρ kt k₂ φ D) (hp : BPZWardProb P X γ M Xc ρ k₂ D) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => ∫ y, ρ y * bpzWardCutWeight γ q n kt y ∂bpzCutChaos P Xc γ n ω) atTop
      (fun ω => ∫ y, ρ y * k₂ y ∂M ω) := by
  have : IsProbabilityMeasure P := hp.hX.1
  have hμ := bpzWeakConv_gmc P X hp.hX hd.γ_pos hp.γ2 M hp.hM hp.hMm Xc hp.hXc
  obtain ⟨K, hK0, hK⟩ := hd.cutWeight_bound
  obtain ⟨R, hR0, hR⟩ := hd.rho_zero_of_norm
  have hV : 0 < K + 1 := by linarith
  have hk₂b : ∀ y, |ρ y * k₂ y| ≤ K + 1 := by
    intro y
    by_cases hy : ρ y = 0
    · rw [hy, zero_mul, abs_zero]; exact hV.le
    · have h2 := (hK 0 le_rfl y hy).2
      rw [← hd.k₂_eq] at h2
      rw [abs_of_nonneg (mul_nonneg (hd.ρ_nonneg y) (hd.k₂_nonneg y))]
      calc ρ y * k₂ y ≤ 1 * K :=
            mul_le_mul (hd.ρ_le_one y) h2 (hd.k₂_nonneg y) zero_le_one
        _ ≤ K + 1 := by linarith
  have hk₁b : ∀ (n : ℕ) y, |ρ y * bpzWardCutWeight γ q n kt y| ≤ K + 1 := by
    intro n y
    by_cases hy : ρ y = 0
    · rw [hy, zero_mul, abs_zero]; exact hV.le
    · have h1 := (hK n (Nat.cast_nonneg n) y hy).1
      have hw0 : 0 ≤ bpzWardCutWeight γ q n kt y := by
        unfold bpzWardCutWeight
        have := hd.kt_nonneg y
        have := Real.rpow_nonneg (bpz_normPlus_pos y).le (4 : ℝ)
        positivity
      rw [abs_of_nonneg (mul_nonneg (hd.ρ_nonneg y) hw0)]
      calc ρ y * bpzWardCutWeight γ q n kt y ≤ 1 * K :=
            mul_le_mul (hd.ρ_le_one y) h1 hw0 zero_le_one
        _ ≤ K + 1 := by linarith
  refine hμ.tendstoInMeasure_random_test (fun n _ y => ρ y * bpzWardCutWeight γ q n kt y)
    (fun _ y => ρ y * k₂ y)
    (fun n => (hd.ρ_meas.comp measurable_snd).mul ((hd.measurable_cutWeight n).comp measurable_snd))
    ((hd.ρ_meas.comp measurable_snd).mul (hd.k₂_meas.comp measurable_snd)) hR0
    (V := fun _ => K + 1) measurable_const (fun _ => hV.le)
    (fun n => Eventually.of_forall fun _ y => hk₁b n y)
    (Eventually.of_forall fun _ y => hk₂b y)
    (fun n _ y hy => by rw [hR y hy, zero_mul])
    (fun _ y hy => by rw [hR y hy, zero_mul]) ?_ ?_
  · intro ε hε
    obtain ⟨δ', hδ', h⟩ := bpz_unifCont_of_compact hd.rho_k₂_cont
      (bpz_hasCompactSupport_of_ball (R := R) fun y hy => by rw [hR y hy, zero_mul])
      (ε * (K + 1)) (by positivity)
    exact ⟨δ', hδ', Eventually.of_forall fun _ x x' hxx' => h x x' hxx'⟩
  · intro ε hε
    filter_upwards [hd.cutWeight_tendsto (ε * (K + 1)) (by positivity)] with n hn
    refine Eventually.of_forall fun _ y => ?_
    by_cases hy : ρ y = 0
    · rw [hy, zero_mul, zero_mul, sub_zero, abs_zero]; positivity
    · have h := hn y hy
      rw [← hd.k₂_eq] at h
      rw [← mul_sub, abs_mul, abs_of_nonneg (hd.ρ_nonneg y)]
      calc ρ y * |bpzWardCutWeight γ q n kt y - k₂ y| ≤ 1 * (ε * (K + 1)) :=
            mul_le_mul (hd.ρ_le_one y) h (abs_nonneg _) zero_le_one
        _ = ε * (K + 1) := one_mul _

end BPZLimitData

theorem bpz_fderiv_mul_zero_of_notMem {φ kt : ℂ → ℝ} (v : ℂ) {x : ℂ}
    (hx : x ∉ tsupport φ) : fderiv ℝ (fun x => φ x * kt x) x v = 0 := by
  have : fderiv ℝ (fun x => φ x * kt x) x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun h => hx ((tsupport_fderiv_subset ℝ).trans
      (tsupport_mul_subset_left (f := φ) (g := kt)) h)
  rw [this, zero_apply]

namespace BPZLimitData

theorem continuous_fderiv_apply (hd : BPZLimitData γ q δ ρ kt k₂ φ D) (v : ℂ) :
    Continuous fun x => fderiv ℝ (fun x => φ x * kt x) x v :=
  (hd.f_C1.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- The left integral converges. -/
theorem conv_left (hd : BPZLimitData γ q δ ρ kt k₂ φ D) (hp : BPZWardProb P X γ M Xc ρ k₂ D)
    (v : ℂ) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => ∫ x, bpzWardLeftWeight γ q n kt φ v x ∂bpzCutChaos P Xc γ n ω) atTop
      (fun ω => ∫ x, fderiv ℝ (fun x => φ x * kt x) x v * normPlus x ^ (4 + γ ^ 2 * q) ∂M ω) := by
  have : IsProbabilityMeasure P := hp.hX.1
  have hμ := bpzWeakConv_gmc P X hp.hX hd.γ_pos hp.γ2 M hp.hM hp.hMm Xc hp.hXc
  obtain ⟨K, hK0, hK⟩ := hd.cutWeight_bound
  obtain ⟨c, hc, hck⟩ := hd.kt_pos
  set f' : ℂ → ℝ := fun x => fderiv ℝ (fun x => φ x * kt x) x v with hf'
  have hf'c : Continuous f' := hd.continuous_fderiv_apply v
  obtain ⟨Rφ, hRφ⟩ := hd.φ_compact.isCompact.isBounded.exists_norm_le
  set R : ℝ := max Rφ 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hf's : ∀ x, R < ‖x‖ → f' x = 0 := fun x hx => bpz_fderiv_mul_zero_of_notMem v (fun h =>
    by have := (hRφ x h).trans (le_max_left Rφ 0); linarith)
  obtain ⟨B₁, hB₁⟩ := hf'c.bounded_above_of_compact_support (bpz_hasCompactSupport_of_ball hf's)
  set A : ℝ := max B₁ 0 / c * K with hA
  have hA0 : 0 ≤ A := by positivity
  have hV : 0 < A + 1 := by linarith
  -- the relation with the cutoff weights on the support of `φ`
  have hrel : ∀ (r : ℝ) x, x ∈ tsupport φ →
      bpzWardLeftWeight γ q r kt φ v x = f' x / kt x * bpzWardCutWeight γ q r kt x := by
    intro r x hx
    have hkt : kt x ≠ 0 := (lt_of_lt_of_le hc (hck x hx)).ne'
    unfold bpzWardLeftWeight bpzWardCutWeight
    simp only [hf']
    field_simp
  have hrel₀ : ∀ x, x ∈ tsupport φ →
      f' x * normPlus x ^ (4 + γ ^ 2 * q) = f' x / kt x * (kt x * normPlus x ^ (4 + γ ^ 2 * q)) := by
    intro x hx
    have hkt : kt x ≠ 0 := (lt_of_lt_of_le hc (hck x hx)).ne'
    field_simp
  have hratio : ∀ x, x ∈ tsupport φ → |f' x / kt x| ≤ max B₁ 0 / c := by
    intro x hx
    have hkt : 0 < kt x := lt_of_lt_of_le hc (hck x hx)
    rw [abs_div, abs_of_pos hkt, div_le_div_iff₀ hkt hc]
    have h1 : |f' x| ≤ max B₁ 0 := by
      rw [← Real.norm_eq_abs]; exact (hB₁ x).trans (le_max_left _ _)
    calc |f' x| * c ≤ max B₁ 0 * c := mul_le_mul_of_nonneg_right h1 hc.le
      _ ≤ max B₁ 0 * kt x := mul_le_mul_of_nonneg_left (hck x hx) (le_max_right _ _)
  have hwb : ∀ (n : ℕ) x, |bpzWardLeftWeight γ q n kt φ v x| ≤ A + 1 := by
    intro n x
    by_cases hx : x ∈ tsupport φ
    · rw [hrel n x hx, abs_mul]
      have hρ1 : ρ x ≠ 0 := by rw [hd.rho_eq_one hx]; exact one_ne_zero
      have hw0 : 0 ≤ bpzWardCutWeight γ q n kt x := by
        unfold bpzWardCutWeight
        have := hd.kt_nonneg x
        have := Real.rpow_nonneg (bpz_normPlus_pos x).le (4 : ℝ)
        positivity
      rw [abs_of_nonneg hw0]
      calc |f' x / kt x| * bpzWardCutWeight γ q n kt x ≤ max B₁ 0 / c * K :=
            mul_le_mul (hratio x hx) (hK n (Nat.cast_nonneg n) x hρ1).1 hw0 (by positivity)
        _ ≤ A + 1 := by linarith
    · unfold bpzWardLeftWeight
      rw [bpz_fderiv_mul_zero_of_notMem v hx]
      simp only [zero_mul, abs_zero]
      exact hV.le
  have hg₀b : ∀ x, |f' x * normPlus x ^ (4 + γ ^ 2 * q)| ≤ A + 1 := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · rw [hrel₀ x hx, abs_mul]
      have hρ1 : ρ x ≠ 0 := by rw [hd.rho_eq_one hx]; exact one_ne_zero
      have hw0 : 0 ≤ kt x * normPlus x ^ (4 + γ ^ 2 * q) :=
        mul_nonneg (hd.kt_nonneg x) (Real.rpow_nonneg (bpz_normPlus_pos x).le _)
      rw [abs_of_nonneg hw0]
      calc |f' x / kt x| * (kt x * normPlus x ^ (4 + γ ^ 2 * q)) ≤ max B₁ 0 / c * K :=
            mul_le_mul (hratio x hx) (hK 0 le_rfl x hρ1).2 hw0 (by positivity)
        _ ≤ A + 1 := by linarith
    · rw [show f' x = 0 from bpz_fderiv_mul_zero_of_notMem v hx, zero_mul, abs_zero]
      exact hV.le
  have hg₀c : Continuous fun x => f' x * normPlus x ^ (4 + γ ^ 2 * q) :=
    hf'c.mul (bpz_continuous_normPlus.rpow_const fun x => Or.inl (bpz_normPlus_pos x).ne')
  have hwm : ∀ n : ℕ, Measurable (bpzWardLeftWeight γ q n kt φ v) := by
    intro n
    unfold bpzWardLeftWeight
    exact (hf'c.measurable.mul (bpz_measurable_normPlus.pow_const _)).mul
      (Real.measurable_exp.comp ((continuous_bpzPin _).measurable.const_mul _))
  refine hμ.tendstoInMeasure_random_test (fun n _ x => bpzWardLeftWeight γ q n kt φ v x)
    (fun _ x => f' x * normPlus x ^ (4 + γ ^ 2 * q))
    (fun n => (hwm n).comp measurable_snd) (hg₀c.measurable.comp measurable_snd) hR0
    (V := fun _ => A + 1) measurable_const (fun _ => hV.le)
    (fun n => Eventually.of_forall fun _ x => hwb n x)
    (Eventually.of_forall fun _ x => hg₀b x)
    (fun n _ x hx => by
      unfold bpzWardLeftWeight
      rw [show fderiv ℝ (fun x => φ x * kt x) x v = 0 from hf's x hx]
      simp)
    (fun _ x hx => by rw [show f' x = 0 from hf's x hx, zero_mul]) ?_ ?_
  · intro ε hε
    obtain ⟨δ', hδ', h⟩ := bpz_unifCont_of_compact hg₀c
      (bpz_hasCompactSupport_of_ball (R := R) fun x hx => by
        rw [show f' x = 0 from hf's x hx, zero_mul])
      (ε * (A + 1)) (by positivity)
    exact ⟨δ', hδ', Eventually.of_forall fun _ x x' hxx' => h x x' hxx'⟩
  · intro ε hε
    have hεc : 0 < ε * (A + 1) / (max B₁ 0 / c + 1) := by positivity
    filter_upwards [hd.cutWeight_tendsto _ hεc] with n hn
    refine Eventually.of_forall fun _ x => ?_
    by_cases hx : x ∈ tsupport φ
    · have hρ1 : ρ x ≠ 0 := by rw [hd.rho_eq_one hx]; exact one_ne_zero
      rw [hrel n x hx, hrel₀ x hx, ← mul_sub, abs_mul]
      have h1 := hratio x hx
      have h2 := hn x hρ1
      calc |f' x / kt x| * |bpzWardCutWeight γ q n kt x - kt x * normPlus x ^ (4 + γ ^ 2 * q)|
          ≤ (max B₁ 0 / c + 1) * (ε * (A + 1) / (max B₁ 0 / c + 1)) :=
            mul_le_mul (by linarith) h2 (abs_nonneg _) (by positivity)
        _ = ε * (A + 1) := by field_simp
    · have h0 : fderiv ℝ (fun x => φ x * kt x) x v = 0 := bpz_fderiv_mul_zero_of_notMem v hx
      simp only [bpzWardLeftWeight, hf', h0, zero_mul, sub_zero, abs_zero]
      positivity

end BPZLimitData

end DOZZ.Proofs
