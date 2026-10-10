/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardLimitConvA

/-! # Limits of the double integrals of the cutoff Ward identity

The double integral of the antisymmetrized cutoff kernel against the cutoff chaos converges in
probability to that of the limit kernel `(φ(x)ρ(y) − φ(y)ρ(x)) k(x) k(y) K_v(x − y)/2` against the
limit chaos: the kernels are bounded uniformly, coincide with the limit kernel away from the
diagonal up to the uniformly convergent pinned weights, and the limit chaos has no atoms. The
far-region test functions converge as random test functions. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]
variable {γ q δ : ℝ} {ρ kt k₂ φ : ℂ → ℝ} {D : Set ℂ}
variable {P : Measure Ω} {X : Ω → Distr} {M : Ω → Measure ℂ} {Xc : Ω → ℂ → ℝ → ℝ}

theorem bpz_abs_mul_sub_mul_le {p p' u u' A B : ℝ} (hp : |p'| ≤ A) (hu : |u| ≤ B) :
    |p * u - p' * u'| ≤ |p - p'| * B + A * |u - u'| := by
  have : p * u - p' * u' = (p - p') * u + p' * (u - u') := by ring
  rw [this]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left hu (abs_nonneg _)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_right hp (abs_nonneg _)

theorem bpz_frac_mul_le_one {S V : ℝ} (hS : 0 ≤ S) (hV : 0 ≤ V) :
    S * V / ((S + 1) * (V + 1)) ≤ 1 := by
  rw [div_le_one (by positivity)]
  nlinarith

theorem bpz_three_frac_mul_le_one {S K V : ℝ} (hS : 0 ≤ S) (hK : 0 ≤ K) (hV : 0 ≤ V) :
    S * K * V / ((S + 1) * (K + 1) * (V + 1)) ≤ 1 := by
  rw [div_le_one (by positivity)]
  have h1 : S * K ≤ (S + 1) * (K + 1) := by nlinarith
  have h2 : S * K * V ≤ (S + 1) * (K + 1) * V := mul_le_mul_of_nonneg_right h1 hV
  nlinarith [mul_nonneg (mul_nonneg hS hK) hV]

/-- The antisymmetrized limit kernel is uniformly continuous in the first variable away from
the diagonal. -/
theorem bpz_antisym_kern_cont {a b : ℂ → ℝ} (ha : Continuous a) (hac : HasCompactSupport a)
    (hb : Continuous b) (hbc : HasCompactSupport b) (v : ℂ) :
    ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x x' y, η ≤ ‖x - y‖ →
      ‖x - x'‖ ≤ δ → |(a x * b y - a y * b x) / 2 * bpzKern v (x - y) -
        (a x' * b y - a y * b x') / 2 * bpzKern v (x' - y)| ≤ ε := by
  intro η hη ε hε
  obtain ⟨Ba, hBa⟩ := ha.bounded_above_of_compact_support hac
  obtain ⟨Bb, hBb⟩ := hb.bounded_above_of_compact_support hbc
  set A : ℝ := max Ba 0 with hA
  set B : ℝ := max Bb 0 with hB
  have hA0 : 0 ≤ A := le_max_right _ _
  have hB0 : 0 ≤ B := le_max_right _ _
  have hAx : ∀ x, |a x| ≤ A := fun x => by
    rw [← Real.norm_eq_abs]; exact (hBa x).trans (le_max_left _ _)
  have hBx : ∀ x, |b x| ≤ B := fun x => by
    rw [← Real.norm_eq_abs]; exact (hBb x).trans (le_max_left _ _)
  set V : ℝ := ‖v‖ with hVdef
  have hV0 : 0 ≤ V := norm_nonneg v
  set e₀ : ℝ := ε * η / ((A + B + 1) * (V + 1)) with he₀
  have he₀p : 0 < e₀ := by positivity
  obtain ⟨δa, hδa, hua⟩ := bpz_unifCont_of_compact ha hac e₀ he₀p
  obtain ⟨δb, hδb, hub⟩ := bpz_unifCont_of_compact hb hbc e₀ he₀p
  set δk : ℝ := ε * (η / 2) ^ 2 / (6 * ((A * B + 1) * (V + 1))) with hδk
  have hδkp : 0 < δk := by positivity
  refine ⟨min (min δa δb) (min (η / 2) δk), by positivity, fun x x' y hxy hxx' => ?_⟩
  have h1 : ‖x - x'‖ ≤ δa := hxx'.trans ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : ‖x - x'‖ ≤ δb := hxx'.trans ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : ‖x - x'‖ ≤ η / 2 := hxx'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : ‖x - x'‖ ≤ δk := hxx'.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hη2 : 0 < η / 2 := by positivity
  have hx'y : η / 2 ≤ ‖x' - y‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub x x' y
    linarith
  have hxy2 : η / 2 ≤ ‖x - y‖ := by linarith
  have hPb : |(a x' * b y - a y * b x') / 2| ≤ A * B := by
    rw [abs_div, abs_two]
    have e1 := mul_le_mul (hAx x') (hBx y) (abs_nonneg _) hA0
    have e2 := mul_le_mul (hAx y) (hBx x') (abs_nonneg _) hA0
    have : |a x' * b y - a y * b x'| ≤ 2 * (A * B) := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul (a x') (b y), abs_mul (a y) (b x')]
      linarith
    linarith
  have hKb : |bpzKern v (x - y)| ≤ V / η :=
    (abs_bpzKern_le v _).trans (div_le_div_of_nonneg_left (norm_nonneg v) hη hxy)
  have hPd : |(a x * b y - a y * b x) / 2 - (a x' * b y - a y * b x') / 2| ≤
      e₀ * (A + B) / 2 := by
    have : (a x * b y - a y * b x) / 2 - (a x' * b y - a y * b x') / 2 =
        ((a x - a x') * b y - a y * (b x - b x')) / 2 := by ring
    rw [this, abs_div, abs_two]
    have e1 : |(a x - a x') * b y| ≤ e₀ * B := by
      rw [abs_mul]; exact mul_le_mul (hua x x' h1) (hBx y) (abs_nonneg _) he₀p.le
    have e2 : |a y * (b x - b x')| ≤ A * e₀ := by
      rw [abs_mul]; exact mul_le_mul (hAx y) (hub x x' h2) (abs_nonneg _) hA0
    have := (abs_sub _ _).trans (add_le_add e1 e2)
    linarith
  have hKd : |bpzKern v (x - y) - bpzKern v (x' - y)| ≤ 3 * V * ‖x - x'‖ / (η / 2) ^ 2 := by
    have := abs_bpzKern_sub_le v hη2 hxy2 hx'y
    rwa [show x - y - (x' - y) = x - x' by ring] at this
  have hfirst : e₀ * (A + B) / 2 * (V / η) ≤ ε / 2 := by
    have := bpz_frac_mul_le_one (add_nonneg hA0 hB0) hV0
    have hrw : e₀ * (A + B) / 2 * (V / η) = ε / 2 * ((A + B) * V / ((A + B + 1) * (V + 1))) := by
      rw [he₀]; field_simp
    rw [hrw]
    calc ε / 2 * ((A + B) * V / ((A + B + 1) * (V + 1))) ≤ ε / 2 * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = ε / 2 := mul_one _
  have hsecond : A * B * (3 * V * δk / (η / 2) ^ 2) ≤ ε / 2 := by
    have := bpz_frac_mul_le_one (mul_nonneg hA0 hB0) hV0
    have hrw : A * B * (3 * V * δk / (η / 2) ^ 2) =
        ε / 2 * (A * B * V / ((A * B + 1) * (V + 1))) := by
      rw [hδk]; field_simp; ring
    rw [hrw]
    calc ε / 2 * (A * B * V / ((A * B + 1) * (V + 1))) ≤ ε / 2 * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = ε / 2 := mul_one _
  calc |(a x * b y - a y * b x) / 2 * bpzKern v (x - y) -
        (a x' * b y - a y * b x') / 2 * bpzKern v (x' - y)|
      ≤ |(a x * b y - a y * b x) / 2 - (a x' * b y - a y * b x') / 2| * (V / η) +
          A * B * |bpzKern v (x - y) - bpzKern v (x' - y)| :=
        bpz_abs_mul_sub_mul_le hPb hKb
    _ ≤ e₀ * (A + B) / 2 * (V / η) + A * B * (3 * V * δk / (η / 2) ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_right hPd (by positivity))
          (mul_le_mul_of_nonneg_left (hKd.trans (by gcongr)) (mul_nonneg hA0 hB0))
    _ ≤ ε / 2 + ε / 2 := add_le_add hfirst hsecond
    _ = ε := by ring

namespace BPZLimitData

theorem rho_abs_cutWeight_le (hd : BPZLimitData γ q δ ρ kt k₂ φ D) {K : ℝ}
    (hK : ∀ r : ℝ, 0 ≤ r → ∀ y, ρ y ≠ 0 →
      bpzWardCutWeight γ q r kt y ≤ K ∧ kt y * normPlus y ^ (4 + γ ^ 2 * q) ≤ K)
    (hK0 : 0 ≤ K) (n : ℕ) (y : ℂ) :
    ρ y * |bpzWardCutWeight γ q n kt y| ≤ K ∧ ρ y * |k₂ y| ≤ K := by
  by_cases hy : ρ y = 0
  · rw [hy, zero_mul, zero_mul]; exact ⟨hK0, hK0⟩
  have hw0 : 0 ≤ bpzWardCutWeight γ q n kt y := by
    unfold bpzWardCutWeight
    have := hd.kt_nonneg y
    have := Real.rpow_nonneg (bpz_normPlus_pos y).le (4 : ℝ)
    positivity
  obtain ⟨h1, h2⟩ := hK n (Nat.cast_nonneg n) y hy
  rw [← hd.k₂_eq] at h2
  rw [abs_of_nonneg hw0, abs_of_nonneg (hd.k₂_nonneg y)]
  exact ⟨(mul_le_mul (hd.ρ_le_one y) h1 hw0 zero_le_one).trans (by linarith),
    (mul_le_mul (hd.ρ_le_one y) h2 (hd.k₂_nonneg y) zero_le_one).trans (by linarith)⟩

theorem symKer_eq_zero (hd : BPZLimitData γ q δ ρ kt k₂ φ D) {R : ℝ}
    (hR : ∀ y, R < ‖y‖ → ρ y = 0) (k L : ℂ → ℝ) {x y : ℂ} (h : R < ‖x‖ ∨ R < ‖y‖) :
    bpzSymKer φ ρ k L x y = 0 := by
  unfold bpzSymKer
  rcases h with h | h
  · rw [hR x h, hd.phi_zero_of_rho_zero (hR x h)]; ring
  · rw [hR y h, hd.phi_zero_of_rho_zero (hR y h)]; ring

theorem symKer_eq_antisym (k L : ℂ → ℝ) (x y : ℂ) :
    bpzSymKer φ ρ k L x y = ((φ x * k x) * (ρ y * k y) - (φ y * k y) * (ρ x * k x)) / 2 * L (x - y) := by
  unfold bpzSymKer; ring

/-- The cutoff kernels converge uniformly away from the diagonal. -/
theorem symKer_unif (hd : BPZLimitData γ q δ ρ kt k₂ φ D) (v : ℂ) :
    ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ x y, η ≤ ‖x - y‖ →
      |bpzSymKer φ ρ (bpzWardCutWeight γ q n kt) (fun w => bpzLamDeriv n w v) x y -
        bpzSymKer φ ρ k₂ (bpzKern v) x y| ≤ ε := by
  intro η hη ε hε
  obtain ⟨K, hK0, hK⟩ := hd.cutWeight_bound
  obtain ⟨B, hB0, hB⟩ := hd.phi_bdd
  set V : ℝ := ‖v‖ with hVdef
  have hV0 : 0 ≤ V := norm_nonneg v
  set ε' : ℝ := ε * η / (2 * ((B + 1) * (K + 1) * (V + 1))) with hε'
  have hε'0 : 0 < ε' := by positivity
  have htail : ∀ᶠ n : ℕ in atTop, 2 * Real.exp (-(n : ℝ)) < η := by
    have := ((Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul
      2).eventually (gt_mem_nhds (show (2 : ℝ) * 0 < η by linarith))
    simpa [Function.comp_def] using this
  filter_upwards [hd.cutWeight_tendsto ε' hε'0, htail] with n hn htn x y hxy
  have hL : bpzLamDeriv n (x - y) v = bpzKern v (x - y) :=
    bpzLamDeriv_apply_eq_kern n (lt_of_lt_of_le htn hxy) v
  have heq : bpzSymKer φ ρ (bpzWardCutWeight γ q n kt) (fun w => bpzLamDeriv n w v) x y -
      bpzSymKer φ ρ k₂ (bpzKern v) x y =
        (φ x * ρ y - φ y * ρ x) * (bpzWardCutWeight γ q n kt x * bpzWardCutWeight γ q n kt y -
          k₂ x * k₂ y) * bpzKern v (x - y) / 2 := by
    unfold bpzSymKer
    beta_reduce
    rw [hL]
    ring
  rw [heq]
  by_cases hρ0 : ρ x = 0 ∨ ρ y = 0
  · rcases hρ0 with h | h
    · rw [h, hd.phi_zero_of_rho_zero h]; simp; positivity
    · rw [h, hd.phi_zero_of_rho_zero h]; simp; positivity
  push Not at hρ0
  obtain ⟨hx0, hy0⟩ := hρ0
  have hdx := hn x hx0
  have hdy := hn y hy0
  rw [← hd.k₂_eq] at hdx hdy
  have hk1x := (hK n (Nat.cast_nonneg n) x hx0).1
  have hk2y := (hK n (Nat.cast_nonneg n) y hy0).2
  rw [← hd.k₂_eq] at hk2y
  have hw0 : 0 ≤ bpzWardCutWeight γ q n kt x := by
    unfold bpzWardCutWeight
    have := hd.kt_nonneg x
    have := Real.rpow_nonneg (bpz_normPlus_pos x).le (4 : ℝ)
    positivity
  have hprod : |bpzWardCutWeight γ q n kt x * bpzWardCutWeight γ q n kt y - k₂ x * k₂ y| ≤
      2 * (K * ε') := by
    have : bpzWardCutWeight γ q n kt x * bpzWardCutWeight γ q n kt y - k₂ x * k₂ y =
        bpzWardCutWeight γ q n kt x * (bpzWardCutWeight γ q n kt y - k₂ y) +
          k₂ y * (bpzWardCutWeight γ q n kt x - k₂ x) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hw0, abs_of_nonneg (hd.k₂_nonneg y)]
    have e1 := mul_le_mul hk1x hdy (abs_nonneg _) hK0
    have e2 := mul_le_mul hk2y hdx (abs_nonneg _) hK0
    linarith
  have hφρ : |φ x * ρ y - φ y * ρ x| ≤ 2 * B := by
    have e1 : |φ x * ρ y| ≤ B := by
      rw [abs_mul, abs_of_nonneg (hd.ρ_nonneg y)]
      exact (mul_le_mul (hB x) (hd.ρ_le_one y) (hd.ρ_nonneg y) hB0).trans (by linarith)
    have e2 : |φ y * ρ x| ≤ B := by
      rw [abs_mul, abs_of_nonneg (hd.ρ_nonneg x)]
      exact (mul_le_mul (hB y) (hd.ρ_le_one x) (hd.ρ_nonneg x) hB0).trans (by linarith)
    have := (abs_sub _ _).trans (add_le_add e1 e2)
    linarith
  have hKb : |bpzKern v (x - y)| ≤ V / η :=
    (abs_bpzKern_le v _).trans (div_le_div_of_nonneg_left (norm_nonneg v) hη hxy)
  rw [abs_div, abs_two, abs_mul, abs_mul]
  have hfin : 2 * B * (2 * (K * ε')) * (V / η) / 2 ≤ ε := by
    have := bpz_three_frac_mul_le_one hB0 hK0 hV0
    have hrw : 2 * B * (2 * (K * ε')) * (V / η) / 2 =
        ε * (B * K * V / ((B + 1) * (K + 1) * (V + 1))) := by
      rw [hε']; field_simp
    rw [hrw]
    calc ε * (B * K * V / ((B + 1) * (K + 1) * (V + 1))) ≤ ε * 1 :=
          mul_le_mul_of_nonneg_left this hε.le
      _ = ε := mul_one _
  calc |φ x * ρ y - φ y * ρ x| *
        |bpzWardCutWeight γ q n kt x * bpzWardCutWeight γ q n kt y - k₂ x * k₂ y| *
        |bpzKern v (x - y)| / 2
      ≤ 2 * B * (2 * (K * ε')) * (V / η) / 2 := by gcongr
    _ ≤ ε := hfin

/-- The symmetric double integrals converge. -/
theorem conv_sym (hd : BPZLimitData γ q δ ρ kt k₂ φ D) (hp : BPZWardProb P X γ M Xc ρ k₂ D)
    (v : ℂ) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => ∫ x, ∫ y, bpzSymKer φ ρ (bpzWardCutWeight γ q n kt)
        (fun w => bpzLamDeriv n w v) x y ∂bpzCutChaos P Xc γ n ω ∂bpzCutChaos P Xc γ n ω) atTop
      (fun ω => ∫ x, ∫ y, bpzSymKer φ ρ k₂ (bpzKern v) x y ∂M ω ∂M ω) := by
  have : IsProbabilityMeasure P := hp.hX.1
  have hμ := bpzWeakConv_gmc P X hp.hX hd.γ_pos hp.γ2 M hp.hM hp.hMm Xc hp.hXc
  have hatom := gmc_noAtoms_ae P X hp.hX γ hd.γ_pos hp.γ2 M hp.hM hp.hMm
  obtain ⟨K, hK0, hK⟩ := hd.cutWeight_bound
  obtain ⟨R, hR0, hR⟩ := hd.rho_zero_of_norm
  obtain ⟨B, hB0, hB⟩ := hd.phi_bdd
  obtain ⟨Lφ, hLφ⟩ := hd.φ_lip
  have hδ := hd.δ_pos
  set Cs : ℝ := 2 * ‖v‖ * ((Lφ : ℝ) + B / δ) with hCs
  have hCs0 : 0 ≤ Cs := by positivity
  have hLn : ∀ (n : ℕ) w, |bpzLamDeriv n w v| ≤ 2 * ‖v‖ / ‖w‖ := fun n w =>
    abs_bpzLamDeriv_apply_le n w v
  have hK2 : ∀ w, |bpzKern v w| ≤ 2 * ‖v‖ / ‖w‖ := fun w =>
    (abs_bpzKern_le v w).trans (div_le_div_of_nonneg_right (by linarith [norm_nonneg v])
      (norm_nonneg w))
  have hbd : ∀ (n : ℕ) x y, |bpzSymKer φ ρ (bpzWardCutWeight γ q n kt)
      (fun w => bpzLamDeriv n w v) x y| ≤ Cs * (K * K) := by
    intro n x y
    refine (hd.abs_symKer_le hB hLφ zero_le_two v (hLn n) x y).trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hd.rho_abs_cutWeight_le hK hK0 n x).1
      (hd.rho_abs_cutWeight_le hK hK0 n y).1 (mul_nonneg (hd.ρ_nonneg y) (abs_nonneg _)) hK0)
      hCs0
  have hbd₀ : ∀ x y, |bpzSymKer φ ρ k₂ (bpzKern v) x y| ≤ Cs * (K * K) := by
    intro x y
    refine (hd.abs_symKer_le hB hLφ zero_le_two v hK2 x y).trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hd.rho_abs_cutWeight_le hK hK0 0 x).2
      (hd.rho_abs_cutWeight_le hK hK0 0 y).2 (mul_nonneg (hd.ρ_nonneg y) (abs_nonneg _)) hK0)
      hCs0
  have hLm : ∀ n : ℕ, Measurable fun w => bpzLamDeriv n w v := fun n =>
    (ContinuousLinearMap.apply ℝ ℝ v).continuous.measurable.comp (measurable_bpzLamDeriv n)
  have hac : Continuous fun x => φ x * k₂ x := by
    have h : (fun x => φ x * k₂ x) = fun x => (φ x * kt x) * normPlus x ^ (4 + γ ^ 2 * q) := by
      funext x; rw [hd.k₂_eq]; ring
    rw [h]
    exact hd.f_C1.continuous.mul (bpz_continuous_normPlus.rpow_const fun x => Or.inl
      (bpz_normPlus_pos x).ne')
  have has : HasCompactSupport fun x => φ x * k₂ x := bpz_hasCompactSupport_of_ball (R := R)
    fun x hx => by rw [hd.phi_zero_of_rho_zero (hR x hx), zero_mul]
  have hbs : HasCompactSupport fun x => ρ x * k₂ x := bpz_hasCompactSupport_of_ball (R := R)
    fun x hx => by rw [hR x hx, zero_mul]
  refine hμ.tendstoInMeasure_double hatom
    (fun n => bpzSymKer φ ρ (bpzWardCutWeight γ q n kt) (fun w => bpzLamDeriv n w v))
    (bpzSymKer φ ρ k₂ (bpzKern v))
    (fun n => measurable_bpzSymKer hd.phi_cont.measurable hd.ρ_meas
      (hd.measurable_cutWeight n) (hLm n))
    (measurable_bpzSymKer hd.phi_cont.measurable hd.ρ_meas hd.k₂_meas (measurable_bpzKern v))
    hR0 hbd hbd₀ (fun n x y h => hd.symKer_eq_zero hR _ _ h)
    (fun x y h => hd.symKer_eq_zero hR _ _ h) ?_ (hd.symKer_unif v)
  intro η hη ε hε
  obtain ⟨δ', hδ', h⟩ := bpz_antisym_kern_cont hac has hd.rho_k₂_cont hbs v η hη ε hε
  refine ⟨δ', hδ', fun x x' y hxy hxx' => ?_⟩
  rw [symKer_eq_antisym, symKer_eq_antisym]
  exact h x x' y hxy hxx'

end BPZLimitData

end DOZZ.Proofs
