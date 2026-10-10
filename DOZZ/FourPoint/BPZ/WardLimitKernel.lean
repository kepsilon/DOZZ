/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardStarC
public import DOZZ.FourPoint.BPZ.SoftCalculus

/-! # Kernels of the cutoff Ward identity in the limit

The cutoff root-derivative kernels `Λ_r'` and `T_r'` coincide with the limit kernel
`K_v(w) = ∂_v(-log|w|) = -⟨w, v⟩/|w|²` once `|w|` exceeds the cutoff scale, `Λ_r'` is odd, and
`|Λ_r'(w) v| ≤ 2|v|/|w|` uniformly in `r`. The pinned cutoff weight converges uniformly on the
cutoff region to `k̃ |x|₊^{4+γ²q}`. The deterministic data of the limit is recorded in
`BPZLimitData`, which yields the cutoff data for every large integer cutoff. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The limit root-derivative kernel `∂_v(-log|w|) = -⟨w, v⟩/|w|²`. -/
noncomputable def bpzKern (v w : ℂ) : ℝ := -((w.re * v.re + w.im * v.im) / ‖w‖ ^ 2)

theorem bpzKern_neg (v w : ℂ) : bpzKern v (-w) = -bpzKern v w := by
  unfold bpzKern
  rw [norm_neg]
  simp only [Complex.neg_re, Complex.neg_im]
  ring

theorem bpzKern_zero (v : ℂ) : bpzKern v 0 = 0 := by simp [bpzKern]

theorem measurable_bpzKern (v : ℂ) : Measurable (bpzKern v) := by
  unfold bpzKern
  fun_prop

theorem abs_bpzKern_le (v w : ℂ) : |bpzKern v w| ≤ ‖v‖ / ‖w‖ := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [bpzKern]
  · have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
    unfold bpzKern
    rw [abs_neg, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ‖w‖ ^ 2),
      div_le_div_iff₀ (by positivity) hw']
    have hcs : |w.re * v.re + w.im * v.im| ≤ ‖w‖ * ‖v‖ := bpzSoft_abs_inner_le w v
    calc |w.re * v.re + w.im * v.im| * ‖w‖ ≤ ‖w‖ * ‖v‖ * ‖w‖ :=
          mul_le_mul_of_nonneg_right hcs hw'.le
      _ = ‖v‖ * ‖w‖ ^ 2 := by ring

/-- The real-algebra core of the Lipschitz bound for the limit kernel. -/
theorem bpz_kern_alg {a b p p' d V η : ℝ} (hη : 0 < η) (ha : η ≤ a) (hb : η ≤ b)
    (hV : 0 ≤ V) (hd : 0 ≤ d) (hpp : |p - p'| ≤ d * V) (hp' : |p'| ≤ b * V)
    (hab : |a - b| ≤ d) : |-(p / a ^ 2) + p' / b ^ 2| ≤ 3 * V * d / η ^ 2 := by
  have ha0 : 0 < a := lt_of_lt_of_le hη ha
  have hb0 : 0 < b := lt_of_lt_of_le hη hb
  have hη2 : 0 < η ^ 2 := by positivity
  have e : -(p / a ^ 2) + p' / b ^ 2 =
      -((p - p') / a ^ 2) + p' * (a - b) * (a + b) / (a ^ 2 * b ^ 2) := by
    field_simp
    ring
  rw [e]
  have h1 : |(p - p') / a ^ 2| ≤ d * V / η ^ 2 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < a ^ 2)]
    calc |p - p'| / a ^ 2 ≤ d * V / a ^ 2 := div_le_div_of_nonneg_right hpp (by positivity)
      _ ≤ d * V / η ^ 2 := div_le_div_of_nonneg_left (by positivity) hη2
          (pow_le_pow_left₀ hη.le ha 2)
  have h2 : |p' * (a - b) * (a + b) / (a ^ 2 * b ^ 2)| ≤ 2 * V * d / η ^ 2 := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < a + b),
      abs_of_pos (by positivity : 0 < a ^ 2 * b ^ 2)]
    have hnum : |p'| * |a - b| * (a + b) ≤ b * V * d * (a + b) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hp' hab (abs_nonneg _) (by positivity))
        (by positivity)
    have hden : b * V * d * (a + b) / (a ^ 2 * b ^ 2) = V * d * (1 / (a * b) + 1 / a ^ 2) := by
      field_simp
    have hab' : 1 / (a * b) ≤ 1 / η ^ 2 :=
      one_div_le_one_div_of_le hη2 (by nlinarith)
    have haa : 1 / a ^ 2 ≤ 1 / η ^ 2 :=
      one_div_le_one_div_of_le hη2 (pow_le_pow_left₀ hη.le ha 2)
    calc |p'| * |a - b| * (a + b) / (a ^ 2 * b ^ 2)
        ≤ b * V * d * (a + b) / (a ^ 2 * b ^ 2) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ = V * d * (1 / (a * b) + 1 / a ^ 2) := hden
      _ ≤ V * d * (1 / η ^ 2 + 1 / η ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add hab' haa) (by positivity)
      _ = 2 * V * d / η ^ 2 := by ring
  calc |-((p - p') / a ^ 2) + p' * (a - b) * (a + b) / (a ^ 2 * b ^ 2)|
      ≤ |(p - p') / a ^ 2| + |p' * (a - b) * (a + b) / (a ^ 2 * b ^ 2)| := by
        rw [← abs_neg ((p - p') / a ^ 2)]
        exact abs_add_le _ _
    _ ≤ d * V / η ^ 2 + 2 * V * d / η ^ 2 := add_le_add h1 h2
    _ = 3 * V * d / η ^ 2 := by ring

/-- The limit kernel is Lipschitz away from the origin. -/
theorem abs_bpzKern_sub_le (v : ℂ) {η : ℝ} (hη : 0 < η) {w w' : ℂ} (hw : η ≤ ‖w‖)
    (hw' : η ≤ ‖w'‖) : |bpzKern v w - bpzKern v w'| ≤ 3 * ‖v‖ * ‖w - w'‖ / η ^ 2 := by
  have hpp : |(w.re * v.re + w.im * v.im) - (w'.re * v.re + w'.im * v.im)| ≤
      ‖w - w'‖ * ‖v‖ := by
    have := bpzSoft_abs_inner_le (w - w') v
    simp only [Complex.sub_re, Complex.sub_im] at this
    calc _ = |(w.re - w'.re) * v.re + (w.im - w'.im) * v.im| := by ring_nf
      _ ≤ ‖w - w'‖ * ‖v‖ := this
  have hp' := bpz_kern_alg (V := ‖v‖) hη hw hw' (norm_nonneg v) (norm_nonneg _) hpp
    ((bpzSoft_abs_inner_le w' v).trans (le_of_eq (by ring)))
    (abs_norm_sub_norm_le w w')
  unfold bpzKern
  calc |-((w.re * v.re + w.im * v.im) / ‖w‖ ^ 2) - -((w'.re * v.re + w'.im * v.im) / ‖w'‖ ^ 2)|
      = |-((w.re * v.re + w.im * v.im) / ‖w‖ ^ 2) +
          (w'.re * v.re + w'.im * v.im) / ‖w'‖ ^ 2| := by ring_nf
    _ ≤ 3 * ‖v‖ * ‖w - w'‖ / η ^ 2 := hp'

theorem bpzLamDeriv_zero (r : ℝ) : bpzLamDeriv r 0 = 0 := by
  unfold bpzLamDeriv
  have h : ∀ θ : ℝ,
      bpzTruncLogDeriv r (0 + Real.exp (-r) * Complex.exp (θ * Complex.I)) = 0 := by
    intro θ
    unfold bpzTruncLogDeriv
    refine ite_eq_right (fun hlt => ?_)
    rw [zero_add, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hlt
    exact lt_irrefl _ hlt
  simp_rw [h]
  simp

/-- The cutoff kernel derivative is odd. -/
theorem bpzLamDeriv_neg (r : ℝ) (w : ℂ) : bpzLamDeriv r (-w) = -bpzLamDeriv r w := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [bpzLamDeriv_zero]
  have h1 : HasFDerivAt (bpzLam r) (bpzLamDeriv r w) w := hasFDerivAt_bpzLam r hw
  have h2 : HasFDerivAt (bpzLam r) (bpzLamDeriv r (-w)) (-w) :=
    hasFDerivAt_bpzLam r (neg_ne_zero.mpr hw)
  have h3 : HasFDerivAt (fun x => bpzLam r (-x))
      ((bpzLamDeriv r (-w)).comp (-ContinuousLinearMap.id ℝ ℂ)) w :=
    h2.comp w (hasFDerivAt_id w).neg
  have heq : (fun x => bpzLam r (-x)) = bpzLam r := funext fun x => bpzLam_neg r x
  rw [heq] at h3
  have huniq := h1.unique h3
  ext h
  have hh := congrArg (fun L : ℂ →L[ℝ] ℝ => L h) huniq
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, neg_apply,
    ContinuousLinearMap.coe_id', id_eq, map_neg] at hh
  rw [neg_apply, hh, neg_neg]

theorem bpzLamDeriv_apply_eq_kern (r : ℝ) {w : ℂ} (hw : 2 * Real.exp (-r) < ‖w‖) (v : ℂ) :
    bpzLamDeriv r w v = bpzKern v w := by
  rw [bpzLamDeriv_eq_of_far r hw, smul_apply, bpzSoft_innerSL_apply, smul_eq_mul, bpzKern]
  ring

theorem bpzTruncLogDeriv_apply_eq_kern (r : ℝ) {w : ℂ} (hw : Real.exp (-r) < ‖w‖) (v : ℂ) :
    bpzTruncLogDeriv r w v = bpzKern v w := by
  unfold bpzTruncLogDeriv
  rw [ite_eq_left hw, smul_apply, bpzSoft_innerSL_apply, smul_eq_mul, bpzKern]
  ring

theorem abs_bpzLamDeriv_apply_le (r : ℝ) (w v : ℂ) :
    |bpzLamDeriv r w v| ≤ 2 * ‖v‖ / ‖w‖ := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [bpzLamDeriv_zero]
  rw [← Real.norm_eq_abs]
  calc ‖bpzLamDeriv r w v‖ ≤ ‖bpzLamDeriv r w‖ * ‖v‖ := (bpzLamDeriv r w).le_opNorm v
    _ ≤ 2 / ‖w‖ * ‖v‖ := mul_le_mul_of_nonneg_right (norm_bpzLamDeriv_le r hw) (norm_nonneg v)
    _ = 2 * ‖v‖ / ‖w‖ := by ring

theorem abs_bpzTruncLogDeriv_apply_le (r : ℝ) (w v : ℂ) :
    |bpzTruncLogDeriv r w v| ≤ ‖v‖ / ‖w‖ := by
  by_cases h : Real.exp (-r) < ‖w‖
  · rw [bpzTruncLogDeriv_apply_eq_kern r h]
    exact abs_bpzKern_le v w
  · unfold bpzTruncLogDeriv
    rw [ite_eq_right h, zero_apply, abs_zero]
    positivity

/-- The deterministic data of the limit of the cutoff Ward identity: the data of
`BPZWardData` without the cutoff, with a Lipschitz test function, a continuous cutoff weight on
the cutoff region, and the far weight equal to the limit of the pinned cutoff weight. -/
structure BPZLimitData (γ q δ : ℝ) (ρ kt k₂ φ : ℂ → ℝ) (D : Set ℂ) : Prop where
  γ_pos : 0 < γ
  q_ge : 1 ≤ q
  δ_pos : 0 < δ
  ρ_meas : Measurable ρ
  ρ_nonneg : ∀ y, 0 ≤ ρ y
  ρ_le_one : ∀ y, ρ y ≤ 1
  ρ_bdd : ∃ R : ℝ, ∀ y, R < ‖y‖ → ρ y = 0
  kt_meas : Measurable kt
  kt_nonneg : ∀ y, 0 ≤ kt y
  kt_bdd : ∃ B : ℝ, ∀ y, ρ y ≠ 0 → kt y ≤ B
  ρkt_cont : Continuous fun y => ρ y * kt y
  k₂_eq : ∀ y, k₂ y = kt y * normPlus y ^ (4 + γ ^ 2 * q)
  f_C1 : ContDiff ℝ 1 (fun x => φ x * kt x)
  φ_compact : HasCompactSupport φ
  φ_lip : ∃ L : ℝ≥0, LipschitzWith L φ
  kt_pos : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ tsupport φ, c ≤ kt x
  sep : ∀ x ∈ tsupport φ, ∀ y, ρ y < 1 → 2 * δ ≤ ‖x - y‖
  D_meas : MeasurableSet D
  D_rho : ∀ y ∈ D, ρ y = 0
  D_low : ∃ c : ℝ, 0 < c ∧ ∀ y ∈ D, c ≤ k₂ y
  D_bdd : ∃ R : ℝ, ∀ y ∈ D, ‖y‖ ≤ R

namespace BPZLimitData

variable {γ q δ : ℝ} {ρ kt k₂ φ : ℂ → ℝ} {D : Set ℂ}

theorem k₂_meas (hd : BPZLimitData γ q δ ρ kt k₂ φ D) : Measurable k₂ := by
  have : k₂ = fun y => kt y * normPlus y ^ (4 + γ ^ 2 * q) := funext hd.k₂_eq
  rw [this]
  exact hd.kt_meas.mul (bpz_measurable_normPlus.pow_const _)

theorem k₂_nonneg (hd : BPZLimitData γ q δ ρ kt k₂ φ D) (y : ℂ) : 0 ≤ k₂ y := by
  rw [hd.k₂_eq]
  exact mul_nonneg (hd.kt_nonneg y) (Real.rpow_nonneg (bpz_normPlus_pos y).le _)

/-- The cutoff data at every cutoff below the separation scale. -/
theorem toWardData (hd : BPZLimitData γ q δ ρ kt k₂ φ D) {r : ℝ} (hr : 0 ≤ r)
    (hδr : Real.exp (-r) ≤ δ) : BPZWardData γ q r δ ρ kt k₂ φ D where
  γ_pos := hd.γ_pos
  q_ge := hd.q_ge
  r_nonneg := hr
  δ_pos := hd.δ_pos
  δ_r := hδr
  ρ_meas := hd.ρ_meas
  ρ_nonneg := hd.ρ_nonneg
  ρ_le_one := hd.ρ_le_one
  ρ_bdd := hd.ρ_bdd
  kt_meas := hd.kt_meas
  kt_nonneg := hd.kt_nonneg
  kt_bdd := hd.kt_bdd
  k₂_meas := hd.k₂_meas
  k₂_nonneg := hd.k₂_nonneg
  f_C1 := hd.f_C1
  φ_compact := hd.φ_compact
  kt_pos := hd.kt_pos
  sep := hd.sep
  D_meas := hd.D_meas
  D_rho := hd.D_rho
  D_low := hd.D_low
  D_bdd := hd.D_bdd

theorem eventually_wardData (hd : BPZLimitData γ q δ ρ kt k₂ φ D) :
    ∀ᶠ n : ℕ in atTop, BPZWardData γ q n δ ρ kt k₂ φ D := by
  have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).eventually
    (gt_mem_nhds hd.δ_pos)
  filter_upwards [h] with n hn
  exact hd.toWardData (Nat.cast_nonneg n) hn.le

theorem rho_eq_one (hd : BPZLimitData γ q δ ρ kt k₂ φ D) {x : ℂ} (hx : x ∈ tsupport φ) :
    ρ x = 1 := by
  by_contra hne
  have h := hd.sep x hx x (lt_of_le_of_ne (hd.ρ_le_one x) hne)
  rw [sub_self, norm_zero] at h
  linarith [hd.δ_pos]

/-- Near the diagonal the antisymmetrized cutoff combination is a difference of `φ`. -/
theorem near_diag (hd : BPZLimitData γ q δ ρ kt k₂ φ D) {x y : ℂ} (hxy : ‖x - y‖ < 2 * δ) :
    φ x * ρ y - φ y * ρ x = φ x - φ y := by
  by_cases hx : φ x = 0
  · by_cases hy : φ y = 0
    · rw [hx, hy]; ring
    · have hyt : y ∈ tsupport φ := subset_tsupport φ hy
      have hρx : ρ x = 1 := by
        by_contra hne
        have h := hd.sep y hyt x (lt_of_le_of_ne (hd.ρ_le_one x) hne)
        rw [norm_sub_rev] at h
        linarith
      rw [hρx, hd.rho_eq_one hyt]; ring
  · have hxt : x ∈ tsupport φ := subset_tsupport φ hx
    have hρy : ρ y = 1 := by
      by_contra hne
      have h := hd.sep x hxt y (lt_of_le_of_ne (hd.ρ_le_one y) hne)
      linarith
    rw [hρy, hd.rho_eq_one hxt]; ring

/-- Uniform bounds for the pinned cutoff weights and their limit on the cutoff region. -/
theorem cutWeight_bound (hd : BPZLimitData γ q δ ρ kt k₂ φ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 0 ≤ r → ∀ y, ρ y ≠ 0 →
      bpzWardCutWeight γ q r kt y ≤ K ∧ kt y * normPlus y ^ (4 + γ ^ 2 * q) ≤ K := by
  obtain ⟨R, hR⟩ := hd.ρ_bdd
  obtain ⟨B, hB⟩ := hd.kt_bdd
  have hq0 : 0 ≤ q := le_trans zero_le_one hd.q_ge
  set R₁ : ℝ := max R 0 + 1 with hR₁
  have hR₁1 : 1 ≤ R₁ := by have := le_max_right R 0; linarith
  set K₁ : ℝ := max B 0 * R₁ ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * (Real.log R₁ + 1))
  set K₂ : ℝ := max B 0 * R₁ ^ (4 + γ ^ 2 * q)
  refine ⟨max K₁ K₂, le_max_of_le_left (by positivity), fun r hr y hy => ?_⟩
  have hyR : ‖y‖ ≤ R := by
    by_contra h
    exact hy (hR y (lt_of_not_ge h))
  have hnp : normPlus y ≤ R₁ := by
    unfold normPlus
    apply max_le hR₁1
    have := le_max_left R 0; linarith
  have hkt : kt y ≤ max B 0 := (hB y hy).trans (le_max_left _ _)
  have hkt0 := hd.kt_nonneg y
  have hnp0 := bpz_normPlus_pos y
  constructor
  · refine le_max_of_le_left ?_
    unfold bpzWardCutWeight
    have hpin : bpzPin r y ≤ Real.log R₁ + 1 := by
      have h1 := bpzPin_le_log_normPlus_add r y
      have h2 := Real.log_le_log hnp0 hnp
      have h3 : Real.exp (-r) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
      linarith
    have h4 : normPlus y ^ (4 : ℝ) ≤ R₁ ^ (4 : ℝ) :=
      Real.rpow_le_rpow hnp0.le hnp (by norm_num)
    have h5 : Real.exp (γ ^ 2 * q * bpzPin r y) ≤ Real.exp (γ ^ 2 * q * (Real.log R₁ + 1)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpin (by positivity))
    have h6 : 0 ≤ normPlus y ^ (4 : ℝ) := Real.rpow_nonneg hnp0.le _
    calc kt y * normPlus y ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r y)
        ≤ max B 0 * R₁ ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * (Real.log R₁ + 1)) :=
          mul_le_mul (mul_le_mul hkt h4 h6 (le_max_right _ _)) h5 (Real.exp_pos _).le
            (by positivity)
      _ = K₁ := rfl
  · refine le_max_of_le_right ?_
    exact mul_le_mul hkt (Real.rpow_le_rpow hnp0.le hnp (by positivity))
      (Real.rpow_nonneg hnp0.le _) (le_max_right _ _)

/-- The pinned cutoff weight converges uniformly on the cutoff region. -/
theorem cutWeight_tendsto (hd : BPZLimitData γ q δ ρ kt k₂ φ D) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ y, ρ y ≠ 0 →
      |bpzWardCutWeight γ q n kt y - kt y * normPlus y ^ (4 + γ ^ 2 * q)| ≤ ε := by
  intro ε hε
  obtain ⟨K, hK0, hK⟩ := hd.cutWeight_bound
  have hq0 : 0 ≤ q := le_trans zero_le_one hd.q_ge
  set c : ℝ := γ ^ 2 * q with hc
  have hc0 : 0 ≤ c := by positivity
  have hlim : Tendsto (fun n : ℕ => 2 * c * K * Real.exp (-(n : ℝ))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul
      (2 * c * K)
    simpa [Function.comp_def] using this
  have hlim1 : Tendsto (fun n : ℕ => c * Real.exp (-(n : ℝ))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul c
    simpa [Function.comp_def] using this
  filter_upwards [hlim.eventually (ge_mem_nhds hε), hlim1.eventually (ge_mem_nhds zero_lt_one)]
    with n hn hn1 y hy
  obtain ⟨h1, h2⟩ := hK n (Nat.cast_nonneg n) y hy
  have hnp0 := bpz_normPlus_pos y
  have hkt0 := hd.kt_nonneg y
  have hpin := abs_bpzPin_sub_le n y
  have hsplit : normPlus y ^ (4 + c) = normPlus y ^ (4 : ℝ) * Real.exp (c * Real.log (normPlus y)) := by
    rw [Real.rpow_add hnp0, Real.rpow_def_of_pos hnp0 c, mul_comm (Real.log _) c]
  have hdiff : bpzWardCutWeight γ q n kt y - kt y * normPlus y ^ (4 + c) =
      kt y * normPlus y ^ (4 + c) * (Real.exp (c * (bpzPin n y - Real.log (normPlus y))) - 1) := by
    have e1 : Real.exp (c * Real.log (normPlus y)) *
        Real.exp (c * (bpzPin n y - Real.log (normPlus y))) =
          Real.exp (γ ^ 2 * q * bpzPin n y) := by
      rw [← Real.exp_add, hc]
      congr 1
      ring
    unfold bpzWardCutWeight
    rw [hsplit, ← e1]
    ring
  rw [hdiff, abs_mul, abs_of_nonneg (mul_nonneg hkt0 (Real.rpow_nonneg hnp0.le _))]
  have habs : |c * (bpzPin n y - Real.log (normPlus y))| ≤ c * Real.exp (-(n : ℝ)) := by
    rw [abs_mul, abs_of_nonneg hc0]
    exact mul_le_mul_of_nonneg_left hpin hc0
  have hexp : |Real.exp (c * (bpzPin n y - Real.log (normPlus y))) - 1| ≤
      2 * (c * Real.exp (-(n : ℝ))) :=
    (Real.abs_exp_sub_one_le (habs.trans hn1)).trans (by linarith)
  calc kt y * normPlus y ^ (4 + c) *
        |Real.exp (c * (bpzPin n y - Real.log (normPlus y))) - 1|
      ≤ K * (2 * (c * Real.exp (-(n : ℝ)))) :=
        mul_le_mul h2 hexp (abs_nonneg _) hK0
    _ = 2 * c * K * Real.exp (-(n : ℝ)) := by ring
    _ ≤ ε := hn

end BPZLimitData

end DOZZ.Proofs
