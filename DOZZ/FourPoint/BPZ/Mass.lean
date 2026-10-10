/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.Weight
public import DOZZ.GMC.SharpMoments.SeibergMoment
public import DOZZ.GMC.SharpMoments.SeibergPieces
public import DOZZ.GMC.SharpMoments.MomentRange
public import DOZZ.Statements.FourPoint.FourPointT

/-! # The degenerate four-point mass

`bpzMass ε m z` integrates the softened degenerate weight against a measure `m`. For an
`IsGMCOf` chaos and `z ∉ {0,1}` the case `ε = 0` is almost surely the Coulomb mass of the
reduced four-point function. The mass is bounded below, uniformly for `z` in a ball and
`0 ≤ ε ≤ 1`, by a positive multiple of the chaos mass of a fixed far disk; hence every negative
moment is finite, uniformly. It is also almost surely finite. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The softened degenerate four-point mass of a measure. -/
noncomputable def bpzMass (γ χ α₁ α₂ α₃ ε : ℝ) (m : Measure ℂ) (z : ℂ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (bpzSoftWeight γ χ α₁ α₂ α₃ ε z x) ∂m

variable {γ χ α₁ α₂ α₃ : ℝ}

theorem measurable_bpzMass_measure (ε : ℝ) (z : ℂ) :
    Measurable (fun m : Measure ℂ => bpzMass γ χ α₁ α₂ α₃ ε m z) :=
  Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp (measurable_bpzSoftWeight ε z))

/-- The far disk used for lower bounds of the mass, for `z` in the closed ball of radius `R`. -/
noncomputable def bpzFarBall (R : ℝ) : Set ℂ := Metric.ball (((R + 4 : ℝ)) : ℂ) (1 / 2)

theorem bpzFarBall_isOpen (R : ℝ) : IsOpen (bpzFarBall R) := Metric.isOpen_ball

theorem bpzFarBall_measurableSet (R : ℝ) : MeasurableSet (bpzFarBall R) :=
  (bpzFarBall_isOpen R).measurableSet

theorem bpzFarBall_bounded (R : ℝ) : Bornology.IsBounded (bpzFarBall R) := Metric.isBounded_ball

theorem bpzFarBall_nonempty (R : ℝ) : (bpzFarBall R).Nonempty :=
  Metric.nonempty_ball.mpr (by norm_num)

private theorem bpzFarBall_norm_bounds {R : ℝ} (hR : 0 ≤ R) {x : ℂ} (hx : x ∈ bpzFarBall R) :
    R + 3 ≤ ‖x‖ ∧ ‖x‖ ≤ R + 5 := by
  rw [bpzFarBall, Metric.mem_ball, dist_eq_norm] at hx
  have hc : ‖(((R + 4 : ℝ)) : ℂ)‖ = R + 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have h1 := norm_sub_norm_le x (((R + 4 : ℝ)) : ℂ)
  have h2 := norm_sub_norm_le (((R + 4 : ℝ)) : ℂ) x
  rw [norm_sub_rev] at h2
  rw [hc] at h1 h2
  constructor <;> linarith

/-- The softened weight is bounded below on the far disk, uniformly for `‖z‖ ≤ R` and
`0 ≤ ε ≤ 1`. -/
theorem bpzSoftWeight_ge_on_farBall (R : ℝ) (hR : 0 ≤ R) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℂ, ‖z‖ ≤ R → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ x ∈ bpzFarBall R, c ≤ bpzSoftWeight γ χ α₁ α₂ α₃ ε z x := by
  set L : ℝ := (2 * R + 6) ^ 2 + 1 with hL
  have hL1 : 1 ≤ L := by rw [hL]; linarith only [sq_nonneg (2 * R + 6)]
  have hLpos : 0 < L := by linarith
  have hLinv : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL1
  refine ⟨L ^ (-|γ * χ / 2|) * (L ^ (-|-(γ * α₁)|) * L ^ (-|-(γ * α₂)|) *
      L ^ (-|γ * (α₁ + α₂ + α₃ - χ)|)), by positivity, ?_⟩
  intro z hz ε hε0 hε1 x hx
  obtain ⟨hx1, hx2⟩ := bpzFarBall_norm_bounds hR hx
  have hxz1 : R + 3 - R ≤ ‖x - z‖ := by
    have := norm_sub_norm_le x z
    linarith
  have hxz2 : ‖x - z‖ ≤ 2 * R + 5 := by
    have := norm_sub_le x z
    linarith
  have hxo1 : R + 2 ≤ ‖x - 1‖ := by
    have := norm_sub_norm_le x 1
    rw [norm_one] at this
    linarith
  have hxo2 : ‖x - 1‖ ≤ R + 6 := by
    have := norm_sub_le x 1
    rw [norm_one] at this
    linarith
  have hnp : normPlus x = ‖x‖ := max_eq_right (by linarith)
  have hRL : R + 6 ≤ L := by
    rw [hL]
    linarith only [hR, mul_le_mul_of_nonneg_left (by linarith only [hR] : (1 : ℝ) ≤ 2 * R + 6)
      (by linarith only [hR] : (0 : ℝ) ≤ 2 * R + 6)]
  -- the four bases lie in `[1, L]`
  have hb0a : 1 ≤ Complex.normSq (x - z) + ε ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    linarith only [sq_nonneg ε,
      pow_le_pow_left₀ (by linarith only [] : (0 : ℝ) ≤ R + 3 - R) hxz1 2]
  have hb0b : Complex.normSq (x - z) + ε ^ 2 ≤ L := by
    rw [Complex.normSq_eq_norm_sq, hL]
    have h0 : 0 ≤ ‖x - z‖ := norm_nonneg _
    linarith only [pow_le_pow_left₀ h0 hxz2 2, pow_le_one₀ (n := 2) hε0 hε1, hR]
  have f0 := coulombWeight_le_rpow hL1 (le_trans hLinv hb0a) hb0b (γ * χ / 2)
  have f1 := coulombWeight_le_rpow hL1 (le_trans hLinv (by linarith)) (by linarith : ‖x‖ ≤ L)
    (-(γ * α₁))
  have f2 := coulombWeight_le_rpow hL1 (le_trans hLinv (by linarith))
    (by linarith : ‖x - 1‖ ≤ L) (-(γ * α₂))
  have f3 := coulombWeight_le_rpow hL1 (le_trans hLinv (by rw [hnp]; linarith))
    (by rw [hnp]; linarith : normPlus x ≤ L) (γ * (α₁ + α₂ + α₃ - χ))
  unfold bpzSoftWeight bpzBaseWeight
  have p0 : 0 ≤ L ^ (-|γ * χ / 2|) := by positivity
  have p1 : 0 ≤ L ^ (-|-(γ * α₁)|) := by positivity
  have p2 : 0 ≤ L ^ (-|-(γ * α₂)|) := by positivity
  have p3 : 0 ≤ L ^ (-|γ * (α₁ + α₂ + α₃ - χ)|) := by positivity
  have q1 : 0 ≤ ‖x‖ ^ (-(γ * α₁)) := Real.rpow_nonneg (norm_nonneg _) _
  have q2 : 0 ≤ ‖x - 1‖ ^ (-(γ * α₂)) := Real.rpow_nonneg (norm_nonneg _) _
  gcongr

/-- The mass is at least a fixed positive multiple of the chaos mass of the far disk. -/
theorem bpzMass_ge_farBall (R : ℝ) (hR : 0 ≤ R) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℂ, ‖z‖ ≤ R → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ m : Measure ℂ,
      ENNReal.ofReal c * m (bpzFarBall R) ≤ bpzMass γ χ α₁ α₂ α₃ ε m z := by
  obtain ⟨c, hc, hcw⟩ := bpzSoftWeight_ge_on_farBall (γ := γ) (χ := χ) (α₁ := α₁)
    (α₂ := α₂) (α₃ := α₃) R hR
  refine ⟨c, hc, fun z hz ε hε0 hε1 m => ?_⟩
  rw [← setLIntegral_const, bpzMass]
  calc ∫⁻ _x in bpzFarBall R, ENNReal.ofReal c ∂m
      ≤ ∫⁻ x in bpzFarBall R, ENNReal.ofReal (bpzSoftWeight γ χ α₁ α₂ α₃ ε z x) ∂m := by
        apply setLIntegral_mono' (bpzFarBall_measurableSet R)
        intro x hx
        exact ENNReal.ofReal_le_ofReal (hcw z hz ε hε0 hε1 x hx)
    _ ≤ _ := setLIntegral_le_lintegral _ _

/-- Every negative moment of the chaos mass of the far disk is finite. -/
theorem bpz_farBall_negMoment_lt_top
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (R q : ℝ) (hq : 0 ≤ q) :
    ∫⁻ ω, ENNReal.rpow (M ω (bpzFarBall R)) (-q) ∂P < ⊤ := by
  have h := (equatorGFF_GMC_moment_range P X hX γ hγ hγ2 M hM (bpzFarBall R)
    (bpzFarBall_isOpen R) (bpzFarBall_bounded R) (bpzFarBall_nonempty R) (-q)).mpr
    (by have : 0 < 4 / γ ^ 2 := by positivity
        linarith)
  simpa [gmcMassMoment] using h

/-- A lower bound transfers to negative powers. -/
theorem bpz_rpow_neg_le_of_le {a b : ℝ≥0∞} {c : ℝ} (hc : 0 < c) (hb : b ≠ ⊤)
    (hab : ENNReal.ofReal c * b ≤ a) (q : ℝ) (hq : 0 ≤ q) :
    ENNReal.rpow a (-q) ≤ ENNReal.ofReal (c ^ (-q)) * ENNReal.rpow b (-q) := by
  have hcb : (ENNReal.ofReal c * b) ^ (-q) =
      ENNReal.ofReal c ^ (-q) * b ^ (-q) :=
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top hb (-q)
  have hmono : a ^ (-q) ≤ (ENNReal.ofReal c * b) ^ (-q) := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hab hq)
  calc ENNReal.rpow a (-q) = a ^ (-q) := rfl
    _ ≤ (ENNReal.ofReal c * b) ^ (-q) := hmono
    _ = ENNReal.ofReal c ^ (-q) * b ^ (-q) := hcb
    _ = ENNReal.ofReal (c ^ (-q)) * ENNReal.rpow b (-q) := by
        rw [ENNReal.ofReal_rpow_of_pos hc]
        rfl

/-- Uniform finiteness of the negative moments of the mass. -/
theorem bpzMass_negMoment_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (R : ℝ) (hR : 0 ≤ R) (q : ℝ) (hq : 0 ≤ q) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ z : ℂ, ‖z‖ ≤ R → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∫⁻ ω, ENNReal.rpow (bpzMass γ χ α₁ α₂ α₃ ε (M ω) z) (-q) ∂P ≤ B := by
  obtain ⟨c, hc, hlow⟩ := bpzMass_ge_farBall (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂)
    (α₃ := α₃) R hR
  refine ⟨ENNReal.ofReal (c ^ (-q)) *
      ∫⁻ ω, ENNReal.rpow (M ω (bpzFarBall R)) (-q) ∂P,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (bpz_farBall_negMoment_lt_top P X hX hγ hγ2 M hM R q hq), ?_⟩
  intro z hz ε hε0 hε1
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro ω
  have hfin : M ω (bpzFarBall R) ≠ ⊤ := by
    have := hM.1 ω
    exact measure_ne_top _ _
  exact bpz_rpow_neg_le_of_le hc hfin (hlow z hz ε hε0 hε1 (M ω)) q hq

/-- The mass is almost surely positive. -/
theorem bpzMass_pos_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (z : ℂ) :
    ∀ᵐ ω ∂P, 0 < bpzMass γ χ α₁ α₂ α₃ ε (M ω) z := by
  set R : ℝ := ‖z‖
  obtain ⟨c, hc, hlow⟩ := bpzMass_ge_farBall (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂)
    (α₃ := α₃) R (norm_nonneg z)
  have hfin := bpz_farBall_negMoment_lt_top P X hX hγ hγ2 M hM R 1 zero_le_one
  have hmeas : AEMeasurable (fun ω => M ω (bpzFarBall R)) P :=
    gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM _ (bpzFarBall_measurableSet R)
  have hfin' : ∫⁻ ω, M ω (bpzFarBall R) ^ (-1 : ℝ) ∂P ≠ ⊤ := hfin.ne
  have hae : ∀ᵐ ω ∂P, M ω (bpzFarBall R) ^ (-1 : ℝ) < ⊤ :=
    ae_lt_top' (hmeas.pow_const _) hfin'
  filter_upwards [hae] with ω hω
  have hpos : M ω (bpzFarBall R) ≠ 0 := by
    intro h0
    rw [h0] at hω
    simp [ENNReal.zero_rpow_of_neg] at hω
  refine lt_of_lt_of_le ?_ (hlow z le_rfl ε hε0 hε1 (M ω))
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hc).ne' hpos |>.bot_lt

/-- The base factor is the Coulomb weight of the two finite charges and the shifted charge at
infinity. -/
theorem coulombWeight_two_eq_ofReal_bpzBaseWeight {x : ℂ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    coulombWeight γ ![α₁, α₂] ![0, 1] (α₃ - χ) x =
      ENNReal.ofReal (bpzBaseWeight γ χ α₁ α₂ α₃ x) := by
  have hn : 0 < normPlus x := bpz_normPlus_pos x
  have h₁ : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have h₂ : 0 < ‖x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx1)
  unfold coulombWeight
  simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.prod_univ_zero, mul_one, sub_zero]
  change ((ENNReal.ofReal (normPlus x / ‖x‖)) ^ (γ * α₁) *
      (ENNReal.ofReal (normPlus x / ‖x - 1‖)) ^ (γ * α₂)) *
      (ENNReal.ofReal (normPlus x)) ^ (γ * (α₃ - χ)) = _
  rw [ENNReal.ofReal_rpow_of_pos (div_pos hn h₁), ENNReal.ofReal_rpow_of_pos (div_pos hn h₂),
    ENNReal.ofReal_rpow_of_pos hn,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (div_pos hn h₁).le _),
    ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (div_pos hn h₁).le _)
      (Real.rpow_nonneg (div_pos hn h₂).le _))]
  congr 1
  unfold bpzBaseWeight
  rw [Real.div_rpow hn.le h₁.le, Real.div_rpow hn.le h₂.le, Real.rpow_neg h₁.le,
    Real.rpow_neg h₂.le,
    show γ * (α₁ + α₂ + α₃ - χ) = γ * α₁ + (γ * α₂ + γ * (α₃ - χ)) by ring,
    Real.rpow_add hn, Real.rpow_add hn]
  field_simp

/-- The power-`2a` subadditivity used to compare softened and unsoftened weights. -/
theorem bpz_add_rpow_le (u v a : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (ha : 0 ≤ a) :
    (u + v) ^ a ≤ 2 ^ a * (u ^ a + v ^ a) := by
  have hmax : u + v ≤ 2 * max u v := by
    rcases le_total u v with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  calc (u + v) ^ a ≤ (2 * max u v) ^ a :=
        Real.rpow_le_rpow (add_nonneg hu hv) hmax ha
    _ = 2 ^ a * (max u v) ^ a := Real.mul_rpow (by norm_num) (le_max_of_le_left hu)
    _ ≤ 2 ^ a * (u ^ a + v ^ a) := by
        gcongr
        rcases le_total u v with h | h
        · rw [max_eq_right h]
          have := Real.rpow_nonneg hu a
          linarith
        · rw [max_eq_left h]
          have := Real.rpow_nonneg hv a
          linarith

/-- The softened weight is bounded by the unsoftened weight plus a multiple of the base. -/
theorem bpzSoftWeight_le (hγχ : 0 ≤ γ * χ) (ε : ℝ) (z x : ℂ) :
    bpzSoftWeight γ χ α₁ α₂ α₃ ε z x ≤
      2 ^ (γ * χ / 2) * (bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x +
        (ε ^ 2) ^ (γ * χ / 2) * bpzBaseWeight γ χ α₁ α₂ α₃ x) := by
  have hb := bpzBaseWeight_nonneg (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) x
  have hle := bpz_add_rpow_le (Complex.normSq (x - z)) (ε ^ 2) (γ * χ / 2)
    (Complex.normSq_nonneg _) (sq_nonneg ε) (by linarith)
  unfold bpzSoftWeight
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero]
  calc (Complex.normSq (x - z) + ε ^ 2) ^ (γ * χ / 2) * bpzBaseWeight γ χ α₁ α₂ α₃ x
      ≤ 2 ^ (γ * χ / 2) * (Complex.normSq (x - z) ^ (γ * χ / 2) + (ε ^ 2) ^ (γ * χ / 2)) *
          bpzBaseWeight γ χ α₁ α₂ α₃ x := mul_le_mul_of_nonneg_right hle hb
    _ = _ := by ring

/-- The reduced four-point function, written with the real degenerate weight. -/
theorem fourPointT_eq_bpzMass
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (μ : ℝ) (z : ℂ) :
    fourPointT P M γ μ (-χ) α₁ α₂ α₃ z =
      2 * μ ^ (-fourPointSExp γ (-χ) α₁ α₂ α₃) / γ *
        Real.Gamma (fourPointSExp γ (-χ) α₁ α₂ α₃) *
        (∫⁻ ω, ENNReal.rpow (bpzMass γ χ α₁ α₂ α₃ 0 (M ω) z)
          (-fourPointSExp γ (-χ) α₁ α₂ α₃) ∂P).toReal := by
  unfold fourPointT
  congr 2
  apply lintegral_congr_ae
  filter_upwards [gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM z,
    gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 0,
    gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 1] with ω hz h0 h1
  rw [coulombMass_eq_lintegral_bpzSoftWeight (M ω) z hz h0 h1]
  rfl

private theorem bpz_ae_lt_top_of_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → ℝ≥0∞} (hY : AEMeasurable Y P)
    {t : ℝ} (ht : 0 < t) (hfin : ∫⁻ ω, ENNReal.rpow (Y ω) t ∂P < ⊤) : ∀ᵐ ω ∂P, Y ω < ⊤ := by
  have hfin' : ∫⁻ ω, Y ω ^ t ∂P ≠ ⊤ := hfin.ne
  filter_upwards [ae_lt_top' (hY.pow_const t) hfin'] with ω hω
  by_contra h
  rw [not_lt, top_le_iff] at h
  rw [h, ENNReal.top_rpow_of_pos ht] at hω
  exact lt_irrefl _ hω

/-- For a measure without atoms at `0` and `1`, the integral of the base factor is a two-root
Coulomb mass. -/
theorem coulombMass_two_eq_lintegral_bpzBaseWeight (μ : Measure ℂ) (h0 : μ {0} = 0)
    (h1 : μ {1} = 0) :
    coulombMass γ μ ![α₁, α₂] ![0, 1] (α₃ - χ) =
      ∫⁻ x, ENNReal.ofReal (bpzBaseWeight γ χ α₁ α₂ α₃ x) ∂μ := by
  rw [coulombMass_eq_lintegral_coulombWeight]
  apply lintegral_congr_ae
  have h0' : ∀ᵐ x ∂μ, x ≠ 0 := by apply ae_iff.mpr; simpa using h0
  have h1' : ∀ᵐ x ∂μ, x ≠ 1 := by apply ae_iff.mpr; simpa using h1
  filter_upwards [h0', h1'] with x hx0 hx1
  exact coulombWeight_two_eq_ofReal_bpzBaseWeight hx0 hx1

theorem bpz_injective_three {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    Function.Injective ![z, (0 : ℂ), 1] := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | (exfalso; revert hij; simp [hz0, hz1, eq_comm])

theorem bpz_injective_two : Function.Injective ![(0 : ℂ), 1] := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | (exfalso; revert hij; simp)

/-- A positive order below six positive bounds. -/
theorem bpz_exists_pos_lt_six {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f) :
    ∃ t : ℝ, 0 < t ∧ t < a ∧ t < b ∧ t < c ∧ t < d ∧ t < e ∧ t < f := by
  refine ⟨min a (min b (min c (min d (min e f)))) / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : 0 < min a (min b (min c (min d (min e f)))) := by
      simp only [lt_min_iff]; exact ⟨ha, hb, hc, hd, he, hf⟩
    linarith
  all_goals
    have h0 : 0 < min a (min b (min c (min d (min e f)))) := by
      simp only [lt_min_iff]; exact ⟨ha, hb, hc, hd, he, hf⟩
  · have := min_le_left a (min b (min c (min d (min e f)))); linarith
  · have := (min_le_right a _).trans (min_le_left b (min c (min d (min e f)))); linarith
  · have := (min_le_right a _).trans ((min_le_right b _).trans
      (min_le_left c (min d (min e f)))); linarith
  · have := (min_le_right a _).trans ((min_le_right b _).trans ((min_le_right c _).trans
      (min_le_left d (min e f)))); linarith
  · have := (min_le_right a _).trans ((min_le_right b _).trans ((min_le_right c _).trans
      ((min_le_right d _).trans (min_le_left e f)))); linarith
  · have := (min_le_right a _).trans ((min_le_right b _).trans ((min_le_right c _).trans
      ((min_le_right d _).trans (min_le_right e f)))); linarith

/-- The degenerate four-point mass is almost surely finite. -/
theorem bpzMass_lt_top_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (hχ : 0 < χ) (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (ε : ℝ) (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    ∀ᵐ ω ∂P, bpzMass γ χ α₁ α₂ α₃ ε (M ω) z < ⊤ := by
  have hQ : 0 < Q γ := by unfold Q; positivity
  have hg : 0 < 2 / γ := by positivity
  obtain ⟨t, htpos, ht1, ht2, ht3, ht4, ht5, ht6⟩ := bpz_exists_pos_lt_six
    (by positivity : (0 : ℝ) < 4 / γ ^ 2)
    (mul_pos hg (by linarith) : 0 < 2 / γ * (Q γ - -χ))
    (mul_pos hg (by linarith) : 0 < 2 / γ * (Q γ - α₁))
    (mul_pos hg (by linarith) : 0 < 2 / γ * (Q γ - α₂))
    (mul_pos hg (by linarith) : 0 < 2 / γ * (Q γ - α₃))
    (mul_pos hg (by linarith) : 0 < 2 / γ * (Q γ - (α₃ - χ)))
  -- the three-root Coulomb mass is almost surely finite
  have hinj3 := bpz_injective_three hz0 hz1
  have hmom3 := coulombMass_moment_lt_top_of_pos P X hX γ hγ hγ2 M hM ![z, 0, 1] hinj3
    ![-χ, α₁, α₂] α₃ t htpos ht1
    (fun k => by fin_cases k <;> simp <;> linarith) ht5
  have hfin3 := bpz_ae_lt_top_of_moment
    (gmc_coulombMass_aemeasurable P X hX γ hγ hγ2 M hM ![-χ, α₁, α₂] ![z, 0, 1] α₃) htpos hmom3
  -- the two-root Coulomb mass is almost surely finite
  have hinj2 := bpz_injective_two
  have hmom2 := coulombMass_moment_lt_top_of_pos P X hX γ hγ hγ2 M hM ![0, 1] hinj2
    ![α₁, α₂] (α₃ - χ) t htpos ht1
    (fun k => by fin_cases k <;> simpa) ht6
  have hfin2 := bpz_ae_lt_top_of_moment
    (gmc_coulombMass_aemeasurable P X hX γ hγ hγ2 M hM ![α₁, α₂] ![0, 1] (α₃ - χ)) htpos hmom2
  filter_upwards [hfin3, hfin2, gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM z,
    gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 0,
    gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 1] with ω h3 h2 hz h0 h1
  rw [coulombMass_eq_lintegral_bpzSoftWeight (M ω) z hz h0 h1] at h3
  rw [coulombMass_two_eq_lintegral_bpzBaseWeight (M ω) h0 h1] at h2
  have hγχ : 0 ≤ γ * χ := by positivity
  set A : ℝ := 2 ^ (γ * χ / 2)
  set c : ℝ := (ε ^ 2) ^ (γ * χ / 2)
  have hA : 0 ≤ A := by positivity
  have hc : 0 ≤ c := Real.rpow_nonneg (sq_nonneg ε) _
  have hm0 : Measurable fun x => ENNReal.ofReal (bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x) :=
    ENNReal.measurable_ofReal.comp (measurable_bpzSoftWeight 0 z)
  have hmb : Measurable fun x => ENNReal.ofReal (bpzBaseWeight γ χ α₁ α₂ α₃ x) :=
    ENNReal.measurable_ofReal.comp measurable_bpzBaseWeight
  calc bpzMass γ χ α₁ α₂ α₃ ε (M ω) z
      ≤ ∫⁻ x, ENNReal.ofReal A * (ENNReal.ofReal (bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x) +
          ENNReal.ofReal c * ENNReal.ofReal (bpzBaseWeight γ χ α₁ α₂ α₃ x)) ∂M ω := by
        apply lintegral_mono
        intro x
        beta_reduce
        rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_add (bpzSoftWeight_nonneg 0 z x)
          (mul_nonneg hc (bpzBaseWeight_nonneg x)), ← ENNReal.ofReal_mul hA]
        exact ENNReal.ofReal_le_ofReal (bpzSoftWeight_le hγχ ε z x)
    _ = ENNReal.ofReal A * (∫⁻ x, ENNReal.ofReal (bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x) ∂M ω +
          ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (bpzBaseWeight γ χ α₁ α₂ α₃ x) ∂M ω) := by
        have hsum : Measurable fun x => ENNReal.ofReal (bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x) +
            ENNReal.ofReal c * ENNReal.ofReal (bpzBaseWeight γ χ α₁ α₂ α₃ x) :=
          hm0.add (hmb.const_mul _)
        rw [lintegral_const_mul _ hsum, lintegral_add_left hm0, lintegral_const_mul _ hmb]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.add_lt_top.mpr ⟨h3, ENNReal.mul_lt_top ENNReal.ofReal_lt_top h2⟩)

end DOZZ.Proofs
