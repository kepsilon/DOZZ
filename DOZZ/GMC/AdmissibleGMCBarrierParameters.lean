/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.GaussianTailBound

/-! Robust subcritical barrier parameters for the admissible mixed-root estimate. -/

@[expose] public section

namespace DOZZ.Proofs

/-- A subcritical charge admits a barrier exponent with room for the covariance-error parameter
in the two-root Gaussian tail estimate. -/
theorem exists_fixed_charge_robust_barrier_parameters
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ a κ η : ℝ, γ < a ∧ a < 2 * γ ∧ 0 < κ ∧ κ < 2 ∧
      0 < η ∧ η < 1 ∧
      γ ^ 2 - ((1 - η) ^ 2 * (2 * γ - a) ^ 2 / (2 * (1 + η))) ≤ κ := by
  obtain ⟨a, κ₀, hγa, ha2, hκeq, hκ₀pos, hκ₀lt⟩ :=
    exists_fixed_charge_barrier_parameters γ hγ hγ2
  let κ : ℝ := (κ₀ + 2) / 2
  have hκ₀κ : κ₀ < κ := by dsimp [κ]; linarith
  have hκpos : 0 < κ := by dsimp [κ]; linarith
  have hκlt : κ < 2 := by dsimp [κ]; linarith
  let b : ℝ := 2 * γ - a
  have hb : 0 < b := by dsimp [b]; linarith
  let gap : ℝ := κ - κ₀
  have hgap : 0 < gap := by dsimp [gap]; linarith
  let η : ℝ := min (1 / 2) (gap / (3 * b ^ 2))
  have hηpos : 0 < η := by
    dsimp [η]
    exact lt_min (by norm_num) (div_pos hgap (by positivity))
  have hηhalf : η ≤ 1 / 2 := min_le_left _ _
  have hηgap : η ≤ gap / (3 * b ^ 2) := min_le_right _ _
  have hηlt : η < 1 := lt_of_le_of_lt hηhalf (by norm_num)
  have hfrac : (3 * η - η ^ 2) / (2 * (1 + η)) ≤ 3 * η / 2 := by
    rw [div_le_iff₀ (by positivity : 0 < 2 * (1 + η))]
    nlinarith [sq_nonneg η]
  have hηerr : η * (3 * b ^ 2 / 2) ≤ gap / 2 := by
    calc
      η * (3 * b ^ 2 / 2) ≤ (gap / (3 * b ^ 2)) * (3 * b ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right hηgap (by positivity)
      _ = gap / 2 := by
        have hb2 : b ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hb)
        field_simp
  have hidentity : γ ^ 2 -
      ((1 - η) ^ 2 * b ^ 2 / (2 * (1 + η))) =
        κ₀ + b ^ 2 * ((3 * η - η ^ 2) / (2 * (1 + η))) := by
    have hden : 1 + η ≠ 0 := ne_of_gt (by positivity)
    rw [hκeq]
    dsimp [b]
    field_simp
    ring
  refine ⟨a, κ, η, hγa, ha2, hκpos, hκlt, hηpos, hηlt, ?_⟩
  rw [show (2 * γ - a) ^ 2 = b ^ 2 by rfl]
  rw [hidentity]
  calc
    κ₀ + b ^ 2 * ((3 * η - η ^ 2) / (2 * (1 + η))) ≤
        κ₀ + b ^ 2 * (3 * η / 2) := by
          simpa [add_comm] using add_le_add_left
            (mul_le_mul_of_nonneg_left hfrac (sq_nonneg b)) κ₀
    _ = κ₀ + η * (3 * b ^ 2 / 2) := by ring
    _ ≤ κ₀ + gap / 2 := by simpa [add_comm] using add_le_add_left hηerr κ₀
    _ ≤ κ := by dsimp [gap]; linarith

/-- Beyond one natural scale, all linear error conditions for a fixed two-root barrier hold and
the coarse radius is below the admissible cutoff. -/
theorem exists_natural_scale_after_covariance_errors
    (C γ η b cutoff : ℝ) (hC : 0 ≤ C) (hγ : 0 < γ) (hη : 0 < η)
    (hb : 0 < b) (hcutoff : 0 < cutoff) :
    ∃ k₀ : ℕ, Real.exp (-(k₀ : ℝ)) ≤ cutoff ∧
      C < (k₀ : ℝ) ∧ C ≤ η * (k₀ : ℝ) ∧
        2 * γ * C + 1 ≤ η * b * (k₀ : ℝ) := by
  let T₁ : ℝ := max 0 (Real.log (1 / cutoff))
  let T₂ : ℝ := max (C + 1) (C / η + 1)
  let T₃ : ℝ := max ((2 * γ * C + 1) / (η * b) + 1) T₁
  let T : ℝ := max T₂ T₃
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt T
  have hT₂ : T₂ ≤ T := le_max_left _ _
  have hT₃ : T₃ ≤ T := le_max_right _ _
  have hCplus : C + 1 ≤ T := le_trans (le_max_left _ _) hT₂
  have hCrate : C / η + 1 ≤ T := le_trans (le_max_right _ _) hT₂
  have hoffset : (2 * γ * C + 1) / (η * b) + 1 ≤ T :=
    le_trans (le_max_left _ _) hT₃
  have hlog : Real.log (1 / cutoff) ≤ T :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hT₃)
  have hTnonneg : 0 ≤ T := by
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hT₃)
  have hkreal : T < (k₀ : ℝ) := hk₀
  have hkC : C < (k₀ : ℝ) := by linarith
  have hkCrate : C / η < (k₀ : ℝ) := by linarith
  have hkoffset : (2 * γ * C + 1) / (η * b) < (k₀ : ℝ) := by linarith
  have hkcut : Real.exp (-(k₀ : ℝ)) ≤ cutoff := by
    by_cases hcutoff1 : cutoff < 1
    · have hdiv : 1 < 1 / cutoff := by
        rw [one_lt_div₀ hcutoff]
        exact hcutoff1
      have hlogpos : 0 < Real.log (1 / cutoff) := Real.log_pos hdiv
      have hklog : Real.log (1 / cutoff) < (k₀ : ℝ) := lt_of_le_of_lt hlog hkreal
      have hexp : Real.exp (-Real.log (1 / cutoff)) = cutoff := by
        rw [Real.exp_neg, Real.exp_log (by positivity : 0 < (1 / cutoff : ℝ))]
        field_simp
      exact le_of_lt <| calc
        Real.exp (-(k₀ : ℝ)) < Real.exp (-Real.log (1 / cutoff)) :=
          Real.exp_lt_exp.mpr (by linarith)
        _ = cutoff := hexp
    · have hcutoffge : 1 ≤ cutoff := le_of_not_gt hcutoff1
      exact (Real.exp_le_one_iff.mpr
        (neg_nonpos.mpr (Nat.cast_nonneg k₀))).trans hcutoffge
  refine ⟨k₀, hkcut, hkC, ?_, ?_⟩
  · have hmul : η * (C / η) < η * (k₀ : ℝ) := mul_lt_mul_of_pos_left hkCrate hη
    have hcancel : η * (C / η) = C := by field_simp
    linarith
  · have hmul := mul_lt_mul_of_pos_left hkoffset (mul_pos hη hb)
    have hcancel : (η * b) * ((2 * γ * C + 1) / (η * b)) = 2 * γ * C + 1 := by
      field_simp
    have hstrict : 2 * γ * C + 1 < η * b * (k₀ : ℝ) := by
      calc
        2 * γ * C + 1 = (η * b) * ((2 * γ * C + 1) / (η * b)) := hcancel.symm
        _ < (η * b) * (k₀ : ℝ) := hmul
        _ = η * b * (k₀ : ℝ) := by ring
    exact le_of_lt hstrict


end DOZZ.Proofs
