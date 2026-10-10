/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.WhiteNoise.Haar.Basic

/-!
# GaussianFields Haar one dimensional refinements

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace

namespace GaussianFields

/-- The normalized one-dimensional Haar packet at scale `j`, cell `k`, and signature `signature`. -/
@[expose]
noncomputable def haar1D (j : ℤ) (k : ℤ) (signature : Bool) : ℝ → ℝ :=
  fun x => haarScaleFactor j * haarAtom1D signature (dyadicPower j * x - (k : ℝ))

/-- The one-dimensional dyadic interval supporting the father packet at scale `j` and cell `k`. -/
@[expose]
def dyadicInterval (j k : ℤ) : Set ℝ :=
  Set.Ico ((k : ℝ) / dyadicPower j) (((k : ℝ) + 1) / dyadicPower j)

theorem mem_dyadicInterval_iff (j k : ℤ) (x : ℝ) :
    x ∈ dyadicInterval j k ↔
      dyadicPower j * x - (k : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by
  let a := dyadicPower j
  have ha : 0 < a := dyadicPower_pos j
  have hane : a ≠ 0 := ne_of_gt ha
  constructor
  · intro hx
    constructor
    · have hmul := mul_le_mul_of_nonneg_left hx.1 ha.le
      have hk : a * ((k : ℝ) / a) = (k : ℝ) := by
        field_simp [hane]
      linarith
    · have hmul := mul_lt_mul_of_pos_left hx.2 ha
      have hk : a * (((k : ℝ) + 1) / a) = (k : ℝ) + 1 := by
        field_simp [hane]
      linarith
  · intro hx
    constructor
    · have hle : (k : ℝ) ≤ a * x := by linarith [hx.1]
      exact (div_le_iff₀ ha).2 (by simpa [mul_comm] using hle)
    · have hlt : a * x < (k : ℝ) + 1 := by linarith [hx.2]
      exact (lt_div_iff₀ ha).2 (by simpa [mul_comm] using hlt)

theorem measurableSet_dyadicInterval (j k : ℤ) :
    MeasurableSet (dyadicInterval j k) := by
  unfold dyadicInterval
  exact measurableSet_Ico

theorem volume_dyadicInterval_ne_top (j k : ℤ) :
    volume (dyadicInterval j k) ≠ ∞ := by
  unfold dyadicInterval
  exact ne_of_lt measure_Ico_lt_top

theorem haar1D_father_eq_indicator_dyadicInterval (j k : ℤ) (x : ℝ) :
    haar1D j k false x =
      haarScaleFactor j *
        Set.indicator (dyadicInterval j k) (fun _ : ℝ => (1 : ℝ)) x := by
  unfold haar1D haarAtom1D haarFather1D
  by_cases hx : x ∈ dyadicInterval j k
  · have hx' : dyadicPower j * x - (k : ℝ) ∈ Set.Ico (0 : ℝ) 1 :=
      (mem_dyadicInterval_iff j k x).1 hx
    simp [hx, hx']
  · have hx' : dyadicPower j * x - (k : ℝ) ∉ Set.Ico (0 : ℝ) 1 :=
      mt (mem_dyadicInterval_iff j k x).2 hx
    simp [hx, hx']

@[fun_prop]
theorem measurable_haar1D (j : ℤ) (k : ℤ) (signature : Bool) :
    Measurable (haar1D j k signature) := by
  unfold haar1D
  exact measurable_const.mul
    ((measurable_haarAtom1D signature).comp (by fun_prop))

theorem integrable_haarFather1D_affine (j k : ℤ) :
    Integrable (fun x : ℝ => haarFather1D (dyadicPower j * x - (k : ℝ)))
      (volume : Measure ℝ) := by
  have hshift :
      Integrable (fun y : ℝ => haarFather1D (y - (k : ℝ))) (volume : Measure ℝ) := by
    simpa [sub_eq_add_neg] using integrable_haarFather1D.comp_add_right (-(k : ℝ))
  simpa [sub_eq_add_neg] using hshift.comp_mul_left' (dyadicPower_ne_zero j)

theorem integral_haarFather1D_affine (j k : ℤ) :
    ∫ x : ℝ, haarFather1D (dyadicPower j * x - (k : ℝ)) ∂volume =
      (dyadicPower j)⁻¹ := by
  have h :=
    integral_comp_mul_add_volume
      (a := dyadicPower j) (b := -(k : ℝ))
      (dyadicPower_ne_zero j) haarFather1D integrable_haarFather1D
  rw [integral_haarFather1D] at h
  have hpos : 0 < dyadicPower j := dyadicPower_pos j
  simpa [sub_eq_add_neg, abs_of_pos (inv_pos.mpr hpos)] using h

theorem integral_haarAtom1D_affine (j k : ℤ) (signature : Bool) :
    ∫ x : ℝ, haarAtom1D signature (dyadicPower j * x - (k : ℝ)) ∂volume =
      (dyadicPower j)⁻¹ * ∫ y : ℝ, haarAtom1D signature y ∂volume := by
  have h := integral_comp_mul_add_volume
    (a := dyadicPower j) (b := -(k : ℝ))
    (dyadicPower_ne_zero j) (haarAtom1D signature) (integrable_haarAtom1D signature)
  have hpos : 0 < dyadicPower j := dyadicPower_pos j
  simpa [sub_eq_add_neg, abs_of_pos (inv_pos.mpr hpos)] using h

theorem integral_haar1D (j k : ℤ) (signature : Bool) :
    ∫ x : ℝ, haar1D j k signature x ∂volume =
      if signature then 0 else haarScaleFactor j * (dyadicPower j)⁻¹ := by
  cases signature
  · unfold haar1D
    rw [integral_const_mul, integral_haarAtom1D_affine]
    simp [haarAtom1D, integral_haarFather1D]
  · unfold haar1D
    rw [integral_const_mul, integral_haarAtom1D_affine]
    simp [haarAtom1D, integral_haarMother1D]

theorem integral_haar1D_mother (j k : ℤ) :
    ∫ x : ℝ, haar1D j k true x ∂volume = 0 := by
  simpa using integral_haar1D j k true

theorem haar1D_sq (j k : ℤ) (signature : Bool) (x : ℝ) :
    haar1D j k signature x ^ (2 : Nat) =
      dyadicPower j * haarFather1D (dyadicPower j * x - (k : ℝ)) := by
  unfold haar1D
  rw [mul_pow, haarAtom1D_sq, haarScaleFactor_sq]

theorem integrable_haar1D_sq (j k : ℤ) (signature : Bool) :
    Integrable (fun x : ℝ => haar1D j k signature x ^ (2 : Nat))
      (volume : Measure ℝ) := by
  refine ((integrable_haarFather1D_affine j k).const_mul (dyadicPower j)).congr
    (ae_of_all _ ?_)
  intro x
  exact (haar1D_sq j k signature x).symm

theorem memLp_haar1D (j k : ℤ) (signature : Bool) :
    MemLp (haar1D j k signature) 2 (volume : Measure ℝ) := by
  rw [memLp_two_iff_integrable_sq]
  · exact integrable_haar1D_sq j k signature
  · exact (measurable_haar1D j k signature).aestronglyMeasurable

/-- The one-dimensional Haar packet as an `L²` vector. -/
@[expose]
noncomputable def haar1DLp (j k : ℤ) (signature : Bool) :
    Lp ℝ 2 (volume : Measure ℝ) :=
  (memLp_haar1D j k signature).toLp (haar1D j k signature)

theorem integral_haar1D_mul_self (j k : ℤ) (signature : Bool) :
    ∫ x : ℝ, haar1D j k signature x * haar1D j k signature x ∂volume = 1 := by
  calc
    ∫ x : ℝ, haar1D j k signature x * haar1D j k signature x ∂volume =
        ∫ x : ℝ, dyadicPower j *
          haarFather1D (dyadicPower j * x - (k : ℝ)) ∂volume := by
          refine integral_congr_ae (ae_of_all _ ?_)
          intro x
          change haar1D j k signature x * haar1D j k signature x =
            dyadicPower j * haarFather1D (dyadicPower j * x - (k : ℝ))
          rw [← pow_two, haar1D_sq]
    _ = dyadicPower j *
        ∫ x : ℝ, haarFather1D (dyadicPower j * x - (k : ℝ)) ∂volume := by
          rw [integral_const_mul]
    _ = 1 := by
          rw [integral_haarFather1D_affine]
          exact mul_inv_cancel₀ (dyadicPower_ne_zero j)

theorem haar1D_mul_haar1D_same_scale_cell (j k : ℤ)
    (signature₁ signature₂ : Bool) (x : ℝ) :
    haar1D j k signature₁ x * haar1D j k signature₂ x =
      dyadicPower j *
        (haarAtom1D signature₁ (dyadicPower j * x - (k : ℝ)) *
          haarAtom1D signature₂ (dyadicPower j * x - (k : ℝ))) := by
  unfold haar1D
  rw [← haarScaleFactor_sq]
  ring

theorem integral_haar1D_mul_haar1D_same_scale_cell (j k : ℤ)
    (signature₁ signature₂ : Bool) :
    ∫ x : ℝ, haar1D j k signature₁ x * haar1D j k signature₂ x ∂volume =
      if signature₁ = signature₂ then 1 else 0 := by
  let f : ℝ → ℝ := fun y => haarAtom1D signature₁ y * haarAtom1D signature₂ y
  have hbase :
      ∫ y : ℝ, f y ∂volume = if signature₁ = signature₂ then 1 else 0 := by
    exact integral_haarAtom1D_mul_haarAtom1D signature₁ signature₂
  have haffine :
      ∫ x : ℝ, f (dyadicPower j * x - (k : ℝ)) ∂volume =
        (dyadicPower j)⁻¹ * ∫ y : ℝ, f y ∂volume := by
    have h := integral_comp_mul_add_volume
      (a := dyadicPower j) (b := -(k : ℝ))
      (dyadicPower_ne_zero j) f
      (integrable_haarAtom1D_mul_haarAtom1D signature₁ signature₂)
    have hpos : 0 < dyadicPower j := dyadicPower_pos j
    simpa [sub_eq_add_neg, abs_of_pos (inv_pos.mpr hpos), f] using h
  calc
    ∫ x : ℝ, haar1D j k signature₁ x * haar1D j k signature₂ x ∂volume =
        ∫ x : ℝ, dyadicPower j * f (dyadicPower j * x - (k : ℝ)) ∂volume := by
          refine integral_congr_ae (ae_of_all _ ?_)
          intro x
          change haar1D j k signature₁ x * haar1D j k signature₂ x =
            dyadicPower j * f (dyadicPower j * x - (k : ℝ))
          rw [haar1D_mul_haar1D_same_scale_cell]
    _ = dyadicPower j *
        ∫ x : ℝ, f (dyadicPower j * x - (k : ℝ)) ∂volume := by
          rw [integral_const_mul]
    _ = if signature₁ = signature₂ then 1 else 0 := by
          rw [haffine, hbase]
          by_cases hsig : signature₁ = signature₂
          · simp [hsig, mul_inv_cancel₀ (dyadicPower_ne_zero j)]
          · simp [hsig]

/-- One-dimensional Haar atoms at the same scale but in distinct cells have pointwise-zero
product. -/
theorem haar1D_mul_haar1D_same_scale_cell_ne (j k₁ k₂ : ℤ)
    (signature₁ signature₂ : Bool) (hk : k₁ ≠ k₂) (x : ℝ) :
    haar1D j k₁ signature₁ x * haar1D j k₂ signature₂ x = 0 := by
  unfold haar1D
  let a₁ := haarAtom1D signature₁ (dyadicPower j * x - (k₁ : ℝ))
  let a₂ := haarAtom1D signature₂ (dyadicPower j * x - (k₂ : ℝ))
  have hprod : a₁ * a₂ = 0 := by
    exact haarAtom1D_mul_eq_zero_of_cells_ne signature₁ signature₂
      (z := dyadicPower j * x) hk
  calc
    haarScaleFactor j * a₁ * (haarScaleFactor j * a₂) =
        haarScaleFactor j * haarScaleFactor j * (a₁ * a₂) := by ring
    _ = 0 := by rw [hprod, mul_zero]

/-- One-dimensional Haar atoms at the same scale but in distinct cells are orthogonal. -/
theorem integral_haar1D_mul_haar1D_same_scale_cell_ne (j k₁ k₂ : ℤ)
    (signature₁ signature₂ : Bool) (hk : k₁ ≠ k₂) :
    ∫ x : ℝ, haar1D j k₁ signature₁ x * haar1D j k₂ signature₂ x ∂volume = 0 := by
  calc
    ∫ x : ℝ, haar1D j k₁ signature₁ x * haar1D j k₂ signature₂ x ∂volume =
        ∫ x : ℝ, 0 ∂volume := by
          refine integral_congr_ae (ae_of_all _ ?_)
          intro x
          exact haar1D_mul_haar1D_same_scale_cell_ne j k₁ k₂
            signature₁ signature₂ hk x
    _ = 0 := by simp

/-- Same-scale one-dimensional Haar inner products reduce to equality of cells and signatures. -/
theorem integral_haar1D_mul_haar1D_same_scale (j k₁ k₂ : ℤ)
    (signature₁ signature₂ : Bool) :
    ∫ x : ℝ, haar1D j k₁ signature₁ x * haar1D j k₂ signature₂ x ∂volume =
      if k₁ = k₂ then if signature₁ = signature₂ then 1 else 0 else 0 := by
  by_cases hk : k₁ = k₂
  · subst k₂
    rw [ite_eq_left rfl]
    exact integral_haar1D_mul_haar1D_same_scale_cell j k₁ signature₁ signature₂
  · rw [ite_eq_right hk]
    exact integral_haar1D_mul_haar1D_same_scale_cell_ne j k₁ k₂
      signature₁ signature₂ hk

/-- Same-scale one-dimensional Haar `L²` inner products reduce to equality of cells and
signatures. -/
theorem inner_haar1DLp_same_scale (j k₁ k₂ : ℤ)
    (signature₁ signature₂ : Bool) :
    ⟪haar1DLp j k₁ signature₁, haar1DLp j k₂ signature₂⟫_ℝ =
      if k₁ = k₂ then if signature₁ = signature₂ then 1 else 0 else 0 := by
  rw [haar1DLp, haar1DLp, MeasureTheory.L2.inner_def]
  calc
    ∫ x : ℝ,
        inner (𝕜 := ℝ)
          ((memLp_haar1D j k₁ signature₁).toLp (haar1D j k₁ signature₁) x)
          ((memLp_haar1D j k₂ signature₂).toLp (haar1D j k₂ signature₂) x)
        ∂volume =
        ∫ x : ℝ, haar1D j k₁ signature₁ x * haar1D j k₂ signature₂ x ∂volume := by
          refine integral_congr_ae ?_
          filter_upwards [(memLp_haar1D j k₁ signature₁).coeFn_toLp,
            (memLp_haar1D j k₂ signature₂).coeFn_toLp] with x hx₁ hx₂
          simp [hx₁, hx₂, mul_comm]
    _ = if k₁ = k₂ then if signature₁ = signature₂ then 1 else 0 else 0 :=
      integral_haar1D_mul_haar1D_same_scale j k₁ k₂ signature₁ signature₂

theorem haar1D_left_child_arg (j k : ℤ) (x : ℝ) :
    dyadicPower (j + 1) * x - 2 * (k : ℝ) =
      2 * (dyadicPower j * x - (k : ℝ)) := by
  rw [dyadicPower_add_one]
  ring

theorem haar1D_right_child_arg (j k : ℤ) (x : ℝ) :
    dyadicPower (j + 1) * x - (2 * (k : ℝ) + 1) =
      2 * (dyadicPower j * x - (k : ℝ)) - 1 := by
  rw [dyadicPower_add_one]
  ring

/-- The normalized father packet is the normalized sum of its two next-scale father children. -/
theorem haar1D_father_refine (j k : ℤ) (x : ℝ) :
    haar1D j k false x =
      (Real.sqrt 2)⁻¹ *
        (haar1D (j + 1) ((2 : ℤ) * k) false x +
          haar1D (j + 1) ((2 : ℤ) * k + 1) false x) := by
  unfold haar1D
  simp [haarAtom1D]
  rw [haar1D_left_child_arg, haar1D_right_child_arg]
  rw [haarFather1D_refine (dyadicPower j * x - (k : ℝ))]
  rw [haarScaleFactor_add_one]
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hsqrt]

/-- The normalized mother packet is the normalized difference of the two next-scale father
children. -/
theorem haar1D_mother_refine (j k : ℤ) (x : ℝ) :
    haar1D j k true x =
      (Real.sqrt 2)⁻¹ *
        (haar1D (j + 1) ((2 : ℤ) * k) false x -
          haar1D (j + 1) ((2 : ℤ) * k + 1) false x) := by
  unfold haar1D
  simp [haarAtom1D]
  rw [haar1D_left_child_arg, haar1D_right_child_arg]
  rw [haarMother1D_refine (dyadicPower j * x - (k : ℝ))]
  rw [haarScaleFactor_add_one]
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hsqrt]

theorem haar1D_left_child_father_refine_pointwise (j k : ℤ) (x : ℝ) :
    haar1D (j + 1) ((2 : ℤ) * k) false x =
      (Real.sqrt 2)⁻¹ * (haar1D j k false x + haar1D j k true x) := by
  let L := haar1D (j + 1) ((2 : ℤ) * k) false x
  let R := haar1D (j + 1) ((2 : ℤ) * k + 1) false x
  let F := haar1D j k false x
  let M := haar1D j k true x
  have hf : F = (Real.sqrt 2)⁻¹ * (L + R) := by
    simpa [F, L, R] using haar1D_father_refine j k x
  have hm : M = (Real.sqrt 2)⁻¹ * (L - R) := by
    simpa [M, L, R] using haar1D_mother_refine j k x
  rw [show haar1D j k false x = F from rfl, hf]
  rw [show haar1D j k true x = M from rfl, hm]
  let c : ℝ := (Real.sqrt 2)⁻¹
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hc : c * (c * 2) = 1 := by
    dsimp [c]
    field_simp [hsqrt]
    rw [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
  change L = c * (c * (L + R) + c * (L - R))
  symm
  calc
    c * (c * (L + R) + c * (L - R)) = c * (c * (2 * L)) := by ring
    _ = (c * (c * 2)) * L := by ring
    _ = L := by rw [hc, one_mul]

theorem haar1D_right_child_father_refine_pointwise (j k : ℤ) (x : ℝ) :
    haar1D (j + 1) ((2 : ℤ) * k + 1) false x =
      (Real.sqrt 2)⁻¹ * (haar1D j k false x - haar1D j k true x) := by
  let L := haar1D (j + 1) ((2 : ℤ) * k) false x
  let R := haar1D (j + 1) ((2 : ℤ) * k + 1) false x
  let F := haar1D j k false x
  let M := haar1D j k true x
  have hf : F = (Real.sqrt 2)⁻¹ * (L + R) := by
    simpa [F, L, R] using haar1D_father_refine j k x
  have hm : M = (Real.sqrt 2)⁻¹ * (L - R) := by
    simpa [M, L, R] using haar1D_mother_refine j k x
  rw [show haar1D j k false x = F from rfl, hf]
  rw [show haar1D j k true x = M from rfl, hm]
  let c : ℝ := (Real.sqrt 2)⁻¹
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hc : c * (c * 2) = 1 := by
    dsimp [c]
    field_simp [hsqrt]
    rw [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
  change R = c * (c * (L + R) - c * (L - R))
  symm
  calc
    c * (c * (L + R) - c * (L - R)) = c * (c * (2 * R)) := by ring
    _ = (c * (c * 2)) * R := by ring
    _ = R := by rw [hc, one_mul]

theorem haar1D_child_father_refine_bool (j k : ℤ) (side : Bool) (x : ℝ) :
    haar1D (j + 1) ((2 : ℤ) * k + if side then 1 else 0) false x =
      ∑ signature : Bool,
        ((Real.sqrt 2)⁻¹ * (if side && signature then (-1 : ℝ) else 1)) *
          haar1D j k signature x := by
  cases side
  · rw [show (2 : ℤ) * k + (if false then 1 else 0) = (2 : ℤ) * k by simp]
    rw [haar1D_left_child_father_refine_pointwise]
    simp
    ring
  · rw [show (2 : ℤ) * k + (if true then 1 else 0) = (2 : ℤ) * k + 1 by simp]
    rw [haar1D_right_child_father_refine_pointwise]
    simp
    ring

/-- The father refinement identity as an equality in `L²(R)`. -/
theorem haar1DLp_father_refine (j k : ℤ) :
    haar1DLp j k false =
      (Real.sqrt 2)⁻¹ •
        (haar1DLp (j + 1) ((2 : ℤ) * k) false +
          haar1DLp (j + 1) ((2 : ℤ) * k + 1) false) := by
  refine Lp.ext ?_
  filter_upwards [(memLp_haar1D j k false).coeFn_toLp,
    Lp.coeFn_smul (c := (Real.sqrt 2)⁻¹)
      (haar1DLp (j + 1) ((2 : ℤ) * k) false +
        haar1DLp (j + 1) ((2 : ℤ) * k + 1) false),
    Lp.coeFn_add (haar1DLp (j + 1) ((2 : ℤ) * k) false)
      (haar1DLp (j + 1) ((2 : ℤ) * k + 1) false),
    (memLp_haar1D (j + 1) ((2 : ℤ) * k) false).coeFn_toLp,
    (memLp_haar1D (j + 1) ((2 : ℤ) * k + 1) false).coeFn_toLp] with
    x hx hsmul hadd hleft hright
  change ((memLp_haar1D j k false).toLp (haar1D j k false)) x =
    (((Real.sqrt 2)⁻¹ : ℝ) •
      (haar1DLp (j + 1) ((2 : ℤ) * k) false +
        haar1DLp (j + 1) ((2 : ℤ) * k + 1) false)) x
  rw [hx, hsmul]
  change haar1D j k false x =
    (Real.sqrt 2)⁻¹ *
      ((haar1DLp (j + 1) ((2 : ℤ) * k) false +
        haar1DLp (j + 1) ((2 : ℤ) * k + 1) false) x)
  rw [hadd]
  change haar1D j k false x =
    (Real.sqrt 2)⁻¹ *
      (((memLp_haar1D (j + 1) ((2 : ℤ) * k) false).toLp
          (haar1D (j + 1) ((2 : ℤ) * k) false)) x +
        ((memLp_haar1D (j + 1) ((2 : ℤ) * k + 1) false).toLp
          (haar1D (j + 1) ((2 : ℤ) * k + 1) false)) x)
  rw [hleft, hright]
  exact haar1D_father_refine j k x

/-- The mother refinement identity as an equality in `L²(R)`. -/
theorem haar1DLp_mother_refine (j k : ℤ) :
    haar1DLp j k true =
      (Real.sqrt 2)⁻¹ •
        (haar1DLp (j + 1) ((2 : ℤ) * k) false -
          haar1DLp (j + 1) ((2 : ℤ) * k + 1) false) := by
  refine Lp.ext ?_
  filter_upwards [(memLp_haar1D j k true).coeFn_toLp,
    Lp.coeFn_smul (c := (Real.sqrt 2)⁻¹)
      (haar1DLp (j + 1) ((2 : ℤ) * k) false -
        haar1DLp (j + 1) ((2 : ℤ) * k + 1) false),
    Lp.coeFn_sub (haar1DLp (j + 1) ((2 : ℤ) * k) false)
      (haar1DLp (j + 1) ((2 : ℤ) * k + 1) false),
    (memLp_haar1D (j + 1) ((2 : ℤ) * k) false).coeFn_toLp,
    (memLp_haar1D (j + 1) ((2 : ℤ) * k + 1) false).coeFn_toLp] with
    x hx hsmul hsub hleft hright
  change ((memLp_haar1D j k true).toLp (haar1D j k true)) x =
    (((Real.sqrt 2)⁻¹ : ℝ) •
      (haar1DLp (j + 1) ((2 : ℤ) * k) false -
        haar1DLp (j + 1) ((2 : ℤ) * k + 1) false)) x
  rw [hx, hsmul]
  change haar1D j k true x =
    (Real.sqrt 2)⁻¹ *
      ((haar1DLp (j + 1) ((2 : ℤ) * k) false -
        haar1DLp (j + 1) ((2 : ℤ) * k + 1) false) x)
  rw [hsub]
  change haar1D j k true x =
    (Real.sqrt 2)⁻¹ *
      (((memLp_haar1D (j + 1) ((2 : ℤ) * k) false).toLp
          (haar1D (j + 1) ((2 : ℤ) * k) false)) x -
        ((memLp_haar1D (j + 1) ((2 : ℤ) * k + 1) false).toLp
          (haar1D (j + 1) ((2 : ℤ) * k + 1) false)) x)
  rw [hleft, hright]
  exact haar1D_mother_refine j k x

theorem haar1DLp_left_child_father_refine (j k : ℤ) :
    haar1DLp (j + 1) ((2 : ℤ) * k) false =
      (Real.sqrt 2)⁻¹ • (haar1DLp j k false + haar1DLp j k true) := by
  let L := haar1DLp (j + 1) ((2 : ℤ) * k) false
  let R := haar1DLp (j + 1) ((2 : ℤ) * k + 1) false
  let F := haar1DLp j k false
  let M := haar1DLp j k true
  have hf : F = (Real.sqrt 2)⁻¹ • (L + R) := by
    simpa [F, L, R] using haar1DLp_father_refine j k
  have hm : M = (Real.sqrt 2)⁻¹ • (L - R) := by
    simpa [M, L, R] using haar1DLp_mother_refine j k
  rw [show haar1DLp j k false = F from rfl, hf]
  rw [show haar1DLp j k true = M from rfl, hm]
  let c : ℝ := (Real.sqrt 2)⁻¹
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hc : c * (c * 2) = 1 := by
    dsimp [c]
    field_simp [hsqrt]
    rw [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
  have hc' : (c * c) * 2 = 1 := by
    simpa [mul_assoc] using hc
  change L = c • (c • (L + R) + c • (L - R))
  rw [← smul_add, smul_smul]
  have hsum : (L + R) + (L - R) = (2 : ℝ) • L := by
    simp [sub_eq_add_neg, two_smul, add_assoc, add_left_comm]
  rw [hsum, smul_smul, hc', one_smul]

theorem haar1DLp_right_child_father_refine (j k : ℤ) :
    haar1DLp (j + 1) ((2 : ℤ) * k + 1) false =
      (Real.sqrt 2)⁻¹ • (haar1DLp j k false - haar1DLp j k true) := by
  let L := haar1DLp (j + 1) ((2 : ℤ) * k) false
  let R := haar1DLp (j + 1) ((2 : ℤ) * k + 1) false
  let F := haar1DLp j k false
  let M := haar1DLp j k true
  have hf : F = (Real.sqrt 2)⁻¹ • (L + R) := by
    simpa [F, L, R] using haar1DLp_father_refine j k
  have hm : M = (Real.sqrt 2)⁻¹ • (L - R) := by
    simpa [M, L, R] using haar1DLp_mother_refine j k
  rw [show haar1DLp j k false = F from rfl, hf]
  rw [show haar1DLp j k true = M from rfl, hm]
  let c : ℝ := (Real.sqrt 2)⁻¹
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hc : c * (c * 2) = 1 := by
    dsimp [c]
    field_simp [hsqrt]
    rw [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
  have hc' : (c * c) * 2 = 1 := by
    simpa [mul_assoc] using hc
  change R = c • (c • (L + R) - c • (L - R))
  rw [← smul_sub, smul_smul]
  have hdiff : (L + R) - (L - R) = (2 : ℝ) • R := by
    simp [sub_eq_add_neg, two_smul, add_assoc, add_left_comm]
  rw [hdiff, smul_smul, hc', one_smul]

/-- A normalized mother Haar atom is orthogonal to the left mother atom at the next dyadic scale. -/
theorem integral_haar1D_mul_left_child_mother (j k : ℤ) :
    ∫ x : ℝ, haar1D j k true x * haar1D (j + 1) ((2 : ℤ) * k) true x ∂volume = 0 := by
  let f : ℝ → ℝ := fun y => haarMother1D y * haarMother1D (2 * y)
  have hbase : ∫ y : ℝ, f y ∂volume = 0 := by
    simpa [f] using integral_haarMother1D_mul_left_child
  have haffine :
      ∫ x : ℝ, f (dyadicPower j * x - (k : ℝ)) ∂volume =
        (dyadicPower j)⁻¹ * ∫ y : ℝ, f y ∂volume := by
    have h := integral_comp_mul_add_volume
      (a := dyadicPower j) (b := -(k : ℝ))
      (dyadicPower_ne_zero j) f integrable_haarMother1D_mul_left_child
    have hpos : 0 < dyadicPower j := dyadicPower_pos j
    simpa [sub_eq_add_neg, abs_of_pos (inv_pos.mpr hpos), f] using h
  calc
    ∫ x : ℝ, haar1D j k true x * haar1D (j + 1) ((2 : ℤ) * k) true x ∂volume =
        ∫ x : ℝ, (haarScaleFactor j * haarScaleFactor (j + 1)) *
          f (dyadicPower j * x - (k : ℝ)) ∂volume := by
          refine integral_congr_ae (ae_of_all _ ?_)
          intro x
          unfold haar1D f
          simp [haarAtom1D]
          rw [haar1D_left_child_arg]
          ring
    _ = (haarScaleFactor j * haarScaleFactor (j + 1)) *
        ∫ x : ℝ, f (dyadicPower j * x - (k : ℝ)) ∂volume := by
          rw [integral_const_mul]
    _ = 0 := by
          rw [haffine, hbase, mul_zero, mul_zero]

/-- A normalized mother Haar atom is orthogonal to the right mother atom at the next dyadic scale. -/
theorem integral_haar1D_mul_right_child_mother (j k : ℤ) :
    ∫ x : ℝ, haar1D j k true x * haar1D (j + 1) ((2 : ℤ) * k + 1) true x ∂volume = 0 := by
  let f : ℝ → ℝ := fun y => haarMother1D y * haarMother1D (2 * y - 1)
  have hbase : ∫ y : ℝ, f y ∂volume = 0 := by
    simpa [f] using integral_haarMother1D_mul_right_child
  have haffine :
      ∫ x : ℝ, f (dyadicPower j * x - (k : ℝ)) ∂volume =
        (dyadicPower j)⁻¹ * ∫ y : ℝ, f y ∂volume := by
    have h := integral_comp_mul_add_volume
      (a := dyadicPower j) (b := -(k : ℝ))
      (dyadicPower_ne_zero j) f integrable_haarMother1D_mul_right_child
    have hpos : 0 < dyadicPower j := dyadicPower_pos j
    simpa [sub_eq_add_neg, abs_of_pos (inv_pos.mpr hpos), f] using h
  calc
    ∫ x : ℝ, haar1D j k true x * haar1D (j + 1) ((2 : ℤ) * k + 1) true x ∂volume =
        ∫ x : ℝ, (haarScaleFactor j * haarScaleFactor (j + 1)) *
          f (dyadicPower j * x - (k : ℝ)) ∂volume := by
          refine integral_congr_ae (ae_of_all _ ?_)
          intro x
          unfold haar1D f
          simp [haarAtom1D]
          rw [haar1D_right_child_arg]
          ring
    _ = (haarScaleFactor j * haarScaleFactor (j + 1)) *
        ∫ x : ℝ, f (dyadicPower j * x - (k : ℝ)) ∂volume := by
          rw [integral_const_mul]
    _ = 0 := by
          rw [haffine, hbase, mul_zero, mul_zero]

theorem integral_haar1D_mul_left_child_mother_any_signature (j k : ℤ) (signature : Bool) :
    ∫ x : ℝ, haar1D j k signature x * haar1D (j + 1) ((2 : ℤ) * k) true x ∂volume = 0 := by
  cases signature
  · let f : ℝ → ℝ := fun y => haarFather1D y * haarMother1D (2 * y)
    have hbase : ∫ y : ℝ, f y ∂volume = 0 := by
      simpa [f] using integral_haarFather1D_mul_left_child_mother
    have haffine :
        ∫ x : ℝ, f (dyadicPower j * x - (k : ℝ)) ∂volume =
          (dyadicPower j)⁻¹ * ∫ y : ℝ, f y ∂volume := by
      have h := integral_comp_mul_add_volume
        (a := dyadicPower j) (b := -(k : ℝ))
        (dyadicPower_ne_zero j) f integrable_haarFather1D_mul_left_child_mother
      have hpos : 0 < dyadicPower j := dyadicPower_pos j
      simpa [sub_eq_add_neg, abs_of_pos (inv_pos.mpr hpos), f] using h
    calc
      ∫ x : ℝ, haar1D j k false x * haar1D (j + 1) ((2 : ℤ) * k) true x ∂volume =
          ∫ x : ℝ, (haarScaleFactor j * haarScaleFactor (j + 1)) *
            f (dyadicPower j * x - (k : ℝ)) ∂volume := by
            refine integral_congr_ae (ae_of_all _ ?_)
            intro x
            unfold haar1D f
            simp [haarAtom1D]
            rw [haar1D_left_child_arg]
            ring
      _ = (haarScaleFactor j * haarScaleFactor (j + 1)) *
          ∫ x : ℝ, f (dyadicPower j * x - (k : ℝ)) ∂volume := by
            rw [integral_const_mul]
      _ = 0 := by rw [haffine, hbase, mul_zero, mul_zero]
  · exact integral_haar1D_mul_left_child_mother j k

theorem integral_haar1D_mul_right_child_mother_any_signature (j k : ℤ) (signature : Bool) :
    ∫ x : ℝ, haar1D j k signature x * haar1D (j + 1) ((2 : ℤ) * k + 1) true x ∂volume = 0 := by
  cases signature
  · let f : ℝ → ℝ := fun y => haarFather1D y * haarMother1D (2 * y - 1)
    have hbase : ∫ y : ℝ, f y ∂volume = 0 := by
      simpa [f] using integral_haarFather1D_mul_right_child_mother
    have haffine :
        ∫ x : ℝ, f (dyadicPower j * x - (k : ℝ)) ∂volume =
          (dyadicPower j)⁻¹ * ∫ y : ℝ, f y ∂volume := by
      have h := integral_comp_mul_add_volume
        (a := dyadicPower j) (b := -(k : ℝ))
        (dyadicPower_ne_zero j) f integrable_haarFather1D_mul_right_child_mother
      have hpos : 0 < dyadicPower j := dyadicPower_pos j
      simpa [sub_eq_add_neg, abs_of_pos (inv_pos.mpr hpos), f] using h
    calc
      ∫ x : ℝ, haar1D j k false x * haar1D (j + 1) ((2 : ℤ) * k + 1) true x ∂volume =
          ∫ x : ℝ, (haarScaleFactor j * haarScaleFactor (j + 1)) *
            f (dyadicPower j * x - (k : ℝ)) ∂volume := by
            refine integral_congr_ae (ae_of_all _ ?_)
            intro x
            unfold haar1D f
            simp [haarAtom1D]
            rw [haar1D_right_child_arg]
            ring
      _ = (haarScaleFactor j * haarScaleFactor (j + 1)) *
          ∫ x : ℝ, f (dyadicPower j * x - (k : ℝ)) ∂volume := by
            rw [integral_const_mul]
      _ = 0 := by rw [haffine, hbase, mul_zero, mul_zero]
  · exact integral_haar1D_mul_right_child_mother j k

theorem int_eq_zero_or_one_of_mem_Ico {y : ℝ} {n : ℤ}
    (hy : y ∈ Set.Ico (0 : ℝ) 1)
    (hz : 2 * y - (n : ℝ) ∈ Set.Ico (0 : ℝ) 1) :
    n = 0 ∨ n = 1 := by
  have hnlt_two_real : (n : ℝ) < 2 := by
    linarith [hz.1, hy.2]
  have hneg_one_lt_real : (-1 : ℝ) < (n : ℝ) := by
    linarith [hz.2, hy.1]
  have hnlt_two : n < 2 := by exact_mod_cast hnlt_two_real
  have hneg_one_lt : (-1 : ℤ) < n := by exact_mod_cast hneg_one_lt_real
  omega

/-- A next-scale dyadic child intersects a parent cell only for the two child cell labels. -/
theorem adjacent_child_overlap_cells {y : ℝ} {k l : ℤ}
    (hy : y ∈ Set.Ico (0 : ℝ) 1)
    (hz : 2 * y + 2 * (k : ℝ) - (l : ℝ) ∈ Set.Ico (0 : ℝ) 1) :
    l = (2 : ℤ) * k ∨ l = (2 : ℤ) * k + 1 := by
  have hz' : 2 * y - ((l - (2 : ℤ) * k : ℤ) : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by
    convert hz using 1
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
    ring
  have h := int_eq_zero_or_one_of_mem_Ico hy hz'
  rcases h with h | h
  · left
    omega
  · right
    omega

/-- If an adjacent-scale child is not one of the two children of the parent cell, the 1D product is
pointwise zero. -/
theorem haar1D_mul_adjacent_child_mother_ne (j k l : ℤ) (signature : Bool)
    (hl0 : l ≠ (2 : ℤ) * k) (hl1 : l ≠ (2 : ℤ) * k + 1) (x : ℝ) :
    haar1D j k signature x * haar1D (j + 1) l true x = 0 := by
  by_cases hparent : dyadicPower j * x - (k : ℝ) ∈ Set.Ico (0 : ℝ) 1
  · by_cases hchild : dyadicPower (j + 1) * x - (l : ℝ) ∈ Set.Ico (0 : ℝ) 1
    · have hchild' :
          2 * (dyadicPower j * x - (k : ℝ)) + 2 * (k : ℝ) - (l : ℝ) ∈
            Set.Ico (0 : ℝ) 1 := by
        convert hchild using 1
        rw [dyadicPower_add_one]
        ring
      have hoverlap := adjacent_child_overlap_cells (k := k) (l := l) hparent hchild'
      rcases hoverlap with h | h
      · exact False.elim (hl0 h)
      · exact False.elim (hl1 h)
    · have hzero : haar1D (j + 1) l true x = 0 := by
        unfold haar1D
        rw [haarAtom1D_eq_zero_of_notMem_Ico true hchild, mul_zero]
      rw [hzero, mul_zero]
  · have hzero : haar1D j k signature x = 0 := by
      unfold haar1D
      rw [haarAtom1D_eq_zero_of_notMem_Ico signature hparent, mul_zero]
    rw [hzero, zero_mul]

theorem integral_haar1D_mul_adjacent_child_mother_ne (j k l : ℤ)
    (signature : Bool) (hl0 : l ≠ (2 : ℤ) * k) (hl1 : l ≠ (2 : ℤ) * k + 1) :
    ∫ x : ℝ, haar1D j k signature x * haar1D (j + 1) l true x ∂volume = 0 := by
  calc
    ∫ x : ℝ, haar1D j k signature x * haar1D (j + 1) l true x ∂volume =
        ∫ x : ℝ, 0 ∂volume := by
          refine integral_congr_ae (ae_of_all _ ?_)
          intro x
          exact haar1D_mul_adjacent_child_mother_ne j k l signature hl0 hl1 x
    _ = 0 := by simp

theorem integral_haar1D_mul_adjacent_child_mother (j k l : ℤ)
    (signature : Bool) :
    ∫ x : ℝ, haar1D j k signature x * haar1D (j + 1) l true x ∂volume = 0 := by
  by_cases hl0 : l = (2 : ℤ) * k
  · subst l
    exact integral_haar1D_mul_left_child_mother_any_signature j k signature
  · by_cases hl1 : l = (2 : ℤ) * k + 1
    · subst l
      exact integral_haar1D_mul_right_child_mother_any_signature j k signature
    · exact integral_haar1D_mul_adjacent_child_mother_ne j k l signature hl0 hl1

/-- The one-dimensional father space at scale `j`, spanned by all father translates. -/
@[expose]
noncomputable def haar1DFatherSubmodule (j : ℤ) :
    Submodule ℝ (Lp ℝ 2 (volume : Measure ℝ)) :=
  Submodule.span ℝ (Set.range fun k : ℤ => haar1DLp j k false)

theorem haar1DLp_father_mem_fatherSubmodule (j k : ℤ) :
    haar1DLp j k false ∈ haar1DFatherSubmodule j := by
  exact Submodule.subset_span ⟨k, rfl⟩

theorem inner_haar1DLp_eq_integral (j₁ k₁ : ℤ) (signature₁ : Bool)
    (j₂ k₂ : ℤ) (signature₂ : Bool) :
    ⟪haar1DLp j₁ k₁ signature₁, haar1DLp j₂ k₂ signature₂⟫_ℝ =
      ∫ x : ℝ, haar1D j₁ k₁ signature₁ x * haar1D j₂ k₂ signature₂ x ∂volume := by
  rw [haar1DLp, haar1DLp, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_haar1D j₁ k₁ signature₁).coeFn_toLp,
    (memLp_haar1D j₂ k₂ signature₂).coeFn_toLp] with x hx₁ hx₂
  simp [hx₁, hx₂, mul_comm]

theorem haar1DLp_mem_fatherSubmodule_succ (j k : ℤ) (signature : Bool) :
    haar1DLp j k signature ∈ haar1DFatherSubmodule (j + 1) := by
  cases signature
  · rw [haar1DLp_father_refine]
    apply Submodule.smul_mem
    apply Submodule.add_mem
    · exact haar1DLp_father_mem_fatherSubmodule (j + 1) ((2 : ℤ) * k)
    · exact haar1DLp_father_mem_fatherSubmodule (j + 1) ((2 : ℤ) * k + 1)
  · rw [haar1DLp_mother_refine]
    apply Submodule.smul_mem
    apply Submodule.sub_mem
    · exact haar1DLp_father_mem_fatherSubmodule (j + 1) ((2 : ℤ) * k)
    · exact haar1DLp_father_mem_fatherSubmodule (j + 1) ((2 : ℤ) * k + 1)

theorem haar1DFatherSubmodule_le_succ (j : ℤ) :
    haar1DFatherSubmodule j ≤ haar1DFatherSubmodule (j + 1) := by
  rw [haar1DFatherSubmodule, haar1DFatherSubmodule]
  refine Submodule.span_le.2 ?_
  intro v hv
  rcases hv with ⟨k, rfl⟩
  exact haar1DLp_mem_fatherSubmodule_succ j k false

theorem inner_haar1DLp_adjacent_child_mother (j k l : ℤ) (signature : Bool) :
    ⟪haar1DLp j k signature, haar1DLp (j + 1) l true⟫_ℝ = 0 := by
  rw [inner_haar1DLp_eq_integral]
  exact integral_haar1D_mul_adjacent_child_mother j k l signature

theorem inner_haar1DFatherSubmodule_adjacent_mother (j l : ℤ)
    {v : Lp ℝ 2 (volume : Measure ℝ)} (hv : v ∈ haar1DFatherSubmodule j) :
    ⟪v, haar1DLp (j + 1) l true⟫_ℝ = 0 := by
  rw [haar1DFatherSubmodule] at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      rcases hv with ⟨k, rfl⟩
      exact inner_haar1DLp_adjacent_child_mother j k l false
  | zero =>
      simp
  | add x y _ _ hx hy =>
      rw [inner_add_left, hx, hy, add_zero]
  | smul c x _ hx =>
      rw [inner_smul_left, hx, mul_zero]

theorem haar1DFatherSubmodule_le_add_nat (j : ℤ) (n : ℕ) :
    haar1DFatherSubmodule j ≤ haar1DFatherSubmodule (j + (n : ℤ)) := by
  induction n with
  | zero =>
      intro v hv
      simpa using hv
  | succ n ih =>
      intro v hv
      have hvn : v ∈ haar1DFatherSubmodule (j + (n : ℤ)) := ih hv
      have hvnext :
          v ∈ haar1DFatherSubmodule ((j + (n : ℤ)) + 1) :=
        haar1DFatherSubmodule_le_succ (j + (n : ℤ)) hvn
      simpa only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one, add_assoc] using hvnext

theorem haar1DLp_mem_fatherSubmodule_add_nat_succ (j k : ℤ)
    (signature : Bool) (n : ℕ) :
    haar1DLp j k signature ∈ haar1DFatherSubmodule (j + ((n + 1 : ℕ) : ℤ)) := by
  have hfirst : haar1DLp j k signature ∈ haar1DFatherSubmodule (j + 1) :=
    haar1DLp_mem_fatherSubmodule_succ j k signature
  have hle := haar1DFatherSubmodule_le_add_nat (j + 1) n
  have hmem : haar1DLp j k signature ∈ haar1DFatherSubmodule ((j + 1) + (n : ℤ)) :=
    hle hfirst
  simpa only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one, add_assoc,
    add_comm, add_left_comm] using hmem

theorem inner_haar1DLp_finer_mother_nat_succ_succ (j k l : ℤ)
    (signature : Bool) (n : ℕ) :
    ⟪haar1DLp j k signature,
      haar1DLp (j + ((n + 1 : ℕ) : ℤ) + 1) l true⟫_ℝ = 0 := by
  exact inner_haar1DFatherSubmodule_adjacent_mother
    (j + ((n + 1 : ℕ) : ℤ)) l
    (haar1DLp_mem_fatherSubmodule_add_nat_succ j k signature n)

theorem inner_haar1DLp_finer_mother_nat_succ (j k l : ℤ)
    (signature : Bool) (n : ℕ) :
    ⟪haar1DLp j k signature,
      haar1DLp (j + ((n + 1 : ℕ) : ℤ)) l true⟫_ℝ = 0 := by
  cases n with
  | zero =>
      simpa using inner_haar1DLp_adjacent_child_mother j k l signature
  | succ n =>
      have h :=
        inner_haar1DLp_finer_mother_nat_succ_succ j k l signature n
      simpa only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one,
        Nat.succ_eq_add_one, add_assoc, add_comm, add_left_comm] using h

theorem integral_haar1D_mul_finer_mother_nat_succ (j k l : ℤ)
    (signature : Bool) (n : ℕ) :
    ∫ x : ℝ,
      haar1D j k signature x *
        haar1D (j + ((n + 1 : ℕ) : ℤ)) l true x ∂volume = 0 := by
  have h := inner_haar1DLp_finer_mother_nat_succ j k l signature n
  simpa [inner_haar1DLp_eq_integral] using h

end GaussianFields

end
