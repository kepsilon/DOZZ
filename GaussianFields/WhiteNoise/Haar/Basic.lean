/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import GaussianFields.Ambient.Euclidean

/-!
# GaussianFields Haar basic atoms

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace

namespace GaussianFields


/-- A dyadic Haar packet index in `R^d`: scale, cell, and a father/mother signature in each
coordinate. -/
structure HaarIndex (d : Nat) where
  /-- Dyadic scale. -/
  scale : ℤ
  /-- Dyadic spatial cell. -/
  cell : Fin d → ℤ
  /-- Coordinate-wise signature: `false` is the father function, `true` is the mother wavelet. -/
  signature : Fin d → Bool
deriving DecidableEq

instance instCountable_haarIndex (d : Nat) : Countable (HaarIndex d) := by
  classical
  exact (show Function.Injective
      (fun idx : HaarIndex d => (idx.scale, idx.cell, idx.signature)) by
    intro idx idx' hidx
    cases idx with
    | mk scale cell signature =>
    cases idx' with
    | mk scale' cell' signature' =>
    simp at hidx
    rcases hidx with ⟨rfl, rfl, rfl⟩
    rfl).countable

noncomputable instance instEncodable_haarIndex (d : Nat) : Encodable (HaarIndex d) :=
  Encodable.ofCountable (HaarIndex d)

/-- A nonzero tensor Haar signature: at least one coordinate uses the mother wavelet. -/
abbrev HaarWaveletSignature (d : Nat) :=
  { signature : Fin d → Bool // signature ≠ fun _ => false }

/-- A dyadic tensor-product Haar wavelet index in `R^d`.  Unlike `HaarIndex`, this excludes the
all-father signature, which is the source of the scale-by-scale redundancy in the raw packet
family. -/
structure HaarWaveletIndex (d : Nat) where
  /-- Dyadic scale. -/
  scale : ℤ
  /-- Dyadic spatial cell. -/
  cell : Fin d → ℤ
  /-- Nonzero coordinate-wise wavelet signature. -/
  signature : HaarWaveletSignature d
deriving DecidableEq

instance instCountable_haarWaveletSignature (d : Nat) :
    Countable (HaarWaveletSignature d) := by
  infer_instance

instance instCountable_haarWaveletIndex (d : Nat) : Countable (HaarWaveletIndex d) := by
  classical
  exact (show Function.Injective
      (fun idx : HaarWaveletIndex d => (idx.scale, idx.cell, idx.signature)) by
    intro idx idx' hidx
    cases idx with
    | mk scale cell signature =>
    cases idx' with
    | mk scale' cell' signature' =>
    simp at hidx
    rcases hidx with ⟨rfl, rfl, rfl⟩
    rfl).countable

noncomputable instance instEncodable_haarWaveletSignature (d : Nat) :
    Encodable (HaarWaveletSignature d) :=
  Encodable.ofCountable (HaarWaveletSignature d)

noncomputable instance instEncodable_haarWaveletIndex (d : Nat) :
    Encodable (HaarWaveletIndex d) :=
  Encodable.ofCountable (HaarWaveletIndex d)

/-- Forget the nonzero-signature proof and view a wavelet index as a raw Haar packet index. -/
@[expose]
def HaarWaveletIndex.toHaarIndex {d : Nat} (idx : HaarWaveletIndex d) : HaarIndex d where
  scale := idx.scale
  cell := idx.cell
  signature := idx.signature

theorem HaarWaveletIndex.toHaarIndex_injective {d : Nat} :
    Function.Injective (@HaarWaveletIndex.toHaarIndex d) := by
  intro idx idx' hidx
  cases idx with
  | mk scale cell signature =>
  cases idx' with
  | mk scale' cell' signature' =>
  cases signature with
  | mk sig hsig =>
  cases signature' with
  | mk sig' hsig' =>
  simp [HaarWaveletIndex.toHaarIndex] at hidx
  rcases hidx with ⟨rfl, rfl, hsigEq⟩
  cases hsigEq
  rfl

/-- The dyadic dilation `2^j`. -/
@[expose]
noncomputable def dyadicPower (j : ℤ) : ℝ :=
  (2 : ℝ) ^ j

theorem dyadicPower_pos (j : ℤ) : 0 < dyadicPower j := by
  unfold dyadicPower
  positivity

theorem dyadicPower_ne_zero (j : ℤ) : dyadicPower j ≠ 0 :=
  ne_of_gt (dyadicPower_pos j)

theorem dyadicPower_add_one (j : ℤ) :
    dyadicPower (j + 1) = 2 * dyadicPower j := by
  unfold dyadicPower
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-- The one-dimensional `L^2` normalization factor `2^(j/2)`. -/
@[expose]
noncomputable def haarScaleFactor (j : ℤ) : ℝ :=
  (2 : ℝ) ^ ((j : ℝ) / 2)

theorem haarScaleFactor_pos (j : ℤ) : 0 < haarScaleFactor j := by
  unfold haarScaleFactor
  positivity

theorem haarScaleFactor_sq (j : ℤ) :
    haarScaleFactor j ^ (2 : Nat) = dyadicPower j := by
  unfold haarScaleFactor dyadicPower
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
  have hmul : (↑j / 2) * ((2 : ℕ) : ℝ) = (j : ℝ) := by norm_num
  rw [hmul, Real.rpow_intCast]

theorem haarScaleFactor_add_one (j : ℤ) :
    haarScaleFactor (j + 1) = Real.sqrt 2 * haarScaleFactor j := by
  unfold haarScaleFactor
  have hexp : (((j + 1 : ℤ) : ℝ) / 2) = (j : ℝ) / 2 + (1 / 2 : ℝ) := by
    norm_num
    ring
  rw [hexp]
  rw [Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
  rw [← Real.sqrt_eq_rpow]
  ring

theorem inv_sqrt_two_mul_haarScaleFactor_add_one (j : ℤ) :
    (Real.sqrt 2)⁻¹ * haarScaleFactor (j + 1) = haarScaleFactor j := by
  rw [haarScaleFactor_add_one]
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hsqrt]

/-- The one-dimensional Haar father function `1_[0,1)`. -/
@[expose]
noncomputable def haarFather1D : ℝ → ℝ :=
  Set.indicator (Set.Ico (0 : ℝ) 1) fun _ => (1 : ℝ)

/-- The one-dimensional Haar mother function `1_[0,1/2) - 1_[1/2,1)`. -/
@[expose]
noncomputable def haarMother1D : ℝ → ℝ :=
  Set.indicator (Set.Ico (0 : ℝ) (1 / 2)) (fun _ => (1 : ℝ)) -
    Set.indicator (Set.Ico (1 / 2 : ℝ) 1) fun _ => (1 : ℝ)

@[fun_prop]
theorem measurable_haarFather1D : Measurable haarFather1D := by
  unfold haarFather1D
  exact measurable_const.indicator measurableSet_Ico

@[fun_prop]
theorem measurable_haarMother1D : Measurable haarMother1D := by
  unfold haarMother1D
  exact (measurable_const.indicator measurableSet_Ico).sub
    (measurable_const.indicator measurableSet_Ico)

theorem integrable_haarFather1D :
    Integrable haarFather1D (volume : Measure ℝ) := by
  unfold haarFather1D
  exact (integrableOn_const (C := (1 : ℝ)) (s := Set.Ico (0 : ℝ) 1)
    (μ := volume) (by
      rw [Real.volume_Ico]
      exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Ico

theorem integrable_haarMother1D :
    Integrable haarMother1D (volume : Measure ℝ) := by
  unfold haarMother1D
  refine Integrable.sub ?_ ?_
  · exact (integrableOn_const (C := (1 : ℝ))
      (s := Set.Ico (0 : ℝ) (1 / 2)) (μ := volume) (by
        rw [Real.volume_Ico]
        exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Ico
  · exact (integrableOn_const (C := (1 : ℝ))
      (s := Set.Ico (1 / 2 : ℝ) 1) (μ := volume) (by
        rw [Real.volume_Ico]
        exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Ico

theorem haarFather1D_sq (x : ℝ) :
    haarFather1D x ^ (2 : Nat) = haarFather1D x := by
  by_cases hx : x ∈ Set.Ico (0 : ℝ) 1
  · simp [haarFather1D, hx]
  · simp [haarFather1D, hx]

theorem haarMother1D_sq (x : ℝ) :
    haarMother1D x ^ (2 : Nat) = haarFather1D x := by
  let leftHalf : Set ℝ := Set.Ico (0 : ℝ) (1 / 2)
  let rightHalf : Set ℝ := Set.Ico (1 / 2 : ℝ) 1
  let unitInterval : Set ℝ := Set.Ico (0 : ℝ) 1
  have hleft_not_right : ∀ {x : ℝ}, x ∈ leftHalf → x ∉ rightHalf := by
    intro y hyLeft hyRight
    exact (not_le_of_gt hyLeft.2) hyRight.1
  have hleft_unit : ∀ {x : ℝ}, x ∈ leftHalf → x ∈ unitInterval := by
    intro y hy
    exact ⟨hy.1, by linarith [hy.2]⟩
  have hright_unit : ∀ {x : ℝ}, x ∈ rightHalf → x ∈ unitInterval := by
    intro y hy
    exact ⟨by linarith [hy.1], hy.2⟩
  by_cases hxLeft : x ∈ leftHalf
  · have hxRight : x ∉ rightHalf := hleft_not_right hxLeft
    have hxUnit : x ∈ unitInterval := hleft_unit hxLeft
    have hxLeft' : x ∈ Set.Ico (0 : ℝ) (1 / 2) := by simpa [leftHalf] using hxLeft
    have hxRight' : x ∉ Set.Ico (1 / 2 : ℝ) 1 := by simpa [rightHalf] using hxRight
    have hxUnit' : x ∈ Set.Ico (0 : ℝ) 1 := by simpa [unitInterval] using hxUnit
    change (((Set.Ico (0 : ℝ) (1 / 2)).indicator (fun _ => (1 : ℝ)) x -
          (Set.Ico (1 / 2 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x) ^ (2 : Nat) =
        (Set.Ico (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x)
    rw [Set.indicator_of_mem hxLeft', Set.indicator_of_notMem hxRight',
      Set.indicator_of_mem hxUnit']
    norm_num
  · by_cases hxRight : x ∈ rightHalf
    · have hxUnit : x ∈ unitInterval := hright_unit hxRight
      have hxLeft' : x ∉ Set.Ico (0 : ℝ) (1 / 2) := by simpa [leftHalf] using hxLeft
      have hxRight' : x ∈ Set.Ico (1 / 2 : ℝ) 1 := by simpa [rightHalf] using hxRight
      have hxUnit' : x ∈ Set.Ico (0 : ℝ) 1 := by simpa [unitInterval] using hxUnit
      change (((Set.Ico (0 : ℝ) (1 / 2)).indicator (fun _ => (1 : ℝ)) x -
            (Set.Ico (1 / 2 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x) ^ (2 : Nat) =
          (Set.Ico (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x)
      rw [Set.indicator_of_notMem hxLeft', Set.indicator_of_mem hxRight',
        Set.indicator_of_mem hxUnit']
      norm_num
    · have hxUnit : x ∉ unitInterval := by
        intro hx
        by_cases hxMid : x < (1 / 2 : ℝ)
        · exact hxLeft ⟨hx.1, hxMid⟩
        · exact hxRight ⟨le_of_not_gt hxMid, hx.2⟩
      have hxLeft' : x ∉ Set.Ico (0 : ℝ) (1 / 2) := by simpa [leftHalf] using hxLeft
      have hxRight' : x ∉ Set.Ico (1 / 2 : ℝ) 1 := by simpa [rightHalf] using hxRight
      have hxUnit' : x ∉ Set.Ico (0 : ℝ) 1 := by simpa [unitInterval] using hxUnit
      change (((Set.Ico (0 : ℝ) (1 / 2)).indicator (fun _ => (1 : ℝ)) x -
            (Set.Ico (1 / 2 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x) ^ (2 : Nat) =
          (Set.Ico (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x)
      rw [Set.indicator_of_notMem hxLeft', Set.indicator_of_notMem hxRight',
        Set.indicator_of_notMem hxUnit']
      norm_num

theorem haarFather1D_mul_haarMother1D (x : ℝ) :
    haarFather1D x * haarMother1D x = haarMother1D x := by
  let leftHalf : Set ℝ := Set.Ico (0 : ℝ) (1 / 2)
  let rightHalf : Set ℝ := Set.Ico (1 / 2 : ℝ) 1
  let unitInterval : Set ℝ := Set.Ico (0 : ℝ) 1
  have hleft_unit : ∀ {x : ℝ}, x ∈ leftHalf → x ∈ unitInterval := by
    intro y hy
    exact ⟨hy.1, by linarith [hy.2]⟩
  have hright_unit : ∀ {x : ℝ}, x ∈ rightHalf → x ∈ unitInterval := by
    intro y hy
    exact ⟨by linarith [hy.1], hy.2⟩
  have hleft_not_right : ∀ {x : ℝ}, x ∈ leftHalf → x ∉ rightHalf := by
    intro y hyLeft hyRight
    exact (not_le_of_gt hyLeft.2) hyRight.1
  by_cases hxLeft : x ∈ leftHalf
  · have hxRight : x ∉ rightHalf := hleft_not_right hxLeft
    have hxUnit : x ∈ unitInterval := hleft_unit hxLeft
    have hxLeft' : x ∈ Set.Ico (0 : ℝ) (1 / 2) := by simpa [leftHalf] using hxLeft
    have hxRight' : x ∉ Set.Ico (1 / 2 : ℝ) 1 := by simpa [rightHalf] using hxRight
    have hxUnit' : x ∈ Set.Ico (0 : ℝ) 1 := by simpa [unitInterval] using hxUnit
    change ((Set.Ico (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x *
        ((Set.Ico (0 : ℝ) (1 / 2)).indicator (fun _ => (1 : ℝ)) x -
          (Set.Ico (1 / 2 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x) =
        (Set.Ico (0 : ℝ) (1 / 2)).indicator (fun _ => (1 : ℝ)) x -
          (Set.Ico (1 / 2 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x)
    rw [Set.indicator_of_mem hxUnit', Set.indicator_of_mem hxLeft',
      Set.indicator_of_notMem hxRight']
    norm_num
  · by_cases hxRight : x ∈ rightHalf
    · have hxUnit : x ∈ unitInterval := hright_unit hxRight
      have hxLeft' : x ∉ Set.Ico (0 : ℝ) (1 / 2) := by simpa [leftHalf] using hxLeft
      have hxRight' : x ∈ Set.Ico (1 / 2 : ℝ) 1 := by simpa [rightHalf] using hxRight
      have hxUnit' : x ∈ Set.Ico (0 : ℝ) 1 := by simpa [unitInterval] using hxUnit
      change ((Set.Ico (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x *
          ((Set.Ico (0 : ℝ) (1 / 2)).indicator (fun _ => (1 : ℝ)) x -
            (Set.Ico (1 / 2 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x) =
          (Set.Ico (0 : ℝ) (1 / 2)).indicator (fun _ => (1 : ℝ)) x -
            (Set.Ico (1 / 2 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x)
      rw [Set.indicator_of_mem hxUnit', Set.indicator_of_notMem hxLeft',
        Set.indicator_of_mem hxRight']
      norm_num
    · have hxUnit : x ∉ unitInterval := by
        intro hx
        by_cases hxMid : x < (1 / 2 : ℝ)
        · exact hxLeft ⟨hx.1, hxMid⟩
        · exact hxRight ⟨le_of_not_gt hxMid, hx.2⟩
      have hxLeft' : x ∉ Set.Ico (0 : ℝ) (1 / 2) := by simpa [leftHalf] using hxLeft
      have hxRight' : x ∉ Set.Ico (1 / 2 : ℝ) 1 := by simpa [rightHalf] using hxRight
      have hxUnit' : x ∉ Set.Ico (0 : ℝ) 1 := by simpa [unitInterval] using hxUnit
      change ((Set.Ico (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x *
          ((Set.Ico (0 : ℝ) (1 / 2)).indicator (fun _ => (1 : ℝ)) x -
            (Set.Ico (1 / 2 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x) =
          (Set.Ico (0 : ℝ) (1 / 2)).indicator (fun _ => (1 : ℝ)) x -
            (Set.Ico (1 / 2 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x)
      rw [Set.indicator_of_notMem hxUnit', Set.indicator_of_notMem hxLeft',
        Set.indicator_of_notMem hxRight']
      norm_num

theorem haarMother1D_mul_haarFather1D (x : ℝ) :
    haarMother1D x * haarFather1D x = haarMother1D x := by
  rw [mul_comm, haarFather1D_mul_haarMother1D]

theorem integral_haarFather1D :
    ∫ x : ℝ, haarFather1D x ∂volume = 1 := by
  rw [haarFather1D, integral_indicator_const]
  · simp [MeasureTheory.measureReal_def, Real.volume_Ico]
  · exact measurableSet_Ico

theorem integral_haarMother1D :
    ∫ x : ℝ, haarMother1D x ∂volume = 0 := by
  rw [haarMother1D]
  change ∫ x : ℝ,
      (Set.Ico (0 : ℝ) (1 / 2)).indicator (fun _ => (1 : ℝ)) x -
        (Set.Ico (1 / 2 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x ∂volume = 0
  rw [integral_sub]
  · rw [integral_indicator_const, integral_indicator_const]
    · norm_num [MeasureTheory.measureReal_def, Real.volume_Ico]
    · exact measurableSet_Ico
    · exact measurableSet_Ico
  · exact (integrableOn_const (C := (1 : ℝ))
      (s := Set.Ico (0 : ℝ) (1 / 2)) (μ := volume) (by
        rw [Real.volume_Ico]
        exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Ico
  · exact (integrableOn_const (C := (1 : ℝ))
      (s := Set.Ico (1 / 2 : ℝ) 1) (μ := volume) (by
        rw [Real.volume_Ico]
        exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Ico

/-- Change variables in the full-line Lebesgue integral under an affine map. -/
theorem integral_comp_mul_add_volume {a b : ℝ} (ha : a ≠ 0) (f : ℝ → ℝ)
    (hf : Integrable f (volume : Measure ℝ)) :
    ∫ x : ℝ, f (a * x + b) ∂volume =
      |a⁻¹| * ∫ y : ℝ, f y ∂volume := by
  have hmap :
      Measure.map (fun x : ℝ => a * x + b) volume =
        ENNReal.ofReal |a⁻¹| • (volume : Measure ℝ) := by
    calc
      Measure.map (fun x : ℝ => a * x + b) volume =
          Measure.map (fun y : ℝ => y + b)
            (Measure.map (fun x : ℝ => a * x) volume) := by
            rw [Measure.map_map]
            · rfl
            · fun_prop
            · fun_prop
      _ = Measure.map (fun y : ℝ => y + b)
            (ENNReal.ofReal |a⁻¹| • (volume : Measure ℝ)) := by
            rw [Real.map_volume_mul_left ha]
      _ = ENNReal.ofReal |a⁻¹| • (volume : Measure ℝ) := by
            rw [Measure.map_smul (ENNReal.ofReal |a⁻¹|)
              (by fun_prop : AEMeasurable (fun y : ℝ => y + b) volume),
              map_add_right_eq_self]
  rw [← integral_map (by fun_prop : AEMeasurable (fun x : ℝ => a * x + b) volume)
    ?_]
  · rw [hmap, integral_smul_measure]
    rw [ENNReal.toReal_ofReal (abs_nonneg _)]
    simp [smul_eq_mul]
  · rw [hmap]
    exact (hf.smul_measure ENNReal.ofReal_ne_top).aestronglyMeasurable

theorem integral_haarFather1D_mul_self :
    ∫ x : ℝ, haarFather1D x * haarFather1D x ∂volume = 1 := by
  calc
    ∫ x : ℝ, haarFather1D x * haarFather1D x ∂volume =
        ∫ x : ℝ, haarFather1D x ∂volume := by
      refine integral_congr_ae (ae_of_all _ ?_)
      intro x
      show haarFather1D x * haarFather1D x = haarFather1D x
      rw [← pow_two, haarFather1D_sq]
    _ = 1 := integral_haarFather1D

theorem integral_haarMother1D_mul_self :
    ∫ x : ℝ, haarMother1D x * haarMother1D x ∂volume = 1 := by
  calc
    ∫ x : ℝ, haarMother1D x * haarMother1D x ∂volume =
        ∫ x : ℝ, haarFather1D x ∂volume := by
      refine integral_congr_ae (ae_of_all _ ?_)
      intro x
      show haarMother1D x * haarMother1D x = haarFather1D x
      rw [← pow_two, haarMother1D_sq]
    _ = 1 := integral_haarFather1D

theorem integral_haarFather1D_mul_haarMother1D :
    ∫ x : ℝ, haarFather1D x * haarMother1D x ∂volume = 0 := by
  calc
    ∫ x : ℝ, haarFather1D x * haarMother1D x ∂volume =
        ∫ x : ℝ, haarMother1D x ∂volume := by
      refine integral_congr_ae (ae_of_all _ ?_)
      exact haarFather1D_mul_haarMother1D
    _ = 0 := integral_haarMother1D

theorem integral_haarMother1D_mul_haarFather1D :
    ∫ x : ℝ, haarMother1D x * haarFather1D x ∂volume = 0 := by
  calc
    ∫ x : ℝ, haarMother1D x * haarFather1D x ∂volume =
        ∫ x : ℝ, haarMother1D x ∂volume := by
      refine integral_congr_ae (ae_of_all _ ?_)
      exact haarMother1D_mul_haarFather1D
    _ = 0 := integral_haarMother1D

/-- The father function is the sum of its two dyadic children. -/
theorem haarFather1D_refine (x : ℝ) :
    haarFather1D x =
      haarFather1D (2 * x) + haarFather1D (2 * x - 1) := by
  by_cases hx : x ∈ Set.Ico (0 : ℝ) (1 / 2)
  · have hxUnit : x ∈ Set.Ico (0 : ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
    have h2x : 2 * x ∈ Set.Ico (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
    have h2x1 : 2 * x - 1 ∉ Set.Ico (0 : ℝ) 1 := by
      intro h
      linarith [h.1, hx.2]
    simp [haarFather1D, hxUnit, h2x, h2x1]
  · by_cases hxRight : x ∈ Set.Ico (1 / 2 : ℝ) 1
    · have hxUnit : x ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith [hxRight.1], hxRight.2⟩
      have h2x : 2 * x ∉ Set.Ico (0 : ℝ) 1 := by
        intro h
        linarith [hxRight.1, h.2]
      have h2x1 : 2 * x - 1 ∈ Set.Ico (0 : ℝ) 1 := by
        constructor <;> linarith [hxRight.1, hxRight.2]
      simp [haarFather1D, hxUnit, h2x, h2x1]
    · have hxUnit : x ∉ Set.Ico (0 : ℝ) 1 := by
        intro hunit
        by_cases hlt : x < (1 / 2 : ℝ)
        · exact hx ⟨hunit.1, hlt⟩
        · exact hxRight ⟨le_of_not_gt hlt, hunit.2⟩
      have h2x : 2 * x ∉ Set.Ico (0 : ℝ) 1 := by
        intro h
        apply hxUnit
        constructor <;> linarith [h.1, h.2]
      have h2x1 : 2 * x - 1 ∉ Set.Ico (0 : ℝ) 1 := by
        intro h
        apply hxUnit
        constructor <;> linarith [h.1, h.2]
      simp [haarFather1D, hxUnit, h2x, h2x1]

/-- The mother function is the difference of the two next-scale father children. -/
theorem haarMother1D_refine (x : ℝ) :
    haarMother1D x =
      haarFather1D (2 * x) - haarFather1D (2 * x - 1) := by
  by_cases hx : x ∈ Set.Ico (0 : ℝ) (1 / 2)
  · have hright : x ∉ Set.Ico (1 / 2 : ℝ) 1 := by
      intro h
      linarith [hx.2, h.1]
    have h2x : 2 * x ∈ Set.Ico (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
    have h2x1 : 2 * x - 1 ∉ Set.Ico (0 : ℝ) 1 := by
      intro h
      linarith [h.1, hx.2]
    change ((Set.Ico (0 : ℝ) (1 / 2)).indicator (fun _ => (1 : ℝ)) x -
        (Set.Ico (1 / 2 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x) =
      (Set.Ico (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) (2 * x) -
        (Set.Ico (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) (2 * x - 1)
    rw [Set.indicator_of_mem hx, Set.indicator_of_notMem hright,
      Set.indicator_of_mem h2x, Set.indicator_of_notMem h2x1]
  · by_cases hxRight : x ∈ Set.Ico (1 / 2 : ℝ) 1
    · have h2x : 2 * x ∉ Set.Ico (0 : ℝ) 1 := by
        intro h
        linarith [hxRight.1, h.2]
      have h2x1 : 2 * x - 1 ∈ Set.Ico (0 : ℝ) 1 := by
        constructor <;> linarith [hxRight.1, hxRight.2]
      change ((Set.Ico (0 : ℝ) (1 / 2)).indicator (fun _ => (1 : ℝ)) x -
          (Set.Ico (1 / 2 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x) =
        (Set.Ico (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) (2 * x) -
          (Set.Ico (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) (2 * x - 1)
      rw [Set.indicator_of_notMem hx, Set.indicator_of_mem hxRight,
        Set.indicator_of_notMem h2x, Set.indicator_of_mem h2x1]
    · have h2x : 2 * x ∉ Set.Ico (0 : ℝ) 1 := by
        intro h
        apply hx
        constructor <;> linarith [h.1, h.2]
      have h2x1 : 2 * x - 1 ∉ Set.Ico (0 : ℝ) 1 := by
        intro h
        apply hxRight
        constructor <;> linarith [h.1, h.2]
      change ((Set.Ico (0 : ℝ) (1 / 2)).indicator (fun _ => (1 : ℝ)) x -
          (Set.Ico (1 / 2 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x) =
        (Set.Ico (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) (2 * x) -
          (Set.Ico (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) (2 * x - 1)
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxRight,
        Set.indicator_of_notMem h2x, Set.indicator_of_notMem h2x1]

/-- On the left dyadic child, the parent mother is identically `1`, so multiplying by it leaves
the child mother unchanged. -/
theorem haarMother1D_mul_left_child (y : ℝ) :
    haarMother1D y * haarMother1D (2 * y) = haarMother1D (2 * y) := by
  by_cases hsupport : 2 * y ∈ Set.Ico (0 : ℝ) 1
  · have hyLeft : y ∈ Set.Ico (0 : ℝ) (1 / 2) := by
      constructor <;> linarith [hsupport.1, hsupport.2]
    have hyRight : y ∉ Set.Ico (1 / 2 : ℝ) 1 := by
      intro hy
      linarith [hy.1, hsupport.2]
    change ((Set.Ico (0 : ℝ) (1 / 2)).indicator (fun _ => (1 : ℝ)) y -
        (Set.Ico (1 / 2 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y) *
        haarMother1D (2 * y) = haarMother1D (2 * y)
    rw [Set.indicator_of_mem hyLeft, Set.indicator_of_notMem hyRight]
    ring
  · have hchild : haarMother1D (2 * y) = 0 := by
      have hfather : haarFather1D (2 * y) = 0 := by
        simp [haarFather1D, hsupport]
      have hsq : haarMother1D (2 * y) ^ (2 : Nat) = 0 := by
        rw [haarMother1D_sq, hfather]
      nlinarith [sq_nonneg (haarMother1D (2 * y))]
    rw [hchild, mul_zero]

/-- On the right dyadic child, the parent mother is identically `-1`, so multiplying by it negates
the child mother. -/
theorem haarMother1D_mul_right_child (y : ℝ) :
    haarMother1D y * haarMother1D (2 * y - 1) = -haarMother1D (2 * y - 1) := by
  by_cases hsupport : 2 * y - 1 ∈ Set.Ico (0 : ℝ) 1
  · have hyRight : y ∈ Set.Ico (1 / 2 : ℝ) 1 := by
      constructor <;> linarith [hsupport.1, hsupport.2]
    have hyLeft : y ∉ Set.Ico (0 : ℝ) (1 / 2) := by
      intro hy
      linarith [hy.2, hsupport.1]
    change ((Set.Ico (0 : ℝ) (1 / 2)).indicator (fun _ => (1 : ℝ)) y -
        (Set.Ico (1 / 2 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y) *
        haarMother1D (2 * y - 1) = -haarMother1D (2 * y - 1)
    rw [Set.indicator_of_notMem hyLeft, Set.indicator_of_mem hyRight]
    ring
  · have hchild : haarMother1D (2 * y - 1) = 0 := by
      have hfather : haarFather1D (2 * y - 1) = 0 := by
        simp [haarFather1D, hsupport]
      have hsq : haarMother1D (2 * y - 1) ^ (2 : Nat) = 0 := by
        rw [haarMother1D_sq, hfather]
      nlinarith [sq_nonneg (haarMother1D (2 * y - 1))]
    rw [hchild, mul_zero, neg_zero]

theorem integrable_haarMother1D_mul_left_child :
    Integrable (fun y : ℝ => haarMother1D y * haarMother1D (2 * y))
      (volume : Measure ℝ) := by
  refine (integrable_haarMother1D.comp_mul_left'
    (by norm_num : (2 : ℝ) ≠ 0)).congr (ae_of_all _ ?_)
  intro y
  exact (haarMother1D_mul_left_child y).symm

theorem integrable_haarMother1D_mul_right_child :
    Integrable (fun y : ℝ => haarMother1D y * haarMother1D (2 * y - 1))
      (volume : Measure ℝ) := by
  have hshift : Integrable (fun y : ℝ => haarMother1D (y - 1)) (volume : Measure ℝ) := by
    simpa [sub_eq_add_neg] using integrable_haarMother1D.comp_add_right (-1)
  have hscaled : Integrable (fun y : ℝ => haarMother1D (2 * y - 1)) (volume : Measure ℝ) := by
    simpa [sub_eq_add_neg] using hshift.comp_mul_left' (by norm_num : (2 : ℝ) ≠ 0)
  refine hscaled.neg.congr (ae_of_all _ ?_)
  intro y
  exact (haarMother1D_mul_right_child y).symm

theorem integral_haarMother1D_mul_left_child :
    ∫ y : ℝ, haarMother1D y * haarMother1D (2 * y) ∂volume = 0 := by
  calc
    ∫ y : ℝ, haarMother1D y * haarMother1D (2 * y) ∂volume =
        ∫ y : ℝ, haarMother1D (2 * y) ∂volume := by
          refine integral_congr_ae (ae_of_all _ ?_)
          intro y
          exact haarMother1D_mul_left_child y
    _ = |(2 : ℝ)⁻¹| * ∫ y : ℝ, haarMother1D y ∂volume := by
          simpa using integral_comp_mul_add_volume (a := (2 : ℝ)) (b := 0)
            (by norm_num) haarMother1D integrable_haarMother1D
    _ = 0 := by rw [integral_haarMother1D, mul_zero]

theorem integral_haarMother1D_mul_right_child :
    ∫ y : ℝ, haarMother1D y * haarMother1D (2 * y - 1) ∂volume = 0 := by
  calc
    ∫ y : ℝ, haarMother1D y * haarMother1D (2 * y - 1) ∂volume =
        ∫ y : ℝ, -haarMother1D (2 * y - 1) ∂volume := by
          refine integral_congr_ae (ae_of_all _ ?_)
          intro y
          exact haarMother1D_mul_right_child y
    _ = - ∫ y : ℝ, haarMother1D (2 * y - 1) ∂volume := by
          rw [integral_neg]
    _ = 0 := by
          have h := integral_comp_mul_add_volume (a := (2 : ℝ)) (b := -1)
            (by norm_num) haarMother1D integrable_haarMother1D
          rw [show ∫ y : ℝ, haarMother1D (2 * y - 1) ∂volume =
              ∫ y : ℝ, haarMother1D (2 * y + -1) ∂volume by
                simp [sub_eq_add_neg]]
          rw [h, integral_haarMother1D, mul_zero, neg_zero]

/-- Select the father or mother Haar function from a Boolean signature. -/
@[expose]
noncomputable def haarAtom1D (signature : Bool) : ℝ → ℝ :=
  if signature then haarMother1D else haarFather1D

@[fun_prop]
theorem measurable_haarAtom1D (signature : Bool) : Measurable (haarAtom1D signature) := by
  cases signature <;> simp [haarAtom1D, measurable_haarFather1D, measurable_haarMother1D]

theorem haarAtom1D_sq (signature : Bool) (x : ℝ) :
    haarAtom1D signature x ^ (2 : Nat) = haarFather1D x := by
  cases signature <;> simp [haarAtom1D, haarFather1D_sq, haarMother1D_sq]

/-- A one-dimensional Haar atom is supported in `[0, 1)`. -/
theorem haarAtom1D_eq_zero_of_notMem_Ico (signature : Bool) {x : ℝ}
    (hx : x ∉ Set.Ico (0 : ℝ) 1) :
    haarAtom1D signature x = 0 := by
  cases signature
  · simp [haarAtom1D, haarFather1D, hx]
  · have hfather : haarFather1D x = 0 := by
      simp [haarFather1D, hx]
    have hsq : haarMother1D x ^ (2 : Nat) = 0 := by
      rw [haarMother1D_sq, hfather]
    have hzero : haarMother1D x = 0 := by
      nlinarith [sq_nonneg (haarMother1D x)]
    simp [haarAtom1D, hzero]

/-- On the left dyadic child, the parent father is identically `1`, so multiplying by it leaves
the child mother unchanged. -/
theorem haarFather1D_mul_left_child_mother (y : ℝ) :
    haarFather1D y * haarMother1D (2 * y) = haarMother1D (2 * y) := by
  by_cases hsupport : 2 * y ∈ Set.Ico (0 : ℝ) 1
  · have hyUnit : y ∈ Set.Ico (0 : ℝ) 1 := by
      constructor <;> linarith [hsupport.1, hsupport.2]
    change (Set.Ico (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y *
        haarMother1D (2 * y) = haarMother1D (2 * y)
    rw [Set.indicator_of_mem hyUnit]
    ring
  · have hchild : haarMother1D (2 * y) = 0 := by
      exact haarAtom1D_eq_zero_of_notMem_Ico true hsupport
    rw [hchild, mul_zero]

/-- On the right dyadic child, the parent father is identically `1`, so multiplying by it leaves
the child mother unchanged. -/
theorem haarFather1D_mul_right_child_mother (y : ℝ) :
    haarFather1D y * haarMother1D (2 * y - 1) = haarMother1D (2 * y - 1) := by
  by_cases hsupport : 2 * y - 1 ∈ Set.Ico (0 : ℝ) 1
  · have hyUnit : y ∈ Set.Ico (0 : ℝ) 1 := by
      constructor <;> linarith [hsupport.1, hsupport.2]
    change (Set.Ico (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y *
        haarMother1D (2 * y - 1) = haarMother1D (2 * y - 1)
    rw [Set.indicator_of_mem hyUnit]
    ring
  · have hchild : haarMother1D (2 * y - 1) = 0 := by
      exact haarAtom1D_eq_zero_of_notMem_Ico true hsupport
    rw [hchild, mul_zero]

theorem integrable_haarFather1D_mul_left_child_mother :
    Integrable (fun y : ℝ => haarFather1D y * haarMother1D (2 * y))
      (volume : Measure ℝ) := by
  refine (integrable_haarMother1D.comp_mul_left'
    (by norm_num : (2 : ℝ) ≠ 0)).congr (ae_of_all _ ?_)
  intro y
  exact (haarFather1D_mul_left_child_mother y).symm

theorem integrable_haarFather1D_mul_right_child_mother :
    Integrable (fun y : ℝ => haarFather1D y * haarMother1D (2 * y - 1))
      (volume : Measure ℝ) := by
  have hshift : Integrable (fun y : ℝ => haarMother1D (y - 1)) (volume : Measure ℝ) := by
    simpa [sub_eq_add_neg] using integrable_haarMother1D.comp_add_right (-1)
  have hscaled : Integrable (fun y : ℝ => haarMother1D (2 * y - 1)) (volume : Measure ℝ) := by
    simpa [sub_eq_add_neg] using hshift.comp_mul_left' (by norm_num : (2 : ℝ) ≠ 0)
  refine hscaled.congr (ae_of_all _ ?_)
  intro y
  exact (haarFather1D_mul_right_child_mother y).symm

theorem integral_haarFather1D_mul_left_child_mother :
    ∫ y : ℝ, haarFather1D y * haarMother1D (2 * y) ∂volume = 0 := by
  calc
    ∫ y : ℝ, haarFather1D y * haarMother1D (2 * y) ∂volume =
        ∫ y : ℝ, haarMother1D (2 * y) ∂volume := by
          refine integral_congr_ae (ae_of_all _ ?_)
          intro y
          exact haarFather1D_mul_left_child_mother y
    _ = |(2 : ℝ)⁻¹| * ∫ y : ℝ, haarMother1D y ∂volume := by
          simpa using integral_comp_mul_add_volume (a := (2 : ℝ)) (b := 0)
            (by norm_num) haarMother1D integrable_haarMother1D
    _ = 0 := by rw [integral_haarMother1D, mul_zero]

theorem integral_haarFather1D_mul_right_child_mother :
    ∫ y : ℝ, haarFather1D y * haarMother1D (2 * y - 1) ∂volume = 0 := by
  calc
    ∫ y : ℝ, haarFather1D y * haarMother1D (2 * y - 1) ∂volume =
        ∫ y : ℝ, haarMother1D (2 * y - 1) ∂volume := by
          refine integral_congr_ae (ae_of_all _ ?_)
          intro y
          exact haarFather1D_mul_right_child_mother y
    _ = 0 := by
          have h := integral_comp_mul_add_volume (a := (2 : ℝ)) (b := -1)
            (by norm_num) haarMother1D integrable_haarMother1D
          rw [show ∫ y : ℝ, haarMother1D (2 * y - 1) ∂volume =
              ∫ y : ℝ, haarMother1D (2 * y + -1) ∂volume by
                simp [sub_eq_add_neg]]
          rw [h, integral_haarMother1D, mul_zero]

/-- Distinct integer translates of `[0,1)` are disjoint. -/
theorem not_both_mem_Ico_sub_int {z : ℝ} {k₁ k₂ : ℤ} (hk : k₁ ≠ k₂) :
    ¬ (z - (k₁ : ℝ) ∈ Set.Ico (0 : ℝ) 1 ∧
      z - (k₂ : ℝ) ∈ Set.Ico (0 : ℝ) 1) := by
  rintro ⟨h₁, h₂⟩
  rcases lt_or_gt_of_ne hk with hklt | hkgt
  · have hle : (k₁ : ℝ) + 1 ≤ (k₂ : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr hklt)
    linarith [h₁.2, h₂.1, hle]
  · have hle : (k₂ : ℝ) + 1 ≤ (k₁ : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr hkgt)
    linarith [h₂.2, h₁.1, hle]

/-- Haar atoms in distinct integer cells have pointwise-zero product. -/
theorem haarAtom1D_mul_eq_zero_of_cells_ne (signature₁ signature₂ : Bool)
    {z : ℝ} {k₁ k₂ : ℤ} (hk : k₁ ≠ k₂) :
    haarAtom1D signature₁ (z - (k₁ : ℝ)) *
        haarAtom1D signature₂ (z - (k₂ : ℝ)) = 0 := by
  by_cases h₁ : z - (k₁ : ℝ) ∈ Set.Ico (0 : ℝ) 1
  · by_cases h₂ : z - (k₂ : ℝ) ∈ Set.Ico (0 : ℝ) 1
    · exact False.elim (not_both_mem_Ico_sub_int hk ⟨h₁, h₂⟩)
    · rw [haarAtom1D_eq_zero_of_notMem_Ico signature₂ h₂, mul_zero]
  · rw [haarAtom1D_eq_zero_of_notMem_Ico signature₁ h₁, zero_mul]

theorem integral_haarAtom1D_mul_haarAtom1D (signature₁ signature₂ : Bool) :
    ∫ x : ℝ, haarAtom1D signature₁ x * haarAtom1D signature₂ x ∂volume =
      if signature₁ = signature₂ then 1 else 0 := by
  cases signature₁ <;> cases signature₂ <;>
    simp [haarAtom1D, integral_haarFather1D_mul_self, integral_haarMother1D_mul_self,
      integral_haarFather1D_mul_haarMother1D, integral_haarMother1D_mul_haarFather1D]

theorem integrable_haarAtom1D (signature : Bool) :
    Integrable (haarAtom1D signature) (volume : Measure ℝ) := by
  cases signature <;> simp [haarAtom1D, integrable_haarFather1D, integrable_haarMother1D]

theorem integral_haarAtom1D (signature : Bool) :
    ∫ x : ℝ, haarAtom1D signature x ∂volume = if signature then 0 else 1 := by
  cases signature <;> simp [haarAtom1D, integral_haarFather1D, integral_haarMother1D]

theorem integral_haarAtom1D_sq (signature : Bool) :
    ∫ x : ℝ, haarAtom1D signature x ^ (2 : Nat) ∂volume = 1 := by
  calc
    ∫ x : ℝ, haarAtom1D signature x ^ (2 : Nat) ∂volume =
        ∫ x : ℝ, haarFather1D x ∂volume := by
          refine integral_congr_ae (ae_of_all _ ?_)
          intro x
          change haarAtom1D signature x ^ (2 : Nat) = haarFather1D x
          rw [haarAtom1D_sq]
    _ = 1 := integral_haarFather1D

theorem integrable_haarAtom1D_mul_haarAtom1D (signature₁ signature₂ : Bool) :
    Integrable (fun x : ℝ => haarAtom1D signature₁ x * haarAtom1D signature₂ x)
      (volume : Measure ℝ) := by
  cases signature₁ <;> cases signature₂
  · refine integrable_haarFather1D.congr (ae_of_all _ ?_)
    intro x
    simp [haarAtom1D, ← pow_two, haarFather1D_sq]
  · refine integrable_haarMother1D.congr (ae_of_all _ ?_)
    intro x
    simp [haarAtom1D, haarFather1D_mul_haarMother1D]
  · refine integrable_haarMother1D.congr (ae_of_all _ ?_)
    intro x
    simp [haarAtom1D, haarMother1D_mul_haarFather1D]
  · refine integrable_haarFather1D.congr (ae_of_all _ ?_)
    intro x
    simp [haarAtom1D, ← pow_two, haarMother1D_sq]

end GaussianFields

end
