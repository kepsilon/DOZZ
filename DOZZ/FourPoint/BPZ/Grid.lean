/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.Complex.Basic

/-! # Square grids in the plane

The half-open squares `[a h, (a+1) h) × [b h, (b+1) h)`, `(a, b) ∈ ℤ²`, partition the plane. A
function of the square index is a finite step function on any bounded region, and its integral
against a finite measure is the corresponding finite sum. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DOZZ.Proofs

/-- The index of the half-open grid square of side `h` containing `x`. -/
noncomputable def bpzGridIdx (h : ℝ) (x : ℂ) : ℤ × ℤ := (⌊x.re / h⌋, ⌊x.im / h⌋)

/-- The lower-left corner of the grid square of side `h` with index `i`. -/
noncomputable def bpzGridCorner (h : ℝ) (i : ℤ × ℤ) : ℂ := ⟨i.1 * h, i.2 * h⟩

/-- The index box `[-N, N]²`. -/
def bpzGridBox (N : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(N : ℤ)) N ×ˢ Finset.Icc (-(N : ℤ)) N

theorem measurable_bpzGridIdx (h : ℝ) : Measurable (bpzGridIdx h) :=
  (Int.measurable_floor.comp (Complex.measurable_re.div_const h)).prodMk
    (Int.measurable_floor.comp (Complex.measurable_im.div_const h))

theorem measurableSet_bpzGridCell (h : ℝ) (i : ℤ × ℤ) :
    MeasurableSet (bpzGridIdx h ⁻¹' {i}) :=
  measurable_bpzGridIdx h (measurableSet_singleton i)

theorem bpzGrid_floor_bounds {h : ℝ} (hh : 0 < h) (t : ℝ) :
    (⌊t / h⌋ : ℝ) * h ≤ t ∧ t < (⌊t / h⌋ : ℝ) * h + h := by
  have h1 := Int.floor_le (t / h)
  have h2 := Int.lt_floor_add_one (t / h)
  constructor
  · calc (⌊t / h⌋ : ℝ) * h ≤ t / h * h := mul_le_mul_of_nonneg_right h1 hh.le
      _ = t := div_mul_cancel₀ t hh.ne'
  · calc t = t / h * h := (div_mul_cancel₀ t hh.ne').symm
      _ < ((⌊t / h⌋ : ℝ) + 1) * h := mul_lt_mul_of_pos_right h2 hh
      _ = (⌊t / h⌋ : ℝ) * h + h := by ring

theorem abs_sub_bpzGrid_floor_le {h : ℝ} (hh : 0 < h) (t : ℝ) :
    |t - (⌊t / h⌋ : ℝ) * h| ≤ h := by
  obtain ⟨h1, h2⟩ := bpzGrid_floor_bounds hh t
  rw [abs_le]
  constructor <;> linarith

/-- A point is within `2h` of the corner of its grid square. -/
theorem norm_sub_bpzGridCorner_le {h : ℝ} (hh : 0 < h) (x : ℂ) :
    ‖x - bpzGridCorner h (bpzGridIdx h x)‖ ≤ 2 * h := by
  have hre : (x - bpzGridCorner h (bpzGridIdx h x)).re = x.re - (⌊x.re / h⌋ : ℝ) * h := by
    simp [bpzGridCorner, bpzGridIdx]
  have him : (x - bpzGridCorner h (bpzGridIdx h x)).im = x.im - (⌊x.im / h⌋ : ℝ) * h := by
    simp [bpzGridCorner, bpzGridIdx]
  calc ‖x - bpzGridCorner h (bpzGridIdx h x)‖
      ≤ |(x - bpzGridCorner h (bpzGridIdx h x)).re| +
          |(x - bpzGridCorner h (bpzGridIdx h x)).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ h + h := by
        rw [hre, him]
        exact add_le_add (abs_sub_bpzGrid_floor_le hh _) (abs_sub_bpzGrid_floor_le hh _)
    _ = 2 * h := by ring

theorem bpzGrid_floor_mem_Icc {h R t : ℝ} (hh : 0 < h) (ht : |t| ≤ R) :
    ⌊t / h⌋ ∈ Finset.Icc (-(⌈R / h⌉₊ : ℤ)) ⌈R / h⌉₊ := by
  rw [Finset.mem_Icc]
  have hR : 0 ≤ R := (abs_nonneg t).trans ht
  have hc : R / h ≤ (⌈R / h⌉₊ : ℝ) := Nat.le_ceil _
  have hlo : -(R / h) ≤ t / h := by
    rw [neg_div', div_le_div_iff_of_pos_right hh]
    linarith [neg_abs_le t]
  have hhi : t / h ≤ R / h := div_le_div_of_nonneg_right ((le_abs_self t).trans ht) hh.le
  constructor
  · rw [Int.le_floor]
    push_cast
    linarith
  · have : (⌊t / h⌋ : ℝ) ≤ (⌈R / h⌉₊ : ℝ) := ((Int.floor_le _).trans hhi).trans hc
    exact_mod_cast this

/-- Points of a closed ball have grid indices in a fixed finite box. -/
theorem bpzGridIdx_mem_box {h R : ℝ} (hh : 0 < h) {x : ℂ} (hx : ‖x‖ ≤ R) :
    bpzGridIdx h x ∈ bpzGridBox ⌈R / h⌉₊ := by
  unfold bpzGridIdx bpzGridBox
  rw [Finset.mem_product]
  exact ⟨bpzGrid_floor_mem_Icc hh ((Complex.abs_re_le_norm x).trans hx),
    bpzGrid_floor_mem_Icc hh ((Complex.abs_im_le_norm x).trans hx)⟩

theorem bpzGrid_abs_le_of_floor_mem {h t : ℝ} (hh : 0 < h) {N : ℕ}
    (ht : ⌊t / h⌋ ∈ Finset.Icc (-(N : ℤ)) N) : |t| ≤ (N + 1) * h := by
  rw [Finset.mem_Icc] at ht
  obtain ⟨h1, h2⟩ := bpzGrid_floor_bounds hh t
  have hlo : (-(N : ℝ)) ≤ (⌊t / h⌋ : ℝ) := by exact_mod_cast ht.1
  have hhi : (⌊t / h⌋ : ℝ) ≤ N := by exact_mod_cast ht.2
  rw [abs_le]
  constructor <;> nlinarith

/-- Points whose grid index lies in the box `[-N, N]²` lie in a ball. -/
theorem norm_le_of_bpzGridIdx_mem_box {h : ℝ} (hh : 0 < h) {N : ℕ} {x : ℂ}
    (hx : bpzGridIdx h x ∈ bpzGridBox N) : ‖x‖ ≤ 2 * ((N + 1) * h) := by
  unfold bpzGridIdx bpzGridBox at hx
  rw [Finset.mem_product] at hx
  calc ‖x‖ ≤ |x.re| + |x.im| := Complex.norm_le_abs_re_add_abs_im x
    _ ≤ (N + 1) * h + (N + 1) * h :=
        add_le_add (bpzGrid_abs_le_of_floor_mem hh hx.1) (bpzGrid_abs_le_of_floor_mem hh hx.2)
    _ = 2 * ((N + 1) * h) := by ring

/-- A step function of the grid index on a finite set of squares is a finite sum of
indicators. -/
theorem bpzGrid_step_eq_sum (h : ℝ) (s : Finset (ℤ × ℤ)) (G : ℤ × ℤ → ℝ) (x : ℂ) :
    (if bpzGridIdx h x ∈ s then G (bpzGridIdx h x) else 0) =
      ∑ i ∈ s, (bpzGridIdx h ⁻¹' {i}).indicator (fun _ => G i) x := by
  classical
  have hterm : ∀ i ∈ s, (bpzGridIdx h ⁻¹' {i}).indicator (fun _ => G i) x =
      if bpzGridIdx h x = i then G i else 0 := by
    intro i _
    by_cases hi : bpzGridIdx h x = i
    · rw [Set.indicator_of_mem (by simpa using hi), ite_eq_left hi]
    · rw [Set.indicator_of_notMem (by simpa using hi), ite_eq_right hi]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]

/-- The integral of a step function of the grid index against a finite measure. -/
theorem integral_bpzGrid_step {μ : Measure ℂ} [IsFiniteMeasure μ] (h : ℝ)
    (s : Finset (ℤ × ℤ)) (G : ℤ × ℤ → ℝ) :
    ∫ x, (if bpzGridIdx h x ∈ s then G (bpzGridIdx h x) else 0) ∂μ =
      ∑ i ∈ s, μ.real (bpzGridIdx h ⁻¹' {i}) * G i := by
  simp_rw [bpzGrid_step_eq_sum h s G]
  rw [integral_finsetSum _ fun i _ =>
    (integrable_const (G i)).indicator (measurableSet_bpzGridCell h i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_indicator_const _ (measurableSet_bpzGridCell h i), smul_eq_mul]

theorem measurable_bpzGrid_step (h : ℝ) (s : Finset (ℤ × ℤ)) (G : ℤ × ℤ → ℝ) :
    Measurable fun x => if bpzGridIdx h x ∈ s then G (bpzGridIdx h x) else 0 := by
  classical
  have hm : Measurable fun i : ℤ × ℤ => if i ∈ s then G i else 0 := measurable_of_countable _
  exact hm.comp (measurable_bpzGridIdx h)

end DOZZ.Proofs
