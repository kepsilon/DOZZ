/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# GaussianFields.Ambient/Euclidean

Port of the corresponding GaussianFields source module.
-/

public section

open scoped BigOperators

namespace GaussianFields


/-- The standalone model of `R^d` for Gaussian fields. -/
abbrev Vec (d : Nat) := Fin d → ℝ

/-- The Euclidean dot product on `Vec d`. -/
@[expose]
noncomputable def euclideanDot {d : Nat} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i

/-- The squared Euclidean norm on `Vec d`. -/
@[expose]
noncomputable def euclideanNormSq {d : Nat} (x : Vec d) : ℝ :=
  euclideanDot x x

/-- The Euclidean norm on `Vec d`. -/
@[expose]
noncomputable def euclideanNorm {d : Nat} (x : Vec d) : ℝ :=
  Real.sqrt (euclideanNormSq x)

/-- The Euclidean distance on `Vec d`. -/
@[expose]
noncomputable def euclideanDist {d : Nat} (x y : Vec d) : ℝ :=
  euclideanNorm (x - y)

@[simp]
theorem euclideanDot_apply {d : Nat} (x y : Vec d) :
    euclideanDot x y = ∑ i, x i * y i :=
  rfl

theorem euclideanNormSq_eq_sum {d : Nat} (x : Vec d) :
    euclideanNormSq x = ∑ i, x i * x i :=
  rfl

theorem euclideanNorm_eq_sqrt {d : Nat} (x : Vec d) :
    euclideanNorm x = Real.sqrt (euclideanNormSq x) :=
  rfl

theorem euclideanNormSq_nonneg {d : Nat} (x : Vec d) :
    0 ≤ euclideanNormSq x := by
  rw [euclideanNormSq_eq_sum]
  refine Finset.sum_nonneg ?_
  intro i _hi
  nlinarith [sq_nonneg (x i)]

theorem euclideanNorm_nonneg {d : Nat} (x : Vec d) :
    0 ≤ euclideanNorm x :=
  Real.sqrt_nonneg _

/-- The squared Euclidean norm is continuous. -/
theorem continuous_euclideanNormSq {d : Nat} :
    Continuous (fun x : Vec d => euclideanNormSq x) := by
  unfold euclideanNormSq euclideanDot
  fun_prop

/-- The local Euclidean norm is continuous. -/
theorem continuous_euclideanNorm {d : Nat} :
    Continuous (fun x : Vec d => euclideanNorm x) := by
  unfold euclideanNorm
  exact Real.continuous_sqrt.comp continuous_euclideanNormSq

/-- The project Euclidean distance is continuous on spatial pairs. -/
theorem continuous_euclideanDist_pair {d : Nat} :
    Continuous (fun z : Vec d × Vec d => euclideanDist z.1 z.2) := by
  unfold euclideanDist
  exact continuous_euclideanNorm.comp (continuous_fst.sub continuous_snd)

/-- The project Euclidean distance from a fixed left endpoint is continuous. -/
theorem continuous_euclideanDist_left {d : Nat} (x : Vec d) :
    Continuous (fun y : Vec d => euclideanDist x y) := by
  unfold euclideanDist
  exact continuous_euclideanNorm.comp (continuous_const.sub continuous_id)

/-- The project Euclidean distance to a fixed right endpoint is continuous. -/
theorem continuous_euclideanDist_right {d : Nat} (y : Vec d) :
    Continuous (fun x : Vec d => euclideanDist x y) := by
  unfold euclideanDist
  exact continuous_euclideanNorm.comp (continuous_id.sub continuous_const)

/-- The strict pair-neighborhood cut out by project Euclidean distance is open. -/
theorem isOpen_setOf_euclideanDist_lt {d : Nat} (r : ℝ) :
    IsOpen {z : Vec d × Vec d | euclideanDist z.1 z.2 < r} := by
  exact isOpen_lt continuous_euclideanDist_pair continuous_const

/-- The closed pair-neighborhood cut out by project Euclidean distance is closed. -/
theorem isClosed_setOf_euclideanDist_le {d : Nat} (r : ℝ) :
    IsClosed {z : Vec d × Vec d | euclideanDist z.1 z.2 ≤ r} := by
  exact isClosed_le continuous_euclideanDist_pair continuous_const

theorem euclideanNorm_mul_self {d : Nat} (x : Vec d) :
    euclideanNorm x * euclideanNorm x = euclideanNormSq x := by
  rw [euclideanNorm, ← pow_two, Real.sq_sqrt (euclideanNormSq_nonneg x)]

/-- Cauchy-Schwarz for the local Euclidean dot product. -/
theorem abs_euclideanDot_le_euclideanNorm_mul {d : Nat} (x y : Vec d) :
    |euclideanDot x y| ≤ euclideanNorm x * euclideanNorm y := by
  unfold euclideanDot euclideanNorm euclideanNormSq
  have hx :
      (∑ i : Fin d, |x i| ^ (2 : Nat)) = ∑ i : Fin d, x i * x i := by
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [sq_abs]
    ring_nf
  have hy :
      (∑ i : Fin d, |y i| ^ (2 : Nat)) = ∑ i : Fin d, y i * y i := by
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [sq_abs]
    ring_nf
  calc
    |∑ i : Fin d, x i * y i|
        ≤ ∑ i : Fin d, |x i * y i| := by
          simpa using
            (Finset.abs_sum_le_sum_abs (fun i : Fin d => x i * y i) Finset.univ)
    _ = ∑ i : Fin d, |x i| * |y i| := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [abs_mul]
    _ ≤ Real.sqrt (∑ i : Fin d, |x i| ^ (2 : Nat)) *
          Real.sqrt (∑ i : Fin d, |y i| ^ (2 : Nat)) := by
          simpa using
            (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
              (fun i : Fin d => |x i|) (fun i : Fin d => |y i|))
    _ = Real.sqrt (∑ i : Fin d, x i * x i) *
          Real.sqrt (∑ i : Fin d, y i * y i) := by
          rw [hx, hy]

/-- The local Euclidean norm is bounded by the coordinate `L^1` norm. -/
theorem euclideanNorm_le_sum_abs {d : Nat} (x : Vec d) :
    euclideanNorm x ≤ ∑ i : Fin d, |x i| := by
  unfold euclideanNorm euclideanNormSq euclideanDot
  rw [Real.sqrt_le_iff]
  constructor
  · exact Finset.sum_nonneg fun i _hi => abs_nonneg (x i)
  · calc
      ∑ i : Fin d, x i * x i
          = ∑ i : Fin d, |x i| ^ (2 : Nat) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [sq_abs]
            ring_nf
      _ ≤ (∑ i : Fin d, |x i|) ^ (2 : Nat) := by
            exact Finset.sum_sq_le_sq_sum_of_nonneg
              (s := Finset.univ) (f := fun i : Fin d => |x i|)
              (fun i _hi => abs_nonneg (x i))

/-- Each coordinate is bounded by the local Euclidean norm. -/
theorem abs_apply_le_euclideanNorm {d : Nat} (x : Vec d) (i : Fin d) :
    |x i| ≤ euclideanNorm x := by
  unfold euclideanNorm euclideanNormSq euclideanDot
  refine Real.abs_le_sqrt ?_
  calc
    x i ^ (2 : Nat) = x i * x i := by ring_nf
    _ ≤ ∑ j : Fin d, x j * x j := by
          exact Finset.single_le_sum
            (s := Finset.univ) (f := fun j : Fin d => x j * x j)
            (fun j _hj => by nlinarith [sq_nonneg (x j)])
            (Finset.mem_univ i)

/-- The local Euclidean norm is positive away from the origin. -/
theorem euclideanNorm_pos_of_ne_zero {d : Nat} {x : Vec d} (hx : x ≠ 0) :
    0 < euclideanNorm x := by
  refine lt_of_le_of_ne (euclideanNorm_nonneg x) ?_
  intro hzero
  apply hx
  ext i
  have hcoord_abs : |x i| ≤ 0 := by
    simpa [hzero] using abs_apply_le_euclideanNorm x i
  exact abs_eq_zero.mp (le_antisymm hcoord_abs (abs_nonneg (x i)))

/-- Mathlib's finite-product sup norm is bounded by the local Euclidean norm. -/
theorem norm_le_euclideanNorm {d : Nat} (x : Vec d) :
    ‖x‖ ≤ euclideanNorm x := by
  rw [pi_norm_le_iff_of_nonneg (euclideanNorm_nonneg x)]
  intro i
  simpa only [Real.norm_eq_abs] using abs_apply_le_euclideanNorm x i

/-- The local Euclidean norm is bounded by `d` times Mathlib's finite-product sup norm. -/
theorem euclideanNorm_le_card_mul_norm {d : Nat} (x : Vec d) :
    euclideanNorm x ≤ (d : ℝ) * ‖x‖ := by
  calc
    euclideanNorm x ≤ ∑ i : Fin d, |x i| := euclideanNorm_le_sum_abs x
    _ = ∑ i : Fin d, ‖x i‖ := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [Real.norm_eq_abs]
    _ ≤ Fintype.card (Fin d) • ‖x‖ := by
          exact Pi.sum_norm_apply_le_norm (f := x)
    _ = (d : ℝ) * ‖x‖ := by
          rw [Fintype.card_fin]
          simp only [nsmul_eq_mul]

theorem euclideanNormSq_smul {d : Nat} (c : ℝ) (x : Vec d) :
    euclideanNormSq (c • x) = c ^ 2 * euclideanNormSq x := by
  rw [euclideanNormSq_eq_sum, euclideanNormSq_eq_sum]
  calc
    (∑ i, (c • x) i * (c • x) i) = ∑ i, c ^ 2 * (x i * x i) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    _ = c ^ 2 * ∑ i, x i * x i := by
      rw [Finset.mul_sum]

theorem euclideanNorm_smul {d : Nat} (c : ℝ) (x : Vec d) :
    euclideanNorm (c • x) = |c| * euclideanNorm x := by
  rw [euclideanNorm, euclideanNorm, euclideanNormSq_smul]
  rw [Real.sqrt_mul (sq_nonneg c)]
  rw [Real.sqrt_sq_eq_abs]

theorem euclideanNormSq_neg {d : Nat} (x : Vec d) :
    euclideanNormSq (-x) = euclideanNormSq x := by
  rw [← neg_one_smul ℝ x, euclideanNormSq_smul]
  norm_num

theorem euclideanNorm_neg {d : Nat} (x : Vec d) :
    euclideanNorm (-x) = euclideanNorm x := by
  rw [euclideanNorm, euclideanNorm, euclideanNormSq_neg]

theorem euclideanNormSq_sub_comm {d : Nat} (x y : Vec d) :
    euclideanNormSq (x - y) = euclideanNormSq (y - x) := by
  have hxy : x - y = -(y - x) := by
    ext i
    simp only [Pi.sub_apply, Pi.neg_apply]
    ring
  rw [hxy, euclideanNormSq_neg]

theorem euclideanNorm_sub_comm {d : Nat} (x y : Vec d) :
    euclideanNorm (x - y) = euclideanNorm (y - x) := by
  rw [euclideanNorm, euclideanNorm, euclideanNormSq_sub_comm]

theorem euclideanDist_comm {d : Nat} (x y : Vec d) :
    euclideanDist x y = euclideanDist y x :=
  euclideanNorm_sub_comm x y

theorem euclideanDist_self {d : Nat} (x : Vec d) :
    euclideanDist x x = 0 := by
  rw [euclideanDist, euclideanNorm, euclideanNormSq_eq_sum]
  simp only [Pi.sub_apply, sub_self, zero_mul, Finset.sum_const_zero, Real.sqrt_zero]

theorem euclideanNormSq_inv_smul {d : Nat} (x : Vec d) (r : ℝ) :
    euclideanNormSq (r⁻¹ • x) = r⁻¹ ^ 2 * euclideanNormSq x :=
  euclideanNormSq_smul r⁻¹ x

theorem euclideanNorm_inv_smul {d : Nat} (x : Vec d) (r : ℝ) :
    euclideanNorm (r⁻¹ • x) = |r⁻¹| * euclideanNorm x :=
  euclideanNorm_smul r⁻¹ x

end GaussianFields

end
