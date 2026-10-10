/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosSmoothConvex

/-! Uniform pointwise envelopes for finite-chaos interpolation. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace DOZZ.Proofs

/-- An interpolated coordinate is controlled by its two absolute endpoint coordinates. -/
theorem kahaneInterpolatedField_abs_le
    (x y t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    |Real.sqrt t * x + Real.sqrt (1 - t) * y| ≤ |x| + |y| := by
  have hs : Real.sqrt t ≤ 1 := by
    simpa using (Real.sqrt_le_sqrt ht.2)
  have hs' : Real.sqrt (1 - t) ≤ 1 := by
    have h := Real.sqrt_le_sqrt (show 1 - t ≤ 1 by linarith [ht.1])
    simpa using h
  calc
    _ ≤ |Real.sqrt t * x| + |Real.sqrt (1 - t) * y| := abs_add_le _ _
    _ = Real.sqrt t * |x| + Real.sqrt (1 - t) * |y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ |x| + |y| := by
      exact add_le_add
        (by simpa using mul_le_mul_of_nonneg_right hs (abs_nonneg x))
        (by simpa using mul_le_mul_of_nonneg_right hs' (abs_nonneg y))

/-- One Wick exponential is bounded by the common endpoint absolute-exponential envelope. -/
theorem kahaneInterpolatedWick_le_absExp
    {ι : Type*} [Fintype ι]
    (x y vX vY : ι → ℝ) (hvX : ∀ i, 0 ≤ vX i) (hvY : ∀ i, 0 ≤ vY i)
    (γ t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (i : ι) :
    Real.exp (γ * (Real.sqrt t * x i + Real.sqrt (1 - t) * y i) -
      γ ^ 2 / 2 * (t * vX i + (1 - t) * vY i)) ≤
      Real.exp (|γ| * ∑ j, (|x j| + |y j|)) := by
  classical
  have hv : 0 ≤ t * vX i + (1 - t) * vY i :=
    add_nonneg (mul_nonneg ht.1 (hvX i)) (mul_nonneg (by linarith [ht.2]) (hvY i))
  have hcoord : |x i| + |y i| ≤ ∑ j, (|x j| + |y j|) :=
    Finset.single_le_sum (f := fun j => |x j| + |y j|)
      (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
      (Finset.mem_univ i)
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ γ * (Real.sqrt t * x i + Real.sqrt (1 - t) * y i) :=
      sub_le_self _ (mul_nonneg (by positivity) hv)
    _ ≤ |γ| * |Real.sqrt t * x i + Real.sqrt (1 - t) * y i| := by
      simpa only [abs_mul] using le_abs_self
        (γ * (Real.sqrt t * x i + Real.sqrt (1 - t) * y i))
    _ ≤ |γ| * (|x i| + |y i|) :=
      mul_le_mul_of_nonneg_left (kahaneInterpolatedField_abs_le _ _ _ ht) (abs_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hcoord (abs_nonneg _)

/-- The full mass has one common envelope on the closed interpolation interval. -/
theorem kahaneInterpolatedMass_norm_le_absExp
    {ΩX ΩY ι : Type*} [Fintype ι]
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ) (vX vY a : ι → ℝ)
    (hvX : ∀ i, 0 ≤ vX i) (hvY : ∀ i, 0 ≤ vY i) (ha : ∀ i, 0 ≤ a i)
    (γ t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (ω : ΩX × ΩY) :
    ‖kahaneInterpolatedMass X Y vX vY a γ t ω‖ ≤
      (∑ i, a i) * Real.exp (|γ| * ∑ i, (|X ω.1 i| + |Y ω.2 i|)) := by
  classical
  unfold kahaneInterpolatedMass
  calc
    _ ≤ ∑ i, ‖a i * Real.exp _‖ := norm_sum_le _ _
    _ ≤ ∑ i, a i * Real.exp (|γ| * ∑ j, (|X ω.1 j| + |Y ω.2 j|)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha i),
        abs_of_nonneg (Real.exp_nonneg _)]
      exact mul_le_mul_of_nonneg_left
        (kahaneInterpolatedWick_le_absExp (X ω.1) (Y ω.2) vX vY hvX hvY γ t ht i) (ha i)
    _ = _ := by rw [Finset.sum_mul]

/-- The scalar interpolation score has a polynomial envelope away from the endpoints. -/
theorem kahaneInterpolatedScore_abs_le
    {ι : Type*} [Fintype ι]
    (x y vX vY : ι → ℝ) (γ ε t : ℝ) (hε : 0 < ε)
    (ht : ε ≤ t) (ht' : ε ≤ 1 - t) (i : ι) :
    |γ * (x i / (2 * Real.sqrt t) - y i / (2 * Real.sqrt (1 - t))) -
      γ ^ 2 / 2 * (vX i - vY i)| ≤
      |γ| / (2 * Real.sqrt ε) * (∑ j, (|x j| + |y j|)) +
        γ ^ 2 / 2 * ∑ j, |vX j - vY j| := by
  classical
  have hsε : 0 < 2 * Real.sqrt ε := by positivity
  have hst : 0 < 2 * Real.sqrt t := mul_pos (by norm_num)
    (Real.sqrt_pos.mpr (hε.trans_le ht))
  have hst' : 0 < 2 * Real.sqrt (1 - t) := mul_pos (by norm_num)
    (Real.sqrt_pos.mpr (hε.trans_le ht'))
  have hx : |x i / (2 * Real.sqrt t)| ≤ |x i| / (2 * Real.sqrt ε) := by
    rw [abs_div, abs_of_pos hst]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hsε
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ht) (by norm_num))
  have hy : |y i / (2 * Real.sqrt (1 - t))| ≤ |y i| / (2 * Real.sqrt ε) := by
    rw [abs_div, abs_of_pos hst']
    exact div_le_div_of_nonneg_left (abs_nonneg _) hsε
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ht') (by norm_num))
  have hcoord : |x i| + |y i| ≤ ∑ j, (|x j| + |y j|) :=
    Finset.single_le_sum (f := fun j => |x j| + |y j|)
      (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
      (Finset.mem_univ i)
  have hv : |vX i - vY i| ≤ ∑ j, |vX j - vY j| :=
    Finset.single_le_sum (f := fun j => |vX j - vY j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  calc
    _ ≤ |γ * (x i / (2 * Real.sqrt t) - y i / (2 * Real.sqrt (1 - t)))| +
        |γ ^ 2 / 2 * (vX i - vY i)| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le
        (γ * (x i / (2 * Real.sqrt t) - y i / (2 * Real.sqrt (1 - t))))
        (γ ^ 2 / 2 * (vX i - vY i))
    _ = |γ| * |x i / (2 * Real.sqrt t) - y i / (2 * Real.sqrt (1 - t))| +
        γ ^ 2 / 2 * |vX i - vY i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ γ ^ 2 / 2)]
    _ ≤ |γ| * (|x i| / (2 * Real.sqrt ε) + |y i| / (2 * Real.sqrt ε)) +
        γ ^ 2 / 2 * |vX i - vY i| := by
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have hsub : |x i / (2 * Real.sqrt t) - y i / (2 * Real.sqrt (1 - t))| ≤
          |x i / (2 * Real.sqrt t)| + |y i / (2 * Real.sqrt (1 - t))| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le
          (x i / (2 * Real.sqrt t)) (y i / (2 * Real.sqrt (1 - t)))
      exact hsub.trans (add_le_add hx hy)
    _ = |γ| / (2 * Real.sqrt ε) * (|x i| + |y i|) +
        γ ^ 2 / 2 * |vX i - vY i| := by ring
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left hcoord (by positivity))
      (mul_le_mul_of_nonneg_left hv (by positivity))

/-- A bounded test derivative yields a locally uniform derivative envelope. -/
theorem kahaneInterpolatedTestDerivative_norm_le_absExp
    {ΩX ΩY ι : Type*} [Fintype ι]
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ) (vX vY a : ι → ℝ)
    (hvX : ∀ i, 0 ≤ vX i) (hvY : ∀ i, 0 ≤ vY i) (ha : ∀ i, 0 ≤ a i)
    (γ ε t B : ℝ) (F' : ℝ → ℝ) (hB : 0 ≤ B) (hF' : ∀ x, ‖F' x‖ ≤ B)
    (hε : 0 < ε) (ht : ε ≤ t) (ht' : ε ≤ 1 - t) (ω : ΩX × ΩY) :
    ‖kahaneInterpolatedTestDerivative X Y vX vY a γ F' t ω‖ ≤
      B * (∑ i, a i) * Real.exp (|γ| * ∑ i, (|X ω.1 i| + |Y ω.2 i|)) *
        (|γ| / (2 * Real.sqrt ε) * (∑ i, (|X ω.1 i| + |Y ω.2 i|)) +
          γ ^ 2 / 2 * ∑ i, |vX i - vY i|) := by
  classical
  let E := Real.exp (|γ| * ∑ i, (|X ω.1 i| + |Y ω.2 i|))
  let D := |γ| / (2 * Real.sqrt ε) * (∑ i, (|X ω.1 i| + |Y ω.2 i|)) +
    γ ^ 2 / 2 * ∑ i, |vX i - vY i|
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨hε.le.trans ht, by linarith⟩
  unfold kahaneInterpolatedTestDerivative
  rw [norm_mul]
  calc
    _ ≤ B * ∑ i, ‖a i * Real.exp _ * _‖ :=
      mul_le_mul (hF' _) (norm_sum_le _ _) (norm_nonneg _) hB
    _ ≤ B * ∑ i, a i * E * D := by
      apply mul_le_mul_of_nonneg_left _ hB
      apply Finset.sum_le_sum
      intro i hi
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (ha i),
        abs_of_nonneg (Real.exp_nonneg _)]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (kahaneInterpolatedWick_le_absExp (X ω.1) (Y ω.2) vX vY hvX hvY γ t htI i) (ha i))
        (kahaneInterpolatedScore_abs_le (X ω.1) (Y ω.2) vX vY γ ε t hε ht ht' i)
        (abs_nonneg _) (mul_nonneg (ha i) (Real.exp_nonneg _))
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring

/-- The common endpoint envelope is integrable for arbitrary, possibly singular Gaussian laws. -/
theorem kahaneEndpointAbsExp_integrable
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian PX X) (hY : DOZZ.IsCenteredJointlyGaussian PY Y)
    (γ : ℝ) :
    Integrable (fun ω : ΩX × ΩY =>
      Real.exp (|γ| * ∑ i, (|X ω.1 i| + |Y ω.2 i|))) (PX.prod PY) := by
  classical
  let Z : ΩX × ΩY → Sum ι ι → ℝ := fun ω k => match k with
    | Sum.inl i => X ω.1 i
    | Sum.inr i => Y ω.2 i
  have hZ := independent_product_concat_isCenteredJointlyGaussian PX PY X Y hX hY
  have h := centeredJointlyGaussian_abs_linear_exp_integrable (PX.prod PY) Z hZ
    (fun _ => |γ|)
  simpa [Z, Fintype.sum_sum_type, Finset.sum_add_distrib, Finset.mul_sum, mul_add] using h

/-- An absolute coordinate factor times the endpoint envelope remains integrable. -/
theorem kahaneEndpointCoordinateAbsExp_integrable
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian PX X) (hY : DOZZ.IsCenteredJointlyGaussian PY Y)
    (γ : ℝ) (i : ι) :
    Integrable (fun ω : ΩX × ΩY =>
      (|X ω.1 i| + |Y ω.2 i|) *
        Real.exp (|γ| * ∑ j, (|X ω.1 j| + |Y ω.2 j|))) (PX.prod PY) := by
  classical
  let Z : ΩX × ΩY → Sum ι ι → ℝ := fun ω k => match k with
    | Sum.inl i => X ω.1 i
    | Sum.inr i => Y ω.2 i
  have hZ := independent_product_concat_isCenteredJointlyGaussian PX PY X Y hX hY
  have h (k : Sum ι ι) :=
    (centeredJointlyGaussian_coordinate_mul_abs_linear_exp_integrable
      (PX.prod PY) Z hZ (fun _ => |γ|) k).abs
  convert (h (.inl i)).add (h (.inr i)) using 1
  funext ω
  simp [Z, abs_mul, abs_of_pos (Real.exp_pos _), Fintype.sum_sum_type,
    Finset.sum_add_distrib, Finset.mul_sum, add_mul, mul_add, Pi.add_apply]


/-- The locally uniform test-derivative envelope is integrable. -/
theorem kahaneInterpolatedDerivativeEnvelope_integrable
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian PX X) (hY : DOZZ.IsCenteredJointlyGaussian PY Y)
    (vX vY a : ι → ℝ) (γ ε B : ℝ) :
    Integrable (fun ω : ΩX × ΩY =>
      B * (∑ i, a i) * Real.exp (|γ| * ∑ i, (|X ω.1 i| + |Y ω.2 i|)) *
        (|γ| / (2 * Real.sqrt ε) * (∑ i, (|X ω.1 i| + |Y ω.2 i|)) +
          γ ^ 2 / 2 * ∑ i, |vX i - vY i|)) (PX.prod PY) := by
  classical
  have hE := kahaneEndpointAbsExp_integrable PX PY X Y hX hY γ
  have hS := integrable_finsetSum (Finset.univ : Finset ι)
    (fun i _ => kahaneEndpointCoordinateAbsExp_integrable PX PY X Y hX hY γ i)
  have h := ((hS.const_mul (|γ| / (2 * Real.sqrt ε))).add
    (hE.const_mul (γ ^ 2 / 2 * ∑ i, |vX i - vY i|))).const_mul (B * ∑ i, a i)
  apply h.congr
  filter_upwards [] with ω
  simp only [Pi.add_apply]
  rw [← Finset.sum_mul]
  ring

end DOZZ.Proofs
