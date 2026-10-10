/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.MixedRadiusGaussianClosure

/-! Uniform covariance potentials for mixed inward and outward circle vertices. -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction
namespace DOZZ.Proofs

/-- Finite sums commute with the uncentered second moment for square-integrable coordinates. -/
theorem gaussianCovariance_finset_sum_right
    {Ω I : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ) (L : I → Ω → ℝ) (S : Finset I)
    (hY : MemLp Y 2 P) (hL : ∀ i ∈ S, MemLp (L i) 2 P) :
    gaussianCovariance P Y (fun ω => ∑ i ∈ S, L i ω) =
      ∑ i ∈ S, gaussianCovariance P Y (L i) := by
  unfold gaussianCovariance
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  intro i hi
  simpa only [Pi.mul_def] using hY.integrable_mul (hL i hi)

/-- Mixed-radius vertices supply the global bounded continuous covariance potential required by
GMC tilt, with the exact averaged Green kernel as its value. -/
theorem mixed_circle_covariance_uniform
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (α : Fin N → ℝ) (z : Fin N → ℂ) (r : Fin N → ℝ) :
    ∃ c : BoundedContinuousFunction ℂ ℝ,
      (∀ x, c x = ∑ i, α i * ∫ v, gffKernel x v ∂circleMeasure (z i) (r i)) ∧
      TendstoUniformly (fun s x => gaussianCovariance P (fun ω => Xc ω x s)
        (fun ω => ∑ i, α i * Xc ω (z i) (r i))) c atTop := by
  classical
  have hsingle (i : Fin N) : ∃ c : BoundedContinuousFunction ℂ ℝ,
      (∀ x, c x = α i * ∫ v, gffKernel x v ∂circleMeasure (z i) (r i)) ∧
      TendstoUniformly (fun s x => gaussianCovariance P (fun ω => Xc ω x s)
        (fun ω => α i * Xc ω (z i) (r i))) c atTop := by
    simpa using circleAverage_sum_covariance_uniform P X hX Xc hXc
      (fun _ : Fin 1 => α i) (fun _ : Fin 1 => z i) (r i)
  choose c hc hconv using hsingle
  let C : BoundedContinuousFunction ℂ ℝ := ∑ i, c i
  have hC (x : ℂ) : C x = ∑ i, c i x := by simp [C]
  have hcov (s : ℝ) (x : ℂ) : gaussianCovariance P (fun ω => Xc ω x s)
      (fun ω => ∑ i, α i * Xc ω (z i) (r i)) =
      ∑ i, gaussianCovariance P (fun ω => Xc ω x s) (fun ω => α i * Xc ω (z i) (r i)) :=
    gaussianCovariance_finset_sum_right P _ _ Finset.univ (hXc.2.1 x s)
      (fun i _ => (hXc.2.1 (z i) (r i)).const_mul (α i))
  refine ⟨C, fun x => ?_, ?_⟩
  · simp only [hC, hc]
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hd : 0 < ε / (N + 1 : ℝ) := div_pos hε (by positivity)
    have he : ∀ᶠ s : ℝ in atTop, ∀ i : Fin N, ∀ x : ℂ,
        dist (c i x) (gaussianCovariance P (fun ω => Xc ω x s)
          (fun ω => α i * Xc ω (z i) (r i))) < ε / (N + 1 : ℝ) :=
      eventually_all.mpr fun i => (Metric.tendstoUniformly_iff.mp (hconv i)) _ hd
    filter_upwards [he] with s hs x
    rw [hC, hcov, Real.dist_eq, ← Finset.sum_sub_distrib]
    have hb : (∑ i : Fin N, |c i x - gaussianCovariance P (fun ω => Xc ω x s)
        (fun ω => α i * Xc ω (z i) (r i))|) ≤ N * (ε / (N + 1 : ℝ)) := by
      calc
        _ ≤ ∑ _ : Fin N, ε / (N + 1 : ℝ) :=
          Finset.sum_le_sum fun i _ => by simpa only [Real.dist_eq] using (hs i x).le
        _ = _ := by simp [nsmul_eq_mul]
    have hN : N * (ε / (N + 1 : ℝ)) < ε := by
      have hp : (0 : ℝ) < N + 1 := by positivity
      rw [← mul_div_assoc, div_lt_iff₀ hp]
      nlinarith
    exact (Finset.abs_sum_le_sum_abs _ _).trans hb |>.trans_lt hN

end DOZZ.Proofs
