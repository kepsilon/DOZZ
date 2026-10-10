/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.ImaginaryNormalization
public import Mathlib.Algebra.Order.Chebyshev

/-! A diagonal variance bound for the imaginary Wick factor. -/

@[expose] public section
open MeasureTheory
namespace DOZZ.Proofs

/-- A finite linear combination's variance is bounded using only the individual second moments.
The coordinates need not be independent. -/
theorem vertex_variance_le_card_sum
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) (L : I → Ω → ℝ) (hm : ∀ i, MemLp (L i) 2 P) (a : I → ℝ) :
    gaussianVariance P (fun ω => ∑ i, a i * L i ω) ≤
      Fintype.card I * ∑ i, a i ^ 2 * gaussianVariance P (L i) := by
  classical
  let Z (i : I) (ω : Ω) := a i * L i ω
  have hZ (i : I) : MemLp (Z i) 2 P := (hm i).const_mul (a i)
  have hs : MemLp (fun ω => ∑ i, Z i ω) 2 P :=
    memLp_finsetSum Finset.univ (fun i _ => hZ i)
  have hi (i : I) : Integrable (fun ω => Z i ω ^ 2) P := by
    simpa only [sq, Pi.mul_def] using (hZ i).integrable_mul (hZ i)
  have hsi : Integrable (fun ω => (∑ i, Z i ω) ^ 2) P := by
    simpa only [sq, Pi.mul_def] using hs.integrable_mul hs
  have hsum : Integrable (fun ω => ∑ i, Z i ω ^ 2) P :=
    integrable_finsetSum Finset.univ (fun i _ => hi i)
  have hb := integral_mono_ae hsi (hsum.const_mul (Fintype.card I : ℝ))
    (Filter.Eventually.of_forall (fun ω => by
      simpa only [Finset.card_univ] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => Z i ω))))
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hi i)] at hb
  have he (i : I) : (∫ ω, Z i ω ^ 2 ∂P) = a i ^ 2 * gaussianVariance P (L i) := by
    unfold gaussianVariance gaussianCovariance
    have hpoint : (fun ω => Z i ω ^ 2) =
        (fun ω => a i ^ 2 * (L i ω * L i ω)) := by
      funext ω
      dsimp only [Z]
      ring
    rw [hpoint, integral_const_mul]
  simp_rw [he] at hb
  simpa only [gaussianVariance, gaussianCovariance, Z, sq] using hb

/-- The actual circle coordinate's raw second moment includes both regular equator pins. -/
theorem circle_raw_variance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (z : ℂ) (r : ℝ) :
    gaussianVariance P (fun ω => Xc ω z r) = r + 2 * equatorCircleMean z r := by
  obtain ⟨_, hm⟩ := circleAverage_isGaussianProcess P X Xc hX hc
  have he : gaussianVariance P (fun ω => Xc ω z r) =
      ProbabilityTheory.covariance (fun ω => Xc ω z r) (fun ω => Xc ω z r) P := by
    simp only [gaussianVariance, gaussianCovariance, ProbabilityTheory.covariance,
      hm z r, sub_zero]
  rw [he, circle_covariance_concentric P X Xc hX hc, min_self]
  ring

/-- The joint imaginary vertex variance grows at most linearly in the cutoff time, uniformly
in the imaginary charge vector. -/
theorem mixed_vertex_variance_growth
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (z : Fin N → ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ), 0 ≤ r → ∀ a : Fin (N + 1) → ℝ,
      gaussianVariance P (fun ω => ∑ i, a i *
        Xc ω (mixedVertexCenters z i) (mixedVertexTimes N r i)) ≤
        C * (r + 1) * ∑ i, a i ^ 2 := by
  classical
  let B : ℝ := 1 + ∑ i, (Real.log (normPlus (z i)) + 1)
  have hB : 1 ≤ B := by
    dsimp only [B]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => by
      linarith [CirclePotential.log_normPlus_nonneg (z i)]))
  have hpin (i : Fin N) (r : ℝ) (hr : 0 ≤ r) : equatorCircleMean (z i) r ≤ B := by
    have he := equator_circle_mean_abs_le (z i) r
    have he1 : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr)
    have hi : Real.log (normPlus (z i)) + 1 ≤
        ∑ j, (Real.log (normPlus (z j)) + 1) :=
      Finset.single_le_sum (f := fun j : Fin N => Real.log (normPlus (z j)) + 1) (fun j _ => by linarith [CirclePotential.log_normPlus_nonneg (z j)])
        (Finset.mem_univ i)
    have ha := le_abs_self (equatorCircleMean (z i) r - Real.log (normPlus (z i)))
    dsimp only [B]
    linarith
  refine ⟨(N + 1 : ℕ) * (1 + 2 * B), by positivity, ?_⟩
  intro r hr a
  have hdiag (i : Fin (N + 1)) :
      gaussianVariance P (fun ω => Xc ω (mixedVertexCenters z i)
        (mixedVertexTimes N r i)) ≤ (1 + 2 * B) * (r + 1) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [mixedVertexCenters, mixedVertexTimes, Fin.snoc_last]
      rw [circle_raw_variance P X Xc hX hc, outward_equator_mean r hr]
      nlinarith
    · simp only [mixedVertexCenters, mixedVertexTimes, Fin.snoc_castSucc]
      rw [circle_raw_variance P X Xc hX hc]
      have hi := hpin j r hr
      nlinarith
  have hv := vertex_variance_le_card_sum P
    (fun i ω => Xc ω (mixedVertexCenters z i) (mixedVertexTimes N r i))
    (fun i => hc.2.1 _ _) a
  calc
    _ ≤ (N + 1 : ℕ) * ∑ i, a i ^ 2 *
        gaussianVariance P (fun ω => Xc ω (mixedVertexCenters z i)
          (mixedVertexTimes N r i)) := by simpa using hv
    _ ≤ (N + 1 : ℕ) * ∑ i, a i ^ 2 * ((1 + 2 * B) * (r + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hdiag i) (sq_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

end DOZZ.Proofs
