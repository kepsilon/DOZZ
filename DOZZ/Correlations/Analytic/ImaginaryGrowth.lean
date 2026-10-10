/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.ImaginaryPinBound

/-! Linear cutoff growth of the imaginary normalization. -/

@[expose] public section
open MeasureTheory
namespace DOZZ.Proofs

/-- The exact deterministic exponent from the norm tilt is bounded by a constant times
`(r + 1)` times the squared imaginary charge size. -/
theorem normalized_imaginary_growth
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (γ : ℝ) (hγ : γ ≠ 0) (z : Fin N → ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 ≤ r → ∀ β : Fin (N + 1) → ℂ,
      (normalizedVertexPolynomial P Xc γ z r β).re +
        gaussianVariance P (fun ω => ∑ i, (β i).re *
          Xc ω (mixedVertexCenters z i) (mixedVertexTimes N r i)) / 2 +
        (γ * ∑ i, (β i.castSucc).re * equatorCircleMean (z i) r) *
          (complexMomentPower γ β).re ≤
        C * (r + 1) * ∑ i, (β i).im ^ 2 := by
  classical
  obtain ⟨C, hC, hv⟩ := mixed_vertex_variance_growth P X Xc hX hc z
  let B : ℝ := 1 + ∑ i, (Real.log (normPlus (z i)) + 1)
  have hB : 0 < B := by
    dsimp only [B]
    have := Finset.sum_nonneg (s := Finset.univ)
      (f := fun i : Fin N => Real.log (normPlus (z i)) + 1)
      (fun i _ => by linarith [CirclePotential.log_normPlus_nonneg (z i)])
    linarith
  have hpin (i : Fin N) (r : ℝ) (hr : 0 ≤ r) :
      |equatorCircleMean (z i) r| ≤ B := by
    have he := equator_circle_mean_abs_le (z i) r
    have he1 : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr)
    have hi := Finset.single_le_sum
      (f := fun j : Fin N => Real.log (normPlus (z j)) + 1)
      (fun j _ => by linarith [CirclePotential.log_normPlus_nonneg (z j)]) (Finset.mem_univ i)
    have ha := abs_add_le (equatorCircleMean (z i) r - Real.log (normPlus (z i)))
      (Real.log (normPlus (z i)))
    rw [sub_add_cancel, abs_of_nonneg (CirclePotential.log_normPlus_nonneg (z i))] at ha
    dsimp only [B]
    linarith
  refine ⟨C / 2 + B * (N + 1 : ℕ), by positivity, ?_⟩
  intro r hr β
  rw [normalized_imaginary_factor P Xc hc.2.1 γ z r β,
    complexMomentPower_im_scaled γ hγ β]
  have hb := imaginary_pin_le (fun i => (β i).im)
    (fun i => equatorCircleMean (z i) r) B hB.le (fun i => hpin i r hr)
  have hvar := hv r hr (fun i => (β i).im)
  have hs : 0 ≤ ∑ i, (β i).im ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hn : (0 : ℝ) ≤ (N + 1 : ℕ) := Nat.cast_nonneg _
  calc
    _ ≤ C * (r + 1) * (∑ i, (β i).im ^ 2) / 2 +
        B * (N + 1 : ℕ) * ∑ i, (β i).im ^ 2 := by linarith
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hB.le hn) (mul_nonneg hr hs)]

end DOZZ.Proofs
