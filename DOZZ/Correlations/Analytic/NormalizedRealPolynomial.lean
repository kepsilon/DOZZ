/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.NormalizedRealTilt

/-! Real restriction of the complex joint Wick and equator normalization. -/

@[expose] public section
open MeasureTheory
namespace DOZZ.Proofs

/-- The complex affine mass power restricts to the literal real zero-mode power. -/
theorem complexMomentPower_ofReal {N : ℕ} (γ : ℝ) (β : Fin N → ℝ) :
    complexMomentPower γ (fun i => (β i : ℂ)) =
      (((2 * Q γ - ∑ i, β i) / γ : ℝ) : ℂ) := by
  unfold complexMomentPower
  push_cast
  ring

/-- On real charges the joint Wick polynomial is minus half the actual joint variance. -/
theorem jointVertexPolynomial_ofReal
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ)
    (z : Fin N → ℂ) (r : Fin N → ℝ)
    (hm : ∀ i, MemLp (fun ω => Xc ω (z i) (r i)) 2 P) (β : Fin N → ℝ) :
    jointVertexPolynomial P Xc z r (fun i => (β i : ℂ)) =
      ((-gaussianVariance P (fun ω => ∑ i, β i * Xc ω (z i) (r i)) / 2 : ℝ) : ℂ) := by
  rw [vertex_variance_expansion P _ hm β]
  unfold jointVertexPolynomial
  push_cast
  rfl

/-- The full complex normalization restricts to the real jointly Wick-normalized tilt density
with the exact deterministic pin cancellation. -/
theorem normalizedVertexPolynomial_ofReal
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ)
    (hmem : ∀ z r, MemLp (fun ω => Xc ω z r) 2 P)
    (γ : ℝ) (z : Fin N → ℂ) (r : ℝ) (β : Fin (N + 1) → ℝ) :
    normalizedVertexPolynomial P Xc γ z r (fun i => (β i : ℂ)) =
      ((-gaussianVariance P (fun ω => ∑ i, β i * Xc ω (mixedVertexCenters z i)
          (mixedVertexTimes N r i)) / 2 -
        ((2 * Q γ - ∑ i, β i) / γ) * γ *
          ∑ i, β i.castSucc * equatorCircleMean (z i) r : ℝ) : ℂ) := by
  unfold normalizedVertexPolynomial
  rw [jointVertexPolynomial_ofReal P Xc _ _ (fun i => hmem _ _) β,
    complexMomentPower_ofReal]
  push_cast
  rfl

end DOZZ.Proofs
