/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.MixedRetainedKernel
public import DOZZ.Correlations.Analytic.MixedRealVertexTilt
public import DOZZ.Correlations.Analytic.JointVertexVariance

/-! Exact real values of the jointly normalized mixed-frame retained observable. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- The equator normalization cancels the tilted mass constant exactly. The formula is valid
for every real power; finiteness is supplied separately by the proved moment bounds. -/
theorem normalized_real_vertex_tilt
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (β : Fin (N + 1) → ℝ) (z : Fin N → ℂ) (r : ℝ) (hr : 0 ≤ r)
    (O : Set ℂ) (ho : MeasurableSet O) (hO : O ⊆ retainedRegion z r) (p : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp
      ((∑ i, β i * Xc ω (mixedVertexCenters z i) (mixedVertexTimes N r i)) -
        gaussianVariance P (fun ω' => ∑ i, β i *
          Xc ω' (mixedVertexCenters z i) (mixedVertexTimes N r i)) / 2 -
        p * γ * ∑ i, β i.castSucc * equatorCircleMean (z i) r)) * M ω O ^ p ∂P) =
      ∫⁻ ω, (∫⁻ x in O,
        coulombWeight γ (fun i => β i.castSucc) z (β (Fin.last N)) x ∂M ω) ^ p ∂P := by
  let A := γ * ∑ i, β i.castSucc * equatorCircleMean (z i) r
  let C := ENNReal.ofReal (Real.exp A)
  let K := ENNReal.ofReal (Real.exp (-p * A))
  have hc0 : C ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hct : C ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcancel : K * C ^ p = 1 := by
    dsimp only [K, C]
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul,
      ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    rw [show -p * A + A * p = 0 by ring, Real.exp_zero, ENNReal.ofReal_one]
  let L (ω : Ω) := ∑ i, β i * Xc ω (mixedVertexCenters z i) (mixedVertexTimes N r i)
  have he (ω : Ω) : ENNReal.ofReal (Real.exp
      (L ω - gaussianVariance P L / 2 - p * γ *
        ∑ i, β i.castSucc * equatorCircleMean (z i) r)) =
      K * ENNReal.ofReal (Real.exp (L ω - gaussianVariance P L / 2)) := by
    dsimp only [K]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 2
    dsimp only [A]
    ring
  change (∫⁻ ω, ENNReal.ofReal (Real.exp (L ω - gaussianVariance P L / 2 -
    p * γ * ∑ i, β i.castSucc * equatorCircleMean (z i) r)) * M ω O ^ p ∂P) = _
  simp_rw [he, mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    mixed_vertex_tilt_retained_mass P X hX γ hγ hγ2 M hM Xc hXc β
      (mixedVertexCenters z) (mixedVertexTimes N r) O ho p]
  simp_rw [mixed_tilted_retained_measure_eq _ γ β z r hr O ho hO]
  change K * (∫⁻ ω, (C * ∫⁻ x in O,
    coulombWeight γ (fun i => β i.castSucc) z (β (Fin.last N)) x ∂M ω) ^ p ∂P) = _
  simp_rw [ennreal_mul_rpow_of_ne_zero_ne_top C _ hc0 hct p]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero hc0 hct),
    ← mul_assoc, hcancel, one_mul]

end DOZZ.Proofs
