/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosInterpolationCalculus
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Differentiation under expectation for the finite-chaos interpolation path. -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace DOZZ.Proofs

/-- The pointwise derivative of a scalar test of the Wick-normalized interpolation mass. -/
noncomputable def kahaneInterpolatedTestDerivative
    {ΩX ΩY ι : Type*} [Fintype ι]
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (vX vY a : ι → ℝ) (γ : ℝ) (F' : ℝ → ℝ)
    (s : ℝ) (ω : ΩX × ΩY) : ℝ :=
  F' (kahaneInterpolatedMass X Y vX vY a γ s ω) *
    ∑ i, a i * Real.exp
      (γ * (Real.sqrt s * X ω.1 i + Real.sqrt (1 - s) * Y ω.2 i) -
        γ ^ 2 / 2 * (s * vX i + (1 - s) * vY i)) *
      (γ * (X ω.1 i / (2 * Real.sqrt s) -
          Y ω.2 i / (2 * Real.sqrt (1 - s))) -
        γ ^ 2 / 2 * (vX i - vY i))

/-- Dominated differentiation of the finite-chaos interpolation expectation at an interior time.
The pointwise derivative is supplied by `kahaneInterpolatedTest_hasDerivAt`; the hypotheses here
are precisely the local measurability, integrability, and common integrable derivative bound used
by `hasDerivAt_integral_of_dominated_loc_of_deriv_le`. -/
theorem kahaneInterpolatedExpectation_hasDerivAt
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (vX vY a : ι → ℝ) (γ t ε : ℝ) (F F' : ℝ → ℝ)
    (hF : ∀ x, HasDerivAt F (F' x) x)
    (hε : 0 < ε) (hεleft : ε ≤ t) (hεright : ε ≤ 1 - t)
    (hMeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable
      (fun ω : ΩX × ΩY => F (kahaneInterpolatedMass X Y vX vY a γ s ω)) (PX.prod PY))
    (hInt : Integrable
      (fun ω : ΩX × ΩY => F (kahaneInterpolatedMass X Y vX vY a γ t ω)) (PX.prod PY))
    (hDMeas : AEStronglyMeasurable
      (fun ω : ΩX × ΩY => kahaneInterpolatedTestDerivative
        X Y vX vY a γ F' t ω) (PX.prod PY))
    (b : ΩX × ΩY → ℝ) (hb : Integrable b (PX.prod PY))
    (hbound : ∀ᵐ ω ∂(PX.prod PY), ∀ s ∈ Metric.ball t ε,
      ‖kahaneInterpolatedTestDerivative X Y vX vY a γ F' s ω‖ ≤ b ω) :
    HasDerivAt
      (fun s => ∫ ω : ΩX × ΩY,
        F (kahaneInterpolatedMass X Y vX vY a γ s ω) ∂(PX.prod PY))
      (∫ ω : ΩX × ΩY,
        kahaneInterpolatedTestDerivative X Y vX vY a γ F' t ω ∂(PX.prod PY)) t := by
  let I : ℝ → ΩX × ΩY → ℝ := fun s ω =>
    F (kahaneInterpolatedMass X Y vX vY a γ s ω)
  let D : ℝ → ΩX × ΩY → ℝ := fun s ω =>
    kahaneInterpolatedTestDerivative X Y vX vY a γ F' s ω
  have hInt' : Integrable (I t) (PX.prod PY) := by simpa [I] using hInt
  have hDMeas' : AEStronglyMeasurable (D t) (PX.prod PY) := by
    simpa [D] using hDMeas
  have hbound' : ∀ᵐ ω ∂(PX.prod PY), ∀ s ∈ Metric.ball t ε,
      ‖D s ω‖ ≤ b ω := by simpa [D] using hbound
  have hderiv : ∀ᵐ ω ∂(PX.prod PY), ∀ s ∈ Metric.ball t ε,
      HasDerivAt (I · ω) (D s ω) s := by
    filter_upwards [] with ω s hs
    have hdist : |s - t| < ε := by
      simpa [Real.dist_eq] using hs
    have hspos : 0 < s := by
      have := (abs_lt.mp hdist).1
      linarith
    have hslt : s < 1 := by
      have := (abs_lt.mp hdist).2
      linarith
    exact by
      simpa [I, D, kahaneInterpolatedTestDerivative] using
        (kahaneInterpolatedTest_hasDerivAt X Y vX vY a γ s ω F F' hF hspos hslt)
  have hdom := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds t hε) hMeas hInt' hDMeas' hbound' hb hderiv
  simpa [I, D] using hdom.2

end DOZZ.Proofs
