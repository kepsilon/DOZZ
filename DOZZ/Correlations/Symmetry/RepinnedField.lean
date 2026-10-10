/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Symmetry.ReflectionTest
public import DOZZ.Statements.Defs.IsEquatorGFF
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
@[expose] public section
open MeasureTheory Set
open scoped Distributions
namespace DOZZ.Proofs

/-- The Lebesgue mass of a test density, as a continuous distribution. -/
noncomputable def symmetryTestIntegralCLM : TestFn →L[ℝ] ℝ :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ)
    volume (fun _ : ℂ => (1 : ℝ))

/-- The continuous mass functional has its intended integral value. -/
theorem symmetryTestIntegralCLM_apply (f : TestFn) :
    symmetryTestIntegralCLM f = ∫ x, f x := by
  rw [symmetryTestIntegralCLM,
    TestFunction.integralAgainstBilinCLM_eq_integral
      ((locallyIntegrable_const (1 : ℝ)).locallyIntegrableOn univ)]
  simp only [ContinuousLinearMap.mul_apply', mul_one]

/-- Actual correlated affine re-pinning on the original probability space. -/
noncomputable def symmetryRepinnedField
    {Ω : Type*} (X : Ω → Distr) (L : Ω → ℝ) (ω : Ω) : Distr :=
  { toFun := fun f => X ω (symmetryReflectionTestCLM f) - L ω * symmetryTestIntegralCLM f
    map_add' := by
      intro f g
      rw [map_add, map_add, map_add]
      ring
    map_smul' := by
      intro c f
      rw [map_smul, map_smul, map_smul]
      simp only [smul_eq_mul, RingHom.id_apply]
      ring
    cont := ((X ω).continuous.comp symmetryReflectionTestCLM.continuous).sub
      (continuous_const.mul symmetryTestIntegralCLM.continuous) }

/-- Every re-pinned evaluation retains the correlated scalar subtraction. -/
theorem symmetryRepinnedField_apply
    {Ω : Type*} (X : Ω → Distr) (L : Ω → ℝ) (ω : Ω) (f : TestFn) :
    symmetryRepinnedField X L ω f = X ω (symmetryReflectionTest f) - L ω * ∫ x, f x := by
  change X ω (symmetryReflectionTestCLM f) - L ω * symmetryTestIntegralCLM f = _
  rw [symmetryTestIntegralCLM_apply]
  rfl

/-- Re-pinned test evaluations are measurable whenever the source field and scalar are. -/
theorem symmetryRepinnedField_eval_measurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (L : Ω → ℝ) (hL : Measurable L) (f : TestFn) :
    Measurable (fun ω => symmetryRepinnedField X L ω f) := by
  simp only [symmetryRepinnedField_apply]
  exact ((hX.2 (symmetryReflectionTest f)).1).sub (hL.mul_const _)
end DOZZ.Proofs
