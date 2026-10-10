/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.CircleAverageL2Limit

/-!
# Coordinatewise circle limits

The canonical L² circle limits form a centered jointly Gaussian family on the original field's
probability space. Each coordinate has a representative measurable in the raw distribution
evaluation sigma algebra.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace DOZZ.Proofs

/-- Raw measurable representatives of the canonical circle L² family. -/
theorem exists_equatorGFF_circle_L2_family
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (X : Ω → Distr) (hX : IsEquatorGFF P X) :
    ∃ f : (ℂ × ℝ) → ℕ → TestFn, ∃ W : (ℂ × ℝ) → Lp ℝ 2 P,
      ∃ Y : (ℂ × ℝ) → Ω → ℝ,
        (∀ p, Tendsto (fun n => circleEnergyGap p.1 p.2 (f p n)) atTop (𝓝 0)) ∧
        (∀ p y s, Tendsto (fun n => circleCross y s (f p n)) atTop
          (𝓝 (∫ z, ∫ w, gffKernel z w ∂circleMeasure y s ∂circleMeasure p.1 p.2))) ∧
        (∀ p, Tendsto (fun n => (equatorGFF_test_memLp X hX (f p n)).toLp
          (fun ω => X ω (f p n))) atTop (𝓝 (W p))) ∧
        (∀ p, Measurable[equatorGFFRawDistributionSigma X] (Y p) ∧
          Measurable (Y p) ∧ MemLp (Y p) 2 P ∧ Y p =ᵐ[P] ⇑(W p) ∧
          Tendsto (fun n => eLpNorm (fun ω => X ω (f p n) - Y p ω) 2 P)
            atTop (𝓝 0)) ∧
        IsGaussianProcess (fun p ω => Y p ω) P := by
  let : IsProbabilityMeasure P := hX.1
  have hlim (p : ℂ × ℝ) :=
    exists_equatorGFF_circle_test_L2_limit_with_cross X hX p.1 p.2
  choose f W hgap hcross hW using hlim
  have hrep (p : ℂ × ℝ) :=
    exists_measurable_equatorGFF_circle_L2_limit X hX (f p) (W p) (hW p)
  choose Y hYraw hYm hYmem hYae hYlim using hrep
  refine ⟨f, W, Y, hgap, hcross, hW, ?_, ?_⟩
  · intro p
    exact ⟨hYraw p, hYm p, hYmem p, hYae p, hYlim p⟩
  · apply isGaussianProcess_of_eLpNorm_sub
      (fun n p ω => X ω (f p n)) Y
    · intro n
      exact equatorGFF_test_family_isGaussianProcess X hX (fun p => f p n)
    · intro p
      exact hYmem p
    · intro p
      exact hYlim p

end DOZZ.Proofs
