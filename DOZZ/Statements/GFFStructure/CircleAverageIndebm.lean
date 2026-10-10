/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GFFStructure.CircleLogPotential
import DOZZ.GFFStructure.CircleCovariance

/-! The statement `DOZZ.circleAverage_indebm`, proved by `DOZZ.Proofs.circleAverage_indebm`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

universe u

namespace DOZZ

/-- Sigma-algebra form of [KRV, Remark 2.2], including tangent disks. Function-valued independence
uses all coordinate cylinders. -/
theorem circleAverage_indebm {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (r₀ : ℝ) (hr₀ : 0 ≤ r₀)
    {n : ℕ} (c : Fin n → ℂ) (hout : ∀ i, 2 ≤ ‖c i‖)
    (hsep : ∀ i j, i ≠ j → 2 ≤ dist (c i) (c j)) :
    (∀ i, IsPreBrownianReal
      (fun t : ℝ≥0 => fun ω => Xc ω (c i) (r₀ + t) - Xc ω (c i) r₀) P) ∧
    iIndepFun (fun i => fun ω => fun t : ℝ≥0 => Xc ω (c i) (r₀ + t) - Xc ω (c i) r₀) P ∧
    IndepFun (fun ω => fun i => fun t : ℝ≥0 => Xc ω (c i) (r₀ + t) - Xc ω (c i) r₀)
      (fun ω => fun f : {f : TestFn // tsupport f ⊆ (⋃ i, ball (c i) (Real.exp (-r₀)))ᶜ} =>
        X ω f.val) P := by exact DOZZ.Proofs.circleAverage_indebm P X Xc hX hc r₀ hr₀ c hout hsep

end DOZZ
