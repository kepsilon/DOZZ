/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GMCChartPartition

/-! The definition `DOZZ.regularizedCoulombMass`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Chartwise regularized `U_N` mass `Z_r`. The finite chart softens each root distance at
`e^{-r}` and uses `normPlus` for a root at infinity. In the inverted chart finite roots have
weight `normPlus u / (‖1-z*u‖+e^{-r})`, while the root at infinity has
`normPlus u / (‖u‖+e^{-r})`. Its cutoff field is `Xc(1/u,e^{-r})`; pulling the original circle
back through inversion gives center `u/(1-e^{-2r}‖u‖²)` and radius
`e^{-r}‖u‖²/(1-e^{-2r}‖u‖²)`. -/
noncomputable def regularizedCoulombMass {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ) (γ : ℝ) (partition : GMCChartPartition)
    {N : ℕ} (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf : ℝ) (r : ℝ) (ω : Ω) : ℝ≥0∞ :=
  (∫⁻ x, (partition.finiteWeight x : ℝ≥0∞) *
      (∏ k, ENNReal.rpow
        (ENNReal.ofReal (normPlus x / (‖x - z k‖ + Real.exp (-r)))) (γ * α k)) *
      ENNReal.rpow (ENNReal.ofReal (normPlus x)) (γ * αinf)
        ∂regularizedGMC P Xc γ r ω) +
    ∫⁻ u, (partition.infinityWeight u : ℝ≥0∞) *
      (∏ k, ENNReal.rpow
        (ENNReal.ofReal (normPlus u / (‖1 - z k * u‖ + Real.exp (-r)))) (γ * α k)) *
      ENNReal.rpow (ENNReal.ofReal
        (normPlus u / (‖u‖ + Real.exp (-r)))) (γ * αinf)
        ∂regularizedGMC P (fun ω' u' δ => Xc ω' (u'⁻¹) δ) γ r ω

end DOZZ
