/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfCrossingMultiplier
public import DOZZ.Statements.Hypergeom.PlanarGaussConstant
public import DOZZ.ShiftEquations.Rbar.Multiplier
import Mathlib.Tactic

/-! # The literal half-charge crossing multiplier

The coefficient extracted from the connection matrix multiplies the unreflected
fusion coefficient at epsilon. This file checks the resulting expression against
the crossing multiplier `gammaHalfCrossingMultiplier`, with all Gamma arguments and signs
retained.
-/

public section
namespace DOZZ.Proofs

/-- On real inputs the planar Gauss constant is a real l-ratio, including its
totalized values. -/
theorem crossing_planarGauss_real (γ ε : ℝ) :
    (planarGaussConstant (γ ^ 2 / 2) (γ * ε)).re =
      Real.pi / (lR (γ * ε / 2) * lR (-(γ ^ 2) / 4) *
        lR (2 + γ ^ 2 / 4 - γ * ε / 2)) := by
  unfold planarGaussConstant
  have hneg : -(γ ^ 2 / 2) / 2 = -(γ ^ 2) / 4 := by ring
  have hlast : 2 - γ * ε / 2 + γ ^ 2 / 2 / 2 = 2 + γ ^ 2 / 4 - γ * ε / 2 := by ring
  rw [hneg, hlast]
  simp only [lFun_ofReal_eq_lR, ← Complex.ofReal_mul, ← Complex.ofReal_div,
    Complex.ofReal_re]

/-- Combining the connection ratio and the epsilon-channel fusion coefficient produces the exact
multiplier `gammaHalfCrossingMultiplier`. No nonzero denominator is hidden here. -/
theorem crossing_connection_times_fusion (γ μ a ε c : ℝ) :
    (lR (gaussParameterA γ (γ / 2) a ε c) *
      lR (gaussParameterB γ (γ / 2) a ε c) /
      (lR (gaussParameterC γ (γ / 2) a) *
        lR (gaussParameterA γ (γ / 2) a ε c +
          gaussParameterB γ (γ / 2) a ε c - gaussParameterC γ (γ / 2) a))) *
      (-μ * (planarGaussConstant (γ ^ 2 / 2) (γ * ε)).re) =
        gammaHalfCrossingMultiplier γ μ a ε c := by
  rw [crossing_planarGauss_real]
  unfold gammaHalfCrossingMultiplier
  simp only [lFun_ofReal_re_eq_lR, div_eq_mul_inv, mul_inv]
  ring

end DOZZ.Proofs
