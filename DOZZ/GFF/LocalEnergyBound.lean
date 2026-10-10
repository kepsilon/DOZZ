/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.EquatorField
public import DOZZ.GFF.LocalSchur

/-!
# DOZZ.GFF.LocalEnergyBound

The G4 map is bounded in local `L²` by the square-integrable covariance kernel. This is the
continuity estimate used when comparing Fourier approximations to a test function.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped InnerProductSpace Topology

namespace DOZZ

/-- On tests supported in a fixed ball, the G4 map's squared norm is controlled by the local
`L²` norm and the `L²` norm of the covariance kernel on the product ball. -/
theorem norm_sq_equatorKernelLimitMap_le_localL2 (R : ℝ) (f : TestFn)
    (hsupp : Function.support f ⊆ ball (0 : ℂ) R) :
    ‖equatorKernelLimitMap f‖ ^ 2 ≤
      (∫ p : ℂ × ℂ in ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R,
        ‖gffKernel p.1 p.2‖ ^ 2) ^ (1 / 2 : ℝ) *
        (∫ x in ball (0 : ℂ) R, ‖f x‖ ^ 2) := by
  have hnorm : ‖equatorKernelLimitMap f‖ ^ 2 = gffCov f f := by
    calc
      ‖equatorKernelLimitMap f‖ ^ 2 =
          ⟪equatorKernelLimitMap f, equatorKernelLimitMap f⟫_ℝ := by
            symm
            exact inner_self_eq_norm_sq_to_K _
      _ = gffCov f f := inner_equatorKernelLimitMap_eq_gffCov f f
  rw [hnorm]
  exact (le_abs_self _).trans (abs_gffCov_self_le_localL2 R f hsupp)


end DOZZ

end
