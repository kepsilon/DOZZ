module

public import DOZZ.Statements.Hypergeom.PlanarDifferenceKernel

/-! The complex Wirtinger kernel has the same absolute-value singularities as the real mixed
kernel. These reductions isolate the two-point power-integrability problem used in the sharp
derivative tests. -/

@[expose] public section

open MeasureTheory
open scoped Topology

namespace DOZZ.Proofs

/-- Away from its two singular points, the norm of the Wirtinger kernel is the corresponding
positive two-point power. -/
theorem norm_planarWirtingerKernel_eq (k β : ℝ) (z u : ℂ) (hu : u ≠ 0)
    (huz : u ≠ z) :
    ‖DOZZ.planarWirtingerKernel k β z u‖ =
      ‖u - z‖ ^ (k - 2) / ‖u‖ ^ β := by
  rw [DOZZ.planarWirtingerKernel, norm_div, Complex.norm_real, norm_mul,
    Complex.norm_pow]
  have hdiff : 0 < ‖u - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huz)
  have hu' : 0 < ‖u‖ := norm_pos_iff.mpr hu
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    show ‖z - u‖ = ‖u - z‖ by rw [← norm_neg, neg_sub],
    ← Real.rpow_natCast ‖u - z‖ 2]
  calc
    ‖u - z‖ ^ k / (‖u - z‖ ^ (2 : ℝ) * ‖u‖ ^ β) =
        (‖u - z‖ ^ k / ‖u - z‖ ^ (2 : ℝ)) / ‖u‖ ^ β := by ring
    _ = ‖u - z‖ ^ (k - 2) / ‖u‖ ^ β := by rw [← Real.rpow_sub hdiff]


end DOZZ.Proofs
