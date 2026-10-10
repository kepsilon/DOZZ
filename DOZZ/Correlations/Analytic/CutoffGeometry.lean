/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.RetainedNegativeMoments

/-! The geometric requirements for the analytic cutoff hold eventually. -/

@[expose] public section
open Filter Topology
namespace DOZZ.Proofs

/-- Shrinking insertion disks, growing exterior radii, and the fixed lower disk are compatible
for every sufficiently large natural cutoff. -/
theorem retained_cutoff_geometry_eventually {N : ℕ} (z : Fin N → ℂ)
    (δ R : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      2 * Real.exp (-(n : ℝ)) ≤ δ ∧ 1 ≤ Real.exp (n : ℝ) / 2 ∧
        (∀ i, 2 * ‖z i‖ ≤ Real.exp (n : ℝ) / 2) ∧ R + 2 ≤ Real.exp (n : ℝ) := by
  have he : Tendsto (fun n : ℕ => Real.exp (n : ℝ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop
  have hneg : Tendsto (fun n : ℕ => 2 * Real.exp (-(n : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul 2
  have hsmall : ∀ᶠ n : ℕ in atTop, 2 * Real.exp (-(n : ℝ)) ≤ δ :=
    (hneg.eventually_lt_const hδ).mono (fun _ h => h.le)
  have hlarge : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.exp (n : ℝ) / 2 := by
    filter_upwards [he.eventually_ge_atTop 2] with n hn
    linarith
  have hroot : ∀ᶠ n : ℕ in atTop, ∀ i, 2 * ‖z i‖ ≤ Real.exp (n : ℝ) / 2 := by
    rw [eventually_all]
    intro i
    filter_upwards [he.eventually_ge_atTop (4 * ‖z i‖)] with n hn
    linarith
  exact hsmall.and (hlarge.and (hroot.and (he.eventually_ge_atTop (R + 2))))

end DOZZ.Proofs
