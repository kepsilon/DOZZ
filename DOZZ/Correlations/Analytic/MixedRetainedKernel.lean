/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.NormalizedVertexHolomorphy
public import DOZZ.Correlations.Analytic.OutwardVertexKernel

/-! Exact retained Coulomb kernels for the mixed finite and infinity frame. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- The Coulomb weight including the infinity charge is the exponential of its logarithmic
potential away from the finite roots. -/
theorem coulomb_weight_exp_log_infinity {N : ℕ} (γ : ℝ) (α : Fin N → ℝ)
    (z : Fin N → ℂ) (αinf : ℝ) (x : ℂ) (hx : ∀ i, x ≠ z i) :
    coulombWeight γ α z αinf x = ENNReal.ofReal
      (Real.exp ((∑ i, γ * α i * Real.log (normPlus x / ‖x - z i‖)) +
        γ * αinf * Real.log (normPlus x))) := by
  have hn : 0 < normPlus x := lt_of_lt_of_le one_pos (le_max_left _ _)
  have he : coulombWeight γ α z αinf x = coulombWeight γ α z 0 x *
      ENNReal.ofReal (normPlus x) ^ (γ * αinf) := by
    unfold coulombWeight
    simp only [mul_zero, ENNReal.rpow_eq_pow, ENNReal.rpow_zero, mul_one]
  rw [he, coulomb_weight_exp_log γ α z x hx,
    ENNReal.ofReal_rpow_of_pos hn, Real.rpow_def_of_pos hn,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2
  ring_nf

/-- On the retained region, mixed circle averaging produces precisely the finite Coulomb
weight with the final charge at infinity, times the finite equator pin factor. -/
theorem mixed_retained_vertex_density {N : ℕ} (γ : ℝ)
    (β : Fin (N + 1) → ℝ) (z : Fin N → ℂ) (r : ℝ) (hr : 0 ≤ r)
    (x : ℂ) (hx : x ∈ retainedRegion z r) :
    ENNReal.ofReal (Real.exp (γ * ∑ i, β i *
      ∫ v, gffKernel x v ∂circleMeasure (mixedVertexCenters z i)
        (mixedVertexTimes N r i))) =
      ENNReal.ofReal (Real.exp (γ * ∑ i, β i.castSucc * equatorCircleMean (z i) r)) *
        coulombWeight γ (fun i => β i.castSucc) z (β (Fin.last N)) x := by
  have hne (i : Fin N) : x ≠ z i := by
    intro he
    have hh := hx.2 i
    simp only [he, sub_self, norm_zero] at hh
    exact (not_lt_of_ge (Real.exp_pos _).le) hh
  rw [coulomb_weight_exp_log_infinity γ (fun i => β i.castSucc) z (β (Fin.last N)) x hne,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2
  rw [Fin.sum_univ_castSucc]
  simp only [mixedVertexCenters, mixedVertexTimes, Fin.snoc_castSucc,
    Fin.snoc_last]
  rw [outward_vertex_potential x r hr hx.1.le]
  simp_rw [retained_vertex_potential x _ r (hx.2 _).le, mul_add]
  rw [Finset.sum_add_distrib]
  simp only [mul_add, Finset.mul_sum]
  ring_nf

/-- The mixed tilted measure on a retained region is exactly the singular Coulomb mass,
including the charge at infinity and its deterministic equator factor. -/
theorem mixed_tilted_retained_measure_eq {N : ℕ}
    (μ : Measure ℂ) (γ : ℝ) (β : Fin (N + 1) → ℝ) (z : Fin N → ℂ) (r : ℝ) (hr : 0 ≤ r)
    (O : Set ℂ) (ho : MeasurableSet O) (hO : O ⊆ retainedRegion z r) :
    μ.withDensity (fun x => ENNReal.ofReal (Real.exp (γ * ∑ i, β i *
      ∫ v, gffKernel x v ∂circleMeasure (mixedVertexCenters z i)
        (mixedVertexTimes N r i)))) O =
      ENNReal.ofReal (Real.exp (γ * ∑ i, β i.castSucc * equatorCircleMean (z i) r)) *
        ∫⁻ x in O, coulombWeight γ (fun i => β i.castSucc) z (β (Fin.last N)) x ∂μ := by
  rw [withDensity_apply _ ho,
    ← lintegral_const_mul _ (measurable_coulombWeight γ (fun i => β i.castSucc) z (β (Fin.last N)))]
  apply setLIntegral_congr_fun ho
  intro x hx
  exact mixed_retained_vertex_density γ β z r hr x (hO hx)

end DOZZ.Proofs
