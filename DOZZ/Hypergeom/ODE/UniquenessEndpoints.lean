/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.Uniqueness

/-! Uniqueness from an arbitrary initial point in a disk, for overlap gluing. -/

@[expose] public section

open Set
open scoped NNReal

namespace DOZZ.Proofs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem holomorphic_linear_system_solution_unique_of_eq_at
    (c : ℂ) (r M : ℝ) (H : ℂ → E →L[ℂ] E) (hM : 0 ≤ M)
    (hHbound : ∀ z ∈ Metric.ball c r, ‖H z‖ ≤ M)
    {F G : ℂ → E}
    (hF : ∀ z ∈ Metric.ball c r, HasDerivAt F (H z (F z)) z)
    (hG : ∀ z ∈ Metric.ball c r, HasDerivAt G (H z (G z)) z)
    {z₀ z : ℂ} (hz₀ : z₀ ∈ Metric.ball c r) (hz : z ∈ Metric.ball c r)
    (heq : F z₀ = G z₀) : F z = G z := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  let path : ℝ → ℂ := AffineMap.lineMap z₀ z
  let fpath : ℝ → E := fun t => F (path t)
  let gpath : ℝ → E := fun t => G (path t)
  let v : ℝ → E → E := fun t x => (z - z₀) • H (path t) x
  let K : ℝ≥0 := ‖z - z₀‖₊ * M.toNNReal
  have hK : (K : ℝ) = ‖z - z₀‖ * M := by
    simp [K, hM, mul_comm]
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp hz)
  have hseg : MapsTo path (Icc (0 : ℝ) 1) (Metric.ball c r) :=
    (convex_ball c r).mapsTo_lineMap hz₀ hz
  have hv : ∀ t ∈ Ico (0 : ℝ) 1, LipschitzWith K (v t) := by
    intro t ht
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hw : path t ∈ Metric.ball c r := hseg (Ico_subset_Icc_self ht)
    have hHxy : ‖H (path t) x - H (path t) y‖ ≤ M * ‖x - y‖ := by
      calc
        ‖H (path t) x - H (path t) y‖ = ‖H (path t) (x - y)‖ := by rw [map_sub]
        _ ≤ ‖H (path t)‖ * ‖x - y‖ := (H (path t)).le_opNorm _
        _ ≤ M * ‖x - y‖ := mul_le_mul_of_nonneg_right (hHbound _ hw) (norm_nonneg _)
    have hvxy : v t x - v t y = (z - z₀) • (H (path t) x - H (path t) y) := by
      dsimp [v]
      rw [← smul_sub]
    rw [dist_eq_norm, hvxy, norm_smul]
    calc
      ‖z - z₀‖ * ‖H (path t) x - H (path t) y‖ ≤
          ‖z - z₀‖ * (M * ‖x - y‖) := mul_le_mul_of_nonneg_left hHxy (norm_nonneg _)
      _ = (K : ℝ) * dist x y := by rw [hK, dist_eq_norm]; ring
  have hFpath : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt fpath (v t (fpath t)) t := by
    intro t ht
    have hFt := hF (path t) (hseg ht)
    have hcomp := hFt.hasFDerivAt.restrictScalars ℝ |>.comp_hasDerivAt t
      (AffineMap.hasDerivAt_lineMap (a := z₀) (b := z))
    simpa [fpath, v, path, Function.comp_def, AffineMap.lineMap_apply_module] using hcomp
  have hGpath : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt gpath (v t (gpath t)) t := by
    intro t ht
    have hGt := hG (path t) (hseg ht)
    have hcomp := hGt.hasFDerivAt.restrictScalars ℝ |>.comp_hasDerivAt t
      (AffineMap.hasDerivAt_lineMap (a := z₀) (b := z))
    simpa [gpath, v, path, Function.comp_def, AffineMap.lineMap_apply_module] using hcomp
  have hFcont : ContinuousOn fpath (Icc (0 : ℝ) 1) :=
    continuousOn_of_forall_continuousAt fun t ht => (hFpath t ht).continuousAt
  have hGcont : ContinuousOn gpath (Icc (0 : ℝ) 1) :=
    continuousOn_of_forall_continuousAt fun t ht => (hGpath t ht).continuousAt
  have hFwithin : ∀ t ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt fpath (v t (fpath t)) (Ici t) t :=
    fun t ht => (hFpath t (Ico_subset_Icc_self ht)).hasDerivWithinAt
  have hGwithin : ∀ t ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt gpath (v t (gpath t)) (Ici t) t :=
    fun t ht => (hGpath t (Ico_subset_Icc_self ht)).hasDerivWithinAt
  have hEq := ODE_solution_unique_of_mem_Icc_right
    (fun t ht => (hv t ht).lipschitzOnWith)
    hFcont hFwithin (fun _ _ => mem_univ _)
    hGcont hGwithin (fun _ _ => mem_univ _)
    (by simpa [fpath, gpath, path] using heq)
  have hend := hEq (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  simpa [fpath, gpath, path] using hend

end DOZZ.Proofs
