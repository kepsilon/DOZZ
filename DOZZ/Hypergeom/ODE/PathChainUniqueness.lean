/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.PathLiftCharts

/-! Finite Picard chains along the same path have the same lift from a fixed initial value. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Two finite disk-chain lifts along the same path agree if they start at the same value. The
chains may use different radii, bounds, and subdivisions. -/
theorem disk_chain_lifts_unique
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (H : ℂ → E →L[ℂ] E) {F G : ℝ → E}
    (hFcont : ContinuousOn F (Icc (0 : ℝ) 1))
    (hGcont : ContinuousOn G (Icc (0 : ℝ) 1))
    (N₁ : ℕ) (hN₁ : 0 < N₁) (r₁ M₁ : ℝ) (hr₁ : 0 < r₁) (hM₁ : 0 ≤ M₁)
    (D₁ : ℕ → HolomorphicDiskSolution H r₁)
    (hcenters₁ : ∀ i ≤ N₁, (D₁ i).center = γ ((i : ℝ) / (N₁ : ℝ)))
    (hbound₁ : ∀ i ≤ N₁, ∀ z ∈ Metric.ball (D₁ i).center r₁, ‖H z‖ ≤ M₁)
    (hcover₁ : ∀ i < N₁, ∀ s ∈ Icc ((i : ℝ) / (N₁ : ℝ))
      (((i + 1 : ℕ) : ℝ) / (N₁ : ℝ)),
      γ s ∈ Metric.ball (D₁ i).center (r₁ / 2))
    (hoverlap₁ : ∀ i < N₁, ∀ z ∈ Metric.ball (D₁ (i + 1)).center (r₁ / 2),
      (D₁ i).solution z = (D₁ (i + 1)).solution z)
    (hFformula : ∀ i < N₁, ∀ s ∈ Icc ((i : ℝ) / (N₁ : ℝ))
      (((i + 1 : ℕ) : ℝ) / (N₁ : ℝ)), F s = (D₁ i).solution (γ s))
    (N₂ : ℕ) (hN₂ : 0 < N₂) (r₂ M₂ : ℝ) (hr₂ : 0 < r₂) (hM₂ : 0 ≤ M₂)
    (D₂ : ℕ → HolomorphicDiskSolution H r₂)
    (hcenters₂ : ∀ i ≤ N₂, (D₂ i).center = γ ((i : ℝ) / (N₂ : ℝ)))
    (hbound₂ : ∀ i ≤ N₂, ∀ z ∈ Metric.ball (D₂ i).center r₂, ‖H z‖ ≤ M₂)
    (hcover₂ : ∀ i < N₂, ∀ s ∈ Icc ((i : ℝ) / (N₂ : ℝ))
      (((i + 1 : ℕ) : ℝ) / (N₂ : ℝ)),
      γ s ∈ Metric.ball (D₂ i).center (r₂ / 2))
    (hoverlap₂ : ∀ i < N₂, ∀ z ∈ Metric.ball (D₂ (i + 1)).center (r₂ / 2),
      (D₂ i).solution z = (D₂ (i + 1)).solution z)
    (hGformula : ∀ i < N₂, ∀ s ∈ Icc ((i : ℝ) / (N₂ : ℝ))
      (((i + 1 : ℕ) : ℝ) / (N₂ : ℝ)), G s = (D₂ i).solution (γ s))
    (hstart : F 0 = G 0) : ∀ t ∈ Icc (0 : ℝ) 1, F t = G t := by
  apply continuous_path_solution_lifts_unique hγ H hFcont hGcont
  · intro t ht
    exact disk_chain_lift_has_path_solution_charts hγ N₁ hN₁ r₁ M₁ hr₁ hM₁ H D₁
      hcenters₁ hbound₁ hcover₁ hoverlap₁ hFformula t ht
  · intro t ht
    exact disk_chain_lift_has_path_solution_charts hγ N₂ hN₂ r₂ M₂ hr₂ hM₂ H D₂
      hcenters₂ hbound₂ hcover₂ hoverlap₂ hGformula t ht
  · exact hstart

end DOZZ.Proofs
