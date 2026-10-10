/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.SoftNear
public import DOZZ.FourPoint.BPZ.SoftMomentDeriv

/-! # Approximation of expectations and real forms of the near-root bounds

An abstract approximation lemma: expectations converge if, for every tolerance, the integrands are
`L¹`-close to integrands whose expectations converge. The near-root bounds of `SoftNear` are
converted to bounds on real expectations `E[I^{-p} ∫ w |x − z|^β dM]`, where `I` is the softened
four-point mass as a real number. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Expectations converge if the integrands are uniformly `L¹`-approximated by integrands whose
expectations converge. -/
theorem bpz_tendsto_integral_of_approx {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {P : Measure Ω} {F : ℕ → Ω → E} {F₀ : Ω → E}
    (h : ∀ η : ℝ, 0 < η → ∃ (G : ℕ → Ω → E) (G₀ : Ω → E),
      Tendsto (fun n => ∫ ω, G n ω ∂P) atTop (𝓝 (∫ ω, G₀ ω ∂P)) ∧
      (∀ᶠ n in atTop, Integrable (F n) P ∧ Integrable (G n) P ∧
        ∫ ω, ‖F n ω - G n ω‖ ∂P ≤ η) ∧
      Integrable F₀ P ∧ Integrable G₀ P ∧ ∫ ω, ‖F₀ ω - G₀ ω‖ ∂P ≤ η) :
    Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (𝓝 (∫ ω, F₀ ω ∂P)) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨G, G₀, hG, hev, hF₀, hG₀, h₀⟩ := h (δ / 4) (by positivity)
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hG) (δ / 4) (by positivity)
  obtain ⟨N₂, hN₂⟩ := hev.exists_forall_of_atTop
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  obtain ⟨hFn, hGn, hn₂⟩ := hN₂ n (le_trans (le_max_right _ _) hn)
  have h1 := hN₁ n (le_trans (le_max_left _ _) hn)
  rw [dist_eq_norm] at h1 ⊢
  have e1 : ‖∫ ω, F n ω ∂P - ∫ ω, G n ω ∂P‖ ≤ δ / 4 := by
    rw [← integral_sub hFn hGn]
    exact (norm_integral_le_integral_norm _).trans hn₂
  have e2 : ‖∫ ω, G₀ ω ∂P - ∫ ω, F₀ ω ∂P‖ ≤ δ / 4 := by
    rw [← integral_sub hG₀ hF₀, ← norm_neg, ← integral_neg]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq_of_le ?_ h₀)
    congr 1; funext ω; rw [neg_sub]
  calc ‖∫ ω, F n ω ∂P - ∫ ω, F₀ ω ∂P‖
      = ‖(∫ ω, F n ω ∂P - ∫ ω, G n ω ∂P) + (∫ ω, G n ω ∂P - ∫ ω, G₀ ω ∂P) +
          (∫ ω, G₀ ω ∂P - ∫ ω, F₀ ω ∂P)‖ := by congr 1; abel
    _ ≤ ‖∫ ω, F n ω ∂P - ∫ ω, G n ω ∂P‖ + ‖∫ ω, G n ω ∂P - ∫ ω, G₀ ω ∂P‖ +
          ‖∫ ω, G₀ ω ∂P - ∫ ω, F₀ ω ∂P‖ := norm_add₃_le
    _ < δ / 4 + δ / 4 + δ / 4 + δ / 4 := by linarith
    _ = δ := by ring

end DOZZ.Proofs
