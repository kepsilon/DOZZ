/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.GMCVertexTiltInputs

/-! Gaussian closure for inward and outward vertices at different circle radii. -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- Addition preserves the Gaussian closure of the same distribution field. -/
theorem gaussianL2Limit_add {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (L K : Ω → ℝ)
    (hL : IsGaussianL2Limit P X L) (hK : IsGaussianL2Limit P X K) :
    IsGaussianL2Limit P X (fun ω => L ω + K ω) := by
  obtain ⟨hmL, f, hf⟩ := hL
  obtain ⟨hmK, g, hg⟩ := hK
  refine ⟨by simpa only [Pi.add_def] using hmL.add hmK, (fun n => f n + g n), ?_⟩
  have he n : (fun ω => L ω + K ω - X ω (f n + g n)) =
      (fun ω => L ω - X ω (f n)) + (fun ω => K ω - X ω (g n)) := by
    funext ω
    rw [map_add]
    simp only [Pi.add_apply]
    ring
  have hb n := eLpNorm_add_le (μ := P) (p := (2 : ℝ≥0∞))
    (f := fun ω => L ω - X ω (f n)) (g := fun ω => K ω - X ω (g n)) (by norm_num)
  have ht := hf.add hg
  simp only [zero_add] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le)
  intro n
  change eLpNorm (fun ω => L ω + K ω - X ω (f n + g n)) 2 P ≤ _
  rw [he]
  exact hb n

/-- Any finite sum of Gaussian closure variables remains in that closure. -/
theorem isGaussianL2Limit_finset_sum {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (L : I → Ω → ℝ) (S : Finset I)
    (hL : ∀ i ∈ S, IsGaussianL2Limit P X (L i)) :
    IsGaussianL2Limit P X (fun ω => ∑ i ∈ S, L i ω) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨by simp, (fun _ => 0), ?_⟩
    have he : (fun ω => (∑ i ∈ (∅ : Finset I), L i ω) - X ω (0 : TestFn)) =
        (0 : Ω → ℝ) := by
      funext ω
      simp
    simp only [he, eLpNorm_zero]
    exact tendsto_const_nhds
  | @insert i S hi ih =>
    have hiL := hL i (Finset.mem_insert_self _ _)
    have hSL := ih (fun j hj => hL j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using
      gaussianL2Limit_add P X (L i) (fun ω => ∑ j ∈ S, L j ω) hiL hSL

/-- Mixed inward/outward circle vertices supply the literal Gaussian closure premise of GMC tilt. -/
theorem circle_vertices_gaussianL2Limit
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (α : Fin N → ℝ) (z : Fin N → ℂ) (r : Fin N → ℝ) :
    IsGaussianL2Limit P X (fun ω => ∑ i, α i * Xc ω (z i) (r i)) := by
  apply isGaussianL2Limit_finset_sum P X (fun i ω => α i * Xc ω (z i) (r i)) Finset.univ
  intro i _
  simpa using circleAverage_sum_isGaussianL2Limit P X hX Xc hXc
    (fun _ : Fin 1 => α i) (fun _ : Fin 1 => z i) (r i)

end DOZZ.Proofs
