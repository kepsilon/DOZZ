/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.CutPlaneTopology
public import Mathlib.Topology.Homotopy.Path

/-! A path homotopy in the Gauss cut plane gives the real-square input used by the ODE
homotopy grid. -/

@[expose] public section

open Set unitInterval

namespace DOZZ.Proofs

theorem subtype_paths_real_homotopy
    {U : Set ℂ} {x y : U} {p q : Path x y} (F : p.Homotopy q) :
    ∃ Γ : ℝ × ℝ → ℂ,
      ContinuousOn Γ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, Γ (0, s) = (x : ℂ)) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, Γ (1, s) = (y : ℂ)) ∧
      (∀ s (hs : s ∈ Icc (0 : ℝ) 1), Γ (s, 0) = (p ⟨s, hs⟩ : ℂ)) ∧
      (∀ s (hs : s ∈ Icc (0 : ℝ) 1), Γ (s, 1) = (q ⟨s, hs⟩ : ℂ)) ∧
      ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, Γ z ∈ U := by
  let proj : ℝ → unitInterval := fun t => Set.projIcc 0 1 zero_le_one t
  let Γ : ℝ × ℝ → ℂ := fun z => (F (proj z.2, proj z.1) : U)
  have hΓcont : Continuous Γ := by
    apply continuous_subtype_val.comp
    have hproj : Continuous proj := by
      dsimp [proj]
      exact continuous_projIcc
    have hpair : Continuous (fun z : ℝ × ℝ => (proj z.2, proj z.1)) := by
      exact (hproj.comp continuous_snd).prodMk (hproj.comp continuous_fst)
    exact F.continuous.comp hpair
  refine ⟨Γ, hΓcont.continuousOn, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have hs' : proj s = ⟨s, hs⟩ := Set.projIcc_of_mem zero_le_one hs
    have h0 : proj 0 = (0 : unitInterval) := by
      exact Set.projIcc_of_mem zero_le_one (by norm_num)
    change ((F (proj s, proj 0) : U) : ℂ) = (x : ℂ)
    rw [hs', h0]
    exact congrArg Subtype.val (F.source ⟨s, hs⟩)
  · intro s hs
    have hs' : proj s = ⟨s, hs⟩ := Set.projIcc_of_mem zero_le_one hs
    have h1 : proj 1 = (1 : unitInterval) := by
      exact Set.projIcc_of_mem zero_le_one (by norm_num)
    change ((F (proj s, proj 1) : U) : ℂ) = (y : ℂ)
    rw [hs', h1]
    exact congrArg Subtype.val (F.target ⟨s, hs⟩)
  · intro s hs
    have hs' : proj s = ⟨s, hs⟩ := Set.projIcc_of_mem zero_le_one hs
    have h0 : proj 0 = (0 : unitInterval) := by
      exact Set.projIcc_of_mem zero_le_one (by norm_num)
    change ((F (proj 0, proj s) : U) : ℂ) =
      ((p ⟨s, hs⟩ : U) : ℂ)
    rw [h0, hs']
    have heval := congrArg (fun r : Path x y => r ⟨s, hs⟩) F.eval_zero
    exact congrArg Subtype.val heval
  · intro s hs
    have hs' : proj s = ⟨s, hs⟩ := Set.projIcc_of_mem zero_le_one hs
    have h1 : proj 1 = (1 : unitInterval) := by
      exact Set.projIcc_of_mem zero_le_one (by norm_num)
    change ((F (proj 1, proj s) : U) : ℂ) =
      ((q ⟨s, hs⟩ : U) : ℂ)
    rw [h1, hs']
    have heval := congrArg (fun r : Path x y => r ⟨s, hs⟩) F.eval_one
    exact congrArg Subtype.val heval
  · intro z hz
    exact (F (proj z.2, proj z.1)).property


end DOZZ.Proofs
