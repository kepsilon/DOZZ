/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.SquareSubdivision
public import DOZZ.Hypergeom.ODE.UniformCompactDisks
public import DOZZ.Hypergeom.ODE.LocalHomotopyGrid

/-! Homotopy invariance of local Picard continuation on a sufficiently fine finite grid. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Finite-grid data for a homotopy of paths with fixed endpoints, including the resulting
equality of lower and upper boundary continuation transfers. -/
structure HomotopyPicardGrid (Γ : ℝ × ℝ → ℂ) (U : Set ℂ)
    (H : ℂ → E →L[ℂ] E) (y : E) where
  N : ℕ
  N_pos : 0 < N
  r : ℝ
  M : ℝ
  r_pos : 0 < r
  M_nonneg : 0 ≤ M
  node : ℕ → ℕ → ℂ
  node_eq : ∀ i ≤ N, ∀ j ≤ N,
    node i j = Γ ((i : ℝ) / (N : ℝ), (j : ℝ) / (N : ℝ))
  node_in_U : ∀ i ≤ N, ∀ j ≤ N, node i j ∈ U
  data : ∀ i ≤ N, ∀ j ≤ N, LocalHolomorphicODEData r M H (node i j)
  cells : ∀ i < N, ∀ j < N,
    dist (node (i + 1) j) (node i j) < r / 4 ∧
    dist (node i (j + 1)) (node i j) < r / 4 ∧
    dist (node (i + 1) (j + 1)) (node i j) < r / 4
  cell_image : ∀ i < N, ∀ j < N, ∀ s ∈ Icc ((i : ℝ) / (N : ℝ))
      (((i + 1 : ℕ) : ℝ) / (N : ℝ)),
    ∀ t ∈ Icc ((j : ℝ) / (N : ℝ)) (((j + 1 : ℕ) : ℝ) / (N : ℝ)),
      dist (Γ (s, t))
        (Γ ((i : ℝ) / (N : ℝ), (j : ℝ) / (N : ℝ))) < r / 4
  left_fixed : ∀ j ≤ N, node 0 j = node 0 0
  right_fixed : ∀ j ≤ N, node N j = node N 0
  transfer_eq :
    let right : ℕ → ℕ → E → E := fun i j v =>
      if hi : i < N then
        if hj : j ≤ N then
          localPicardTransfer r M H (data i (Nat.le_of_lt hi) j hj) v (node (i + 1) j)
        else v
      else v
    finiteGridHorizontal right 0 0 N y = finiteGridHorizontal right 0 N N y

theorem exists_homotopy_picard_grid
    {Γ : ℝ × ℝ → ℂ} (hΓ : ContinuousOn Γ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (U : Set ℂ) (hU : IsOpen U) (H : ℂ → E →L[ℂ] E)
    (hH : DifferentiableOn ℂ H U)
    (himage : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, Γ p ∈ U)
    (z₀ z₁ : ℂ)
    (hleft : ∀ s ∈ Icc (0 : ℝ) 1, Γ (0, s) = z₀)
    (hright : ∀ s ∈ Icc (0 : ℝ) 1, Γ (1, s) = z₁)
    (y : E) : Nonempty (HomotopyPicardGrid Γ U H y) := by
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  have hK : IsCompact K := by dsimp [K]; exact isCompact_Icc.prod isCompact_Icc
  obtain ⟨r, M, hr, hM, hlocal⟩ :=
    exists_uniform_holomorphic_disks_on_compact hK Γ hΓ U hU H hH
      (by simpa [K] using himage)
  obtain ⟨N, hN, hgrid⟩ := exists_square_grid_subdivision hΓ (by linarith : 0 < r / 4)
  let node : ℕ → ℕ → ℂ := fun i j => Γ ((i : ℝ) / (N : ℝ), (j : ℝ) / (N : ℝ))
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcoord (i : ℕ) (hi : i ≤ N) : (i : ℝ) / (N : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one hNreal).2
      exact_mod_cast hi
  have hdata : ∀ i ≤ N, ∀ j ≤ N, LocalHolomorphicODEData r M H (node i j) := by
    intro i hi j hj
    have hp : ((i : ℝ) / (N : ℝ), (j : ℝ) / (N : ℝ)) ∈ K := by
      simp only [K, mem_prod]
      exact ⟨hcoord i hi, hcoord j hj⟩
    have h := hlocal _ hp
    simpa [node] using (LocalHolomorphicODEData.mk h.1 h.2)
  have hcells : ∀ i < N, ∀ j < N,
      dist (node (i + 1) j) (node i j) < r / 4 ∧
      dist (node i (j + 1)) (node i j) < r / 4 ∧
      dist (node (i + 1) (j + 1)) (node i j) < r / 4 := by
    intro i hi j hj
    have hiNext : i + 1 ≤ N := Nat.succ_le_iff.mpr hi
    have hjNext : j + 1 ≤ N := Nat.succ_le_iff.mpr hj
    have hxi : (i : ℝ) < ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self i
    have hyj : (j : ℝ) < ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self j
    have hxi' : (i : ℝ) / (N : ℝ) < ((i + 1 : ℕ) : ℝ) / (N : ℝ) :=
      (div_lt_div_iff_of_pos_right hNreal).2 hxi
    have hyj' : (j : ℝ) / (N : ℝ) < ((j + 1 : ℕ) : ℝ) / (N : ℝ) :=
      (div_lt_div_iff_of_pos_right hNreal).2 hyj
    have hR := hgrid i hi j hj (((i + 1 : ℕ) : ℝ) / (N : ℝ))
      ⟨hxi'.le, le_rfl⟩
      ((j : ℝ) / (N : ℝ)) ⟨le_rfl, hyj'.le⟩
    have hU := hgrid i hi j hj ((i : ℝ) / (N : ℝ))
      ⟨le_rfl, hxi'.le⟩
      (((j + 1 : ℕ) : ℝ) / (N : ℝ)) ⟨hyj'.le, le_rfl⟩
    have hD := hgrid i hi j hj (((i + 1 : ℕ) : ℝ) / (N : ℝ))
      ⟨hxi'.le, le_rfl⟩
      (((j + 1 : ℕ) : ℝ) / (N : ℝ)) ⟨hyj'.le, le_rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [node] using hR
    · simpa [node] using hU
    · simpa [node] using hD
  have hleftNode : ∀ j ≤ N, node 0 j = node 0 0 := by
    intro j hj
    have h := hleft ((j : ℝ) / (N : ℝ)) (hcoord j hj)
    have hz₀ : Γ (0, 0) = z₀ := hleft 0 (by norm_num)
    have hzero : (0 : ℝ) / (N : ℝ) = 0 := by simp
    simpa [node, hzero] using h.trans hz₀.symm
  have hrightNode : ∀ j ≤ N, node N j = node N 0 := by
    intro j hj
    have h := hright ((j : ℝ) / (N : ℝ)) (hcoord j hj)
    have hz₁ : Γ (1, 0) = z₁ := hright 0 (by norm_num)
    have hNN : (N : ℝ) / (N : ℝ) = 1 := div_self (by exact_mod_cast hN.ne')
    simpa [node, hNN] using h.trans hz₁.symm
  refine ⟨⟨N, hN, r, M, hr, hM, node, ?_, ?_, hdata, hcells, ?_,
    hleftNode, hrightNode, ?_⟩⟩
  · intro i hi j hj
    rfl
  · intro i hi j hj
    apply himage
    simp only [mem_prod]
    exact ⟨hcoord i hi, hcoord j hj⟩
  · intro i hi j hj s hs t ht
    exact hgrid i hi j hj s hs t ht
  · exact localPicard_homotopy_grid_endpoint_eq N r M hr hM H node hdata
      hcells hleftNode hrightNode y

/-- A chosen finite local Picard grid for a homotopy with fixed endpoints. -/
noncomputable def homotopyPicardGridOf
    {Γ : ℝ × ℝ → ℂ} (hΓ : ContinuousOn Γ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (U : Set ℂ) (hU : IsOpen U) (H : ℂ → E →L[ℂ] E)
    (hH : DifferentiableOn ℂ H U)
    (himage : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, Γ p ∈ U)
    (z₀ z₁ : ℂ)
    (hleft : ∀ s ∈ Icc (0 : ℝ) 1, Γ (0, s) = z₀)
    (hright : ∀ s ∈ Icc (0 : ℝ) 1, Γ (1, s) = z₁)
    (y : E) : HomotopyPicardGrid Γ U H y :=
  Classical.choice (exists_homotopy_picard_grid hΓ U hU H hH himage z₀ z₁ hleft hright y)

end DOZZ.Proofs
