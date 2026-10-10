/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import GaussianFields.WhiteNoise.Haar

/-!
# GaussianFields Haar basis indices and orthogonality

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace Topology symmDiff
open Filter

namespace GaussianFields


instance instFact_two_ne_top_haarBasis : Fact ((2 : ℝ≥0∞) ≠ ∞) :=
  ⟨ENNReal.ofNat_ne_top⟩

/-- Nonnegative-scale tensor Haar wavelet indices. -/
abbrev HaarNonnegativeWaveletIndex (d : Nat) :=
  { idx : HaarWaveletIndex d // 0 ≤ idx.scale }

/-- The inhomogeneous Haar basis index: scale-zero father packets and all wavelets at scales
`j ≥ 0`. -/
inductive HaarBasisIndex (d : Nat) where
  | father (cell : Fin d → ℤ)
  | wavelet (idx : HaarNonnegativeWaveletIndex d)
deriving DecidableEq

instance instCountable_haarNonnegativeWaveletIndex (d : Nat) :
    Countable (HaarNonnegativeWaveletIndex d) := by
  infer_instance

instance instCountable_haarBasisIndex (d : Nat) :
    Countable (HaarBasisIndex d) := by
  classical
  exact (show Function.Injective
      (fun idx : HaarBasisIndex d =>
        match idx with
        | HaarBasisIndex.father cell => Sum.inl cell
        | HaarBasisIndex.wavelet idx => Sum.inr idx) by
    intro idx idx' hidx
    cases idx with
    | father cell =>
        cases idx' with
        | father cell' =>
            simp at hidx
            subst hidx
            rfl
        | wavelet idx' =>
            simp at hidx
    | wavelet idx =>
        cases idx' with
        | father cell' =>
            simp at hidx
        | wavelet idx' =>
            simp at hidx
            subst hidx
            rfl).countable

noncomputable instance instEncodable_haarBasisIndex (d : Nat) :
    Encodable (HaarBasisIndex d) :=
  Encodable.ofCountable (HaarBasisIndex d)

/-- The raw all-father Haar packet index at scale zero. -/
@[expose]
def haarFatherPacketIndex {d : Nat} (cell : Fin d → ℤ) : HaarIndex d where
  scale := 0
  cell := cell
  signature := fun _ => false

/-- The scale-zero father packet as an `L²(R^d)` vector. -/
@[expose]
noncomputable def haarFatherPacketLp {d : Nat} (cell : Fin d → ℤ) :
    Lp ℝ 2 (volume : Measure (Vec d)) :=
  haarPacketLp (haarFatherPacketIndex cell)

/-- The inhomogeneous Haar basis vector associated to an index. -/
@[expose]
noncomputable def haarBasisLp {d : Nat} :
    HaarBasisIndex d → Lp ℝ 2 (volume : Measure (Vec d))
  | HaarBasisIndex.father cell => haarFatherPacketLp cell
  | HaarBasisIndex.wavelet idx => haarWaveletPacketLp idx.1

theorem inner_haarFatherPacketLp {d : Nat} (cell₁ cell₂ : Fin d → ℤ) :
    ⟪haarFatherPacketLp cell₁, haarFatherPacketLp cell₂⟫_ℝ =
      if cell₁ = cell₂ then 1 else 0 := by
  have h := inner_haarPacketLp_same_scale
    (haarFatherPacketIndex cell₁) (haarFatherPacketIndex cell₂) rfl
  simpa [haarFatherPacketLp, haarFatherPacketIndex] using h

theorem haarFatherPacketIndex_ne_wavelet_toHaarIndex {d : Nat}
    (cell : Fin d → ℤ) (idx : HaarWaveletIndex d) :
    haarFatherPacketIndex cell ≠ idx.toHaarIndex := by
  intro hidx
  have hsig : idx.signature.1 = fun _ : Fin d => false := by
    funext r
    have hr := congrArg (fun idx : HaarIndex d => idx.signature r) hidx
    simpa [haarFatherPacketIndex, HaarWaveletIndex.toHaarIndex] using hr
  exact idx.signature.2 hsig

theorem inner_haarFatherPacketLp_haarWaveletPacketLp {d : Nat}
    (cell : Fin d → ℤ) (idx : HaarNonnegativeWaveletIndex d) :
    ⟪haarFatherPacketLp cell, haarWaveletPacketLp idx.1⟫_ℝ = 0 := by
  rw [haarWaveletPacketLp_eq_haarPacketLp]
  by_cases hzero : idx.1.scale = 0
  · have hsame := inner_haarPacketLp_same_scale
      (haarFatherPacketIndex cell) idx.1.toHaarIndex (by
        simp [haarFatherPacketIndex, HaarWaveletIndex.toHaarIndex, hzero])
    have hne := haarFatherPacketIndex_ne_wavelet_toHaarIndex cell idx.1
    simpa [haarFatherPacketLp, hne] using hsame
  · have hpos : 0 < idx.1.scale := lt_of_le_of_ne idx.2 (Ne.symm hzero)
    obtain ⟨n, hn⟩ := exists_nat_succ_scale_gap hpos
    rcases exists_true_of_ne_false_signature idx.1.signature.property with ⟨r, hsig⟩
    have hscale :
        idx.1.toHaarIndex.scale =
          (haarFatherPacketIndex cell).scale + ((n + 1 : ℕ) : ℤ) := by
      simpa [haarFatherPacketIndex, HaarWaveletIndex.toHaarIndex] using hn
    exact inner_haarPacketLp_finer_of_signature_true_nat_succ
      (haarFatherPacketIndex cell) idx.1.toHaarIndex n hscale hsig

theorem inner_haarWaveletPacketLp_haarFatherPacketLp {d : Nat}
    (idx : HaarNonnegativeWaveletIndex d) (cell : Fin d → ℤ) :
    ⟪haarWaveletPacketLp idx.1, haarFatherPacketLp cell⟫_ℝ = 0 := by
  rw [← inner_conj_symm]
  simp [inner_haarFatherPacketLp_haarWaveletPacketLp cell idx]

/-- Inner products in the inhomogeneous Haar system are Kronecker deltas. -/
theorem inner_haarBasisLp (d : Nat) (idx₁ idx₂ : HaarBasisIndex d) :
    ⟪haarBasisLp idx₁, haarBasisLp idx₂⟫_ℝ =
      if idx₁ = idx₂ then 1 else 0 := by
  cases idx₁ with
  | father cell₁ =>
      cases idx₂ with
      | father cell₂ =>
          simpa [haarBasisLp] using inner_haarFatherPacketLp cell₁ cell₂
      | wavelet idx₂ =>
          rw [ite_eq_right]
          · exact inner_haarFatherPacketLp_haarWaveletPacketLp cell₁ idx₂
          · intro h
            cases h
  | wavelet idx₁ =>
      cases idx₂ with
      | father cell₂ =>
          rw [ite_eq_right]
          · exact inner_haarWaveletPacketLp_haarFatherPacketLp idx₁ cell₂
          · intro h
            cases h
      | wavelet idx₂ =>
          rw [haarBasisLp]
          have h := inner_haarWaveletPacketLp d idx₁.1 idx₂.1
          by_cases hidx : idx₁ = idx₂
          · subst idx₂
            simpa [haarBasisLp] using h
          · have hval : idx₁.1 ≠ idx₂.1 := by
              intro hval
              exact hidx (Subtype.ext hval)
            simp [hidx, hval] at h ⊢
            exact h

/-- The inhomogeneous Haar system is orthonormal in `L²(R^d)`. -/
theorem orthonormal_haarBasisLp (d : Nat) :
    Orthonormal ℝ (haarBasisLp : HaarBasisIndex d → Lp ℝ 2 (volume : Measure (Vec d))) := by
  classical
  rw [orthonormal_iff_ite]
  intro idx₁ idx₂
  exact inner_haarBasisLp d idx₁ idx₂

/-- The algebraic span of the inhomogeneous Haar basis vectors. -/
@[expose]
noncomputable def haarBasisSubmodule (d : Nat) :
    Submodule ℝ (Lp ℝ 2 (volume : Measure (Vec d))) :=
  Submodule.span ℝ
    (Set.range (haarBasisLp : HaarBasisIndex d → Lp ℝ 2 (volume : Measure (Vec d))))

theorem haarBasisLp_mem_haarBasisSubmodule {d : Nat} (idx : HaarBasisIndex d) :
    haarBasisLp idx ∈ haarBasisSubmodule d := by
  exact Submodule.subset_span ⟨idx, rfl⟩

theorem haarFatherPacketLp_mem_haarBasisSubmodule {d : Nat} (cell : Fin d → ℤ) :
    haarFatherPacketLp cell ∈ haarBasisSubmodule d := by
  exact haarBasisLp_mem_haarBasisSubmodule (HaarBasisIndex.father cell)

theorem haarWaveletPacketLp_mem_haarBasisSubmodule_of_nonnegative {d : Nat}
    (idx : HaarWaveletIndex d) (hscale : 0 ≤ idx.scale) :
    haarWaveletPacketLp idx ∈ haarBasisSubmodule d := by
  exact haarBasisLp_mem_haarBasisSubmodule
    (HaarBasisIndex.wavelet ⟨idx, hscale⟩)

theorem haarPacketLp_mem_haarBasisSubmodule_of_signature
    {d : Nat} {j : ℤ} (hj : 0 ≤ j) (cell : Fin d → ℤ)
    (signature : Fin d → Bool)
    (hfather :
      haarPacketLp { scale := j, cell := cell, signature := fun _ => false } ∈
        haarBasisSubmodule d) :
    haarPacketLp { scale := j, cell := cell, signature := signature } ∈
      haarBasisSubmodule d := by
  by_cases hsig : signature = fun _ : Fin d => false
  · subst signature
    exact hfather
  · let idx : HaarWaveletIndex d :=
      { scale := j
        cell := cell
        signature := ⟨signature, hsig⟩ }
    have hmem := haarWaveletPacketLp_mem_haarBasisSubmodule_of_nonnegative idx hj
    simpa [idx, haarWaveletPacketLp_eq_haarPacketLp, HaarWaveletIndex.toHaarIndex] using hmem

theorem haarPacketLp_child_father_mem_haarBasisSubmodule
    {d : Nat} {j : ℤ} (hj : 0 ≤ j) (cell : Fin d → ℤ)
    (side : Fin d → Bool)
    (hparent :
      haarPacketLp { scale := j, cell := cell, signature := fun _ => false } ∈
        haarBasisSubmodule d) :
    haarPacketLp
        { scale := j + 1
          cell := haarChildCell cell side
          signature := fun _ => false } ∈
      haarBasisSubmodule d := by
  rw [haarPacketLp_child_father_refine]
  exact Submodule.sum_mem _ fun signature _ =>
    Submodule.smul_mem _ _
      (haarPacketLp_mem_haarBasisSubmodule_of_signature hj cell signature hparent)

/-- The parent cell of an integer dyadic cell. -/
@[expose]
def haarParentCell {d : Nat} (cell : Fin d → ℤ) : Fin d → ℤ :=
  fun r => cell r / 2

/-- The left/right side vector of an integer dyadic cell relative to its parent. -/
@[expose]
def haarCellSide {d : Nat} (cell : Fin d → ℤ) : Fin d → Bool :=
  fun r => cell r % 2 = 1

theorem haarChildCell_parent_side {d : Nat} (cell : Fin d → ℤ) :
    haarChildCell (haarParentCell cell) (haarCellSide cell) = cell := by
  funext r
  unfold haarChildCell haarParentCell haarCellSide
  rcases Int.emod_two_eq_zero_or_one (cell r) with hmod | hmod
  · have hdecomp := Int.emod_add_mul_ediv (cell r) 2
    rw [hmod] at hdecomp
    simp at hdecomp ⊢
    omega
  · have hdecomp := Int.emod_add_mul_ediv (cell r) 2
    rw [hmod] at hdecomp
    simp [hmod]
    omega

theorem haarPacketLp_father_mem_haarBasisSubmodule_nat_scale
    {d : Nat} (n : ℕ) (cell : Fin d → ℤ) :
    haarPacketLp
        { scale := (n : ℤ), cell := cell, signature := fun _ => false } ∈
      haarBasisSubmodule d := by
  revert cell
  induction n with
  | zero =>
      intro cell
      simpa [haarFatherPacketLp, haarFatherPacketIndex] using
        haarFatherPacketLp_mem_haarBasisSubmodule cell
  | succ n ih =>
      intro cell
      let parent := haarParentCell cell
      let side := haarCellSide cell
      have hparent :
          haarPacketLp
              { scale := (n : ℤ), cell := parent, signature := fun _ => false } ∈
            haarBasisSubmodule d :=
        ih parent
      have hchild := haarPacketLp_child_father_mem_haarBasisSubmodule
        (d := d) (j := (n : ℤ)) (by exact_mod_cast Nat.zero_le n)
        parent side hparent
      have hcell : haarChildCell parent side = cell := by
        simpa [parent, side] using haarChildCell_parent_side cell
      simpa [hcell, Nat.cast_add, Nat.cast_one] using hchild

theorem haarPacketLp_father_mem_haarBasisSubmodule_of_nonnegative
    {d : Nat} {j : ℤ} (hj : 0 ≤ j) (cell : Fin d → ℤ) :
    haarPacketLp { scale := j, cell := cell, signature := fun _ => false } ∈
      haarBasisSubmodule d := by
  have hjcast : j = (j.toNat : ℤ) := (Int.eq_natCast_toNat).2 hj
  rw [hjcast]
  exact haarPacketLp_father_mem_haarBasisSubmodule_nat_scale j.toNat cell

theorem haarPacketLp_mem_haarBasisSubmodule_of_nonnegative
    {d : Nat} {j : ℤ} (hj : 0 ≤ j) (cell : Fin d → ℤ)
    (signature : Fin d → Bool) :
    haarPacketLp { scale := j, cell := cell, signature := signature } ∈
      haarBasisSubmodule d :=
  haarPacketLp_mem_haarBasisSubmodule_of_signature hj cell signature
    (haarPacketLp_father_mem_haarBasisSubmodule_of_nonnegative hj cell)

end GaussianFields

end
