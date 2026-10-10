/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.Complex.Basic

/-! A continuous homotopy on the unit square admits a fine equal grid so each cell image lies
near its lower-left vertex. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

theorem exists_square_grid_subdivision {Γ : ℝ × ℝ → ℂ}
    (hΓ : ContinuousOn Γ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧
      ∀ i < N, ∀ j < N, ∀ s ∈ Icc ((i : ℝ) / (N : ℝ))
          (((i + 1 : ℕ) : ℝ) / (N : ℝ)),
        ∀ t ∈ Icc ((j : ℝ) / (N : ℝ)) (((j + 1 : ℕ) : ℝ) / (N : ℝ)),
          dist (Γ (s, t))
            (Γ ((i : ℝ) / (N : ℝ), (j : ℝ) / (N : ℝ))) < ε := by
  have hcompact : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hu := hcompact.uniformContinuousOn_of_continuous hΓ
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ, hδ, hclose⟩ := hu ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  let N := n + 1
  have hNnat : 0 < N := Nat.succ_pos n
  have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNnat
  have hgap : 1 / (N : ℝ) < δ := by simpa [N] using hn
  have hcoord (i : ℕ) (hi : i ≤ N) : (i : ℝ) / (N : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one hN).2
      exact_mod_cast hi
  refine ⟨N, hNnat, ?_⟩
  intro i hi j hj s hs t ht
  have hiNext : i + 1 ≤ N := Nat.succ_le_iff.mpr hi
  have hjNext : j + 1 ≤ N := Nat.succ_le_iff.mpr hj
  have hleft := hcoord i (Nat.le_of_lt hi)
  have hright := hcoord (i + 1) hiNext
  have hbottom := hcoord j (Nat.le_of_lt hj)
  have htop := hcoord (j + 1) hjNext
  have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨le_trans hleft.1 hs.1, le_trans hs.2 hright.2⟩
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨le_trans hbottom.1 ht.1, le_trans ht.2 htop.2⟩
  have hsDist : dist s ((i : ℝ) / (N : ℝ)) ≤ 1 / (N : ℝ) := by
    have hlen : (((i + 1 : ℕ) : ℝ) / (N : ℝ)) - (i : ℝ) / (N : ℝ) =
        1 / (N : ℝ) := by rw [Nat.cast_add, Nat.cast_one]; ring
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hs.1, hs.2, hlen]
  have htDist : dist t ((j : ℝ) / (N : ℝ)) ≤ 1 / (N : ℝ) := by
    have hlen : (((j + 1 : ℕ) : ℝ) / (N : ℝ)) - (j : ℝ) / (N : ℝ) =
        1 / (N : ℝ) := by rw [Nat.cast_add, Nat.cast_one]; ring
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [ht.1, ht.2, hlen]
  have hprod : dist (s, t)
      ((i : ℝ) / (N : ℝ), (j : ℝ) / (N : ℝ)) < δ := by
    rw [Prod.dist_eq]
    exact max_lt (hsDist.trans_lt hgap) (htDist.trans_lt hgap)
  have hbase := hclose (s, t) ⟨hs01, ht01⟩
    ((i : ℝ) / (N : ℝ), (j : ℝ) / (N : ℝ)) ⟨hleft, hbottom⟩ hprod
  exact hbase

end DOZZ.Proofs
