/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.ExtendedSeibergN

/-! Strict parameter neighborhoods for the finite-insertion extended Seiberg domain. -/

@[expose] public section
open Filter Topology Set
namespace DOZZ.Proofs

/-- The background charge varies continuously away from zero. -/
theorem continuousAt_Q {γ : ℝ} (hγ : γ ≠ 0) : ContinuousAt Q γ := by
  unfold Q
  exact ((continuousAt_const.div continuousAt_id hγ).add
    (continuousAt_id.div_const 2))

/-- The finite-insertion zero-mode exponent varies jointly continuously away from zero. -/
theorem continuousAt_nPointSExp {N : ℕ} (q : ℝ × (Fin N → ℝ)) (hq : q.1 ≠ 0) :
    ContinuousAt (fun p : ℝ × (Fin N → ℝ) => nPointSExp p.1 p.2) q := by
  unfold nPointSExp
  have hs : ContinuousAt (fun p : ℝ × (Fin N → ℝ) => ∑ i, p.2 i) q := by
    exact (continuous_finsetSum _ (fun i _ => (continuous_apply i).comp
      continuous_snd)).continuousAt
  exact (hs.sub (continuousAt_const.mul
    ((continuousAt_Q hq).comp continuousAt_fst))).div continuousAt_fst hq

/-- All strict admissibility inequalities persist on a joint parameter neighborhood. -/
theorem extendedSeibergN_mem_nhds {N : ℕ} (q : ℝ × (Fin N → ℝ))
    (hq : 0 < q.1) (hq2 : q.1 < 2) (ha : ExtendedSeibergN q.1 q.2) :
    {p : ℝ × (Fin N → ℝ) | 0 < p.1 ∧ p.1 < 2 ∧ ExtendedSeibergN p.1 p.2} ∈ 𝓝 q := by
  have hQ := (continuousAt_Q hq.ne').comp continuousAt_fst
  have hs := (continuousAt_nPointSExp q hq.ne').neg
  have hb : ContinuousAt (fun p : ℝ × (Fin N → ℝ) => 4 / p.1 ^ 2) q :=
    continuousAt_const.div (continuousAt_fst.pow 2) (pow_ne_zero _ hq.ne')
  have hc : ∀ i, ContinuousAt (fun p : ℝ × (Fin N → ℝ) => p.2 i) q :=
    fun i => (continuous_apply i).continuousAt.comp continuousAt_snd
  have hi : ∀ i, ContinuousAt
      (fun p : ℝ × (Fin N → ℝ) => 2 / p.1 * (Q p.1 - p.2 i)) q :=
    fun i => (continuousAt_const.div continuousAt_fst hq.ne').mul (hQ.sub (hc i))
  have hroot : ∀ᶠ p in 𝓝 q, ∀ i, p.2 i < Q p.1 := by
    rw [Filter.eventually_all]
    exact fun i => (hc i).eventually_lt hQ (ha.1 i)
  have hinsert : ∀ᶠ p in 𝓝 q, ∀ i, -nPointSExp p.1 p.2 <
      2 / p.1 * (Q p.1 - p.2 i) := by
    rw [Filter.eventually_all]
    exact fun i => hs.eventually_lt (hi i) (ha.2.2 i)
  filter_upwards [continuousAt_const.eventually_lt continuousAt_fst hq,
    continuousAt_fst.eventually_lt continuousAt_const hq2,
    hroot, hs.eventually_lt hb ha.2.1, hinsert] with p hp hp2 hr hbulk hins
  exact ⟨hp, hp2, hr, hbulk, hins⟩


/-- The zero infinity charge in the all-finite frame obeys the extra GMC moment inequalities. -/
theorem finite_frame_admissible {N : ℕ} (γ : ℝ) (hγ : 0 < γ)
    (α : Fin N → ℝ) (ha : ExtendedSeibergN γ α) :
    (∀ i, α i < Q γ) ∧ (0 : ℝ) < Q γ ∧
    (2 * Q γ - (∑ i, α i + 0)) / γ < 4 / γ ^ 2 ∧
    (∀ i, (2 * Q γ - (∑ i, α i + 0)) / γ < 2 / γ * (Q γ - α i)) ∧
    (2 * Q γ - (∑ i, α i + 0)) / γ < 2 / γ * (Q γ - 0) := by
  have he : (2 * Q γ - (∑ i, α i + 0)) / γ = -nPointSExp γ α := by
    simp only [add_zero, nPointSExp]
    ring
  have hQ : 0 < Q γ := by unfold Q; positivity
  have hb : 4 / γ ^ 2 < 2 / γ * (Q γ - 0) := by
    have hid : 2 / γ * (Q γ - 0) = 4 / γ ^ 2 + 1 := by
      unfold Q
      field_simp [hγ.ne']
      ring
    rw [hid]
    exact lt_add_one _
  rw [he]
  exact ⟨ha.1, hQ, ha.2.1, ha.2.2, ha.2.1.trans hb⟩

end DOZZ.Proofs
