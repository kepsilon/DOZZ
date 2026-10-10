/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Complex.Basic

/-! Narrow-strip representatives with whole-plane codiscrete shift equations. Real translations
preserve both the strip and its exterior. -/

@[expose] public section
open Filter Topology Set

namespace DOZZ.Proofs

/-- Restricting exceptions to a set whose closure stays in the original open domain makes
them globally codiscrete. The closure condition also covers the new boundary. -/
theorem codiscreteWithin_restrict_closure
    {S T : Set ℂ} (hS : IsOpen S) (hTS : closure T ⊆ S)
    {p : ℂ → Prop} (hp : ∀ᶠ z in codiscreteWithin S, p z) :
    ∀ᶠ z in codiscrete ℂ, z ∈ T → p z := by
  apply mem_codiscrete_iff_forall_mem_nhdsNE.mpr
  intro z
  by_cases hz : z ∈ closure T
  · have hzS := hTS hz
    have hlocal := eventually_codiscreteWithin_iff_forall_eventually_nhdsNE.mp hp z hzS
    have hSne : ∀ᶠ w in 𝓝[≠] z, w ∈ S :=
      (show ∀ᶠ w in 𝓝 z, w ∈ S from hS.mem_nhds hzS).filter_mono nhdsWithin_le_nhds
    filter_upwards [hlocal, hSne] with w hw hSw _
    exact hw hSw
  · have hext : ∀ᶠ w in 𝓝[≠] z, w ∉ closure T :=
      (show ∀ᶠ w in 𝓝 z, w ∉ closure T from
        isClosed_closure.isOpen_compl.mem_nhds hz).filter_mono nhdsWithin_le_nhds
    filter_upwards [hext] with w hw hwT
    exact (hw (subset_closure hwT)).elim

/-- A meromorphic first-shift germ on a wider strip admits a representative on a narrower
strip whose homogeneous shift equation holds codiscretely on the whole plane. -/
theorem exists_wholePlane_strip_representative
    (F A : ℂ → ℂ) (b H h : ℝ) (hhH : h < H)
    (hF : MeromorphicOn F (horizontalStrip H))
    (hshift : ∀ᶠ z in codiscreteWithin (horizontalStrip H),
      F (z + b) = A z * F (z - b)) :
    ∃ C : ℂ → ℂ, MeromorphicOn C (horizontalStrip h) ∧
      EqOn C F (horizontalStrip h) ∧
      ∀ᶠ z in codiscrete ℂ, C (z + b) = A z * C (z - b) := by
  classical
  let C : ℂ → ℂ := fun z => if z ∈ horizontalStrip h then F z else 0
  have hopen := isOpen_horizontalStrip h
  have hsub : horizontalStrip h ⊆ horizontalStrip H := fun z hz => lt_trans hz hhH
  have hclosure : closure (horizontalStrip h) ⊆ horizontalStrip H := by
    have hclosed : IsClosed {z : ℂ | |z.im| ≤ h} :=
      isClosed_le Complex.continuous_im.abs continuous_const
    have hsc : horizontalStrip h ⊆ {z : ℂ | |z.im| ≤ h} := by
      intro z hz
      change |z.im| ≤ h
      exact le_of_lt hz
    have hcl : closure (horizontalStrip h) ⊆ {z : ℂ | |z.im| ≤ h} :=
      closure_minimal hsc hclosed
    exact fun z hz => lt_of_le_of_lt (hcl hz) hhH
  have heq : EqOn F C (horizontalStrip h) := by
    intro z hz
    simp only [C, ite_eq_left hz]
  have hFnarrow : MeromorphicOn F (horizontalStrip h) := fun z hz => hF z (hsub hz)
  refine ⟨C, hFnarrow.congr heq hopen, heq.symm, ?_⟩
  have hglobal := codiscreteWithin_restrict_closure
    (isOpen_horizontalStrip H) hclosure hshift
  filter_upwards [hglobal] with z hz
  have hplus : z + (b : ℂ) ∈ horizontalStrip h ↔ z ∈ horizontalStrip h := by
    simp only [horizontalStrip, mem_ofPred_eq, Complex.add_im, Complex.ofReal_im, add_zero]
  have hminus : z - (b : ℂ) ∈ horizontalStrip h ↔ z ∈ horizontalStrip h := by
    simp only [horizontalStrip, mem_ofPred_eq, Complex.sub_im, Complex.ofReal_im, sub_zero]
  by_cases hzin : z ∈ horizontalStrip h
  · simp only [C, ite_eq_left (hplus.mpr hzin), ite_eq_left (hminus.mpr hzin)]
    exact hz hzin
  · simp only [C, ite_eq_right (hplus.not.mpr hzin), ite_eq_right (hminus.not.mpr hzin),
      mul_zero]

end DOZZ.Proofs
