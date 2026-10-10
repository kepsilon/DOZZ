/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Topology.Semicontinuity.Lindelof

/-! Countable supporting affine functions on the positive half-line. -/

@[expose] public section

open Set Function

namespace DOZZ.Proofs

/-- The right derivative at an interior positive point defines a supporting affine function. -/
theorem convex_right_tangent_le
    (F : ℝ → ℝ) (hF : ConvexOn ℝ (Ici 0) F) (r : ℝ) (hr : 0 < r)
    (x : ℝ) (hx : 0 < x) :
    F r + derivWithin F (Ioi r) r * (x - r) ≤ F x := by
  have hrint : r ∈ interior (Ici (0 : ℝ)) := by simpa only [interior_Ici, mem_Ioi] using hr
  rcases lt_trichotomy r x with hlt | heq | hgt
  · have h := hF.rightDeriv_le_slope_of_mem_interior hrint hx.le hlt
    rw [slope_def_field] at h
    have hmul := (le_div_iff₀ (sub_pos.mpr hlt)).mp h
    linarith
  · subst x
    simp
  · have h := (hF.slope_le_leftDeriv_of_mem_interior hx.le hrint hgt).trans
      (hF.leftDeriv_le_rightDeriv_of_mem_interior hrint)
    rw [slope_def_field] at h
    have hmul := (div_le_iff₀ (sub_pos.mpr hgt)).mp h
    linarith

/-- Every convex test on the nonnegative half-line is the pointwise supremum on positive
arguments of a countable family of globally affine minorants. -/
theorem convex_positive_countable_affine_minorants
    (F : ℝ → ℝ) (hF : ConvexOn ℝ (Ici 0) F) :
    ∃ (a b : ℕ → ℝ),
      (∀ n x, 0 < x → a n * x + b n ≤ F x) ∧
        ∀ x, 0 < x → (⨆ n, a n * x + b n) = F x := by
  classical
  let S := Ioi (0 : ℝ)
  let G : S → ℝ := fun x => F x.val
  let L : ℝ → ℝ → ℝ := fun r x =>
    F r + derivWithin F (Ioi r) r * (x - r)
  let A : Set (S → ℝ) := {f | ∃ r : ℝ, 0 < r ∧ f = fun x => L r x.val}
  have hAupper : G ∈ upperBounds A := by
    intro f hf x
    obtain ⟨r, hr, rfl⟩ := hf
    exact convex_right_tangent_le F hF r hr x.val x.property
  have hAlub : IsLUB A G := by
    refine ⟨hAupper, ?_⟩
    intro g hg x
    have h := hg (show (fun y : S => L x.val y.val) ∈ A from
      ⟨x.val, x.property, rfl⟩) x
    simpa [L, G] using h
  have hAcont : ∀ f ∈ A, LowerSemicontinuous f := by
    intro f hf
    obtain ⟨r, hr, rfl⟩ := hf
    have h : Continuous (fun x : S => L r x.val) := by dsimp [L]; fun_prop
    exact h.lowerSemicontinuous
  obtain ⟨A', hsub, hcount, hlub⟩ := exists_countable_lowerSemicontinuous_isLUB hAcont hAlub
  have hnonempty : A'.Nonempty := by
    by_contra hempty
    have heq : A' = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    have hbound : (fun x : S => G x - 1) ∈ upperBounds A' := by simp [heq]
    have h := hlub.2 hbound (⟨1, by change (0 : ℝ) < 1; norm_num⟩ : S)
    linarith
  obtain ⟨f, hf⟩ := hcount.exists_eq_range hnonempty
  have hrep (n : ℕ) : ∃ r : ℝ, 0 < r ∧ f n = fun x => L r x.val :=
    hsub (hf ▸ mem_range_self n)
  choose r hr hfr using hrep
  let a : ℕ → ℝ := fun n => derivWithin F (Ioi (r n)) (r n)
  let b : ℕ → ℝ := fun n => F (r n) - a n * r n
  have hline (n : ℕ) (x : S) : f n x = a n * x.val + b n := by
    rw [hfr n]
    dsimp [L, a, b]
    ring
  have hsup : (⨆ n, f n) = G := by
    rw [← sSup_range, ← hf]
    exact hlub.csSup_eq hnonempty
  refine ⟨a, b, ?_, ?_⟩
  · intro n x hx
    rw [← hline n ⟨x, hx⟩]
    exact hAupper (hsub (hf ▸ mem_range_self n)) ⟨x, hx⟩
  · intro x hx
    have h := congrFun hsup (⟨x, hx⟩ : S)
    simpa only [iSup_apply, hline, G] using h

end DOZZ.Proofs
