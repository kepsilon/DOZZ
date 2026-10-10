/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Roots.ChargeGeometry
public import DOZZ.ShiftEquations.Rbar.Continuation
import Mathlib.Analysis.Convex.Basic
/-! # Convex charge segments for continuation -/
@[expose] public section
open Set
namespace DOZZ.Proofs
/-- The extended bounds become affine inequalities at fixed positive gamma. -/
theorem roots_extended_linear_bounds {γ a b c : ℝ} (hγ : 0 < γ)
    (h : ExtendedSeiberg3 γ a b c) :
    2 * Q γ - (a + b + c) < 4 / γ ∧
      2 * Q γ - (a + b + c) < 2 * (Q γ - a) ∧
      2 * Q γ - (a + b + c) < 2 * (Q γ - b) ∧
      2 * Q γ - (a + b + c) < 2 * (Q γ - c) := by
  obtain ⟨h1, h2, h3⟩ := roots_extended_triangle hγ h
  have hb := lt_of_lt_of_le h.2.2.2 (min_le_left _ _)
  have he : -sExp γ a b c = (2 * Q γ - (a + b + c)) / γ := by unfold sExp; ring
  rw [he] at hb
  have hb' := (div_lt_iff₀ hγ).mp hb
  have he' : (4 / γ ^ 2) * γ = 4 / γ := by field_simp
  rw [he'] at hb'
  exact ⟨hb', by linarith only [h1], by linarith only [h2], by linarith only [h3]⟩
/-- Every real segment joining extended triples remains in the strict extended domain. -/
theorem roots_extendedSeiberg3_segment {γ a b c d e f : ℝ} (hγ : 0 < γ)
    (ha : ExtendedSeiberg3 γ a b c) (hb : ExtendedSeiberg3 γ d e f)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ExtendedSeiberg3 γ (t * a + (1 - t) * d) (t * b + (1 - t) * e) (t * c + (1 - t) * f) := by
  have hmix (x y L : ℝ) (hx : x < L) (hy : y < L) : t * x + (1 - t) * y < L := by
    simpa only [smul_eq_mul, mem_Iio] using (convex_Iio L) hx hy ht.1 (sub_nonneg.mpr ht.2) (by ring : t + (1 - t) = 1)
  obtain ⟨ha0, ha1, ha2, ha3⟩ := roots_extended_linear_bounds hγ ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := roots_extended_linear_bounds hγ hb
  apply extendedSeiberg3_of_lt hγ (hmix _ _ _ ha.1 hb.1) (hmix _ _ _ ha.2.1 hb.2.1)
    (hmix _ _ _ ha.2.2.1 hb.2.2.1)
  · have h := hmix _ _ _ ha0 hb0
    convert h using 1; ring
  · obtain ⟨h1, _, _⟩ := roots_extended_triangle hγ ha
    obtain ⟨h2, _, _⟩ := roots_extended_triangle hγ hb
    have h := hmix (a - b - c) (d - e - f) 0 (by linarith only [h1]) (by linarith only [h2])
    linarith only [h]
  · obtain ⟨_, h1, _⟩ := roots_extended_triangle hγ ha
    obtain ⟨_, h2, _⟩ := roots_extended_triangle hγ hb
    have h := hmix (b - a - c) (e - d - f) 0 (by linarith only [h1]) (by linarith only [h2])
    linarith only [h]
  · obtain ⟨_, _, h1⟩ := roots_extended_triangle hγ ha
    obtain ⟨_, _, h2⟩ := roots_extended_triangle hγ hb
    have h := hmix (c - a - b) (f - d - e) 0 (by linarith only [h1]) (by linarith only [h2])
    linarith only [h]
/-- A strict near-Q cube with 3 eta below Q lies in the ordinary Seiberg domain. -/
theorem roots_extended_cube {γ η a b c : ℝ} (hγ : 0 < γ) (hη : 3 * η < Q γ)
    (ha : Q γ - η < a) (haQ : a < Q γ) (hb : Q γ - η < b) (hbQ : b < Q γ)
    (hc : Q γ - η < c) (hcQ : c < Q γ) : ExtendedSeiberg3 γ a b c := by
  have hs : 2 * Q γ < a + b + c := by linarith only [hη, ha, hb, hc]
  have h4 : 0 < 4 / γ := by positivity
  exact extendedSeiberg3_of_lt hγ haQ hbQ hcQ (by linarith only [hs, h4])
    (by linarith only [hs, haQ]) (by linarith only [hs, hbQ]) (by linarith only [hs, hcQ])
end DOZZ.Proofs
