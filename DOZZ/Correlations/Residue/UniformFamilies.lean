/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.LocalWeightFamily

/-! Common bounds for the two exact weight classes supplied to the two-insertion tail theorem
`DOZZ.twoInsertion_tail_sum_uniform`. -/

@[expose] public section
open MeasureTheory Set
namespace DOZZ.Proofs

/-- Enlarge common upper bounds and decrease the positive center lower bound. -/
theorem residue_uniformFamily_mono_bounds
    (K : Set ℂ) (F : ℂ → Set (ℂ → ℝ)) (r s d l s' d' l' : ℝ)
    (hF : UniformPositiveC1Family K F r s d l)
    (hs : s ≤ s') (hd : d ≤ d') (hl : l' ≤ l) (hl' : 0 < l') :
    UniformPositiveC1Family K F r s' d' l' := by
  rcases hF with ⟨hr, hs0, hd0, _, hF⟩
  refine ⟨hr, hs0.trans hs, hd0.trans hd, hl', ?_⟩
  intro z hz f hf
  rcases hF z hz f hf with ⟨hm, hb, hlz, hc, hder⟩
  exact ⟨hm, fun x => ⟨(hb x).1, (hb x).2.trans hs⟩, hl.trans hlz,
    hc, fun x hx => (hder x hx).trans hd⟩

/-- Two separately constructed positive C1 classes admit the shared bounds required by the
exact two-insertion tail statement. -/
theorem residue_uniformFamilies_common_bounds
    (K1 K2 : Set ℂ) (F1 F2 : ℂ → Set (ℂ → ℝ)) (r s1 d1 l1 s2 d2 l2 : ℝ)
    (h1 : UniformPositiveC1Family K1 F1 r s1 d1 l1)
    (h2 : UniformPositiveC1Family K2 F2 r s2 d2 l2) :
    ∃ s d l : ℝ, UniformPositiveC1Family K1 F1 r s d l ∧
      UniformPositiveC1Family K2 F2 r s d l := by
  refine ⟨max s1 s2, max d1 d2, min l1 l2, ?_, ?_⟩
  · exact residue_uniformFamily_mono_bounds K1 F1 r s1 d1 l1 _ _ _ h1
      (le_max_left _ _) (le_max_left _ _) (min_le_left _ _) (lt_min h1.2.2.2.1 h2.2.2.2.1)
  · exact residue_uniformFamily_mono_bounds K2 F2 r s2 d2 l2 _ _ _ h2
      (le_max_right _ _) (le_max_right _ _) (min_le_right _ _) (lt_min h1.2.2.2.1 h2.2.2.2.1)

end DOZZ.Proofs
