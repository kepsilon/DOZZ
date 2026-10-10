/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Inversion.Representative
import DOZZ.ShiftEquations.Gluing.Meromorphy
import DOZZ.Brownian.Reflection.RtheorAnalytic

/-! Inversion of a nonzero meromorphic three-point germ by applying gluing twice. This uses the
literal gluing equation in `DOZZ.structureConstant_reflected_shift_and_gluing`, hence needs no
independent dual seed. -/

@[expose] public section
open Filter Topology Set
namespace DOZZ.Proofs

/-- Nonzero physical values on a real interval rule out the identically zero germ,
even when the representative has arbitrary isolated point values. -/
theorem order_ne_top_of_real_nonzero
    (C : ℂ → ℂ) (lo hi x : ℝ) (hx : lo < x ∧ x < hi)
    (hreal : ∀ y : ℝ, lo < y → y < hi → C (y : ℂ) ≠ 0) :
    meromorphicOrderAt C (x : ℂ) ≠ ⊤ := by
  intro htop
  have hz := (tendsto_ofReal_nhdsNE x).eventually
    (meromorphicOrderAt_eq_top_iff.mp htop)
  have hI : ∀ᶠ y : ℝ in 𝓝[≠] x, y ∈ Ioo lo hi :=
    nhdsWithin_le_nhds (Ioo_mem_nhds hx.1 hx.2)
  obtain ⟨y, hyI, hyz⟩ := (hI.and hz).exists
  exact hreal y hyI.1 hyI.2 hyz

/-- Applying the gluing equation of `DOZZ.structureConstant_reflected_shift_and_gluing` twice
cancels the three-point germ away from its discrete zeros. The resulting inversion identity is on
the entire strip. -/
theorem inversion_of_gluing
    (C R : ℂ → ℂ) (q H lo hi : ℝ) (hH : 0 < H) (hlohi : lo < hi)
    (hC : MeromorphicOn C (horizontalStrip H))
    (hreal : ∀ y : ℝ, lo < y → y < hi → C (y : ℂ) ≠ 0)
    (hglue : ∀ᶠ z in codiscrete ℂ, C z = R z * C ((q : ℂ) - z)) :
    ∀ᶠ z in codiscreteWithin (horizontalStrip H), R z * R ((q : ℂ) - z) = 1 := by
  obtain ⟨x, hxlo, hxhi⟩ := exists_between hlohi
  have hxS : (x : ℂ) ∈ horizontalStrip H := by
    simpa only [horizontalStrip, mem_ofPred_eq, Complex.ofReal_im, abs_zero] using hH
  have horder := order_ne_top_of_real_nonzero C lo hi x ⟨hxlo, hxhi⟩ hreal
  have hne := MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero hC
    (fun z hz => hC.meromorphicOrderAt_ne_top_of_isPreconnected
      (isPreconnected_horizontalStrip H) hxS hz horder)
  have hle := (codiscreteWithin_le_codiscrete_inf_principal (horizontalStrip H)).trans
    inf_le_left
  filter_upwards [hglue.filter_mono hle,
    (codiscrete_reflect hglue q).filter_mono hle, hne] with z hz hzr hzn
  rw [sub_sub_cancel] at hzr
  apply mul_right_cancel₀ hzn
  rw [one_mul, mul_assoc, ← hzr, ← hz]

end DOZZ.Proofs
