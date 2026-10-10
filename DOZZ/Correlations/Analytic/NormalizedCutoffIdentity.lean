/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.NormalizedRealValue
public import DOZZ.Complex.Identity

/-! The exact fixed-region cutoff identity, extended from real to complex charges. -/

@[expose] public section
open MeasureTheory
namespace DOZZ.Proofs

/-- Moving all vertex circles while retaining the old spatial region leaves the normalized
observable unchanged on every real-centered polydisc in the bulk half-space. -/
theorem normalized_vertex_fixed_region_eqOn
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (z : Fin N → ℂ) (r s : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s)
    (O : Set ℂ) (ho : IsOpen O) (hb : Bornology.IsBounded O) (hn : O.Nonempty)
    (hO : O ⊆ retainedRegion z r)
    (a R : Fin (N + 1) → ℝ) (hR : ∀ i, 0 < R i)
    (hbulk : ∀ β ∈ complexPolydisc (fun i => (a i : ℂ)) R,
      (complexMomentPower γ β).re < 4 / γ ^ 2) :
    Set.EqOn (normalizedVertexMoment P Xc M O γ z s)
      (normalizedVertexMoment P Xc M O γ z r)
      (complexPolydisc (fun i => (a i : ℂ)) R) := by
  have hs := (normalized_vertex_moment_holomorphic P X hX γ hγ hγ2 M hM Xc hXc
    O ho hb hn z s).2
  have hr' := (normalized_vertex_moment_holomorphic P X hX γ hγ hγ2 M hM Xc hXc
    O ho hb hn z r).2
  apply eqOn_polydisc_of_real_box a R hR _ _ (hs.mono hbulk) (hr'.mono hbulk)
  intro β _
  rw [normalized_vertex_moment_ofReal P X hX γ hγ hγ2 M hM Xc hXc β z s
      (hr.trans hrs) O ho hb hn (hO.trans (retainedRegion_mono z hrs)),
    normalized_vertex_moment_ofReal P X hX γ hγ hγ2 M hM Xc hXc β z r hr O ho hb hn hO]

end DOZZ.Proofs
