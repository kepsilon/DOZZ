/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.CopiedRadialChart
/-! Joint measurability of full chart masses, including unbounded radial weights. -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Local finiteness on the open chart suffices for joint measurability of an arbitrary
measurable nonnegative parameter weight; no global finiteness of the lateral measure is assumed. -/
theorem reflected_chart_parameter_mass_measurable
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (U : Set ℂ) (hU : IsOpen U) (N : Ω → Measure ℂ) (hN : Measurable N)
    (hfin : ∀ ω K, IsCompact K → K ⊆ U → N ω K < ⊤)
    (F : A × ℂ → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun p : A × Ω => ∫⁻ x in U, F (p.1, x) ∂N p.2) := by
  let _ : LocallyCompactSpace U := hU.locallyCompactSpace
  let E := CompactExhaustion.choice U
  let K : ℕ → Set ℂ := fun n => Subtype.val '' E n
  have hK (n : ℕ) : IsCompact (K n) := (E.isCompact n).image continuous_subtype_val
  have hKU (n : ℕ) : K n ⊆ U := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hKm : Monotone K := fun _ _ hnm => image_mono (E.subset hnm)
  have hKe : (⋃ n, K n) = U := by
    ext x
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, hx⟩
      exact hKU n hx
    · intro hx
      obtain ⟨n, hn⟩ := E.exists_mem ⟨x, hx⟩
      exact mem_iUnion.mpr ⟨n, ⟨⟨x, hx⟩, hn, rfl⟩⟩
  let NF : Ω → ℕ → FiniteMeasure ℂ := fun ω n =>
    ⟨(N ω).restrict (K n), ⟨by simpa only [Measure.restrict_apply_univ] using
      (hfin ω (K n) (hK n) (hKU n))⟩⟩
  have hNF (n : ℕ) : Measurable (fun ω => NF ω n) := Measurable.subtype_mk
    ((measurable_measure_restrict (K n) (hK n).measurableSet).comp hN)
  have hi (p : A × Ω) : (∫⁻ x in U, F (p.1, x) ∂N p.2) =
      ⨆ n, ∫⁻ x, F (p.1, x) ∂(NF p.2 n : Measure ℂ) := by
    rw [← hKe]
    exact setLIntegral_iUnion_of_directed _ hKm.directed_le
  simp_rw [hi]
  apply Measurable.iSup
  intro n
  exact (measurable_lintegral_finiteMeasure_parameter hF).comp
    (measurable_fst.prodMk ((hNF n).comp measurable_snd))

end DOZZ.Proofs
