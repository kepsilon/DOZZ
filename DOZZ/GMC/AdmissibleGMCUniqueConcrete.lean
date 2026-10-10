/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.AdmissibleGMCUniqueness
public import DOZZ.GMC.AdmissibleGMCCountableTests
public import DOZZ.GMC.AdmissibleGMCDetermines
public import DOZZ.Statements.GMC.IsAdmissibleLogRegularization

/-! Concrete almost-sure uniqueness for admissible GMC versions of one regularization. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Topology
open scoped CompactlySupported

namespace DOZZ.Proofs

/-- Two admissible GMC versions of the same regularization agree almost surely. The compact-test
uniqueness is applied on a concrete countable family, which determines locally finite measures
carried by the open chart. -/
theorem admissible_regularization_measure_unique_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (γ : ℝ) (M N : Ω → Measure ℂ)
    (hM : IsAdmissibleGMCVersion P U dens Y γ M)
    (hN : IsAdmissibleGMCVersion P U dens Y γ N) :
    ∀ᵐ ω ∂P, M ω = N ω := by
  obtain ⟨K, hKcompact, hKU, hKmono, hKcover, hKcofinal, f, hf, hdense⟩ :=
    exists_countable_dense_admissible_tests U hY.openChart
  have hEach : ∀ nm : ℕ × ℕ,
      (fun ω => ∫ x, f nm x ∂M ω) =ᵐ[P] fun ω => ∫ x, f nm x ∂N ω := by
    intro nm
    exact admissible_regularization_test_integral_unique_ae P U dens Y γ M N hM hN
      (f nm) (hf nm.1 nm.2).1 ((hf nm.1 nm.2).2.2)
  have hAll : ∀ᵐ ω ∂P, ∀ nm : ℕ × ℕ,
      ∫ x, f nm x ∂M ω = ∫ x, f nm x ∂N ω := by
    rw [ae_all_iff]
    exact hEach
  filter_upwards [hAll] with ω hω
  exact admissible_countable_tests_determine_chart_measures U hY.openChart (M ω) (N ω)
    (hM.2.1 ω) (hN.2.1 ω)
    (fun L hL hLU => (hM.2.2.1 ω L hL hLU))
    (fun L hL hLU => (hN.2.2.1 ω L hL hLU))
    K hKcompact hKU hKcofinal f
    (fun n m => ⟨(hf n m).1, (hf n m).2.1⟩)
    (fun n g hg hgs δ hδ => hdense n g hg hgs δ hδ)
    (fun n m => hω (n, m))


end DOZZ.Proofs
