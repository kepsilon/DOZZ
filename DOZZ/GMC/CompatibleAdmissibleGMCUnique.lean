/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.AdmissibleGMCUniqueConcrete
public import DOZZ.Statements.GMC.IsCompatibleAdmissibleRegularizations
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Uniqueness transfer once mixed cutoff test integrals are Cauchy in measure. -/

@[expose] public section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped CompactlySupported

namespace DOZZ.Proofs

/-- Subtraction preserves convergence in measure for real-valued families. -/
theorem tendstoInMeasure_sub
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) {l : Filter ι}
    (F G : ι → Ω → ℝ) (Flim Glim : Ω → ℝ)
    (hF : TendstoInMeasure P F l Flim)
    (hG : TendstoInMeasure P G l Glim) :
    TendstoInMeasure P (fun i ω => F i ω - G i ω) l
      (fun ω => Flim ω - Glim ω) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hFnorm := (tendstoInMeasure_iff_norm).mp hF
  have hGnorm := (tendstoInMeasure_iff_norm).mp hG
  have hFzero : Tendsto
      (fun i => P {ω | δ ≤ ‖F i ω - Flim ω‖}) l (𝓝 0) := hFnorm δ hδ
  have hGzero : Tendsto
      (fun i => P {ω | δ ≤ ‖G i ω - Glim ω‖}) l (𝓝 0) := hGnorm δ hδ
  have hsum : Tendsto
      (fun i => P {ω | δ ≤ ‖F i ω - Flim ω‖} +
        P {ω | δ ≤ ‖G i ω - Glim ω‖}) l (𝓝 0) := by
    simpa using hFzero.add hGzero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum ?_ ?_
  · intro i
    exact bot_le
  · intro i
    let A : Set Ω := {ω | δ ≤ ‖F i ω - Flim ω‖}
    let B : Set Ω := {ω | δ ≤ ‖G i ω - Glim ω‖}
    let E : Set Ω := {ω | ε ≤ ‖(F i ω - G i ω) - (Flim ω - Glim ω)‖}
    have hsubset : E ⊆ A ∪ B := by
      intro ω hω
      change ε ≤ ‖(F i ω - G i ω) - (Flim ω - Glim ω)‖ at hω
      have htriangle :
          ‖(F i ω - G i ω) - (Flim ω - Glim ω)‖ ≤
            ‖F i ω - Flim ω‖ + ‖G i ω - Glim ω‖ := by
        calc
          _ = ‖(F i ω - Flim ω) - (G i ω - Glim ω)‖ := by congr 1; ring
          _ ≤ _ := norm_sub_le _ _
      by_contra hnot
      have hFlt : ‖F i ω - Flim ω‖ < δ := lt_of_not_ge (by
        intro h
        exact hnot (Or.inl h))
      have hGlt : ‖G i ω - Glim ω‖ < δ := lt_of_not_ge (by
        intro h
        exact hnot (Or.inr h))
      have hFltNorm : ‖F i ω - Flim ω‖ < δ := by
        simpa only [Real.norm_eq_abs] using hFlt
      have hGltNorm : ‖G i ω - Glim ω‖ < δ := by
        simpa only [Real.norm_eq_abs] using hGlt
      have hsumlt : ‖F i ω - Flim ω‖ + ‖G i ω - Glim ω‖ < ε := by
        calc
          _ < δ + δ := add_lt_add hFltNorm hGltNorm
          _ = ε := by dsimp [δ]; ring
      exact (not_le_of_gt (lt_of_le_of_lt htriangle hsumlt)) hω
    change P E ≤ P A + P B
    calc
      P E ≤ P (A ∪ B) := measure_mono hsubset
      _ ≤ P A + P B := measure_union_le A B

/-- Restrict a two-parameter limit to the diagonal cutoff sequence. -/
theorem tendstoInMeasure_prod_diagonal
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℝ × ℝ → Ω → ℝ) (G : Ω → ℝ)
    (hF : TendstoInMeasure P F (atTop ×ˢ atTop) G) :
    TendstoInMeasure P (fun r ω => F (r, r) ω) atTop G := by
  exact hF.comp (tendsto_id.prodMk tendsto_id)

/-- If two cutoff families converge in measure and their same-scale difference tends to zero,
their limits agree almost everywhere. -/
theorem tendstoInMeasure_limits_eq_of_difference_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F G : ℝ → Ω → ℝ) (Flim Glim : Ω → ℝ)
    (hF : TendstoInMeasure P F atTop Flim)
    (hG : TendstoInMeasure P G atTop Glim)
    (hFG : TendstoInMeasure P (fun r ω => F r ω - G r ω)
      atTop (fun _ => 0)) :
    Flim =ᵐ[P] Glim := by
  have hzero : (fun _ : Ω => (0 : ℝ)) =ᵐ[P]
      (fun ω => Flim ω - Glim ω) :=
    tendstoInMeasure_ae_unique hFG (tendstoInMeasure_sub P F G Flim Glim hF hG)
  filter_upwards [hzero] with ω hω
  linarith

/-- Two admissible GMC versions agree almost surely if the mixed cutoff test integrals tend to
the same limit in probability. This isolates the countable measure-determination step from the
growing-barrier estimate. -/
theorem compatible_admissible_gmc_measure_unique_ae_of_mixed_test_cauchy
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (_hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    (_hYZ : IsCompatibleAdmissibleRegularizations P U ε₀ ε₁ Y Z)
    (γ : ℝ) (M N : Ω → Measure ℂ)
    (hM : IsAdmissibleGMCVersion P U dens Y γ M)
    (hN : IsAdmissibleGMCVersion P U dens Z γ N)
    (hcross : ∀ f : BoundedContinuousFunction ℂ ℝ,
      HasCompactSupport (f : ℂ → ℝ) → tsupport (f : ℂ → ℝ) ⊆ U →
      TendstoInMeasure P
        (fun p : ℝ × ℝ => fun ω =>
          regularizedLogChaosTestMass P U dens Y γ p.1 ω f -
            regularizedLogChaosTestMass P U dens Z γ p.2 ω f)
        (atTop ×ˢ atTop) (fun _ => 0)) :
    ∀ᵐ ω ∂P, M ω = N ω := by
  obtain ⟨K, hKcompact, hKU, hKmono, hKcover, hKcofinal, f, hf, hdense⟩ :=
    exists_countable_dense_admissible_tests U hY.openChart
  have hEach : ∀ nm : ℕ × ℕ,
      (fun ω => ∫ x, f nm x ∂M ω) =ᵐ[P]
        fun ω => ∫ x, f nm x ∂N ω := by
    intro nm
    have hlimY := hM.2.2.2 (f nm) (hf nm.1 nm.2).1 ((hf nm.1 nm.2).2.2)
    have hlimZ := hN.2.2.2 (f nm) (hf nm.1 nm.2).1 ((hf nm.1 nm.2).2.2)
    have hcross' := hcross (f nm) (hf nm.1 nm.2).1 ((hf nm.1 nm.2).2.2)
    have hcrossDiag : TendstoInMeasure P
        (fun r ω => regularizedLogChaosTestMass P U dens Y γ r ω (f nm) -
          regularizedLogChaosTestMass P U dens Z γ r ω (f nm))
        atTop (fun _ => 0) := by
      simpa only [Prod.fst, Prod.snd] using
        tendstoInMeasure_prod_diagonal P
          (fun p ω => regularizedLogChaosTestMass P U dens Y γ p.1 ω (f nm) -
            regularizedLogChaosTestMass P U dens Z γ p.2 ω (f nm))
          (fun _ => 0) hcross'
    exact tendstoInMeasure_limits_eq_of_difference_zero P
        (fun r ω => regularizedLogChaosTestMass P U dens Y γ r ω (f nm))
        (fun r ω => regularizedLogChaosTestMass P U dens Z γ r ω (f nm))
        (fun ω => ∫ x, f nm x ∂M ω) (fun ω => ∫ x, f nm x ∂N ω)
        hlimY hlimZ hcrossDiag
  have hAll : ∀ᵐ ω ∂P, ∀ nm : ℕ × ℕ,
      ∫ x, f nm x ∂M ω = ∫ x, f nm x ∂N ω := by
    rw [ae_all_iff]
    exact hEach
  filter_upwards [hAll] with ω hω
  exact admissible_countable_tests_determine_chart_measures U hY.openChart (M ω) (N ω)
    (hM.2.1 ω) (hN.2.1 ω)
    (fun L hL hLU => hM.2.2.1 ω L hL hLU)
    (fun L hL hLU => hN.2.2.1 ω L hL hLU)
    K hKcompact hKU hKcofinal f
    (fun n m => ⟨(hf n m).1, (hf n m).2.1⟩)
    (fun n g hg hgs δ hδ => hdense n g hg hgs δ hδ)
    (fun n m => hω (n, m))


end DOZZ.Proofs
