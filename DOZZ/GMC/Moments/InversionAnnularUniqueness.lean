/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionAdmissiblePair
public import DOZZ.GMC.Moments.InversionChartTransport
public import DOZZ.GMC.AdmissibleGMCRestriction

/-! Regularization uniqueness (`DOZZ.admissibleLogRegularization_GMC_unique_ae`) identifies the
inverted chaos on annular charts. -/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Distributions ENNReal

namespace DOZZ.Proofs

/-- The transformed-circle chaos is almost surely the inverted arbitrary GMC measure, restricted to
the bounded annular chart. This applies `DOZZ.admissibleLogRegularization_GMC_unique_ae` to the
actual compatible pair on the original probability space. -/
theorem isGMCOf_inversion_annular_version
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (U : Set ℂ) (hUopen : IsOpen U) {m R : ℝ} (hm : 0 < m) (hR : 0 ≤ R)
    (hU : ∀ x ∈ U, 2 * m ≤ ‖x‖ ∧ ‖x‖ ≤ R) :
    ∃ f : (ℂ × ℝ) → ℕ → TestFn,
    ∃ hf : ∀ p n, tsupport (f p n : ℂ → ℝ) ⊆ inversionChart,
    ∃ Z : Ω → ℂ → ℝ → ℝ, ∃ N : Ω → Measure ℂ,
      (∀ p, Tendsto (fun n => circleEnergyGap p.1 p.2 (f p n)) atTop (𝓝 0)) ∧
      (∀ x r, MemLp (fun ω => Z ω x r) 2 P) ∧
      (∀ p, Tendsto (fun n => eLpNorm (fun ω =>
        X ω (inversionTest (f p n) (hf p n)) - Z ω p.1 p.2) 2 P) atTop (𝓝 0)) ∧
      IsAdmissibleLogRegularization P U (fun x => normPlus x ^ (-4 : ℝ)) (min (m / 2) 1)
        (fun ω ε x => Z ω x (Real.log (1 / ε))) ∧
      IsAdmissibleGMCVersion P U (fun x => normPlus x ^ (-4 : ℝ))
        (fun ω ε x => Z ω x (Real.log (1 / ε))) γ N ∧
      ∀ᵐ ω ∂P, N ω = ((M ω).map (fun x : ℂ => x⁻¹)).restrict U := by
  obtain ⟨f, hf, Z, hgap, hmem, hlim, hY, hZ, hcompat⟩ :=
    exists_equatorGFF_inversion_admissible_pair X hX Xc hXc U hUopen hm hR hU
  obtain ⟨A, hA, hAeq⟩ := isGMCOf_inversion_chart_transport P X hX γ hγ hγ2 M hM Xc hXc
  have hUsub : U ⊆ inversionChart := by
    intro x hx
    change x ≠ 0
    exact norm_pos_iff.mp (by linarith only [hm, (hU x hx).1])
  have hAU := admissibleGMCVersion_restrict_of_subset P inversionChart U
    (fun x => normPlus x ^ (-4 : ℝ))
    (fun ω ε x => Xc ω x⁻¹ (Real.log (1 / ε))) γ A hA hUopen.measurableSet hUsub
  obtain ⟨N, hN⟩ := admissibleLogRegularization_GMC_exists P U
    (fun x => normPlus x ^ (-4 : ℝ)) (min (m / 2) 1)
    (fun ω ε x => Z ω x (Real.log (1 / ε))) hZ γ hγ hγ2
  have heq := admissibleLogRegularization_GMC_unique_ae P U
    (fun x => normPlus x ^ (-4 : ℝ)) 1 (min (m / 2) 1)
    (fun ω ε x => Xc ω x⁻¹ (Real.log (1 / ε)))
    (fun ω ε x => Z ω x (Real.log (1 / ε))) hY hZ hcompat γ hγ hγ2
    (fun ω => (A ω).restrict U) N hAU hN
  refine ⟨f, hf, Z, N, hgap, hmem, hlim, hZ, hN, ?_⟩
  filter_upwards [heq, hAeq] with ω hω hωA
  exact hω.symm.trans (congrArg (fun μ : Measure ℂ => μ.restrict U) hωA.symm)

end DOZZ.Proofs
