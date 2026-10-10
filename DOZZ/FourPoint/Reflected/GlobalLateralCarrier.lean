/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.ChartMassMeasurable
public import DOZZ.FourPoint.Reflected.ConditionalCompactLimit
/-! One actual measurable lateral carrier on the entire punctured plane. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- Radial removal preserves finite mass on every compact set away from the origin, for
every continuous radial path and every finite input measure. -/
theorem reflected_removed_mass_compact_finite (γ : ℝ) (A : TwoSidedPath)
    (μ : Measure ℂ) [IsFiniteMeasure μ] (K : Set ℂ) (hK : IsCompact K)
    (hK0 : K ⊆ ({0} : Set ℂ)ᶜ) :
    μ.withDensity (lateralRadialWeight γ A) K < ⊤ := by
  let f : ℂ → ℝ := fun x => Real.exp (-γ*A (-Real.log ‖x‖)+γ*Q γ*|Real.log ‖x‖|)
  have hc : ContinuousOn f K := by
    intro x hx
    have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr (by simpa using hK0 hx)
    have hl : ContinuousAt (fun x : ℂ => Real.log ‖x‖) x :=
      continuous_norm.continuousAt.log hx0
    exact ((continuousAt_const.mul (A.continuous.continuousAt.comp hl.neg)).add
      (continuousAt_const.mul hl.abs)).rexp.continuousWithinAt
  have hi := ContinuousOn.integrableOn_compact hK hc (μ := μ)
  have he : (∫⁻ x in K, lateralRadialWeight γ A x ∂μ) =
      ∫⁻ x in K, ENNReal.ofReal (f x) ∂μ := by
    apply setLIntegral_congr_fun hK.measurableSet
    intro x hx
    have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr (by simpa using hK0 hx)
    simp only [lateralRadialWeight, ite_eq_right hx0]
    rfl
  rw [withDensity_apply _ hK.measurableSet, he,
    ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun x => (Real.exp_pos _).le))]
  exact ENNReal.ofReal_lt_top

/-- A single measurable independent lateral measure agrees with the actual radial-removed
GMC and is locally finite on the entire punctured plane, on every sample. -/
theorem reflected_global_lateral_carrier
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    ∃ N : Ω → Measure ℂ, Measurable N ∧
      IndepFun (originRadialPath Xc) N P ∧
      (∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤) ∧
      N =ᵐ[P] (fun ω => (M ω).withDensity
        (lateralRadialWeight γ (originRadialPath Xc ω))) := by
  let A := originRadialPath Xc
  have hA : AEMeasurable A P := originRadialPath_aemeasurable P X Xc hc hcont
  obtain ⟨M', hM', hMf, hMeq⟩ := equatorGFF_GMC_measurable_version P X hX γ hγ hγ₂ M hM
  let MF : Ω → FiniteMeasure ℂ := fun ω => ⟨M' ω, hMf ω⟩
  have hMF : Measurable MF := Measurable.subtype_mk hM'
  let N : Ω → Measure ℂ := fun ω => (M' ω).withDensity
    (lateralRadialWeight γ (hA.mk A ω))
  have harg : Measurable (fun ω : Ω => ((γ, hA.mk A ω), MF ω)) :=
    ((measurable_const.prodMk hA.measurable_mk).prodMk hMF)
  have hN : Measurable N := by
    change Measurable ((fun p : (ℝ × TwoSidedPath) × FiniteMeasure ℂ =>
      (p.2 : Measure ℂ).withDensity (lateralRadialWeight p.1.1 p.1.2)) ∘
        fun ω : Ω => ((γ, hA.mk A ω), MF ω))
    exact measurable_originRadialRemovedGMC_finite.comp harg
  have heq : N =ᵐ[P] (fun ω => (M ω).withDensity (lateralRadialWeight γ (A ω))) := by
    exact (hMeq.and hA.ae_eq_mk).mono fun ω hω =>
      congrArg₂ (fun (μ : Measure ℂ) (a : TwoSidedPath) =>
        μ.withDensity (lateralRadialWeight γ a)) hω.1.symm hω.2.symm
  refine Exists.intro N ?_
  apply And.intro hN
  apply And.intro
  · exact (originRadialRemovedGMC_indep P X Xc hX hc hm hcont γ hγ hγ₂ M hM).congr
      (ae_of_all P fun _ => rfl) heq.symm
  · apply And.intro
    · intro ω K hK hK0
      let _ := hMf ω
      exact reflected_removed_mass_compact_finite γ (hA.mk A ω) (M' ω) K hK hK0
    · exact heq

end DOZZ.Proofs
