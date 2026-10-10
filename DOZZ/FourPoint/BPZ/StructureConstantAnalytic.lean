/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.StructureConstantHolomorphic
public import DOZZ.FourPoint.BPZ.GammaAnalytic
public import DOZZ.Statements.Defs.StructureConstant
public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
public import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Real analyticity of the structure constant in the first charge

On the extended Seiberg domain, the unit-volume structure constant is the restriction of a
holomorphic function of the three charges
(`DOZZ.unitVolumeStructureConstant_holomorphic_near_extended_domain`). Restricting it to the
complex line through the first charge gives a holomorphic function of one variable, so the
structure constant is real-analytic in the first charge; the normalization `μ^{-s} Γ(s)` is
real-analytic for `s > 0`. -/

@[expose] public section

open MeasureTheory Filter Topology

namespace DOZZ.Proofs

/-- The structure constant is `μ^{-s} Γ(s)` times the unit-volume structure constant. -/
theorem bpz_structureConstant_eq_unitVolume {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) (γ μ α₁ α₂ α₃ : ℝ) :
    structureConstant P M γ μ α₁ α₂ α₃ =
      μ ^ (-sExp γ α₁ α₂ α₃) * Real.Gamma (sExp γ α₁ α₂ α₃) *
        unitVolumeStructureConstant P M γ α₁ α₂ α₃ := by
  unfold structureConstant unitVolumeStructureConstant
  ring

/-- The extended Seiberg condition is open in the first charge. -/
theorem bpz_extendedSeiberg3_eventually {γ α₁ α₂ α₃ : ℝ} (h : ExtendedSeiberg3 γ α₁ α₂ α₃) :
    ∀ᶠ t in 𝓝 α₁, ExtendedSeiberg3 γ t α₂ α₃ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hs : ContinuousAt (fun t => -sExp γ t α₂ α₃) α₁ := by
    unfold sExp
    fun_prop
  have hm : ContinuousAt (fun t => min (4 / γ ^ 2) (min (2 / γ * (Q γ - t))
      (min (2 / γ * (Q γ - α₂)) (2 / γ * (Q γ - α₃))))) α₁ := by
    fun_prop
  filter_upwards [continuousAt_id.eventually_lt continuousAt_const h1,
    hs.eventually_lt hm h4] with t ht1 ht4
  exact ⟨ht1, h2, h3, ht4⟩

/-- The complex line through the first charge. -/
theorem bpz_complexify_line (t α₂ α₃ : ℝ) :
    complexifyNCharges ![t, α₂, α₃] = ![(t : ℂ), (α₂ : ℂ), (α₃ : ℂ)] := by
  funext i
  fin_cases i <;> rfl

/-- The unit-volume structure constant is real-analytic in the first charge on the extended
Seiberg domain. -/
theorem bpz_analyticAt_unitVolumeStructureConstant {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (M : Ω → Measure ℂ) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hM : IsGMCOf P X γ M) {α₁ α₂ α₃ : ℝ}
    (h : ExtendedSeiberg3 γ α₁ α₂ α₃) :
    AnalyticAt ℝ (fun t => unitVolumeStructureConstant P M γ t α₂ α₃) α₁ := by
  obtain ⟨V, hVo, hVmem, f, hf, hfeq⟩ :=
    unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM
  set e : ℂ → (Fin 3 → ℂ) := fun τ => ![τ, (α₂ : ℂ), (α₃ : ℂ)] with he_def
  have he : ∀ t : ℝ, e (t : ℂ) = complexifyNCharges ![t, α₂, α₃] := fun t =>
    (bpz_complexify_line t α₂ α₃).symm
  have hediff : Differentiable ℂ e := by
    rw [he_def]
    refine differentiable_pi.mpr fun i => ?_
    fin_cases i
    · exact differentiable_id
    · exact differentiable_const _
    · exact differentiable_const _
  have hU : IsOpen (e ⁻¹' V) := hVo.preimage hediff.continuous
  have hmem : (α₁ : ℂ) ∈ e ⁻¹' V := by
    rw [Set.mem_preimage, he]
    exact hVmem _ h
  have hF : DifferentiableOn ℂ (f ∘ e) (e ⁻¹' V) :=
    hf.comp hediff.differentiableOn fun τ hτ => hτ
  have hFa : AnalyticAt ℂ (f ∘ e) (α₁ : ℂ) := hF.analyticAt (hU.mem_nhds hmem)
  have h1 : AnalyticAt ℝ (fun t : ℝ => (t : ℂ)) α₁ := Complex.ofRealCLM.analyticAt α₁
  have h2 : AnalyticAt ℝ (fun t : ℝ => (f ∘ e) (t : ℂ)) α₁ :=
    (hFa.restrictScalars (𝕜 := ℝ)).comp h1
  have hg : AnalyticAt ℝ (fun t : ℝ => ((f ∘ e) (t : ℂ)).re) α₁ :=
    (Complex.reCLM.analyticAt _).comp h2
  refine hg.congr ?_
  filter_upwards [bpz_extendedSeiberg3_eventually h] with t ht
  have hval := hfeq ![t, α₂, α₃] ht
  simp only [Function.comp_apply, he, hval, Complex.ofReal_re]
  rfl

/-- The structure constant is real-analytic in the first charge on the extended Seiberg domain
with a positive Seiberg exponent. -/
theorem bpz_analyticAt_structureConstant {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (M : Ω → Measure ℂ) (γ μ : ℝ) (hγ : 0 < γ)
    (hγ2 : γ < 2) (hμ : 0 < μ) (hM : IsGMCOf P X γ M) {α₁ α₂ α₃ : ℝ}
    (h : ExtendedSeiberg3 γ α₁ α₂ α₃) (hs : 0 < sExp γ α₁ α₂ α₃) :
    AnalyticAt ℝ (fun t => structureConstant P M γ μ t α₂ α₃) α₁ := by
  have hfun : (fun t => structureConstant P M γ μ t α₂ α₃) = fun t =>
      Real.exp (Real.log μ * -sExp γ t α₂ α₃) * Real.Gamma (sExp γ t α₂ α₃) *
        unitVolumeStructureConstant P M γ t α₂ α₃ := by
    funext t
    rw [bpz_structureConstant_eq_unitVolume, Real.rpow_def_of_pos hμ]
  rw [hfun]
  have haff : AnalyticAt ℝ (fun t => sExp γ t α₂ α₃) α₁ := by
    unfold sExp
    fun_prop
  have hexp : AnalyticAt ℝ (fun t => Real.exp (Real.log μ * -sExp γ t α₂ α₃)) α₁ :=
    analyticAt_rexp.comp (analyticAt_const.mul haff.neg)
  have hpole : ∀ m : ℕ, sExp γ α₁ α₂ α₃ ≠ -(m : ℝ) := by
    intro m hm
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hgam : AnalyticAt ℝ (fun t => Real.Gamma (sExp γ t α₂ α₃)) α₁ :=
    AnalyticAt.comp (g := Real.Gamma) (f := fun t => sExp γ t α₂ α₃)
      (bpz_analyticAt_real_Gamma hpole) haff
  exact (hexp.mul hgam).mul
    (bpz_analyticAt_unitVolumeStructureConstant P X hX M γ hγ hγ2 hM h)

end DOZZ.Proofs
