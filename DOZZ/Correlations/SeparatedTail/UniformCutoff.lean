/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.SeparatedTail.CutoffBound
public import DOZZ.Correlations.SeparatedTail.ChargeSlack
public import DOZZ.Statements.GMC.EquatorGFFGMCWeightedCutoffBound

/-! The compact geometry and charge sets select one mixed-cutoff moment constant for the
separated joint-tail estimate. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Metric Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Uniformity is selected before choosing centers, charges or cutoff. Each Dirichlet order
stays at least `ε/2` below its insertion and bulk thresholds. -/
theorem separatedTail_cutoff_mixed_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (K2 K3 : Set ℂ) (hK2 : IsCompact K2) (hK3 : IsCompact K3)
    (hsep : ∀ z2 ∈ K2, ∀ z3 ∈ K3, 3 ≤ ‖z2-z3‖)
    (A2 A3 : Set ℝ) (hA2 : IsCompact A2) (hA3 : IsCompact A3)
    (hα2 : ∀ α ∈ A2, γ/2 < α ∧ α < Q γ)
    (hα3 : ∀ α ∈ A3, γ/2 < α ∧ α < Q γ)
    (ε : ℝ) (hε : 0 < ε)
    (hε2 : ∀ α ∈ A2, ε < reflectionExponent γ α)
    (hε3 : ∀ α ∈ A3, ε < reflectionExponent γ α) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧
      ∀ z2 ∈ K2, ∀ z3 ∈ K3, ∀ α2 ∈ A2, ∀ α3 ∈ A3, ∀ δ : ℝ,
        0 < δ → δ < 1/4 →
        (∫⁻ ω, cutoffWeightedGmcBallMass P Xc γ α2 z2 1 δ ω ^ (reflectionExponent γ α2-ε) *
          cutoffWeightedGmcBallMass P Xc γ α3 z3 1 δ ω ^ (reflectionExponent γ α3-ε) ∂P) ≤ B := by
  classical
  let _ : IsProbabilityMeasure P := hX.1
  obtain ⟨q,hq,hqs⟩ := separatedTail_exists_uniform_holder_slack hγ hε
  let p := Real.conjExponent q
  have hpq : p.HolderConjugate q := (Real.HolderConjugate.conjExponent hq).symm
  let T : ℝ := 4/γ^2
  have hT : 0 < T := by dsimp [T]; positivity
  have hadm (α : ℝ) (hα : α ∈ A2 ∪ A3) :
      γ/2 < α ∧ α < Q γ ∧ ε < reflectionExponent γ α := by
    rcases hα with h | h
    · exact ⟨(hα2 α h).1,(hα2 α h).2,hε2 α h⟩
    · exact ⟨(hα3 α h).1,(hα3 α h).2,hε3 α h⟩
  let params : ℝ → ℝ × ℝ := fun α => (α, q*(reflectionExponent γ α-ε))
  have hparams : Continuous params := by unfold params reflectionExponent; fun_prop
  have hpc : IsCompact (params '' (A2 ∪ A3)) := (hA2.union hA3).image hparams
  obtain ⟨C0,hC0,hC0b⟩ := DOZZ.equatorGFF_GMC_weighted_cutoff_bound P X hX γ hγ hγ2 Xc hc
    (params '' (A2 ∪ A3)) hpc (by
      rintro _ ⟨α,hα,rfl⟩
      obtain ⟨hαlo,hαhi,hαε⟩ := hadm α hα
      obtain ⟨ht,hti,htb⟩ := hqs α hαlo hαε
      refine ⟨hαhi,ht,lt_min ?_ ?_⟩
      · linarith
      · change q*(reflectionExponent γ α-ε) < 2/γ*(Q γ-α)
        have he : 2/γ*(Q γ-α) = reflectionExponent γ α := by unfold reflectionExponent; ring
        rw [he]
        linarith)
    (K2 ∪ K3) (hK2.union hK3) 1 (by norm_num)
  obtain ⟨Z,hZ⟩ := (hK2.union hK3).exists_bound_of_continuousOn (f := fun z : ℂ => ‖z‖)
    continuous_norm.continuousOn
  let R : ℝ := max Z 0+3
  have hR : 1 < R := by dsimp [R]; linarith [le_max_right Z 0]
  have hnorm (z : ℂ) (hz : z ∈ K2 ∪ K3) : ‖z‖ ≤ max Z 0 := by
    have hn : ‖z‖ ≤ Z := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)] using hZ z hz
    exact hn.trans (le_max_left _ _)
  obtain ⟨C,hC,hdata⟩ := separatedTail_exists_markov_data R hR
  let b : ℝ≥0∞ := ENNReal.ofReal C0
  let BD : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ^2*(4+2*R)/2*(T^2+T)))*b
  let BE : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ^2*(4+2*R)/2*(2*T*p)))*
    (2*ENNReal.ofReal (C (2*(γ*T*p))))
  have hBD : BD < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hBE : BE < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)
  refine ⟨BE^(1/p)*(BD*BD)^(1/q),
    separatedTail_mixed_moment_constant_lt_top BE BD BD hBE hBD hBD p q hpq, ?_⟩
  intro z2 hz2 z3 hz3 α2 hα2mem α3 hα3mem δ hδ hδ4
  let c : Fin 2 → ℂ := ![z2,z3]
  let α : Fin 2 → ℝ := ![α2,α3]
  let a : Fin 2 → ℝ := fun i => reflectionExponent γ (α i)-ε
  have hcK : ∀ i, c i ∈ K2 ∪ K3 := by
    intro i
    fin_cases i
    · exact Or.inl hz2
    · exact Or.inr hz3
  have hαA : ∀ i, α i ∈ A2 ∪ A3 := by
    intro i
    fin_cases i
    · exact Or.inl hα2mem
    · exact Or.inr hα3mem
  have hpin : ∀ i, ‖c i‖+5/4+1/4 ≤ R := by
    intro i
    have hn := hnorm (c i) (hcK i)
    dsimp [R]
    linarith
  have hsep' : ∀ i j, i ≠ j → 3 ≤ ‖c i-c j‖ := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hsep z2 hz2 z3 hz3
    · change 3 ≤ ‖z3-z2‖
      rw [norm_sub_rev]
      exact hsep z2 hz2 z3 hz3
    · exact (hij rfl).elim
  obtain ⟨data⟩ := hdata Ω P X Xc hX hc c hpin hsep'
  have ha (i : Fin 2) : 0 < a i := sub_pos.mpr (hadm (α i) (hαA i)).2.2
  have hqa (i : Fin 2) : a i*q < T := by
    have hh := (hqs (α i) (hadm (α i) (hαA i)).1 (hadm (α i) (hαA i)).2.2).2.2
    dsimp [T,a]
    nlinarith
  have haT (i : Fin 2) : a i ≤ T := by
    have hmul : a i ≤ a i*q := by nlinarith [ha i]
    exact hmul.trans (hqa i).le
  have hbare (i : Fin 2) : (∫⁻ ω, cutoffWeightedGmcBallMass P Xc γ (α i) (c i) 1 δ ω ^ (a i*q) ∂P) ≤ b := by
    have hb := hC0b (params (α i)) ⟨α i,hαA i,rfl⟩ (c i) (hcK i) δ 1 hδ (by linarith) le_rfl
    simpa only [params,a,b,mul_comm,Real.rpow_eq_pow,Real.one_rpow,mul_one,ENNReal.rpow_eq_pow] using hb
  exact separatedTail_cutoff_mixed_bound_of_markov_data P X hX Xc hc c R hR
    (fun i => by have := hpin i; linarith) C data γ hγ α a
    (fun i => by have := (hadm (α i) (hαA i)).1; linarith) p q T hpq hT ha haT
    (fun i => (hqa i).le) b δ hδ hδ4 hbare

end DOZZ.Proofs
