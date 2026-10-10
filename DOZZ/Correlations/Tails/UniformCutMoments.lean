/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.TailCutParameters
public import DOZZ.Correlations.Tails.ImprovedChargeMoment
public import Mathlib.Topology.Order.Compact

/-! Uniform strict moment margins at the exact one-insertion error ceiling. -/

@[expose] public section
open Set

namespace DOZZ.Proofs

theorem uniform_oneInsertion_cut_moments
    (γ : ℝ) (hγ : 0 < γ) (K : Set ℝ) (hK : IsCompact K) (hn : K.Nonempty)
    (hα : ∀ α ∈ K, γ/2 < α ∧ α < Q γ)
    (η : ℝ) (hη : 0 < η) (hceil : ∀ α ∈ K, η < oneInsertionErrorCeiling γ α) :
    ∃ a : ℝ, ∃ r : ℝ → ℝ, ∃ R g pH qH : ℝ,
      η < a ∧ a < 1 ∧ 0 < R ∧ R < 4/γ^2 ∧ 0 < g ∧ pH.HolderConjugate qH ∧
        ∀ α ∈ K, 0 < r α ∧ r α ≤ R ∧ reflectionExponent γ α+η < (1-a)*r α ∧
          r α*qH+g ≤ oneInsertionMomentCeiling γ α := by
  let p := fun α => reflectionExponent γ α
  let β := fun α => oneInsertionMomentCeiling γ α
  have hp (α : ℝ) (hαk : α ∈ K) : 0 < p α :=
    (residue_critical_order_bounds γ α hγ (hα α hαk).1 (hα α hαk).2).1
  have hβ (α : ℝ) (hαk : α ∈ K) : 0 < β α := by
    have hb : p α < β α := lt_min (lt_add_of_pos_right _ (by positivity))
      (residue_critical_order_bounds γ α hγ (hα α hαk).1 (hα α hαk).2).2
    exact (hp α hαk).trans hb
  have hpc : Continuous p := by unfold p reflectionExponent; fun_prop
  have hβc : Continuous β := by unfold β oneInsertionMomentCeiling reflectionExponent; fun_prop
  let t := fun α => (β α-p α-η)/β α
  have htc : ContinuousOn t K :=
    ((hβc.continuousOn.sub hpc.continuousOn).sub continuous_const.continuousOn).div
      hβc.continuousOn (fun α hαk => (hβ α hαk).ne')
  have hηt (α : ℝ) (hαk : α ∈ K) : η < t α := by
    have hc := (lt_div_iff₀ (by linarith only [hβ α hαk] : 0 < 1+β α)).mp (hceil α hαk)
    apply (lt_div_iff₀ (hβ α hαk)).mpr
    change η*(1+β α) < β α-p α at hc
    linarith only [hc]
  obtain ⟨α₀,hα₀,hmin⟩ := hK.exists_isMinOn hn htc
  obtain ⟨a,hηa,hat₀⟩ := exists_between (hηt α₀ hα₀)
  have hat (α : ℝ) (hαk : α ∈ K) : a < t α := hat₀.trans_le (hmin hαk)
  have ha1 : a < 1 := by
    have ht1 : t α₀ < 1 := (div_lt_one (hβ α₀ hα₀)).mpr (by linarith only [hp α₀ hα₀,hη])
    exact hat₀.trans ht1
  have hden : 0 < 1-a := sub_pos.mpr ha1
  let low := fun α => (p α+η)/(1-a)
  have hlow (α : ℝ) (hαk : α ∈ K) : 0 < low α ∧ low α < β α := by
    refine ⟨div_pos (add_pos (hp α hαk) hη) hden,?_⟩
    have ht := (lt_div_iff₀ (hβ α hαk)).mp (hat α hαk)
    apply (div_lt_iff₀ hden).mpr
    change a*β α < β α-p α-η at ht
    nlinarith only [ht]
  let r := fun α => (low α+β α)/2
  have hr (α : ℝ) (hαk : α ∈ K) : 0 < r α ∧ r α < β α ∧ p α+η < (1-a)*r α := by
    obtain ⟨hl0,hlβ⟩ := hlow α hαk
    have hrl : low α < r α := by dsimp [r]; linarith only [hlβ]
    refine ⟨hl0.trans hrl,by dsimp [r]; linarith only [hlβ],?_⟩
    simpa only [mul_comm] using (div_lt_iff₀ hden).mp hrl
  have hrc : Continuous r := (hpc.add continuous_const).div_const (1-a) |>.add hβc |>.div_const 2
  have hΔc : Continuous (fun α => β α-r α) := hβc.sub hrc
  obtain ⟨αδ,hαδ,hδmin⟩ := hK.exists_isMinOn hn hΔc.continuousOn
  let δ := β αδ-r αδ
  have hδ : 0 < δ := sub_pos.mpr (hr αδ hαδ).2.1
  have hδle (α : ℝ) (hαk : α ∈ K) : δ ≤ β α-r α := hδmin hαk
  obtain ⟨αM,hαM,hMmax⟩ := hK.exists_isMaxOn hn hrc.continuousOn
  let M := r αM
  have hM : 0 < M := (hr αM hαM).1
  have hrM (α : ℝ) (hαk : α ∈ K) : r α ≤ M := hMmax hαk
  let qH := 1+δ/(4*(M+1))
  have hqH : 1 < qH := lt_add_of_pos_right 1 (div_pos hδ (by positivity))
  let pH := Real.conjExponent qH
  have hpq : pH.HolderConjugate qH := (Real.HolderConjugate.conjExponent hqH).symm
  let g := δ/4
  let R := 4/γ^2-δ/2
  have hrR (α : ℝ) (hαk : α ∈ K) : r α ≤ R := by
    have hβbulk : β α ≤ 4/γ^2 := min_le_right _ _
    have hΔ := hδle α hαk
    dsimp [R]
    linarith only [hβbulk,hΔ,hδ]
  refine ⟨a,r,R,g,pH,qH,hηa,ha1,(hr α₀ hα₀).1.trans_le (hrR α₀ hα₀),
    by dsimp [R]; linarith only [hδ],by dsimp [g]; positivity,hpq,?_⟩
  intro α hαk
  refine ⟨(hr α hαk).1,hrR α hαk,(hr α hαk).2.2,?_⟩
  have hsmall : r α*(δ/(4*(M+1))) ≤ δ/4 := by
    have hd : 0 < 4*(M+1) := by positivity
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).mpr
    have he : (δ/4)*(4*(M+1)) = δ*(M+1) := by ring
    rw [he]
    have hb := mul_le_mul_of_nonneg_right (hrM α hαk) hδ.le
    nlinarith only [hb,hδ]
  have hΔ := hδle α hαk
  change r α*(1+δ/(4*(M+1)))+δ/4 ≤ β α
  rw [mul_add,mul_one]
  linarith only [hsmall,hΔ,hδ]


end DOZZ.Proofs
