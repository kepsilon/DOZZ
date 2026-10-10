/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.WilliamsENNRealModelTail
public import DOZZ.Correlations.Tails.PrefactoredSourceWilliamsLaw
public import DOZZ.Correlations.Tails.PrefactoredReflectionUniform
public import DOZZ.Correlations.Tails.PrefactorMomentGap
public import DOZZ.Correlations.Tails.ActualPrefactorCriticalMoment
public import DOZZ.Correlations.Tails.SourceCutOrdering
public import DOZZ.Brownian.Reflection.MomentAssembly

/-! Uniform leading Williams tails on the original source reflection family. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

theorem source_williams_tail_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (Kz : Set ℂ) (hKz : IsCompact Kz) (hz : ∀ z ∈ Kz, 2 ≤ ‖z‖)
    (Kα : Set ℝ) (hKα : IsCompact Kα) (hα : ∀ α ∈ Kα, γ/2 < α ∧ α < Q γ)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hZ : IsLateralGMCOf P γ Z) (hData : ∀ α ∈ Kα, IsReflectionData P γ α (B α) Z)
    (b R η a : ℝ) (hb : 0 ≤ b) (hR : 0 < R) (hRbulk : R < 4/γ^2)
    (hη : 0 < η) (ha : η < a) (r : ℝ → ℝ)
    (hr : ∀ α ∈ Kα, 0 < r α ∧ r α ≤ R)
    (hpr : ∀ α ∈ Kα, reflectionExponent γ α+η < (1-a)*r α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Kz, ∀ α ∈ Kα, ∀ f : ℝ, 0 < f → f ≤ b →
      ∀ x : ℝ, 1 ≤ x →
      |(((brownianMaximumReferenceLaw (Q γ-α)).prod (P.prod P))
        {q | ENNReal.ofReal x <
          (ENNReal.ofReal (f*‖z‖^(-4 : ℝ)*Real.exp (γ*Xc q.2.2 z 0-γ^2*Real.log ‖z‖))*
            twoSidedReflectionCutMass γ q.1 (B α) Z q.2.1)*
              ENNReal.ofReal (Real.exp (γ*q.1))}).toReal -
          oneInsertionTailCoefficient γ α z f (reflectionBarR P γ α (B α) Z)*
            x^(-reflectionExponent γ α)| ≤ C*x^(-reflectionExponent γ α-η) := by
  let : IsProbabilityMeasure P := hX.1
  rcases Kα.eq_empty_or_nonempty with he | hn
  · refine ⟨0,le_rfl,?_⟩
    intro z hzk α hαk
    simp only [he,mem_empty_iff_false] at hαk
  obtain ⟨αlo,hαlo,hlo⟩ := hKα.exists_isMinOn hn continuous_id.continuousOn
  obtain ⟨αhi,hαhi,hhi⟩ := hKα.exists_isMaxOn hn continuous_id.continuousOn
  let ν₁ := Q γ-αhi
  let ν₂ := Q γ-αlo
  have hν₁ : 0 < ν₁ := sub_pos.mpr (hα αhi hαhi).2
  have hνrange (α : ℝ) (hαk : α ∈ Kα) : ν₁ ≤ Q γ-α ∧ Q γ-α ≤ ν₂ := by
    have h1 := hlo hαk
    have h2 := hhi hαk
    change αlo ≤ α at h1
    change α ≤ αhi at h2
    constructor <;> dsimp [ν₁,ν₂] <;> linarith only [h1,h2]
  let Kν := (fun α => Q γ-α) '' Kα
  let Kp := (fun α => reflectionExponent γ α) '' Kα
  have hKν : IsCompact Kν := hKα.image (continuous_const.sub continuous_id)
  have hKp : IsCompact Kp := hKα.image (by unfold reflectionExponent; fun_prop)
  let Bs := fun ν => B (Q γ-ν)
  have hBs (ν : ℝ) (hνk : ν ∈ Kν) :
      0 < ν ∧ IsTwoSidedConditionedBrownianProcess P (Bs ν) ν := by
    rcases hνk with ⟨α,hαk,rfl⟩
    refine ⟨sub_pos.mpr (hα α hαk).2,?_⟩
    simpa only [Bs,sub_sub_cancel] using (hData α hαk).1
  have hInd (ν : ℝ) (hνk : ν ∈ Kν) : IndepFun (Bs ν) Z P := by
    rcases hνk with ⟨α,hαk,rfl⟩
    simpa only [Bs,sub_sub_cancel] using (hData α hαk).2.2
  have hpK (p : ℝ) (hpk : p ∈ Kp) : 0 < p ∧ p < 4/γ^2 := by
    rcases hpk with ⟨α,hαk,rfl⟩
    exact residue_critical_order_bounds γ α hγ (hα α hαk).1 (hα α hαk).2
  obtain ⟨D,hD,hgap⟩ := reflectionMass_lastCut_bound P γ hγ hγ2 Kν Kp hKν hKp Bs hBs Z hZ hInd hpK
  obtain ⟨L,hL,hPin⟩ := actual_prefactor_moment_uniform P X Xc hX hc Kz hKz hz γ b R hb hR
  obtain ⟨T,hT,hMass⟩ := prefactored_reflection_moment_uniform P X Xc hX hc
    Kz hKz hz γ b R ν₁ ν₂ hγ hb hR hRbulk hν₁ Z hZ
  let C := L.toReal*D+3*T.toReal
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro z hzk α hαk f hf hfb x hx
  let p := reflectionExponent γ α
  let ν := Q γ-α
  have hν : 0 < ν := sub_pos.mpr (hα α hαk).2
  have hp : 0 < p := (hpK p ⟨α,hαk,rfl⟩).1
  have hrα := (hr α hαk).1
  have hpR : p ≤ R := by
    have ha0 := hη.trans ha
    have hprα := hpr α hαk
    have hrR := (hr α hαk).2
    nlinarith only [hprα,ha0,hη,hrα,hrR]
  let S := fun ω => ENNReal.ofReal (f*‖z‖^(-4 : ℝ)*
    Real.exp (γ*Xc ω z 0-γ^2*Real.log ‖z‖))
  have hpin : Measurable (fun ω => Xc ω z 0) :=
    (hc.1 0).comp (measurable_id.prodMk measurable_const)
  have hS : Measurable S := (((hpin.const_mul γ).sub_const _).exp.const_mul _).ennreal_ofReal
  let J₀ := fun ω => twoSidedReflectionMass γ (B α) Z ω
  let Jc₀ := fun c ω => twoSidedReflectionCutMass γ c (B α) Z ω
  let J := fun q : Ω × Ω => S q.2*J₀ q.1
  let Jc := fun c (q : Ω × Ω) => S q.2*Jc₀ c q.1
  let A := fun q : ℝ × (Ω × Ω) => Jc q.1 q.2
  have hB := aemeasurable_of_twoSidedConditioned (hData α hαk).1
  have hJ₀ : AEMeasurable J₀ P := twoSidedReflectionMass_aemeasurable_of_lateral P γ (B α) Z hB hZ
  have hJc₀ (c : ℝ) : AEMeasurable (Jc₀ c) P :=
    twoSidedReflectionCutMass_aemeasurable P γ c (B α) Z hB hZ.2.2.2.1 hZ.2.2.2.2.1
  have hJ : AEMeasurable J (P.prod P) :=
    (hS.aemeasurable.comp_quasiMeasurePreserving measurePreserving_snd.quasiMeasurePreserving).mul
      (hJ₀.comp_quasiMeasurePreserving measurePreserving_fst.quasiMeasurePreserving)
  have hJc (c : ℝ) : AEMeasurable (Jc c) (P.prod P) :=
    (hS.aemeasurable.comp_quasiMeasurePreserving measurePreserving_snd.quasiMeasurePreserving).mul
      ((hJc₀ c).comp_quasiMeasurePreserving measurePreserving_fst.quasiMeasurePreserving)
  have hJcle (c : ℝ) (q : Ω × Ω) : Jc c q ≤ J q :=
    mul_le_mul' le_rfl (twoSidedReflectionCutMass_le_mass γ c (B α) Z q.1)
  have hMom (s : ℝ) (hs : 0 < s) (hsR : s ≤ R) : (∫⁻ q, J q^s ∂P.prod P) ≤ T :=
    hMass z hzk f hf.le hfb ν (hνrange α hαk).1 (hνrange α hαk).2 s hs hsR
      (B α) (hData α hαk).1 (hData α hαk).2.2
  have hJp : (∫⁻ q, J q^p ∂P.prod P) < ⊤ := (hMom p hp hpR).trans_lt hT
  have hJr : (∫⁻ q, J q^(r α) ∂P.prod P) < ⊤ := (hMom _ hrα (hr α hαk).2).trans_lt hT
  have hupper : ∀ᵐ q ∂(brownianMaximumReferenceLaw ν).prod (P.prod P), A q ≤ J q.2 :=
    ae_of_all _ fun q => hJcle q.1 q.2
  have hD₀ := (hData α hαk).1.2.1
  have hDL : HasLaw (fun ω => (B α ω).2) (P.map (fun ω => (B α ω).2)) P := ⟨hD₀.1,rfl⟩
  have hDL' := hDL.comp (measurePreserving_fst (μ := P) (ν := P)).hasLaw
  have hD' : IsNegativeConditionedBrownianProcess (P.prod P) (fun q => (B α q.1).2) ν :=
    ⟨hDL'.aemeasurable,by
      change IsNegativeConditionedBrownianLaw ν
        ((P.prod P).map ((fun ω => (B α ω).2) ∘ Prod.fst))
      rw [hDL'.map_eq]
      exact hD₀.2⟩
  have hlower (c : ℝ) (_hc : 0 ≤ c) :
      ∀ᵐ q ∂(brownianMaximumReferenceLaw ν).prod (P.prod P), c ≤ q.1 → Jc c q.2 ≤ A q := by
    filter_upwards [source_last_exit_mono_prod_ae (P.prod P) ν c hν _ hD'] with q hq
    intro hcq
    exact mul_le_mul' le_rfl (reflection_cut_mass_le_of_last_exit_le γ c q.1
      (B α) Z q.2.1 (hq hcq))
  have hGap (c : ℝ) (hc0 : 0 ≤ c) :
      (∫⁻ q, J q^p ∂P.prod P).toReal-(∫⁻ q, Jc c q^p ∂P.prod P).toReal ≤
        (L.toReal*D)*Real.exp (-γ*c) := by
    have hSbound := ENNReal.toReal_mono hL.ne (hPin z hzk f hf.le hfb p hp hpR)
    have hG := (hgap ν ⟨α,hαk,rfl⟩ p ⟨α,hαk,rfl⟩ c hc0).2
    simp only [Bs,ν,sub_sub_cancel] at hG
    exact independent_prefactor_moment_gap P P J₀ (Jc₀ c) S hJ₀ (hJc₀ c)
      hS.aemeasurable p L.toReal D γ c hp.le hD hSbound hG
  have hmodel := williams_ennreal_model_tail_bound (P.prod P) A J Jc hJ hJc hJcle
    ν γ η a (r α) (L.toReal*D) T.toReal hν hγ hη ha hrα (hpr α hαk)
    (mul_nonneg ENNReal.toReal_nonneg hD) ENNReal.toReal_nonneg hJp hJr
    (ENNReal.toReal_mono hT.ne (hMom _ hrα (hr α hαk).2)) hupper hlower hGap x hx
  have hCoefficient : (∫⁻ q, J q^p ∂P.prod P).toReal =
      oneInsertionTailCoefficient γ α z f (reflectionBarR P γ α (B α) Z) := by
    have hprod : (∫⁻ q, J q^p ∂P.prod P) =
        (∫⁻ ω, J₀ ω^p ∂P)*(∫⁻ ω, S ω^p ∂P) := by
      simp_rw [J,ENNReal.mul_rpow_of_nonneg _ _ hp.le,mul_comm (S _^p)]
      exact lintegral_prod_mul (hJ₀.pow_const p) (hS.aemeasurable.pow_const p)
    rw [hprod,ENNReal.toReal_mul,actual_prefactor_critical_moment P X Xc hX hc z
      (hz z hzk) γ α f hγ.ne' hf]
    change (reflectionBarR P γ α (B α) Z)*(‖z‖^(-4*α*(Q γ-α))*f^p) = _
    unfold oneInsertionTailCoefficient
    simp only [Real.rpow_eq_pow]
    dsimp only [p]
    ring
  change |(((brownianMaximumReferenceLaw ν).prod (P.prod P))
    {q | ENNReal.ofReal x < A q*ENNReal.ofReal (Real.exp (γ*q.1))}).toReal-
    x^(-p)*(∫⁻ q, J q^p ∂P.prod P).toReal| ≤ (L.toReal*D+3*T.toReal)*x^(-p-η) at hmodel
  rw [hCoefficient] at hmodel
  rw [mul_comm (x^(-p))] at hmodel
  simpa only [A,Jc,Jc₀,S,p,ν,C] using hmodel


end DOZZ.Proofs
