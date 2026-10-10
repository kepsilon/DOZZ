/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.WilliamsModelTail
public import DOZZ.Correlations.Tails.ENNRealMomentVersion

/-! Apply the scalar Williams estimate to actual extended-real chaos masses. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DOZZ.Proofs

theorem williams_ennreal_model_tail_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℝ × Ω → ℝ≥0∞) (J : Ω → ℝ≥0∞) (Jc : ℝ → Ω → ℝ≥0∞)
    (hJ : AEMeasurable J P) (hJcm : ∀ c, AEMeasurable (Jc c) P)
    (hJcle : ∀ c ω, Jc c ω ≤ J ω)
    (ν γ η a r D K : ℝ) (hν : 0 < ν) (hγ : 0 < γ)
    (hη : 0 < η) (ha : η < a) (hr : 0 < r)
    (hpr : 2*ν/γ+η < (1-a)*r) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hJp : (∫⁻ ω, J ω^(2*ν/γ) ∂P) < ⊤)
    (hJr : (∫⁻ ω, J ω^r ∂P) < ⊤)
    (hJrK : (∫⁻ ω, J ω^r ∂P).toReal ≤ K)
    (hupper : ∀ᵐ q ∂(brownianMaximumReferenceLaw ν).prod P, A q ≤ J q.2)
    (hlower : ∀ c : ℝ, 0 ≤ c →
      ∀ᵐ q ∂(brownianMaximumReferenceLaw ν).prod P, c ≤ q.1 → Jc c q.2 ≤ A q)
    (hgap : ∀ c : ℝ, 0 ≤ c → (∫⁻ ω, J ω^(2*ν/γ) ∂P).toReal-
      (∫⁻ ω, Jc c ω^(2*ν/γ) ∂P).toReal ≤ D*Real.exp (-γ*c)) :
    ∀ x : ℝ, 1 ≤ x →
      |(((brownianMaximumReferenceLaw ν).prod P)
          {q | ENNReal.ofReal x < A q*ENNReal.ofReal (Real.exp (γ*q.1))}).toReal-
        x^(-(2*ν/γ))*(∫⁻ ω, J ω^(2*ν/γ) ∂P).toReal| ≤
          (D+3*K)*x^(-(2*ν/γ)-η) := by
  let μ := brownianMaximumReferenceLaw ν
  let : IsProbabilityMeasure μ := isProbabilityMeasure_brownianMaximumReferenceLaw hν
  have hp : 0 < 2*ν/γ := by positivity
  have hJf : ∀ᵐ ω ∂P, J ω ≠ ⊤ := by
    have hf := ae_lt_top' (hJ.pow_const r) hJr.ne
    filter_upwards [hf] with ω hω
    intro ht
    rw [ht,ENNReal.top_rpow_of_pos hr] at hω
    exact lt_irrefl _ hω
  obtain ⟨f,hfm,hf0,hfe,hfMom⟩ := nonnegative_moment_version P J hJ hJf
  have hJcf (c : ℝ) : ∀ᵐ ω ∂P, Jc c ω ≠ ⊤ :=
    hJf.mono fun ω hω => ne_top_of_le_ne_top hω (hJcle c ω)
  choose fc hfcm hfc0 hfce hfcMom using
    fun c : ℝ => nonnegative_moment_version P (Jc c) (hJcm c) (hJcf c)
  have hJcMom (c s : ℝ) (hs : 0 ≤ s) :
      (∫⁻ ω, Jc c ω^s ∂P) ≤ ∫⁻ ω, J ω^s ∂P :=
    lintegral_mono fun ω => ENNReal.rpow_le_rpow (hJcle c ω) hs
  have hJcp (c : ℝ) : (∫⁻ ω, Jc c ω^(2*ν/γ) ∂P) < ⊤ :=
    (hJcMom c _ hp.le).trans_lt hJp
  have hJcr (c : ℝ) : (∫⁻ ω, Jc c ω^r ∂P) < ⊤ :=
    (hJcMom c r hr.le).trans_lt hJr
  have hfp := hfMom _ hp.le hJp
  have hfr := hfMom r hr.le hJr
  have hAfinite : ∀ᵐ q ∂μ.prod P, A q ≠ ⊤ := by
    have hj := (measurePreserving_snd (μ := μ) (ν := P)).quasiMeasurePreserving.ae hJf
    filter_upwards [hupper,hj] with q hq hjq
    exact ne_top_of_le_ne_top hjq hq
  have hupper' : ∀ᵐ q ∂μ.prod P, (A q).toReal ≤ f q.2 := by
    have hj := (measurePreserving_snd (μ := μ) (ν := P)).quasiMeasurePreserving.ae hJf
    have he := (measurePreserving_snd (μ := μ) (ν := P)).quasiMeasurePreserving.ae hfe
    filter_upwards [hupper,hj,he] with q hq hjq heq
    rw [heq]
    exact ENNReal.toReal_mono hjq hq
  have hlower' (c : ℝ) (hc : 0 ≤ c) :
      ∀ᵐ q ∂μ.prod P, c ≤ q.1 → fc c q.2 ≤ (A q).toReal := by
    have he := (measurePreserving_snd (μ := μ) (ν := P)).quasiMeasurePreserving.ae (hfce c)
    filter_upwards [hlower c hc,hAfinite,he] with q hq hAf heq
    intro hlevel
    rw [heq]
    exact ENNReal.toReal_mono hAf (hq hlevel)
  have hfcK (c : ℝ) : (∫ ω, fc c ω^r ∂P) ≤ K := by
    rw [(hfcMom c r hr.le (hJcr c)).2]
    exact (ENNReal.toReal_mono hJr.ne (hJcMom c r hr.le)).trans hJrK
  have hfgap (c : ℝ) (hc : 0 ≤ c) :
      (∫ ω, f ω^(2*ν/γ) ∂P)-(∫ ω, fc c ω^(2*ν/γ) ∂P) ≤ D*Real.exp (-γ*c) := by
    rw [hfp.2,(hfcMom c _ hp.le (hJcp c)).2]
    exact hgap c hc
  have hmodel := williams_model_tail_bound P (fun q => (A q).toReal) f fc hfm hf0
    ν γ η a r D K hν hγ hη ha hr hpr hD hK hfp.1 hfr.1
    (by rw [hfr.2]; exact hJrK) (fun c _ => hfcm c) (fun c _ => hfc0 c)
    (fun c _ => (hfcMom c _ hp.le (hJcp c)).1)
    (fun c _ => (hfcMom c r hr.le (hJcr c)).1) (fun c _ => hfcK c)
    hupper' hlower' hfgap
  intro x hx
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hevent : {q : ℝ × Ω | ENNReal.ofReal x < A q*ENNReal.ofReal (Real.exp (γ*q.1))}
      =ᵐ[μ.prod P] {q | x < (A q).toReal*Real.exp (γ*q.1)} := by
    filter_upwards [hAfinite] with q hq
    apply propext
    rw [← ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top
      (ENNReal.mul_lt_top hq.lt_top ENNReal.ofReal_lt_top).ne,
      ENNReal.toReal_ofReal hx0,ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  rw [measure_congr hevent]
  rw [← hfp.2]
  exact hmodel x hx


end DOZZ.Proofs
