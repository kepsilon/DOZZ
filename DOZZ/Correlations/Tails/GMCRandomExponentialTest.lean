/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.ExponentialParameterTest
public import DOZZ.Correlations.Tails.CorrelatedMassEnvelope
public import DOZZ.GMC.Assembly.AdmissibleGMC
public import DOZZ.GMC.Construction.FiniteMeasureTotalize

/-! Actual GMC cutoff convergence for compact exponential tests with a correlated pin. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The actual integer-cutoff GMC converges against a compact exponential test whose
parameter can depend on the same field. Exponential moments of the parameter, combined
with the cutoff moments, give the mixed approximation estimate. -/
theorem gmc_correlated_exponential_test_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (f c : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ))
    (θ : Ω → ℝ) (hθ : Measurable θ)
    (hθexp : ∀ l : ℝ, (∫⁻ ω, ENNReal.ofReal (Real.exp (l*|θ ω|)) ∂P) < ⊤) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => ∫ x, f x * Real.exp (c x * θ ω) ∂regularizedGMC P Xc γ n ω)
      atTop (fun ω => ∫ x, f x * Real.exp (c x * θ ω) ∂M ω) := by
  let : IsProbabilityMeasure P := hX.1
  have hcrit : 1 < 4 / γ^2 := (lt_div_iff₀ (by positivity)).mpr (by nlinarith)
  obtain ⟨q, hq1, hqc⟩ := exists_between hcrit
  let p := Real.conjExponent q
  have hpq : p.HolderConjugate q := (Real.HolderConjugate.conjExponent hq1).symm
  have hp : 0 < p := hpq.pos
  let Lcoef : ℝ → ℝ := fun t => ‖f‖ * ‖c‖ * Real.exp (‖c‖ * (|t|+1))
  let E : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Lcoef (θ ω))
  have hE : Measurable E :=
    (((continuous_abs.measurable.comp hθ).add_const 1).const_mul ‖c‖).exp.const_mul (‖f‖ * ‖c‖) |>.ennreal_ofReal
  have hEp : (∫⁻ ω, E ω ^ p ∂P) < ⊤ := by
    let B : ℝ := ‖f‖ * ‖c‖ * Real.exp ‖c‖
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have heq (ω : Ω) : E ω ^ p = ENNReal.ofReal B ^ p *
        ENNReal.ofReal (Real.exp ((p*‖c‖)*|θ ω|)) := by
      have hfactor : Lcoef (θ ω) = B * Real.exp (‖c‖ * |θ ω|) := by
        dsimp [Lcoef, B]
        rw [mul_add, mul_one, Real.exp_add]
        ring
      change ENNReal.ofReal (Lcoef (θ ω)) ^ p = _
      rw [hfactor, ENNReal.ofReal_mul hB,
        ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
        ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
      congr 2
      ring_nf
    simp_rw [heq]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_lt_top_of_nonneg hp.le ENNReal.ofReal_ne_top).ne]
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hp.le ENNReal.ofReal_ne_top)
      (hθexp (p*‖c‖))
  obtain ⟨R, hRs⟩ : ∃ R : ℝ, tsupport (f : ℂ → ℝ) ⊆ Metric.closedBall (0 : ℂ) R :=
    hfc.isBounded.subset_closedBall 0
  let R' := max R 0
  have hR' : 0 ≤ R' := le_max_right _ _
  let K := Metric.closedBall (0 : ℂ) R'
  have hK : IsCompact K := isCompact_closedBall _ _
  have hFK (t : ℝ) : tsupport (exponentialParameterTest f c t : ℂ → ℝ) ⊆ K :=
    (exponential_parameter_test_support f c t).trans
      (hRs.trans (Metric.closedBall_subset_closedBall (le_max_left _ _)))
  obtain ⟨C, hC, hcut, hlim⟩ := regularized_mass_envelope_uniform
    P X hX Xc hc γ R' hγ hγ2 hR' M hM E hE.aemeasurable p q hpq hqc hEp
  obtain ⟨M', hM'm, hM'f, hM'e⟩ := equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  have hversions (n : ℕ) := exists_everywhere_finite_measure_version P
    (regularizedGMC P Xc γ n) (regularizedGMC_measurable P X hX Xc hc γ n)
      (regularizedGMC_finite_ae P X hX Xc hc γ n)
  choose N hNm hNf hNe using hversions
  have hNmK (n : ℕ) (ω : Ω) : N n ω K < ⊤ := by
    let : IsFiniteMeasure (N n ω) := hNf n ω
    exact measure_lt_top _ _
  have hM'mK (ω : Ω) : M' ω K < ⊤ := by
    let : IsFiniteMeasure (M' ω) := hM'f ω
    exact measure_lt_top _ _
  have hconv (t : ℝ) : TendstoInMeasure P
      (fun n ω => ∫ x, exponentialParameterTest f c t x ∂N n ω)
      atTop (fun ω => ∫ x, exponentialParameterTest f c t x ∂M' ω) := by
    have h := (DOZZ.Assembly.isGMCOf_tendstoInMeasure P X hX Xc hc γ M hM
      (exponentialParameterTest f c t)).comp tendsto_natCast_atTop_atTop
    have hleft (n : ℕ) : (fun ω => ∫ x, exponentialParameterTest f c t x
        ∂regularizedGMC P Xc γ n ω) =ᵐ[P]
        fun ω => ∫ x, exponentialParameterTest f c t x ∂N n ω := by
      filter_upwards [hNe n] with ω hω
      rw [hω]
    have hright : (fun ω => ∫ x, exponentialParameterTest f c t x ∂M ω) =ᵐ[P]
        fun ω => ∫ x, exponentialParameterTest f c t x ∂M' ω := by
      filter_upwards [hM'e] with ω hω
      rw [hω]
    exact (h.congr_left hleft).congr_right hright
  have hcut' (n : ℕ) : (∫⁻ ω, ENNReal.ofReal (Lcoef (θ ω)) * N n ω K ∂P) ≤ C := by
    have heq : (fun ω => ENNReal.ofReal (Lcoef (θ ω)) * N n ω K) =ᵐ[P]
        fun ω => E ω * regularizedGMC P Xc γ n ω K := by
      filter_upwards [hNe n] with ω hω
      rw [hω]
    rw [lintegral_congr_ae heq]
    exact hcut n
  have hlim' : (∫⁻ ω, ENNReal.ofReal (Lcoef (θ ω)) * M' ω K ∂P) ≤ C := by
    have heq : (fun ω => ENNReal.ofReal (Lcoef (θ ω)) * M' ω K) =ᵐ[P]
        fun ω => E ω * M ω K := by
      filter_upwards [hM'e] with ω hω
      rw [hω]
    rw [lintegral_congr_ae heq]
    exact hlim
  have h := tendstoInMeasure_parameter_integral P N M' hNm hM'm K hK hNmK hM'mK
    (exponentialParameterTest f c) (exponential_parameter_test_measurable f c)
      hFK θ hθ hconv Lcoef (fun t => by dsimp [Lcoef]; positivity)
        (fun t u htu x _ => exponential_parameter_test_lipschitz f c t u htu x)
          C hC.ne hcut' hlim'
  have hleft (n : ℕ) : (fun ω => ∫ x, exponentialParameterTest f c (θ ω) x ∂N n ω) =ᵐ[P]
      fun ω => ∫ x, f x * Real.exp (c x * θ ω) ∂regularizedGMC P Xc γ n ω := by
    filter_upwards [hNe n] with ω hω
    rw [hω]
    rfl
  have hright : (fun ω => ∫ x, exponentialParameterTest f c (θ ω) x ∂M' ω) =ᵐ[P]
      fun ω => ∫ x, f x * Real.exp (c x * θ ω) ∂M ω := by
    filter_upwards [hM'e] with ω hω
    rw [hω]
    rfl
  exact (h.congr_left hleft).congr_right hright


end DOZZ.Proofs
