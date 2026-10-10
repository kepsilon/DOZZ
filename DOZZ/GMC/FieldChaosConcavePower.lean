/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FieldChaosNegativePower
public import DOZZ.GMC.FiniteChaosResolvent
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation

/-! Positive subunit Kahane comparison for continuum field chaos. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Kahane's comparison for concave powers `0 < p < 1` of continuum field chaos. -/
theorem kahane_field_power_concave
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [MeasurableSpace S]
    (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField PX Φ) (hΨ : DOZZ.IsCenteredGaussianField PY Ψ)
    (ν : Measure S) [IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ p : ℝ) (hp : 0 < p ∧ p < 1)
    (hcov : ∀ᵐ q ∂ν.prod ν,
      ∫ ω, Φ ω q.1 * Φ ω q.2 ∂PX ≤ ∫ ω, Ψ ω q.1 * Ψ ω q.2 ∂PY)
    (hdiag : ∀ᵐ x ∂ν,
      ∫ ω, Φ ω x ^ 2 ∂PX ≤ ∫ ω, Ψ ω x ^ 2 ∂PY) :
    ∫⁻ ω, DOZZ.fieldChaosMass PX Φ ν h γ ω ^ p ∂PX ≥
      ∫⁻ ω, DOZZ.fieldChaosMass PY Ψ ν h γ ω ^ p ∂PY := by
  classical
  have hPXzero := hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)
  have hPYzero := hΨ.2 0 (fun i : Fin 0 => Fin.elim0 i)
  let : IsProbabilityMeasure PX := hPXzero.1
  let : IsProbabilityMeasure PY := hPYzero.1
  by_cases hνzero : ν = 0
  · have hmassX (ω : ΩX) : DOZZ.fieldChaosMass PX Φ ν h γ ω = 0 := by
      simp [DOZZ.fieldChaosMass, hνzero]
    have hmassY (ω : ΩY) : DOZZ.fieldChaosMass PY Ψ ν h γ ω = 0 := by
      simp [DOZZ.fieldChaosMass, hνzero]
    simp [hmassX, hmassY, ENNReal.zero_rpow_of_pos hp.1,
      hPXzero.1.measure_univ, hPYzero.1.measure_univ]
  let νf : FiniteMeasure S := ⟨ν, inferInstance⟩
  have hνf : νf ≠ 0 := by
    intro hzero
    apply hνzero
    have hcoerce := congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) hzero
    simpa [νf] using hcoerce
  have hS : Nonempty S := by
    have hUniv : ν Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hνzero
    obtain ⟨x, _⟩ := nonempty_of_measure_ne_zero hUniv
    exact ⟨x⟩
  let : Nonempty S := hS
  let ρ : Measure S := νf.normalize
  have hρprob : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  let : IsProbabilityMeasure ρ := hρprob
  let α : ℝ := ∫ x, (h x : ℝ) ∂ρ
  have hαnonneg : 0 ≤ α := by
    dsimp [α]
    exact integral_nonneg_of_ae (ae_of_all _ fun x => NNReal.coe_nonneg (h x))
  by_cases hαzero : α = 0
  · have hmassX := centeredGaussianField_fieldChaosMass_eq_zero_of_zero_weight_integral
      PX Φ νf h hh hhb γ (by simpa [α, ρ] using hαzero)
    have hmassY := centeredGaussianField_fieldChaosMass_eq_zero_of_zero_weight_integral
      PY Ψ νf h hh hhb γ (by simpa [α, ρ] using hαzero)
    simp [show ν = (νf : Measure S) by rfl, hmassX, hmassY,
      ENNReal.zero_rpow_of_pos hp.1, hPXzero.1.measure_univ,
      hPYzero.1.measure_univ]
  have hαpos : 0 < α := lt_of_le_of_ne hαnonneg (Ne.symm hαzero)
  have hcov' : ∀ᵐ xy ∂(νf : Measure S).prod νf,
      DOZZ.gaussianCovariance PX (fun ω => Φ ω xy.1) (fun ω => Φ ω xy.2) ≤
        DOZZ.gaussianCovariance PY (fun ω => Ψ ω xy.1) (fun ω => Ψ ω xy.2) := by
    filter_upwards [hcov] with xy hxy
    simpa [DOZZ.gaussianCovariance] using hxy
  have hdiag' : ∀ᵐ x ∂(νf : Measure S),
      DOZZ.gaussianVariance PX (fun ω => Φ ω x) ≤
        DOZZ.gaussianVariance PY (fun ω => Ψ ω x) := by
    filter_upwards [hdiag] with x hx
    simpa [DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two] using hx
  let MX : ΩX → ℝ≥0∞ := fun ω => DOZZ.fieldChaosMass PX Φ ν h γ ω
  let MY : ΩY → ℝ≥0∞ := fun ω => DOZZ.fieldChaosMass PY Ψ ν h γ ω
  let mX : ΩX → ℝ := fun ω => if (MX ω).toReal = 0 then 1 else (MX ω).toReal
  let mY : ΩY → ℝ := fun ω => if (MY ω).toReal = 0 then 1 else (MY ω).toReal
  have hmassMeasX := centeredGaussianField_fieldChaosMass_measurable PX Φ hΦ ν h hh γ
  have hmassMeasY := centeredGaussianField_fieldChaosMass_measurable PY Ψ hΨ ν h hh γ
  have hmXMeas : Measurable mX := by
    apply Measurable.ite
      (measurableSet_eq_fun hmassMeasX.ennreal_toReal measurable_const)
    · exact measurable_const
    · exact hmassMeasX.ennreal_toReal
  have hmYMeas : Measurable mY := by
    apply Measurable.ite
      (measurableSet_eq_fun hmassMeasY.ennreal_toReal measurable_const)
    · exact measurable_const
    · exact hmassMeasY.ennreal_toReal
  have hmX : ∀ ω, 0 < mX ω := by
    intro ω
    dsimp [mX]
    split_ifs with hz
    · norm_num
    · exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz)
  have hmY : ∀ ω, 0 < mY ω := by
    intro ω
    dsimp [mY]
    split_ifs with hz
    · norm_num
    · exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz)
  have hmX0 : ∀ ω, 0 ≤ mX ω := fun ω => (hmX ω).le
  have hmY0 : ∀ ω, 0 ≤ mY ω := fun ω => (hmY ω).le
  have hmassEqX : ∀ᵐ ω ∂PX, MX ω = ENNReal.ofReal (mX ω) := by
    change ∀ᵐ ω ∂PX,
      DOZZ.fieldChaosMass PX Φ ν h γ ω = ENNReal.ofReal
        (if (DOZZ.fieldChaosMass PX Φ ν h γ ω).toReal = 0 then 1 else
          (DOZZ.fieldChaosMass PX Φ ν h γ ω).toReal)
    exact fieldChaosMass_eq_ofReal_modified_toReal_ae
      PX Φ hΦ νf hνf h hh hhb γ (by simpa [ρ, α] using hαpos)
  have hmassEqY : ∀ᵐ ω ∂PY, MY ω = ENNReal.ofReal (mY ω) := by
    change ∀ᵐ ω ∂PY,
      DOZZ.fieldChaosMass PY Ψ ν h γ ω = ENNReal.ofReal
        (if (DOZZ.fieldChaosMass PY Ψ ν h γ ω).toReal = 0 then 1 else
          (DOZZ.fieldChaosMass PY Ψ ν h γ ω).toReal)
    exact fieldChaosMass_eq_ofReal_modified_toReal_ae
      PY Ψ hΨ νf hνf h hh hhb γ (by simpa [ρ, α] using hαpos)
  have htoRealEqX : ∀ᵐ ω ∂PX, (MX ω).toReal = mX ω := by
    filter_upwards [hmassEqX] with ω hω
    rw [hω, ENNReal.toReal_ofReal (le_of_lt (hmX ω))]
  have htoRealEqY : ∀ᵐ ω ∂PY, (MY ω).toReal = mY ω := by
    filter_upwards [hmassEqY] with ω hω
    rw [hω, ENNReal.toReal_ofReal (le_of_lt (hmY ω))]
  have hLap (s : ℝ) (hs : 0 ≤ s) :
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-(s * mX ω))) ∂PX ≤
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-(s * mY ω))) ∂PY := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (-(s * (MX ω).toReal))) ∂PX := by
        apply lintegral_congr_ae
        filter_upwards [htoRealEqX] with ω hω
        rw [hω]
      _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (-(s * (MY ω).toReal))) ∂PY := by
        simpa [νf, MX, MY] using
          kahane_field_laplace_of_nonzero_finite_measure_eq
            PX PY Φ Ψ hΦ hΨ νf hνf h hh hhb γ s hs hcov' hdiag'
      _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (-(s * mY ω))) ∂PY := by
        apply lintegral_congr_ae
        filter_upwards [htoRealEqY] with ω hω
        rw [hω]
  let c : ℝ := (∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t 1 ∂volume)⁻¹
  have hcpos : 0 < c := by
    dsimp [c]
    exact inv_pos.mpr (Real.integral_rpowIntegrand₀₁_one_pos ⟨hp.1, hp.2⟩)
  let νt : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let fX : ΩX → ℝ → ℝ≥0∞ := fun ω t =>
    ENNReal.ofReal (Real.rpowIntegrand₀₁ p t (mX ω))
  let fY : ΩY → ℝ → ℝ≥0∞ := fun ω t =>
    ENNReal.ofReal (Real.rpowIntegrand₀₁ p t (mY ω))
  have hfX : AEMeasurable (Function.uncurry fX) (PX.prod νt) := by
    have hkernel : Measurable (fun z : ℝ × ℝ =>
        Real.rpowIntegrand₀₁ p z.1 z.2) := by
      unfold Real.rpowIntegrand₀₁
      fun_prop
    have hpair : AEMeasurable (fun z : ΩX × ℝ => (z.2, mX z.1)) (PX.prod νt) :=
      measurable_snd.aemeasurable.prodMk hmXMeas.aemeasurable.comp_fst
    exact (hkernel.comp_aemeasurable hpair).ennreal_ofReal
  have hfY : AEMeasurable (Function.uncurry fY) (PY.prod νt) := by
    have hkernel : Measurable (fun z : ℝ × ℝ =>
        Real.rpowIntegrand₀₁ p z.1 z.2) := by
      unfold Real.rpowIntegrand₀₁
      fun_prop
    have hpair : AEMeasurable (fun z : ΩY × ℝ => (z.2, mY z.1)) (PY.prod νt) :=
      measurable_snd.aemeasurable.prodMk hmYMeas.aemeasurable.comp_fst
    exact (hkernel.comp_aemeasurable hpair).ennreal_ofReal
  have hpointX (ω : ΩX) :
      ENNReal.rpow (ENNReal.ofReal (mX ω)) p =
        ENNReal.ofReal c * ∫⁻ t, fX ω t ∂νt := by
    change ENNReal.ofReal (mX ω) ^ p = _
    rw [ENNReal.ofReal_rpow_of_pos (hmX ω)]
    have hkernelInt : IntegrableOn
        (fun t => Real.rpowIntegrand₀₁ p t (mX ω)) (Ioi (0 : ℝ)) volume :=
      Real.integrableOn_rpowIntegrand₀₁_Ioi ⟨hp.1, hp.2⟩ (hmX0 ω)
    have hkernelNonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun t => Real.rpowIntegrand₀₁ p t (mX ω)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Real.rpowIntegrand₀₁_nonneg hp.1 (le_of_lt ht) (hmX0 ω)
    have hkernelL := ofReal_integral_eq_lintegral_ofReal hkernelInt hkernelNonneg
    rw [show (mX ω) ^ p = c *
          ∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t (mX ω) ∂volume by
          simpa [c] using Real.rpow_eq_const_mul_integral
            ⟨hp.1, hp.2⟩ (hmX0 ω),
      ENNReal.ofReal_mul hcpos.le, hkernelL]
  have hpointY (ω : ΩY) :
      ENNReal.rpow (ENNReal.ofReal (mY ω)) p =
        ENNReal.ofReal c * ∫⁻ t, fY ω t ∂νt := by
    change ENNReal.ofReal (mY ω) ^ p = _
    rw [ENNReal.ofReal_rpow_of_pos (hmY ω)]
    have hkernelInt : IntegrableOn
        (fun t => Real.rpowIntegrand₀₁ p t (mY ω)) (Ioi (0 : ℝ)) volume :=
      Real.integrableOn_rpowIntegrand₀₁_Ioi ⟨hp.1, hp.2⟩ (hmY0 ω)
    have hkernelNonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun t => Real.rpowIntegrand₀₁ p t (mY ω)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Real.rpowIntegrand₀₁_nonneg hp.1 (le_of_lt ht) (hmY0 ω)
    have hkernelL := ofReal_integral_eq_lintegral_ofReal hkernelInt hkernelNonneg
    rw [show (mY ω) ^ p = c *
          ∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t (mY ω) ∂volume by
          simpa [c] using Real.rpow_eq_const_mul_integral
            ⟨hp.1, hp.2⟩ (hmY0 ω),
      ENNReal.ofReal_mul hcpos.le, hkernelL]
  have hRepX :
      ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (mX ω)) p ∂PX =
        ENNReal.ofReal c *
          ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ω, fX ω t ∂PX ∂volume := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal c * (∫⁻ t, fX ω t ∂νt) ∂PX := by
        apply lintegral_congr_ae
        exact ae_of_all PX hpointX
      _ = ENNReal.ofReal c * ∫⁻ ω, ∫⁻ t, fX ω t ∂νt ∂PX :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal c * ∫⁻ t, ∫⁻ ω, fX ω t ∂PX ∂νt := by
        congr 1
        exact lintegral_lintegral_swap hfX
  have hRepY :
      ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (mY ω)) p ∂PY =
        ENNReal.ofReal c *
          ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ω, fY ω t ∂PY ∂volume := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal c * (∫⁻ t, fY ω t ∂νt) ∂PY := by
        apply lintegral_congr_ae
        exact ae_of_all PY hpointY
      _ = ENNReal.ofReal c * ∫⁻ ω, ∫⁻ t, fY ω t ∂νt ∂PY :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal c * ∫⁻ t, ∫⁻ ω, fY ω t ∂PY ∂νt := by
        congr 1
        exact lintegral_lintegral_swap hfY
  have hkernelOrder (t : ℝ) (ht : 0 < t) :
      ∫⁻ ω, fY ω t ∂PY ≤ ∫⁻ ω, fX ω t ∂PX := by
    have hfrac := laplace_order_fraction_expectation PX PY mX mY
      hmXMeas.aemeasurable hmYMeas.aemeasurable hmX0 hmY0 hLap t ht
    have hfracIntX := resolvent_fraction_integrable PX mX hmXMeas.aemeasurable hmX0 t ht
    have hfracIntY := resolvent_fraction_integrable PY mY hmYMeas.aemeasurable hmY0 t ht
    have hcoef : 0 ≤ t ^ (p - 1) := Real.rpow_nonneg (le_of_lt ht) _
    have hkernelEqX (ω : ΩX) : Real.rpowIntegrand₀₁ p t (mX ω) =
        t ^ (p - 1) * (mX ω / (t + mX ω)) := by
      rw [Real.rpowIntegrand₀₁_eq_pow_div ⟨hp.1, hp.2⟩ ht.le (hmX0 ω)]
      ring
    have hkernelEqY (ω : ΩY) : Real.rpowIntegrand₀₁ p t (mY ω) =
        t ^ (p - 1) * (mY ω / (t + mY ω)) := by
      rw [Real.rpowIntegrand₀₁_eq_pow_div ⟨hp.1, hp.2⟩ ht.le (hmY0 ω)]
      ring
    have hkerIntX : Integrable (fun ω => Real.rpowIntegrand₀₁ p t (mX ω)) PX := by
      rw [show (fun ω => Real.rpowIntegrand₀₁ p t (mX ω)) =
        fun ω => t ^ (p - 1) * (mX ω / (t + mX ω)) by
          funext ω
          exact hkernelEqX ω]
      exact (hfracIntX.const_mul (t ^ (p - 1))).congr
        (Filter.Eventually.of_forall fun ω => by ring)
    have hkerIntY : Integrable (fun ω => Real.rpowIntegrand₀₁ p t (mY ω)) PY := by
      rw [show (fun ω => Real.rpowIntegrand₀₁ p t (mY ω)) =
        fun ω => t ^ (p - 1) * (mY ω / (t + mY ω)) by
          funext ω
          exact hkernelEqY ω]
      exact (hfracIntY.const_mul (t ^ (p - 1))).congr
        (Filter.Eventually.of_forall fun ω => by ring)
    have hkerNonnegX : ∀ ω, 0 ≤ Real.rpowIntegrand₀₁ p t (mX ω) :=
      fun ω => Real.rpowIntegrand₀₁_nonneg hp.1 ht.le (hmX0 ω)
    have hkerNonnegY : ∀ ω, 0 ≤ Real.rpowIntegrand₀₁ p t (mY ω) :=
      fun ω => Real.rpowIntegrand₀₁_nonneg hp.1 ht.le (hmY0 ω)
    have hkerReal :
        ∫ ω, Real.rpowIntegrand₀₁ p t (mY ω) ∂PY ≤
          ∫ ω, Real.rpowIntegrand₀₁ p t (mX ω) ∂PX := by
      rw [show (fun ω => Real.rpowIntegrand₀₁ p t (mX ω)) =
          fun ω => t ^ (p - 1) * (mX ω / (t + mX ω)) by
            funext ω
            exact hkernelEqX ω,
        show (fun ω => Real.rpowIntegrand₀₁ p t (mY ω)) =
          fun ω => t ^ (p - 1) * (mY ω / (t + mY ω)) by
            funext ω
            exact hkernelEqY ω,
        integral_const_mul, integral_const_mul]
      exact mul_le_mul_of_nonneg_left hfrac hcoef
    have hlinX := ofReal_integral_eq_lintegral_ofReal hkerIntX
      (Filter.Eventually.of_forall hkerNonnegX)
    have hlinY := ofReal_integral_eq_lintegral_ofReal hkerIntY
      (Filter.Eventually.of_forall hkerNonnegY)
    rw [← hlinY, ← hlinX]
    exact ENNReal.ofReal_le_ofReal hkerReal
  have houter :
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ω, fY ω t ∂PY ∂volume ≤
        ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ω, fX ω t ∂PX ∂volume := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hkernelOrder t ht
  have hmassPowerX :
      ∫⁻ ω, MX ω ^ p ∂PX = ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (mX ω)) p ∂PX := by
    apply lintegral_congr_ae
    filter_upwards [hmassEqX] with ω hω
    rw [hω]
    rfl
  have hmassPowerY :
      ∫⁻ ω, MY ω ^ p ∂PY = ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (mY ω)) p ∂PY := by
    apply lintegral_congr_ae
    filter_upwards [hmassEqY] with ω hω
    rw [hω]
    rfl
  calc
    _ = ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (mX ω)) p ∂PX := hmassPowerX
    _ = ENNReal.ofReal c *
          ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ω, fX ω t ∂PX ∂volume := hRepX
    _ ≥ ENNReal.ofReal c *
          ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ω, fY ω t ∂PY ∂volume :=
        mul_le_mul_of_nonneg_left houter (by positivity)
    _ = ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (mY ω)) p ∂PY := hRepY.symm
    _ = _ := hmassPowerY.symm


end DOZZ.Proofs
