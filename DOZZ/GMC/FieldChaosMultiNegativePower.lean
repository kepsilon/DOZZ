/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FieldChaosNegativePower
public import DOZZ.GMC.FiniteChaosMultiNegativePower
public import DOZZ.GMC.FiniteMultiMellin
public import DOZZ.Statements.GMC.FieldChaosMass

/-! Multiblock negative powers for continuum field chaos. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- A finite weighted sum of continuum chaos masses is one chaos mass with the weights summed
pointwise. -/
theorem fieldChaosMass_weighted_sum
    {Ω S κ : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Fintype κ]
    (P : Measure Ω) (Φ : Ω → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : Measure S) (h : κ → S → ℝ≥0) (hh : ∀ k, Measurable (h k))
    (t : κ → ℝ) (γ : ℝ) (ω : Ω) :
    DOZZ.fieldChaosMass P Φ ν
        (fun x => ∑ k, Real.toNNReal (t k) * h k x) γ ω =
      ∑ k, ENNReal.ofReal (t k) * DOZZ.fieldChaosMass P Φ ν (h k) γ ω := by
  classical
  let wick : S → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp
    (γ * Φ ω x - γ ^ 2 / 2 * ∫ ω', Φ ω' x ^ 2 ∂P))
  let hsum : S → ℝ≥0 := fun x => ∑ k, Real.toNNReal (t k) * h k x
  have hvar : Measurable (fun x => ∫ ω', Φ ω' x ^ 2 ∂P) := by
    simpa [DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two] using
      centeredGaussianField_variance_measurable P Φ hΦ
  have hsection : Measurable (fun x => Φ ω x) := by
    exact hΦ.1.comp (measurable_const.prodMk measurable_id)
  have hwick : Measurable wick := by
    dsimp [wick]
    fun_prop
  have hhsum : Measurable hsum := by
    dsimp [hsum]
    fun_prop
  have hkernel (x : S) :
      ENNReal.ofNNReal (hsum x) * wick x =
        ∑ k, ENNReal.ofReal (t k) *
          (ENNReal.ofNNReal (h k x) * wick x) := by
    dsimp [hsum, wick]
    rw [ENNReal.ofNNReal_finsetSum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [ENNReal.coe_mul, ENNReal.ofNNReal_toNNReal]
    ring
  have hweightWickMeas (k : κ) : Measurable
      (fun x => ENNReal.ofNNReal (h k x) * wick x) := by
    have hmeas : Measurable
        (fun x => ENNReal.ofReal ((h k x : ℝ≥0) : ℝ) * wick x) :=
      (ENNReal.measurable_ofReal.comp
        (NNReal.continuous_coe.measurable.comp (hh k))).mul hwick
    simpa only [ENNReal.ofReal_coe_nnreal] using hmeas
  have htermMeas (k : κ) : Measurable
      (fun x => ENNReal.ofReal (t k) *
        (ENNReal.ofNNReal (h k x) * wick x)) := by
    exact (measurable_const : Measurable (fun _ : S => ENNReal.ofReal (t k))).mul
      (hweightWickMeas k)
  calc
    _ = ∫⁻ x, ∑ k, ENNReal.ofReal (t k) *
          (ENNReal.ofNNReal (h k x) * wick x) ∂ν := by
            unfold DOZZ.fieldChaosMass
            apply lintegral_congr_ae
            exact ae_of_all ν hkernel
    _ = ∑ k, ∫⁻ x, ENNReal.ofReal (t k) *
          (ENNReal.ofNNReal (h k x) * wick x) ∂ν := by
            apply lintegral_finsetSum' Finset.univ
            intro k hk
            exact (htermMeas k).aemeasurable
    _ = ∑ k, ENNReal.ofReal (t k) *
          DOZZ.fieldChaosMass P Φ ν (h k) γ ω := by
            apply Finset.sum_congr rfl
            intro k hk
            change ∫⁻ x, ENNReal.ofReal (t k) *
              (ENNReal.ofNNReal (h k x) * wick x) ∂ν =
              ENNReal.ofReal (t k) * ∫⁻ x,
                ENNReal.ofNNReal (h k x) * wick x ∂ν
            rw [lintegral_const_mul'' _ (hweightWickMeas k).aemeasurable]

/-- The sum of several block masses has the single-field Laplace comparison whenever the
individual blocks do. -/
theorem kahane_field_multi_block_laplace
    {ΩX ΩY S κ : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [MeasurableSpace S] [Fintype κ] [Nonempty S]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField PX Φ)
    (hΨ : DOZZ.IsCenteredGaussianField PY Ψ)
    (ν : FiniteMeasure S) (hν : ν ≠ 0)
    (h : κ → S → ℝ≥0) (hh : ∀ k, Measurable (h k))
    (hhb : ∀ k, ∃ c : ℝ≥0, ∀ x, h k x ≤ c)
    (γ : ℝ) (t : κ → ℝ) (ht : ∀ k, 0 ≤ t k)
    (hposX : ∀ k, 0 < ∫ x, (h k x : ℝ) ∂(ν.normalize : Measure S))
    (hposY : ∀ k, 0 < ∫ x, (h k x : ℝ) ∂(ν.normalize : Measure S))
    (hcov : ∀ᵐ xy ∂(ν : Measure S).prod ν,
      DOZZ.gaussianCovariance PX (fun ω => Φ ω xy.1) (fun ω => Φ ω xy.2) ≤
        DOZZ.gaussianCovariance PY (fun ω => Ψ ω xy.1) (fun ω => Ψ ω xy.2))
    (hdiag : ∀ᵐ x ∂(ν : Measure S),
      DOZZ.gaussianVariance PX (fun ω => Φ ω x) ≤
        DOZZ.gaussianVariance PY (fun ω => Ψ ω x)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-∑ k, t k *
      (DOZZ.fieldChaosMass PX Φ (ν : Measure S) (h k) γ ω).toReal)) ∂PX ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-∑ k, t k *
        (DOZZ.fieldChaosMass PY Ψ (ν : Measure S) (h k) γ ω).toReal)) ∂PY := by
  classical
  let hsum : S → ℝ≥0 := fun x => ∑ k, Real.toNNReal (t k) * h k x
  have hsumMeas : Measurable hsum := by
    change Measurable (fun x => ∑ k, Real.toNNReal (t k) * h k x)
    apply Finset.measurable_fun_sum Finset.univ
    intro k hk
    exact measurable_const.mul (hh k)
  have hsumBound : ∃ c : ℝ≥0, ∀ x, hsum x ≤ c := by
    classical
    choose c hc using hhb
    refine ⟨∑ k, Real.toNNReal (t k) * c k, ?_⟩
    intro x
    dsimp [hsum]
    apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_left (hc k x) (NNReal.coe_nonneg _)
  have hmassX ω : DOZZ.fieldChaosMass PX Φ (ν : Measure S) hsum γ ω =
      ∑ k, ENNReal.ofReal (t k) *
        DOZZ.fieldChaosMass PX Φ (ν : Measure S) (h k) γ ω :=
    fieldChaosMass_weighted_sum PX Φ hΦ (ν : Measure S) h hh t γ ω
  have hmassY ω : DOZZ.fieldChaosMass PY Ψ (ν : Measure S) hsum γ ω =
      ∑ k, ENNReal.ofReal (t k) *
        DOZZ.fieldChaosMass PY Ψ (ν : Measure S) (h k) γ ω :=
    fieldChaosMass_weighted_sum PY Ψ hΨ (ν : Measure S) h hh t γ ω
  have hmassFiniteX (k : κ) : ∀ᵐ ω ∂PX,
      DOZZ.fieldChaosMass PX Φ (ν : Measure S) (h k) γ ω ≠ ∞ := by
    have heq := fieldChaosMass_eq_ofReal_modified_toReal_ae
      PX Φ hΦ ν hν (h k) (hh k) (hhb k) γ (hposX k)
    filter_upwards [heq] with ω hω
    rw [hω]
    exact ENNReal.ofReal_ne_top
  have hmassFiniteY (k : κ) : ∀ᵐ ω ∂PY,
      DOZZ.fieldChaosMass PY Ψ (ν : Measure S) (h k) γ ω ≠ ∞ := by
    have heq := fieldChaosMass_eq_ofReal_modified_toReal_ae
      PY Ψ hΨ ν hν (h k) (hh k) (hhb k) γ (hposY k)
    filter_upwards [heq] with ω hω
    rw [hω]
    exact ENNReal.ofReal_ne_top
  have hmassXtoReal : ∀ᵐ ω ∂PX,
      (DOZZ.fieldChaosMass PX Φ (ν : Measure S) hsum γ ω).toReal =
        ∑ k, t k * (DOZZ.fieldChaosMass PX Φ (ν : Measure S) (h k) γ ω).toReal := by
    filter_upwards [ae_all_iff.2 hmassFiniteX] with ω hω
    rw [hmassX ω, ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (ht k)]
    · intro k hk
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hω k)
  have hmassYtoReal : ∀ᵐ ω ∂PY,
      (DOZZ.fieldChaosMass PY Ψ (ν : Measure S) hsum γ ω).toReal =
        ∑ k, t k * (DOZZ.fieldChaosMass PY Ψ (ν : Measure S) (h k) γ ω).toReal := by
    filter_upwards [ae_all_iff.2 hmassFiniteY] with ω hω
    rw [hmassY ω, ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (ht k)]
    · intro k hk
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hω k)
  have hLap := kahane_field_laplace_of_nonzero_finite_measure_eq
    PX PY Φ Ψ hΦ hΨ ν hν hsum hsumMeas hsumBound γ 1 (by norm_num)
    hcov hdiag
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (Real.exp
          (-(DOZZ.fieldChaosMass PX Φ (ν : Measure S) hsum γ ω).toReal)) ∂PX := by
            apply lintegral_congr_ae
            filter_upwards [hmassXtoReal] with ω hω
            rw [hω]
    _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp
          (-(DOZZ.fieldChaosMass PY Ψ (ν : Measure S) hsum γ ω).toReal)) ∂PY := by
            simpa using hLap
    _ = _ := by
          apply lintegral_congr_ae
          filter_upwards [hmassYtoReal] with ω hω
          rw [hω]

/-- The continuum multiblock negative-power comparison follows by taking the Mellin transform of
the joint Laplace comparison for positive linear combinations of block masses. -/
theorem kahane_field_multi_negative_power
    {ΩX ΩY S κ : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [MeasurableSpace S] [Fintype κ]
    (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField PX Φ) (hΨ : DOZZ.IsCenteredGaussianField PY Ψ)
    (ν : Measure S) [IsFiniteMeasure ν] (h : κ → S → ℝ≥0)
    (hh : ∀ k, Measurable (h k))
    (hhb : ∀ k, ∃ c : ℝ≥0, ∀ x, h k x ≤ c)
    (γ : ℝ) (q : κ → ℝ) (hq : ∀ k, 0 ≤ q k)
    (hcov : ∀ᵐ xy ∂ν.prod ν,
      ∫ ω, Φ ω xy.1 * Φ ω xy.2 ∂PX ≤ ∫ ω, Ψ ω xy.1 * Ψ ω xy.2 ∂PY)
    (hdiag : ∀ᵐ x ∂ν,
      ∫ ω, Φ ω x ^ 2 ∂PX ≤ ∫ ω, Ψ ω x ^ 2 ∂PY) :
    ∫⁻ ω, ∏ k, ENNReal.rpow (DOZZ.fieldChaosMass PX Φ ν (h k) γ ω) (-q k) ∂PX ≤
      ∫⁻ ω, ∏ k, ENNReal.rpow (DOZZ.fieldChaosMass PY Ψ ν (h k) γ ω) (-q k) ∂PY := by
  classical
  let p : κ → Prop := fun k => 0 < q k
  let K := {k : κ // p k}
  let zX : ΩX → κ → ℝ≥0∞ := fun ω k =>
    ENNReal.rpow (DOZZ.fieldChaosMass PX Φ ν (h k) γ ω) (-q k)
  let zY : ΩY → κ → ℝ≥0∞ := fun ω k =>
    ENNReal.rpow (DOZZ.fieldChaosMass PY Ψ ν (h k) γ ω) (-q k)
  have hPXprob : IsProbabilityMeasure PX := (hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
  have hPYprob : IsProbabilityMeasure PY := (hΨ.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
  change ∫⁻ ω, ∏ k, zX ω k ∂PX ≤ ∫⁻ ω, ∏ k, zY ω k ∂PY
  by_cases hνzero : ν = 0
  · by_cases hK : Nonempty K
    · obtain ⟨k₀⟩ := hK
      have hmassX (ω : ΩX) (k : κ) :
          DOZZ.fieldChaosMass PX Φ ν (h k) γ ω = 0 := by
        simp [DOZZ.fieldChaosMass, hνzero]
      have hmassY (ω : ΩY) (k : κ) :
          DOZZ.fieldChaosMass PY Ψ ν (h k) γ ω = 0 := by
        simp [DOZZ.fieldChaosMass, hνzero]
      have hprodX (ω : ΩX) : ∏ k, zX ω k = ∞ := by
        change (∏ k, ENNReal.rpow
          (DOZZ.fieldChaosMass PX Φ ν (h k) γ ω) (-q k)) = ∞
        apply WithTop.prod_eq_top (Finset.mem_univ k₀.val)
        · change ENNReal.rpow
            (DOZZ.fieldChaosMass PX Φ ν (h k₀.val) γ ω) (-q k₀.val) = ∞
          rw [hmassX ω k₀.val]
          exact ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr k₀.property)
        · intro k hk
          by_cases hk0 : q k = 0
          · change ENNReal.rpow
              (DOZZ.fieldChaosMass PX Φ ν (h k) γ ω) (-q k) ≠ 0
            rw [hk0]
            simp
          · have hkpos : 0 < q k := lt_of_le_of_ne (hq k) (Ne.symm hk0)
            change ENNReal.rpow (DOZZ.fieldChaosMass PX Φ ν (h k) γ ω) (-q k) ≠ 0
            rw [hmassX ω k]
            have hpow : ENNReal.rpow (0 : ℝ≥0∞) (-q k) = ∞ :=
              ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr hkpos)
            rw [hpow]
            exact ENNReal.top_ne_zero
      have hprodY (ω : ΩY) : ∏ k, zY ω k = ∞ := by
        change (∏ k, ENNReal.rpow
          (DOZZ.fieldChaosMass PY Ψ ν (h k) γ ω) (-q k)) = ∞
        apply WithTop.prod_eq_top (Finset.mem_univ k₀.val)
        · change ENNReal.rpow
            (DOZZ.fieldChaosMass PY Ψ ν (h k₀.val) γ ω) (-q k₀.val) = ∞
          rw [hmassY ω k₀.val]
          exact ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr k₀.property)
        · intro k hk
          by_cases hk0 : q k = 0
          · change ENNReal.rpow
              (DOZZ.fieldChaosMass PY Ψ ν (h k) γ ω) (-q k) ≠ 0
            rw [hk0]
            simp
          · have hkpos : 0 < q k := lt_of_le_of_ne (hq k) (Ne.symm hk0)
            change ENNReal.rpow (DOZZ.fieldChaosMass PY Ψ ν (h k) γ ω) (-q k) ≠ 0
            rw [hmassY ω k]
            have hpow : ENNReal.rpow (0 : ℝ≥0∞) (-q k) = ∞ :=
              ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr hkpos)
            rw [hpow]
            exact ENNReal.top_ne_zero
      have hIX : ∫⁻ ω, ∏ k, zX ω k ∂PX = ∞ := by
        calc
          _ = ∫⁻ _ω : ΩX, (∞ : ℝ≥0∞) ∂PX := by
            apply lintegral_congr_ae
            exact ae_of_all PX hprodX
          _ = ∞ := by simp [hPXprob.measure_univ]
      have hIY : ∫⁻ ω, ∏ k, zY ω k ∂PY = ∞ := by
        calc
          _ = ∫⁻ _ω : ΩY, (∞ : ℝ≥0∞) ∂PY := by
            apply lintegral_congr_ae
            exact ae_of_all PY hprodY
          _ = ∞ := by simp [hPYprob.measure_univ]
      rw [hIX, hIY]
    · have hqzero (k : κ) : q k = 0 := by
        by_contra hne
        have hkpos : 0 < q k := lt_of_le_of_ne (hq k) (Ne.symm hne)
        exact hK ⟨k, hkpos⟩
      simp [zX, zY, hqzero, hPXprob.measure_univ, hPYprob.measure_univ]
  · let νf : FiniteMeasure S := ⟨ν, inferInstance⟩
    have hνf : νf ≠ 0 := by
      intro hzero
      apply hνzero
      have hcoerce := congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) hzero
      simpa [νf] using hcoerce
    have hνeq : (νf : Measure S) = ν := rfl
    have hS : Nonempty S := by
      have hUniv : ν Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hνzero
      obtain ⟨x, _⟩ := nonempty_of_measure_ne_zero hUniv
      exact ⟨x⟩
    let : Nonempty S := hS
    let ρ : Measure S := νf.normalize
    let α : κ → ℝ := fun k => ∫ x, (h k x : ℝ) ∂ρ
    have hαnonneg (k : κ) : 0 ≤ α k := by
      dsimp [α, ρ]
      exact integral_nonneg_of_ae (ae_of_all _ fun x => NNReal.coe_nonneg (h k x))
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
    by_cases hK : Nonempty K
    · obtain ⟨kdefault⟩ := hK
      let zKX : ΩX → K → ℝ≥0∞ := fun ω k =>
        ENNReal.rpow (DOZZ.fieldChaosMass PX Φ ν (h k.val) γ ω) (-q k.val)
      let zKY : ΩY → K → ℝ≥0∞ := fun ω k =>
        ENNReal.rpow (DOZZ.fieldChaosMass PY Ψ ν (h k.val) γ ω) (-q k.val)
      have hzXinactive (ω : ΩX) (k : {k : κ // ¬ p k}) : zX ω k.val = 1 := by
        have hq0 : q k.val = 0 := le_antisymm (le_of_not_gt k.property) (hq k.val)
        simp [zX, hq0]
      have hzYinactive (ω : ΩY) (k : {k : κ // ¬ p k}) : zY ω k.val = 1 := by
        have hq0 : q k.val = 0 := le_antisymm (le_of_not_gt k.property) (hq k.val)
        simp [zY, hq0]
      have hprodX (ω : ΩX) : ∏ k, zX ω k = ∏ k : K, zKX ω k := by
        calc
          (∏ k : κ, zX ω k) =
              (∏ k : K, zX ω k.val) * ∏ k : {k : κ // ¬ p k}, zX ω k.val :=
                (Fintype.prod_subtype_mul_prod_subtype p (zX ω)).symm
          _ = ∏ k : K, zX ω k.val := by simp [hzXinactive]
          _ = ∏ k : K, zKX ω k := by
                apply Finset.prod_congr rfl
                intro k hk
                rfl
      have hprodY (ω : ΩY) : ∏ k, zY ω k = ∏ k : K, zKY ω k := by
        calc
          (∏ k : κ, zY ω k) =
              (∏ k : K, zY ω k.val) * ∏ k : {k : κ // ¬ p k}, zY ω k.val :=
                (Fintype.prod_subtype_mul_prod_subtype p (zY ω)).symm
          _ = ∏ k : K, zY ω k.val := by simp [hzYinactive]
          _ = ∏ k : K, zKY ω k := by
                apply Finset.prod_congr rfl
                intro k hk
                rfl
      by_cases hweights : ∀ k : K, 0 < α k.val
      · let MX : ΩX → K → ℝ≥0∞ := fun ω k =>
          DOZZ.fieldChaosMass PX Φ ν (h k.val) γ ω
        let MY : ΩY → K → ℝ≥0∞ := fun ω k =>
          DOZZ.fieldChaosMass PY Ψ ν (h k.val) γ ω
        let mX : ΩX → K → ℝ := fun ω k =>
          if (MX ω k).toReal = 0 then 1 else (MX ω k).toReal
        let mY : ΩY → K → ℝ := fun ω k =>
          if (MY ω k).toReal = 0 then 1 else (MY ω k).toReal
        have hmXpos (ω : ΩX) (k : K) : 0 < mX ω k := by
          dsimp [mX]
          split_ifs with hz
          · norm_num
          · exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz)
        have hmYpos (ω : ΩY) (k : K) : 0 < mY ω k := by
          dsimp [mY]
          split_ifs with hz
          · norm_num
          · exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz)
        have hmassEqX (k : K) : ∀ᵐ ω ∂PX, MX ω k = ENNReal.ofReal (mX ω k) := by
          change ∀ᵐ ω ∂PX,
            DOZZ.fieldChaosMass PX Φ ν (h k.val) γ ω = ENNReal.ofReal
              (if (DOZZ.fieldChaosMass PX Φ ν (h k.val) γ ω).toReal = 0 then 1 else
                (DOZZ.fieldChaosMass PX Φ ν (h k.val) γ ω).toReal)
          exact fieldChaosMass_eq_ofReal_modified_toReal_ae PX Φ hΦ νf hνf
            (h k.val) (hh k.val) (hhb k.val) γ (by simpa [α, ρ] using hweights k)
        have hmassEqY (k : K) : ∀ᵐ ω ∂PY, MY ω k = ENNReal.ofReal (mY ω k) := by
          change ∀ᵐ ω ∂PY,
            DOZZ.fieldChaosMass PY Ψ ν (h k.val) γ ω = ENNReal.ofReal
              (if (DOZZ.fieldChaosMass PY Ψ ν (h k.val) γ ω).toReal = 0 then 1 else
                (DOZZ.fieldChaosMass PY Ψ ν (h k.val) γ ω).toReal)
          exact fieldChaosMass_eq_ofReal_modified_toReal_ae PY Ψ hΨ νf hνf
            (h k.val) (hh k.val) (hhb k.val) γ (by simpa [α, ρ] using hweights k)
        have htoRealX (k : K) : ∀ᵐ ω ∂PX, (MX ω k).toReal = mX ω k := by
          filter_upwards [hmassEqX k] with ω hω
          rw [hω, ENNReal.toReal_ofReal (le_of_lt (hmXpos ω k))]
        have htoRealY (k : K) : ∀ᵐ ω ∂PY, (MY ω k).toReal = mY ω k := by
          filter_upwards [hmassEqY k] with ω hω
          rw [hω, ENNReal.toReal_ofReal (le_of_lt (hmYpos ω k))]
        let nuPos : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
        let νK : K → Measure ℝ := fun _ => nuPos
        let T : Measure (K → ℝ) := Measure.pi νK
        let c : K → ℝ≥0∞ := fun k => ENNReal.ofReal (1 / Real.Gamma (q k.val))
        let C : ℝ≥0∞ := ∏ k : K, c k
        let fX : ΩX → (K → ℝ) → ℝ≥0∞ := fun ω t =>
          ∏ k : K, ENNReal.ofReal
            (t k ^ (q k.val - 1) * Real.exp (-(mX ω k * t k)))
        let fY : ΩY → (K → ℝ) → ℝ≥0∞ := fun ω t =>
          ∏ k : K, ENNReal.ofReal
            (t k ^ (q k.val - 1) * Real.exp (-(mY ω k * t k)))
        have hmXmass (k : K) : Measurable (fun ω => MX ω k) := by
          exact centeredGaussianField_fieldChaosMass_measurable PX Φ hΦ νf
            (h k.val) (hh k.val) γ
        have hmYmass (k : K) : Measurable (fun ω => MY ω k) := by
          exact centeredGaussianField_fieldChaosMass_measurable PY Ψ hΨ νf
            (h k.val) (hh k.val) γ
        have hmX (k : K) : Measurable (fun ω => mX ω k) := by
          apply Measurable.ite
            (measurableSet_eq_fun (hmXmass k).ennreal_toReal measurable_const)
          · exact measurable_const
          · exact (hmXmass k).ennreal_toReal
        have hmY (k : K) : Measurable (fun ω => mY ω k) := by
          apply Measurable.ite
            (measurableSet_eq_fun (hmYmass k).ennreal_toReal measurable_const)
          · exact measurable_const
          · exact (hmYmass k).ennreal_toReal
        have hmXprod : AEMeasurable (Function.uncurry fX) (PX.prod T) := by
          apply Finset.aemeasurable_fun_prod Finset.univ
          intro k hk
          have hm : AEMeasurable (fun z : ΩX × (K → ℝ) => mX z.1 k) (PX.prod T) :=
            (hmX k).aemeasurable.comp_fst
          have ht : Measurable (fun z : ΩX × (K → ℝ) => z.2 k) :=
            (measurable_pi_apply k).comp measurable_snd
          have harg : AEMeasurable (fun z : ΩX × (K → ℝ) =>
              -(mX z.1 k * z.2 k)) (PX.prod T) := (hm.mul ht.aemeasurable).neg
          have hpow : Measurable
              (fun z : ΩX × (K → ℝ) => z.2 k ^ (q k.val - 1)) := by fun_prop
          have hreal : AEMeasurable (fun z : ΩX × (K → ℝ) =>
              z.2 k ^ (q k.val - 1) * Real.exp (-(mX z.1 k * z.2 k))) (PX.prod T) :=
            hpow.aemeasurable.mul (Real.measurable_exp.comp_aemeasurable harg)
          exact hreal.ennreal_ofReal
        have hmYprod : AEMeasurable (Function.uncurry fY) (PY.prod T) := by
          apply Finset.aemeasurable_fun_prod Finset.univ
          intro k hk
          have hm : AEMeasurable (fun z : ΩY × (K → ℝ) => mY z.1 k) (PY.prod T) :=
            (hmY k).aemeasurable.comp_fst
          have ht : Measurable (fun z : ΩY × (K → ℝ) => z.2 k) :=
            (measurable_pi_apply k).comp measurable_snd
          have harg : AEMeasurable (fun z : ΩY × (K → ℝ) =>
              -(mY z.1 k * z.2 k)) (PY.prod T) := (hm.mul ht.aemeasurable).neg
          have hpow : Measurable
              (fun z : ΩY × (K → ℝ) => z.2 k ^ (q k.val - 1)) := by fun_prop
          have hreal : AEMeasurable (fun z : ΩY × (K → ℝ) =>
              z.2 k ^ (q k.val - 1) * Real.exp (-(mY z.1 k * z.2 k))) (PY.prod T) :=
            hpow.aemeasurable.mul (Real.measurable_exp.comp_aemeasurable harg)
          exact hreal.ennreal_ofReal
        have hIX : AEMeasurable (fun ω => ∫⁻ t, fX ω t ∂T) PX :=
          hmXprod.lintegral_prod_right
        have hIY : AEMeasurable (fun ω => ∫⁻ t, fY ω t ∂T) PY :=
          hmYprod.lintegral_prod_right
        have hscalarX (ω : ΩX) (k : K) :
            ENNReal.rpow (ENNReal.ofReal (mX ω k)) (-q k.val) =
              c k * ∫⁻ t in Ioi (0 : ℝ),
                ENNReal.ofReal (t ^ (q k.val - 1) *
                  Real.exp (-(mX ω k * t))) ∂volume := by
          change ENNReal.ofReal (mX ω k) ^ (-q k.val) = _
          rw [ENNReal.ofReal_rpow_of_pos (hmXpos ω k)]
          simpa [c] using ofReal_rpow_neg_eq_mellin_lintegral
            (hmXpos ω k) (k.property)
        have hscalarY (ω : ΩY) (k : K) :
            ENNReal.rpow (ENNReal.ofReal (mY ω k)) (-q k.val) =
              c k * ∫⁻ t in Ioi (0 : ℝ),
                ENNReal.ofReal (t ^ (q k.val - 1) *
                  Real.exp (-(mY ω k * t))) ∂volume := by
          change ENNReal.ofReal (mY ω k) ^ (-q k.val) = _
          rw [ENNReal.ofReal_rpow_of_pos (hmYpos ω k)]
          simpa [c] using ofReal_rpow_neg_eq_mellin_lintegral
            (hmYpos ω k) (k.property)
        have hpiX (ω : ΩX) : ∫⁻ t, fX ω t ∂T =
            ∏ k : K, ∫⁻ s in Ioi (0 : ℝ),
              ENNReal.ofReal (s ^ (q k.val - 1) *
                Real.exp (-(mX ω k * s))) ∂volume := by
          have h := lintegral_pi_prod νK
            (fun k s => ENNReal.ofReal (s ^ (q k.val - 1) *
              Real.exp (-(mX ω k * s))))
            (fun k => by infer_instance) (fun k => by fun_prop)
          simpa [T, nuPos, νK, fX] using h
        have hpiY (ω : ΩY) : ∫⁻ t, fY ω t ∂T =
            ∏ k : K, ∫⁻ s in Ioi (0 : ℝ),
              ENNReal.ofReal (s ^ (q k.val - 1) *
                Real.exp (-(mY ω k * s))) ∂volume := by
          have h := lintegral_pi_prod νK
            (fun k s => ENNReal.ofReal (s ^ (q k.val - 1) *
              Real.exp (-(mY ω k * s))))
            (fun k => by infer_instance) (fun k => by fun_prop)
          simpa [T, nuPos, νK, fY] using h
        have hpointX : ∀ᵐ ω ∂PX,
            (∏ k : K, ENNReal.rpow (MX ω k) (-q k.val)) =
              C * ∫⁻ t, fX ω t ∂T := by
          filter_upwards [ae_all_iff.2 hmassEqX] with ω hω
          calc
            (∏ k : K, ENNReal.rpow (MX ω k) (-q k.val)) =
                ∏ k : K, c k * ∫⁻ t in Ioi (0 : ℝ),
                  ENNReal.ofReal (t ^ (q k.val - 1) *
                    Real.exp (-(mX ω k * t))) ∂volume := by
                    apply Finset.prod_congr rfl
                    intro k hk
                    rw [hω k]
                    exact hscalarX ω k
            _ = C * ∏ k : K, ∫⁻ t in Ioi (0 : ℝ),
                  ENNReal.ofReal (t ^ (q k.val - 1) *
                    Real.exp (-(mX ω k * t))) ∂volume := by
                    simp [C, Finset.prod_mul_distrib]
            _ = C * ∫⁻ t, fX ω t ∂T := by rw [← hpiX ω]
        have hpointY : ∀ᵐ ω ∂PY,
            (∏ k : K, ENNReal.rpow (MY ω k) (-q k.val)) =
              C * ∫⁻ t, fY ω t ∂T := by
          filter_upwards [ae_all_iff.2 hmassEqY] with ω hω
          calc
            (∏ k : K, ENNReal.rpow (MY ω k) (-q k.val)) =
                ∏ k : K, c k * ∫⁻ t in Ioi (0 : ℝ),
                  ENNReal.ofReal (t ^ (q k.val - 1) *
                    Real.exp (-(mY ω k * t))) ∂volume := by
                    apply Finset.prod_congr rfl
                    intro k hk
                    rw [hω k]
                    exact hscalarY ω k
            _ = C * ∏ k : K, ∫⁻ t in Ioi (0 : ℝ),
                  ENNReal.ofReal (t ^ (q k.val - 1) *
                    Real.exp (-(mY ω k * t))) ∂volume := by
                    simp [C, Finset.prod_mul_distrib]
            _ = C * ∫⁻ t, fY ω t ∂T := by rw [← hpiY ω]
        have hcoordPos (k : K) : ∀ᵐ t ∂T, 0 < t k := by
          rw [ae_iff]
          have hnull : nuPos (Iic (0 : ℝ)) = 0 := by
            change (volume.restrict (Ioi (0 : ℝ))) (Iic (0 : ℝ)) = 0
            rw [Measure.restrict_apply measurableSet_Iic]
            rw [Set.inter_comm, Ioi_inter_Iic]
            simp
          simpa [Function.eval, Set.preimage, Set.mem_Iic] using
            (Measure.pi_eval_preimage_null νK hnull)
        have hcoordsPos : ∀ᵐ t ∂T, ∀ k : K, 0 < t k := ae_all_iff.2 hcoordPos
        have hinner (t : K → ℝ) (ht : ∀ k : K, 0 < t k) :
            ∫⁻ ω, fX ω t ∂PX ≤ ∫⁻ ω, fY ω t ∂PY := by
          have hLap := kahane_field_multi_block_laplace PX PY Φ Ψ hΦ hΨ νf hνf
            (fun k x => h k.val x) (fun k => hh k.val) (fun k => hhb k.val)
            γ t (fun k => (ht k).le)
            (fun k => by simpa [α, ρ] using hweights k)
            (fun k => by simpa [α, ρ] using hweights k) hcov' hdiag'
          have hsumX : ∀ᵐ ω ∂PX,
              ∑ k : K, t k * (MX ω k).toReal = ∑ k : K, t k * mX ω k := by
            filter_upwards [ae_all_iff.2 htoRealX] with ω hω
            apply Finset.sum_congr rfl
            intro k hk
            rw [hω k]
          have hsumY : ∀ᵐ ω ∂PY,
              ∑ k : K, t k * (MY ω k).toReal = ∑ k : K, t k * mY ω k := by
            filter_upwards [ae_all_iff.2 htoRealY] with ω hω
            apply Finset.sum_congr rfl
            intro k hk
            rw [hω k]
          have hLapM :
              ∫⁻ ω, ENNReal.ofReal (Real.exp (-∑ k : K, t k * mX ω k)) ∂PX ≤
                ∫⁻ ω, ENNReal.ofReal (Real.exp (-∑ k : K, t k * mY ω k)) ∂PY := by
            calc
              _ = ∫⁻ ω, ENNReal.ofReal (Real.exp
                    (-∑ k : K, t k * (MX ω k).toReal)) ∂PX := by
                    apply lintegral_congr_ae
                    filter_upwards [hsumX] with ω hω
                    rw [hω]
              _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp
                    (-∑ k : K, t k * (MY ω k).toReal)) ∂PY := by
                    simpa only [MX, MY, hνeq] using hLap
              _ = ∫⁻ ω, ENNReal.ofReal (Real.exp
                    (-∑ k : K, t k * mY ω k)) ∂PY := by
                    apply lintegral_congr_ae
                    filter_upwards [hsumY] with ω hω
                    rw [hω]
          have hkernelX (ω : ΩX) : fX ω t =
              ENNReal.ofReal (∏ k : K, t k ^ (q k.val - 1)) *
                ENNReal.ofReal (Real.exp (-∑ k : K, t k * mX ω k)) := by
            change (∏ k : K, ENNReal.ofReal
              (t k ^ (q k.val - 1) * Real.exp (-(mX ω k * t k)))) = _
            have hExp : (∏ k : K, Real.exp (-(mX ω k * t k))) =
                Real.exp (-∑ k : K, t k * mX ω k) := by
              rw [← Real.exp_sum]
              congr 1
              calc
                ∑ k : K, -(mX ω k * t k) = -(∑ k : K, mX ω k * t k) := by
                  rw [Finset.sum_neg_distrib]
                _ = -(∑ k : K, t k * mX ω k) := by
                  congr 1
                  apply Finset.sum_congr rfl
                  intro k hk
                  ring
            calc
              _ = ∏ k : K, (ENNReal.ofReal (t k ^ (q k.val - 1)) *
                    ENNReal.ofReal (Real.exp (-(mX ω k * t k)))) := by
                      apply Finset.prod_congr rfl
                      intro k hk
                      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt (ht k)) _)]
              _ = (∏ k : K, ENNReal.ofReal (t k ^ (q k.val - 1))) *
                    ∏ k : K, ENNReal.ofReal (Real.exp (-(mX ω k * t k))) :=
                    Finset.prod_mul_distrib
              _ = _ := by
                    rw [← ENNReal.ofReal_prod_of_nonneg
                      (fun k hk => Real.rpow_nonneg (le_of_lt (ht k)) _),
                      ← ENNReal.ofReal_prod_of_nonneg
                        (fun k hk => Real.exp_nonneg (-(mX ω k * t k))), hExp]
          have hkernelY (ω : ΩY) : fY ω t =
              ENNReal.ofReal (∏ k : K, t k ^ (q k.val - 1)) *
                ENNReal.ofReal (Real.exp (-∑ k : K, t k * mY ω k)) := by
            change (∏ k : K, ENNReal.ofReal
              (t k ^ (q k.val - 1) * Real.exp (-(mY ω k * t k)))) = _
            have hExp : (∏ k : K, Real.exp (-(mY ω k * t k))) =
                Real.exp (-∑ k : K, t k * mY ω k) := by
              rw [← Real.exp_sum]
              congr 1
              calc
                ∑ k : K, -(mY ω k * t k) = -(∑ k : K, mY ω k * t k) := by
                  rw [Finset.sum_neg_distrib]
                _ = -(∑ k : K, t k * mY ω k) := by
                  congr 1
                  apply Finset.sum_congr rfl
                  intro k hk
                  ring
            calc
              _ = ∏ k : K, (ENNReal.ofReal (t k ^ (q k.val - 1)) *
                    ENNReal.ofReal (Real.exp (-(mY ω k * t k)))) := by
                      apply Finset.prod_congr rfl
                      intro k hk
                      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt (ht k)) _)]
              _ = (∏ k : K, ENNReal.ofReal (t k ^ (q k.val - 1))) *
                    ∏ k : K, ENNReal.ofReal (Real.exp (-(mY ω k * t k))) :=
                    Finset.prod_mul_distrib
              _ = _ := by
                    rw [← ENNReal.ofReal_prod_of_nonneg
                      (fun k hk => Real.rpow_nonneg (le_of_lt (ht k)) _),
                      ← ENNReal.ofReal_prod_of_nonneg
                        (fun k hk => Real.exp_nonneg (-(mY ω k * t k))), hExp]
          rw [show (fun ω : ΩX => fX ω t) = fun ω =>
              ENNReal.ofReal (∏ k : K, t k ^ (q k.val - 1)) *
                ENNReal.ofReal (Real.exp (-∑ k : K, t k * mX ω k)) by
                  funext ω
                  exact hkernelX ω,
            show (fun ω : ΩY => fY ω t) = fun ω =>
              ENNReal.ofReal (∏ k : K, t k ^ (q k.val - 1)) *
                ENNReal.ofReal (Real.exp (-∑ k : K, t k * mY ω k)) by
                  funext ω
                  exact hkernelY ω]
          have hcoeff : ENNReal.ofReal (∏ k : K, t k ^ (q k.val - 1)) ≠ ∞ :=
            ENNReal.ofReal_ne_top
          rw [lintegral_const_mul' _ _ hcoeff, lintegral_const_mul' _ _ hcoeff]
          gcongr
        have houter :
            ∫⁻ t, ∫⁻ ω, fX ω t ∂PX ∂T ≤
              ∫⁻ t, ∫⁻ ω, fY ω t ∂PY ∂T := by
          apply lintegral_mono_ae
          filter_upwards [hcoordsPos] with t ht
          exact hinner t ht
        have hMomentX :
            ∫⁻ ω, ∏ k : K, ENNReal.rpow (MX ω k) (-q k.val) ∂PX =
              C * ∫⁻ t, ∫⁻ ω, fX ω t ∂PX ∂T := by
          calc
            _ = ∫⁻ ω, C * (∫⁻ t, fX ω t ∂T) ∂PX := by
              apply lintegral_congr_ae
              exact hpointX
            _ = C * ∫⁻ ω, ∫⁻ t, fX ω t ∂T ∂PX := lintegral_const_mul'' C hIX
            _ = C * ∫⁻ t, ∫⁻ ω, fX ω t ∂PX ∂T := by
              congr 1
              exact lintegral_lintegral_swap hmXprod
        have hMomentY :
            ∫⁻ ω, ∏ k : K, ENNReal.rpow (MY ω k) (-q k.val) ∂PY =
              C * ∫⁻ t, ∫⁻ ω, fY ω t ∂PY ∂T := by
          calc
            _ = ∫⁻ ω, C * (∫⁻ t, fY ω t ∂T) ∂PY := by
              apply lintegral_congr_ae
              exact hpointY
            _ = C * ∫⁻ ω, ∫⁻ t, fY ω t ∂T ∂PY := lintegral_const_mul'' C hIY
            _ = C * ∫⁻ t, ∫⁻ ω, fY ω t ∂PY ∂T := by
              congr 1
              exact lintegral_lintegral_swap hmYprod
        have hactive :
            ∫⁻ ω, ∏ k : K, zKX ω k ∂PX ≤ ∫⁻ ω, ∏ k : K, zKY ω k ∂PY := by
          calc
            _ = C * ∫⁻ t, ∫⁻ ω, fX ω t ∂PX ∂T := hMomentX
            _ ≤ C * ∫⁻ t, ∫⁻ ω, fY ω t ∂PY ∂T := by gcongr
            _ = _ := hMomentY.symm
        calc
          ∫⁻ ω, ∏ k, zX ω k ∂PX = ∫⁻ ω, ∏ k : K, zKX ω k ∂PX := by
            apply lintegral_congr_ae
            exact ae_of_all _ hprodX
          _ ≤ ∫⁻ ω, ∏ k : K, zKY ω k ∂PY := hactive
          _ = ∫⁻ ω, ∏ k, zY ω k ∂PY := by
            apply lintegral_congr_ae
            exact ae_of_all _ fun ω => (hprodY ω).symm
      · obtain ⟨kbad, hkbad⟩ := not_forall.mp hweights
        have hzeroWeight : α kbad.val = 0 := le_antisymm (not_lt.mp hkbad) (hαnonneg kbad.val)
        have hzeroX (ω : ΩX) :
            DOZZ.fieldChaosMass PX Φ ν (h kbad.val) γ ω = 0 := by
          have hz := centeredGaussianField_fieldChaosMass_eq_zero_of_zero_weight_integral
            PX Φ νf (h kbad.val) (hh kbad.val) (hhb kbad.val) γ
            (by simpa [α, ρ] using hzeroWeight)
          simpa [νf] using hz ω
        have hzeroY (ω : ΩY) :
            DOZZ.fieldChaosMass PY Ψ ν (h kbad.val) γ ω = 0 := by
          have hz := centeredGaussianField_fieldChaosMass_eq_zero_of_zero_weight_integral
            PY Ψ νf (h kbad.val) (hh kbad.val) (hhb kbad.val) γ
            (by simpa [α, ρ] using hzeroWeight)
          simpa [νf] using hz ω
        have hfactorTopX (ω : ΩX) : zKX ω kbad = ∞ := by
          change ENNReal.rpow
            (DOZZ.fieldChaosMass PX Φ ν (h kbad.val) γ ω) (-q kbad.val) = ∞
          rw [hzeroX ω]
          exact ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr kbad.property)
        have hfactorTopY (ω : ΩY) : zKY ω kbad = ∞ := by
          change ENNReal.rpow
            (DOZZ.fieldChaosMass PY Ψ ν (h kbad.val) γ ω) (-q kbad.val) = ∞
          rw [hzeroY ω]
          exact ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr kbad.property)
        have hfactorNeZeroX (k : K) : ∀ᵐ ω ∂PX, zKX ω k ≠ 0 := by
          by_cases hα0 : α k.val = 0
          · have hzero : ∀ ω, DOZZ.fieldChaosMass PX Φ ν (h k.val) γ ω = 0 :=
              by
                have hz := centeredGaussianField_fieldChaosMass_eq_zero_of_zero_weight_integral
                  PX Φ νf (h k.val) (hh k.val) (hhb k.val) γ
                  (by simpa [α, ρ] using hα0)
                intro ω
                simpa only [hνeq] using hz ω
            filter_upwards with ω
            change ENNReal.rpow
              (DOZZ.fieldChaosMass PX Φ ν (h k.val) γ ω) (-q k.val) ≠ 0
            rw [hzero ω]
            have hrpow : ENNReal.rpow (0 : ℝ≥0∞) (-q k.val) = ∞ :=
              ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr k.property)
            rw [hrpow]
            exact ENNReal.top_ne_zero
          · have hαpos : 0 < α k.val := lt_of_le_of_ne (hαnonneg k.val) (Ne.symm hα0)
            have hpos := centeredGaussianField_fieldChaosMass_pos_ae_of_pos_weight_integral
              PX Φ hΦ νf hνf (h k.val) (hh k.val) (hhb k.val) γ
              (by simpa [α, ρ] using hαpos)
            have hfinite := fieldChaosMass_eq_ofReal_modified_toReal_ae
              PX Φ hΦ νf hνf (h k.val) (hh k.val) (hhb k.val) γ
              (by simpa [α, ρ] using hαpos)
            filter_upwards [hpos, hfinite] with ω hpω hfω
            have hpω' : 0 < DOZZ.fieldChaosMass PX Φ ν (h k.val) γ ω := by
              simpa only [hνeq] using hpω
            have hneTop : DOZZ.fieldChaosMass PX Φ ν (h k.val) γ ω ≠ ∞ := by
              have hfω' : DOZZ.fieldChaosMass PX Φ ν (h k.val) γ ω =
                  ENNReal.ofReal
                    (if (DOZZ.fieldChaosMass PX Φ ν (h k.val) γ ω).toReal = 0 then 1 else
                      (DOZZ.fieldChaosMass PX Φ ν (h k.val) γ ω).toReal) := by
                simpa only [hνeq] using hfω
              rw [hfω']
              exact ENNReal.ofReal_ne_top
            exact (ENNReal.rpow_pos hpω' hneTop).ne'
        have hfactorNeZeroY (k : K) : ∀ᵐ ω ∂PY, zKY ω k ≠ 0 := by
          by_cases hα0 : α k.val = 0
          · have hzero : ∀ ω, DOZZ.fieldChaosMass PY Ψ ν (h k.val) γ ω = 0 :=
              by
                have hz := centeredGaussianField_fieldChaosMass_eq_zero_of_zero_weight_integral
                  PY Ψ νf (h k.val) (hh k.val) (hhb k.val) γ
                  (by simpa [α, ρ] using hα0)
                intro ω
                simpa only [hνeq] using hz ω
            filter_upwards with ω
            change ENNReal.rpow
              (DOZZ.fieldChaosMass PY Ψ ν (h k.val) γ ω) (-q k.val) ≠ 0
            rw [hzero ω]
            have hrpow : ENNReal.rpow (0 : ℝ≥0∞) (-q k.val) = ∞ :=
              ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr k.property)
            rw [hrpow]
            exact ENNReal.top_ne_zero
          · have hαpos : 0 < α k.val := lt_of_le_of_ne (hαnonneg k.val) (Ne.symm hα0)
            have hpos := centeredGaussianField_fieldChaosMass_pos_ae_of_pos_weight_integral
              PY Ψ hΨ νf hνf (h k.val) (hh k.val) (hhb k.val) γ
              (by simpa [α, ρ] using hαpos)
            have hfinite := fieldChaosMass_eq_ofReal_modified_toReal_ae
              PY Ψ hΨ νf hνf (h k.val) (hh k.val) (hhb k.val) γ
              (by simpa [α, ρ] using hαpos)
            filter_upwards [hpos, hfinite] with ω hpω hfω
            have hpω' : 0 < DOZZ.fieldChaosMass PY Ψ ν (h k.val) γ ω := by
              simpa only [hνeq] using hpω
            have hneTop : DOZZ.fieldChaosMass PY Ψ ν (h k.val) γ ω ≠ ∞ := by
              have hfω' : DOZZ.fieldChaosMass PY Ψ ν (h k.val) γ ω =
                  ENNReal.ofReal
                    (if (DOZZ.fieldChaosMass PY Ψ ν (h k.val) γ ω).toReal = 0 then 1 else
                      (DOZZ.fieldChaosMass PY Ψ ν (h k.val) γ ω).toReal) := by
                simpa only [hνeq] using hfω
              rw [hfω']
              exact ENNReal.ofReal_ne_top
            exact (ENNReal.rpow_pos hpω' hneTop).ne'
        have hprodTopX : ∀ᵐ ω ∂PX, ∏ k : K, zKX ω k = ∞ := by
          filter_upwards [ae_all_iff.2 hfactorNeZeroX] with ω hω
          exact WithTop.prod_eq_top (Finset.mem_univ kbad) (hfactorTopX ω)
            (fun k hk => hω k)
        have hprodTopY : ∀ᵐ ω ∂PY, ∏ k : K, zKY ω k = ∞ := by
          filter_upwards [ae_all_iff.2 hfactorNeZeroY] with ω hω
          exact WithTop.prod_eq_top (Finset.mem_univ kbad) (hfactorTopY ω)
            (fun k hk => hω k)
        have hIX : ∫⁻ ω, ∏ k, zX ω k ∂PX = ∞ := by
          calc
            _ = ∫⁻ _ω : ΩX, (∞ : ℝ≥0∞) ∂PX := by
              apply lintegral_congr_ae
              filter_upwards [hprodTopX] with ω hω
              rw [hprodX ω, hω]
            _ = ∞ := by simp [hPXprob.measure_univ]
        have hIY : ∫⁻ ω, ∏ k, zY ω k ∂PY = ∞ := by
          calc
            _ = ∫⁻ _ω : ΩY, (∞ : ℝ≥0∞) ∂PY := by
              apply lintegral_congr_ae
              filter_upwards [hprodTopY] with ω hω
              rw [hprodY ω, hω]
            _ = ∞ := by simp [hPYprob.measure_univ]
        rw [hIX, hIY]
    · have hqzero (k : κ) : q k = 0 := by
        by_contra hne
        have hkpos : 0 < q k := lt_of_le_of_ne (hq k) (Ne.symm hne)
        exact hK ⟨k, hkpos⟩
      simp [zX, zY, hqzero, hPXprob.measure_univ, hPYprob.measure_univ]


end DOZZ.Proofs
