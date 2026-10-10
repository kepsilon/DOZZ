/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FieldChaosMultiNegativePower
public import DOZZ.GMC.FieldChaosFiniteness
public import DOZZ.GMC.KahaneLimitFieldNegativePower
public import DOZZ.GMC.KahaneMultiNegativeMellin

/-! Multiblock Laplace comparison for limits of continuum chaos masses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Finite weighted sums preserve convergence in measure. The proof uses the finite union bound
and the Lipschitz estimate for the weighted sum, so it applies to arbitrary finite index types. -/
theorem tendstoInMeasure_weighted_sum
    {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    (P : Measure Ω) (f : κ → ℝ → Ω → ℝ) (g : κ → Ω → ℝ)
    (t : κ → ℝ) (_hpos : ∀ k, 0 ≤ t k)
    (hfg : ∀ k, TendstoInMeasure P (f k) atTop (g k)) :
    TendstoInMeasure P
      (fun r ω => ∑ k, t k * f k r ω) atTop
      (fun ω => ∑ k, t k * g k ω) := by
  classical
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  let C : ℝ := 1 + ∑ k, |t k|
  let δ : ℝ := ε / C
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hδpos : 0 < δ := div_pos hε hCpos
  have hsmall : (∑ k, |t k|) * δ < ε := by
    dsimp [C, δ]
    have hsum : 0 ≤ ∑ k, |t k| := Finset.sum_nonneg fun k hk => abs_nonneg _
    field_simp
    nlinarith
  have hbadbound (r : ℝ) :
      P {ω | ε ≤ ‖(∑ k, t k * f k r ω) - (∑ k, t k * g k ω)‖} ≤
        ∑ k, P {ω | δ ≤ ‖f k r ω - g k ω‖} := by
    let A : Set Ω := {ω | ε ≤ ‖(∑ k, t k * f k r ω) - (∑ k, t k * g k ω)‖}
    let B : κ → Set Ω := fun k => {ω | δ ≤ ‖f k r ω - g k ω‖}
    have hsubset : A ⊆ ⋃ k, B k := by
      intro ω hω
      by_contra hnot
      have hcoord : ∀ k, ‖f k r ω - g k ω‖ < δ := by
        intro k
        have hk : ω ∉ B k := by
          intro hmem
          exact hnot (Set.mem_iUnion.mpr ⟨k, hmem⟩)
        exact lt_of_not_ge (by simpa [B] using hk)
      have hsumdiff :
          (∑ k, t k * f k r ω) - (∑ k, t k * g k ω) =
            ∑ k, t k * (f k r ω - g k ω) := by
        rw [← Finset.sum_sub_distrib]
        congr 1
        funext k
        ring
      have hnorm :
          ‖(∑ k, t k * f k r ω) - (∑ k, t k * g k ω)‖ ≤
            (∑ k, |t k|) * δ := by
        rw [hsumdiff]
        calc
          ‖∑ k, t k * (f k r ω - g k ω)‖ ≤
              ∑ k, ‖t k * (f k r ω - g k ω)‖ := norm_sum_le _ _
          _ = ∑ k, |t k| * ‖f k r ω - g k ω‖ := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [norm_mul, Real.norm_eq_abs]
          _ ≤ ∑ k, |t k| * δ := by
              apply Finset.sum_le_sum
              intro k hk
              exact mul_le_mul_of_nonneg_left (le_of_lt (hcoord k)) (abs_nonneg _)
          _ = (∑ k, |t k|) * δ := by rw [Finset.sum_mul]
      exact (not_lt_of_ge hω) (lt_of_le_of_lt hnorm hsmall)
    calc
      P A ≤ P (⋃ k, B k) := measure_mono hsubset
      _ ≤ ∑ k, P (B k) := measure_iUnion_fintype_le P B
  have hsum : Tendsto
      (fun r : ℝ => ∑ k : κ, P {ω | δ ≤ ‖f k r ω - g k ω‖}) atTop (𝓝 0) := by
    have hEach (k : κ) (_hk : k ∈ (Finset.univ : Finset κ)) :=
      tendstoInMeasure_iff_norm.mp (hfg k) δ hδpos
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum (Finset.univ : Finset κ) hEach
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum ?_ ?_
  · intro r
    exact bot_le
  · intro r
    exact hbadbound r

/-- The limiting vector of continuum masses inherits every nonnegative weighted Laplace
comparison. The cutoff masses are combined into one field-chaos mass, and the weighted sums
converge in measure by the finite-sum estimate above. -/
theorem kahane_limit_field_multi_block_laplace
    {ΩX ΩY S κ : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [MeasurableSpace S] [Fintype κ]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (Φ : ℝ → ΩX → S → ℝ) (Ψ : ℝ → ΩY → S → ℝ)
    (hΦ : ∀ r, DOZZ.IsCenteredGaussianField PX (Φ r))
    (hΨ : ∀ r, DOZZ.IsCenteredGaussianField PY (Ψ r))
    (ν : Measure S) [IsFiniteMeasure ν]
    (h : κ → S → ℝ≥0) (hh : ∀ k, Measurable (h k))
    (hhb : ∀ k, ∃ c : ℝ≥0, ∀ x, h k x ≤ c)
    (γ : ℝ) (t : κ → ℝ) (ht : ∀ k, 0 ≤ t k)
    (hcov : ∀ r, ∀ᵐ xy ∂ν.prod ν,
      ∫ ω, Φ r ω xy.1 * Φ r ω xy.2 ∂PX ≤
        ∫ ω, Ψ r ω xy.1 * Ψ r ω xy.2 ∂PY)
    (hdiag : ∀ r, ∀ᵐ x ∂ν,
      ∫ ω, Φ r ω x ^ 2 ∂PX ≤ ∫ ω, Ψ r ω x ^ 2 ∂PY)
    (ZX : κ → ΩX → ℝ) (ZY : κ → ΩY → ℝ)
    (hXconv : ∀ k, TendstoInMeasure PX
      (fun r ω => (DOZZ.fieldChaosMass PX (Φ r) ν (h k) γ ω).toReal) atTop (ZX k))
    (hYconv : ∀ k, TendstoInMeasure PY
      (fun r ω => (DOZZ.fieldChaosMass PY (Ψ r) ν (h k) γ ω).toReal) atTop (ZY k)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-∑ k, t k * ZX k ω)) ∂PX ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-∑ k, t k * ZY k ω)) ∂PY := by
  classical
  let hsum : S → ℝ≥0 := fun x => ∑ k, Real.toNNReal (t k) * h k x
  have hsumMeas : Measurable hsum := by
    dsimp [hsum]
    fun_prop
  have hsumBound : ∃ c : ℝ≥0, ∀ x, hsum x ≤ c := by
    choose c hc using hhb
    refine ⟨∑ k, Real.toNNReal (t k) * c k, ?_⟩
    intro x
    dsimp [hsum]
    apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_left (hc k x) (NNReal.coe_nonneg _)
  let νf : FiniteMeasure S := ⟨ν, inferInstance⟩
  have hmassX (r : ℝ) (ω : ΩX) :
      DOZZ.fieldChaosMass PX (Φ r) ν hsum γ ω =
        ∑ k, ENNReal.ofReal (t k) *
          DOZZ.fieldChaosMass PX (Φ r) ν (h k) γ ω := by
    exact fieldChaosMass_weighted_sum PX (Φ r) (hΦ r) ν h hh t γ ω
  have hmassY (r : ℝ) (ω : ΩY) :
      DOZZ.fieldChaosMass PY (Ψ r) ν hsum γ ω =
        ∑ k, ENNReal.ofReal (t k) *
          DOZZ.fieldChaosMass PY (Ψ r) ν (h k) γ ω := by
    exact fieldChaosMass_weighted_sum PY (Ψ r) (hΨ r) ν h hh t γ ω
  have hfiniteX (r : ℝ) (k : κ) : ∀ᵐ ω ∂PX,
      DOZZ.fieldChaosMass PX (Φ r) ν (h k) γ ω ≠ ∞ := by
    by_cases hνzero : ν = 0
    · filter_upwards [] with ω
      simp [DOZZ.fieldChaosMass, hνzero]
    · have hUniv : ν Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hνzero
      have hS : Nonempty S := by
        obtain ⟨x, _⟩ := nonempty_of_measure_ne_zero hUniv
        exact ⟨x⟩
      let : Nonempty S := hS
      simpa [νf] using centeredGaussianField_fieldChaosMass_ne_top_ae
        PX (Φ r) (hΦ r) νf (h k) (hh k) (hhb k) γ
  have hfiniteY (r : ℝ) (k : κ) : ∀ᵐ ω ∂PY,
      DOZZ.fieldChaosMass PY (Ψ r) ν (h k) γ ω ≠ ∞ := by
    by_cases hνzero : ν = 0
    · filter_upwards [] with ω
      simp [DOZZ.fieldChaosMass, hνzero]
    · have hUniv : ν Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hνzero
      have hS : Nonempty S := by
        obtain ⟨x, _⟩ := nonempty_of_measure_ne_zero hUniv
        exact ⟨x⟩
      let : Nonempty S := hS
      simpa [νf] using centeredGaussianField_fieldChaosMass_ne_top_ae
        PY (Ψ r) (hΨ r) νf (h k) (hh k) (hhb k) γ
  have htoRealX (r : ℝ) : ∀ᵐ ω ∂PX,
      (DOZZ.fieldChaosMass PX (Φ r) ν hsum γ ω).toReal =
        ∑ k, t k * (DOZZ.fieldChaosMass PX (Φ r) ν (h k) γ ω).toReal := by
    filter_upwards [ae_all_iff.2 (hfiniteX r)] with ω hω
    rw [hmassX r ω, ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (ht k)]
    · intro k hk
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hω k)
  have htoRealY (r : ℝ) : ∀ᵐ ω ∂PY,
      (DOZZ.fieldChaosMass PY (Ψ r) ν hsum γ ω).toReal =
        ∑ k, t k * (DOZZ.fieldChaosMass PY (Ψ r) ν (h k) γ ω).toReal := by
    filter_upwards [ae_all_iff.2 (hfiniteY r)] with ω hω
    rw [hmassY r ω, ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (ht k)]
    · intro k hk
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hω k)
  let gX : ΩX → ℝ := fun ω => ∑ k, t k * ZX k ω
  let gY : ΩY → ℝ := fun ω => ∑ k, t k * ZY k ω
  have hXsum := tendstoInMeasure_weighted_sum PX
    (fun k r ω => (DOZZ.fieldChaosMass PX (Φ r) ν (h k) γ ω).toReal)
    (fun k ω => ZX k ω) t ht hXconv
  have hYsum := tendstoInMeasure_weighted_sum PY
    (fun k r ω => (DOZZ.fieldChaosMass PY (Ψ r) ν (h k) γ ω).toReal)
    (fun k ω => ZY k ω) t ht hYconv
  have hXmass : TendstoInMeasure PX
      (fun r ω => (DOZZ.fieldChaosMass PX (Φ r) ν hsum γ ω).toReal) atTop gX := by
    exact TendstoInMeasure.congr'
      (Filter.Eventually.of_forall fun r => Filter.EventuallyEq.symm (htoRealX r))
      (ae_of_all _ fun ω => rfl) (by simpa [gX] using hXsum)
  have hYmass : TendstoInMeasure PY
      (fun r ω => (DOZZ.fieldChaosMass PY (Ψ r) ν hsum γ ω).toReal) atTop gY := by
    exact TendstoInMeasure.congr'
      (Filter.Eventually.of_forall fun r => Filter.EventuallyEq.symm (htoRealY r))
      (ae_of_all _ fun ω => rfl) (by simpa [gY] using hYsum)
  have hLap := kahane_limit_field_laplace PX PY Φ Ψ hΦ hΨ ν hsum hsumMeas
    hsumBound γ 1 (by norm_num) hcov hdiag gX gY hXmass hYmass
  simpa [gX, gY] using hLap

/-- Multivariate negative-power Kahane comparison for chaos limits. Convergence in probability of
each block mass suffices, through the multivariate Laplace representation. -/
theorem kahane_limit_field_multi_negative_power
    {ΩX ΩY S κ : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [MeasurableSpace S]
    [Fintype κ]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (Φ : ℝ → ΩX → S → ℝ) (Ψ : ℝ → ΩY → S → ℝ)
    (hΦ : ∀ r, IsCenteredGaussianField PX (Φ r))
    (hΨ : ∀ r, IsCenteredGaussianField PY (Ψ r))
    (ν : Measure S) [IsFiniteMeasure ν] (h : κ → S → ℝ≥0)
    (hh : ∀ k, Measurable (h k)) (hhb : ∀ k, ∃ c : ℝ≥0, ∀ x, h k x ≤ c)
    (γ : ℝ) (q : κ → ℝ) (hq : ∀ k, 0 ≤ q k)
    (hcov : ∀ r, ∀ᵐ xy ∂ν.prod ν,
      ∫ ω, Φ r ω xy.1 * Φ r ω xy.2 ∂PX ≤ ∫ ω, Ψ r ω xy.1 * Ψ r ω xy.2 ∂PY)
    (hdiag : ∀ r, ∀ᵐ x ∂ν,
      ∫ ω, Φ r ω x ^ 2 ∂PX ≤ ∫ ω, Ψ r ω x ^ 2 ∂PY)
    (ZX : κ → ΩX → ℝ) (ZY : κ → ΩY → ℝ)
    (hXconv : ∀ k, TendstoInMeasure PX
      (fun r ω => (fieldChaosMass PX (Φ r) ν (h k) γ ω).toReal) atTop (ZX k))
    (hYconv : ∀ k, TendstoInMeasure PY
      (fun r ω => (fieldChaosMass PY (Ψ r) ν (h k) γ ω).toReal) atTop (ZY k)) :
    ∫⁻ ω, ∏ k, ENNReal.rpow (ENNReal.ofReal (ZX k ω)) (-q k) ∂PX ≤
      ∫⁻ ω, ∏ k, ENNReal.rpow (ENNReal.ofReal (ZY k ω)) (-q k) ∂PY := by
  classical
  let : IsProbabilityMeasure PX := (hΦ 0).2 0 (fun i : Fin 0 => Fin.elim0 i) |>.1
  let : IsProbabilityMeasure PY := (hΨ 0).2 0 (fun i : Fin 0 => Fin.elim0 i) |>.1
  have hmeasX (k : κ) (r : ℝ) : AEMeasurable
      (fun ω => (fieldChaosMass PX (Φ r) ν (h k) γ ω).toReal) PX :=
    (centeredGaussianField_fieldChaosMass_measurable
      PX (Φ r) (hΦ r) ν (h k) (hh k) γ).ennreal_toReal.aemeasurable
  have hmeasY (k : κ) (r : ℝ) : AEMeasurable
      (fun ω => (fieldChaosMass PY (Ψ r) ν (h k) γ ω).toReal) PY :=
    (centeredGaussianField_fieldChaosMass_measurable
      PY (Ψ r) (hΨ r) ν (h k) (hh k) γ).ennreal_toReal.aemeasurable
  have hZXmeas (k : κ) : AEMeasurable (ZX k) PX := (hXconv k).aemeasurable (hmeasX k)
  have hZYmeas (k : κ) : AEMeasurable (ZY k) PY := (hYconv k).aemeasurable (hmeasY k)
  have hZXnonneg (k : κ) : ∀ᵐ ω ∂PX, 0 ≤ ZX k ω := by
    have hn := (hXconv k).comp tendsto_natCast_atTop_atTop
    obtain ⟨ns, _hns, hae⟩ := hn.exists_seq_tendsto_ae
    filter_upwards [hae] with ω hω
    exact isClosed_Ici.mem_of_tendsto hω
      (Filter.Eventually.of_forall fun n => ENNReal.toReal_nonneg)
  have hZYnonneg (k : κ) : ∀ᵐ ω ∂PY, 0 ≤ ZY k ω := by
    have hn := (hYconv k).comp tendsto_natCast_atTop_atTop
    obtain ⟨ns, _hns, hae⟩ := hn.exists_seq_tendsto_ae
    filter_upwards [hae] with ω hω
    exact isClosed_Ici.mem_of_tendsto hω
      (Filter.Eventually.of_forall fun n => ENNReal.toReal_nonneg)
  let mX : ΩX → κ → ℝ := fun ω k => max (ZX k ω) 0
  let mY : ΩY → κ → ℝ := fun ω k => max (ZY k ω) 0
  have hmXeq : ∀ᵐ ω ∂PX, ∀ k, mX ω k = ZX k ω := by
    filter_upwards [ae_all_iff.2 hZXnonneg] with ω hω
    intro k
    exact max_eq_left (hω k)
  have hmYeq : ∀ᵐ ω ∂PY, ∀ k, mY ω k = ZY k ω := by
    filter_upwards [ae_all_iff.2 hZYnonneg] with ω hω
    intro k
    exact max_eq_left (hω k)
  have hLap (t : κ → ℝ) (ht : ∀ k, 0 ≤ t k) :
      (∫⁻ ω, ENNReal.ofReal (Real.exp (-∑ k, t k * mX ω k)) ∂PX) ≤
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-∑ k, t k * mY ω k)) ∂PY := by
    have h := kahane_limit_field_multi_block_laplace
      PX PY Φ Ψ hΦ hΨ ν h hh hhb γ t ht hcov hdiag ZX ZY hXconv hYconv
    have hEqX : (∫⁻ ω, ENNReal.ofReal (Real.exp (-∑ k, t k * mX ω k)) ∂PX) =
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-∑ k, t k * ZX k ω)) ∂PX := by
      apply lintegral_congr_ae
      filter_upwards [hmXeq] with ω hω
      simp only [hω]
    have hEqY : (∫⁻ ω, ENNReal.ofReal (Real.exp (-∑ k, t k * mY ω k)) ∂PY) =
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-∑ k, t k * ZY k ω)) ∂PY := by
      apply lintegral_congr_ae
      filter_upwards [hmYeq] with ω hω
      simp only [hω]
    rw [hEqX, hEqY]
    exact h
  have h := nonneg_multi_nonpositive_power_le_of_laplace PX PY mX mY
    (fun k => (hZXmeas k).max measurable_const.aemeasurable)
    (fun k => (hZYmeas k).max measurable_const.aemeasurable)
    (fun ω k => le_max_right _ _) (fun ω k => le_max_right _ _) q hq hLap
  have hEqX : (∫⁻ ω, ∏ k, ENNReal.rpow (ENNReal.ofReal (mX ω k)) (-q k) ∂PX) =
      ∫⁻ ω, ∏ k, ENNReal.rpow (ENNReal.ofReal (ZX k ω)) (-q k) ∂PX := by
    apply lintegral_congr_ae
    filter_upwards [hmXeq] with ω hω
    simp only [hω]
  have hEqY : (∫⁻ ω, ∏ k, ENNReal.rpow (ENNReal.ofReal (mY ω k)) (-q k) ∂PY) =
      ∫⁻ ω, ∏ k, ENNReal.rpow (ENNReal.ofReal (ZY k ω)) (-q k) ∂PY := by
    apply lintegral_congr_ae
    filter_upwards [hmYeq] with ω hω
    simp only [hω]
  rwa [hEqX, hEqY] at h



end DOZZ.Proofs
