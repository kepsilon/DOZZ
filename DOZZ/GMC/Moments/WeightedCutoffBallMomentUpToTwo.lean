/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Annulus.PositiveBase
public import DOZZ.GMC.Annulus.CutoffScale
public import DOZZ.GMC.Annulus.BallCover
public import DOZZ.GMC.Moments.WeightedCutoffPositiveSubunit
public import DOZZ.GMC.Moments.WeightedLpFiniteSum

/-! Local finite-cutoff ball moments through the first positive-moment induction step. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

theorem ennreal_lintegral_rpow_const_mul_root_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : ℝ) (hp : 0 < p) (c : ℝ≥0∞) (hc : c < ⊤)
    (f : Ω → ℝ≥0∞) (hf : AEMeasurable f P)
    (hfmom : (∫⁻ ω, ENNReal.rpow (f ω) p ∂P) < ⊤) :
    (∫⁻ ω, ENNReal.rpow (c * f ω) p ∂P) ^ (1 / p) =
      c * (∫⁻ ω, ENNReal.rpow (f ω) p ∂P) ^ (1 / p) := by
  have hp0 : 0 ≤ p := hp.le
  have hpowMeas : AEMeasurable (fun ω => ENNReal.rpow (f ω) p) P :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hf
  have hcPow : c ^ p < ⊤ :=
    lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg hp0 hc.ne)
  have hfactor :
      (∫⁻ ω, ENNReal.rpow (c * f ω) p ∂P) =
        c ^ p * ∫⁻ ω, ENNReal.rpow (f ω) p ∂P := by
    calc
      _ = ∫⁻ ω, c ^ p * ENNReal.rpow (f ω) p ∂P := by
        apply lintegral_congr
        intro ω
        exact ENNReal.mul_rpow_of_nonneg c (f ω) hp0
      _ = _ := lintegral_const_mul'' _ hpowMeas
  have hroot : (c ^ p) ^ (1 / p) = c := by
    rw [← ENNReal.rpow_mul]
    rw [show p * (1 / p) = 1 by field_simp [ne_of_gt hp]]
    exact ENNReal.rpow_one c
  rw [hfactor, ENNReal.mul_rpow_of_ne_top hcPow.ne hfmom.ne, hroot]

private theorem ennreal_ofReal_rpow_of_pos_upto_two {x p : ℝ} (hx : 0 < x) :
    ENNReal.rpow (ENNReal.ofReal x) p = ENNReal.ofReal (x ^ p) := by
  have hx0 : ENNReal.ofReal x ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hx)
  have hleft : ENNReal.rpow (ENNReal.ofReal x) p ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hx0 ENNReal.ofReal_ne_top
  have hright : ENNReal.ofReal (x ^ p) ≠ ⊤ := ENNReal.ofReal_ne_top
  apply (ENNReal.toReal_eq_toReal_iff' hleft hright).1
  calc
    (ENNReal.rpow (ENNReal.ofReal x) p).toReal = (ENNReal.ofReal x).toReal ^ p :=
      (ENNReal.toReal_rpow _ _).symm
    _ = x ^ p := by rw [ENNReal.toReal_ofReal hx.le]
    _ = (ENNReal.ofReal (x ^ p)).toReal :=
      (ENNReal.toReal_ofReal (Real.rpow_nonneg hx.le p)).symm

/-- Extracting a positive real scale from an `ENNReal` moment root. -/
theorem ennreal_root_mul_ofReal_rpow_eq
    (C : ℝ≥0∞) (hC : C < ⊤) (a xi p : ℝ) (ha : 0 < a) (hp : 0 < p) :
    (C * ENNReal.ofReal (a ^ xi)) ^ (1 / p) =
      C ^ (1 / p) * ENNReal.ofReal (a ^ (xi / p)) := by
  have hreal : 0 < a ^ xi := Real.rpow_pos_of_pos ha xi
  calc
    _ = C ^ (1 / p) * ENNReal.rpow (ENNReal.ofReal (a ^ xi)) (1 / p) :=
      ENNReal.mul_rpow_of_ne_top hC.ne ENNReal.ofReal_ne_top _
    _ = C ^ (1 / p) * ENNReal.ofReal ((a ^ xi) ^ (1 / p)) := by
      rw [ennreal_ofReal_rpow_of_pos_upto_two hreal]
    _ = C ^ (1 / p) * ENNReal.ofReal (a ^ (xi / p)) := by
      congr 2
      rw [← Real.rpow_mul ha.le]
      congr 1
      field_simp [ne_of_gt hp]

private theorem weighted_cutoff_rpow_exponent_relation (γ α p : ℝ)
    (hγ : 0 < γ) (hp : 0 < p) :
    -γ * α + (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p =
      weightedCutoffMomentScaleExponent γ α p / p := by
  dsimp [weightedCutoffMomentScaleExponent, Q]
  field_simp [ne_of_gt hγ, ne_of_gt hp]
  ring

theorem weighted_cutoff_core_rpow_identity
    (γ α p δ : ℝ) (hγ : 0 < γ) (hp : 0 < p) (hδ : 0 < δ) :
    δ ^ (-γ * α) * (δ / (1 / 8 : ℝ)) ^
      ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) =
      ((1 / 8 : ℝ)⁻¹) ^
        ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) *
        δ ^ (weightedCutoffMomentScaleExponent γ α p / p) := by
  have hδbase : 0 ≤ δ := hδ.le
  have hrecip : 0 ≤ (1 / 8 : ℝ)⁻¹ := by positivity
  rw [show δ / (1 / 8 : ℝ) = δ * (1 / 8 : ℝ)⁻¹ by field_simp]
  rw [Real.mul_rpow hδbase hrecip]
  calc
    _ = (δ ^ (-γ * α) * δ ^
          ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p)) *
          ((1 / 8 : ℝ)⁻¹) ^
            ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) := by ac_rfl
    _ = δ ^ (-γ * α +
          (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) *
          ((1 / 8 : ℝ)⁻¹) ^
            ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) := by
      rw [← Real.rpow_add hδ]
    _ = _ := by
      rw [weighted_cutoff_rpow_exponent_relation γ α p hγ hp]
      ring

theorem weighted_cutoff_shell_rpow_identity
    (γ α p R : ℝ) (hγ : 0 < γ) (hp : 0 < p) (hR : 0 < R) (n : ℕ) :
    (cutoffDyadicBallRadius R (n + 1)) ^ (-γ * α) *
      (cutoffDyadicBallRadius R n / (1 / 8 : ℝ)) ^
        ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) =
      (2 / (1 / 8 : ℝ)) ^
          ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) *
        R ^ (weightedCutoffMomentScaleExponent γ α p / p) *
          ((1 / 2 : ℝ) ^ (weightedCutoffMomentScaleExponent γ α p / p)) ^ (n + 1) := by
  let ρ : ℝ := cutoffDyadicBallRadius R (n + 1)
  have hρ : 0 < ρ := by dsimp [ρ, cutoffDyadicBallRadius]; positivity
  have hstep : cutoffDyadicBallRadius R n = 2 * ρ := by
    dsimp [ρ, cutoffDyadicBallRadius]
    rw [pow_succ]
    field_simp
  have hratio : cutoffDyadicBallRadius R n / (1 / 8 : ℝ) =
      (2 / (1 / 8 : ℝ)) * ρ := by
    rw [hstep]
    field_simp
  have hrel := weighted_cutoff_rpow_exponent_relation γ α p hγ hp
  have hrad : ρ = R * (1 / 2 : ℝ) ^ (n + 1) := by
    dsimp [ρ, cutoffDyadicBallRadius]
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow]
    field_simp
  calc
    _ = ρ ^ (-γ * α) *
        ((2 / (1 / 8 : ℝ)) ^
          ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) *
          ρ ^ ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p)) := by
      rw [show cutoffDyadicBallRadius R (n + 1) = ρ by rfl, hratio,
        Real.mul_rpow (by positivity) hρ.le]
    _ = (2 / (1 / 8 : ℝ)) ^
          ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) *
        ρ ^ (weightedCutoffMomentScaleExponent γ α p / p) := by
      calc
        _ = (2 / (1 / 8 : ℝ)) ^
            ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) *
            (ρ ^ (-γ * α) * ρ ^
              ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p)) := by ac_rfl
        _ = (2 / (1 / 8 : ℝ)) ^
            ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) *
            ρ ^ (-γ * α +
              (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) := by
          rw [← Real.rpow_add hρ]
        _ = _ := by rw [hrel]
    _ = (2 / (1 / 8 : ℝ)) ^
          ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p) *
        (R ^ (weightedCutoffMomentScaleExponent γ α p / p) *
          ((1 / 2 : ℝ) ^ (weightedCutoffMomentScaleExponent γ α p / p)) ^ (n + 1)) := by
      rw [hrad, Real.mul_rpow hR.le (by positivity)]
      have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
      rw [← Real.rpow_natCast_mul hhalf (n + 1)
          (weightedCutoffMomentScaleExponent γ α p / p)]
      rw [show ((n + 1 : ℕ) : ℝ) *
          (weightedCutoffMomentScaleExponent γ α p / p) =
          (weightedCutoffMomentScaleExponent γ α p / p) * (n + 1 : ℕ) by ring,
        Real.rpow_mul_natCast hhalf]
    _ = _ := by ring


/-- The same first-induction-step cutoff moment bound with one coefficient for every center,
radius, and cutoff whose disk remains in the logarithmic chart. -/
theorem regularizedGMC_openBall_moment_bound_upto_two_uniform_chart
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ p : ℝ) (hγ : 0 < γ) (hp : 1 < p) (hp2 : p ≤ 2)
    (hpcrit : p < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (z : ℂ) (R δ : ℝ),
      0 < R → R ≤ 1 / 8 → 0 < δ → δ ≤ R → ‖z‖ + 2 * R ≤ 1 →
      (∫⁻ ω, ENNReal.rpow
        (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P) ≤
        C * ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^
          (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) := by
  let R₀ : ℝ := 1 / 8
  obtain ⟨C, hC, hbound⟩ := regularizedGMC_reference_positive_moment_uniform_upto_two
    P X hX Xc hXc γ p hγ hp hp2 hpcrit
    (by norm_num [R₀] : 0 < R₀) (by norm_num [R₀] : R₀ ≤ 1 / 8)
  refine ⟨C, hC, ?_⟩
  intro z R δ hR hRsmall hδ hδR hchart
  let t : ℝ := Real.log (1 / δ)
  have hR₀ : 0 < R₀ := by norm_num [R₀]
  have hR₀small : R₀ ≤ 1 / 8 := by norm_num [R₀]
  have hR₀one : R₀ < 1 := by norm_num [R₀]
  have hδeq : Real.exp (-t) = δ := by
    dsimp [t]
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  have hratio : δ * (R₀ / R) ≤ R₀ := by
    have hmul := mul_le_mul_of_nonneg_right hδR (div_nonneg (le_of_lt hR₀) hR.le)
    calc
      δ * (R₀ / R) ≤ R * (R₀ / R) := hmul
      _ = R₀ := by field_simp [ne_of_gt hR]
  have hbase : R₀ + Real.exp (-t) * (R₀ / R) ≤ 1 := by
    rw [hδeq]
    calc
      R₀ + δ * (R₀ / R) ≤ R₀ + R₀ := by
        simpa [add_comm] using add_le_add_left hratio R₀
      _ ≤ 1 := by norm_num [R₀]
  have htarget : ‖z‖ + R + Real.exp (-t) ≤ 1 := by
    rw [hδeq]
    linarith only [hchart, hδR]
  have htbase : 0 ≤ t + Real.log (R / R₀) := by
    have hquot : 1 ≤ R / (δ * R₀) := by
      apply (le_div_iff₀ (mul_pos hδ hR₀)).2
      have hδR₀ : δ * R₀ ≤ R * R₀ :=
        mul_le_mul_of_nonneg_right hδR (le_of_lt hR₀)
      have hR₀le : R * R₀ ≤ R := mul_le_of_le_one_right hR.le hR₀one.le
      simpa using hδR₀.trans hR₀le
    have hlog : 0 ≤ Real.log (R / (δ * R₀)) := Real.log_nonneg hquot
    have hlogmul : Real.log (R / (δ * R₀)) = t + Real.log (R / R₀) := by
      have hmul : (1 / δ) * (R / R₀) = R / (δ * R₀) := by
        field_simp [ne_of_gt hδ, ne_of_gt hR₀]
      rw [← hmul, Real.log_mul (by positivity) (by positivity)]
    rw [← hlogmul]
    exact hlog
  have hscale := regularizedGMC_local_ball_moment_scale P X hX γ Xc hXc z
    (s := R) (R := R₀) (t := t) hR hRsmall hR₀ hR₀one
    (by linarith only [hchart, hR]) hbase htarget p
  have hbaseBound := hbound (t + Real.log (R / R₀)) htbase
  change gmcMassMoment P (regularizedGMC P Xc γ (Real.log (1 / δ)))
    (Metric.ball z R) p ≤ _
  rw [hscale]
  calc
    _ ≤ ENNReal.ofReal ((R / R₀) ^
          (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) * C :=
      mul_le_mul' le_rfl hbaseBound
    _ = _ := by rw [mul_comm]

/-- The uniform ball estimate also controls the `Lᵖ` root of each cutoff ball mass. -/
theorem regularizedGMC_openBall_lp_root_bound_upto_two_uniform_chart
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ p : ℝ) (hγ : 0 < γ) (hp : 1 < p) (hp2 : p ≤ 2)
    (hpcrit : p < 4 / γ ^ 2) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧ ∀ (z : ℂ) (R δ : ℝ),
      0 < R → R ≤ 1 / 8 → 0 < δ → δ ≤ R → ‖z‖ + 2 * R ≤ 1 →
      ((∫⁻ ω, ENNReal.rpow
        (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P) ^
          (1 / p) ≤ A * ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^
            ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p))) ∧
        (∫⁻ ω, ENNReal.rpow
          (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P) < ⊤ := by
  obtain ⟨C, hC, hbound⟩ := regularizedGMC_openBall_moment_bound_upto_two_uniform_chart
    P X hX Xc hXc γ p hγ hp hp2 hpcrit
  let A : ℝ≥0∞ := C ^ (1 / p)
  have hA : A < ⊤ := by
    dsimp [A]
    exact lt_top_iff_ne_top.mpr <| ENNReal.rpow_ne_top_of_nonneg
      (one_div_nonneg.mpr (le_trans zero_le_one hp.le)) hC.ne
  refine ⟨A, hA, ?_⟩
  intro z R δ hR hRsmall hδ hδR hchart
  have hmom := hbound z R δ hR hRsmall hδ hδR hchart
  have hscaleTop : ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^
      (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) < ⊤ := ENNReal.ofReal_lt_top
  have hmomTop : (∫⁻ ω, ENNReal.rpow
      (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P) < ⊤ :=
    lt_of_le_of_lt hmom (ENNReal.mul_lt_top hC hscaleTop)
  constructor
  · have hroot := ENNReal.rpow_le_rpow hmom
      (one_div_nonneg.mpr (le_trans zero_le_one hp.le))
    have hRratio : 0 < R / (1 / 8 : ℝ) := by positivity
    change (∫⁻ ω, ENNReal.rpow
        (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P) ^
          (1 / p) ≤ _
    calc
      _ ≤ (C * ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^
          (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2))) ^ (1 / p) := hroot
      _ = A * ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^
          ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p)) := by
        rw [ennreal_root_mul_ofReal_rpow_eq C hC (R / (1 / 8 : ℝ))
          (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) p hRratio
          (lt_trans zero_lt_one hp)]
  · exact hmomTop

/-- For `p ≥ 1`, the positive-charge cutoff moment is bounded by the finite sum of the `Lᵖ`
sizes of its core and dyadic shell masses. This is the form used with the first induction-step
ball bound to sum the shells uniformly in the cutoff. -/
theorem cutoffWeightedGmcBallMoment_positive_lp_shell_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ α : ℝ) (hγ : 0 < γ) (hα : 0 < α) (z : ℂ) (R δ p : ℝ)
    (N : ℕ) (hR : 0 < R) (hδ : 0 < δ)
    (hNlo : cutoffDyadicBallRadius R (N + 1) ≤ δ)
    (hp : 1 ≤ p) :
    (∫⁻ ω, ENNReal.rpow (cutoffWeightedGmcBallMass P Xc γ α z R δ ω) p ∂P) ^
        (1 / p) ≤
      (∫⁻ ω, (ENNReal.ofReal (δ ^ (-γ * α)) *
        regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z δ)) ^ p ∂P) ^
          (1 / p) +
      ∑ n ∈ Finset.range (N + 1),
        (∫⁻ ω, (cutoffDyadicBallWeight γ α R N n *
          regularizedGMC P Xc γ (Real.log (1 / δ)) ω
            (Metric.ball z (cutoffDyadicBallRadius R n))) ^ p ∂P) ^ (1 / p) := by
  classical
  let core : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (δ ^ (-γ * α)) *
    regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z δ)
  let shell : ℕ → Ω → ℝ≥0∞ := fun n ω => cutoffDyadicBallWeight γ α R N n *
    regularizedGMC P Xc γ (Real.log (1 / δ)) ω
      (Metric.ball z (cutoffDyadicBallRadius R n))
  let term : Option ℕ → Ω → ℝ≥0∞ := fun i ω =>
    match i with
    | none => core ω
    | some n => shell n ω
  let indices : Finset (Option ℕ) :=
    insert none ((Finset.range (N + 1)).image some)
  have hcoreMeas : AEMeasurable core P := by
    dsimp [core]
    exact aemeasurable_const.mul (regularizedGMC_mass_aemeasurable P X hX Xc hXc γ
      (Real.log (1 / δ)) (Metric.ball z δ) Metric.isOpen_ball.measurableSet)
  have hshellMeas (n : ℕ) : AEMeasurable (shell n) P := by
    dsimp [shell]
    exact aemeasurable_const.mul (regularizedGMC_mass_aemeasurable P X hX Xc hXc γ
      (Real.log (1 / δ)) (Metric.ball z (cutoffDyadicBallRadius R n))
      Metric.isOpen_ball.measurableSet)
  have htermMeas : ∀ i ∈ indices, AEMeasurable (term i) P := by
    intro i hi
    cases i with
    | none => exact hcoreMeas
    | some n => exact hshellMeas n
  have htsum (ω : Ω) :
      (∑' n : ℕ, if n ≤ N then
        ENNReal.ofReal ((cutoffDyadicBallRadius R (n + 1)) ^ (-γ * α)) *
          regularizedGMC P Xc γ (Real.log (1 / δ)) ω
            (Metric.ball z (cutoffDyadicBallRadius R n)) else 0) =
        ∑ n ∈ Finset.range (N + 1), shell n ω := by
    rw [tsum_eq_sum (s := Finset.range (N + 1))]
    · apply Finset.sum_congr rfl
      intro n hn
      have hnle : n ≤ N := by
        have : n < N + 1 := Finset.mem_range.mp hn
        omega
      simp [shell, cutoffDyadicBallWeight, hnle]
    · intro n hn
      have hnrange : ¬ n < N + 1 := by
        intro hnlt
        exact hn (Finset.mem_range.mpr hnlt)
      have hnlt : N < n := by
        omega
      have hnle : ¬ n ≤ N := by omega
      simp [hnle]
  have hdecomp (ω : Ω) :
      cutoffWeightedGmcBallMass P Xc γ α z R δ ω ≤
        core ω + ∑ n ∈ Finset.range (N + 1), shell n ω := by
    change (∫⁻ x in Metric.ball z R,
      ENNReal.ofReal ((‖x - z‖ + δ) ^ (-γ * α)) ∂
        regularizedGMC P Xc γ (Real.log (1 / δ)) ω) ≤ _
    have h := cutoffWeightedGmcBallMass_le_positive_dyadic_cover
      (regularizedGMC P Xc γ (Real.log (1 / δ)) ω) γ α z R δ N
      hγ hα hR hδ hNlo
    rw [htsum ω] at h
    simpa [core, shell, cutoffDyadicBallWeight] using h
  have hsum : ∀ ω, ∑ i ∈ indices, term i ω =
      core ω + ∑ n ∈ Finset.range (N + 1), shell n ω := by
    intro ω
    simp [indices, term, core, shell, Finset.sum_image]
  have hpoint (ω : Ω) :
      ENNReal.rpow (cutoffWeightedGmcBallMass P Xc γ α z R δ ω) p ≤
        ENNReal.rpow (∑ i ∈ indices, term i ω) p := by
    rw [hsum]
    exact ENNReal.rpow_le_rpow (hdecomp ω) (le_trans zero_le_one hp)
  calc
    _ ≤ (∫⁻ ω, ENNReal.rpow (∑ i ∈ indices, term i ω) p ∂P) ^ (1 / p) := by
      apply ENNReal.rpow_le_rpow
      · exact lintegral_mono hpoint
      · exact one_div_nonneg.mpr (le_trans zero_le_one hp)
    _ ≤ ∑ i ∈ indices, (∫⁻ ω, ENNReal.rpow (term i ω) p ∂P) ^ (1 / p) :=
      ennreal_lintegral_rpow_finset_sum_root_le indices term p hp htermMeas
    _ = _ := by
      simp [indices, term, Finset.sum_image, core, shell]

theorem regularizedGMC_openBall_moment_bound_upto_two_large_chart
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ p : ℝ) (hγ : 0 < γ) (hp : 1 < p) (hp2 : p ≤ 2)
    (hpcrit : p < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (z : ℂ) (R δ : ℝ),
      1 / 8 ≤ R → R ≤ 1 / 2 → 0 < δ → δ ≤ R → ‖z‖ + 2 * R ≤ 1 →
      (∫⁻ ω, ENNReal.rpow
        (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P) ≤ C := by
  classical
  let r₀ : ℝ := 1 / 32
  let K : Set ℂ := Metric.closedBall 0 (7 / 8 : ℝ)
  let U : Type := {w : ℂ // w ∈ K}
  obtain ⟨S, hcover⟩ := (isCompact_closedBall (0 : ℂ) (7 / 8 : ℝ)).elim_finite_subcover
    (fun w : U => Metric.ball (w : ℂ) r₀) (fun _ => Metric.isOpen_ball)
    (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (by norm_num [r₀])⟩)
  have hSne : S.Nonempty := by
    have hzero : (0 : ℂ) ∈ K := by simp [K]; positivity
    have hc := hcover hzero
    simp only [Set.mem_iUnion] at hc
    obtain ⟨w, hwS, _⟩ := hc
    exact ⟨w, hwS⟩
  have hr₀pos : 0 < r₀ := by norm_num [r₀]
  have hr₀small : r₀ ≤ 1 / 8 := by norm_num [r₀]
  have hsmallChart : ∀ w : U, ‖(w : ℂ)‖ + 2 * r₀ ≤ 1 := by
    intro w
    have hw : ‖(w : ℂ)‖ ≤ 7 / 8 := by
      have hwmem : (w : ℂ) ∈ Metric.closedBall 0 (7 / 8 : ℝ) := w.property
      simpa only [Metric.mem_closedBall, dist_zero_right] using hwmem
    norm_num [r₀] at hw ⊢
    linarith only [hw]
  obtain ⟨Csmall, hCsmall, hsmall⟩ :=
    regularizedGMC_openBall_moment_bound_upto_two_uniform_chart
      P X hX Xc hXc γ p hγ hp hp2 hpcrit
  let Hcover : ℝ≥0∞ := Csmall * ENNReal.ofReal
    ((r₀ / (1 / 8 : ℝ)) ^ (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2))
  have hHcover : Hcover < ⊤ := by
    dsimp [Hcover]
    exact ENNReal.mul_lt_top hCsmall ENNReal.ofReal_lt_top
  let Ccover : ℝ≥0∞ := (S.card : ℝ≥0∞) ^ p * (S.card : ℝ≥0∞) * Hcover
  have hCcover : Ccover < ⊤ := by
    dsimp [Ccover]
    have hcardpow : (S.card : ℝ≥0∞) ^ p < ⊤ :=
      lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg (by linarith only [hp])
        (ENNReal.natCast_ne_top S.card))
    have hcard : (S.card : ℝ≥0∞) < ⊤ :=
      lt_top_iff_ne_top.mpr (ENNReal.natCast_ne_top S.card)
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top hcardpow hcard) hHcover
  let T : ℝ := Real.log 32
  let Ccoarse : ℝ≥0∞ :=
    (gmcReferenceMeasure Set.univ) ^ p * ENNReal.ofReal
      (Real.exp (γ ^ 2 * (p ^ 2 - p) / 2 * (T + gmcCircleChartRemainder 1)))
  have hCcoarse : Ccoarse < ⊤ := by
    dsimp [Ccoarse]
    have hrefpow : (gmcReferenceMeasure Set.univ) ^ p < ⊤ :=
      lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg (by linarith only [hp])
        gmcReferenceMeasure_univ_ne_top)
    exact ENNReal.mul_lt_top
      hrefpow ENNReal.ofReal_lt_top
  let C : ℝ≥0∞ := Ccover + Ccoarse
  have hC : C < ⊤ := by
    dsimp [C]
    exact ENNReal.add_lt_top.mpr ⟨hCcover, hCcoarse⟩
  refine ⟨C, hC, ?_⟩
  intro z R δ hRlo hRhi hδ hδR hchart
  let t : ℝ := Real.log (1 / δ)
  have ht0 : 0 ≤ t := by
    dsimp [t]
    apply Real.log_nonneg
    have hδhalf : δ ≤ 1 / 2 := hδR.trans hRhi
    exact (one_le_div₀ hδ).2 (by linarith only [hδhalf])
  by_cases hδcoarse : 1 / 32 < δ
  · have hδupper : 1 / δ ≤ 32 := by
      apply (div_le_iff₀ hδ).2
      linarith only [hδcoarse]
    have htT : t ≤ T := by
      dsimp [t, T]
      exact Real.log_le_log (one_div_pos.mpr hδ) hδupper
    have hballChart : ∀ x ∈ Metric.ball z R, ‖x‖ ≤ 1 := by
      intro x hx
      have hdist : ‖x - z‖ < R := by
        simpa only [Metric.mem_ball, dist_eq_norm] using hx
      have hnorm : ‖x‖ ≤ ‖z‖ + ‖x - z‖ := by
        calc
          ‖x‖ = ‖(x - z) + z‖ := by congr 1; abel
          _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
          _ = ‖z‖ + ‖x - z‖ := by ring
      have hzR : ‖z‖ + R ≤ 1 := by linarith only [hchart, hRlo]
      exact le_trans hnorm (by linarith only [hzR, hdist])
    have hcoarse := regularizedGMC_coarse_chart_moment_upper P X hX Xc hXc γ 1 T p
      (by norm_num) (by linarith only [hp]) (Metric.ball z R) Metric.isOpen_ball.measurableSet
      hballChart t ht0 htT
    have hmeasure : gmcReferenceMeasure (Metric.ball z R) ≤ gmcReferenceMeasure Set.univ :=
      measure_mono (Set.subset_univ _)
    have hpow := ENNReal.rpow_le_rpow hmeasure (by linarith only [hp] : 0 ≤ p)
    dsimp [t, Ccoarse] at hcoarse ⊢
    have hcoarse' := hcoarse.trans (mul_le_mul_of_nonneg_right hpow (by positivity))
    dsimp [C]
    exact hcoarse'.trans (le_add_of_nonneg_left (by positivity))
  · have hδsmall : δ ≤ r₀ := by
      dsimp [r₀]
      exact not_lt.mp hδcoarse
    have htargetDisk : Metric.ball z R ⊆ K := by
      intro x hx
      have hdist : ‖x - z‖ < R := by
        simpa only [Metric.mem_ball, dist_eq_norm] using hx
      have hnorm : ‖x‖ ≤ ‖z‖ + ‖x - z‖ := by
        calc
          ‖x‖ = ‖(x - z) + z‖ := by congr 1; abel
          _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
          _ = ‖z‖ + ‖x - z‖ := by ring
      have hRnorm : ‖z‖ + R ≤ 7 / 8 := by
        have : 1 / 8 ≤ R := hRlo
        linarith only [hchart, this]
      have hxnorm : ‖x‖ ≤ 7 / 8 := le_trans hnorm (by linarith only [hRnorm, hdist])
      simpa [K, Metric.mem_closedBall, dist_zero_right] using hxnorm
    let μ : Ω → Measure ℂ := regularizedGMC P Xc γ t
    let f : U → Ω → ℝ≥0∞ := fun w ω => μ ω (Metric.ball (w : ℂ) r₀)
    have hmass : ∀ ω, μ ω (Metric.ball z R) ≤ ∑ w ∈ S, f w ω := by
      intro ω
      calc
        μ ω (Metric.ball z R) ≤ μ ω (⋃ w ∈ S, Metric.ball (w : ℂ) r₀) := by
          apply measure_mono
          exact htargetDisk.trans hcover
        _ ≤ ∑ w ∈ S, μ ω (Metric.ball (w : ℂ) r₀) := measure_biUnion_finset_le _ _
    have hmeas (w : U) : AEMeasurable (fun ω => (f w ω) ^ p) P := by
      exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
        ((regularizedGMC_mass_aemeasurable P X hX Xc hXc γ t
          (Metric.ball (w : ℂ) r₀) Metric.isOpen_ball.measurableSet))
    have hlocal (w : U) : (∫⁻ ω, (f w ω) ^ p ∂P) ≤ Hcover := by
      dsimp [f, μ, Hcover]
      have hwchart := hsmallChart w
      simpa [r₀, t] using hsmall (w : ℂ) r₀ δ hr₀pos hr₀small hδ hδsmall hwchart
    have hsumMeas : AEMeasurable (fun ω => ∑ w ∈ S, f w ω ^ p) P :=
      Finset.aemeasurable_fun_sum _ fun w hw => hmeas w
    have hmoment : (∫⁻ ω, (μ ω (Metric.ball z R)) ^ p ∂P) ≤ Ccover := by
      calc
        _ ≤ ∫⁻ ω, ((S.card : ℝ≥0∞) ^ p) * ∑ w ∈ S, (f w ω) ^ p ∂P := by
          apply lintegral_mono
          intro ω
          exact (ENNReal.rpow_le_rpow (hmass ω) (by linarith only [hp])).trans
            (ennreal_finset_sum_rpow_le_card_rpow_sum S hSne (fun w => f w ω) p
              (by linarith only [hp]))
        _ = (S.card : ℝ≥0∞) ^ p * ∑ w ∈ S, ∫⁻ ω, (f w ω) ^ p ∂P := by
          rw [lintegral_const_mul'' _ hsumMeas,
            lintegral_finsetSum' S (f := fun w ω => (f w ω) ^ p)
              (fun w hw => hmeas w)]
        _ ≤ (S.card : ℝ≥0∞) ^ p * ∑ _w ∈ S, Hcover := by
          gcongr
          exact hlocal _
        _ = Ccover := by simp [Ccover]; ac_rfl
    dsimp [C]
    exact hmoment.trans (le_add_of_nonneg_right (by positivity))

/-- The cutoff ball's `Lᵖ` root has the sharp small-scale factor on every chart radius up to
`1/2`. For radii above `1/8`, the finite-cover moment bound is absorbed into that factor. -/
theorem regularizedGMC_openBall_lp_root_bound_upto_two_uniform_chart_all_radius
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ p : ℝ) (hγ : 0 < γ) (hp : 1 < p) (hp2 : p ≤ 2)
    (hpcrit : p < 4 / γ ^ 2) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧ ∀ (z : ℂ) (R δ : ℝ),
      0 < R → R ≤ 1 / 2 → 0 < δ → δ ≤ R → ‖z‖ + 2 * R ≤ 1 →
      (((∫⁻ ω, ENNReal.rpow
        (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P) ^
          (1 / p) ≤ A * ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^
            ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p))) ∧
        (∫⁻ ω, ENNReal.rpow
          (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P) < ⊤) := by
  have hpcrit' : γ ^ 2 * p < 4 := by
    have h := (lt_div_iff₀ (sq_pos_of_pos hγ)).mp hpcrit
    linarith only [h]
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hxi : 0 < 2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2 := by
    have hfactor : 0 < 2 + γ ^ 2 / 2 - γ ^ 2 * p / 2 := by
      linarith only [hpcrit', sq_nonneg γ]
    exact (mul_pos hp0 hfactor).trans_eq (by ring)
  let beta : ℝ := (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p
  have hbeta : 0 < beta := div_pos hxi (by linarith only [hp])
  obtain ⟨Asmall, hAsmall, hsmall⟩ :=
    regularizedGMC_openBall_lp_root_bound_upto_two_uniform_chart
      P X hX Xc hXc γ p hγ hp hp2 hpcrit
  obtain ⟨Cbig, hCbig, hbig⟩ :=
    regularizedGMC_openBall_moment_bound_upto_two_large_chart
      P X hX Xc hXc γ p hγ hp hp2 hpcrit
  let Abig : ℝ≥0∞ := Cbig ^ (1 / p)
  have hAbig : Abig < ⊤ := by
    dsimp [Abig]
    exact lt_top_iff_ne_top.mpr <| ENNReal.rpow_ne_top_of_nonneg
      (one_div_nonneg.mpr (by linarith only [hp])) hCbig.ne
  let A : ℝ≥0∞ := Asmall + Abig
  have hA : A < ⊤ := by
    dsimp [A]
    exact ENNReal.add_lt_top.mpr ⟨hAsmall, hAbig⟩
  refine ⟨A, hA, ?_⟩
  intro z R δ hR hRhi hδ hδR hchart
  by_cases hRsmall : R ≤ 1 / 8
  · obtain ⟨hroot, htop⟩ := hsmall z R δ hR hRsmall hδ hδR hchart
    constructor
    · exact hroot.trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (by positivity)) (by positivity))
    · exact htop
  · have hRlo : 1 / 8 ≤ R := le_of_not_ge hRsmall
    have hmoment := hbig z R δ hRlo hRhi hδ hδR hchart
    have hroot :
        (∫⁻ ω, ENNReal.rpow
          (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P) ^
            (1 / p) ≤ Abig := by
      dsimp [Abig]
      exact ENNReal.rpow_le_rpow hmoment (one_div_nonneg.mpr (by linarith only [hp]))
    have hratio : 1 ≤ R / (1 / 8 : ℝ) := (one_le_div₀ (by norm_num)).2 hRlo
    have hscaleReal : 1 ≤ (R / (1 / 8 : ℝ)) ^ beta := Real.one_le_rpow hratio hbeta.le
    have hscale : 1 ≤ ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^ beta) := by
      exact ENNReal.one_le_ofReal.mpr hscaleReal
    have hAbigA : Abig ≤ A := by
      dsimp [A]
      exact le_add_of_nonneg_left (by positivity)
    refine ⟨?_, lt_of_le_of_lt hmoment hCbig⟩
    calc
      _ ≤ Abig := hroot
      _ ≤ A := hAbigA
      _ = A * 1 := by simp
      _ ≤ A * ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^ beta) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = _ := by rfl

/-- The scale-free dyadic shell coefficient for a positive insertion, with a chosen uniform
annular exponent margin. -/
noncomputable def cutoffWeightedPositiveScaleRootBoundConstant
    (A : ℝ≥0∞) (γ p ε : ℝ) : ℝ≥0∞ :=
  A * (ENNReal.ofReal (((1 / 8 : ℝ)⁻¹) ^
      ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p)) +
    ENNReal.ofReal ((2 / (1 / 8 : ℝ)) ^
      ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p)) *
      ENNReal.ofReal ((1 / 2 : ℝ) ^ ε) *
      (1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ ε))⁻¹)

/-- A shared cutoff-ball root estimate and a uniform positive annular margin give an explicit
positive-charge cutoff moment constant at every `p > 1`. The unweighted root estimate is the only
input that may restrict the order. -/
theorem cutoffWeightedGmcBallMoment_positive_scale_of_ball_root_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ α p : ℝ) (hγ : 0 < γ) (hα : 0 < α)
    (hp : 1 < p)
    (hpRange : p < min (4 / γ ^ 2) (2 / γ * (Q γ - α)))
    (ε : ℝ) (hε : 0 < ε)
    (hεbeta : ε ≤ weightedCutoffMomentScaleExponent γ α p / p)
    (A : ℝ≥0∞) (hA : A < ⊤)
    (hballRoot : ∀ (z : ℂ) (R δ : ℝ),
      0 < R → R ≤ 1 / 2 → 0 < δ → δ ≤ R → ‖z‖ + 2 * R ≤ 1 →
      (((∫⁻ ω, ENNReal.rpow
        (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P) ^
          (1 / p) ≤ A * ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^
            ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p))) ∧
        (∫⁻ ω, ENNReal.rpow
          (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P) < ⊤)) :
    cutoffWeightedPositiveScaleRootBoundConstant A γ p ε ^ p < ⊤ ∧
      ∀ z : ℂ, ∀ R : ℝ,
      0 < R → R ≤ 1 / 2 → ‖z‖ + 2 * R ≤ 1 →
      ∀ δ : ℝ, 0 < δ → δ ≤ R →
      (∫⁻ ω, ENNReal.rpow
        (cutoffWeightedGmcBallMass P Xc γ α z R δ ω) p ∂P) ≤
        cutoffWeightedPositiveScaleRootBoundConstant A γ p ε ^ p * ENNReal.ofReal
          (R ^ weightedCutoffMomentScaleExponent γ α p) := by
  classical
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpcrit : p < 4 / γ ^ 2 := lt_of_lt_of_le hpRange (min_le_left _ _)
  have heta : 0 < weightedCutoffMomentScaleExponent γ α p :=
    weightedGmcMomentExponent_pos_of_sharp_range hγ hp0 hpRange
  let xi : ℝ := 2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2
  let beta : ℝ := weightedCutoffMomentScaleExponent γ α p / p
  have hbeta : 0 < beta := div_pos heta hp0
  have hεbeta' : ε ≤ beta := by simpa [beta] using hεbeta
  have hxi : 0 < xi := by
    dsimp [xi]
    have hcrit' : γ ^ 2 * p < 4 := by
      have h := (lt_div_iff₀ (sq_pos_of_pos hγ)).mp hpcrit
      linarith only [h]
    have hfactor : 0 < 2 + γ ^ 2 / 2 - γ ^ 2 * p / 2 := by
      linarith only [hcrit', sq_nonneg γ]
    exact (mul_pos hp0 hfactor).trans_eq (by ring)
  have hxiBeta : 0 < xi / p := div_pos hxi hp0
  let halfRatioReal : ℝ := (1 / 2 : ℝ) ^ beta
  let halfRatio : ℝ≥0∞ := ENNReal.ofReal halfRatioReal
  let halfRatio0Real : ℝ := (1 / 2 : ℝ) ^ ε
  let halfRatio0 : ℝ≥0∞ := ENNReal.ofReal halfRatio0Real
  let coreCoefReal : ℝ := ((1 / 8 : ℝ)⁻¹) ^ (xi / p)
  let shellCoefReal : ℝ := (2 / (1 / 8 : ℝ)) ^ (xi / p)
  have hhalfRatioPos : 0 < halfRatioReal := by
    dsimp [halfRatioReal]
    exact Real.rpow_pos_of_pos (by norm_num) beta
  have hhalfRatioLt : halfRatioReal < 1 := by
    dsimp [halfRatioReal]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) hbeta
  have hhalfRatio : halfRatio < 1 :=
    ENNReal.ofReal_lt_one.mpr (by simpa [halfRatio] using hhalfRatioLt)
  have hhalfRatio0Lt : halfRatio0Real < 1 := by
    dsimp [halfRatio0Real]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) hε
  have hhalfRatio0 : halfRatio0 < 1 :=
    ENNReal.ofReal_lt_one.mpr (by simpa [halfRatio0] using hhalfRatio0Lt)
  have hratioReal : halfRatioReal ≤ halfRatio0Real := by
    dsimp [halfRatioReal, halfRatio0Real]
    exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hεbeta'
  have hratio : halfRatio ≤ halfRatio0 := ENNReal.ofReal_le_ofReal hratioReal
  have hden : 1 - halfRatio0 ≠ 0 := by
    intro h
    exact (not_le_of_gt hhalfRatio0) (tsub_eq_zero_iff_le.mp h)
  have hgeomTop : (1 - halfRatio0)⁻¹ < ⊤ :=
    lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr hden)
  have hhalfRatio0Top : halfRatio0 < ⊤ := ENNReal.ofReal_lt_top
  have hcoreCoefPos : 0 < coreCoefReal := by
    dsimp [coreCoefReal]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hcoreCoefTop : ENNReal.ofReal coreCoefReal < ⊤ := ENNReal.ofReal_lt_top
  have hshellCoefPos : 0 < shellCoefReal := by
    dsimp [shellCoefReal]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hshellCoefTop : ENNReal.ofReal shellCoefReal < ⊤ := ENNReal.ofReal_lt_top
  let D : ℝ≥0∞ := ENNReal.ofReal coreCoefReal +
    ENNReal.ofReal shellCoefReal * halfRatio0 * (1 - halfRatio0)⁻¹
  let K : ℝ≥0∞ := A * D
  have hD : D < ⊤ := by
    dsimp [D]
    exact ENNReal.add_lt_top.mpr ⟨hcoreCoefTop,
      ENNReal.mul_lt_top (ENNReal.mul_lt_top hshellCoefTop hhalfRatio0Top) hgeomTop⟩
  have hK : K < ⊤ := by
    dsimp [K]
    exact ENNReal.mul_lt_top hA hD
  have hKeq : K = cutoffWeightedPositiveScaleRootBoundConstant A γ p ε := by
    simp [K, D, cutoffWeightedPositiveScaleRootBoundConstant, coreCoefReal,
      shellCoefReal, halfRatio0, halfRatio0Real, xi]
  refine ⟨?_, ?_⟩
  · rw [← hKeq]
    exact lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg hp0.le hK.ne)
  · intro z R hR hRsmall hchart δ hδ hδR
    obtain ⟨N, hNlo, hNhi⟩ : ∃ N : ℕ,
        cutoffDyadicBallRadius R (N + 1) ≤ δ ∧ δ ≤ cutoffDyadicBallRadius R N := by
      by_cases hδeq : δ = R
      · refine ⟨0, ?_, ?_⟩
        · have hRhalf : R / 2 ≤ R := by
            apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
            linarith only [hR]
          simpa [cutoffDyadicBallRadius, hδeq] using hRhalf
        · rw [hδeq]
          simp [cutoffDyadicBallRadius]
      · have hδlt : δ < R := lt_of_le_of_ne hδR hδeq
        obtain ⟨N, hlow, hhigh⟩ := exists_dyadic_shell_index hδ hδlt
        exact ⟨N, hlow, hhigh.le⟩
    have hδchart : ‖z‖ + 2 * δ ≤ 1 := by linarith only [hchart, hδR]
    have hcoreBase := hballRoot z δ δ hδ (le_trans hδR hRsmall) hδ le_rfl hδchart
    let coreMass : Ω → ℝ≥0∞ := fun ω =>
      regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z δ)
    let coreCoeff : ℝ≥0∞ := ENNReal.ofReal (δ ^ (-γ * α))
    have hcoreId : δ ^ (-γ * α) * (δ / (1 / 8 : ℝ)) ^ (xi / p) =
        coreCoefReal * δ ^ beta := by
      simpa [xi, beta, coreCoefReal] using
        (weighted_cutoff_core_rpow_identity γ α p δ hγ hp0 hδ)
    have hcoreMassMeas : AEMeasurable coreMass P := by
      exact regularizedGMC_mass_aemeasurable P X hX Xc hXc γ (Real.log (1 / δ))
        (Metric.ball z δ) Metric.isOpen_ball.measurableSet
    have hcoreRoot :
        (∫⁻ ω, (coreCoeff * coreMass ω) ^ p ∂P) ^ (1 / p) ≤
          A * ENNReal.ofReal coreCoefReal * ENNReal.ofReal (R ^ beta) := by
      have hrootEq := ennreal_lintegral_rpow_const_mul_root_eq p hp0 coreCoeff
        ENNReal.ofReal_lt_top coreMass hcoreMassMeas hcoreBase.2
      have hrealBound :
          δ ^ (-γ * α) * (δ / (1 / 8 : ℝ)) ^ (xi / p) ≤
            coreCoefReal * R ^ beta := by
        rw [hcoreId]
        have hmon : δ ^ (weightedCutoffMomentScaleExponent γ α p / p) ≤
            R ^ (weightedCutoffMomentScaleExponent γ α p / p) :=
          Real.rpow_le_rpow hδ.le hδR hbeta.le
        exact mul_le_mul_of_nonneg_left hmon (le_of_lt hcoreCoefPos)
      have hrealNonneg : 0 ≤ δ ^ (-γ * α) := Real.rpow_nonneg hδ.le _
      have hscaleRealNonneg : 0 ≤ (δ / (1 / 8 : ℝ)) ^ (xi / p) := by positivity
      have hcoeffBound :
          ENNReal.ofReal (δ ^ (-γ * α)) *
            ENNReal.ofReal ((δ / (1 / 8 : ℝ)) ^ (xi / p)) ≤
              ENNReal.ofReal (coreCoefReal * R ^ beta) := by
        rw [← ENNReal.ofReal_mul hrealNonneg]
        exact ENNReal.ofReal_le_ofReal hrealBound
      calc
        _ = coreCoeff * (∫⁻ ω, ENNReal.rpow (coreMass ω) p ∂P) ^ (1 / p) := hrootEq
        _ ≤ coreCoeff * (A * ENNReal.ofReal ((δ / (1 / 8 : ℝ)) ^ (xi / p))) :=
          mul_le_mul_of_nonneg_left hcoreBase.1 (by positivity)
        _ = A * (coreCoeff * ENNReal.ofReal
            ((δ / (1 / 8 : ℝ)) ^ (xi / p))) := by ac_rfl
        _ ≤ A * ENNReal.ofReal (coreCoefReal * R ^ beta) :=
          mul_le_mul_of_nonneg_left hcoeffBound (by positivity)
        _ = A * ENNReal.ofReal coreCoefReal * ENNReal.ofReal (R ^ beta) := by
          rw [ENNReal.ofReal_mul (le_of_lt hcoreCoefPos)]
          ac_rfl
    let shellMass (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
      regularizedGMC P Xc γ (Real.log (1 / δ)) ω
        (Metric.ball z (cutoffDyadicBallRadius R n))
    let shellCoeff (n : ℕ) : ℝ≥0∞ := cutoffDyadicBallWeight γ α R N n
    have hshellRoot (n : ℕ) (hn : n ∈ Finset.range (N + 1)) :
        (∫⁻ ω, (shellCoeff n * shellMass n ω) ^ p ∂P) ^ (1 / p) ≤
          A * ENNReal.ofReal shellCoefReal * ENNReal.ofReal (R ^ beta) *
            halfRatio ^ (n + 1) := by
      have hnle : n ≤ N := by
        have hnlt : n < N + 1 := Finset.mem_range.mp hn
        omega
      have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ N :=
        pow_le_pow_right₀ (by norm_num) hnle
      have hradN : cutoffDyadicBallRadius R N ≤ cutoffDyadicBallRadius R n := by
        dsimp [cutoffDyadicBallRadius]
        exact div_le_div_of_nonneg_left hR.le (by positivity) hpow
      have hδn : δ ≤ cutoffDyadicBallRadius R n := hNhi.trans hradN
      have hRn : cutoffDyadicBallRadius R n ≤ R := by
        dsimp [cutoffDyadicBallRadius]
        apply (div_le_iff₀ (by positivity)).2
        have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
        exact le_mul_of_one_le_right hR.le hpow1
      have hchartn : ‖z‖ + 2 * cutoffDyadicBallRadius R n ≤ 1 := by
        linarith only [hchart, hRn]
      have hρpos : 0 < cutoffDyadicBallRadius R n := by
        dsimp [cutoffDyadicBallRadius]
        positivity
      have hmassBase := hballRoot z (cutoffDyadicBallRadius R n) δ
        hρpos (hRn.trans hRsmall) hδ hδn hchartn
      have hmassMeas : AEMeasurable (shellMass n) P := by
        exact regularizedGMC_mass_aemeasurable P X hX Xc hXc γ (Real.log (1 / δ))
          (Metric.ball z (cutoffDyadicBallRadius R n)) Metric.isOpen_ball.measurableSet
      have hρnext : 0 < cutoffDyadicBallRadius R (n + 1) := by
        dsimp [cutoffDyadicBallRadius]
        positivity
      have hcoeffR : cutoffDyadicBallRadius R (n + 1) ^ (-γ * α) > 0 :=
        Real.rpow_pos_of_pos hρnext _
      have hcoeff : shellCoeff n = ENNReal.ofReal
          (cutoffDyadicBallRadius R (n + 1) ^ (-γ * α)) := by
        simp [shellCoeff, cutoffDyadicBallWeight, hnle]
      rw [hcoeff]
      have hrootEq := ennreal_lintegral_rpow_const_mul_root_eq p hp0
        (ENNReal.ofReal (cutoffDyadicBallRadius R (n + 1) ^ (-γ * α)))
        ENNReal.ofReal_lt_top (shellMass n) hmassMeas hmassBase.2
      have hrealEq := weighted_cutoff_shell_rpow_identity γ α p R hγ hp0 hR n
      have hrealSplit :
          ENNReal.ofReal
            ((2 / (1 / 8 : ℝ)) ^ (xi / p) * R ^ beta *
              ((1 / 2 : ℝ) ^ beta) ^ (n + 1)) =
            ENNReal.ofReal shellCoefReal * ENNReal.ofReal (R ^ beta) *
              halfRatio ^ (n + 1) := by
        dsimp [shellCoefReal, halfRatio, halfRatioReal, beta, xi]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow (by positivity)]
      have hrealNonneg : 0 ≤ cutoffDyadicBallRadius R (n + 1) ^ (-γ * α) :=
        Real.rpow_nonneg hρnext.le _
      have hrealForm :
          ENNReal.ofReal (cutoffDyadicBallRadius R (n + 1) ^ (-γ * α)) *
            ENNReal.ofReal ((cutoffDyadicBallRadius R n / (1 / 8 : ℝ)) ^ (xi / p)) =
          ENNReal.ofReal shellCoefReal * ENNReal.ofReal (R ^ beta) *
            halfRatio ^ (n + 1) := by
        rw [← ENNReal.ofReal_mul hrealNonneg, hrealEq]
        exact hrealSplit
      calc
        _ = ENNReal.ofReal
            (cutoffDyadicBallRadius R (n + 1) ^ (-γ * α)) *
              (∫⁻ ω, ENNReal.rpow (shellMass n ω) p ∂P) ^ (1 / p) := hrootEq
        _ ≤ ENNReal.ofReal
            (cutoffDyadicBallRadius R (n + 1) ^ (-γ * α)) *
              (A * ENNReal.ofReal
                ((cutoffDyadicBallRadius R n / (1 / 8 : ℝ)) ^ (xi / p))) :=
          mul_le_mul_of_nonneg_left hmassBase.1 (by positivity)
        _ = A * (ENNReal.ofReal
              (cutoffDyadicBallRadius R (n + 1) ^ (-γ * α)) *
                ENNReal.ofReal
                  ((cutoffDyadicBallRadius R n / (1 / 8 : ℝ)) ^ (xi / p))) := by ac_rfl
        _ = A * (ENNReal.ofReal shellCoefReal * ENNReal.ofReal (R ^ beta) *
              halfRatio ^ (n + 1)) := by rw [hrealForm]
        _ = _ := by ac_rfl
    have hseries : (∑' n : ℕ, halfRatio ^ (n + 1)) =
        halfRatio * (1 - halfRatio)⁻¹ := by
      calc
        _ = ∑' n : ℕ, halfRatio * halfRatio ^ n := by
          apply tsum_congr
          intro n
          rw [pow_succ]
          ac_rfl
        _ = halfRatio * ∑' n : ℕ, halfRatio ^ n := ENNReal.tsum_mul_left
        _ = _ := by rw [ENNReal.tsum_geometric]
    have hshellSumActual :
        (∑ n ∈ Finset.range (N + 1),
          (∫⁻ ω, (shellCoeff n * shellMass n ω) ^ p ∂P) ^ (1 / p)) ≤
          A * ENNReal.ofReal shellCoefReal * ENNReal.ofReal (R ^ beta) *
            (halfRatio * (1 - halfRatio)⁻¹) := by
      calc
        _ ≤ ∑ n ∈ Finset.range (N + 1),
            A * ENNReal.ofReal shellCoefReal * ENNReal.ofReal (R ^ beta) *
              halfRatio ^ (n + 1) := by
          apply Finset.sum_le_sum
          intro n hn
          exact hshellRoot n hn
        _ ≤ ∑' n : ℕ,
            A * ENNReal.ofReal shellCoefReal * ENNReal.ofReal (R ^ beta) *
              halfRatio ^ (n + 1) := ENNReal.sum_le_tsum _
        _ = A * ENNReal.ofReal shellCoefReal * ENNReal.ofReal (R ^ beta) *
            (halfRatio * (1 - halfRatio)⁻¹) := by
          calc
            _ = ∑' n : ℕ,
                (A * ENNReal.ofReal shellCoefReal * ENNReal.ofReal (R ^ beta) * halfRatio) *
                  halfRatio ^ n := by
              apply tsum_congr
              intro n
              rw [pow_succ]
              ac_rfl
            _ = (A * ENNReal.ofReal shellCoefReal * ENNReal.ofReal (R ^ beta) * halfRatio) *
                ∑' n : ℕ, halfRatio ^ n := ENNReal.tsum_mul_left
            _ = _ := by rw [ENNReal.tsum_geometric]; ac_rfl
    have hgeomCompare : halfRatio * (1 - halfRatio)⁻¹ ≤
        halfRatio0 * (1 - halfRatio0)⁻¹ := by
      have hdenom : 1 - halfRatio0 ≤ 1 - halfRatio :=
        tsub_le_tsub_left hratio 1
      have hinv : (1 - halfRatio)⁻¹ ≤ (1 - halfRatio0)⁻¹ := by
        apply ENNReal.inv_le_inv'
        exact hdenom
      calc
        _ ≤ halfRatio0 * (1 - halfRatio)⁻¹ :=
          mul_le_mul_of_nonneg_right hratio (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by positivity)
    have hshellSum :
        (∑ n ∈ Finset.range (N + 1),
          (∫⁻ ω, (shellCoeff n * shellMass n ω) ^ p ∂P) ^ (1 / p)) ≤
          A * ENNReal.ofReal shellCoefReal * ENNReal.ofReal (R ^ beta) *
            (halfRatio0 * (1 - halfRatio0)⁻¹) := by
      exact hshellSumActual.trans
        (mul_le_mul_of_nonneg_left hgeomCompare (by positivity))
    have hdecomp := cutoffWeightedGmcBallMoment_positive_lp_shell_bound
      P X hX Xc hXc γ α hγ hα z R δ p N hR hδ hNlo hp.le
    have hrootBound :
        (∫⁻ ω, ENNReal.rpow
          (cutoffWeightedGmcBallMass P Xc γ α z R δ ω) p ∂P) ^ (1 / p) ≤
          K * ENNReal.ofReal (R ^ beta) := by
      calc
        _ ≤ (∫⁻ ω, (coreCoeff * coreMass ω) ^ p ∂P) ^ (1 / p) +
            ∑ n ∈ Finset.range (N + 1),
              (∫⁻ ω, (shellCoeff n * shellMass n ω) ^ p ∂P) ^ (1 / p) := hdecomp
        _ ≤ A * ENNReal.ofReal coreCoefReal * ENNReal.ofReal (R ^ beta) +
            A * ENNReal.ofReal shellCoefReal * ENNReal.ofReal (R ^ beta) *
              (halfRatio0 * (1 - halfRatio0)⁻¹) :=
          add_le_add hcoreRoot hshellSum
        _ = K * ENNReal.ofReal (R ^ beta) := by
          dsimp [K, D]
          ring
    have hleftPow :
        ((∫⁻ ω, ENNReal.rpow
          (cutoffWeightedGmcBallMass P Xc γ α z R δ ω) p ∂P) ^ (1 / p)) ^ p =
            ∫⁻ ω, ENNReal.rpow
              (cutoffWeightedGmcBallMass P Xc γ α z R δ ω) p ∂P := by
      rw [← ENNReal.rpow_mul]
      rw [show 1 / p * p = 1 by field_simp [ne_of_gt hp0], ENNReal.rpow_one]
    have hrightPow : (K * ENNReal.ofReal (R ^ beta)) ^ p =
        K ^ p * ENNReal.ofReal (R ^ weightedCutoffMomentScaleExponent γ α p) := by
      rw [ENNReal.mul_rpow_of_ne_top hK.ne ENNReal.ofReal_ne_top]
      have hscalePow := ennreal_ofReal_rpow_of_pos_upto_two
        (p := p) (Real.rpow_pos_of_pos hR beta)
      change K ^ p * ENNReal.rpow (ENNReal.ofReal (R ^ beta)) p =
        K ^ p * ENNReal.ofReal (R ^ weightedCutoffMomentScaleExponent γ α p)
      rw [hscalePow]
      have hReal : (R ^ beta) ^ p =
          R ^ weightedCutoffMomentScaleExponent γ α p := by
        rw [← Real.rpow_mul hR.le]
        dsimp [beta]
        field_simp [ne_of_gt hp0]
      rw [hReal]
    calc
      _ = ((∫⁻ ω, ENNReal.rpow
          (cutoffWeightedGmcBallMass P Xc γ α z R δ ω) p ∂P) ^ (1 / p)) ^ p :=
        hleftPow.symm
      _ ≤ (K * ENNReal.ofReal (R ^ beta)) ^ p :=
      ENNReal.rpow_le_rpow hrootBound hp0.le
      _ = K ^ p * ENNReal.ofReal
          (R ^ weightedCutoffMomentScaleExponent γ α p) := hrightPow
      _ = cutoffWeightedPositiveScaleRootBoundConstant A γ p ε ^ p *
          ENNReal.ofReal (R ^ weightedCutoffMomentScaleExponent γ α p) := by rw [hKeq]

/-- The margin estimate with its own insertion exponent, retaining the original existential API. -/
theorem cutoffWeightedGmcBallMoment_positive_scale_upto_two_with_margin
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ α p : ℝ) (hγ : 0 < γ) (hα : 0 < α)
    (hp : 1 < p) (hp2 : p ≤ 2)
    (hpRange : p < min (4 / γ ^ 2) (2 / γ * (Q γ - α)))
    (ε : ℝ) (hε : 0 < ε)
    (hεbeta : ε ≤ weightedCutoffMomentScaleExponent γ α p / p)
    :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z : ℂ, ∀ R : ℝ,
      0 < R → R ≤ 1 / 2 → ‖z‖ + 2 * R ≤ 1 →
      ∀ δ : ℝ, 0 < δ → δ ≤ R →
      (∫⁻ ω, ENNReal.rpow
        (cutoffWeightedGmcBallMass P Xc γ α z R δ ω) p ∂P) ≤
        C * ENNReal.ofReal
          (R ^ weightedCutoffMomentScaleExponent γ α p) := by
  have hpcrit : p < 4 / γ ^ 2 := lt_of_lt_of_le hpRange (min_le_left _ _)
  obtain ⟨A, hA, hballRoot⟩ :=
    regularizedGMC_openBall_lp_root_bound_upto_two_uniform_chart_all_radius
      P X hX Xc hXc γ p hγ hp hp2 hpcrit
  let C := cutoffWeightedPositiveScaleRootBoundConstant A γ p ε ^ p
  have hmain := cutoffWeightedGmcBallMoment_positive_scale_of_ball_root_bound
    P X hX Xc hXc γ α p hγ hα hp hpRange ε hε hεbeta A hA hballRoot
  refine ⟨C, hmain.1, ?_⟩
  intro z R hR hRhi hchart δ hδ hδR
  simpa [C] using hmain.2 z R hR hRhi hchart δ hδ hδR


end DOZZ.Proofs
