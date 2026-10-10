/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.WeightedCutoffSubunit
public import DOZZ.GMC.Moments.WeightedDyadic

/-! Positive-charge subunit estimates for smoothed local insertion weights. -/

@[expose] public section

open MeasureTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

noncomputable def cutoffDyadicBallRadius (R : ℝ) (n : ℕ) : ℝ :=
  R / (2 : ℝ) ^ n

noncomputable def cutoffDyadicBallWeight (γ α R : ℝ) (N n : ℕ) : ℝ≥0∞ :=
  if n ≤ N then ENNReal.ofReal
    ((cutoffDyadicBallRadius R (n + 1)) ^ (-γ * α)) else 0

noncomputable def weightedCutoffMomentScaleExponent (γ α p : ℝ) : ℝ :=
  γ * (Q γ - α) * p - γ ^ 2 * p ^ 2 / 2

noncomputable def cutoffWeightedPositiveSubunitScaleConstant (γ α p : ℝ) : ℝ≥0∞ :=
  let xi : ℝ := 2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2
  let eta : ℝ := weightedCutoffMomentScaleExponent γ α p
  let q : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ) ^ eta)
  let refBase : ℝ≥0∞ := 1 + gmcReferenceMeasure (Metric.ball 0 (1 / 2))
  ENNReal.ofReal (2 ^ xi) * refBase +
    ENNReal.ofReal ((1 / 2 : ℝ) ^ (-γ * α * p) * 2 ^ xi) *
      refBase * (1 - q)⁻¹

private theorem cutoff_dyadic_product_rpow {R e ξ η : ℝ} (hR : 0 < R)
    (hη : e + ξ = η) (n : ℕ) :
    ((R / 2) * (1 / 2 : ℝ) ^ n) ^ e *
      ((2 * R) * (1 / 2 : ℝ) ^ n) ^ ξ =
        ((R / 2) ^ e * (2 * R) ^ ξ) * ((1 / 2 : ℝ) ^ η) ^ n := by
  have hhalf : 0 < (1 / 2 : ℝ) := by norm_num
  have hleft : 0 ≤ R / 2 := by positivity
  have hright : 0 ≤ 2 * R := by positivity
  rw [Real.mul_rpow hleft (by positivity), Real.mul_rpow hright (by positivity),
    ← Real.rpow_natCast_mul hhalf.le n e,
    ← Real.rpow_natCast_mul hhalf.le n ξ]
  calc
    _ = ((R / 2) ^ e * (2 * R) ^ ξ) *
        ((1 / 2 : ℝ) ^ (n * e) * (1 / 2 : ℝ) ^ (n * ξ)) := by ring
    _ = ((R / 2) ^ e * (2 * R) ^ ξ) * (1 / 2 : ℝ) ^ (n * e + n * ξ) := by
      rw [← Real.rpow_add hhalf (n * e) (n * ξ)]
    _ = ((R / 2) ^ e * (2 * R) ^ ξ) * (1 / 2 : ℝ) ^ (n * η) := by
      congr 2
      rw [show n * e + n * ξ = n * η by rw [← hη]; ring]
    _ = _ := by
      rw [show (n : ℝ) * η = η * (n : ℝ) by ring,
        Real.rpow_mul_natCast hhalf.le η n]

private theorem cutoff_positive_shell_base_scale {R a ξ η : ℝ} (hR : 0 < R)
    (haξ : a + ξ = η) :
    (R / 2) ^ a * (2 * R) ^ ξ =
      ((1 / 2 : ℝ) ^ a * 2 ^ ξ) * R ^ η := by
  have hR0 : 0 ≤ R := le_of_lt hR
  rw [show R / 2 = R * (1 / 2 : ℝ) by ring,
    show 2 * R = 2 * R by rfl,
    Real.mul_rpow hR0 (by norm_num),
    Real.mul_rpow (by norm_num) hR0]
  calc
    _ = ((1 / 2 : ℝ) ^ a * 2 ^ ξ) * (R ^ a * R ^ ξ) := by ring
    _ = ((1 / 2 : ℝ) ^ a * 2 ^ ξ) * R ^ (a + ξ) := by
      rw [← Real.rpow_add hR a ξ]
    _ = _ := by rw [haξ]

/-- The smoothed positive-charge mass is dominated by its core and finitely many dyadic
annular masses. -/
theorem cutoffWeightedGmcBallMass_le_positive_dyadic_cover
    (μ : Measure ℂ) (γ α : ℝ) (z : ℂ) (R δ : ℝ) (N : ℕ)
    (hγ : 0 < γ) (hα : 0 < α) (hR : 0 < R) (hδ : 0 < δ)
    (hNlo : cutoffDyadicBallRadius R (N + 1) ≤ δ)
    :
    (∫⁻ x in Metric.ball z R,
      ENNReal.ofReal ((‖x - z‖ + δ) ^ (-γ * α)) ∂μ) ≤
      ENNReal.ofReal (δ ^ (-γ * α)) * μ (Metric.ball z δ) +
        ∑' n : ℕ, (if n ≤ N then
          ENNReal.ofReal ((cutoffDyadicBallRadius R (n + 1)) ^ (-γ * α)) *
            μ (Metric.ball z (cutoffDyadicBallRadius R n)) else 0) := by
  classical
  let B : Set ℂ := Metric.ball z R
  let core : Set ℂ := Metric.ball z δ
  let f : ℂ → ℝ≥0∞ := B.indicator
    (fun x => ENNReal.ofReal ((‖x - z‖ + δ) ^ (-γ * α)))
  let coreTerm : ℂ → ℝ≥0∞ := core.indicator
    (fun _ => ENNReal.ofReal (δ ^ (-γ * α)))
  let shellTerm : ℕ → ℂ → ℝ≥0∞ := fun n =>
    (Metric.ball z (cutoffDyadicBallRadius R n)).indicator
      (fun _ => cutoffDyadicBallWeight γ α R N n)
  have hexp : -γ * α < 0 := by linarith only [mul_pos hγ hα]
  have hpoint (x : ℂ) : f x ≤ coreTerm x + ∑' n : ℕ, shellTerm n x := by
    by_cases hx : x ∈ B
    · have hd : ‖x - z‖ < R := by
        simpa [B, Metric.mem_ball, dist_eq_norm] using hx
      by_cases hcore : ‖x - z‖ < δ
      · have hxcore : x ∈ core := by
          simpa [core, Metric.mem_ball, dist_eq_norm] using hcore
        have hbase : δ ≤ ‖x - z‖ + δ := by
          exact le_add_of_nonneg_left (norm_nonneg _)
        have hweight : ENNReal.ofReal ((‖x - z‖ + δ) ^ (-γ * α)) ≤
            ENNReal.ofReal (δ ^ (-γ * α)) := by
          apply ENNReal.ofReal_le_ofReal
          exact Real.rpow_le_rpow_of_nonpos (by positivity) hbase hexp.le
        have hcoreTerm : coreTerm x = ENNReal.ofReal (δ ^ (-γ * α)) := by
          simp [coreTerm, hxcore]
        have hsumCore : ENNReal.ofReal (δ ^ (-γ * α)) ≤
            ENNReal.ofReal (δ ^ (-γ * α)) + ∑' n : ℕ, shellTerm n x := by
          calc
            _ = 0 + ENNReal.ofReal (δ ^ (-γ * α)) := by simp
            _ ≤ (∑' n : ℕ, shellTerm n x) + ENNReal.ofReal (δ ^ (-γ * α)) :=
              add_le_add_left (bot_le : (0 : ℝ≥0∞) ≤ ∑' n : ℕ, shellTerm n x) _
            _ = _ := add_comm _ _
        simpa [f, hx, hcoreTerm] using hweight.trans hsumCore
      · have hδd : δ ≤ ‖x - z‖ := le_of_not_gt hcore
        have hdpos : 0 < ‖x - z‖ := lt_of_lt_of_le hδ hδd
        obtain ⟨n, hlow, hhigh⟩ := exists_dyadic_shell_index hdpos hd
        have hnle : n ≤ N := by
          by_contra hn
          have hNlt : N < n := Nat.lt_of_not_ge hn
          have hpow : (2 : ℝ) ^ (N + 1) ≤ (2 : ℝ) ^ n := by
            exact pow_le_pow_right₀ (by norm_num) (by omega)
          have hradius : cutoffDyadicBallRadius R n ≤
              cutoffDyadicBallRadius R (N + 1) := by
            dsimp [cutoffDyadicBallRadius]
            exact div_le_div_of_nonneg_left hR.le (by positivity) hpow
          have : ‖x - z‖ < δ := lt_of_lt_of_le hhigh
            (le_trans hradius hNlo)
          exact (not_lt_of_ge hδd) this
        have hball : x ∈ Metric.ball z (cutoffDyadicBallRadius R n) := by
          simpa [cutoffDyadicBallRadius, Metric.mem_ball, dist_eq_norm] using hhigh
        have hlow' : cutoffDyadicBallRadius R (n + 1) ≤ ‖x - z‖ := by
          simpa [cutoffDyadicBallRadius] using hlow
        have hbase : cutoffDyadicBallRadius R (n + 1) ≤ ‖x - z‖ + δ := by
          linarith
        have hweight : ENNReal.ofReal ((‖x - z‖ + δ) ^ (-γ * α)) ≤
            ENNReal.ofReal ((cutoffDyadicBallRadius R (n + 1)) ^ (-γ * α)) := by
          apply ENNReal.ofReal_le_ofReal
          have hrad : 0 < cutoffDyadicBallRadius R (n + 1) := by
            dsimp [cutoffDyadicBallRadius]
            positivity
          exact Real.rpow_le_rpow_of_nonpos hrad hbase hexp.le
        have hcoef : cutoffDyadicBallWeight γ α R N n =
            ENNReal.ofReal ((cutoffDyadicBallRadius R (n + 1)) ^ (-γ * α)) :=
          by simp [cutoffDyadicBallWeight, hnle]
        have hshell : shellTerm n x =
            ENNReal.ofReal ((cutoffDyadicBallRadius R (n + 1)) ^ (-γ * α)) := by
          simp [shellTerm, hball, hcoef]
        have hsum : shellTerm n x ≤ ∑' j : ℕ, shellTerm j x :=
          ENNReal.le_tsum (f := fun j => shellTerm j x) n
        have hsumShell :
            ENNReal.ofReal ((cutoffDyadicBallRadius R (n + 1)) ^ (-γ * α)) ≤
              coreTerm x + ∑' j : ℕ, shellTerm j x := by
          calc
            _ = 0 + ENNReal.ofReal ((cutoffDyadicBallRadius R (n + 1)) ^ (-γ * α)) := by simp
            _ ≤ coreTerm x + ENNReal.ofReal
                ((cutoffDyadicBallRadius R (n + 1)) ^ (-γ * α)) :=
              add_le_add_left (bot_le : (0 : ℝ≥0∞) ≤ coreTerm x) _
            _ = coreTerm x + shellTerm n x := by rw [← hshell]
            _ ≤ _ := add_le_add_right hsum _
        simpa [f, hx, hshell] using hweight.trans hsumShell
    · have hf : f x = 0 := by simp [f, hx]
      rw [hf]
      exact bot_le
  let g : ℂ → ℝ≥0∞ := coreTerm + fun x => ∑' n : ℕ, shellTerm n x
  calc
    _ = ∫⁻ x, f x ∂μ := by
      rw [← lintegral_indicator Metric.isOpen_ball.measurableSet]
    _ ≤ ∫⁻ x, g x ∂μ := lintegral_mono hpoint
    _ = ENNReal.ofReal (δ ^ (-γ * α)) * μ (Metric.ball z δ) +
        ∑' n : ℕ, (if n ≤ N then
          ENNReal.ofReal ((cutoffDyadicBallRadius R (n + 1)) ^ (-γ * α)) *
            μ (Metric.ball z (cutoffDyadicBallRadius R n)) else 0) := by
      change (∫⁻ x, coreTerm x + (∑' n : ℕ, shellTerm n x) ∂μ) = _
      rw [lintegral_add_left' ((measurable_const.indicator
        Metric.isOpen_ball.measurableSet).aemeasurable)]
      have hcoreInt : ∫⁻ x, coreTerm x ∂μ =
          ENNReal.ofReal (δ ^ (-γ * α)) * μ (Metric.ball z δ) := by
        rw [show coreTerm = core.indicator
          (fun _ => ENNReal.ofReal (δ ^ (-γ * α))) by rfl,
          lintegral_indicator_const Metric.isOpen_ball.measurableSet]
      rw [hcoreInt, lintegral_tsum]
      · apply congrArg (fun q : ℝ≥0∞ =>
          ENNReal.ofReal (δ ^ (-γ * α)) * μ (Metric.ball z δ) + q)
        apply tsum_congr
        intro n
        rw [show shellTerm n = (Metric.ball z (cutoffDyadicBallRadius R n)).indicator
          (fun _ => cutoffDyadicBallWeight γ α R N n) by rfl,
          lintegral_indicator_const Metric.isOpen_ball.measurableSet]
        simp [cutoffDyadicBallWeight, cutoffDyadicBallRadius]
      · intro n
        exact (measurable_const.indicator Metric.isOpen_ball.measurableSet).aemeasurable

private theorem ennreal_ofReal_rpow_of_pos_cutoff {x p : ℝ} (hx : 0 < x) :
    ENNReal.rpow (ENNReal.ofReal x) p = ENNReal.ofReal (x ^ p) := by
  have hx0 : ENNReal.ofReal x ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hx)
  have hleft : ENNReal.rpow (ENNReal.ofReal x) p ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hx0 ENNReal.ofReal_ne_top
  have hright : ENNReal.ofReal (x ^ p) ≠ ⊤ := ENNReal.ofReal_ne_top
  apply (ENNReal.toReal_eq_toReal_iff' hleft hright).1
  calc
    (ENNReal.rpow (ENNReal.ofReal x) p).toReal =
        (ENNReal.ofReal x).toReal ^ p := (ENNReal.toReal_rpow _ _).symm
    _ = x ^ p := by rw [ENNReal.toReal_ofReal hx.le]
    _ = (ENNReal.ofReal (x ^ p)).toReal := by
      rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hx.le p)]

/-- The cutoff weighted moment is bounded by the subunit moments of the core disk and the
finite dyadic shells down to the cutoff scale. -/
theorem cutoffWeightedGmcBallMoment_le_positive_dyadic_moments
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ α : ℝ) (hγ : 0 < γ) (hα : 0 < α) (z : ℂ) (R δ p : ℝ)
    (N : ℕ) (hR : 0 < R) (hδ : 0 < δ)
    (hNlo : cutoffDyadicBallRadius R (N + 1) ≤ δ)
    (hp : 0 < p) (hp1 : p ≤ 1) :
    (∫⁻ ω, ENNReal.rpow
      (cutoffWeightedGmcBallMass P Xc γ α z R δ ω) p ∂P) ≤
      (ENNReal.ofReal (δ ^ (-γ * α))) ^ p *
        (∫⁻ ω, ENNReal.rpow
          (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z δ)) p ∂P) +
      ∑' n : ℕ, (cutoffDyadicBallWeight γ α R N n) ^ p *
        (∫⁻ ω, ENNReal.rpow
          (regularizedGMC P Xc γ (Real.log (1 / δ)) ω
            (Metric.ball z (cutoffDyadicBallRadius R n))) p ∂P) := by
  classical
  let coreCoeff : ℝ≥0∞ := ENNReal.ofReal (δ ^ (-γ * α))
  let coreMass (ω : Ω) : ℝ≥0∞ :=
    regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z δ)
  let shellMass (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
    regularizedGMC P Xc γ (Real.log (1 / δ)) ω
      (Metric.ball z (cutoffDyadicBallRadius R n))
  let shellCoeff (n : ℕ) : ℝ≥0∞ := cutoffDyadicBallWeight γ α R N n
  let shellTerm (n : ℕ) (ω : Ω) : ℝ≥0∞ := shellCoeff n * shellMass n ω
  have hcoreMassMeas : AEMeasurable coreMass P := by
    exact regularizedGMC_mass_aemeasurable P X hX Xc hXc γ (Real.log (1 / δ))
      (Metric.ball z δ) Metric.isOpen_ball.measurableSet
  have hcorePowMeas : AEMeasurable (fun ω => ENNReal.rpow (coreMass ω) p) P :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hcoreMassMeas
  have hcoreTermMeas : AEMeasurable (fun ω => coreCoeff * coreMass ω) P :=
    aemeasurable_const.mul hcoreMassMeas
  have hcoreTermPowMeas : AEMeasurable
      (fun ω => ENNReal.rpow (coreCoeff * coreMass ω) p) P :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hcoreTermMeas
  have hshellMassMeas (n : ℕ) : AEMeasurable (shellMass n) P := by
    exact regularizedGMC_mass_aemeasurable P X hX Xc hXc γ (Real.log (1 / δ))
      (Metric.ball z (cutoffDyadicBallRadius R n)) Metric.isOpen_ball.measurableSet
  have hshellTermPowMeas (n : ℕ) : AEMeasurable
      (fun ω => ENNReal.rpow (shellTerm n ω) p) P := by
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      ((aemeasurable_const.mul (hshellMassMeas n)))
  have hpoint (ω : Ω) :
      ENNReal.rpow (cutoffWeightedGmcBallMass P Xc γ α z R δ ω) p ≤
        ENNReal.rpow (coreCoeff * coreMass ω) p +
          ∑' n : ℕ, ENNReal.rpow (shellTerm n ω) p := by
    have hcover := cutoffWeightedGmcBallMass_le_positive_dyadic_cover
      (regularizedGMC P Xc γ (Real.log (1 / δ)) ω)
      γ α z R δ N hγ hα hR hδ hNlo
    have hmass : cutoffWeightedGmcBallMass P Xc γ α z R δ ω ≤
        coreCoeff * coreMass ω + ∑' n : ℕ, shellTerm n ω := by
      simpa [cutoffWeightedGmcBallMass, coreCoeff, coreMass, shellTerm,
        shellCoeff, cutoffDyadicBallWeight, shellMass, mul_comm] using hcover
    calc
      _ ≤ ENNReal.rpow (coreCoeff * coreMass ω + ∑' n : ℕ, shellTerm n ω) p :=
        ENNReal.rpow_le_rpow hmass hp.le
      _ ≤ ENNReal.rpow (coreCoeff * coreMass ω) p +
          ENNReal.rpow (∑' n : ℕ, shellTerm n ω) p :=
        ENNReal.rpow_add_le_add_rpow _ _ hp.le hp1
      _ ≤ _ := add_le_add_right
        (ennreal_rpow_tsum_le_tsum_rpow (fun n => shellTerm n ω) hp hp1) _
  have hshellTsumMeas : ∀ n : ℕ,
      AEMeasurable (fun ω => ENNReal.rpow (shellTerm n ω) p) P := hshellTermPowMeas
  calc
    _ ≤ ∫⁻ ω, ENNReal.rpow (coreCoeff * coreMass ω) p +
        ∑' n : ℕ, ENNReal.rpow (shellTerm n ω) p ∂P := lintegral_mono hpoint
    _ = (∫⁻ ω, ENNReal.rpow (coreCoeff * coreMass ω) p ∂P) +
        ∑' n : ℕ, ∫⁻ ω, ENNReal.rpow (shellTerm n ω) p ∂P := by
      rw [lintegral_add_left' hcoreTermPowMeas, lintegral_tsum]
      · intro n
        exact hshellTsumMeas n
    _ = coreCoeff ^ p * (∫⁻ ω, ENNReal.rpow (coreMass ω) p ∂P) +
        ∑' n : ℕ, shellCoeff n ^ p *
          (∫⁻ ω, ENNReal.rpow (shellMass n ω) p ∂P) := by
      congr 1
      · calc
          _ = ∫⁻ ω, coreCoeff ^ p * ENNReal.rpow (coreMass ω) p ∂P := by
            apply lintegral_congr
            intro ω
            exact ENNReal.mul_rpow_of_nonneg _ _ hp.le
          _ = _ := lintegral_const_mul'' _ hcorePowMeas
      · apply tsum_congr
        intro n
        calc
          _ = ∫⁻ ω, shellCoeff n ^ p * ENNReal.rpow (shellMass n ω) p ∂P := by
            apply lintegral_congr
            intro ω
            exact ENNReal.mul_rpow_of_nonneg _ _ hp.le
          _ = _ := lintegral_const_mul'' _ (by
            exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
              (hshellMassMeas n))
    _ = _ := by rfl

/-- For positive insertion charge and strict insertion slack, the cutoff weighted moment is
uniformly bounded as the regularization scale tends to zero, at every subunit order. -/
theorem cutoffWeightedGmcBallMoment_positive_subunit_scale_formula
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ α : ℝ) (hγ : 0 < γ) (hα : 0 < α) (z : ℂ) (R p : ℝ)
    (hR : 0 < R) (hR1 : R ≤ 1 / 2) (hchart : ‖z‖ + 2 * R ≤ 1)
    (hp : 0 < p) (hp1 : p ≤ 1)
    (hpRange : p < min (4 / γ ^ 2) (2 / γ * (Q γ - α))) :
    cutoffWeightedPositiveSubunitScaleConstant γ α p < ⊤ ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ R →
      (∫⁻ ω, ENNReal.rpow
        (cutoffWeightedGmcBallMass P Xc γ α z R δ ω) p ∂P) ≤
          cutoffWeightedPositiveSubunitScaleConstant γ α p *
            ENNReal.ofReal (R ^ weightedCutoffMomentScaleExponent γ α p)) := by
  classical
  let xi : ℝ := 2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2
  let eta : ℝ := weightedCutoffMomentScaleExponent γ α p
  let q : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ) ^ eta)
  let scale : ℝ≥0∞ := ENNReal.ofReal (R ^ eta)
  let shellConst : ℝ≥0∞ := ENNReal.ofReal
    ((1 / 2 : ℝ) ^ (-γ * α * p) * 2 ^ xi) * scale
  let refBase : ℝ≥0∞ := 1 + gmcReferenceMeasure (Metric.ball 0 (1 / 2))
  let coreConst : ℝ≥0∞ := ENNReal.ofReal (2 ^ xi) * scale * refBase
  let C : ℝ≥0∞ := ENNReal.ofReal (2 ^ xi) * refBase +
    ENNReal.ofReal ((1 / 2 : ℝ) ^ (-γ * α * p) * 2 ^ xi) *
      refBase * (1 - q)⁻¹
  change C < ⊤ ∧ (∀ δ : ℝ, 0 < δ → δ ≤ R →
    (∫⁻ ω, ENNReal.rpow
      (cutoffWeightedGmcBallMass P Xc γ α z R δ ω) p ∂P) ≤
        C * ENNReal.ofReal (R ^ eta))
  have heta : γ * (Q γ - α) * p - γ ^ 2 * p ^ 2 / 2 = eta := rfl
  have hEtaDyad : -γ * α * p + xi = eta := by
    dsimp [eta, xi, weightedCutoffMomentScaleExponent, Q]
    field_simp [ne_of_gt hγ]
    ring
  have hetaPos : 0 < eta := by
    rw [← heta]
    exact weightedGmcMomentExponent_pos_of_sharp_range hγ hp hpRange
  have hqReal : (1 / 2 : ℝ) ^ eta < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) hetaPos
  have hq : q < 1 := ENNReal.ofReal_lt_one.mpr (by simpa [q] using hqReal)
  have hden : 1 - q ≠ 0 := by
    intro h
    have hqle : 1 ≤ q := tsub_eq_zero_iff_le.mp h
    exact (not_le_of_gt hq) hqle
  have hgeom : (1 - q)⁻¹ < ⊤ :=
    lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr hden)
  have hRefBall : gmcReferenceMeasure (Metric.ball 0 (1 / 2)) ≤
      gmcReferenceMeasure Set.univ :=
    measure_mono (Set.subset_univ _)
  have hRefBallTop : gmcReferenceMeasure (Metric.ball 0 (1 / 2)) < ⊤ :=
    lt_of_le_of_lt hRefBall (lt_top_iff_ne_top.mpr gmcReferenceMeasure_univ_ne_top)
  have hrefBase : refBase < ⊤ := by
    dsimp [refBase]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hRefBallTop⟩
  have hscale : scale < ⊤ := by
    dsimp [scale]
    exact ENNReal.ofReal_lt_top
  have hcoreConst : coreConst < ⊤ := by
    dsimp [coreConst]
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hscale) hrefBase
  have hshellConst : shellConst < ⊤ := by
    dsimp [shellConst]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hscale
  have hC : C < ⊤ := by
    dsimp [C]
    exact ENNReal.add_lt_top.mpr ⟨
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hrefBase,
      ENNReal.mul_lt_top
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hrefBase) hgeom⟩
  refine ⟨hC, ?_⟩
  intro δ hδ hδR
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
  let base : ℝ≥0∞ := refBase
  let coreCoeff : ℝ≥0∞ := ENNReal.ofReal (δ ^ (-γ * α))
  let coreMoment : ℝ≥0∞ := ∫⁻ ω,
    ENNReal.rpow (regularizedGMC P Xc γ (Real.log (1 / δ)) ω
      (Metric.ball z δ)) p ∂P
  have hcoreChart : ‖z‖ + 2 * δ ≤ 1 := by linarith only [hchart, hδR]
  have hcoreScale := regularizedGMC_openBall_subunit_scale_bound P X hX Xc hXc γ z
    δ δ p hδ (by linarith [hδR, hR1]) hδ le_rfl hcoreChart hp.le hp1
  have hcoreCoeff : coreCoeff ^ p = ENNReal.ofReal (δ ^ (-γ * α * p)) := by
    calc
      _ = (ENNReal.ofReal δ) ^ ((-γ * α) * p) := by
        dsimp [coreCoeff]
        rw [← ennreal_ofReal_rpow_of_pos_cutoff hδ]
        exact (ENNReal.rpow_mul (ENNReal.ofReal δ) (-γ * α) p).symm
      _ = ENNReal.ofReal (δ ^ ((-γ * α) * p)) :=
        ennreal_ofReal_rpow_of_pos_cutoff hδ
      _ = _ := by congr 1
  have hcoreReal : δ ^ (-γ * α * p) * (2 * δ) ^ xi ≤ 2 ^ xi * R ^ eta := by
    have he := hEtaDyad
    have heq : δ ^ (-γ * α * p) * (2 * δ) ^ xi = 2 ^ xi * δ ^ eta := by
      rw [Real.mul_rpow (by norm_num) hδ.le]
      calc
        _ = 2 ^ xi * (δ ^ (-γ * α * p) * δ ^ xi) := by ac_rfl
        _ = _ := by rw [← Real.rpow_add hδ _ _]; rw [he]
    calc
      _ = 2 ^ xi * δ ^ eta := heq
      _ ≤ 2 ^ xi * R ^ eta := by
        gcongr
  have hcoreMomentBound : coreCoeff ^ p * coreMoment ≤ coreConst := by
    have hrealNonneg : 0 ≤ δ ^ (-γ * α * p) := Real.rpow_nonneg hδ.le _
    calc
      _ ≤ ENNReal.ofReal (δ ^ (-γ * α * p)) *
          (ENNReal.ofReal ((2 * δ) ^ xi) * base) := by
        rw [hcoreCoeff]
        gcongr
      _ = ENNReal.ofReal
          (δ ^ (-γ * α * p) * (2 * δ) ^ xi) * base := by
        calc
          _ = (ENNReal.ofReal (δ ^ (-γ * α * p)) *
              ENNReal.ofReal ((2 * δ) ^ xi)) * base := by ac_rfl
          _ = _ := by rw [← ENNReal.ofReal_mul hrealNonneg]
      _ ≤ ENNReal.ofReal (2 ^ xi * R ^ eta) * refBase := by
        dsimp [base]
        gcongr
      _ = coreConst := by
        dsimp [base, coreConst, scale]
        rw [← ENNReal.ofReal_mul
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) xi)]
  have htermBound (n : ℕ) :
      (cutoffDyadicBallWeight γ α R N n) ^ p *
        (∫⁻ ω, ENNReal.rpow
          (regularizedGMC P Xc γ (Real.log (1 / δ)) ω
            (Metric.ball z (cutoffDyadicBallRadius R n))) p ∂P) ≤
        shellConst * q ^ n * refBase := by
    by_cases hn : n ≤ N
    · have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ N := by
        exact pow_le_pow_right₀ (by norm_num) hn
      have hradN : cutoffDyadicBallRadius R N ≤ cutoffDyadicBallRadius R n := by
        dsimp [cutoffDyadicBallRadius]
        exact div_le_div_of_nonneg_left hR.le (by positivity) hpow
      have hδn : δ ≤ cutoffDyadicBallRadius R n := hNhi.trans hradN
      have hRn : cutoffDyadicBallRadius R n ≤ R := by
        dsimp [cutoffDyadicBallRadius]
        apply (div_le_iff₀ (by positivity)).2
        have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ n :=
          one_le_pow₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ))
        exact le_mul_of_one_le_right hR.le hpow1
      have hRn1 : cutoffDyadicBallRadius R n ≤ 1 / 2 := hRn.trans hR1
      have hchartn : ‖z‖ + 2 * cutoffDyadicBallRadius R n ≤ 1 := by
        linarith only [hchart, hRn]
      have hscale := regularizedGMC_openBall_subunit_scale_bound P X hX Xc hXc γ z
        (cutoffDyadicBallRadius R n) δ p (by
          dsimp [cutoffDyadicBallRadius]
          positivity) hRn1 hδ hδn hchartn hp.le hp1
      have hradpos : 0 < cutoffDyadicBallRadius R (n + 1) := by
        dsimp [cutoffDyadicBallRadius]
        positivity
      have hcoeffpow : (cutoffDyadicBallWeight γ α R N n) ^ p =
          ENNReal.ofReal
            ((cutoffDyadicBallRadius R (n + 1)) ^ (-γ * α * p)) := by
        calc
          _ = (ENNReal.ofReal (cutoffDyadicBallRadius R (n + 1) ^ (-γ * α))) ^ p := by
            simp [cutoffDyadicBallWeight, hn]
          _ = (ENNReal.rpow (ENNReal.ofReal (cutoffDyadicBallRadius R (n + 1)))
              (-γ * α)) ^ p := by
            rw [← ennreal_ofReal_rpow_of_pos_cutoff hradpos]
          _ = ENNReal.rpow (ENNReal.ofReal (cutoffDyadicBallRadius R (n + 1)))
              ((-γ * α) * p) := (ENNReal.rpow_mul _ _ _).symm
          _ = ENNReal.ofReal
              ((cutoffDyadicBallRadius R (n + 1)) ^ ((-γ * α) * p)) :=
            ennreal_ofReal_rpow_of_pos_cutoff hradpos
          _ = _ := by congr 1
      have hradDecomp : cutoffDyadicBallRadius R (n + 1) =
          (R / 2) * (1 / 2 : ℝ) ^ n := by
        dsimp [cutoffDyadicBallRadius]
        rw [pow_succ, div_pow]
        field_simp
        ring
      have hstep : cutoffDyadicBallRadius R n =
          2 * cutoffDyadicBallRadius R (n + 1) := by
        dsimp [cutoffDyadicBallRadius]
        rw [pow_succ]
        field_simp
      have hradDecomp2 : 2 * cutoffDyadicBallRadius R n =
          (2 * R) * (1 / 2 : ℝ) ^ n := by
        rw [hstep, hradDecomp]
        ring
      have hη : -γ * α * p + xi = eta := by
        exact hEtaDyad
      have hbaseScale := cutoff_positive_shell_base_scale hR hη
      have hprod :
          (cutoffDyadicBallRadius R (n + 1)) ^ (-γ * α * p) *
            (2 * cutoffDyadicBallRadius R n) ^ xi =
          ((R / 2) ^ (-γ * α * p) * (2 * R) ^ xi) *
            ((1 / 2 : ℝ) ^ eta) ^ n := by
        rw [hradDecomp, hradDecomp2]
        exact cutoff_dyadic_product_rpow hR hη n
      have htermRealNonneg : 0 ≤
          (cutoffDyadicBallRadius R (n + 1)) ^ (-γ * α * p) :=
        Real.rpow_nonneg (le_of_lt hradpos) _
      calc
        _ ≤ ENNReal.ofReal
            ((cutoffDyadicBallRadius R (n + 1)) ^ (-γ * α * p)) *
              (ENNReal.ofReal ((2 * cutoffDyadicBallRadius R n) ^ xi) * refBase) := by
          rw [hcoeffpow]
          gcongr
        _ = ENNReal.ofReal
              ((cutoffDyadicBallRadius R (n + 1)) ^ (-γ * α * p) *
                (2 * cutoffDyadicBallRadius R n) ^ xi) * refBase := by
          calc
            _ = (ENNReal.ofReal ((cutoffDyadicBallRadius R (n + 1)) ^ (-γ * α * p)) *
                ENNReal.ofReal ((2 * cutoffDyadicBallRadius R n) ^ xi)) * refBase := by ac_rfl
            _ = _ := by rw [← ENNReal.ofReal_mul htermRealNonneg]
        _ = shellConst * q ^ n * refBase := by
          rw [hprod]
          dsimp [shellConst, q, scale]
          rw [hbaseScale, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
    · simp [cutoffDyadicBallWeight, hn, ENNReal.zero_rpow_of_pos hp]
  have hsumBound :
      (∑' n : ℕ, (cutoffDyadicBallWeight γ α R N n) ^ p *
        (∫⁻ ω, ENNReal.rpow
          (regularizedGMC P Xc γ (Real.log (1 / δ)) ω
            (Metric.ball z (cutoffDyadicBallRadius R n))) p ∂P)) ≤
        shellConst * refBase * (1 - q)⁻¹ := by
    calc
      _ ≤ ∑' n : ℕ, shellConst * q ^ n * refBase :=
        ENNReal.tsum_le_tsum htermBound
      _ = shellConst * refBase * (1 - q)⁻¹ := by
        calc
          _ = ∑' n : ℕ, (shellConst * refBase) * q ^ n := by
            apply tsum_congr
            intro n
            ac_rfl
          _ = (shellConst * refBase) * ∑' n : ℕ, q ^ n := ENNReal.tsum_mul_left
          _ = _ := by rw [ENNReal.tsum_geometric]
  have hmoment := cutoffWeightedGmcBallMoment_le_positive_dyadic_moments
    P X hX Xc hXc γ α hγ hα z R δ p N hR hδ hNlo hp hp1
  have htotal :
      (∫⁻ ω, ENNReal.rpow
        (cutoffWeightedGmcBallMass P Xc γ α z R δ ω) p ∂P) ≤ C * scale := by
    calc
      _ ≤ coreCoeff ^ p * coreMoment +
          ∑' n : ℕ, (cutoffDyadicBallWeight γ α R N n) ^ p *
            (∫⁻ ω, ENNReal.rpow
              (regularizedGMC P Xc γ (Real.log (1 / δ)) ω
                (Metric.ball z (cutoffDyadicBallRadius R n))) p ∂P) := hmoment
      _ ≤ coreConst + shellConst * refBase * (1 - q)⁻¹ :=
        add_le_add hcoreMomentBound hsumBound
      _ = C * scale := by
        dsimp [C, coreConst, shellConst, scale]
        rw [add_mul]
        ac_rfl
  have hetaScale : eta = γ * (Q γ - α) * p - γ ^ 2 * p ^ 2 / 2 := by
    exact heta.symm
  have htotal' :
      (∫⁻ ω, ENNReal.rpow
        (cutoffWeightedGmcBallMass P Xc γ α z R δ ω) p ∂P) ≤ C *
          ENNReal.ofReal (R ^ (γ * (Q γ - α) * p - γ ^ 2 * p ^ 2 / 2)) := by
    simpa [scale, hetaScale] using htotal
  simpa [weightedCutoffMomentScaleExponent, hetaScale] using htotal'

/-- Existential-constant form of the positive-charge subunit cutoff bound. -/
theorem cutoffWeightedGmcBallMoment_positive_subunit_uniform_cutoff
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ α : ℝ) (hγ : 0 < γ) (hα : 0 < α) (z : ℂ) (R p : ℝ)
    (hR : 0 < R) (hR1 : R ≤ 1 / 2) (hchart : ‖z‖ + 2 * R ≤ 1)
    (hp : 0 < p) (hp1 : p ≤ 1)
    (hpRange : p < min (4 / γ ^ 2) (2 / γ * (Q γ - α))) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ R →
      (∫⁻ ω, ENNReal.rpow
        (cutoffWeightedGmcBallMass P Xc γ α z R δ ω) p ∂P) ≤
          C * ENNReal.ofReal (R ^ weightedCutoffMomentScaleExponent γ α p) := by
  obtain ⟨hC, hbound⟩ := cutoffWeightedGmcBallMoment_positive_subunit_scale_formula
    P X hX Xc hXc γ α hγ hα z R p hR hR1 hchart hp hp1 hpRange
  refine ⟨cutoffWeightedPositiveSubunitScaleConstant γ α p, hC, ?_⟩
  intro δ hδ hδR
  exact hbound δ hδ hδR

end DOZZ.Proofs
