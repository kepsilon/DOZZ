/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.RadialEnergy

/-!
# DOZZ.GFF.EnergyPositivity

Quantitative radial estimates for the finite-energy approximation to the equator measure.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace DOZZ

/-- The radial probability density is nonnegative at positive radii. -/
theorem annularRadiusLaw_nonneg (n : ℕ) {r : ℝ} (hr : 0 < r) :
    0 ≤ annularRadiusLaw n r := by
  rw [annularRadiusLaw, annularProbabilityRadial]
  exact mul_nonneg (mul_nonneg (by positivity) hr.le)
    (mul_nonneg (inv_nonneg.mpr (annularProfileMass_pos n).le)
      (annularProfile_nonneg n r))

/-- A logarithm of two maxima changes by at most twice the radial displacement from one. -/
theorem abs_log_max_sub_log_max_one (r t δ : ℝ) (hr : 0 < r)
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) (hnear : |r - 1| ≤ δ) :
    |Real.log (max r t) - Real.log (max 1 t)| ≤ 2 * δ := by
  let a := max r t
  let b := max 1 t
  have ha : 0 < a := lt_of_lt_of_le hr (le_max_left r t)
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one (le_max_left 1 t)
  have hab : |a - b| ≤ δ := by
    have hmax : |max r t - max 1 t| ≤ |r - 1| :=
      abs_max_sub_max_le_abs r 1 t
    exact (hmax.trans hnear)
  have haHalf : 1 / 2 ≤ a := by
    have hrLower : 1 - δ ≤ r := by
      have := (abs_le.mp hnear).1
      linarith only [this]
    have hδLower : 1 / 2 ≤ 1 - δ := by linarith only [hδhalf]
    exact (hδLower.trans hrLower).trans (le_max_left r t)
  have hbOne : 1 ≤ b := le_max_left 1 t
  have hratio : |a / b - 1| ≤ δ := by
    rw [show a / b - 1 = (a - b) / b by field_simp [ne_of_gt hb], abs_div,
      abs_of_pos hb]
    apply (div_le_iff₀ hb).2
    linarith only [hab, mul_nonneg hδ (sub_nonneg.mpr hbOne)]
  have hratioInv : |b / a - 1| ≤ 2 * δ := by
    rw [show b / a - 1 = (b - a) / a by field_simp [ne_of_gt ha], abs_div,
      abs_of_pos ha]
    apply (div_le_iff₀ ha).2
    have hδa : δ ≤ 2 * δ * a := by
      linarith only [mul_nonneg hδ (sub_nonneg.mpr haHalf)]
    have hba : |b - a| ≤ δ := by simpa [abs_sub_comm] using hab
    linarith only [hba, hδa]
  have hq : 0 < a / b := div_pos ha hb
  have hqInv : 0 < (a / b)⁻¹ := inv_pos.mpr hq
  have hlogUpper : Real.log (a / b) ≤ 2 * δ := by
    calc
      Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos hq
      _ ≤ |a / b - 1| := le_abs_self _
      _ ≤ δ := hratio
      _ ≤ 2 * δ := by linarith only [hδ]
  have hlogLower : -Real.log (a / b) ≤ 2 * δ := by
    have h := Real.log_le_sub_one_of_pos hqInv
    rw [Real.log_inv] at h
    calc
      -Real.log (a / b) ≤ (a / b)⁻¹ - 1 := h
      _ = b / a - 1 := by field_simp [ne_of_gt ha, ne_of_gt hb]
      _ ≤ |b / a - 1| := le_abs_self _
      _ ≤ 2 * δ := hratioInv
  have hlog :
      Real.log a - Real.log b = Real.log (a / b) := by
    exact (Real.log_div ha.ne' hb.ne').symm
  rw [show Real.log (max r t) - Real.log (max 1 t) = Real.log (a / b) by
    simpa [a, b] using hlog]
  exact abs_le.mpr ⟨by linarith only [hlogLower], hlogUpper⟩

/-- The annular logarithmic potential integrand is integrable on positive radii. A continuous
extension of the logarithm below radius `1/2` is harmless because the radial density vanishes
there. -/
theorem integrable_annularRadiusLaw_mul_logmax (n : ℕ) (t : ℝ) :
    Integrable (fun r => annularRadiusLaw n r * Real.log (max r t))
      ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))) := by
  let extLog : ℝ → ℝ := fun r => Real.log (max r (max t (1 / 2)))
  have hext : Continuous extLog := by
    apply (continuous_id.max continuous_const).log
    intro r
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_right r (max t (1 / 2))))
  have hcont : Continuous (fun r => annularRadiusLaw n r * extLog r) :=
    (continuous_annularRadiusLaw n).mul hext
  have hcomp : HasCompactSupport (fun r => annularRadiusLaw n r * extLog r) :=
    (hasCompactSupport_annularRadiusLaw n).mul_right
  have hbase : Integrable (fun r => annularRadiusLaw n r * extLog r)
      (volume : Measure ℝ) := hcont.integrable_of_hasCompactSupport hcomp
  have heq :
      (fun r => annularRadiusLaw n r * Real.log (max r t)) =
        (fun r => annularRadiusLaw n r * extLog r) := by
    funext r
    by_cases hrzero : annularRadiusLaw n r = 0
    · simp [hrzero]
    · have hrmem : r ∈ Function.support (annularRadiusLaw n) := by
        simpa [Function.mem_support] using hrzero
      have hrhalf : 1 / 2 ≤ r :=
        (support_annularRadiusLaw_subset n hrmem).1
      have hmax : max r (max t (1 / 2)) = max r t := by
        calc
          max r (max t (1 / 2)) = max (max r t) (1 / 2) := by rw [← max_assoc]
          _ = max r t := max_eq_left
            (hrhalf.trans (le_max_left r t))
      dsimp [extLog]
      rw [hmax]
  exact (hbase.restrict).congr
    (Filter.Eventually.of_forall fun r => (congrFun heq r).symm)

/-- The radial logarithmic potential is uniformly close to the unit-circle potential. -/
theorem abs_annularLogPotential_sub_logmax (n : ℕ) (t : ℝ) :
    |(∫ r in Ioi (0 : ℝ),
        annularRadiusLaw n r * Real.log (max r t)) - Real.log (max 1 t)| ≤
      2 / ((n : ℝ) + 2) := by
  let δ : ℝ := 1 / ((n : ℝ) + 2)
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Ioi (0 : ℝ))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδhalf : δ ≤ 1 / 2 := by
    dsimp [δ]
    apply one_div_le_one_div_of_le (by norm_num)
    exact_mod_cast Nat.le_add_left 2 n
  have hpotInt := integrable_annularRadiusLaw_mul_logmax n t
  have hmassInt := integrable_annularRadiusLawOn n
  let c : ℝ := Real.log (max 1 t)
  have hcInt : Integrable (fun r : ℝ => c * annularRadiusLaw n r) μ :=
    hmassInt.const_mul c
  have hdiffInt : Integrable
      (fun r : ℝ => annularRadiusLaw n r * (Real.log (max r t) - c)) μ := by
    apply (hpotInt.sub hcInt).congr
    filter_upwards with r
    change annularRadiusLaw n r * Real.log (max r t) -
        c * annularRadiusLaw n r =
      annularRadiusLaw n r * (Real.log (max r t) - c)
    ring
  have hmass : ∫ r in Ioi (0 : ℝ), annularRadiusLaw n r = 1 :=
    integral_annularRadiusLaw n
  have hcIntegral : ∫ r in Ioi (0 : ℝ), c * annularRadiusLaw n r = c := by
    rw [integral_const_mul, hmass]
    simp [c]
  have hdiffIntegral :
      (∫ r in Ioi (0 : ℝ),
        annularRadiusLaw n r * (Real.log (max r t) - c)) =
        (∫ r in Ioi (0 : ℝ),
          annularRadiusLaw n r * Real.log (max r t)) - c := by
    calc
      _ = ∫ r in Ioi (0 : ℝ),
            annularRadiusLaw n r * Real.log (max r t) -
              c * annularRadiusLaw n r := by
            apply integral_congr_ae
            filter_upwards with r
            ring_nf
      _ = (∫ r in Ioi (0 : ℝ),
              annularRadiusLaw n r * Real.log (max r t)) -
            ∫ r in Ioi (0 : ℝ), c * annularRadiusLaw n r :=
          integral_sub hpotInt hcInt
      _ = _ := by rw [hcIntegral]
  have hupperInt : Integrable
      (fun r : ℝ => (2 * δ) * annularRadiusLaw n r) μ :=
    hmassInt.const_mul (2 * δ)
  have hbound :
      |(∫ r in Ioi (0 : ℝ), annularRadiusLaw n r * Real.log (max r t)) - c| ≤
        2 * δ := by
    rw [← hdiffIntegral]
    calc
      _ ≤ ∫ r in Ioi (0 : ℝ),
            |annularRadiusLaw n r * (Real.log (max r t) - c)| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ r in Ioi (0 : ℝ), (2 * δ) * annularRadiusLaw n r := by
          apply integral_mono_ae hdiffInt.norm hupperInt
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
          by_cases hzero : annularRadiusLaw n r = 0
          · simp [hzero]
          · have hradial : annularProbabilityRadial n r ≠ 0 := by
              intro hz
              apply hzero
              simp [annularRadiusLaw, hz]
            have hprofile : annularProfile n r ≠ 0 := by
              intro hz
              apply hradial
              simp [annularProbabilityRadial, hz]
            have hnear : |r - 1| < δ := by
              simpa [δ] using annularProfile_radius_bound n r hprofile
            have hnonneg := annularRadiusLaw_nonneg n hr
            have hlog := abs_log_max_sub_log_max_one r t δ hr hδ.le hδhalf hnear.le
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnonneg]
            calc
              annularRadiusLaw n r *
                    |Real.log (max r t) - Real.log (max 1 t)| ≤
                  annularRadiusLaw n r * (2 * δ) :=
                mul_le_mul_of_nonneg_left hlog hnonneg
              _ = (2 * δ) * annularRadiusLaw n r := by ring
      _ = 2 * δ := by
          rw [integral_const_mul, hmass]
          ring
  simpa [c, δ, div_eq_mul_inv, mul_comm] using hbound

/-- The planar logarithmic potential generated by the annular probability density. -/
noncomputable def annularLogPotential (n : ℕ) (z : ℂ) : ℝ :=
  ∫ r in Ioi (0 : ℝ),
    annularRadiusLaw n r * Real.log (max r ‖z‖)

theorem abs_annularLogPotential_sub_logPlus (n : ℕ) (z : ℂ) :
    |annularLogPotential n z - Real.log (max 1 ‖z‖)| ≤
      2 / ((n : ℝ) + 2) := by
  exact abs_annularLogPotential_sub_logmax n ‖z‖

/-- The logarithmic potential of a DOZZ test density is its complex-plane integral against
`log (max 1 ‖z‖)`. -/
theorem testFnPotential_eq_complex_logPlus (f : TestFn) :
    testFnPotential f =
      ∫ z : ℂ, f z * Real.log (max 1 ‖z‖) := by
  let u : GaussianFields.Vec 2 → ℝ := fun x =>
    testFnVec f x * logNormPlusVec x
  have hchange := volume_preserving_complexToVecTwo.integral_comp'
    (f := complexToVecTwo) (g := u)
  calc
    testFnPotential f = ∫ x : GaussianFields.Vec 2, u x := rfl
    _ = ∫ z : ℂ, u (complexToVecTwo z) := hchange.symm
    _ = ∫ z : ℂ, f z * Real.log (max 1 ‖z‖) := by
      apply integral_congr_ae
      filter_upwards with z
      simp [u, testFnVec_complexToVecTwo, logNormPlusVec,
        euclideanNorm_complexToVecTwo]

theorem integrable_testFn_mul_logPlus (f : TestFn) :
    Integrable (fun z : ℂ => f z * Real.log (max 1 ‖z‖))
      (volume : Measure ℂ) := by
  have hlog : Continuous (fun z : ℂ => Real.log (max 1 ‖z‖)) := by
    apply (continuous_const.max continuous_norm).log
    intro z
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_left 1 ‖z‖))
  exact (f.continuous.mul hlog).integrable_of_hasCompactSupport
    f.hasCompactSupport.mul_right

/-- On the support annulus, the unit-circle potential `log (max 1 ‖z‖)` is small. -/
theorem abs_logPlus_of_annularDensity_ne_zero (n : ℕ) (z : ℂ)
    (hz : annularProbabilityDensity n z ≠ 0) :
    |Real.log (max 1 ‖z‖)| ≤ 1 / ((n : ℝ) + 2) := by
  let δ : ℝ := 1 / ((n : ℝ) + 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hnear := annularProbabilityDensity_radius_bound n z hz
  have hnormUpper : ‖z‖ ≤ 1 + δ := by
    have h := (abs_le.mp hnear.le).2
    dsimp [δ]
    linarith
  have htLower : 1 ≤ max 1 ‖z‖ := le_max_left 1 ‖z‖
  have htUpper : max 1 ‖z‖ ≤ 1 + δ :=
    max_le (by linarith) hnormUpper
  have hlogNonneg : 0 ≤ Real.log (max 1 ‖z‖) := Real.log_nonneg htLower
  rw [abs_of_nonneg hlogNonneg]
  calc
    Real.log (max 1 ‖z‖) ≤ max 1 ‖z‖ - 1 :=
      Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one htLower)
    _ ≤ δ := by linarith

noncomputable def annularCrossEnergy (f : TestFn) (n : ℕ) : ℝ :=
  ∫ q : ℂ × ℂ,
    f q.1 * annularProbabilityDensity n q.2 * (-Real.log ‖q.1 - q.2‖)
    ∂((volume : Measure ℂ).prod (volume : Measure ℂ))

noncomputable def annularSelfEnergy (n : ℕ) : ℝ :=
  ∫ q : ℂ × ℂ,
    annularProbabilityDensity n q.1 * annularProbabilityDensity n q.2 *
      (-Real.log ‖q.1 - q.2‖)
    ∂((volume : Measure ℂ).prod (volume : Measure ℂ))

/-- The annular cross energy converges to minus the pinned test potential, with an explicit
error controlled by the `L¹` norm of the test density. -/
theorem abs_annularCrossEnergy_add_testFnPotential (f : TestFn) (n : ℕ) :
    |annularCrossEnergy f n + testFnPotential f| ≤
      (2 / ((n : ℝ) + 2)) * ∫ z : ℂ, |f z| := by
  let V : ℂ → ℝ := annularLogPotential n
  let L : ℂ → ℝ := fun z => Real.log (max 1 ‖z‖)
  let μ : Measure ℂ := volume
  have hV := integral_logKernel_annular f f.continuous f.hasCompactSupport n
  have hVInt : Integrable (fun z : ℂ => f z * V z) μ := by
    simpa [V, μ, annularLogPotential] using hV.1
  have hLInt : Integrable (fun z : ℂ => f z * L z) μ := by
    simpa [L, μ] using integrable_testFn_mul_logPlus f
  have hAbsInt : Integrable (fun z : ℂ => |f z|) μ := by
    have hf : Integrable f (volume : Measure ℂ) :=
      f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
    have h := hf.norm
    simpa [μ, Real.norm_eq_abs] using h
  have hDiffInt : Integrable (fun z : ℂ => f z * (L z - V z)) μ := by
    apply (hLInt.sub hVInt).congr
    filter_upwards with z
    change f z * L z - f z * V z = _
    ring
  have hCross := hV.2
  have hCross' : annularCrossEnergy f n = -(∫ z : ℂ, f z * V z ∂μ) := by
    simpa [annularCrossEnergy, V, μ, annularLogPotential] using hCross
  have hPotential : testFnPotential f = ∫ z : ℂ, f z * L z ∂μ := by
    simpa [L, μ] using testFnPotential_eq_complex_logPlus f
  have hIdentity : annularCrossEnergy f n + testFnPotential f =
      ∫ z : ℂ, f z * (L z - V z) ∂μ := by
    rw [hCross', hPotential]
    calc
      -(∫ z : ℂ, f z * V z ∂μ) + ∫ z : ℂ, f z * L z ∂μ =
          (∫ z : ℂ, f z * L z ∂μ) - ∫ z : ℂ, f z * V z ∂μ := by ring
      _ = ∫ z : ℂ, f z * L z - f z * V z ∂μ :=
        (integral_sub hLInt hVInt).symm
      _ = ∫ z : ℂ, f z * (L z - V z) ∂μ := by
        apply integral_congr_ae
        filter_upwards with z
        ring
  have hUpperInt : Integrable
      (fun z : ℂ => (2 / ((n : ℝ) + 2)) * |f z|) μ := hAbsInt.const_mul _
  have hPointwise (z : ℂ) : |f z * (L z - V z)| ≤
      (2 / ((n : ℝ) + 2)) * |f z| := by
    rw [abs_mul]
    have hpotential := abs_annularLogPotential_sub_logPlus n z
    have hpotential' : |L z - V z| ≤ 2 / ((n : ℝ) + 2) := by
      simpa [L, V, abs_sub_comm] using hpotential
    calc
      |f z| * |L z - V z| ≤ |f z| * (2 / ((n : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hpotential' (abs_nonneg (f z))
      _ = (2 / ((n : ℝ) + 2)) * |f z| := by ring
  calc
    _ = |∫ z : ℂ, f z * (L z - V z) ∂μ| := by rw [hIdentity]
    _ ≤ ∫ z : ℂ, |f z * (L z - V z)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ z : ℂ, (2 / ((n : ℝ) + 2)) * |f z| ∂μ := by
      apply integral_mono_ae hDiffInt.norm hUpperInt
      filter_upwards with z
      exact hPointwise z
    _ = (2 / ((n : ℝ) + 2)) * ∫ z : ℂ, |f z| := by
      rw [integral_const_mul]

theorem annularProbabilityDensity_nonneg (n : ℕ) (z : ℂ) :
    0 ≤ annularProbabilityDensity n z := by
  rw [annularProbabilityDensity]
  exact mul_nonneg (inv_nonneg.mpr (annularProfileMass_pos n).le)
    (annularProfile_nonneg n ‖z‖)

/-- The annular self-energy tends to the zero self-energy of the unit circle. -/
theorem abs_annularSelfEnergy_le (n : ℕ) :
    |annularSelfEnergy n| ≤ 4 / ((n : ℝ) + 2) := by
  let ρ : ℂ → ℝ := annularProbabilityDensity n
  let V : ℂ → ℝ := annularLogPotential n
  let μ : Measure ℂ := volume
  let c : ℝ := 4 / ((n : ℝ) + 2)
  have hPair := integral_logKernel_annular ρ
    (continuous_annularProbabilityDensity n)
    (hasCompactSupport_annularProbabilityDensity n) n
  have hVInt : Integrable (fun z : ℂ => ρ z * V z) μ := by
    simpa [ρ, V, μ, annularLogPotential] using hPair.1
  have hρInt : Integrable ρ μ := by
    simpa [ρ, μ] using integrable_annularProbabilityDensity n
  have hρMass : ∫ z : ℂ, ρ z ∂μ = 1 := by
    simpa [ρ, μ] using integral_annularProbabilityDensity n
  have hD : annularSelfEnergy n = -(∫ z : ℂ, ρ z * V z ∂μ) := by
    simpa [annularSelfEnergy, ρ, V, μ, annularLogPotential] using hPair.2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hUpperInt : Integrable (fun z : ℂ => c * ρ z) μ := hρInt.const_mul c
  have hPointwise (z : ℂ) : |ρ z * V z| ≤ c * ρ z := by
    by_cases hzero : ρ z = 0
    · simp [hzero]
    · have hρnonneg : 0 ≤ ρ z := by
        exact annularProbabilityDensity_nonneg n z
      have hlog := abs_logPlus_of_annularDensity_ne_zero n z (by simpa [ρ] using hzero)
      have hpotential := abs_annularLogPotential_sub_logPlus n z
      have hV : |V z| ≤ c := by
        have htri : |V z| ≤ |V z - Real.log (max 1 ‖z‖)| +
            |Real.log (max 1 ‖z‖)| := by
          calc
            |V z| = |(V z - Real.log (max 1 ‖z‖)) +
                Real.log (max 1 ‖z‖)| := by congr 1; ring
            _ ≤ |V z - Real.log (max 1 ‖z‖)| +
                |Real.log (max 1 ‖z‖)| := abs_add_le _ _
        have hpot : |V z - Real.log (max 1 ‖z‖)| ≤
            2 / ((n : ℝ) + 2) := by simpa [V] using hpotential
        have hbound : |V z| ≤ 3 / ((n : ℝ) + 2) := by
          calc
            |V z| ≤ |V z - Real.log (max 1 ‖z‖)| +
                |Real.log (max 1 ‖z‖)| := htri
            _ ≤ 2 / ((n : ℝ) + 2) + 1 / ((n : ℝ) + 2) := add_le_add hpot hlog
            _ = 3 / ((n : ℝ) + 2) := by ring
        have hthree : 3 / ((n : ℝ) + 2) ≤ 4 / ((n : ℝ) + 2) := by
          exact div_le_div_of_nonneg_right (by norm_num)
            (by positivity : 0 ≤ (n : ℝ) + 2)
        exact hbound.trans (by simpa [c] using hthree)
      rw [abs_mul, abs_of_nonneg hρnonneg]
      calc
        ρ z * |V z| ≤ ρ z * c := mul_le_mul_of_nonneg_left hV hρnonneg
        _ = c * ρ z := by ring
  calc
    |annularSelfEnergy n| = |∫ z : ℂ, ρ z * V z ∂μ| := by rw [hD, abs_neg]
    _ ≤ ∫ z : ℂ, |ρ z * V z| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ z : ℂ, c * ρ z ∂μ := by
      apply integral_mono_ae hVInt.norm hUpperInt
      filter_upwards with z
      exact hPointwise z
    _ = c := by rw [integral_const_mul, hρMass]; ring
    _ = 4 / ((n : ℝ) + 2) := rfl

/-- The complex logarithmic pairing equals its transported `Vec 2` pairing for compact
continuous densities. -/
theorem integral_complexLogKernelPair_eq_vec (u v : ℂ → ℝ)
    (hu : Continuous u) (hv : Continuous v)
    (huc : HasCompactSupport u) (hvc : HasCompactSupport v) :
    Integrable (fun q : ℂ × ℂ =>
      u q.1 * v q.2 * (-Real.log ‖q.1 - q.2‖))
      ((volume : Measure ℂ).prod (volume : Measure ℂ)) ∧
    (∫ q : ℂ × ℂ, u q.1 * v q.2 * (-Real.log ‖q.1 - q.2‖)
      ∂((volume : Measure ℂ).prod (volume : Measure ℂ))) =
      ∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
        (u (complexLinearEquivVecTwo.symm p.1)) *
          (v (complexLinearEquivVecTwo.symm p.2)) *
          GaussianFields.abkLogCovarianceKernel p.1 p.2
        ∂((volume : Measure (GaussianFields.Vec 2)).prod
          (volume : Measure (GaussianFields.Vec 2))) := by
  let uVec : GaussianFields.Vec 2 → ℝ := fun x =>
    u (complexLinearEquivVecTwo.symm x)
  let vVec : GaussianFields.Vec 2 → ℝ := fun x =>
    v (complexLinearEquivVecTwo.symm x)
  let F : ℂ × ℂ → ℝ := fun q =>
    u q.1 * v q.2 * (-Real.log ‖q.1 - q.2‖)
  let FVec : GaussianFields.Vec 2 × GaussianFields.Vec 2 → ℝ := fun p =>
    uVec p.1 * vVec p.2 * GaussianFields.abkLogCovarianceKernel p.1 p.2
  have huVec : Continuous uVec := hu.comp complexLinearEquivVecTwo.symm.continuous
  have hvVec : Continuous vVec := hv.comp complexLinearEquivVecTwo.symm.continuous
  have hucVec : HasCompactSupport uVec :=
    huc.comp_homeomorph complexLinearEquivVecTwo.symm.toHomeomorph
  have hvcVec : HasCompactSupport vVec :=
    hvc.comp_homeomorph complexLinearEquivVecTwo.symm.toHomeomorph
  have hFVec := integrable_compactLogKernelPair uVec vVec huVec hvVec hucVec hvcVec
  have hnorm (z w : ℂ) :
      GaussianFields.euclideanNorm (complexToVecTwo z - complexToVecTwo w) =
        ‖z - w‖ := by
    rw [← complexToVecTwo_sub]
    exact euclideanNorm_complexToVecTwo (z - w)
  have hkernel (z w : ℂ) :
      GaussianFields.abkLogCovarianceKernel (complexToVecTwo z) (complexToVecTwo w) =
        -Real.log ‖z - w‖ := by
    rw [GaussianFields.abkLogCovarianceKernel]
    exact congrArg (fun t : ℝ => -Real.log t) (hnorm z w)
  have hback (z : ℂ) : complexLinearEquivVecTwo.symm (complexToVecTwo z) = z := by
    rw [← complexLinearEquivVecTwo_apply]
    simp
  have hcomp : F = FVec ∘ complexPairToVecTwo := by
    funext q
    rcases q with ⟨z, w⟩
    change u z * v w * (-Real.log ‖z - w‖) =
      uVec (complexToVecTwo z) * vVec (complexToVecTwo w) *
        GaussianFields.abkLogCovarianceKernel (complexToVecTwo z) (complexToVecTwo w)
    rw [show uVec (complexToVecTwo z) = u z by simp [uVec, hback],
      show vVec (complexToVecTwo w) = v w by simp [vVec, hback], hkernel]
  have hF : Integrable F ((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
    have hcompInt : Integrable (FVec ∘ complexPairToVecTwo)
        ((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
      simpa using
        volume_preserving_complexPairToVecTwo.integrable_comp_of_integrable hFVec
    exact hcompInt.congr (by
      filter_upwards with q
      exact (congrFun hcomp q).symm)
  refine ⟨hF, ?_⟩
  calc
    _ = ∫ q : ℂ × ℂ, FVec (complexPairToVecTwo q)
          ∂((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
            apply integral_congr_ae
            filter_upwards with q
            exact congrFun hcomp q
    _ = ∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2, FVec p
          ∂((volume : Measure (GaussianFields.Vec 2)).prod
            (volume : Measure (GaussianFields.Vec 2))) :=
      volume_preserving_complexPairToVecTwo.integral_comp'
        (f := complexPairToVecTwo) (g := FVec)

/-- The ABK pairing of a mean-zero test function is the same logarithmic energy in complex
coordinates. -/
theorem abkLogCovariancePairing_eq_complex
    (ψ : GaussianFields.MeanZeroTestFunction 2) :
    GaussianFields.abkLogCovariancePairing ψ ψ =
      ∫ q : ℂ × ℂ,
        ψ (complexToVecTwo q.1) * ψ (complexToVecTwo q.2) *
          (-Real.log ‖q.1 - q.2‖)
        ∂((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
  let ψC : ℂ → ℝ := fun z => ψ (complexLinearEquivVecTwo z)
  have hψC : Continuous ψC := ψ.continuous.comp complexLinearEquivVecTwo.continuous
  have hψCc : HasCompactSupport ψC :=
    ψ.hasCompactSupport.comp_homeomorph complexLinearEquivVecTwo.toHomeomorph
  have hpair := integral_complexLogKernelPair_eq_vec ψC ψC hψC hψC hψCc hψCc
  have hψmap (z : ℂ) : ψC z = ψ (complexToVecTwo z) := by
    dsimp [ψC]
    rw [complexLinearEquivVecTwo_apply]
  unfold GaussianFields.abkLogCovariancePairing GaussianFields.abkKernelPairing
  have hvec :
      (fun p : GaussianFields.Vec 2 × GaussianFields.Vec 2 =>
        ψC (complexLinearEquivVecTwo.symm p.1) *
          ψC (complexLinearEquivVecTwo.symm p.2) *
          GaussianFields.abkLogCovarianceKernel p.1 p.2) =
      (fun p => ψ p.1 * ψ p.2 * GaussianFields.abkLogCovarianceKernel p.1 p.2) := by
    funext p
    simp [ψC]
  calc
    _ = ∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
          ψC (complexLinearEquivVecTwo.symm p.1) *
            ψC (complexLinearEquivVecTwo.symm p.2) *
            GaussianFields.abkLogCovarianceKernel p.1 p.2
          ∂((volume : Measure (GaussianFields.Vec 2)).prod
            (volume : Measure (GaussianFields.Vec 2))) := by
              apply integral_congr_ae
              filter_upwards with p
              exact (congrFun hvec p).symm
    _ = ∫ q : ℂ × ℂ,
          ψC q.1 * ψC q.2 * (-Real.log ‖q.1 - q.2‖)
        ∂((volume : Measure ℂ).prod (volume : Measure ℂ)) := hpair.2.symm
    _ = _ := by
        apply integral_congr_ae
        filter_upwards with q
        rw [hψmap q.1, hψmap q.2]

/-- The DOZZ logarithmic pairing transports to its ordinary complex-plane integral. -/
theorem testFnLogPairing_eq_complex (f g : TestFn) :
    testFnLogPairing f g =
      ∫ q : ℂ × ℂ, f q.1 * g q.2 * (-Real.log ‖q.1 - q.2‖)
        ∂((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
  simpa [testFnLogPairing, testFnVec] using
    (integral_complexLogKernelPair_eq_vec f g f.continuous g.continuous
      f.hasCompactSupport g.hasCompactSupport).2.symm

/-- The annular mean-zero test agrees in complex coordinates with subtraction of the annular
probability density. -/
theorem annularCenteredTestFn_complexValue (f : TestFn) (n : ℕ) (z : ℂ) :
    annularCenteredTestFn f n (complexToVecTwo z) =
      f z - testMass f * annularProbabilityDensity n z := by
  have h := testFnVec_eq_annularCenteredTestFn_add f n (complexToVecTwo z)
  rw [testFnVec_complexToVecTwo] at h
  have hdens : annularProbabilityDensityVec n (complexToVecTwo z) =
      annularProbabilityDensity n z := by
    simp [annularProbabilityDensityVec, annularProbabilityDensity,
      ← complexLinearEquivVecTwo_apply]
  rw [hdens] at h
  linarith

/-- Pairing the annular centered test with itself is its literal complex logarithmic energy. -/
theorem annularCenteredPairing_eq_complex (f : TestFn) (n : ℕ) :
    GaussianFields.abkLogCovariancePairing
        (annularCenteredTestFn f n) (annularCenteredTestFn f n) =
      ∫ q : ℂ × ℂ,
        (f q.1 - testMass f * annularProbabilityDensity n q.1) *
          (f q.2 - testMass f * annularProbabilityDensity n q.2) *
          (-Real.log ‖q.1 - q.2‖)
        ∂((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
  rw [abkLogCovariancePairing_eq_complex]
  apply integral_congr_ae
  filter_upwards with q
  rw [annularCenteredTestFn_complexValue f n q.1,
    annularCenteredTestFn_complexValue f n q.2]

/-- Expanding the annular mean-zero energy gives the test energy, two equal cross terms, and the
annular self-energy. -/
theorem annularCenteredPairing_eq_expansion (f : TestFn) (n : ℕ) :
    GaussianFields.abkLogCovariancePairing
        (annularCenteredTestFn f n) (annularCenteredTestFn f n) =
      testFnLogPairing f f - 2 * testMass f *
          (∫ q : ℂ × ℂ,
            f q.1 * annularProbabilityDensity n q.2 * (-Real.log ‖q.1 - q.2‖)
            ∂((volume : Measure ℂ).prod (volume : Measure ℂ))) +
        testMass f ^ 2 *
          (∫ q : ℂ × ℂ,
            annularProbabilityDensity n q.1 * annularProbabilityDensity n q.2 *
              (-Real.log ‖q.1 - q.2‖)
            ∂((volume : Measure ℂ).prod (volume : Measure ℂ))) := by
  let m := testMass f
  let ρ := annularProbabilityDensity n
  let g : ℂ → ℝ := fun z => f z - m * ρ z
  let A : ℂ × ℂ → ℝ := fun q => f q.1 * f q.2 * (-Real.log ‖q.1 - q.2‖)
  let B : ℂ × ℂ → ℝ := fun q => f q.1 * ρ q.2 * (-Real.log ‖q.1 - q.2‖)
  let C : ℂ × ℂ → ℝ := fun q => ρ q.1 * f q.2 * (-Real.log ‖q.1 - q.2‖)
  let D : ℂ × ℂ → ℝ := fun q => ρ q.1 * ρ q.2 * (-Real.log ‖q.1 - q.2‖)
  let μ : Measure (ℂ × ℂ) := (volume : Measure ℂ).prod (volume : Measure ℂ)
  have hρc := continuous_annularProbabilityDensity n
  have hρcs := hasCompactSupport_annularProbabilityDensity n
  have hgc : Continuous g := by
    exact f.continuous.sub (hρc.const_mul m)
  have hgcs : HasCompactSupport g := by
    have hmρ : HasCompactSupport (fun z : ℂ => m * ρ z) := by
      have heq : (fun z : ℂ => m * ρ z) = (fun _ : ℂ => m) • ρ := by
        funext z
        simp [smul_eq_mul]
      rw [heq]
      exact hρcs.smul_left (f := fun _ : ℂ => m)
    exact f.hasCompactSupport.sub hmρ
  have hA := integral_complexLogKernelPair_eq_vec f f f.continuous f.continuous
    f.hasCompactSupport f.hasCompactSupport
  have hB := integral_complexLogKernelPair_eq_vec f ρ f.continuous hρc
    f.hasCompactSupport hρcs
  have hC := integral_complexLogKernelPair_eq_vec ρ f hρc f.continuous
    hρcs f.hasCompactSupport
  have hD := integral_complexLogKernelPair_eq_vec ρ ρ hρc hρc hρcs hρcs
  have hAint : Integrable A μ := by simpa [A, μ] using hA.1
  have hBint : Integrable B μ := by simpa [B, μ] using hB.1
  have hCint : Integrable C μ := by simpa [C, μ] using hC.1
  have hDint : Integrable D μ := by simpa [D, μ] using hD.1
  have hgPair := integral_complexLogKernelPair_eq_vec g g hgc hgc hgcs hgcs
  have hgInt : Integrable (fun q : ℂ × ℂ =>
      g q.1 * g q.2 * (-Real.log ‖q.1 - q.2‖)) μ := by
    simpa [μ] using hgPair.1
  have hBm : Integrable (fun q => m * B q) μ := hBint.const_mul m
  have hCm : Integrable (fun q => m * C q) μ := hCint.const_mul m
  have hDmm : Integrable (fun q => m ^ 2 * D q) μ := hDint.const_mul (m ^ 2)
  have hExpanded : Integrable (fun q => (A q - m * B q) - (m * C q - m ^ 2 * D q)) μ :=
    (hAint.sub hBm).sub (hCm.sub hDmm)
  have hPointwise (q : ℂ × ℂ) :
      g q.1 * g q.2 * (-Real.log ‖q.1 - q.2‖) =
        (A q - m * B q) - (m * C q - m ^ 2 * D q) := by
    simp [A, B, C, D, g, ρ, m]
    ring
  have hswap : ∫ q : ℂ × ℂ, C q ∂μ = ∫ q : ℂ × ℂ, B q ∂μ := by
    calc
      _ = ∫ q : ℂ × ℂ, B q.swap ∂μ := by
            apply integral_congr_ae
            filter_upwards with q
            dsimp [B, C]
            rw [norm_sub_rev]
            ring
      _ = ∫ q : ℂ × ℂ, B q ∂μ := integral_prod_swap B
  have hcomplex := annularCenteredPairing_eq_complex f n
  have hgf :
      GaussianFields.abkLogCovariancePairing
          (annularCenteredTestFn f n) (annularCenteredTestFn f n) =
        ∫ q : ℂ × ℂ, g q.1 * g q.2 * (-Real.log ‖q.1 - q.2‖) ∂μ := by
    simpa [g, ρ, m, μ] using hcomplex
  have hExpandedIntegral :
      (∫ q : ℂ × ℂ, g q.1 * g q.2 * (-Real.log ‖q.1 - q.2‖) ∂μ) =
        (∫ q : ℂ × ℂ, A q ∂μ) - m * (∫ q : ℂ × ℂ, B q ∂μ) -
          m * (∫ q : ℂ × ℂ, C q ∂μ) + m ^ 2 * (∫ q : ℂ × ℂ, D q ∂μ) := by
    calc
      _ = ∫ q : ℂ × ℂ, (A q - m * B q) - (m * C q - m ^ 2 * D q) ∂μ := by
            apply integral_congr_ae
            filter_upwards with q
            exact hPointwise q
      _ = (∫ q : ℂ × ℂ, A q - m * B q ∂μ) -
            ∫ q : ℂ × ℂ, m * C q - m ^ 2 * D q ∂μ := integral_sub
              (hAint.sub hBm) (hCm.sub hDmm)
      _ = (∫ q : ℂ × ℂ, A q ∂μ) - m * (∫ q : ℂ × ℂ, B q ∂μ) -
            m * (∫ q : ℂ × ℂ, C q ∂μ) + m ^ 2 * (∫ q : ℂ × ℂ, D q ∂μ) := by
            rw [integral_sub hAint hBm, integral_sub hCm hDmm]
            simp only [integral_const_mul]
            ring
  rw [hgf, hExpandedIntegral, hswap]
  have hAtest : testFnLogPairing f f = ∫ q : ℂ × ℂ, A q ∂μ := by
    simpa [A, μ] using testFnLogPairing_eq_complex f f
  rw [← hAtest]
  simp only [two_mul]
  ring

/-- Integrability and the value of a negative-log section against the equator measure. -/
theorem integral_negLog_circleMeasure (x : ℂ) :
    Integrable (fun y : ℂ => -Real.log ‖x - y‖) (circleMeasure 0 0) ∧
      ∫ y, -Real.log ‖x - y‖ ∂circleMeasure 0 0 = -Real.log (normPlus x) := by
  have h := integral_log_norm_sub_circleMeasure x
  refine ⟨h.1.neg, ?_⟩
  rw [integral_neg, h.2]

noncomputable def circleRawLogCross (f : TestFn) : ℝ :=
  ∫ x : ℂ, f x *
    (∫ y : ℂ, -Real.log ‖x - y‖ ∂circleMeasure 0 0)

theorem integrable_circleRawLogCross (f : TestFn) :
    Integrable (fun x : ℂ => f x *
      (∫ y : ℂ, -Real.log ‖x - y‖ ∂circleMeasure 0 0))
      (volume : Measure ℂ) := by
  have h := integrable_testFn_mul_logPlus f
  apply h.neg.congr
  filter_upwards with x
  rw [(integral_negLog_circleMeasure x).2]
  simp [normPlus]

theorem circleRawLogCross_eq (f : TestFn) :
    circleRawLogCross f = -testFnPotential f := by
  have hint := integrable_circleRawLogCross f
  calc
    circleRawLogCross f =
        ∫ x : ℂ, -(f x * Real.log (max 1 ‖x‖)) := by
          rw [circleRawLogCross]
          apply integral_congr_ae
          filter_upwards with x
          rw [(integral_negLog_circleMeasure x).2]
          simp [normPlus]
    _ = -(∫ x : ℂ, f x * Real.log (max 1 ‖x‖)) := by rw [integral_neg]
    _ = -testFnPotential f := by rw [testFnPotential_eq_complex_logPlus]

noncomputable def circleRawLogSelfEnergy : ℝ :=
  ∫ x : ℂ, ∫ y : ℂ, -Real.log ‖x - y‖
    ∂circleMeasure 0 0 ∂circleMeasure 0 0


theorem circleRawLogSelfEnergy_eq_zero : circleRawLogSelfEnergy = 0 := by
  have h := iterated_circle_log_selfEnergy_zero
  calc
    circleRawLogSelfEnergy =
        ∫ x : ℂ, -(∫ y : ℂ, Real.log ‖x - y‖
          ∂circleMeasure 0 0) ∂circleMeasure 0 0 := by
            rw [circleRawLogSelfEnergy]
            apply integral_congr_ae
            filter_upwards with x
            rw [integral_neg]
    _ = -(∫ x : ℂ, ∫ y : ℂ, Real.log ‖x - y‖
        ∂circleMeasure 0 0 ∂circleMeasure 0 0) := by rw [integral_neg]
    _ = 0 := by rw [h.2]; simp

/-- The four-term raw logarithmic energy of the signed projection
`f dx - testMass(f) * circleMeasure(0,0)` against the corresponding projection of `g`.
The four terms are the Lebesgue-Lebesgue, two mixed, and circle-circle energies. -/
noncomputable def equatorProjectedLogEnergy (f g : TestFn) : ℝ :=
  testFnLogPairing f g - testMass g * circleRawLogCross f -
    testMass f * circleRawLogCross g +
      testMass f * testMass g * circleRawLogSelfEnergy



/-- The covariance of a test function is nonnegative, by approximation of the equator measure
with the smooth annular probability densities. -/
theorem gffCov_self_nonneg (f : TestFn) : 0 ≤ gffCov f f := by
  let m : ℝ := testMass f
  let L : ℝ := ∫ z : ℂ, |f z|
  let Q : ℕ → ℝ := fun n =>
    GaussianFields.abkLogCovariancePairing
      (annularCenteredTestFn f n) (annularCenteredTestFn f n)
  let C : ℝ := |m| * L + m ^ 2
  have hLnonneg : 0 ≤ L := by
    dsimp [L]
    exact integral_nonneg (fun z => abs_nonneg (f z))
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hCovExpansion : gffCov f f =
      testFnLogPairing f f + 2 * m * testFnPotential f := by
    rw [gffCov_eq_equatorLogEnergy]
    dsimp [m]
    ring
  have hError (n : ℕ) :
      |Q n - gffCov f f| ≤ (4 / ((n : ℝ) + 2)) * C := by
    have hExpansion := annularCenteredPairing_eq_expansion f n
    have hQ : Q n = testFnLogPairing f f -
        2 * m * annularCrossEnergy f n + m ^ 2 * annularSelfEnergy n := by
      simpa [Q, annularCrossEnergy, annularSelfEnergy, m] using hExpansion
    have hCross := abs_annularCrossEnergy_add_testFnPotential f n
    have hSelf := abs_annularSelfEnergy_le n
    have hDiff : Q n - gffCov f f =
        -2 * m * (annularCrossEnergy f n + testFnPotential f) +
          m ^ 2 * annularSelfEnergy n := by
      rw [hQ, hCovExpansion]
      ring
    have hCoeff : |-2 * m| = 2 * |m| := by
      rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      |Q n - gffCov f f| =
          |-2 * m * (annularCrossEnergy f n + testFnPotential f) +
            m ^ 2 * annularSelfEnergy n| := by rw [hDiff]
      _ ≤ |-2 * m * (annularCrossEnergy f n + testFnPotential f)| +
            |m ^ 2 * annularSelfEnergy n| := abs_add_le _ _
      _ = 2 * |m| * |annularCrossEnergy f n + testFnPotential f| +
            m ^ 2 * |annularSelfEnergy n| := by
          rw [abs_mul, hCoeff, abs_mul, abs_of_nonneg (sq_nonneg m)]
      _ ≤ 2 * |m| * ((2 / ((n : ℝ) + 2)) * L) +
            m ^ 2 * (4 / ((n : ℝ) + 2)) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hCross
              (by positivity : 0 ≤ 2 * |m|)
          · exact mul_le_mul_of_nonneg_left hSelf (sq_nonneg m)
      _ = (4 / ((n : ℝ) + 2)) * C := by
          dsimp [C, L, m]
          ring
  have hbase : Tendsto (fun n : ℕ => (4 : ℝ) / ((n : ℝ) + 2))
      atTop (𝓝 0) := by
    convert (tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ)).comp
      (tendsto_add_atTop_nat 2) using 1
    ext n
    simp [Nat.cast_add]
  have herrorTendsto : Tendsto (fun n : ℕ =>
      (4 / ((n : ℝ) + 2)) * C) atTop (𝓝 0) := by
    simpa using hbase.mul_const C
  have hnegativeTendsto : Tendsto (fun n : ℕ =>
      -((4 / ((n : ℝ) + 2)) * C)) atTop (𝓝 0) := by
    simpa using herrorTendsto.neg
  have hconstant : Tendsto (fun _ : ℕ => gffCov f f) atTop (𝓝 (gffCov f f)) :=
    tendsto_const_nhds
  apply le_of_tendsto_of_tendsto' hnegativeTendsto hconstant
  intro n
  have hQnonneg : 0 ≤ Q n := by
    exact abkLogCovariancePairing_self_nonneg (annularCenteredTestFn f n)
  have hupper := (abs_le.mp (hError n)).2
  dsimp [Q] at hQnonneg
  linarith

end DOZZ

end
