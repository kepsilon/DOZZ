/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationHermitianJets
public import DOZZ.Hypergeom.ClassificationCanonicalHermitian
public import DOZZ.Hypergeom.ClassificationCutCrossingBranch
public import DOZZ.Hypergeom.ClassificationMonodromy
public import DOZZ.Hypergeom.ODE.CutPlaneTopology

/-! Matching values and first Wirtinger derivatives across the negative cut. -/

@[expose] public section

open Filter
open scoped Topology

namespace DOZZ.Proofs

private noncomputable def gaussNegativeCrossingCenter : ℂ := -1 / 2

private def gaussNegativeCrossingUpperSet : Set ℂ :=
  gaussNegativeCrossingDisk ∩ {z : ℂ | 0 < z.im}

private def gaussNegativeCrossingLowerSet : Set ℂ :=
  gaussNegativeCrossingDisk ∩ {z : ℂ | z.im < 0}

private theorem gaussNegativeCrossingUpperSet_isOpen :
    IsOpen gaussNegativeCrossingUpperSet := by
  exact gaussNegativeCrossingDisk_isOpen.inter (isOpen_Ioi.preimage Complex.continuous_im)

private theorem gaussNegativeCrossingLowerSet_isOpen :
    IsOpen gaussNegativeCrossingLowerSet := by
  exact gaussNegativeCrossingDisk_isOpen.inter (isOpen_Iio.preimage Complex.continuous_im)

private theorem gaussNegativeCrossingDisk_subset_regularPlane :
    gaussNegativeCrossingDisk ⊆ gaussRegularPlane := by
  intro z hz
  change z ≠ 0 ∧ z ≠ 1
  have hx := gaussNegativeCrossingDisk_real_bounds hz
  constructor
  · intro he
    have hre : z.re = 0 := by rw [he]; simp
    linarith
  · intro he
    have hre : z.re = 1 := by rw [he]; simp
    linarith

private theorem gaussNegativeCrossingSlitPlane_isOpen : IsOpen gaussSlitPlane := by
  change IsOpen ({z : ℂ | z.im ≠ 0} ∪ {z | z.re < 1})
  exact (isOpen_compl_singleton.preimage Complex.continuous_im).union
    (isOpen_Iio.preimage Complex.continuous_re)

private theorem gaussNegativeCrossingPhase_star
    (c : ℝ) :
    star (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (1 - (c : ℂ)))) =
      Complex.exp (-((2 * (Real.pi : ℂ) * Complex.I) * (1 - (c : ℂ)))) := by
  simp only [Complex.star_def]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_sub, map_one]
  ring_nf

private theorem gaussNegativeCrossingPhase_star_mul_self
    (c : ℝ) :
    star (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (1 - (c : ℂ)))) *
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (1 - (c : ℂ))) = 1 := by
  rw [gaussNegativeCrossingPhase_star]
  rw [← Complex.exp_add]
  rw [show -((2 * (Real.pi : ℂ) * Complex.I) * (1 - (c : ℂ))) +
      (2 * (Real.pi : ℂ) * Complex.I) * (1 - (c : ℂ)) = 0 by ring,
    Complex.exp_zero]

private theorem gaussNegativeCrossingUpper_closure :
    gaussNegativeCrossingCenter ∈ closure gaussNegativeCrossingUpperSet := by
  apply mem_closure_iff_nhds.mpr
  intro s hs
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  let r : ℝ := min (ε / 2) (1 / 8)
  have hr : 0 < r := lt_min (by linarith) (by norm_num)
  have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrquarter : r < (1 / 4 : ℝ) :=
    lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  let w : ℂ := gaussNegativeCrossingCenter + (r : ℂ) * Complex.I
  have hwNear : w ∈ Metric.ball gaussNegativeCrossingCenter ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    calc
      ‖w - gaussNegativeCrossingCenter‖ = ‖(r : ℂ) * Complex.I‖ := by simp [w]
      _ = r := by simp [Real.norm_eq_abs, abs_of_pos hr]
      _ < ε := hrε
  have hwDisk : w ∈ gaussNegativeCrossingDisk := by
    change dist w gaussNegativeCrossingCenter < (1 / 4 : ℝ)
    rw [dist_eq_norm]
    calc
      ‖w - gaussNegativeCrossingCenter‖ = ‖(r : ℂ) * Complex.I‖ := by simp [w]
      _ = r := by simp [Real.norm_eq_abs, abs_of_pos hr]
      _ < (1 / 4 : ℝ) := hrquarter
  have hwUpper : 0 < w.im := by
    simp [w, gaussNegativeCrossingCenter, Complex.add_im, hr]
  exact ⟨w, hball hwNear, ⟨hwDisk, hwUpper⟩⟩

private theorem gaussNegativeCrossingLower_closure :
    gaussNegativeCrossingCenter ∈ closure
      (gaussNegativeCrossingDisk ∩ {z : ℂ | z.im < 0}) := by
  apply mem_closure_iff_nhds.mpr
  intro s hs
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  let r : ℝ := min (ε / 2) (1 / 8)
  have hr : 0 < r := lt_min (by linarith) (by norm_num)
  have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrquarter : r < (1 / 4 : ℝ) :=
    lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  let w : ℂ := gaussNegativeCrossingCenter - (r : ℂ) * Complex.I
  have hwNear : w ∈ Metric.ball gaussNegativeCrossingCenter ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    calc
      ‖w - gaussNegativeCrossingCenter‖ = ‖-((r : ℂ) * Complex.I)‖ := by simp [w]
      _ = r := by simp [Real.norm_eq_abs, abs_of_pos hr]
      _ < ε := hrε
  have hwDisk : w ∈ gaussNegativeCrossingDisk := by
    change dist w gaussNegativeCrossingCenter < (1 / 4 : ℝ)
    rw [dist_eq_norm]
    calc
      ‖w - gaussNegativeCrossingCenter‖ = ‖-((r : ℂ) * Complex.I)‖ := by simp [w]
      _ = r := by simp [Real.norm_eq_abs, abs_of_pos hr]
      _ < (1 / 4 : ℝ) := hrquarter
  have hwLower : w.im < 0 := by
    simp [w, gaussNegativeCrossingCenter, Complex.sub_im, hr]
  exact ⟨w, hball hwNear, ⟨hwDisk, hwLower⟩⟩

private theorem crossing_functions_match_jets_of_eqOn
    {S : Set ℂ} {z : ℂ} (hS : IsOpen S) (hz : z ∈ closure S)
    {F G : ℂ → ℂ}
    (hF : ContDiffAt ℝ 2 F z) (hG : ContDiffAt ℝ 2 G z)
    (hFdiff : ∀ w ∈ S, DifferentiableAt ℝ F w)
    (hGdiff : ∀ w ∈ S, DifferentiableAt ℝ G w)
    (hEq : ∀ w ∈ S, F w = G w) :
    F z = G z ∧ wirtingerZ F z = wirtingerZ G z := by
  have hfreq := mem_closure_iff_frequently.mp hz
  have hvalueFreq : ∃ᶠ w in 𝓝 z, F w = G w := hfreq.mono hEq
  have hvalue := tendsto_nhds_unique_of_frequently_eq
    hF.continuousAt.tendsto hG.continuousAt.tendsto hvalueFreq
  have hFz : DifferentiableAt ℝ (fun w => wirtingerZ F w) z :=
    differentiableAt_wirtingerZ_of_contDiffAt_two hF
  have hGz : DifferentiableAt ℝ (fun w => wirtingerZ G w) z :=
    differentiableAt_wirtingerZ_of_contDiffAt_two hG
  have hderivFreq : ∃ᶠ w in 𝓝 z, wirtingerZ F w = wirtingerZ G w := by
    exact hfreq.mono fun w hw => by
      have hnear : F =ᶠ[𝓝 w] G := by
        filter_upwards [hS.mem_nhds hw] with v hv
        exact hEq v hv
      exact wirtingerZ_congr_of_eventuallyEq (hFdiff w hw) (hGdiff w hw) hnear
  have hderiv := tendsto_nhds_unique_of_frequently_eq
    hFz.continuousAt.tendsto hGz.continuousAt.tendsto hderivFreq
  exact ⟨hvalue, hderiv⟩

/-- The canonical Hermitian tensor of a real Gauss solution has no off-diagonal term. The
negative-cut crossing compares its two local representatives at the seam, including their value
and first `∂z` jet; a nonzero Wronskian then removes the off-diagonal entries. -/
theorem realGaussSolution_canonical_hermitian_offDiagonal_zero
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℝ) (hc : ∀ n : ℤ, c ≠ (n : ℝ))
    (T : ℂ → ℝ) (hT : IsRealGaussSolution a b c T) :
    ∃ α δ : ℝ, ∃ β : ℂ,
      (∀ z ∈ gaussCutPlane,
        (T z : ℂ) =
          gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z *
              star ((α : ℂ) * gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z +
                β * gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) +
            gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z *
              star (star β * gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z +
                (δ : ℂ) * gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z)) ∧
      β = 0 := by
  obtain ⟨α, δ, β, hrep⟩ :=
    realGaussSolution_canonical_hermitian_representation hH a b c hc T hT
  have hcC : ∀ n : ℤ, (c : ℂ) ≠ (n : ℂ) := by
    intro n hn
    apply hc n
    exact_mod_cast hn
  have hcNat : ∀ n : ℕ, (c : ℂ) ≠ -(n : ℂ) := by
    intro n hn
    apply hcC (-(n : ℤ))
    exact hn.trans (by simp)
  have hchar := hH (a : ℂ) (b : ℂ) (c : ℂ) hcNat
  have hFanalyticSlit : AnalyticOnNhd ℂ
      (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ)) gaussSlitPlane :=
    hchar.1.analyticOnNhd gaussNegativeCrossingSlitPlane_isOpen
  let f : ℂ → ℂ := gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ)
  let g : ℂ → ℂ := gaussNegativeCrossingSecond H (a : ℂ) (b : ℂ) (c : ℂ)
  let F : ℂ → ℂ := fun z => (T z : ℂ)
  have hf : AnalyticOnNhd ℂ f gaussNegativeCrossingDisk := by
    exact hFanalyticSlit.mono (by simpa [f] using gaussNegativeCrossingDisk_subset_gaussSlitPlane)
  have hg : AnalyticOnNhd ℂ g gaussNegativeCrossingDisk := by
    simpa [g] using gaussNegativeCrossingSecond_analyticOnNhd hH
      (a : ℂ) (b : ℂ) (c : ℂ) hcC
  have hFcont : ∀ z ∈ gaussNegativeCrossingDisk, ContDiffAt ℝ 2 F z := by
    intro z hz
    have hzReg := gaussNegativeCrossingDisk_subset_regularPlane hz
    have hTAt := (hT.1 z hzReg).contDiffAt
      (gaussRegularPlane_isOpen.mem_nhds hzReg)
    change ContDiffAt ℝ 2 (fun w => Complex.ofRealCLM (T w)) z
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp z hTAt
  let phase : ℂ :=
    Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (1 - (c : ℂ)))
  have hphaseNe : phase ≠ 1 := by
    simpa [phase] using gaussZeroMonodromyPhase_ne_one c hc
  have hphaseUnit : star phase * phase = 1 := by
    dsimp [phase]
    exact gaussNegativeCrossingPhase_star_mul_self c
  have hphase0 : phase ≠ 0 := Complex.exp_ne_zero _
  have hphaseStar : star phase = phase⁻¹ := eq_inv_of_mul_eq_one_left hphaseUnit
  have hphaseInvStar : star (phase⁻¹) = phase := by
    calc
      star (phase⁻¹) = (star phase)⁻¹ := by simp
      _ = (phase⁻¹)⁻¹ := by rw [hphaseStar]
      _ = phase := by simp
  have hphaseInvUnit : phase⁻¹ * phase = 1 := inv_mul_cancel₀ hphase0
  have hphaseMulInvUnit : phase * phase⁻¹ = 1 := mul_inv_cancel₀ hphase0
  let Qup : ℂ → ℂ := hermitianQuadraticTensor f g
    (α : ℂ) (star β) β (δ : ℂ)
  let Bdown : ℂ := star β * phase
  let Cdown : ℂ := β * phase⁻¹
  let Qdown : ℂ → ℂ := hermitianQuadraticTensor f g
    (α : ℂ) Bdown Cdown (δ : ℂ)
  have hQupAt : ∀ z ∈ gaussNegativeCrossingDisk, ContDiffAt ℝ 2 Qup z := by
    intro z hz
    exact hermitianQuadraticTensor_contDiffAt_two hf hg
      (α : ℂ) (star β) β (δ : ℂ) hz
  have hQdownAt : ∀ z ∈ gaussNegativeCrossingDisk, ContDiffAt ℝ 2 Qdown z := by
    intro z hz
    exact hermitianQuadraticTensor_contDiffAt_two hf hg
      (α : ℂ) Bdown Cdown (δ : ℂ) hz
  have hUpperEq : ∀ z ∈ gaussNegativeCrossingUpperSet, F z = Qup z := by
    intro z hz
    have hrepz := hrep z (Or.inl (ne_of_gt hz.2))
    change F z = _ at hrepz
    calc
      F z = _ := hrepz
      _ = Qup z := by
        dsimp [F, Qup, f, g, hermitianQuadraticTensor]
        rw [gaussNegativeCrossingSecond_eq_gaussFPlus_of_im_pos
          (a : ℂ) (b : ℂ) (c : ℂ) z hz.2]
        simp only [map_add, map_mul, Complex.conj_conj,
          Complex.conj_ofReal]
        ring_nf
  have hLowerEq : ∀ z ∈ gaussNegativeCrossingLowerSet, F z = Qdown z := by
    intro z hz
    have hrepz := hrep z (Or.inl (ne_of_lt hz.2))
    have htrans := gaussNegativeCrossingSecond_eq_phase_mul_gaussFPlus_of_im_neg
      (H := H)
      (a : ℂ) (b : ℂ) (c : ℂ) z hz.2
    have hplus : gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z =
        phase⁻¹ * g z := by
      calc
        gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z =
            (phase⁻¹ * phase) * gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z := by
              simp [hphaseInvUnit]
        _ = phase⁻¹ * (phase * gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) := by ring
        _ = phase⁻¹ * g z := by rw [← htrans]
    change F z = _ at hrepz
    calc
      F z = _ := hrepz
      _ = Qdown z := by
        dsimp [F, Qdown, Bdown, Cdown, f, g, hermitianQuadraticTensor]
        rw [hplus]
        simp only [map_add, map_mul, Complex.conj_conj, Complex.conj_ofReal]
        rw [show (starRingEnd ℂ) (phase⁻¹) = phase from hphaseInvStar]
        linear_combination ((δ : ℂ) * g z * (starRingEnd ℂ) (g z)) * hphaseMulInvUnit
  have hUpperFdiff : ∀ z ∈ gaussNegativeCrossingUpperSet,
      DifferentiableAt ℝ F z := by
    intro z hz
    exact (hFcont z hz.1).differentiableAt (by norm_num)
  have hLowerFdiff : ∀ z ∈ gaussNegativeCrossingLowerSet,
      DifferentiableAt ℝ F z := by
    intro z hz
    exact (hFcont z hz.1).differentiableAt (by norm_num)
  have hUpperQdiff : ∀ z ∈ gaussNegativeCrossingUpperSet,
      DifferentiableAt ℝ Qup z := by
    intro z hz
    exact (hQupAt z hz.1).differentiableAt (by norm_num)
  have hLowerQdiff : ∀ z ∈ gaussNegativeCrossingLowerSet,
      DifferentiableAt ℝ Qdown z := by
    intro z hz
    exact (hQdownAt z hz.1).differentiableAt (by norm_num)
  have hcenter : gaussNegativeCrossingCenter ∈ gaussNegativeCrossingDisk := by
    norm_num [gaussNegativeCrossingDisk, gaussNegativeCrossingCenter,
      Metric.mem_ball, dist_eq_norm]
  have hcenterC2 : ContDiffAt ℝ 2 F gaussNegativeCrossingCenter := hFcont _ hcenter
  have hcenterUpC2 : ContDiffAt ℝ 2 Qup gaussNegativeCrossingCenter := hQupAt _ hcenter
  have hcenterDownC2 : ContDiffAt ℝ 2 Qdown gaussNegativeCrossingCenter := hQdownAt _ hcenter
  have hJetsUp := crossing_functions_match_jets_of_eqOn
    gaussNegativeCrossingUpperSet_isOpen gaussNegativeCrossingUpper_closure
    hcenterC2 hcenterUpC2 hUpperFdiff hUpperQdiff hUpperEq
  have hJetsDown := crossing_functions_match_jets_of_eqOn
    gaussNegativeCrossingLowerSet_isOpen gaussNegativeCrossingLower_closure
    hcenterC2 hcenterDownC2 hLowerFdiff hLowerQdiff hLowerEq
  have hW : f gaussNegativeCrossingCenter * deriv g gaussNegativeCrossingCenter -
      deriv f gaussNegativeCrossingCenter * g gaussNegativeCrossingCenter ≠ 0 := by
    have h := gaussNegativeCrossing_wronskian_ne_zero hH
      (a : ℂ) (b : ℂ) (c : ℂ) hcC gaussNegativeCrossingCenter hcenter
    simpa [gaussCramerWronskian, f, g] using h
  have hβHerm : Cdown - β = star (Bdown - star β) := by
    simp only [Bdown, Cdown, star_sub, star_mul, star_star, hphaseStar]
    ring
  have h₀ : (Bdown - star β) * f gaussNegativeCrossingCenter *
        star (g gaussNegativeCrossingCenter) +
      (Cdown - β) * g gaussNegativeCrossingCenter *
        star (f gaussNegativeCrossingCenter) = 0 := by
    have hvalue := hJetsDown.1.symm.trans hJetsUp.1
    change (α : ℂ) * f gaussNegativeCrossingCenter * star (f gaussNegativeCrossingCenter) +
        Bdown * f gaussNegativeCrossingCenter * star (g gaussNegativeCrossingCenter) +
        Cdown * g gaussNegativeCrossingCenter * star (f gaussNegativeCrossingCenter) +
        (δ : ℂ) * g gaussNegativeCrossingCenter * star (g gaussNegativeCrossingCenter) =
      (α : ℂ) * f gaussNegativeCrossingCenter * star (f gaussNegativeCrossingCenter) +
        star β * f gaussNegativeCrossingCenter * star (g gaussNegativeCrossingCenter) +
        β * g gaussNegativeCrossingCenter * star (f gaussNegativeCrossingCenter) +
        (δ : ℂ) * g gaussNegativeCrossingCenter * star (g gaussNegativeCrossingCenter) at hvalue
    linear_combination hvalue
  have h₁ : (Bdown - star β) * deriv f gaussNegativeCrossingCenter *
        star (g gaussNegativeCrossingCenter) +
      (Cdown - β) * deriv g gaussNegativeCrossingCenter *
        star (f gaussNegativeCrossingCenter) = 0 := by
    have hderiv := hJetsDown.2.symm.trans hJetsUp.2
    rw [hermitianQuadraticTensor_wirtingerZ hf hg (α : ℂ) Bdown Cdown (δ : ℂ) hcenter,
      hermitianQuadraticTensor_wirtingerZ hf hg (α : ℂ) (star β) β (δ : ℂ) hcenter] at hderiv
    change (α : ℂ) * deriv f gaussNegativeCrossingCenter *
        star (f gaussNegativeCrossingCenter) +
        Bdown * deriv f gaussNegativeCrossingCenter * star (g gaussNegativeCrossingCenter) +
        Cdown * deriv g gaussNegativeCrossingCenter * star (f gaussNegativeCrossingCenter) +
        (δ : ℂ) * deriv g gaussNegativeCrossingCenter *
          star (g gaussNegativeCrossingCenter) =
      (α : ℂ) * deriv f gaussNegativeCrossingCenter *
        star (f gaussNegativeCrossingCenter) +
        star β * deriv f gaussNegativeCrossingCenter * star (g gaussNegativeCrossingCenter) +
        β * deriv g gaussNegativeCrossingCenter * star (f gaussNegativeCrossingCenter) +
        (δ : ℂ) * deriv g gaussNegativeCrossingCenter *
          star (g gaussNegativeCrossingCenter) at hderiv
    linear_combination hderiv
  have hOffDiag := hermitianOffDiagonal_eq_zero_of_value_and_z_derivative
    (f gaussNegativeCrossingCenter) (g gaussNegativeCrossingCenter)
    (deriv f gaussNegativeCrossingCenter) (deriv g gaussNegativeCrossingCenter)
    (Bdown - star β) (Cdown - β) hW hβHerm h₀ h₁
  have hCzero : Cdown - β = 0 := hOffDiag.2
  have hphaseInvNe : phase⁻¹ ≠ 1 := by
    intro h
    apply hphaseNe
    simpa using congrArg Inv.inv h
  have hβfactor : β * (phase⁻¹ - 1) = 0 := by
    dsimp [Cdown] at hCzero
    linear_combination hCzero
  have hβzero : β = 0 := by
    rcases mul_eq_zero.mp hβfactor with hβ | hphase
    · exact hβ
    · exact (hphaseInvNe (sub_eq_zero.mp hphase)).elim
  exact ⟨α, δ, β, hrep, hβzero⟩

end DOZZ.Proofs
