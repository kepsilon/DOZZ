/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFFStructure.DirichletCircleVersion

/-!
# Exterior-pinned finite Markov assembly

Harmonic means and exterior pin cancellation identify literal Dirichlet circle Green
covariances. The supported original-space distributions assemble into independent finite
Dirichlet blocks and a harmonic complement, with one common test event, raw circle
versions and an explicit positive uniform bound preceding every realization and center.
-/

@[expose] public section
open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped Topology ENNReal NNReal
universe u
namespace DOZZ.Proofs

/-- Conjugation makes the regular Green numerator symmetric. -/
theorem norm_diskGreen_numerator_comm (c z w : ℂ) (ρ : ℝ) :
    ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖ = ‖(ρ : ℂ)^2-(w-c)*star (z-c)‖ := by
  have he : (ρ : ℂ)^2-(w-c)*star (z-c) = star ((ρ : ℂ)^2-(z-c)*star (w-c)) := by
    simp only [Complex.star_def,map_sub,map_pow,map_mul,Complex.conj_conj,Complex.conj_ofReal]
    ring
  rw [he,norm_star]

/-- The regular logarithm has its harmonic mean value on every strict interior circle. -/
theorem integral_diskGreen_regular_circle (c x w : ℂ) (ρ r : ℝ) (hρ : 0 < ρ)
    (hx : ‖x-c‖+Real.exp (-r) < ρ) (hw : w ∈ ball c ρ) :
    (∫ z, Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖ ∂circleMeasure x r) =
      Real.log ‖(ρ : ℂ)^2-(x-c)*star (w-c)‖ := by
  rw [integral_circleMeasure_eq_circleAverage x r _ (by fun_prop)]
  exact ((harmonicOnNhd_diskGreen_regular c w ρ hρ hw).mono
    ((interior_circle_closedBall_subset c x ρ r hx).trans ball_subset_closedBall)).circleAverage_eq

/-- The regular logarithm is integrable on any strict interior circle. -/
theorem integrable_diskGreen_regular_circle (c x w : ℂ) (ρ r : ℝ) (hρ : 0 < ρ)
    (hx : ‖x-c‖+Real.exp (-r) < ρ) (hw : w ∈ ball c ρ) :
    Integrable (fun z : ℂ => Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖) (circleMeasure x r) := by
  apply integrable_circleMeasure_of_circleIntegrable x r (by fun_prop)
  have hs : sphere x |Real.exp (-r)| ⊆ closedBall c ρ :=
    (sphere_subset_closedBall.trans (interior_circle_closedBall_subset c x ρ r hx)).trans ball_subset_closedBall
  exact ((harmonicOnNhd_diskGreen_regular c w ρ hρ hw).continuousOn.mono hs).circleIntegrable'

/-- Interior circle measures stay inside the original disk. -/
theorem ae_mem_ball_of_interior_circle (c x : ℂ) (ρ r : ℝ)
    (hx : ‖x-c‖+Real.exp (-r) < ρ) : ∀ᵐ z ∂circleMeasure x r, z ∈ ball c ρ := by
  filter_upwards [ae_mem_sphere_circleMeasure x r] with z hz
  exact interior_circle_closedBall_subset c x ρ r hx
    (by simpa only [abs_of_pos (Real.exp_pos _)] using sphere_subset_closedBall hz)

/-- A Green circle section is its regular harmonic mean minus the logarithmic circle potential. -/
theorem integral_diskGreenKernel_circle (c x w : ℂ) (ρ r : ℝ) (hρ : 0 < ρ)
    (hx : ‖x-c‖+Real.exp (-r) < ρ) (hw : w ∈ ball c ρ) :
    (∫ z, diskGreenKernel c ρ hρ w z ∂circleMeasure x r) =
      Real.log ‖(ρ : ℂ)^2-(w-c)*star (x-c)‖-Real.log ρ-
        Real.log (max (Real.exp (-r)) ‖x-w‖) := by
  let _ := circleMeasure_isProbability x r
  let _ := circleMeasure_noAtoms x r
  have he : (fun z => diskGreenKernel c ρ hρ w z) =ᵐ[circleMeasure x r]
      fun z => Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖-Real.log ρ-Real.log ‖w-z‖ := by
    filter_upwards [ae_mem_ball_of_interior_circle c x ρ r hx,(circleMeasure x r).ae_ne w] with z hz hzw
    rw [diskGreenKernel_eq_log_parts c w z ρ hρ hw hz hzw.symm,
      norm_diskGreen_numerator_comm c w z ρ]
  have hi := integrable_diskGreen_regular_circle c x w ρ r hρ hx hw
  have hl : Integrable (fun z : ℂ => Real.log ‖w-z‖) (circleMeasure x r) := by
    simpa only [norm_sub_rev w] using integrable_log_norm_sub_circleMeasure x w r
  have hsub := integral_sub (hi.sub (integrable_const (Real.log ρ))) hl
  have hsub2 := integral_sub hi (integrable_const (Real.log ρ))
  simp only [Pi.sub_apply] at hsub hsub2
  rw [integral_congr_ae he,hsub,hsub2,integral_const,probReal_univ,one_smul,
    integral_diskGreen_regular_circle c x w ρ r hρ hx hw,
    integral_log_norm_rev_sub_circleMeasure,norm_diskGreen_numerator_comm c x w ρ]

/-- The literal double-circle Green integral separates its regular and singular parts. -/
theorem integral_integral_diskGreenKernel (c x y : ℂ) (ρ r s : ℝ) (hρ : 0 < ρ)
    (hx : ‖x-c‖+Real.exp (-r) < ρ) (hy : ‖y-c‖+Real.exp (-s) < ρ) :
    (∫ v, ∫ w, diskGreenKernel c ρ hρ v w ∂circleMeasure y s ∂circleMeasure x r) =
      Real.log ‖(ρ : ℂ)^2-(x-c)*star (y-c)‖-Real.log ρ-
        (∫ v, Real.log (max (Real.exp (-s)) ‖y-v‖) ∂circleMeasure x r) := by
  let _ := circleMeasure_isProbability x r
  have hys : y ∈ ball c ρ := mem_ball_iff_norm.mpr (by linarith [Real.exp_pos (-s)])
  have he : (fun v => ∫ w, diskGreenKernel c ρ hρ v w ∂circleMeasure y s) =ᵐ[circleMeasure x r]
      fun v => Real.log ‖(ρ : ℂ)^2-(v-c)*star (y-c)‖-Real.log ρ-
        Real.log (max (Real.exp (-s)) ‖y-v‖) := by
    filter_upwards [ae_mem_ball_of_interior_circle c x ρ r hx] with v hv
    exact integral_diskGreenKernel_circle c y v ρ s hρ hy hv
  have hi := integrable_diskGreen_regular_circle c x y ρ r hρ hx hys
  have hlog : Continuous (fun v : ℂ => Real.log (max (Real.exp (-s)) ‖y-v‖)) :=
    (continuous_const.max (continuous_const.sub continuous_id).norm).log
      (fun _ => ne_of_gt ((Real.exp_pos _).trans_le (le_max_left _ _)))
  have hl := integrable_circleMeasure_of_circleIntegrable x r hlog.measurable hlog.continuousOn.circleIntegrable'
  have hsub := integral_sub (hi.sub (integrable_const (Real.log ρ))) hl
  have hsub2 := integral_sub hi (integrable_const (Real.log ρ))
  simp only [Pi.sub_apply] at hsub hsub2
  rw [integral_congr_ae he,hsub,hsub2,integral_const,probReal_univ,one_smul,
    integral_diskGreen_regular_circle c x y ρ r hρ hx hys]

/-- Circle points in an interior disk also lie inside its exterior pin. -/
theorem interior_circle_norm_le_pin (c x : ℂ) (R ρ r : ℝ)
    (hpin : ‖c‖+ρ ≤ R) (hx : ‖x-c‖+Real.exp (-r) < ρ) :
    ∀ᵐ z ∂circleMeasure x r, ‖z‖ ≤ R := by
  filter_upwards [ae_mem_ball_of_interior_circle c x ρ r hx] with z hz
  calc
    ‖z‖ = ‖(z-c)+c‖ := by rw [sub_add_cancel]
    _ ≤ ‖z-c‖+‖c‖ := norm_add_le _ _
    _ ≤ R := by linarith [mem_ball_iff_norm.mp hz]

/-- The covariance with the exterior pin is precisely the regular equator term. -/
theorem circleAverage_pin_covariance_interior {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c x : ℂ) (R ρ r : ℝ) (hR : 1 < R) (hpin : ‖c‖+ρ ≤ R)
    (hx : ‖x-c‖+Real.exp (-r) < ρ) :
    covariance (circleAverageL2 hc (x,r)) (circleAverageL2 hc (0,-Real.log R)) P =
      ∫ z, Real.log (normPlus z) ∂circleMeasure x r := by
  rw [covariance_congr_ae (circleAverageL2_ae_eq hc (x,r)) (circleAverageL2_ae_eq hc (0,-Real.log R)),
    circleAverage_covariance_integral P X Xc hX hc]
  apply integral_congr_ae
  filter_upwards [interior_circle_norm_le_pin c x R ρ r hpin hx] with z hz
  rw [integral_gffKernel_exterior_origin R hR,max_eq_left hz]
  ring

/-- The actual pinned circle covariance cancels both equator regular terms. -/
theorem pinnedCircleL2_covariance_interior {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c x y : ℂ) (R ρ r s : ℝ) (hR : 1 < R) (hpin : ‖c‖+ρ ≤ R)
    (hx : ‖x-c‖+Real.exp (-r) < ρ) (hy : ‖y-c‖+Real.exp (-s) < ρ) :
    covariance (⇑(circleAverageL2 hc (x,r)-circleAverageL2 hc (0,-Real.log R)))
      (⇑(circleAverageL2 hc (y,s)-circleAverageL2 hc (0,-Real.log R))) P =
      Real.log R-(∫ z, Real.log (max (Real.exp (-s)) ‖y-z‖) ∂circleMeasure x r) := by
  let _ := hX.1
  have hxx : covariance (circleAverageL2 hc (x,r)) (circleAverageL2 hc (y,s)) P =
      -(∫ z, Real.log (max (Real.exp (-s)) ‖y-z‖) ∂circleMeasure x r)+
        (∫ z, Real.log (normPlus z) ∂circleMeasure x r)+
        (∫ z, Real.log (normPlus z) ∂circleMeasure y s) := by
    rw [covariance_congr_ae (circleAverageL2_ae_eq hc (x,r)) (circleAverageL2_ae_eq hc (y,s)),
      circleAverage_covariance_integral P X Xc hX hc,integral_integral_gffKernel_eq_logmax]
  have hpp : covariance (circleAverageL2 hc (0,-Real.log R)) (circleAverageL2 hc (0,-Real.log R)) P = Real.log R := by
    rw [covariance_congr_ae (circleAverageL2_ae_eq hc (0,-Real.log R)) (circleAverageL2_ae_eq hc (0,-Real.log R)),
      circleAverage_covariance_self X Xc hX hc,circleSelfEnergy_exterior_origin R hR]
  have hxpin := circleAverage_pin_covariance_interior P X Xc hX hc c x R ρ r hR hpin hx
  have hypin := circleAverage_pin_covariance_interior P X Xc hX hc c y R ρ s hR hpin hy
  have hpiny : covariance (circleAverageL2 hc (0,-Real.log R)) (circleAverageL2 hc (y,s)) P = _ :=
    (covariance_comm _ _).trans hypin
  rw [covariance_L2_sub_left,covariance_L2_sub_right,covariance_L2_sub_right,hxx,hxpin,hpiny,hpp]
  ring

/-- Orthogonal residuals subtract only the regular harmonic covariance. -/
theorem covariance_L2_orthogonal_residuals {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A B U V : Lp ℝ 2 P)
    (hAV : covariance (⇑(A-U)) V P = 0) (hBU : covariance (⇑(B-V)) U P = 0) :
    covariance (⇑(A-U)) (⇑(B-V)) P = covariance A B P-covariance U V P := by
  rw [covariance_L2_sub_left] at hBU
  have hUB : covariance U B P = covariance U V P := by
    rw [covariance_comm U B,covariance_comm U V]
    exact sub_eq_zero.mp hBU
  rw [covariance_L2_sub_right,covariance_L2_sub_left,hUB,hAV]
  ring

/-- The actual Dirichlet circle residual has the exact double-circle Green covariance. -/
theorem dirichletCircleResidualL2_covariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ ε : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε) (hpin : ‖c‖+ρ ≤ R)
    (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hmean : ∀ z ∈ ball c ρ, (∫ ω, V ω z ∂P) = 0)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ))
    (hcov : ∀ z w, z ∈ ball c ρ → w ∈ ball c ρ →
      covariance (fun ω => V ω z) (fun ω => V ω w) P = Real.log R+Real.log ρ-
        Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖)
    (hlim : ∀ z (hz : z ∈ ball c ρ), Tendsto (fun k => eLpNorm
      (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
        (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-V ω z) 2 P) atTop (𝓝 0))
    (hVm : Measurable (fun p : Ω × ℂ => V p.1 p.2))
    (hVh : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (V ω) (ball c ρ))
    (x y : ℂ) (r s : ℝ)
    (hx : ‖x-c‖+Real.exp (-r) < ρ) (hy : ‖y-c‖+Real.exp (-s) < ρ) :
    covariance (dirichletCircleResidualL2 P X Xc hc c R ρ V hV x r)
      (dirichletCircleResidualL2 P X Xc hc c R ρ V hV y s) P =
      ∫ v, ∫ w, diskGreenKernel c ρ hρ v w ∂circleMeasure y s ∂circleMeasure x r := by
  let _ := hX.1
  have hxs : x ∈ ball c ρ := mem_ball_iff_norm.mpr (by linarith [Real.exp_pos (-r)])
  have hys : y ∈ ball c ρ := mem_ball_iff_norm.mpr (by linarith [Real.exp_pos (-s)])
  have hsub (z : ℂ) (t : ℝ) : dirichletCircleResidualL2 P X Xc hc c R ρ V hV z t =
      (circleAverageL2 hc (z,t)-circleAverageL2 hc (0,-Real.log R))-poissonFamilyL2 P c ρ V hV z := by
    unfold dirichletCircleResidualL2
    abel
  have hxU := dirichletCircleResidualL2_poisson_covariance_zero P X Xc hX hc c R ρ ε hR hρ hε hpin
    V hV hmean hU hcov hlim hVm hVh x r hx y hys
  have hyU := dirichletCircleResidualL2_poisson_covariance_zero P X Xc hX hc c R ρ ε hR hρ hε hpin
    V hV hmean hU hcov hlim hVm hVh y s hy x hxs
  rw [hsub] at hxU hyU
  rw [hsub,hsub,covariance_L2_orthogonal_residuals P _ _ _ _ hxU hyU,
    pinnedCircleL2_covariance_interior P X Xc hX hc c x y R ρ r s hR hpin hx hy,
    covariance_congr_ae (poissonFamilyL2_ae_eq P c ρ V hV x hxs) (poissonFamilyL2_ae_eq P c ρ V hV y hys),
    hcov x y hxs hys,integral_integral_diskGreenKernel c x y ρ r s hρ hx hy]
  ring

/-- The actual raw distribution sigma algebra supports every Dirichlet circle clause of
`DOZZ.exists_exteriorPinned_markov_uniform`. -/
theorem exists_dirichletDistribution_circle_green {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ ε : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε) (hpin : ‖c‖+ρ ≤ R)
    (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hmean : ∀ z ∈ ball c ρ, (∫ ω, V ω z ∂P) = 0)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ))
    (hcov : ∀ z w, z ∈ ball c ρ → w ∈ ball c ρ →
      covariance (fun ω => V ω z) (fun ω => V ω w) P = Real.log R+Real.log ρ-
        Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖)
    (hlim : ∀ z (hz : z ∈ ball c ρ), Tendsto (fun k => eLpNorm
      (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
        (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-V ω z) 2 P) atTop (𝓝 0))
    (hVm : Measurable (fun p : Ω × ℂ => V p.1 p.2))
    (hVh : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (V ω) (ball c ρ) ∧ ContinuousOn (V ω) (ball c ρ)) :
    ∃ Dc : Ω → ℂ → ℝ → ℝ,
      Measurable[(MeasurableSpace.comap
        (fun ω => fun f : TestFn => dirichletDistribution P X Xc hX hc c R ρ (by linarith) V hV hU ω f)
        MeasurableSpace.pi).prod inferInstance] (fun p : Ω × (ℂ × ℝ) => Dc p.1 p.2.1 p.2.2) ∧
      IsGaussianProcess (fun p : {p : ℂ × ℝ // ‖p.1-c‖+Real.exp (-p.2) < ρ} => fun ω => Dc ω p.1.1 p.1.2) P ∧
      (∀ x r, ‖x-c‖+Real.exp (-r) < ρ → MemLp (fun ω => Dc ω x r) 2 P ∧
        (∫ ω, Dc ω x r ∂P) = 0 ∧
        (fun ω => Xc ω x r) =ᵐ[P] fun ω => Dc ω x r+V ω x-equatorRestorationScalar Xc R (by linarith) ω) ∧
      (∀ x y r s, ‖x-c‖+Real.exp (-r) < ρ → ‖y-c‖+Real.exp (-s) < ρ →
        covariance (fun ω => Dc ω x r) (fun ω => Dc ω y s) P =
          ∫ v, ∫ w, diskGreenKernel c ρ hρ v w ∂circleMeasure y s ∂circleMeasure x r) := by
  obtain ⟨Dc,hDcm,hDcg,hDc,hDce⟩ := exists_dirichletDistribution_circle_gaussian_split
    P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hcov hlim hVm hVh
  refine ⟨Dc,hDcm,hDcg,hDc,?_⟩
  intro x y r s hx hy
  rw [covariance_congr_ae (hDce x r hx) (hDce y s hy)]
  exact dirichletCircleResidualL2_covariance P X Xc hX hc c R ρ ε hR hρ hε hpin
    V hV hmean hU hcov hlim hVm (hVh.mono (fun ω hω => hω.1)) x y r s hx hy

/-- The actual harmonic L² family is continuous on its open disk. -/
theorem continuousOn_poissonFamilyL2_of_covariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (c : ℂ) (R ρ : ℝ) (hρ : 0 < ρ)
    (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hmean : ∀ z ∈ ball c ρ, (∫ ω, V ω z ∂P) = 0)
    (hcov : ∀ z w, z ∈ ball c ρ → w ∈ ball c ρ →
      covariance (fun ω => V ω z) (fun ω => V ω w) P = Real.log R+Real.log ρ-
        Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖) :
    ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ) := by
  classical
  rw [continuousOn_iff_continuous_domRestrict]
  convert continuous_poisson_gaussian_toLp P c R ρ hρ
    (fun z : {z : ℂ // z ∈ ball c ρ} => fun ω => V ω z.1)
    (fun z => hV z.1 z.2) (fun z => hmean z.1 z.2)
    (fun z w => hcov z.1 w.1 z.2 w.2) using 1
  funext z
  change (if hz : z.1 ∈ ball c ρ then (hV z.1 hz).toLp (fun ω => V ω z.1) else 0) = _
  simp only [dite_eq_left z.2]

/-- Supported versions assemble the jointly Gaussian complement and mutually independent blocks. -/
theorem finiteMarkovComplement_gaussian_independence {Ω I : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (R : ℝ) (hR : 0 < R)
    (Z : I → Lp ℝ 2 P) (hZ : IsGaussianProcess (fun i => ⇑(Z i)) P)
    (D : Fin n → Ω → Distr) (T : Fin n → TestFn → Lp ℝ 2 P)
    (hD : ∀ i (f : TestFn), (fun ω => D i ω f) =ᵐ[P] ⇑(T i f))
    (hYspan : ∀ f, exteriorPinnedTestL2 P X Xc hX hc R hR f ∈ gaussianHilbertSpan Z)
    (hTspan : ∀ i f, T i f ∈ gaussianHilbertSpan Z)
    (hself : ∀ i f g, covariance (T i f) (exteriorPinnedTestL2 P X Xc hX hc R hR g) P = covariance (T i f) (T i g) P)
    (hcross : ∀ i j, i ≠ j → ∀ f g, covariance (T i f) (T j g) P = 0) :
    IsGaussianProcess (fun f : TestFn => fun ω => finiteMarkovComplement X Xc R hR D ω f) P ∧
      iIndepFun (fun j : Option (Fin n) => fun ω => fun f : TestFn =>
        match j with | none => finiteMarkovComplement X Xc R hR D ω f | some i => D i ω f) P := by
  let _ := hX.1
  let Y := exteriorPinnedTestL2 P X Xc hX hc R hR
  let U : Option (Fin n) → TestFn → Ω → ℝ := fun j f ω =>
    match j with | none => finiteMarkovComplement X Xc R hR D ω f | some i => D i ω f
  have hG := finiteMarkovTestL2Family_isGaussianProcess P Z hZ Y T hYspan hTspan
  have hU : ∀ j f, U j f =ᵐ[P] ⇑(finiteMarkovTestL2Family P Y T j f) := by
    intro j f
    cases j with
    | none => exact finiteMarkovComplement_apply_ae_eq P X Xc hX hc R hR D T hD f
    | some i => exact hD i f
  exact ⟨finiteMarkovVersion_block_isGaussianProcess P Y T U hG hU none,
    finiteMarkovVersion_iIndepFun P Y T U hG hU hself hcross⟩

/-- Flattened Dirichlet process independence gives the literal nested finite family. -/
theorem IndepFun.dirichlet_curry {Ω J : Type*} [MeasurableSpace Ω] [MeasurableSpace J] {n : ℕ}
    {P : Measure Ω} {D : Fin n → Ω → Distr} {V : Ω → J}
    (h : IndepFun (fun ω (p : Fin n × TestFn) => D p.1 ω p.2) V P) :
    IndepFun (fun ω => fun i => fun f : TestFn => D i ω f) V P := by
  have hm : Measurable (fun F : (Fin n × TestFn) → ℝ => fun i => fun f : TestFn => F (i,f)) :=
    Measurable.of_eval (fun i => Measurable.of_eval (fun f => measurable_pi_apply (i,f)))
  exact h.comp hm measurable_id
/-- Exterior-pin Markov decomposition with all-order uniform harmonic moments, for the separated
two-insertion joint tail [KRV, Lemma 7.3] (erratum K9, see docs/ERRATA-AND-DEVIATIONS.md). For this
application take `n = 2`, `ρ = 5/4`, `a = 1` and a fixed positive separation margin. The bound
precedes every realization and center choice. Neither the pin scalar nor the exterior field of `X`
is asserted independent. The circle-cutoff conjuncts (with a `σ(Dᵢ) ⊗ Borel`-measurable version
`Dc`) are the form needed for that tail estimate; the test-level conjuncts alone do not reach it. -/
theorem exists_exteriorPinned_markov_uniform
    (n : ℕ) (R ρ a δ : ℝ) (hR : 1 < R) (hρ : 0 < ρ)
    (haρ : a < ρ) (hδ : 0 < δ) :
    ∃ C : ℝ → ℝ, (∀ l, 0 < l → 0 < C l) ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω]
      (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ),
      IsEquatorGFF P X → IsCircleAverage P X Xc →
    ∀ c : Fin n → ℂ,
      (∀ i, ‖c i‖ + ρ + δ ≤ R) →
      (∀ i j, i ≠ j → 2 * ρ + δ ≤ dist (c i) (c j)) →
    ∃ (D : Fin n → Ω → Distr) (H : Ω → Distr)
      (Hi : Fin n → Ω → ℂ → ℝ) (Dc : Fin n → Ω → ℂ → ℝ → ℝ) (ε : ℝ) (q : ℕ → ℝ → ℝ)
      (p : Fin n → ℂ → ℕ → TestFn),
      0 < ε ∧ ε < δ / 2 ∧
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (q k) ∧ HasCompactSupport (q k) ∧
        tsupport (q k) ⊆ Ioo 0 (ε / (k + 1)) ∧
        (∀ t, 0 ≤ q k t) ∧ (∫ t : ℝ, q k t) = 1) ∧
      (∀ i z (hz : z ∈ ball (c i) ρ), ∀ k,
        (∀ w, p i z k w = poissonCollarValue (c i) z ρ hρ hz (q k) w) ∧
        tsupport (p i z k) ⊆ (⋃ j, ball (c j) ρ)ᶜ) ∧
      (∀ i z, z ∈ ball (c i) ρ →
        Tendsto (fun k => eLpNorm
          (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω (p i z k) - Hi i ω z) 2 P)
          atTop (𝓝 0)) ∧
      (∀ i, IsGaussianProcess (fun f : TestFn => fun ω => D i ω f) P ∧
        (∀ f : TestFn, Measurable (fun ω => D i ω f) ∧
          MemLp (fun ω => D i ω f) 2 P ∧ (∫ ω, D i ω f ∂P) = 0) ∧
        (∀ f g : TestFn, covariance (fun ω => D i ω f) (fun ω => D i ω g) P =
          diskGreenCovariance (c i) ρ hρ f g)) ∧
      IsGaussianProcess (fun f : TestFn => fun ω => H ω f) P ∧
      (∀ f : TestFn, Measurable (fun ω => H ω f) ∧
        MemLp (fun ω => H ω f) 2 P ∧ (∫ ω, H ω f ∂P) = 0) ∧
      (∀ i, Measurable (fun w : Ω × ℂ => Hi i w.1 w.2)) ∧
      (∀ i z, z ∈ ball (c i) ρ →
        MemLp (fun ω => Hi i ω z) 2 P ∧ (∫ ω, Hi i ω z ∂P) = 0) ∧
      (∀ i z w, z ∈ ball (c i) ρ → w ∈ ball (c i) ρ →
        covariance (fun ω => Hi i ω z) (fun ω => Hi i ω w) P =
          Real.log R + Real.log ρ -
            Real.log ‖(ρ : ℂ) ^ 2 - (z - c i) * star (w - c i)‖) ∧
      (∀ᵐ ω ∂P,
        (∀ f : TestFn, exteriorPinnedEvaluation X Xc R (by linarith) ω f =
          (∑ i, D i ω f) + H ω f) ∧
          (∀ f : TestFn, X ω f = (∑ i, D i ω f) + H ω f -
          equatorRestorationScalar Xc R (by linarith) ω * (∫ z : ℂ, f z)) ∧
        (∀ i, InnerProductSpace.HarmonicOnNhd (Hi i ω) (ball (c i) ρ) ∧
          ContDiffOn ℝ (⊤ : ℕ∞) (Hi i ω) (ball (c i) ρ)) ∧
        (∀ i (f : TestFn), tsupport f ⊆ ball (c i) ρ →
          H ω f = (∫ z : ℂ, f z * Hi i ω z)) ∧
        (∀ i (f : TestFn), tsupport f ⊆ (closedBall (c i) ρ)ᶜ → D i ω f = 0)) ∧
      iIndepFun (fun j : Option (Fin n) => fun ω => fun f : TestFn =>
        match j with | none => H ω f | some i => D i ω f) P ∧
      IndepFun (fun ω => fun i => fun f : TestFn => D i ω f)
        (fun ω => fun f : {f : TestFn // tsupport f ⊆ (⋃ i, ball (c i) ρ)ᶜ} =>
          exteriorPinnedEvaluation X Xc R (by linarith) ω f.val) P ∧
      (∀ i l, 0 < l →
        ∫⁻ ω, ENNReal.ofReal (Real.exp (l *
            |equatorRestorationScalar Xc R (by linarith) ω|)) *
          ⨆ z ∈ closedBall (c i) a, ENNReal.ofReal (Real.exp (l * |Hi i ω z|)) ∂P
          ≤ ENNReal.ofReal (C l)) ∧
      -- Circle cutoffs of each Dirichlet field, radius `e^{-r}` as in `IsCircleAverage`.
      (∀ i, Measurable[(MeasurableSpace.comap (fun ω => fun f : TestFn => D i ω f)
          MeasurableSpace.pi).prod inferInstance]
        (fun w : Ω × (ℂ × ℝ) => Dc i w.1 w.2.1 w.2.2)) ∧
      (∀ i, IsGaussianProcess (fun p : {p : ℂ × ℝ // ‖p.1 - c i‖ + Real.exp (-p.2) < ρ} =>
        fun ω => Dc i ω p.1.1 p.1.2) P) ∧
      (∀ i (x : ℂ) (r : ℝ), ‖x - c i‖ + Real.exp (-r) < ρ →
        MemLp (fun ω => Dc i ω x r) 2 P ∧ (∫ ω, Dc i ω x r ∂P) = 0 ∧
        (fun ω => Xc ω x r) =ᵐ[P] fun ω =>
          Dc i ω x r + Hi i ω x - equatorRestorationScalar Xc R (by linarith) ω) ∧
      (∀ i (x y : ℂ) (r s : ℝ), ‖x - c i‖ + Real.exp (-r) < ρ →
        ‖y - c i‖ + Real.exp (-s) < ρ →
        covariance (fun ω => Dc i ω x r) (fun ω => Dc i ω y s) P =
          ∫ v, ∫ w, diskGreenKernel (c i) ρ hρ v w ∂circleMeasure y s ∂circleMeasure x r) := by
  classical
  refine ⟨exteriorPinnedHarmonicMomentBound R ρ a,
    fun l _ => exteriorPinnedHarmonicMomentBound_pos R ρ a l hρ haρ,?_⟩
  intro Ω _ P X Xc hX hc c hmargin hsep
  let _ := hX.1
  let ε : ℝ := δ/4
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hεδ2 : ε < δ/2 := by dsimp only [ε]; linarith
  have hεδ : ε < δ := by linarith
  have hRp : 0 < R := by linarith
  have hpin i : ‖c i‖+ρ ≤ R := by linarith [hmargin i]
  have hfamily i := exists_exteriorPinned_harmonic_poisson_family P X Xc hX hc (c i) R ρ ε δ
    hR hρ hε hεδ (hmargin i)
  choose Hi hHim hHih hHiG hHi hHicov using hfamily
  have hHimem i z hz := (hHi i z hz).1
  have hHimean i z hz := (hHi i z hz).2.1
  have hHilim i z hz := (hHi i z hz).2.2
  have hUc i := continuousOn_poissonFamilyL2_of_covariance P (c i) R ρ hρ
    (Hi i) (hHimem i) (hHimean i) (hHicov i)
  let T (i : Fin n) (f : TestFn) : Lp ℝ 2 P :=
    dirichletCompletedL2Map P X Xc hX hc (c i) R ρ hRp (Hi i) (hHimem i) (hUc i)
      (diskTestRestrictionL2 (c i) ρ f)
  let D (i : Fin n) : Ω → Distr :=
    dirichletDistribution P X Xc hX hc (c i) R ρ hRp (Hi i) (hHimem i) (hUc i)
  let H : Ω → Distr := finiteMarkovComplement X Xc R hRp D
  have hDversion i f : (fun ω => D i ω f) =ᵐ[P] ⇑(T i f) :=
    dirichletDistribution_apply_ae_eq P X Xc hX hc (c i) R ρ hRp (Hi i) (hHimem i) (hUc i) f
  have hDm i f : Measurable (fun ω => D i ω f) :=
    measurable_dirichletDistribution_apply P X Xc hX hc (c i) R ρ hRp (Hi i) (hHimem i) (hUc i) f
  have hDmem i f : MemLp (fun ω => D i ω f) 2 P :=
    dirichletDistribution_apply_memLp P X Xc hX hc (c i) R ρ hRp (Hi i) (hHimem i) (hUc i) f
  have hDmean i f : (∫ ω, D i ω f ∂P) = 0 :=
    dirichletDistribution_apply_integral_zero P X Xc hX hc (c i) R ρ ε hR hρ hε (hpin i)
      (Hi i) (hHimem i) (hHimean i) (hUc i) (hHicov i) (hHilim i) f
  have hDcov i f g : covariance (fun ω => D i ω f) (fun ω => D i ω g) P = diskGreenCovariance (c i) ρ hρ f g :=
    dirichletDistribution_covariance P X Xc hX hc (c i) R ρ ε hR hρ hε (hpin i)
      (Hi i) (hHimem i) (hHimean i) (hUc i) (hHicov i) (hHilim i) f g
  have hDG i : IsGaussianProcess (fun f : TestFn => fun ω => D i ω f) P :=
    dirichletDistribution_isGaussianProcess P X Xc hX hc (c i) R ρ ε hR hρ hε (hpin i)
      (Hi i) (hHimem i) (hHimean i) (hUc i) (hHicov i) (hHilim i)
  have hTspan i f : T i f ∈ gaussianHilbertSpan (gffStructureL2Family X Xc hX hc) :=
    dirichletCompletedL2Map_mem_original_gaussianHilbertSpan P X Xc hX hc (c i) R ρ ε hR hρ hε (hpin i)
      (Hi i) (hHimem i) (hHimean i) (hUc i) (hHicov i) (hHilim i) _
  have hself i f g : covariance (T i f) (exteriorPinnedTestL2 P X Xc hX hc R hRp g) P = covariance (T i f) (T i g) P := by
    rw [dirichletCompletedL2Map_test_covariance P X Xc hX hc (c i) R ρ ε hR hρ hε (hpin i)
        (Hi i) (hHimem i) (hHimean i) (hUc i) (hHicov i) (hHilim i),
      dirichletCompletedL2Map_covariance P X Xc hX hc (c i) R ρ ε hR hρ hε (hpin i)
        (Hi i) (hHimem i) (hHimean i) (hUc i) (hHicov i) (hHilim i)]
  have hcross i j (hij : i ≠ j) f g : covariance (T i f) (T j g) P = 0 :=
    dirichletCompletedL2Map_separated_covariance_zero P X Xc hX hc (c i) R ρ ε hR hρ hε (hpin i)
      (Hi i) (hHimem i) (hHimean i) (hUc i) (hHicov i) (hHilim i)
      (c j) (hpin j) δ hδ hεδ (hsep i j hij)
      (Hi j) (hHimem j) (hHimean j) (hUc j) (hHicov j) (hHilim j) f g
  obtain ⟨hHG,hblocks⟩ := finiteMarkovComplement_gaussian_independence P X Xc hX hc R hRp
    (gffStructureL2Family X Xc hX hc) (gffStructureL2Family_isGaussianProcess X Xc hX hc)
    D T hDversion (exteriorPinnedTestL2_mem_original_gaussianHilbertSpan P X Xc hX hc R hRp)
    hTspan hself hcross
  let E := {f : TestFn // tsupport f ⊆ (⋃ i, ball (c i) ρ)ᶜ}
  have hDYzero i f (g : E) : covariance (T i f) (exteriorPinnedTestL2 P X Xc hX hc R hRp g.1) P = 0 := by
    rw [dirichletCompletedL2Map_test_covariance P X Xc hX hc (c i) R ρ ε hR hρ hε (hpin i)
      (Hi i) (hHimem i) (hHimean i) (hUc i) (hHicov i) (hHilim i)]
    exact diskGreenCovariance_eq_zero_of_exterior_union c ρ hρ i f g.1 g.2
  have hexind : IndepFun (fun ω => fun i => fun f : TestFn => D i ω f)
      (fun ω => fun f : E => exteriorPinnedEvaluation X Xc R hRp ω f.1) P := by
    apply IndepFun.dirichlet_curry
    exact finiteDirichletVersion_indep_pinned P (gffStructureL2Family X Xc hX hc)
      (gffStructureL2Family_isGaussianProcess X Xc hX hc) T
      (fun g : E => exteriorPinnedTestL2 P X Xc hX hc R hRp g.1) hTspan
      (fun g => exteriorPinnedTestL2_mem_original_gaussianHilbertSpan P X Xc hX hc R hRp g.1)
      (fun i f ω => D i ω f) (fun g ω => exteriorPinnedEvaluation X Xc R hRp ω g.1)
      hDversion (fun g => (exteriorPinnedTestL2_ae_eq P X Xc hX hc R hRp g.1).symm) hDYzero
  have hDext i : ∀ᵐ ω ∂P, ∀ f : TestFn, tsupport f ⊆ (closedBall (c i) ρ)ᶜ → D i ω f = 0 :=
    ae_dirichletDistribution_exterior_tests_zero P X Xc hX hc (c i) R ρ hRp (Hi i) (hHimem i) (hUc i)
  have hlocal i : ∀ᵐ ω ∂P, ∀ f : TestFn, tsupport f ⊆ ball (c i) ρ →
      exteriorPinnedEvaluation X Xc R hRp ω f-D i ω f = ∫ z : ℂ, f z*Hi i ω z :=
    ae_dirichletDistribution_interior_harmonic_agreement P X Xc hX hc (c i) R ρ ε hR hρ hε (hpin i)
      (Hi i) (hHimem i) (hHimean i) (hUc i) (hHicov i) (hHilim i) (hHim i)
      ((hHih i).mono (fun ω hω => hω.2.continuousOn))
  have hHlocal := ae_finiteMarkovComplement_harmonic_agreement P X Xc R hRp c ρ D Hi
    (separated_interior_test_support_exterior c ρ δ hδ hsep) hlocal hDext
  have hcircle i := exists_dirichletDistribution_circle_green P X Xc hX hc (c i) R ρ ε hR hρ hε (hpin i)
    (Hi i) (hHimem i) (hHimean i) (hUc i) (hHicov i) (hHilim i) (hHim i)
    ((hHih i).mono (fun ω hω => ⟨hω.1,hω.2.continuousOn⟩))
  choose Dc hDcm hDcG hDc hDccov using hcircle
  let p (i : Fin n) (z : ℂ) (k : ℕ) : TestFn :=
    if hz : z ∈ ball (c i) ρ then canonicalPoissonCollarTest (c i) z ρ ε hρ hε hz k else 0
  have hp i z (hz : z ∈ ball (c i) ρ) k : p i z k = canonicalPoissonCollarTest (c i) z ρ ε hρ hε hz k := by
    simp only [p,dite_eq_left hz]
  refine ⟨D,H,Hi,Dc,ε,poissonCollarDensity ε hε,p,hε,hεδ2,?_,?_,?_,?_,hHG,?_,hHim,?_,hHicov,?_,hblocks,hexind,?_,hDcm,hDcG,hDc,hDccov⟩
  · intro k
    exact ⟨poissonCollarDensity_contDiff ε hε k,poissonCollarDensity_hasCompactSupport ε hε k,
      tsupport_poissonCollarDensity_subset ε hε k,poissonCollarDensity_nonneg ε hε k,
      integral_poissonCollarDensity ε hε k⟩
  · intro i z hz k
    rw [hp i z hz k]
    refine ⟨fun w => rfl,?_⟩
    exact tsupport_poissonCollarTest_exterior c ρ (ε/((k : ℝ)+1)) δ hρ
      ((poissonCollarWidth_le ε hε k).trans_lt hεδ2) hsep i z hz _
      (poissonCollarDensity_contDiff ε hε k) (tsupport_poissonCollarDensity_subset ε hε k)
  · intro i z hz
    simpa only [hp i z hz] using hHilim i z hz
  · intro i
    exact ⟨hDG i,fun f => ⟨hDm i f,hDmem i f,hDmean i f⟩,hDcov i⟩
  · intro f
    exact ⟨measurable_finiteMarkovComplement_apply P X Xc hX hc R hRp D hDm f,
      finiteMarkovComplement_apply_memLp P X Xc hX hc R hRp D hDmem f,
      finiteMarkovComplement_apply_integral_zero P X Xc hX hc R hRp D hDmem hDmean f⟩
  · intro i z hz
    exact ⟨hHimem i z hz,hHimean i z hz⟩
  · filter_upwards [ae_finiteMarkovComplement_restoration P X Xc hc R hRp D,
      ae_all_iff.mpr hHih,hHlocal,ae_all_iff.mpr hDext] with ω hrestore hh hhl hde
    exact ⟨finiteMarkovComplement_decomposition X Xc R hRp D ω,hrestore,hh,hhl,hde⟩
  · intro i l hl
    exact exteriorPinned_harmonic_uniform_moments P X Xc hX hc (c i) R ρ a hR hρ haρ
      (Hi i) (hHim i) (hHih i) (hHiG i) (hHimem i) (hHimean i) (hHicov i) l hl

end DOZZ.Proofs
