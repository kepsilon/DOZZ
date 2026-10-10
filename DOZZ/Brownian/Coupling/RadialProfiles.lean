/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Coupling.SkeletonDensity
public import DOZZ.Brownian.Barrier.GaussianTilting

/-!
# Radial endpoint profiles for entire finite histories

Symmetry of the Cartesian heat density and the actual vector Markov law show that multiplying
by any finite family of radial observation tests leaves a radial density at the final vector.

The cylindrical identity can therefore average the terminal Gaussian tilt while retaining all
previous observations.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology Classical

namespace DOZZ.Proofs

/-- Radial heat propagation with an arbitrary Cartesian terminal test, in adjoint form. -/
theorem lintegral_radial_profile_heat (t : ℝ≥0) (ht : 0 < t)
    (u f : ℝ → ℝ≥0∞) (hu : Measurable u) (hf : Measurable f)
    (H : EuclideanSpace ℝ (Fin 3) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ z : EuclideanSpace ℝ (Fin 3), u ‖z‖ *
      ∫⁻ w, f ‖z + w‖ * H (z + w) ∂radialGaussianVectorMeasure t) =
    ∫⁻ w : EuclideanSpace ℝ (Fin 3),
      (f ‖w‖ * radialHeatConvolution t u w) * H w := by
  have hfu : Measurable (fun w : EuclideanSpace ℝ (Fin 3) => f ‖w‖ * H w) :=
    (hf.comp continuous_norm.measurable).mul hH
  have hinner (z : EuclideanSpace ℝ (Fin 3)) :
      (∫⁻ w, f ‖z + w‖ * H (z + w) ∂radialGaussianVectorMeasure t) =
        ∫⁻ w, radialGaussianVectorDensity t (w - z) * (f ‖w‖ * H w) := by
    rw [← lintegral_map hfu (show Measurable (fun w => z + w) from
      (continuous_const.add continuous_id).measurable),
      radialGaussianVectorMeasure_add_map_eq_density z t ht,
      lintegral_withDensity_eq_lintegral_mul volume
        (show Measurable (fun w => radialGaussianVectorDensity t (w - z)) from
          (measurable_radialGaussianVectorDensity t).comp (measurable_id.sub_const z)) hfu]
    rfl
  simp_rw [hinner]
  have hm : Measurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      (u ‖p.1‖ * radialGaussianVectorDensity t (p.2 - p.1)) * (f ‖p.2‖ * H p.2)) :=
    ((hu.comp measurable_fst.norm).mul (measurable_radialGaussianVectorDensity_sub t)).mul
      (hfu.comp measurable_snd)
  calc
    _ = ∫⁻ z, ∫⁻ w, (u ‖z‖ * radialGaussianVectorDensity t (w - z)) * (f ‖w‖ * H w) := by
      apply lintegral_congr
      intro z
      rw [← lintegral_const_mul _ (show Measurable (fun w =>
        radialGaussianVectorDensity t (w - z) * (f ‖w‖ * H w)) from
          ((measurable_radialGaussianVectorDensity t).comp (measurable_id.sub_const z)).mul hfu)]
      simp only [mul_assoc]
    _ = ∫⁻ w, ∫⁻ z, (u ‖z‖ * radialGaussianVectorDensity t (w - z)) * (f ‖w‖ * H w) :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro w
      rw [lintegral_mul_const _ (show Measurable (fun z =>
        u ‖z‖ * radialGaussianVectorDensity t (w - z)) from
          (hu.comp continuous_norm.measurable).mul
            ((measurable_radialGaussianVectorDensity t).comp (measurable_const.sub measurable_id)))]
      have he : (∫⁻ z, u ‖z‖ * radialGaussianVectorDensity t (w - z)) = radialHeatConvolution t u w := by
        simp_rw [mul_comm (u _)]
        exact lintegral_radial_heat_density_reverse t ht u hu w
      rw [he]
      ac_rfl

/-- A finite product of radial observation tests is measurable on the actual Wiener source. -/
theorem measurable_wienerRadial_product {n : ℕ} (times : Fin n → ℝ≥0)
    (f : Fin n → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun V : BrownianTriple => ∏ i, f i ‖wienerVectorEval (times i) V‖) :=
  Finset.measurable_prod Finset.univ fun i _ =>
    (hf i).comp (measurable_wienerVectorEval (times i)).norm

/-- Every finite radial history leaves a measurable radial density at its last Cartesian vector. -/
theorem exists_wienerRadial_endpoint_profile : ∀ (n : ℕ)
    (times : Fin (n + 1) → ℝ≥0) (f : Fin (n + 1) → ℝ → ℝ≥0∞),
    (∀ i, 0 < times i) → StrictMono times → (∀ i, Measurable (f i)) →
    ∃ u : ℝ → ℝ≥0∞, Measurable u ∧ ∀ (H : EuclideanSpace ℝ (Fin 3) → ℝ≥0∞),
      Measurable H →
      (∫⁻ V, (∏ i, f i ‖wienerVectorEval (times i) V‖) *
        H (wienerVectorEval (times (Fin.last n)) V) ∂wienerTripleMeasure) =
      ∫⁻ z : EuclideanSpace ℝ (Fin 3), u ‖z‖ * H z := by
  intro n
  induction n with
  | zero =>
    intro times f hpos hmono hf
    let u := fun r : ℝ => f 0 r * (ENNReal.ofReal (radialGaussianConstant (times 0)) *
      ENNReal.ofReal (Real.exp (-r ^ 2 / (2 * (times 0 : ℝ)))))
    have hu : Measurable u := (hf 0).mul (measurable_const.mul
      (show Measurable (fun r : ℝ => ENNReal.ofReal (Real.exp (-r ^ 2 / (2 * (times 0 : ℝ))))) from by fun_prop))
    refine ⟨u, hu, ?_⟩
    intro H hH
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, Fin.last_zero]
    rw [← lintegral_map (show Measurable (fun z : EuclideanSpace ℝ (Fin 3) => f 0 ‖z‖ * H z) from
      ((hf 0).comp continuous_norm.measurable).mul hH)
      (measurable_wienerVectorEval (times 0)), (wienerVectorEval_hasLaw (times 0)).map_eq,
      lintegral_radialGaussianVectorMeasure (times 0) (hpos 0) _
        (show Measurable (fun z : EuclideanSpace ℝ (Fin 3) => f 0 ‖z‖ * H z) from
          ((hf 0).comp continuous_norm.measurable).mul hH)]
    apply lintegral_congr
    intro z
    change _ = (f 0 ‖z‖ * _) * H z
    ac_rfl
  | succ n ih =>
    intro times f hpos hmono hf
    let past := Fin.init times
    let fp := Fin.init f
    let s := times ((Fin.last n).castSucc)
    let dt := times (Fin.last (n + 1)) - s
    have hlastlt : s < times (Fin.last (n + 1)) := hmono (Fin.castSucc_lt_last _)
    have hdt : 0 < dt := tsub_pos_iff_lt.mpr hlastlt
    have hsum : s + dt = times (Fin.last (n + 1)) := add_tsub_cancel_of_le hlastlt.le
    have hpast : ∀ i, past i ≤ s := fun i =>
      hmono.monotone (Fin.strictMono_castSucc.monotone (Fin.le_last i))
    obtain ⟨u, hu, hprofile⟩ := ih past fp (fun i => hpos i.castSucc)
      (hmono.comp Fin.strictMono_castSucc) (fun i => hf i.castSucc)
    let v := fun r : ℝ => f (Fin.last (n + 1)) r * radialHeatConvolution dt u (radialAxisVector r)
    have haxis : Measurable (radialAxisVector : ℝ → EuclideanSpace ℝ (Fin 3)) := by
      apply (PiLp.continuous_toLp 2 _).measurable.comp
      exact measurable_pi_iff.mpr fun i => by split_ifs <;> fun_prop
    have hv : Measurable v := (hf _).mul ((measurable_radialHeatConvolution dt u hu).comp haxis)
    refine ⟨v, hv, ?_⟩
    intro H hH
    let G := fun p : BrownianTriple × EuclideanSpace ℝ (Fin 3) =>
      (∏ i, fp i ‖wienerVectorEval (past i) p.1‖) * (f (Fin.last (n + 1)) ‖p.2‖ * H p.2)
    have hG : Measurable G :=
      ((measurable_wienerRadial_product past fp (fun i => hf i.castSucc)).comp measurable_fst).mul
        (((hf _).comp measurable_snd.norm).mul (hH.comp measurable_snd))
    have hmk := wienerVector_deterministic_markov_lintegral s dt G hG
    dsimp only [G] at hmk
    simp_rw [wienerVectorEval_stop_of_le _ _ (hpast _), hsum] at hmk
    rw [show (∫⁻ V, (∏ i, f i ‖wienerVectorEval (times i) V‖) *
        H (wienerVectorEval (times (Fin.last (n + 1))) V) ∂wienerTripleMeasure) =
        ∫⁻ V, (∏ i, fp i ‖wienerVectorEval (past i) V‖) *
          (f (Fin.last (n + 1)) ‖wienerVectorEval (times (Fin.last (n + 1))) V‖ *
            H (wienerVectorEval (times (Fin.last (n + 1))) V)) ∂wienerTripleMeasure by
      apply lintegral_congr
      intro V
      rw [Fin.prod_univ_castSucc]
      exact mul_assoc _ _ _, hmk]
    let K := fun z : EuclideanSpace ℝ (Fin 3) =>
      ∫⁻ w, f (Fin.last (n + 1)) ‖z + w‖ * H (z + w) ∂radialGaussianVectorMeasure dt
    have hK : Measurable K := Measurable.lintegral_prod_right
      (((hf _).comp (measurable_fst.add measurable_snd).norm).mul
        (hH.comp (measurable_fst.add measurable_snd)))
    have hfactor : (∫⁻ V, ∫⁻ w, (∏ i, fp i ‖wienerVectorEval (past i) V‖) *
        (f (Fin.last (n + 1)) ‖wienerVectorEval s V + w‖ * H (wienerVectorEval s V + w))
          ∂radialGaussianVectorMeasure dt ∂wienerTripleMeasure) =
        ∫⁻ V, (∏ i, fp i ‖wienerVectorEval (past i) V‖) * K (wienerVectorEval s V) ∂wienerTripleMeasure := by
      apply lintegral_congr
      intro V
      exact lintegral_const_mul _
        (((hf _).comp (measurable_const.add measurable_id).norm).mul
          (hH.comp (measurable_const.add measurable_id)))
    have hpk := hprofile K hK
    change (∫⁻ V, (∏ i, fp i ‖wienerVectorEval (past i) V‖) * K (wienerVectorEval s V) ∂wienerTripleMeasure) = _ at hpk
    rw [hfactor, hpk,
      lintegral_radial_profile_heat dt hdt u _ hu (hf _) H hH]
    apply lintegral_congr
    intro w
    have hrot := radialHeatConvolution_eq_of_norm_eq dt hdt u hu w (radialAxisVector ‖w‖)
      (by rw [norm_radialAxisVector, abs_of_nonneg (norm_nonneg _)])
    dsimp only [v]
    rw [hrot]

/-- The spherical average of the longitudinal exponential, with its continuous zero value. -/
noncomputable def radialAngularFactor (a r : ℝ) : ℝ :=
  if a * r = 0 then 1 else Real.sinh (a * r) / (a * r)

/-- The angular factor is measurable on its entire real state carrier. -/
theorem measurable_radialAngularFactor (a : ℝ) : Measurable (radialAngularFactor a) := by
  exact Measurable.ite (measurableSet_eq_fun (measurable_const.mul measurable_id) measurable_const)
    measurable_const (((measurable_const.mul measurable_id).sinh).div (measurable_const.mul measurable_id))

/-- At zero tilt every direction has likelihood one. -/
theorem radialAngularFactor_zero (r : ℝ) : radialAngularFactor 0 r = 1 := by
  simp only [radialAngularFactor, zero_mul, ite_true]

/-- For a nonzero tilt and positive radius the angular average is the literal sinh quotient. -/
theorem radialAngularFactor_of_ne_zero (a r : ℝ) (ha : a ≠ 0) (hr : r ≠ 0) :
    radialAngularFactor a r = Real.sinh (a * r) / (a * r) := by
  simp only [radialAngularFactor, mul_ne_zero ha hr, ite_false]

/-- The angular likelihood is nonnegative at every nonnegative radius. -/
theorem radialAngularFactor_nonneg (a r : ℝ) (hr : 0 ≤ r) : 0 ≤ radialAngularFactor a r := by
  by_cases har : a * r = 0
  · simp only [radialAngularFactor, har, ite_true]; exact zero_le_one
  · have ha : a ≠ 0 := left_ne_zero_of_mul har
    have hr' : r ≠ 0 := right_ne_zero_of_mul har
    rw [radialAngularFactor_of_ne_zero a r ha hr', div_mul_eq_div_div]
    exact div_nonneg (sinh_div_nonneg_longitudinal a r ha hr) hr

/-- Cylindrical integration averages the longitudinal likelihood of any radial endpoint density. -/
theorem lintegral_radial_profile_angular (u : ℝ → ℝ≥0∞) (hu : Measurable u) (a : ℝ) :
    (∫⁻ z : EuclideanSpace ℝ (Fin 3), u ‖z‖ *
      ENNReal.ofReal (Real.exp (a * WithLp.ofLp z 0))) =
      ∫⁻ z : EuclideanSpace ℝ (Fin 3), u ‖z‖ * ENNReal.ofReal (radialAngularFactor a ‖z‖) := by
  by_cases ha : a = 0
  · subst a
    simp only [zero_mul, Real.exp_zero, ENNReal.ofReal_one, radialAngularFactor_zero, mul_one]
  · have hm : Measurable (fun z : EuclideanSpace ℝ (Fin 3) => u ‖z‖ *
        ENNReal.ofReal (Real.exp (a * WithLp.ofLp z 0))) :=
      (hu.comp continuous_norm.measurable).mul (by fun_prop)
    have hm' : Measurable (fun z : EuclideanSpace ℝ (Fin 3) => u ‖z‖ *
        ENNReal.ofReal (radialAngularFactor a ‖z‖)) :=
      (hu.comp continuous_norm.measurable).mul
        (((measurable_radialAngularFactor a).comp continuous_norm.measurable).ennreal_ofReal)
    rw [← (PiLp.volume_preserving_toLp (Fin 3)).lintegral_comp hm,
      ← (PiLp.volume_preserving_toLp (Fin 3)).lintegral_comp hm', lintegral_three_radial_exp u hu a ha]
    have hr := lintegral_three_radial_zero (fun r => u r * ENNReal.ofReal (radialAngularFactor a r))
      (hu.mul (measurable_radialAngularFactor a).ennreal_ofReal)
    change _ = ∫⁻ z : Fin 3 → ℝ, (fun r => u r * ENNReal.ofReal (radialAngularFactor a r)) ‖WithLp.toLp 2 z‖
    rw [hr]
    congr 1
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hrad : 0 ≤ radialAngularFactor a r := radialAngularFactor_nonneg a r hr.le
    dsimp only
    rw [mul_assoc, ← ENNReal.ofReal_mul hrad]
    congr 2
    rw [radialAngularFactor_of_ne_zero a r ha hr.ne']
    field_simp

/-- Averaging the terminal direction preserves every earlier radial observation test. -/
theorem wienerRadial_product_terminal_angular (n : ℕ)
    (times : Fin (n + 1) → ℝ≥0) (f : Fin (n + 1) → ℝ → ℝ≥0∞)
    (hpos : ∀ i, 0 < times i) (hmono : StrictMono times) (hf : ∀ i, Measurable (f i))
    (a : ℝ) :
    (∫⁻ V, (∏ i, f i ‖wienerVectorEval (times i) V‖) *
      ENNReal.ofReal (Real.exp (a * V 0 (times (Fin.last n)))) ∂wienerTripleMeasure) =
    ∫⁻ V, (∏ i, f i ‖wienerVectorEval (times i) V‖) *
      ENNReal.ofReal (radialAngularFactor a ‖wienerVectorEval (times (Fin.last n)) V‖) ∂wienerTripleMeasure := by
  obtain ⟨u, hu, hprofile⟩ := exists_wienerRadial_endpoint_profile n times f hpos hmono hf
  have hL := hprofile (fun z => ENNReal.ofReal (Real.exp (a * WithLp.ofLp z 0))) (by fun_prop)
  have hR := hprofile (fun z => ENNReal.ofReal (radialAngularFactor a ‖z‖))
    (((measurable_radialAngularFactor a).comp continuous_norm.measurable).ennreal_ofReal)
  exact hL.trans ((lintegral_radial_profile_angular u hu a).trans hR.symm)

/-- Drift only the first of the three actual coordinate paths. -/
noncomputable def wienerTripleDrift (a : ℝ) (V : BrownianTriple) : BrownianTriple :=
  fun i => if i = 0 then driftedBrownianPath a (V i) else V i

/-- Coordinate drift is measurable on the full continuous-path product. -/
theorem measurable_wienerTripleDrift (a : ℝ) : Measurable (wienerTripleDrift a) := by
  apply measurable_pi_iff.mpr
  intro i
  dsimp only [wienerTripleDrift]
  split_ifs
  · exact continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk (measurable_pi_apply i))
  · exact measurable_pi_apply i

/-- The drifted Wiener vector is precisely the vector inside the Rogers--Pitman norm. -/
theorem wienerVectorEval_drift (a : ℝ) (V : BrownianTriple) (t : ℝ≥0) :
    wienerVectorEval t (wienerTripleDrift a V) = rogersPitmanVectorAt a V t := by
  apply WithLp.ofLp_injective 2
  funext i
  dsimp only [wienerVectorEval, wienerTripleDrift, rogersPitmanVectorAt]
  split_ifs <;> simp only [driftedBrownianPath, ContinuousMap.coe_mk, add_zero]

/-- Finite-horizon Gaussian tilting acts on the actual independent Wiener triple. -/
theorem wienerTriple_drift_stopped_lintegral (a : ℝ) (T : ℝ≥0) (hT : T ≠ 0)
    (F : BrownianTriple → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ V, F (wienerTripleStop T (wienerTripleDrift a V)) ∂wienerTripleMeasure) =
    ∫⁻ V, brownianGaussianLikelihood a T (V 0 T) * F (wienerTripleStop T V) ∂wienerTripleMeasure := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => BrownianPath) 0
  let Q := Measure.pi (fun _ : Fin 2 => wienerPathMeasure)
  have he : MeasurePreserving e wienerTripleMeasure (wienerPathMeasure.prod Q) :=
    measurePreserving_piFinSuccAbove (α := fun _ : Fin 3 => BrownianPath)
      (fun _ : Fin 3 => wienerPathMeasure) 0
  have hmL := hF.comp ((measurable_wienerTripleStop T).comp (measurable_wienerTripleDrift a))
  have hmR : Measurable (fun V : BrownianTriple =>
      brownianGaussianLikelihood a T (V 0 T) * F (wienerTripleStop T V)) :=
    ((measurable_brownianGaussianLikelihood a T).comp
      ((show Measurable (fun p : BrownianPath => p T) from ContinuousMap.measurable_eval T).comp
        (measurable_pi_apply (0 : Fin 3)))).mul
        (hF.comp (measurable_wienerTripleStop T))
  rw [← he.symm.lintegral_comp_emb e.symm.measurableEmbedding
      (fun V => F (wienerTripleStop T (wienerTripleDrift a V))),
    ← he.symm.lintegral_comp_emb e.symm.measurableEmbedding
      (fun V => brownianGaussianLikelihood a T (V 0 T) * F (wienerTripleStop T V)),
    lintegral_prod_symm _ (show Measurable (fun p => F (wienerTripleStop T (wienerTripleDrift a (e.symm p)))) from
      hmL.comp e.symm.measurable).aemeasurable,
    lintegral_prod_symm _ (show Measurable (fun p => brownianGaussianLikelihood a T (e.symm p 0 T) *
      F (wienerTripleStop T (e.symm p))) from hmR.comp e.symm.measurable).aemeasurable]
  apply lintegral_congr
  intro W
  let tail := fun i : Fin 2 => stopBrownianPath (W i) T
  let G := fun p : BrownianPath => F (e.symm (p, tail))
  have hG : Measurable G := hF.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const))
  have hscalar := brownianFiniteTilt_stoppedPath_lintegral wienerPathMeasure
    wienerPathMeasure_isBrownian.toIsPreBrownianReal a T hT G hG
  have hstop (p : BrownianPath) : wienerTripleStop T (e.symm (p, W)) =
      e.symm (stopBrownianPath p T, tail) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e, wienerTripleStop, tail]
    · simp [e, wienerTripleStop, tail]
  have hdrift (p : BrownianPath) : wienerTripleDrift a (e.symm (p, W)) =
      e.symm (driftedBrownianPath a p, W) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e, wienerTripleDrift]
    · simp [e, wienerTripleDrift]
  simp_rw [hdrift, hstop]
  have hhead (p : BrownianPath) : e.symm (p, W) 0 = p := by simp [e]
  simp_rw [hhead]
  exact hscalar

/-- The terminal radial likelihood for the drifted norm skeleton. -/
noncomputable def radialTerminalLikelihood (a t r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-a ^ 2 * t / 2)) * ENNReal.ofReal (radialAngularFactor a r)

/-- The terminal radial likelihood is measurable on the whole real state carrier. -/
theorem measurable_radialTerminalLikelihood (a t : ℝ) : Measurable (radialTerminalLikelihood a t) :=
  measurable_const.mul (measurable_radialAngularFactor a).ennreal_ofReal

/-- All finite Rogers--Pitman observation tests have the actual Cartesian terminal tilt. -/
theorem rogersPitman_skeleton_terminal_tilt {n : ℕ} (a : ℝ)
    (times : Fin (n + 1) → ℝ≥0) (hT : times (Fin.last n) ≠ 0)
    (hle : ∀ i, times i ≤ times (Fin.last n))
    (F : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ V, F (fun i => ‖rogersPitmanVectorAt a V (times i)‖) ∂wienerTripleMeasure) =
    ∫⁻ V, brownianGaussianLikelihood a (times (Fin.last n)) (V 0 (times (Fin.last n))) *
      F (wienerRadialSamples times V) ∂wienerTripleMeasure := by
  have h := wienerTriple_drift_stopped_lintegral a (times (Fin.last n)) hT
    (fun V => F (wienerRadialSamples times V)) (hF.comp (measurable_wienerRadialSamples times))
  simp_rw [wienerRadialSamples_stop times _ hle] at h
  change (∫⁻ V, F (fun i => ‖wienerVectorEval (times i) (wienerTripleDrift a V)‖) ∂wienerTripleMeasure) = _ at h
  simp_rw [wienerVectorEval_drift] at h
  exact h

/-- The full drifted radial product test has the averaged terminal likelihood. -/
theorem rogersPitman_radial_product_terminal_likelihood (n : ℕ) (a : ℝ)
    (times : Fin (n + 1) → ℝ≥0) (f : Fin (n + 1) → ℝ → ℝ≥0∞)
    (hpos : ∀ i, 0 < times i) (hmono : StrictMono times) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ V, (∏ i, f i ‖rogersPitmanVectorAt a V (times i)‖) ∂wienerTripleMeasure) =
    ∫⁻ V, (∏ i, f i ‖wienerVectorEval (times i) V‖) *
      radialTerminalLikelihood a (times (Fin.last n)) ‖wienerVectorEval (times (Fin.last n)) V‖
        ∂wienerTripleMeasure := by
  have hF : Measurable (fun x : Fin (n + 1) → ℝ => ∏ i, f i (x i)) :=
    Finset.measurable_prod Finset.univ fun i _ => (hf i).comp (measurable_pi_apply i)
  rw [rogersPitman_skeleton_terminal_tilt a times (hpos _).ne'
    (fun i => hmono.monotone (Fin.le_last i)) _ hF]
  let c := ENNReal.ofReal (Real.exp (-a ^ 2 * (times (Fin.last n) : ℝ) / 2))
  have hm : Measurable (fun V : BrownianTriple =>
      (∏ i, f i ‖wienerVectorEval (times i) V‖) *
        ENNReal.ofReal (Real.exp (a * V 0 (times (Fin.last n))))) :=
    (measurable_wienerRadial_product times f hf).mul
      (((show Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (a * x))) from by fun_prop).comp
        ((show Measurable (fun p : BrownianPath => p (times (Fin.last n))) from
          ContinuousMap.measurable_eval _).comp (measurable_pi_apply (0 : Fin 3)))))
  have hm' : Measurable (fun V : BrownianTriple =>
      (∏ i, f i ‖wienerVectorEval (times i) V‖) *
        ENNReal.ofReal (radialAngularFactor a ‖wienerVectorEval (times (Fin.last n)) V‖)) :=
    (measurable_wienerRadial_product times f hf).mul
      (((measurable_radialAngularFactor a).comp (measurable_wienerVectorEval _).norm).ennreal_ofReal)
  calc
    _ = c * ∫⁻ V, (∏ i, f i ‖wienerVectorEval (times i) V‖) *
        ENNReal.ofReal (Real.exp (a * V 0 (times (Fin.last n)))) ∂wienerTripleMeasure := by
      rw [← lintegral_const_mul c hm]
      apply lintegral_congr
      intro V
      dsimp only [brownianGaussianLikelihood, wienerRadialSamples, c]
      rw [show a * V 0 (times (Fin.last n)) - a ^ 2 * (times (Fin.last n) : ℝ) / 2 =
        (-a ^ 2 * (times (Fin.last n) : ℝ) / 2) + a * V 0 (times (Fin.last n)) by ring,
        Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
      ac_rfl
    _ = c * ∫⁻ V, (∏ i, f i ‖wienerVectorEval (times i) V‖) *
        ENNReal.ofReal (radialAngularFactor a ‖wienerVectorEval (times (Fin.last n)) V‖)
          ∂wienerTripleMeasure := by
      rw [wienerRadial_product_terminal_angular n times f hpos hmono hf a]
    _ = _ := by
      rw [← lintegral_const_mul c hm']
      apply lintegral_congr
      intro V
      dsimp only [radialTerminalLikelihood, c]
      ac_rfl




end DOZZ.Proofs
