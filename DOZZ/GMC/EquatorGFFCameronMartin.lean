/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsGaussianL2Limit
public import DOZZ.GMC.FiniteGaussianTilt
public import DOZZ.GMC.GaussianInputs
public import Mathlib.MeasureTheory.Constructions.Cylinders

/-! Cameron--Martin on the evaluation sigma algebra, by finite cylinders. -/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

private theorem equatorGFF_tilted_eval_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : DOZZ.IsEquatorGFF P X) (L : Ω → ℝ) (hL : DOZZ.IsGaussianL2Limit P X L)
    (t : ℝ) :
    Measure.map (fun ω f => X ω f)
        (P.withDensity (fun ω => ENNReal.ofReal (Real.exp
          (t * L ω - t ^ 2 / 2 * DOZZ.gaussianVariance P L)))) =
      Measure.map (fun ω f => X ω f + t *
        DOZZ.gaussianCovariance P (fun ω => X ω f) L) P := by
  classical
  let : IsProbabilityMeasure P := hX.1
  let eval : Ω → TestFn → ℝ := fun ω f => X ω f
  let evalShift : Ω → TestFn → ℝ := fun ω f => X ω f +
    t * DOZZ.gaussianCovariance P (fun ω => X ω f) L
  let density : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp
    (t * L ω - t ^ 2 / 2 * DOZZ.gaussianVariance P L))
  let μ : Measure (TestFn → ℝ) := Measure.map eval (P.withDensity density)
  let ν : Measure (TestFn → ℝ) := Measure.map evalShift P
  have hEval : Measurable eval := by
    rw [measurable_pi_iff]
    exact fun f => (hX.2 f).1
  have hEvalShift : Measurable evalShift := by
    rw [measurable_pi_iff]
    intro f
    exact (hX.2 f).1.add measurable_const
  have hDensity : AEMeasurable density P := by
    have hlog : AEMeasurable (fun ω => t * L ω - t ^ 2 / 2 *
        DOZZ.gaussianVariance P L) P := by
      exact (hL.1.aemeasurable.const_mul t).sub (measurable_const.aemeasurable)
    exact (Real.measurable_exp.comp_aemeasurable hlog).ennreal_ofReal
  have hCylinder (s : Finset TestFn) (S : Set (∀ i : s, ℝ)) (hS : MeasurableSet S) :
      μ (MeasureTheory.cylinder s S) = ν (MeasureTheory.cylinder s S) := by
    let family : Ω → Option s → ℝ := fun ω i =>
      match i with
      | none => L ω
      | some j => X ω j.val
    let coeff : Option s → ℝ := fun i => if i = none then t else 0
    let project : (Option s → ℝ) → (∀ i : s, ℝ) := fun y i => y (some i)
    let F : (Option s → ℝ) → ℝ≥0∞ := S.indicator (fun _ => 1) ∘ project
    have hProject : Measurable project := by fun_prop
    have hF : Measurable F := by
      dsimp [F]
      exact (measurable_const.indicator hS).comp hProject
    have hJointRaw := DOZZ.Proofs.equatorGFF_finite_evaluations_with_L_jointly_gaussian
      P X hX L hL (fun i : s => i.val)
    have hJoint : DOZZ.IsCenteredJointlyGaussian P family := by
      convert hJointRaw using 1; ext ω i; cases i <;> rfl
    have hLinear (ω : Ω) : ∑ i, coeff i * family ω i = t * L ω := by
      simp [coeff, family]
    have hVariance :
        (∑ i, ∑ j, coeff i * DOZZ.gaussianCovariance P (fun ω => family ω i)
          (fun ω => family ω j) * coeff j) =
          t ^ 2 * DOZZ.gaussianVariance P L := by
      simp [coeff, family, DOZZ.gaussianVariance, DOZZ.gaussianCovariance]
      ring
    have hExponent (ω : Ω) :
        (∑ i, coeff i * family ω i) -
          (∑ i, ∑ j, coeff i * DOZZ.gaussianCovariance P
            (fun ω => family ω i) (fun ω => family ω j) * coeff j) / 2 =
        t * L ω - t ^ 2 / 2 * DOZZ.gaussianVariance P L := by
      rw [hLinear, hVariance]
      ring
    let shiftedFamily : Ω → Option s → ℝ := fun ω i =>
      family ω i + ∑ j, DOZZ.gaussianCovariance P
        (fun ω => family ω i) (fun ω => family ω j) * coeff j
    have hFiniteTilt := DOZZ.Proofs.finite_gaussian_tilt P family hJoint coeff F hF
    have hTilt :
        (∫⁻ ω, density ω * F (family ω) ∂P) =
          ∫⁻ ω, F (shiftedFamily ω) ∂P := by
      calc
        _ = ∫⁻ ω, ENNReal.ofReal (Real.exp
            ((∑ i, coeff i * family ω i) -
              (∑ i, ∑ j, coeff i * DOZZ.gaussianCovariance P
                (fun ω => family ω i) (fun ω => family ω j) * coeff j) / 2)) *
            F (family ω) ∂P := by
              apply lintegral_congr_ae
              exact ae_of_all _ (fun ω => by
                change density ω * F (family ω) = _
                dsimp [density]
                rw [← hExponent ω])
        _ = ∫⁻ ω, F (shiftedFamily ω) ∂P := hFiniteTilt
    have hPreEval : MeasurableSet (eval ⁻¹' MeasureTheory.cylinder s S) :=
      (hS.cylinder).preimage hEval
    have hPreShift : MeasurableSet (evalShift ⁻¹' MeasureTheory.cylinder s S) :=
      (hS.cylinder).preimage hEvalShift
    have hLeft : μ (MeasureTheory.cylinder s S) =
        ∫⁻ ω, density ω * F (family ω) ∂P := by
      dsimp [μ]
      rw [Measure.map_apply hEval (hS.cylinder), withDensity_apply density hPreEval,
        ← lintegral_indicator hPreEval]
      apply lintegral_congr_ae
      exact ae_of_all _ (fun ω => by
        have hproject : project (family ω) = s.restrict (eval ω) := by
          funext i
          simp [project, family, eval]
        by_cases hx : eval ω ∈ MeasureTheory.cylinder s S
        · have hxS : s.restrict (eval ω) ∈ S := by simpa using hx
          simp [F, hproject, hx, hxS]
        · have hxS : s.restrict (eval ω) ∉ S := by simpa using hx
          simp [F, hproject, hx, hxS])
    have hRight : ν (MeasureTheory.cylinder s S) =
        ∫⁻ ω, F (shiftedFamily ω) ∂P := by
      dsimp [ν]
      rw [Measure.map_apply hEvalShift (hS.cylinder)]
      calc
        P (evalShift ⁻¹' MeasureTheory.cylinder s S) =
            ∫⁻ ω, (evalShift ⁻¹' MeasureTheory.cylinder s S).indicator
              (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
                symm
                rw [lintegral_indicator_const hPreShift 1]
                simp
        _ = ∫⁻ ω, F (shiftedFamily ω) ∂P := by
              apply lintegral_congr_ae
              exact ae_of_all _ (fun ω => by
                have hcoord (i : s) : shiftedFamily ω (some i) = evalShift ω i.val := by
                  simp [shiftedFamily, family, coeff, evalShift, DOZZ.gaussianCovariance]
                  ring
                have hproject : project (shiftedFamily ω) = s.restrict (evalShift ω) := by
                  funext i
                  exact hcoord i
                by_cases hx : evalShift ω ∈ MeasureTheory.cylinder s S
                · have hxS : s.restrict (evalShift ω) ∈ S := by simpa using hx
                  simp [F, hproject, hx, hxS]
                · have hxS : s.restrict (evalShift ω) ∉ S := by simpa using hx
                  simp [F, hproject, hx, hxS])
    exact hLeft.trans (hTilt.trans hRight.symm)
  let C : Set (Set (TestFn → ℝ)) :=
    MeasureTheory.measurableCylinders (fun _ : TestFn => ℝ)
  have hCylinders : ∀ A ∈ C, μ A = ν A := by
    intro A hA
    obtain ⟨s, S, hS, rfl⟩ :=
      (MeasureTheory.mem_measurableCylinders (α := fun _ : TestFn => ℝ) A).mp hA
    exact hCylinder s S hS
  have hUnivC : Set.univ ∈ C :=
    MeasureTheory.univ_mem_measurableCylinders (fun _ : TestFn => ℝ)
  have hνUniv : ν Set.univ = 1 := by
    rw [Measure.map_apply hEvalShift MeasurableSet.univ]
    simp
  have hμUniv : μ Set.univ = 1 := by rw [hCylinders Set.univ hUnivC, hνUniv]
  have hMeasuresUniv : μ Set.univ = ν Set.univ := by rw [hμUniv, hνUniv]
  have : IsFiniteMeasure μ := ⟨by rw [hμUniv]; simp⟩
  apply ext_of_generate_finite C
    (by simpa [C] using
      (MeasureTheory.generateFrom_measurableCylinders (α := fun _ : TestFn => ℝ)).symm)
    MeasureTheory.isPiSystem_measurableCylinders hCylinders hMeasuresUniv

/-- Cameron--Martin for all measurable functions of the equator-GFF evaluations. -/
theorem equatorGFF_cameron_martin
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L)
    (t : ℝ) (H : (TestFn → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ ω,
      ENNReal.ofReal (Real.exp
        (t * L ω - t ^ 2 / 2 * gaussianVariance P L)) *
        H (fun f => X ω f) ∂P) =
    ∫⁻ ω, H (fun f => X ω f +
      t * gaussianCovariance P (fun ω => X ω f) L) ∂P := by
  let eval : Ω → TestFn → ℝ := fun ω f => X ω f
  let evalShift : Ω → TestFn → ℝ := fun ω f => X ω f +
    t * gaussianCovariance P (fun ω => X ω f) L
  let density : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp
    (t * L ω - t ^ 2 / 2 * gaussianVariance P L))
  have hEval : Measurable eval := by
    rw [measurable_pi_iff]
    exact fun f => (hX.2 f).1
  have hEvalShift : Measurable evalShift := by
    rw [measurable_pi_iff]
    intro f
    exact (hX.2 f).1.add measurable_const
  have hDensity : AEMeasurable density P := by
    have hlog : AEMeasurable (fun ω => t * L ω - t ^ 2 / 2 * gaussianVariance P L) P := by
      exact (hL.1.aemeasurable.const_mul t).sub (measurable_const.aemeasurable)
    exact (Real.measurable_exp.comp_aemeasurable hlog).ennreal_ofReal
  have hLaw := equatorGFF_tilted_eval_law P X hX L hL t
  calc
    _ = ∫⁻ ω, density ω * H (eval ω) ∂P := by rfl
    _ = ∫⁻ ω, H (eval ω) ∂P.withDensity density := by
      exact (lintegral_withDensity_eq_lintegral_mul_non_measurable₀ P hDensity
        (Filter.Eventually.of_forall (fun ω => ENNReal.ofReal_lt_top))
        (fun ω => H (eval ω))).symm
    _ = ∫⁻ y, H y ∂Measure.map eval (P.withDensity density) :=
      (lintegral_map hH hEval).symm
    _ = ∫⁻ y, H y ∂Measure.map evalShift P := by rw [hLaw]
    _ = ∫⁻ ω, H (evalShift ω) ∂P := lintegral_map hH hEvalShift

private lemma ennreal_ofReal_max_zero (x : ℝ) :
    ENNReal.ofReal (max x 0) = ENNReal.ofReal x := by
  by_cases hx : 0 ≤ x
  · simp [max_eq_left hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    simp only [ENNReal.ofReal, max_eq_right hx']
    rw [Real.toNNReal_of_nonpos hx']
    simp

/-- Signed-field Cameron--Martin follows from the measurable evaluation law and integrability of
the shifted functional. -/
theorem equatorGFF_cameron_martin_signed
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L)
    (t : ℝ) (H : (TestFn → ℝ) → ℝ) (hH : Measurable H)
    (hI : Integrable (fun ω => H (fun f => X ω f +
      t * gaussianCovariance P (fun ω => X ω f) L)) P) :
    ∫ ω, Real.exp (t * L ω - t ^ 2 / 2 * gaussianVariance P L) *
        H (fun f => X ω f) ∂P =
      ∫ ω, H (fun f => X ω f +
        t * gaussianCovariance P (fun ω => X ω f) L) ∂P := by
  classical
  let eval : Ω → TestFn → ℝ := fun ω f => X ω f
  let evalShift : Ω → TestFn → ℝ := fun ω f => X ω f +
    t * gaussianCovariance P (fun ω => X ω f) L
  let tiltExp : Ω → ℝ := fun ω => Real.exp
    (t * L ω - t ^ 2 / 2 * gaussianVariance P L)
  let G : Ω → ℝ := fun ω => tiltExp ω * H (eval ω)
  let pos : (TestFn → ℝ) → ℝ≥0∞ := fun y => ENNReal.ofReal (max (H y) 0)
  let neg : (TestFn → ℝ) → ℝ≥0∞ := fun y => ENNReal.ofReal (max (-H y) 0)
  let absH : (TestFn → ℝ) → ℝ≥0∞ := fun y => ENNReal.ofReal |H y|
  have hEval : Measurable eval := by
    rw [measurable_pi_iff]
    exact fun f => (hX.2 f).1
  have hEvalShift : Measurable evalShift := by
    rw [measurable_pi_iff]
    intro f
    exact (hX.2 f).1.add measurable_const
  have hlog : AEMeasurable (fun ω => t * L ω - t ^ 2 / 2 * gaussianVariance P L) P := by
    exact (hL.1.aemeasurable.const_mul t).sub (measurable_const.aemeasurable)
  have hTiltExp : AEMeasurable tiltExp P := by
    simpa [tiltExp, Function.comp_def] using Real.measurable_exp.comp_aemeasurable hlog
  have hGmeas : AEStronglyMeasurable G P := by
    have hpair := hTiltExp.prodMk (hH.comp_aemeasurable hEval.aemeasurable)
    exact (measurable_mul.comp_aemeasurable hpair).aestronglyMeasurable
  have hPosMeas : Measurable pos := by
    dsimp [pos]
    fun_prop
  have hNegMeas : Measurable neg := by
    dsimp [neg]
    fun_prop
  have hAbsMeas : Measurable absH := by
    dsimp [absH]
    fun_prop
  have hPosTilt := equatorGFF_cameron_martin P X hX L hL t pos hPosMeas
  have hNegTilt := equatorGFF_cameron_martin P X hX L hL t neg hNegMeas
  have hAbsTilt := equatorGFF_cameron_martin P X hX L hL t absH hAbsMeas
  have hIShift : Integrable (fun ω => H (evalShift ω)) P := by
    simpa [evalShift] using hI
  have hAbsShift : Integrable (fun ω => |H (evalShift ω)|) P := hIShift.norm
  have hAbsShiftFinite :
      ∫⁻ ω, ENNReal.ofReal (|H (evalShift ω)|) ∂P ≠ ∞ := by
    exact (lintegral_ofReal_ne_top_iff_integrable
      hAbsShift.aestronglyMeasurable (Filter.Eventually.of_forall (fun _ => abs_nonneg _))).2
      hAbsShift
  have hNormGFinite : ∫⁻ ω, ENNReal.ofReal (‖G ω‖) ∂P ≠ ∞ := by
    have hAbsG (ω : Ω) : |G ω| = tiltExp ω * |H (eval ω)| := by
      rw [show G ω = tiltExp ω * H (eval ω) by rfl, abs_mul,
        abs_of_nonneg (le_of_lt (Real.exp_pos _))]
    have hpoint (ω : Ω) : ENNReal.ofReal (‖G ω‖) =
        ENNReal.ofReal (tiltExp ω) * absH (eval ω) := by
      calc
        ENNReal.ofReal (‖G ω‖) = ENNReal.ofReal (|G ω|) := by simp
        _ = ENNReal.ofReal (tiltExp ω * |H (eval ω)|) := congrArg ENNReal.ofReal (hAbsG ω)
        _ = ENNReal.ofReal (tiltExp ω) * ENNReal.ofReal (|H (eval ω)|) :=
          ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))
        _ = ENNReal.ofReal (tiltExp ω) * absH (eval ω) := rfl
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (tiltExp ω) * absH (eval ω) ∂P := by
        apply lintegral_congr_ae
        exact ae_of_all _ (fun ω => hpoint ω)
      _ = ∫⁻ ω, absH (evalShift ω) ∂P := hAbsTilt
      _ = ∫⁻ ω, ENNReal.ofReal (|H (evalShift ω)|) ∂P := by
        apply lintegral_congr_ae
        exact ae_of_all _ (fun _ => rfl)
      _ ≠ ∞ := hAbsShiftFinite
  have hGInt : Integrable G P := by
    rw [← integrable_norm_iff hGmeas]
    exact (lintegral_ofReal_ne_top_iff_integrable hGmeas.norm
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))).mp hNormGFinite
  have hLeftPos :
      ∫⁻ ω, ENNReal.ofReal (G ω) ∂P =
        ∫⁻ ω, ENNReal.ofReal (tiltExp ω) * pos (eval ω) ∂P := by
    apply lintegral_congr_ae
    exact ae_of_all _ (fun ω => by
      change ENNReal.ofReal (G ω) = _
      rw [show G ω = tiltExp ω * H (eval ω) by rfl,
        ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
      change ENNReal.ofReal (tiltExp ω) * ENNReal.ofReal (H (eval ω)) =
        ENNReal.ofReal (tiltExp ω) * ENNReal.ofReal (max (H (eval ω)) 0)
      rw [ennreal_ofReal_max_zero])
  have hLeftNeg :
      ∫⁻ ω, ENNReal.ofReal (-G ω) ∂P =
        ∫⁻ ω, ENNReal.ofReal (tiltExp ω) * neg (eval ω) ∂P := by
    apply lintegral_congr_ae
    exact ae_of_all _ (fun ω => by
      change ENNReal.ofReal (-G ω) = _
      rw [show -G ω = tiltExp ω * (-H (eval ω)) by simp [G],
        ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
      change ENNReal.ofReal (tiltExp ω) * ENNReal.ofReal (-H (eval ω)) =
        ENNReal.ofReal (tiltExp ω) * ENNReal.ofReal (max (-H (eval ω)) 0)
      rw [ennreal_ofReal_max_zero])
  have hRightPos :
      ∫⁻ ω, pos (evalShift ω) ∂P =
        ∫⁻ ω, ENNReal.ofReal (H (evalShift ω)) ∂P := by
    apply lintegral_congr_ae
    exact ae_of_all _ (fun ω => by
      change ENNReal.ofReal (max (H (evalShift ω)) 0) = _
      exact ennreal_ofReal_max_zero _)
  have hRightNeg :
      ∫⁻ ω, neg (evalShift ω) ∂P =
        ∫⁻ ω, ENNReal.ofReal (-H (evalShift ω)) ∂P := by
    apply lintegral_congr_ae
    exact ae_of_all _ (fun ω => by
      change ENNReal.ofReal (max (-H (evalShift ω)) 0) = _
      exact ennreal_ofReal_max_zero _)
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hGInt,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hIShift,
    hLeftPos, hLeftNeg, hPosTilt, hNegTilt, hRightPos, hRightNeg]

end DOZZ.Proofs
