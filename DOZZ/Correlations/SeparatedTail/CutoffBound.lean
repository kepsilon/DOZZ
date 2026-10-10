/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.SeparatedTail.MarkovData
public import DOZZ.Correlations.SeparatedTail.ActualCutoffDomination

/-! Assemble the actual exterior-pinned cutoff domination, Kahane and Hölder estimates. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Metric Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The absolute quadratic correction is uniformly bounded on a positive bounded order range. -/
theorem separatedTail_abs_quadratic_le {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    |t^2-t| ≤ T^2+T := by
  calc
    _ ≤ |t^2|+|t| := abs_sub _ _
    _ = t^2+t := by rw [abs_of_nonneg (sq_nonneg t), abs_of_nonneg ht]
    _ ≤ _ := by nlinarith

/-- The finite-cutoff mixed moment bound of the separated joint-tail estimate, with constants
independent of centers, charges, and cutoff. The only input beyond the actual Markov realization
is the equator cutoff bound. -/
theorem separatedTail_cutoff_mixed_bound_of_markov_data
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (c : Fin 2 → ℂ) (R : ℝ) (hR : 1 < R) (hpin : ∀ i, ‖c i‖+5/4 ≤ R)
    (C : ℝ → ℝ) (data : SeparatedTailMarkovData P Xc c R hR C)
    (γ : ℝ) (hγ : 0 < γ) (α a : Fin 2 → ℝ) (hα : ∀ i, 0 ≤ α i)
    (p q T : ℝ) (hpq : p.HolderConjugate q) (hT : 0 < T)
    (ha : ∀ i, 0 < a i) (haT : ∀ i, a i ≤ T) (haqT : ∀ i, a i*q ≤ T)
    (B : ℝ≥0∞) (δ : ℝ) (hδ : 0 < δ) (hδ4 : δ < 1/4)
    (hB : ∀ i, (∫⁻ ω, cutoffWeightedGmcBallMass P Xc γ (α i) (c i) 1 δ ω ^ (a i*q) ∂P) ≤ B) :
    (∫⁻ ω, cutoffWeightedGmcBallMass P Xc γ (α 0) (c 0) 1 δ ω ^ (a 0) *
      cutoffWeightedGmcBallMass P Xc γ (α 1) (c 1) 1 δ ω ^ (a 1) ∂P) ≤
      (ENNReal.ofReal (Real.exp (γ^2*(4+2*R)/2*(2*T*p))) *
        (2*ENNReal.ofReal (C (2*(γ*T*p))))) ^ (1/p) *
      ((ENNReal.ofReal (Real.exp (γ^2*(4+2*R)/2*(T^2+T)))*B) *
        (ENNReal.ofReal (Real.exp (γ^2*(4+2*R)/2*(T^2+T)))*B)) ^ (1/q) := by
  let _ : IsProbabilityMeasure P := hX.1
  let _ : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
  let r := Real.log (1/δ)
  let L := equatorRestorationScalar Xc R (show 0 < R by linarith)
  let d : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ^2*(4+2*R)/2))
  let E (i : Fin 2) (l : ℝ) := separatedTail_harmonicEnvelope (c i) (data.H i) L l
  let D (i : Fin 2) := fieldChaosMass P (fun ω x => data.Dc i ω (separatedTail_diskPoint (c i) x) r)
    (gmcReferenceMeasure.restrict (ball (c i) 1)) (separatedTail_softWeight γ (α i) δ (c i)) γ
  let W (i : Fin 2) := cutoffWeightedGmcBallMass P Xc γ (α i) (c i) 1 δ
  have hscale : Real.exp (-r) = δ := by
    dsimp [r]
    rw [one_div, Real.log_inv, neg_neg, Real.exp_log hδ]
  have hfield (i : Fin 2) : IsCenteredGaussianField P
      (fun ω x => data.Dc i ω (separatedTail_diskPoint (c i) x) r) :=
    separatedTail_dirichletCircle_isCenteredGaussianField P (data.D i) (data.Dc i) (c i)
      (data.measurable_D i) (data.measurable_Dc i) (data.gaussian_Dc i)
      (data.mean_Dc i) r (by rw [hscale]; exact hδ4)
  have hDm (i : Fin 2) : Measurable (D i) := centeredGaussianField_fieldChaosMass_measurable
    P _ (hfield i) _ _ (separatedTail_softWeight_measurable _ _ _ _) γ
  have hDi : IndepFun (D 0) (D 1) P := separatedTail_indepFun_of_comap_measurable P _ _ _ _
    data.independent_D
    (separatedTail_dirichletChaosMass_comap_measurable P (data.D 0) (data.Dc 0) (c 0)
      (data.measurable_Dc 0) r (hfield 0) _ _ (separatedTail_softWeight_measurable _ _ _ _) γ)
    (separatedTail_dirichletChaosMass_comap_measurable P (data.D 1) (data.Dc 1) (c 1)
      (data.measurable_Dc 1) r (hfield 1) _ _ (separatedTail_softWeight_measurable _ _ _ _) γ)
  have hLm : Measurable L := equatorRestorationScalar_measurable X Xc hc R (by linarith)
  have hEm (i : Fin 2) (l : ℝ) : AEMeasurable (E i l) P := separatedTail_harmonicEnvelope_aemeasurable
    P (c i) (data.H i) L (data.measurable_H i) hLm (data.continuous_H i) l
  have hdom (i : Fin 2) : ∀ᵐ ω ∂P, W i ω ≤ d*E i γ ω*D i ω := by
    apply separatedTail_actual_cutoff_mass_le P X hX Xc hc (fun ω x => data.Dc i ω x r)
      (data.H i) L (c i) R δ γ (α i) hR (hpin i) hδ hδ4 hγ (hfield i)
      (data.measurable_H i) hLm
    · intro x hx
      exact data.split i x r (by rw [hscale]; linarith [mem_ball_iff_norm.mp hx])
    · intro x y hx hy
      exact data.covariance_Dc i x y r r (by simpa only [hscale] using hx)
        (by simpa only [hscale] using hy)
  let Eall : Ω → ℝ≥0∞ := fun ω => d^(a 0+a 1)* (E 0 (γ*a 0) ω*E 1 (γ*a 1) ω)
  have hEall : AEMeasurable Eall P := aemeasurable_const.mul
    ((hEm 0 _).mul (hEm 1 _))
  have hproduct : ∀ᵐ ω ∂P, W 0 ω ^ (a 0)*W 1 ω ^ (a 1) ≤
      Eall ω*(D 0 ω ^ (a 0)*D 1 ω ^ (a 1)) := by
    filter_upwards [hdom 0,hdom 1] with ω h0 h1
    have h := mul_le_mul' (ENNReal.rpow_le_rpow h0 (ha 0).le)
      (ENNReal.rpow_le_rpow h1 (ha 1).le)
    simp only [ENNReal.mul_rpow_of_nonneg _ _ (ha 0).le,
      ENNReal.mul_rpow_of_nonneg _ _ (ha 1).le] at h
    have he0 := separatedTail_harmonicEnvelope_rpow (c 0) (data.H 0) L γ (a 0) (ha 0) ω
    have he1 := separatedTail_harmonicEnvelope_rpow (c 1) (data.H 1) L γ (a 1) (ha 1) ω
    change (E 0 γ ω)^(a 0) = E 0 (γ*a 0) ω at he0
    change (E 1 γ ω)^(a 1) = E 1 (γ*a 1) ω at he1
    rw [he0,he1] at h
    have hd : d^(a 0+a 1) = d^(a 0)*d^(a 1) :=
      ENNReal.rpow_add _ _ (by dsimp [d]; exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')
        (by dsimp [d]; exact ENNReal.ofReal_ne_top)
    refine h.trans_eq ?_
    dsimp [Eall]
    rw [hd]
    ac_rfl
  have hEB : (∫⁻ ω, Eall ω^p ∂P) ≤
      ENNReal.ofReal (Real.exp (γ^2*(4+2*R)/2*(2*T*p)))*
        (2*ENNReal.ofReal (C (2*(γ*T*p)))) := by
    have hp := hpq.pos
    have hEnv := separatedTail_product_envelope_moment_le P (c 0) (c 1) (data.H 0) (data.H 1) L
      (hEm 0) C (data.envelope_bound 0) (data.envelope_bound 1)
      (γ*a 0) (γ*a 1) p (γ*T*p) hp (by positivity)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (haT 0) hγ.le) hp.le)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (haT 1) hγ.le) hp.le)
    have hpower : ∀ ω, Eall ω^p = d^((a 0+a 1)*p)*
        (E 0 (γ*a 0) ω*E 1 (γ*a 1) ω)^p := by
      intro ω
      dsimp [Eall]
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← ENNReal.rpow_mul]
    simp_rw [hpower]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (mul_nonneg (add_nonneg (ha 0).le (ha 1).le) hp.le)
      (by dsimp [d]; exact ENNReal.ofReal_ne_top))]
    refine mul_le_mul' ?_ hEnv
    dsimp [d]
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hcp : 0 ≤ γ^2*(4+2*R)/2 := by positivity
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (show a 0+a 1 ≤ 2*T by linarith [haT 0,haT 1]) hp.le) hcp
  have hDB (i : Fin 2) : (∫⁻ ω, D i ω^(a i*q) ∂P) ≤
      ENNReal.ofReal (Real.exp (γ^2*(4+2*R)/2*(T^2+T)))*B := by
    have h := separatedTail_dirichlet_cutoff_moment_le P X hX Xc hc (data.Dc i) (c i) R δ γ (α i)
      (a i*q) hR (hpin i) hδ hδ4 (by nlinarith [hα i])
      (mul_pos (ha i) hpq.symm.pos) (hfield i)
      (by
        intro x y hx hy
        exact data.covariance_Dc i x y r r
          (by simpa only [hscale] using hx) (by simpa only [hscale] using hy))
    refine h.trans (mul_le_mul' ?_ (hB i))
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left (separatedTail_abs_quadratic_le (mul_nonneg (ha i).le hpq.symm.pos.le) (haqT i))
    positivity
  exact separatedTail_mixed_moment_le_uniform P (W 0) (W 1) (D 0) (D 1) Eall
    (hDm 0).aemeasurable (hDm 1).aemeasurable hEall hDi (a 0) (a 1) p q (ha 0).le (ha 1).le
    hpq hproduct _ _ _ hEB (hDB 0) (hDB 1)

end DOZZ.Proofs
