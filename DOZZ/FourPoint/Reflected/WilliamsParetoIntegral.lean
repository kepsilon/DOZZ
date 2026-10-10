/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.ReferenceParetoLaw
public import DOZZ.FourPoint.Reflected.InverseIncrementIntegrable
import Mathlib.Tactic
/-! The full and fixed-cut Williams expectations are the literal source Pareto expectations. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
namespace DOZZ.Proofs

/-- Independent maximum integration is exactly Pareto integration, retaining the correlated
source mass and restart scale and requiring only the retained inverse moment. -/
theorem reflected_williams_pareto_integral
    {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (R : Measure Λ) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (B₀ : Measure BrownianPath) (hB₀ : IsBrownianReal (fun t p => p t) B₀)
    (γ ν p : ℝ) (hγ : 0 < γ) (hν : 0 < ν) (hp : 0 < p)
    (A b : Ω → ℝ) (S : Λ → ℝ)
    (hA : ∀ᵐ ω ∂P, 0 < A ω) (hb : ∀ᵐ ω ∂P, 0 ≤ b ω) (hS : ∀ᵐ ω ∂R, 0 ≤ S ω)
    (hAm : AEMeasurable A P) (hbm : AEMeasurable b P) (hSm : AEMeasurable S R)
    (hInv : Integrable (fun ω => (A ω)^(-p)) P) :
    (∫ v : Ω × (ℝ × Λ),
      (A v.1+b v.1*Real.exp (γ*v.2.1)*S v.2.2)^(-p)-(A v.1)^(-p)
        ∂P.prod ((brownianMaximumReferenceLaw ν).prod R)) =
    ∫ v : Ω × Λ, (∫ w,
      (A v.1+b v.1*S v.2*w)^(-p)-(A v.1)^(-p) ∂paretoMeasure 1 (2*ν/γ)) ∂P.prod R := by
  let μ := brownianMaximumReferenceLaw ν
  let _ : IsProbabilityMeasure μ := isProbabilityMeasure_brownianMaximumReferenceLaw hν
  let Q := (P.prod R).prod μ
  let f := fun v : (Ω × Λ) × ℝ =>
    (A v.1.1+b v.1.1*S v.1.2*Real.exp (γ*v.2))^(-p)-(A v.1.1)^(-p)
  let e : Ω × (ℝ × Λ) ≃ᵐ (Ω × Λ) × ℝ :=
    ((MeasurableEquiv.refl Ω).prodCongr (MeasurableEquiv.prodComm : ℝ × Λ ≃ᵐ Λ × ℝ)).trans
      MeasurableEquiv.prodAssoc.symm
  have he : MeasurePreserving e (P.prod (μ.prod R)) Q := by
    exact (MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc P R μ)).comp
      ((MeasurePreserving.id P).prod (Measure.measurePreserving_swap (μ := μ) (ν := R)))
  have hA0 := (measurePreserving_fst (μ := P) (ν := R)).quasiMeasurePreserving.ae hA
  have hb0 := (measurePreserving_fst (μ := P) (ν := R)).quasiMeasurePreserving.ae hb
  have hS0 := (measurePreserving_snd (μ := P) (ν := R)).quasiMeasurePreserving.ae hS
  have hAq := (measurePreserving_fst (μ := P.prod R) (ν := μ)).quasiMeasurePreserving.ae hA0
  have hbq := (measurePreserving_fst (μ := P.prod R) (ν := μ)).quasiMeasurePreserving.ae hb0
  have hSq := (measurePreserving_fst (μ := P.prod R) (ν := μ)).quasiMeasurePreserving.ae hS0
  have hAm0 := hAm.comp_quasiMeasurePreserving
    (measurePreserving_fst (μ := P) (ν := R)).quasiMeasurePreserving
  have hbm0 := hbm.comp_quasiMeasurePreserving
    (measurePreserving_fst (μ := P) (ν := R)).quasiMeasurePreserving
  have hSm0 := hSm.comp_quasiMeasurePreserving
    (measurePreserving_snd (μ := P) (ν := R)).quasiMeasurePreserving
  have hAmq := hAm0.comp_quasiMeasurePreserving
    (measurePreserving_fst (μ := P.prod R) (ν := μ)).quasiMeasurePreserving
  have hbmq := hbm0.comp_quasiMeasurePreserving
    (measurePreserving_fst (μ := P.prod R) (ν := μ)).quasiMeasurePreserving
  have hSmq := hSm0.comp_quasiMeasurePreserving
    (measurePreserving_fst (μ := P.prod R) (ν := μ)).quasiMeasurePreserving
  have hT : ∀ᵐ v : (Ω × Λ) × ℝ ∂Q, 0 ≤ b v.1.1*S v.1.2*Real.exp (γ*v.2) := by
    filter_upwards [hbq,hSq] with v hv hSv
    exact mul_nonneg (mul_nonneg hv hSv) (Real.exp_pos _).le
  have hInvq : Integrable (fun v : (Ω × Λ) × ℝ => (A v.1.1)^(-p)) Q := by
    simpa only [mul_one] using
      (hInv.mul_prod (integrable_const (1 : ℝ))).mul_prod (integrable_const (1 : ℝ))
  have hf : Integrable f Q := reflected_inverse_increment_integrable Q p hp _ _ hAq hT hAmq
    ((hbmq.mul hSmq).mul
      (show AEMeasurable (fun v : (Ω × Λ) × ℝ => Real.exp (γ*v.2)) Q from
        (by fun_prop : Measurable (fun v : (Ω × Λ) × ℝ => Real.exp (γ*v.2))).aemeasurable)) hInvq
  have hreg : (∫ v : Ω × (ℝ × Λ),
      (A v.1+b v.1*Real.exp (γ*v.2.1)*S v.2.2)^(-p)-(A v.1)^(-p) ∂P.prod (μ.prod R)) =
      ∫ v, f v ∂Q := by
    have hh := he.integral_comp' f
    convert hh using 1
    congr 1
    funext v
    change (A v.1+b v.1*Real.exp (γ*v.2.1)*S v.2.2)^(-p)-(A v.1)^(-p) =
      (A v.1+b v.1*S v.2.2*Real.exp (γ*v.2.1))^(-p)-(A v.1)^(-p)
    rw [mul_right_comm (b v.1)]
  rw [hreg,integral_prod f hf]
  apply integral_congr_ae
  apply ae_of_all
  intro v
  have hpow : Measurable (fun w : ℝ => (A v.1+b v.1*S v.2*w)^(-p)-(A v.1)^(-p)) := by fun_prop
  have hh := integral_map
    (show AEMeasurable (fun m : ℝ => Real.exp (γ*m)) μ from (by fun_prop : Measurable _).aemeasurable)
    hpow.aestronglyMeasurable
  rw [reflected_maximum_reference_pareto_law B₀ hB₀ γ ν hγ hν] at hh
  exact hh.symm

end DOZZ.Proofs
