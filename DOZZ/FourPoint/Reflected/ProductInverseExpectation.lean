/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.InverseMassExpectation
public import Mathlib.MeasureTheory.Integral.Prod
/-! A finite added mass converts extended-real inverse moments to signed real increments. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

theorem reflected_product_inverse_increment_expectation
    {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (R : Measure Λ) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (A : Ω → ℝ≥0∞) (b : Ω → ℝ) (T : Λ → ℝ≥0∞)
    (hA : AEMeasurable A P) (hb : AEMeasurable b P) (hT : AEMeasurable T R)
    (hAf : ∀ᵐ ω ∂P, A ω ≠ ⊤) (hbf : ∀ᵐ ω ∂P, 0 ≤ b ω)
    (hTf : ∀ᵐ ω ∂R, T ω ≠ ⊤) (p : ℝ) (hp : 0 ≤ p)
    (hfin : (∫⁻ ω, A ω^(-p) ∂P) < ⊤) :
    let D := fun v : Ω × Λ => ((A v.1).toReal+b v.1*(T v.2).toReal)^(-p)-(A v.1).toReal^(-p)
    (∫⁻ v : Ω × Λ, (A v.1+ENNReal.ofReal (b v.1)*T v.2)^(-p) ∂P.prod R) < ⊤ ∧
    Integrable D (P.prod R) ∧
    (∫⁻ v : Ω × Λ, (A v.1+ENNReal.ofReal (b v.1)*T v.2)^(-p) ∂P.prod R).toReal-
      (∫⁻ ω, A ω^(-p) ∂P).toReal = ∫ v, D v ∂P.prod R := by
  have hAm : AEMeasurable (fun v : Ω × Λ => A v.1) (P.prod R) :=
    hA.comp_quasiMeasurePreserving measurePreserving_fst.quasiMeasurePreserving
  have hbm : AEMeasurable (fun v : Ω × Λ => b v.1) (P.prod R) :=
    hb.comp_quasiMeasurePreserving measurePreserving_fst.quasiMeasurePreserving
  have hTm : AEMeasurable (fun v : Ω × Λ => T v.2) (P.prod R) :=
    hT.comp_quasiMeasurePreserving measurePreserving_snd.quasiMeasurePreserving
  have hbase : (∫⁻ v : Ω × Λ, A v.1^(-p) ∂P.prod R) = ∫⁻ ω, A ω^(-p) ∂P := by
    have hf : AEMeasurable (fun ω => A ω^(-p)) ((P.prod R).map Prod.fst) := by
      rw [(measurePreserving_fst (μ := P) (ν := R)).map_eq]
      exact hA.pow_const (-p)
    have he := lintegral_map' hf
      (measurable_fst.aemeasurable : AEMeasurable (Prod.fst : Ω × Λ → Ω) (P.prod R))
    rw [(measurePreserving_fst (μ := P) (ν := R)).map_eq] at he
    exact he.symm
  have hS : AEMeasurable (fun v : Ω × Λ => ENNReal.ofReal (b v.1)*T v.2) (P.prod R) :=
    hbm.ennreal_ofReal.mul hTm
  have h := reflected_ennreal_inverse_increment_expectation (P.prod R)
    (fun v : Ω × Λ => A v.1) (fun v => ENNReal.ofReal (b v.1)*T v.2) hAm hS p hp
    (hbase.symm ▸ hfin)
  have he : (fun v : Ω × Λ => ((A v.1+ENNReal.ofReal (b v.1)*T v.2)^(-p)).toReal-
      (A v.1^(-p)).toReal) =ᵐ[P.prod R]
      fun v => ((A v.1).toReal+b v.1*(T v.2).toReal)^(-p)-(A v.1).toReal^(-p) := by
    filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae hAf,
      measurePreserving_fst.quasiMeasurePreserving.ae hbf,
      measurePreserving_snd.quasiMeasurePreserving.ae hTf] with v hAv hbv hTv
    simp only [← ENNReal.toReal_rpow,
      ENNReal.toReal_add hAv (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hTv),
      ENNReal.toReal_mul,ENNReal.toReal_ofReal hbv]
  refine ⟨h.1,h.2.1.congr he,?_⟩
  rw [← hbase,h.2.2]
  exact integral_congr_ae he

end DOZZ.Proofs
