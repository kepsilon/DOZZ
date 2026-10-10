/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.RestartPast
/-! The Williams inner copy retains its joint law with the actual outer past. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- A measurable code for the inward exponential mass on all measure-valued inputs. -/
noncomputable def reflectedInwardPolarMassCode (γ ν : ℝ)
    (p : BrownianPath × Measure ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, ∫⁻ t, (if 0 < t then ENNReal.ofReal
    (Real.exp (γ * (p.1 (Real.toNNReal t) - ν * t))) else 0)
      ∂(finiteRestrictionOnSet (translationShell n) p.2 : Measure ℝ)

/-- The measurable code agrees with the literal polar integral on every locally finite input. -/
theorem reflected_inwardPolarMassCode_eq (γ ν : ℝ) (D : BrownianPath) (Z : Measure ℝ)
    (hfin : ∀ a b : ℝ, Z (Icc a b) < ⊤) :
    reflectedInwardPolarMassCode γ ν (D,Z) =
      ∫⁻ t, (if 0 < t then ENNReal.ofReal
        (Real.exp (γ * (D (Real.toNNReal t) - ν * t))) else 0) ∂Z := by
  have hshell (n : ℕ) : Z (translationShell n) < ⊤ :=
    lt_of_le_of_lt (measure_mono (translationShell_subset_window n)) (hfin _ _)
  exact (lintegral_eq_tsum_finiteRestrictionOnSet_translationShell _ Z hshell).symm

/-- The polar mass is jointly measurable in the continuous Brownian path and lateral measure. -/
theorem reflected_measurable_inwardPolarMassCode (γ ν : ℝ) :
    Measurable (reflectedInwardPolarMassCode γ ν) := by
  have ht : Measurable (fun p : BrownianPath × ℝ => p.1 (Real.toNNReal p.2)) :=
    continuous_eval.measurable.comp (measurable_fst.prodMk
      (continuous_real_toNNReal.measurable.comp measurable_snd))
  have hi : Measurable (fun p : BrownianPath × ℝ => if 0 < p.2 then
      ENNReal.ofReal (Real.exp (γ * (p.1 (Real.toNNReal p.2) - ν * p.2))) else 0) :=
    Measurable.ite (measurableSet_lt measurable_const measurable_snd)
      (((ht.sub (measurable_snd.const_mul ν)).const_mul γ).exp.ennreal_ofReal) measurable_const
  apply Measurable.tsum
  intro n
  exact (measurable_lintegral_finiteMeasure_parameter hi).comp
    (measurable_fst.prodMk
      ((measurable_finiteRestrictionOnSet _ (measurableSet_translationShell n)).comp measurable_snd))

/-- The independent inner lateral copy has Williams' exact law jointly with any actual outer
past independent of the restarted Brownian path. No independence of the source lateral
measure from that outer past is required. -/
theorem reflected_copied_williams_joint_law
    {Ω ζ : Type*} [MeasurableSpace Ω] [MeasurableSpace ζ]
    (P : Measure Ω) (D : Ω → BrownianPath) (hD : AEMeasurable D P)
    (hB : IsBrownianReal (fun t p => p t) (P.map D))
    (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (hDZ : IndepFun D Z P) (Y : Ω → ζ) (hY : AEMeasurable Y P)
    (hYD : IndepFun Y D P) (ν : ℝ) (hν : 0 < ν)
    (Qν : Measure BrownianPath) (hQν : IsNegativeConditionedBrownianLaw ν Qν) :
    (P.prod P).map (fun ω : Ω × Ω => (Y ω.1, ∫⁻ t,
      (if 0 < t then ENNReal.ofReal (Real.exp
        (γ * (D ω.1 (Real.toNNReal t) - ν * t))) else 0) ∂Z ω.2)) =
      (P.map Y).prod
        ((((((brownianMaximumReferenceLaw ν).prod Qν).map
          (fun v => (v.1, negativeConditionedLastExitSegment v.1 v.2))).prod Qν).prod
            (P.map Z)).map (williamsMassFunctional γ)) := by
  let _ : IsProbabilityMeasure P := hZ.2.2.1
  have hZm : AEMeasurable Z P := hZ.2.2.2.1
  let F := reflectedInwardPolarMassCode γ ν
  have hF : Measurable F := reflected_measurable_inwardPolarMassCode γ ν
  have hpair : AEMeasurable (fun ω : Ω × Ω => (Y ω.1,(D ω.1,Z ω.2))) (P.prod P) :=
    (hY.comp_quasiMeasurePreserving measurePreserving_fst.quasiMeasurePreserving).prodMk
      ((hD.comp_quasiMeasurePreserving measurePreserving_fst.quasiMeasurePreserving).prodMk
        (hZm.comp_quasiMeasurePreserving measurePreserving_snd.quasiMeasurePreserving))
  have hfin : ∀ᵐ ω : Ω × Ω ∂P.prod P, ∀ a b : ℝ, Z ω.2 (Icc a b) < ⊤ :=
    measurePreserving_snd.quasiMeasurePreserving.ae hZ.2.2.2.2.1
  have he : (fun ω : Ω × Ω => (Y ω.1, ∫⁻ t,
      (if 0 < t then ENNReal.ofReal (Real.exp (γ * (D ω.1 (Real.toNNReal t)-ν*t))) else 0)
        ∂Z ω.2)) =ᵐ[P.prod P] (fun ω : Ω × Ω => (Y ω.1, F (D ω.1,Z ω.2))) := by
    filter_upwards [hfin] with ω hω
    exact Prod.ext rfl (reflected_inwardPolarMassCode_eq γ ν (D ω.1) (Z ω.2) hω).symm
  rw [Measure.map_congr he]
  have hm := AEMeasurable.map_map_of_aemeasurable
    (measurable_id.prodMap hF).aemeasurable hpair
  change ((P.prod P).map (fun ω : Ω × Ω => (Y ω.1,(D ω.1,Z ω.2)))).map
    (Prod.map id F) = (P.prod P).map (fun ω : Ω × Ω => (Y ω.1,F (D ω.1,Z ω.2))) at hm
  rw [← hm, reflected_copied_triple_law P Y D Z hY hD hZm hYD,
    ← Measure.map_prod_map (P.map Y) ((P.map D).prod (P.map Z)) measurable_id hF,
    Measure.map_id]
  have hj := (indepFun_iff_map_prod_eq_prod_map_map hD hZm).mp hDZ
  rw [← hj, AEMeasurable.map_map_of_aemeasurable hF.aemeasurable (hD.prodMk hZm)]
  have he' : (fun ω => F (D ω,Z ω)) =ᵐ[P] fun ω => ∫⁻ t,
      (if 0 < t then ENNReal.ofReal (Real.exp (γ * (D ω (Real.toNNReal t)-ν*t))) else 0) ∂Z ω :=
    hZ.2.2.2.2.1.mono fun ω hω => reflected_inwardPolarMassCode_eq γ ν (D ω) (Z ω) hω
  simp only [Function.comp_def]
  rw [Measure.map_congr he']
  rw [williams_polar_mass_law P D hD hB γ Z hZ hDZ ν hν Qν hQν]

end DOZZ.Proofs
