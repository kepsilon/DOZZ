/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Strip.ModelLaw
public import DOZZ.Correlations.Tails.OriginPolarMass
public import DOZZ.Correlations.Tails.SingularMassMeasurability
public import DOZZ.ShiftEquations.Reflection.Witness
public import DOZZ.Statements.Brownian.EquatorGFFLateralGMCDecomposition

/-! The critical small-power limit for the genuine equator singular mass at the origin. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The origin singular mass has the Williams-model law on the original conditioned-copy
carrier, with only an independent exponential maximum added. -/
theorem lastone_origin_williams_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ ν : ℝ) (hν : 0 < ν) (M : Ω → Measure ℂ) (A : Ω → TwoSidedPath)
    (hA : AEMeasurable A P) (hBp : IsBrownianReal (fun t ω => A ω (t : ℝ)) P)
    (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z) (hAZ : IndepFun A Z P)
    (hZeq : ∀ᵐ ω ∂P, Z ω = lateralProjectedGMC γ (A ω) (M ω))
    (hM0 : ∀ᵐ ω ∂P, M ω {0} = 0)
    (B : Ω → BrownianPath × BrownianPath)
    (hB : IsTwoSidedConditionedBrownianProcess P B ν) (hInd : IndepFun B Z P) :
    P.map (localSingularMass M (fun _ => 1) 0 γ (Q γ - ν)) =
      ((brownianMaximumReferenceLaw ν).prod P).map (fun z : ℝ × Ω =>
        williamsMassFunctional γ
          (((z.1, negativeConditionedLastExitSegment z.1 (B z.2).2), (B z.2).1), Z z.2)) := by
  let : IsProbabilityMeasure P := hZ.2.2.1
  let : IsProbabilityMeasure (brownianMaximumReferenceLaw ν) :=
    isProbabilityMeasure_brownianMaximumReferenceLaw hν
  let D : Ω → BrownianPath := fun ω => radialPositiveHalf (A ω)
  have hD : AEMeasurable D P := continuous_radialPositiveHalf.measurable.comp_aemeasurable hA
  have hDB := radialPositiveHalf_map_isBrownian P A hA hBp
  have hDZ : IndepFun D Z P := hAZ.comp continuous_radialPositiveHalf.measurable measurable_id
  have hmass : (localSingularMass M (fun _ => 1) 0 γ (Q γ - ν)) =ᵐ[P]
      (fun ω => ∫⁻ t, (if 0 < t then ENNReal.ofReal
        (Real.exp (γ * (D ω (Real.toNNReal t) - ν * t))) else 0) ∂Z ω) := by
    filter_upwards [hZeq, hM0] with ω hZω hMω
    change localSingularMass (fun _ : Unit => M ω) (fun _ => 1) 0 γ (Q γ - ν) () = _
    rw [origin_singular_mass_polar γ (Q γ - ν) (A ω) (M ω) hMω, ← hZω]
    apply lintegral_congr
    intro t
    by_cases ht : 0 < t
    · rw [ite_eq_left ht, ite_eq_left ht]
      have heval : D ω (Real.toNNReal t) = A ω t := by
        change A ω ((Real.toNNReal t : ℝ≥0) : ℝ) = A ω t
        rw [Real.coe_toNNReal t ht.le]
      rw [heval]
      congr 3
      ring
    · rw [ite_eq_right ht, ite_eq_right ht]
  let Qν := P.map (fun ω => (B ω).1)
  have hQν : IsNegativeConditionedBrownianLaw ν Qν := hB.1.2
  have hW := williams_polar_mass_law P D hD hDB γ Z hZ hDZ ν hν Qν hQν
  have hInput := lastone_williamsInput_law_on_given_space P
    (brownianMaximumReferenceLaw ν) ν Qν hQν B Z hB hZ.2.2.2.1 hInd
  have hsnd := (measurePreserving_snd (μ := brownianMaximumReferenceLaw ν) (ν := P)).quasiMeasurePreserving
  have hBm := (aemeasurable_of_twoSidedConditioned hB).comp_quasiMeasurePreserving hsnd
  have hZm := hZ.2.2.2.1.comp_quasiMeasurePreserving hsnd
  have hstop := measurable_lastExitSegment_joint.comp_aemeasurable
    (measurable_fst.aemeasurable.prodMk hBm.snd)
  have hTm := ((measurable_fst.aemeasurable.prodMk hstop).prodMk hBm.fst).prodMk hZm
  rw [Measure.map_congr hmass, hW, ← hInput]
  exact AEMeasurable.map_map_of_aemeasurable
    (measurable_williamsMassFunctional γ).aemeasurable hTm

/-- The genuine local equator GMC singular mass has critical small-power expectation `2`.
The source lateral projection and conditioned family are realized on the supplied space. -/
theorem lastone_origin_smallPower_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    Tendsto (fun ν : ℝ =>
      (∫⁻ ω, localSingularMass M (fun _ => 1) 0 γ (Q γ - ν) ω ^ (ν / γ) ∂P).toReal)
      (𝓝[>] 0) (𝓝 2) := by
  let : IsProbabilityMeasure P := hX.1
  obtain ⟨A, hc, hA, hA0, hBp, hBn, hhalves, hZm, hAZ, hZ⟩ :=
    DOZZ.equatorGFF_lateral_GMC_decomposition P X M γ hγ hγ2 hX hM
  let Z : Ω → Measure ℝ := fun ω => lateralProjectedGMC γ (A ω) (M ω)
  have hsource : IsSourceLateralProjection P X γ M Z :=
    ⟨hX, hM, A, hc, hA, hA0, hBp, hBn, hhalves, hZm, hAZ, ae_of_all P (fun _ => rfl)⟩
  obtain ⟨Bc, hBc⟩ := exists_reflectionData_family P X γ M Z hsource hZ
  let B : ℝ → Ω → BrownianPath × BrownianPath := fun ν => Bc (Q γ - ν)
  have hB (ν : ℝ) (hν : 0 < ν) : IsTwoSidedConditionedBrownianProcess P (B ν) ν := by
    simpa only [B, sub_sub_cancel] using (hBc (Q γ - ν) (by linarith)).1
  have hInd (ν : ℝ) (hν : 0 < ν) : IndepFun (B ν) Z P :=
    (hBc (Q γ - ν) (by linarith)).2.2
  have hlim := lastone_williamsModel_smallPower_limit P γ hγ hγ2 Z B hB hZ hInd
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ν hν
  have hνpos : 0 < ν := hν
  have hm := localSingularMass_aemeasurable P X hX γ hγ hγ2 M hM
    (fun _ => 1) measurable_const 0 (Q γ - ν)
  have hlaw := lastone_origin_williams_law P γ ν hνpos M A hA hBp Z hZ hAZ
    (ae_of_all P fun _ => rfl) (equatorGFF_GMC_origin_null_ae P X hX γ hγ hγ2 M hM)
    (B ν) (hB ν hνpos) (hInd ν hνpos)
  have hBm := (aemeasurable_of_twoSidedConditioned (hB ν hνpos)).comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_snd (μ := brownianMaximumReferenceLaw ν) (ν := P))
  have hZm' := hZ.2.2.2.1.comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_snd (μ := brownianMaximumReferenceLaw ν) (ν := P))
  have hstop := measurable_lastExitSegment_joint.comp_aemeasurable
    (measurable_fst.aemeasurable.prodMk hBm.snd)
  have hWm := (measurable_williamsMassFunctional γ).comp_aemeasurable
    (((measurable_fst.aemeasurable.prodMk hstop).prodMk hBm.fst).prodMk hZm')
  change AEMeasurable (fun z : ℝ × Ω => williamsMassFunctional γ
    (((z.1, negativeConditionedLastExitSegment z.1 (B ν z.2).2), (B ν z.2).1), Z z.2))
      ((brownianMaximumReferenceLaw ν).prod P) at hWm
  have hp : Measurable (fun x : ℝ≥0∞ => x ^ (ν / γ)) :=
    ENNReal.continuous_rpow_const.measurable
  congr 1
  rw [← lintegral_map' hp.aemeasurable hWm, ← hlaw, lintegral_map' hp.aemeasurable hm]

end DOZZ.Proofs
