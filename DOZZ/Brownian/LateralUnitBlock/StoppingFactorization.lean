/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LateralUnitBlock.Factorization
public import DOZZ.Brownian.LateralUnitBlock.Restart
public import DOZZ.Brownian.LateralTranslation

/-!
# Lateral inverse mass at a raw stopping time

Stationarity and independence of the original whole path identify the random translated
lateral law. In particular the stopped unit inverse mass stays independent of every
measurable function of the entire Brownian path, even though its interval is random.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- Random unit-interval inverse mass has the fixed unit-interval law and remains independent
of the entire original Brownian path. No inverse-moment finiteness is assumed here. -/
theorem lateralUnitBlock_random_lateral_inverse {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : Ω → BrownianPath) (hB : AEMeasurable B P)
    (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (hInd : IndepFun B Z P) (τ : Ω → ℝ≥0) (hτ : IsBrownianStoppingTime B τ)
    (q : ℝ) :
    AEMeasurable (fun ω => (Z ω (Icc (τ ω : ℝ) ((τ ω : ℝ) + 1))) ^ (-q)) P ∧
    IndepFun B (fun ω => (Z ω (Icc (τ ω : ℝ) ((τ ω : ℝ) + 1))) ^ (-q)) P ∧
    (∫⁻ ω, (Z ω (Icc (τ ω : ℝ) ((τ ω : ℝ) + 1))) ^ (-q) ∂P) =
      ∫⁻ ω, (Z ω (Icc 0 1)) ^ (-q) ∂P := by
  classical
  obtain ⟨T, hT, heτ⟩ := (lateralUnitBlock_stoppingTime_measurable_pathSigma B τ hτ).exists_eq_measurable_comp
  let R : BrownianPath → ℝ := fun p => -(T p : ℝ)
  have hR : Measurable R := (NNReal.continuous_coe.measurable.comp hT).neg
  let Y : Ω → Measure ℝ := fun ω => (Z ω).map (fun s => s + R (B ω))
  obtain ⟨hY, hYlaw, hIY⟩ := lateralGMC_random_translation P γ Z hZ B hB hInd R hR
  let g : Measure ℝ → ℝ≥0∞ := fun μ => (μ (Icc 0 1)) ^ (-q)
  have hg : Measurable g := ENNReal.continuous_rpow_const.measurable.comp
    (Measure.measurable_coe measurableSet_Icc)
  have he (ω : Ω) : g (Y ω) = (Z ω (Icc (τ ω : ℝ) ((τ ω : ℝ) + 1))) ^ (-q) := by
    dsimp [g, Y]
    rw [Measure.map_apply (f := fun s : ℝ => s + R (B ω))
      (by fun_prop) measurableSet_Icc]
    have htime : T (B ω) = τ ω := congrFun heτ ω |>.symm
    have hs : (fun s => s + R (B ω)) ⁻¹' Icc 0 1 =
        Icc (τ ω : ℝ) ((τ ω : ℝ) + 1) := by
      ext s
      simp only [mem_preimage, mem_Icc, R, htime]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    rw [hs]
  have hm := hg.comp_aemeasurable hY
  have hi := hIY.comp measurable_id hg
  have hint : (∫⁻ ω, g (Y ω) ∂P) = ∫⁻ ω, g (Z ω) ∂P := by
    have heY := lintegral_map' hg.aemeasurable hY
    have heZ := lintegral_map' hg.aemeasurable hZ.2.2.2.1
    rw [← heY, hYlaw, heZ]
  change AEMeasurable (fun ω => g (Y ω)) P at hm
  change IndepFun B (fun ω => g (Y ω)) P at hi
  simp only [he] at hm hi hint
  exact ⟨hm, hi, hint⟩

/-- Every whole-path measurable weight factors from the random lateral inverse mass. -/
theorem lateralUnitBlock_random_lateral_inverse_factor {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : Ω → BrownianPath) (hBm : Measurable B)
    (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (hInd : IndepFun B Z P) (τ : Ω → ℝ≥0) (hτ : IsBrownianStoppingTime B τ)
    (q : ℝ) (W : Ω → ℝ≥0∞)
    (hW : Measurable[MeasurableSpace.comap B inferInstance] W) :
    (∫⁻ ω, W ω * (Z ω (Icc (τ ω : ℝ) ((τ ω : ℝ) + 1))) ^ (-q) ∂P) =
      (∫⁻ ω, W ω ∂P) * ∫⁻ ω, (Z ω (Icc 0 1)) ^ (-q) ∂P := by
  obtain ⟨hm, hi, he⟩ := lateralUnitBlock_random_lateral_inverse P B hBm.aemeasurable γ Z hZ hInd τ hτ q
  have hWi : IndepFun W (fun ω => (Z ω (Icc (τ ω : ℝ) ((τ ω : ℝ) + 1))) ^ (-q)) P := by
    apply (IndepFun_iff_Indep _ _ P).mpr
    intro S T hS hT
    exact ((IndepFun_iff_Indep _ _ P).mp hi) S T (hW.comap_le _ hS) hT
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (hW.mono hBm.comap_le le_rfl).aemeasurable hm hWi, he]

/-- The bridge factor separates even when the endpoint test depends on an independent past. -/
theorem lateralUnitBlock_bridgeWeight_factor_with_past
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → BrownianPath) (hU : Measurable U)
    (H : Ω → E) (hH : Measurable H) (hi : IndepFun H U P)
    (μ : Measure BrownianPath) (hμ : IsPreBrownianReal (fun t p => p t) μ)
    (hUlaw : P.map U = μ) (θ : ℝ)
    (hK : (∫⁻ p, lateralUnitBlock_bridgeWeight θ p ∂μ) ≠ ⊤)
    (w : E × ℝ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ ω, lateralUnitBlock_bridgeWeight θ (U ω) * w (H ω, U ω 1) ∂P) =
      (∫⁻ p, lateralUnitBlock_bridgeWeight θ p ∂μ) * ∫⁻ ω, w (H ω, U ω 1) ∂P := by
  let _ := (hμ.hasLaw_eval 0).isProbabilityMeasure
  let ν := P.map H
  let K := ∫⁻ p, lateralUnitBlock_bridgeWeight θ p ∂μ
  let f : E × BrownianPath → ℝ≥0∞ := fun z =>
    lateralUnitBlock_bridgeWeight θ z.2 * w (z.1, z.2 1)
  let f₀ : E × BrownianPath → ℝ≥0∞ := fun z => w (z.1, z.2 1)
  have hpair : Measurable (fun ω => (H ω, U ω)) := hH.prodMk hU
  have hp : P.map (fun ω => (H ω, U ω)) = ν.prod μ := by
    rw [hi.map_prod_eq_prod_map_map hH.aemeasurable hU.aemeasurable, hUlaw]
  have hf₀ : Measurable f₀ := hw.comp
    (measurable_fst.prodMk ((ContinuousMap.measurable_eval 1).comp measurable_snd))
  have hf : Measurable f := ((measurable_lateralUnitBlock_bridgeWeight θ).comp measurable_snd).mul hf₀
  have he := lintegral_map' (μ := P) hf.aemeasurable hpair.aemeasurable
  have he₀ := lintegral_map' (μ := P) hf₀.aemeasurable hpair.aemeasurable
  change (∫⁻ z, f z ∂P.map (fun ω => (H ω, U ω))) =
    ∫⁻ ω, f (H ω, U ω) ∂P at he
  change (∫⁻ z, f₀ z ∂P.map (fun ω => (H ω, U ω))) =
    ∫⁻ ω, f₀ (H ω, U ω) ∂P at he₀
  rw [hp] at he he₀
  calc
    _ = ∫⁻ z, f z ∂ν.prod μ := he.symm
    _ = ∫⁻ e, ∫⁻ p, f (e, p) ∂μ ∂ν := lintegral_prod _ hf.aemeasurable
    _ = ∫⁻ e, K * ∫⁻ p, f₀ (e, p) ∂μ ∂ν := by
      apply lintegral_congr
      intro e
      exact lateralUnitBlock_bridgeWeight_factor μ hμ θ (fun n => w (e, n))
        (hw.comp (measurable_const.prodMk measurable_id))
    _ = K * ∫⁻ e, ∫⁻ p, f₀ (e, p) ∂μ ∂ν := lintegral_const_mul' K _ hK
    _ = K * ∫⁻ z, f₀ z ∂ν.prod μ := by rw [lintegral_prod _ hf₀.aemeasurable]
    _ = _ := congrArg (K * ·) he₀

/-- All three factors separate at finite unbounded stopping times, for endpoint tests that
also depend measurably on the stopped past. -/
theorem lateralUnitBlock_stopped_bridge_lateral_factor
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (B : Ω → BrownianPath)
    (hBm : ∀ t, Measurable fun ω => B ω t)
    (hB : IsBrownianReal (fun t ω => B ω t) P)
    (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (hInd : IndepFun B Z P) (τ : Ω → ℝ≥0) (hτ : IsBrownianStoppingTime B τ)
    (θ q : ℝ) (hθ : 0 ≤ θ) (H : Ω → E)
    (hH : Measurable[(lateralUnitBlock_isStoppingTime B hBm τ hτ).measurableSpace] H)
    (w : E × ℝ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ ω, lateralUnitBlock_bridgeWeight θ (brownianShiftPath (τ ω) (B ω)) *
      w (H ω, brownianShiftPath (τ ω) (B ω) 1) *
      (Z ω (Icc (τ ω : ℝ) ((τ ω : ℝ) + 1))) ^ (-q) ∂P) =
      (∫⁻ p, lateralUnitBlock_bridgeWeight θ p ∂P.map B) *
        (∫⁻ ω, w (H ω, brownianShiftPath (τ ω) (B ω) 1) ∂P) *
        ∫⁻ ω, (Z ω (Icc 0 1)) ^ (-q) ∂P := by
  let _ : IsProbabilityMeasure P := hZ.2.2.1
  have hmB : Measurable B := ContinuousMap.measurable_iff_eval.mpr hBm
  have hmτ := lateralUnitBlock_stoppingTime_measurable_pathSigma B τ hτ
  let U : Ω → BrownianPath := fun ω => brownianShiftPath (τ ω) (B ω)
  have hmUσ : Measurable[MeasurableSpace.comap B inferInstance] U :=
    continuous_brownianShiftPath.measurable.comp
      (hmτ.prodMk (Measurable.of_comap_le le_rfl))
  have hmHσ := hH.mono (lateralUnitBlock_stoppedSigma_le_pathSigma B hBm τ hτ) le_rfl
  have hmU := hmUσ.mono hmB.comap_le le_rfl
  have hmH := hmHσ.mono hmB.comap_le le_rfl
  let W : Ω → ℝ≥0∞ := fun ω => lateralUnitBlock_bridgeWeight θ (U ω) * w (H ω, U ω 1)
  have hmW : Measurable[MeasurableSpace.comap B inferInstance] W :=
    ((measurable_lateralUnitBlock_bridgeWeight θ).comp hmUσ).mul
      (hw.comp (hmHσ.prodMk ((ContinuousMap.measurable_eval 1).comp hmUσ)))
  have hiHU : IndepFun H U P := by
    apply (IndepFun_iff_Indep _ _ P).mpr
    intro S T hS hT
    exact lateralUnitBlock_stopped_path_indep P B hBm hB τ hτ S T (hH.comap_le _ hS) hT
  have hμ := lateralUnitBlock_brownianPath_map_isBrownian P B hB
  have hK := (lateralUnitBlock_bridge_exponential_moment_lt_top _ hμ θ hθ).ne
  rw [lateralUnitBlock_random_lateral_inverse_factor P B hmB γ Z hZ hInd τ hτ q W hmW]
  rw [lateralUnitBlock_bridgeWeight_factor_with_past P U hmU H hmH hiHU (P.map B)
    hμ.toIsPreBrownianReal (lateralUnitBlock_stopped_path_map P B hBm hB τ hτ) θ hK w hw]

end DOZZ.Proofs
