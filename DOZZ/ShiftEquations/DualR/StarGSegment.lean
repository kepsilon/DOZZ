/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.DualR.SwitchPoint
import DOZZ.Correlations.Analytic.StructureConstantHolomorphic
import DOZZ.ShiftEquations.Rbar.Continuation
import DOZZ.Brownian.Reflection.RtheorAnalytic

/-!
# Continuation of the shifted second dual seed along a segment

From a good start point where the shifted second dual seed holds nearby (`starG_eventually`),
the shifted identity
`R(ε) (-𝒜(2Q - ε - 2/γ - γ/2) C(2Q - ε - 2/γ - γ, α, α')/(πμ)) = L R(α) C(ε, 2Q - α - 2/γ, α')`
continues along the segment to any end point where both shifted triples are in the extended
Seiberg domain (a convex condition) and all factors are analytic.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- **Segment continuation of the shifted second dual seed.** -/
theorem starG_segment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hSeed : ∀ α ε α' : ℝ, α < Q γ → ε < Q γ → α' < Q γ → 2 * Q γ + 2 / γ < α + ε + α' →
      ∃ Bε Bα : Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧ IsReflectionData P γ ε Bε Z ∧
          IsReflectionData P γ α Bα Z ∧
          reflectionR P γ μ ε Bε Z * structureConstant P M γ μ (2 * Q γ - ε - 2 / γ) α α' =
            dualCrossingL γ ε α α' * reflectionR P γ μ α Bα Z *
              structureConstant P M γ μ ε (2 * Q γ - α - 2 / γ) α')
    (hShiftGluing : ∀ η : ℝ, (0 < η ∧ Q γ - 2 * η > γ) → ∀ α₂ α₃ : ℝ,
      (Q γ - η < α₂ ∧ α₂ < Q γ) → (Q γ - η < α₃ ∧ α₃ < Q γ) →
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α : ℝ, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ C R : ℂ → ℂ,
              MeromorphicOn C {z | |z.im| < h} ∧
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, 2 * η < α → α < Q γ →
                C (α : ℂ) = (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) = (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              (∀ᶠ z in codiscrete ℂ, C z = R z * C (2 * Q γ - z)) ∧
              (∀ᶠ z in codiscrete ℂ,
                R (z + γ / 2) * C (2 * Q γ - z - γ / 2) =
                  -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) *
                    C (z - γ / 2)))
    {hR : ℝ} (hhR : 0 < hR) {R : ℂ → ℂ} (hRm : MeromorphicOn R (horizontalStrip hR))
    {BR : ℝ → Ω → BrownianPath × BrownianPath} {ZR : Ω → Measure ℝ}
    (hBR : ∀ α : ℝ, γ / 2 < α → α < Q γ → IsReflectionData P γ α (BR α) ZR)
    (hRv : ∀ α : ℝ, γ / 2 < α → α < Q γ → R (α : ℂ) = (reflectionR P γ μ α (BR α) ZR : ℂ))
    {es as a's ef af a'f : ℝ}
    (hS1 : ExtendedSeiberg3 γ (2 * Q γ - es - 2 / γ) as a's)
    (hS2 : ExtendedSeiberg3 γ es (2 * Q γ - as - 2 / γ) a's)
    (hS3 : ExtendedSeiberg3 γ (2 * Q γ - es - 2 / γ - γ) as a's)
    (hRes : AnalyticAt ℂ R (es : ℂ)) (hRas : AnalyticAt ℂ R (as : ℂ))
    (hsS1 : AnalyticAt ℂ Complex.Gamma (sExp γ (2 * Q γ - es - 2 / γ) as a's : ℂ))
    (hsS2 : AnalyticAt ℂ Complex.Gamma (sExp γ es (2 * Q γ - as - 2 / γ) a's : ℂ))
    (hsS3 : AnalyticAt ℂ Complex.Gamma (sExp γ (2 * Q γ - es - 2 / γ - γ) as a's : ℂ))
    (hgS1 : AnalyticAt ℂ Complex.Gamma (dualArg₁ γ es))
    (hgS2 : AnalyticAt ℂ Complex.Gamma (dualArg₂ γ as))
    (hgS3 : AnalyticAt ℂ Complex.Gamma (1 - dualArg₃ γ es as a's))
    (hgS4 : AnalyticAt ℂ Complex.Gamma (1 - dualArg₄ γ es as a's))
    (hAS : ShiftCoeffGood γ (((2 * Q γ - es - 2 / γ : ℝ) : ℂ) - γ / 2) as a's)
    (hP1 : ExtendedSeiberg3 γ (2 * Q γ - ef - 2 / γ - γ) af a'f)
    (hP2 : ExtendedSeiberg3 γ ef (2 * Q γ - af - 2 / γ) a'f)
    (hRef : AnalyticAt ℂ R (ef : ℂ)) (hRaf : AnalyticAt ℂ R (af : ℂ))
    (hsP1 : AnalyticAt ℂ Complex.Gamma (sExp γ (2 * Q γ - ef - 2 / γ - γ) af a'f : ℂ))
    (hsP2 : AnalyticAt ℂ Complex.Gamma (sExp γ ef (2 * Q γ - af - 2 / γ) a'f : ℂ))
    (hgP1 : AnalyticAt ℂ Complex.Gamma (dualArg₁ γ ef))
    (hgP2 : AnalyticAt ℂ Complex.Gamma (dualArg₂ γ af))
    (hgP3 : AnalyticAt ℂ Complex.Gamma (1 - dualArg₃ γ ef af a'f))
    (hgP4 : AnalyticAt ℂ Complex.Gamma (1 - dualArg₄ γ ef af a'f))
    (hAP : ShiftCoeffGood γ (((2 * Q γ - ef - 2 / γ : ℝ) : ℂ) - γ / 2) af a'f) :
    R ef * (-(1 / (Real.pi * μ)) *
        shiftCoeffA γ (γ / 2) (((2 * Q γ - ef - 2 / γ : ℝ) : ℂ) - γ / 2) af a'f *
          (structureConstant P M γ μ (2 * Q γ - ef - 2 / γ - γ) af a'f : ℂ)) =
      dualLC γ ef af a'f * R af * (structureConstant P M γ μ ef (2 * Q γ - af - 2 / γ) a'f : ℂ) := by
  obtain ⟨V₃, hV₃, hV₃mem, f₃, hf₃, hf₃eq⟩ :=
    unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM
  -- the shifted seed near the start point
  have hnear := starG_eventually P X M hγ hγ2 hμ hX hM hSeed hShiftGluing hhR hRm hBR hRv
    (f₁ := fun t => es + t * (ef - es)) (f₂ := fun t => as + t * (af - as))
    (f₃ := fun t => a's + t * (a'f - a's)) (by fun_prop) (by fun_prop) (by fun_prop) (t₀ := 0)
    (by simp only [zero_mul, add_zero]; exact hS1) (by simp only [zero_mul, add_zero]; exact hS2)
    (by simp only [zero_mul, add_zero]; exact hS3)
    (by simp only [zero_mul, add_zero]; exact hRes) (by simp only [zero_mul, add_zero]; exact hRas)
    (by simp only [zero_mul, add_zero]; exact hsS1) (by simp only [zero_mul, add_zero]; exact hsS2)
    (by simp only [zero_mul, add_zero]; exact hsS3) (by simp only [zero_mul, add_zero]; exact hgS1)
    (by simp only [zero_mul, add_zero]; exact hgS2) (by simp only [zero_mul, add_zero]; exact hgS3)
    (by simp only [zero_mul, add_zero]; exact hgS4) (by simp only [zero_mul, add_zero]; exact hAS)
  set U : Set ℂ := (segC es ef ⁻¹' horizontalStrip hR ∩ segC as af ⁻¹' horizontalStrip hR) ∩
    (segT (2 * Q γ - es - 2 / γ - γ) (2 * Q γ - ef - 2 / γ - γ) as af a's a'f ⁻¹' V₃ ∩
      segT es ef (2 * Q γ - as - 2 / γ) (2 * Q γ - af - 2 / γ) a's a'f ⁻¹' V₃) with hU
  set F : ℂ → ℂ := fun t => R (segC es ef t) * (-(1 / (Real.pi * μ)) *
    shiftCoeffA γ ((γ : ℂ) / 2) (segC (2 * Q γ - es - 2 / γ) (2 * Q γ - ef - 2 / γ) t - γ / 2)
      (segC as af t) (segC a's a'f t) *
      structureConstantH f₃ γ μ
        (segT (2 * Q γ - es - 2 / γ - γ) (2 * Q γ - ef - 2 / γ - γ) as af a's a'f t)) with hF
  set G : ℂ → ℂ := fun t => dualLC γ (segC es ef t) (segC as af t) (segC a's a'f t) *
    R (segC as af t) *
      structureConstantH f₃ γ μ
        (segT es ef (2 * Q γ - as - 2 / γ) (2 * Q γ - af - 2 / γ) a's a'f t) with hG
  have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (t : ℂ) ∈ U := fun t h0 h1 =>
    ⟨⟨segC_mem_horizontalStrip hhR es ef t, segC_mem_horizontalStrip hhR as af t⟩,
      segT_mem hγ hV₃mem hS3 hP1 h0 h1, segT_mem hγ hV₃mem hS2 hP2 h0 h1⟩
  have hFm : MeromorphicOn F U := fun t ht =>
    (segR_meromorphicOn hRm es ef t ht.1.1).fun_mul
      ((MeromorphicAt.const _ t |>.fun_mul (meromorphicAt_shiftCoeffA_comp
        (f₁ := fun t => segC (2 * Q γ - es - 2 / γ) (2 * Q γ - ef - 2 / γ) t - γ / 2)
        ((analyticAt_segC _ _ t).sub analyticAt_const)
        (analyticAt_segC as af t) (analyticAt_segC a's a'f t))).fun_mul
        (segH_meromorphicOn hV₃ hf₃ hμ _ _ as af a's a'f t ht.2.1))
  have hGm : MeromorphicOn G U := fun t ht =>
    ((meromorphicAt_dualLC_comp (analyticAt_segC es ef t) (analyticAt_segC as af t)
      (analyticAt_segC a's a'f t)).fun_mul (segR_meromorphicOn hRm as af t ht.1.2)).fun_mul
      (segH_meromorphicOn hV₃ hf₃ hμ es ef _ _ a's a'f t ht.2.2)
  have hstart : ∀ᶠ t : ℝ in 𝓝[>] 0, F t = G t := by
    filter_upwards [nhdsWithin_le_nhds hnear, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)]
      with t ht hI
    have hE₁ := extendedSeiberg3_segment hγ hS3 hP1 hI.1.le hI.2.le
    have hE₂ := extendedSeiberg3_segment hγ hS2 hP2 hI.1.le hI.2.le
    simp only [hF, hG]
    rw [segH_ofReal P M hμ hf₃eq hE₁, segH_ofReal P M hμ hf₃eq hE₂, segC_ofReal, segC_ofReal,
      segC_ofReal, segC_ofReal,
      show 2 * Q γ - es - 2 / γ + t * (2 * Q γ - ef - 2 / γ - (2 * Q γ - es - 2 / γ)) =
        2 * Q γ - (es + t * (ef - es)) - 2 / γ by ring,
      show 2 * Q γ - es - 2 / γ - γ + t * (2 * Q γ - ef - 2 / γ - γ - (2 * Q γ - es - 2 / γ - γ)) =
        2 * Q γ - (es + t * (ef - es)) - 2 / γ - γ by ring,
      show 2 * Q γ - as - 2 / γ + t * (2 * Q γ - af - 2 / γ - (2 * Q γ - as - 2 / γ)) =
        2 * Q γ - (as + t * (af - as)) - 2 / γ by ring]
    exact ht
  have hF1 : AnalyticAt ℂ F 1 := by
    refine (segR_analyticAt_one hRef).mul ((analyticAt_const.mul (analyticAt_shiftCoeffA_comp
      (f₁ := fun t => segC (2 * Q γ - es - 2 / γ) (2 * Q γ - ef - 2 / γ) t - γ / 2)
      ((analyticAt_segC _ _ 1).sub analyticAt_const) (analyticAt_segC as af 1)
      (analyticAt_segC a's a'f 1) ?_)).mul
      (segH_analyticAt_one hV₃ hf₃ hμ (hV₃mem ![2 * Q γ - ef - 2 / γ - γ, af, a'f] hP1) hsP1))
    rw [segC_one, segC_one, segC_one]
    exact hAP
  have hG1 : AnalyticAt ℂ G 1 := by
    refine ((analyticAt_dualLC_comp (analyticAt_segC es ef 1) (analyticAt_segC as af 1)
      (analyticAt_segC a's a'f 1) ?_ ?_ ?_ ?_).mul (segR_analyticAt_one hRaf)).mul
      (segH_analyticAt_one hV₃ hf₃ hμ (hV₃mem ![ef, 2 * Q γ - af - 2 / γ, a'f] hP2) hsP2)
    · rw [segC_one]; exact hgP1
    · rw [segC_one]; exact hgP2
    · rw [segC_one, segC_one, segC_one]; exact hgP3
    · rw [segC_one, segC_one, segC_one]; exact hgP4
  have key := eq_at_one_of_segment hseg hFm hGm hstart hF1 hG1
  simp only [hF, hG] at key
  rw [segH_one P M hμ hf₃eq hP1, segH_one P M hμ hf₃eq hP2, segC_one, segC_one, segC_one,
    segC_one] at key
  exact key

end DOZZ.Proofs

end
