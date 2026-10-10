/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.DualR.SegFactors
public import DOZZ.ShiftEquations.DualR.DualL
public import DOZZ.Statements.Defs.IsEquatorGFF
public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.Statements.Brownian.ReflectionR
public import DOZZ.Statements.Brownian.IsSourceLateralProjection
public import DOZZ.Statements.Brownian.IsReflectionData
import DOZZ.Brownian.Reflection.WitnessIndependence
import DOZZ.Brownian.Reflection.RtheorAnalytic
import DOZZ.Correlations.Analytic.StructureConstantHolomorphic
import DOZZ.ShiftEquations.Rbar.Continuation

/-!
# The second dual crossing seed on its whole two-triple extended domain

The second dual crossing seed (`DOZZ.dual_crossing_seed_two`, [KRV, Proposition 9.10])
`R(ε) C(2Q - ε - 2/γ, α, α') = L(ε, α, α') R(α) C(ε, 2Q - α - 2/γ, α')` holds for `ε, α, α' < Q`
with `α + ε + α' > 2Q + 2/γ`. The real points where both triples lie in the extended Seiberg domain
form a convex set containing that seed region, and every factor is meromorphic along its segments
(the reflection coefficient through a strip-meromorphic representative `R`, the structure constants
through `DOZZ.unitVolumeStructureConstant_holomorphic_near_extended_domain`, `L` through `l`).
Continuing along a segment from the seed region gives the identity at every point of that set where
all factors are analytic: the source's first continuation step in the proof of the `2/γ` shift
equation ([KRV, §10.5]).
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- **The second dual crossing seed on the two-triple extended domain.** `hSeed` is the conclusion
of `DOZZ.dual_crossing_seed_two` at the given field, chaos and coupling; `R` is any
strip-meromorphic function with the physical reflection values. -/
theorem seed_full {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hSeed : ∀ α ε α' : ℝ, α < Q γ → ε < Q γ → α' < Q γ → 2 * Q γ + 2 / γ < α + ε + α' →
      ∃ Bε Bα : Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧ IsReflectionData P γ ε Bε Z ∧
          IsReflectionData P γ α Bα Z ∧
          reflectionR P γ μ ε Bε Z * structureConstant P M γ μ (2 * Q γ - ε - 2 / γ) α α' =
            dualCrossingL γ ε α α' * reflectionR P γ μ α Bα Z *
              structureConstant P M γ μ ε (2 * Q γ - α - 2 / γ) α')
    {hR : ℝ} (hhR : 0 < hR) {R : ℂ → ℂ} (hRm : MeromorphicOn R (horizontalStrip hR))
    {BR : ℝ → Ω → BrownianPath × BrownianPath} {ZR : Ω → Measure ℝ}
    (hBR : ∀ α : ℝ, γ / 2 < α → α < Q γ → IsReflectionData P γ α (BR α) ZR)
    (hRv : ∀ α : ℝ, γ / 2 < α → α < Q γ → R (α : ℂ) = (reflectionR P γ μ α (BR α) ZR : ℂ))
    {ε α α' : ℝ} (h₁ : ExtendedSeiberg3 γ (2 * Q γ - ε - 2 / γ) α α')
    (h₂ : ExtendedSeiberg3 γ ε (2 * Q γ - α - 2 / γ) α')
    (hRε : AnalyticAt ℂ R (ε : ℂ)) (hRα : AnalyticAt ℂ R (α : ℂ))
    (hs₁ : AnalyticAt ℂ Complex.Gamma (sExp γ (2 * Q γ - ε - 2 / γ) α α' : ℂ))
    (hs₂ : AnalyticAt ℂ Complex.Gamma (sExp γ ε (2 * Q γ - α - 2 / γ) α' : ℂ))
    (g₁ : AnalyticAt ℂ Complex.Gamma (dualArg₁ γ ε))
    (g₂ : AnalyticAt ℂ Complex.Gamma (dualArg₂ γ α))
    (g₃ : AnalyticAt ℂ Complex.Gamma (1 - dualArg₃ γ ε α α'))
    (g₄ : AnalyticAt ℂ Complex.Gamma (1 - dualArg₄ γ ε α α')) :
    R ε * (structureConstant P M γ μ (2 * Q γ - ε - 2 / γ) α α' : ℂ) =
      dualLC γ ε α α' * R α * (structureConstant P M γ μ ε (2 * Q γ - α - 2 / γ) α' : ℂ) := by
  obtain ⟨V₃, hV₃, hV₃mem, f₃, hf₃, hf₃eq⟩ :=
    unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hγh : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ (by norm_num) hγ]
    nlinarith
  have h2γ : 0 < 2 / γ := by positivity
  have h42 : 4 / γ = 2 * (2 / γ) := by ring
  -- the seed point
  set e₀ : ℝ := Q γ - γ / 12 with he₀
  have hq₀₁ : ExtendedSeiberg3 γ (2 * Q γ - e₀ - 2 / γ) e₀ e₀ :=
    extendedSeiberg3_of_lt hγ (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith)
  have hq₀₂ : ExtendedSeiberg3 γ e₀ (2 * Q γ - e₀ - 2 / γ) e₀ :=
    extendedSeiberg3_of_lt hγ (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith)
  set U : Set ℂ := (segC e₀ ε ⁻¹' horizontalStrip hR ∩ segC e₀ α ⁻¹' horizontalStrip hR) ∩
    (segT (2 * Q γ - e₀ - 2 / γ) (2 * Q γ - ε - 2 / γ) e₀ α e₀ α' ⁻¹' V₃ ∩
      segT e₀ ε (2 * Q γ - e₀ - 2 / γ) (2 * Q γ - α - 2 / γ) e₀ α' ⁻¹' V₃) with hU
  set F : ℂ → ℂ := fun t => R (segC e₀ ε t) *
    structureConstantH f₃ γ μ (segT (2 * Q γ - e₀ - 2 / γ) (2 * Q γ - ε - 2 / γ) e₀ α e₀ α' t)
    with hF
  set G : ℂ → ℂ := fun t => dualLC γ (segC e₀ ε t) (segC e₀ α t) (segC e₀ α' t) *
    R (segC e₀ α t) *
      structureConstantH f₃ γ μ (segT e₀ ε (2 * Q γ - e₀ - 2 / γ) (2 * Q γ - α - 2 / γ) e₀ α' t)
    with hG
  have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (t : ℂ) ∈ U := fun t h0 h1 =>
    ⟨⟨segC_mem_horizontalStrip hhR e₀ ε t, segC_mem_horizontalStrip hhR e₀ α t⟩,
      segT_mem hγ hV₃mem hq₀₁ h₁ h0 h1, segT_mem hγ hV₃mem hq₀₂ h₂ h0 h1⟩
  have hFm : MeromorphicOn F U := fun t ht =>
    (segR_meromorphicOn hRm e₀ ε t ht.1.1).fun_mul
      (segH_meromorphicOn hV₃ hf₃ hμ _ _ e₀ α e₀ α' t ht.2.1)
  have hGm : MeromorphicOn G U := fun t ht =>
    ((meromorphicAt_dualLC_comp (analyticAt_segC e₀ ε t) (analyticAt_segC e₀ α t)
      (analyticAt_segC e₀ α' t)).fun_mul (segR_meromorphicOn hRm e₀ α t ht.1.2)).fun_mul
      (segH_meromorphicOn hV₃ hf₃ hμ e₀ ε _ _ e₀ α' t ht.2.2)
  have hstart : ∀ᶠ t : ℝ in 𝓝[>] 0, F t = G t := by
    have hsum := eventually_segC_mem (a := e₀ + e₀ + e₀) (b := ε + α + α')
      (N := Ioi (2 * Q γ + 2 / γ)) isOpen_Ioi (show 2 * Q γ + 2 / γ < e₀ + e₀ + e₀ by linarith)
    filter_upwards [eventually_segC_mem (b := ε) (N := Iio (Q γ)) isOpen_Iio
        (show e₀ < Q γ by linarith),
      eventually_segC_mem (b := α) (N := Iio (Q γ)) isOpen_Iio (show e₀ < Q γ by linarith),
      eventually_segC_mem (b := α') (N := Iio (Q γ)) isOpen_Iio (show e₀ < Q γ by linarith),
      hsum, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t hεt hαt hα't hst ht
    simp only [mem_Iio, mem_Ioi] at hεt hαt hα't hst
    set εt : ℝ := e₀ + t * (ε - e₀) with hεt'
    set αt : ℝ := e₀ + t * (α - e₀) with hαt'
    set α't : ℝ := e₀ + t * (α' - e₀) with hα't'
    have hsum' : 2 * Q γ + 2 / γ < αt + εt + α't := by
      have e : e₀ + e₀ + e₀ + t * (ε + α + α' - (e₀ + e₀ + e₀)) = αt + εt + α't := by
        rw [hεt', hαt', hα't']
        ring
      linarith
    have hE₁ := extendedSeiberg3_segment hγ hq₀₁ h₁ ht.1.le ht.2.le
    have hE₂ := extendedSeiberg3_segment hγ hq₀₂ h₂ ht.1.le ht.2.le
    obtain ⟨Bε, Bα, Z, -, hBε, hBα, hseed⟩ := hSeed αt εt α't hαt hεt hα't hsum'
    have hεγ : γ / 2 < εt := by linarith
    have hαγ : γ / 2 < αt := by linarith
    simp only [hF, hG]
    rw [segH_ofReal P M hμ hf₃eq hE₁, segH_ofReal P M hμ hf₃eq hE₂, segC_ofReal, segC_ofReal,
      segC_ofReal, dualLC_ofReal hγ.ne', hRv _ hεγ hεt, hRv _ hαγ hαt,
      reflectionR_eq_of_isReflectionData P P γ μ _ (BR _) ZR Bε Z (hBR _ hεγ hεt) hBε,
      reflectionR_eq_of_isReflectionData P P γ μ _ (BR _) ZR Bα Z (hBR _ hαγ hαt) hBα,
      show 2 * Q γ - e₀ - 2 / γ + t * (2 * Q γ - ε - 2 / γ - (2 * Q γ - e₀ - 2 / γ)) =
        2 * Q γ - εt - 2 / γ by rw [hεt']; ring,
      show 2 * Q γ - e₀ - 2 / γ + t * (2 * Q γ - α - 2 / γ - (2 * Q γ - e₀ - 2 / γ)) =
        2 * Q γ - αt - 2 / γ by rw [hαt']; ring]
    exact_mod_cast hseed
  have hF1 : AnalyticAt ℂ F 1 :=
    (segR_analyticAt_one hRε).mul
      (segH_analyticAt_one hV₃ hf₃ hμ (hV₃mem ![2 * Q γ - ε - 2 / γ, α, α'] h₁) hs₁)
  have hG1 : AnalyticAt ℂ G 1 := by
    refine ((analyticAt_dualLC_comp (analyticAt_segC e₀ ε 1) (analyticAt_segC e₀ α 1)
      (analyticAt_segC e₀ α' 1) ?_ ?_ ?_ ?_).mul (segR_analyticAt_one hRα)).mul
      (segH_analyticAt_one hV₃ hf₃ hμ (hV₃mem ![ε, 2 * Q γ - α - 2 / γ, α'] h₂) hs₂)
    · rw [segC_one]; exact g₁
    · rw [segC_one]; exact g₂
    · rw [segC_one, segC_one, segC_one]; exact g₃
    · rw [segC_one, segC_one, segC_one]; exact g₄
  have key := eq_at_one_of_segment hseg hFm hGm hstart hF1 hG1
  simp only [hF, hG] at key
  rw [segH_one P M hμ hf₃eq h₁, segH_one P M hμ hf₃eq h₂, segC_one, segC_one, segC_one] at key
  exact key

end DOZZ.Proofs

end
