/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.DualR.SegFactors
public import DOZZ.Statements.Defs.IsEquatorGFF
public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.Statements.Brownian.ReflectionR
public import DOZZ.Statements.Brownian.IsSourceLateralProjection
public import DOZZ.Statements.Brownian.IsReflectionData
import DOZZ.ShiftEquations.Gluing.BandNear
import DOZZ.Brownian.Reflection.RtheorAnalytic
import DOZZ.Correlations.Analytic.StructureConstantHolomorphic
import DOZZ.ShiftEquations.Rbar.Continuation

/-!
# The first γ/2 structure shift on the whole two-triple extended domain

For spectators near `Q` the first structure shift `C(x) = -𝒜(x - γ/2) C(x - γ)/(πμ)` holds at exact
real points (from `DOZZ.structureConstant_reflected_shift_and_gluing`, `firstShift_exact_of_strip`).
The set of real triples `(x, b, c)` with `(x, b, c)` and `(x - γ, b, c)` both in the extended
Seiberg domain is convex, and both sides are meromorphic along its segments
(`DOZZ.unitVolumeStructureConstant_holomorphic_near_extended_domain`). Continuing from the near-`Q`
box along a segment gives the shift at every real point of that set where `Γ` is analytic at both
`s`-parameters and the shift coefficient is analytic (`ShiftCoeffGood`). This is the continuation in
the spectators of the gluing lemma ([KRV, Lemma 10.5], first half).
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- **Continuation of the first structure shift from a box.** If the first structure shift holds
at every real point of an open box containing a point `(x₀, b₀, c₀)` of the two-triple extended
domain, then it holds at every real point `(x, b, c)` of that domain where `Γ` is analytic at both
`s`-parameters and `ShiftCoeffGood` holds. -/
theorem firstShift_of_box {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ)
    {γ μ : ℝ} (hγ : 0 < γ) (hμ : 0 < μ)
    {V₃ : Set (Fin 3 → ℂ)} (hV₃ : IsOpen V₃)
    (hV₃mem : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) → complexifyNCharges α ∈ V₃)
    {f₃ : (Fin 3 → ℂ) → ℂ} (hf₃ : DifferentiableOn ℂ f₃ V₃)
    (hf₃eq : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) →
      f₃ (complexifyNCharges α) = (unitVolumeStructureConstant P M γ (α 0) (α 1) (α 2) : ℂ))
    {xl xu bl bu cl cu : ℝ}
    (hbox : ∀ y b' c' : ℝ, xl < y → y < xu → bl < b' → b' < bu → cl < c' → c' < cu →
      (structureConstant P M γ μ y b' c' : ℂ) = -(1 / (Real.pi * μ)) *
        shiftCoeffA γ (γ / 2) ((y : ℂ) - γ / 2) b' c' * (structureConstant P M γ μ (y - γ) b' c' : ℂ))
    {x₀ b₀ c₀ : ℝ} (hx₀ : x₀ ∈ Ioo xl xu) (hb₀ : b₀ ∈ Ioo bl bu) (hc₀ : c₀ ∈ Ioo cl cu)
    (hq₀₁ : ExtendedSeiberg3 γ x₀ b₀ c₀) (hq₀₂ : ExtendedSeiberg3 γ (x₀ - γ) b₀ c₀)
    {x b c : ℝ} (h₁ : ExtendedSeiberg3 γ x b c) (h₂ : ExtendedSeiberg3 γ (x - γ) b c)
    (hs₁ : AnalyticAt ℂ Complex.Gamma (sExp γ x b c : ℂ))
    (hs₂ : AnalyticAt ℂ Complex.Gamma (sExp γ (x - γ) b c : ℂ))
    (hA : ShiftCoeffGood γ ((x : ℂ) - γ / 2) b c) :
    (structureConstant P M γ μ x b c : ℂ) = -(1 / (Real.pi * μ)) *
      shiftCoeffA γ (γ / 2) ((x : ℂ) - γ / 2) b c * (structureConstant P M γ μ (x - γ) b c : ℂ) := by
  set U : Set ℂ := segT x₀ x b₀ b c₀ c ⁻¹' V₃ ∩ segT (x₀ - γ) (x - γ) b₀ b c₀ c ⁻¹' V₃ with hU
  set F : ℂ → ℂ := fun t => structureConstantH f₃ γ μ (segT x₀ x b₀ b c₀ c t) with hF
  set G : ℂ → ℂ := fun t => -(1 / (Real.pi * μ)) *
    shiftCoeffA γ ((γ : ℂ) / 2) (segC x₀ x t - γ / 2) (segC b₀ b t) (segC c₀ c t) *
      structureConstantH f₃ γ μ (segT (x₀ - γ) (x - γ) b₀ b c₀ c t) with hG
  have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (t : ℂ) ∈ U := fun t h0 h1 =>
    ⟨segT_mem hγ hV₃mem hq₀₁ h₁ h0 h1, segT_mem hγ hV₃mem hq₀₂ h₂ h0 h1⟩
  have hFm : MeromorphicOn F U :=
    (segH_meromorphicOn hV₃ hf₃ hμ x₀ x b₀ b c₀ c).mono_set inter_subset_left
  have hGm : MeromorphicOn G U := fun t ht =>
    (MeromorphicAt.const _ t |>.fun_mul (meromorphicAt_shiftCoeffA_comp
      (f₁ := fun t => segC x₀ x t - γ / 2) ((analyticAt_segC x₀ x t).sub analyticAt_const) (analyticAt_segC b₀ b t)
      (analyticAt_segC c₀ c t))).fun_mul
      (segH_meromorphicOn hV₃ hf₃ hμ (x₀ - γ) (x - γ) b₀ b c₀ c t ht.2)
  have hstart : ∀ᶠ t : ℝ in 𝓝[>] 0, F t = G t := by
    filter_upwards [eventually_segC_mem (b := x) isOpen_Ioo hx₀,
      eventually_segC_mem (b := b) isOpen_Ioo hb₀, eventually_segC_mem (b := c) isOpen_Ioo hc₀,
      Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t hxt hbt hct ht
    have hE₁ := extendedSeiberg3_segment hγ hq₀₁ h₁ ht.1.le ht.2.le
    have hE₂ := extendedSeiberg3_segment hγ hq₀₂ h₂ ht.1.le ht.2.le
    simp only [hF, hG]
    rw [segH_ofReal P M hμ hf₃eq hE₁, segH_ofReal P M hμ hf₃eq hE₂, segC_ofReal, segC_ofReal,
      segC_ofReal, show x₀ - γ + t * (x - γ - (x₀ - γ)) = x₀ + t * (x - x₀) - γ by ring]
    exact hbox _ _ _ hxt.1 hxt.2 hbt.1 hbt.2 hct.1 hct.2
  have hF1 : AnalyticAt ℂ F 1 := segH_analyticAt_one hV₃ hf₃ hμ (hV₃mem ![x, b, c] h₁) hs₁
  have hG1 : AnalyticAt ℂ G 1 := by
    refine (analyticAt_const.mul (analyticAt_shiftCoeffA_comp
      (f₁ := fun t => segC x₀ x t - γ / 2)
      ((analyticAt_segC x₀ x 1).sub analyticAt_const) (analyticAt_segC b₀ b 1)
      (analyticAt_segC c₀ c 1) ?_)).mul
      (segH_analyticAt_one hV₃ hf₃ hμ (hV₃mem ![x - γ, b, c] h₂) hs₂)
    rw [segC_one, segC_one, segC_one]
    exact hA
  have key := eq_at_one_of_segment hseg hFm hGm hstart hF1 hG1
  simp only [hF, hG] at key
  rw [segH_one P M hμ hf₃eq h₁, segH_one P M hμ hf₃eq h₂, segC_one, segC_one, segC_one] at key
  exact key

/-- **The first structure shift near `Q` from `DOZZ.structureConstant_reflected_shift_and_gluing`**,
at every real point of the near-`Q` box. -/
theorem firstShift_nearQ_of_reflected_shift_and_gluing {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) {η : ℝ} (hη : 0 < η ∧ Q γ - 2 * η > γ)
    (hShiftGluing : ∀ α₂ α₃ : ℝ, (Q γ - η < α₂ ∧ α₂ < Q γ) → (Q γ - η < α₃ ∧ α₃ < Q γ) →
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
    (y b c : ℝ) (hy₁ : 2 * η + γ < y) (hy₂ : y < Q γ) (hb₁ : Q γ - η < b) (hb₂ : b < Q γ)
    (hc₁ : Q γ - η < c) (hc₂ : c < Q γ) :
    (structureConstant P M γ μ y b c : ℂ) = -(1 / (Real.pi * μ)) *
      shiftCoeffA γ (γ / 2) ((y : ℂ) - γ / 2) b c * (structureConstant P M γ μ (y - γ) b c : ℂ) := by
  obtain ⟨V₃, hV₃, hV₃mem, f₃, hf₃, hf₃eq⟩ :=
    unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM
  obtain ⟨B, Z, -, -, h, hh, C, R, hCm, -, hCv, -, hglue, hrefl⟩ :=
    hShiftGluing b c ⟨hb₁, hb₂⟩ ⟨hc₁, hc₂⟩
  have hCs : ∀ᶠ z in codiscrete ℂ, C (z + γ / 2) =
      -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (b : ℂ) (c : ℂ) * C (z - γ / 2) := by
    filter_upwards [eventually_codiscrete_comp_add hglue ((γ : ℂ) / 2), hrefl] with z h1 h2
    rw [h1, show 2 * (Q γ : ℂ) - (z + γ / 2) = 2 * Q γ - z - γ / 2 by ring, h2]
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hγh : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ (by norm_num) hγ]
    nlinarith
  have h2γ : 0 < 2 / γ := by positivity
  have h42 : 4 / γ = 2 * (2 / γ) := by ring
  have hgood : ShiftCoeffGood γ ((y : ℂ) - γ / 2) b c :=
    shiftCoeffGood_of_lt hγ (by linarith [hη.1]) (by linarith [hη.2])
      (by linarith [hη.1, hη.2]) (by linarith [hη.1, hη.2]) (by linarith [hη.1, hη.2])
  have hAy : AnalyticAt ℂ (fun z => shiftCoeffA γ (γ / 2) z (b : ℂ) (c : ℂ)) ((y : ℂ) - γ / 2) :=
    analyticAt_shiftCoeffA_comp (f₁ := id) (f₂ := fun _ => (b : ℂ)) (f₃ := fun _ => (c : ℂ))
      analyticAt_id analyticAt_const analyticAt_const hgood
  exact firstShift_exact_of_strip P M hγ hγ2 hμ hη ⟨hb₁, hb₂⟩ ⟨hc₁, hc₂⟩ hV₃ hV₃mem hf₃ hf₃eq hh
    hCm hCv hCs hy₁ hy₂ hAy

/-- **The first structure shift on the two-triple extended domain**, from
`DOZZ.structureConstant_reflected_shift_and_gluing`: at every real `(x, b, c)` with `(x, b, c)` and
`(x - γ, b, c)` in the extended Seiberg domain, `Γ` analytic at both `s`-parameters and the shift
coefficient analytic. -/
theorem firstShift_full {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
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
    {x b c : ℝ} (h₁ : ExtendedSeiberg3 γ x b c) (h₂ : ExtendedSeiberg3 γ (x - γ) b c)
    (hs₁ : AnalyticAt ℂ Complex.Gamma (sExp γ x b c : ℂ))
    (hs₂ : AnalyticAt ℂ Complex.Gamma (sExp γ (x - γ) b c : ℂ))
    (hA : ShiftCoeffGood γ ((x : ℂ) - γ / 2) b c) :
    (structureConstant P M γ μ x b c : ℂ) = -(1 / (Real.pi * μ)) *
      shiftCoeffA γ (γ / 2) ((x : ℂ) - γ / 2) b c * (structureConstant P M γ μ (x - γ) b c : ℂ) := by
  obtain ⟨V₃, hV₃, hV₃mem, f₃, hf₃, hf₃eq⟩ :=
    unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hγh : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ (by norm_num) hγ]
    nlinarith
  have h2γ : 0 < 2 / γ := by positivity
  have h42 : 4 / γ = 2 * (2 / γ) := by ring
  set η₀ : ℝ := (Q γ - γ) / 4 with hη₀
  have hη : 0 < η₀ ∧ Q γ - 2 * η₀ > γ := ⟨by rw [hη₀]; linarith, by rw [hη₀]; linarith⟩
  have hbox := firstShift_nearQ_of_reflected_shift_and_gluing P X M hγ hγ2 hμ hX hM hη (hShiftGluing η₀ hη)
  set x₀ : ℝ := (2 * η₀ + γ + Q γ) / 2 with hx₀
  set b₀ : ℝ := Q γ - η₀ / 2 with hb₀
  have hx₀1 : 2 * η₀ + γ < x₀ := by rw [hx₀]; linarith
  have hx₀2 : x₀ < Q γ := by rw [hx₀]; linarith
  have hb₀1 : Q γ - η₀ < b₀ := by rw [hb₀]; linarith
  have hb₀2 : b₀ < Q γ := by rw [hb₀]; linarith
  have hq₀₁ : ExtendedSeiberg3 γ x₀ b₀ b₀ :=
    extendedSeiberg3_of_lt hγ hx₀2 hb₀2 hb₀2 (by linarith) (by linarith) (by linarith)
      (by linarith)
  have hq₀₂ : ExtendedSeiberg3 γ (x₀ - γ) b₀ b₀ :=
    extendedSeiberg3_of_lt hγ (by linarith) hb₀2 hb₀2 (by linarith) (by linarith) (by linarith)
      (by linarith)
  exact firstShift_of_box P M hγ hμ hV₃ hV₃mem hf₃ hf₃eq
    (fun y b' c' hy₁ hy₂ hb₁ hb₂ hc₁ hc₂ => hbox y b' c' hy₁ hy₂ hb₁ hb₂ hc₁ hc₂)
    ⟨hx₀1, hx₀2⟩ ⟨hb₀1, hb₀2⟩ ⟨hb₀1, hb₀2⟩ hq₀₁ hq₀₂ h₁ h₂ hs₁ hs₂ hA

end DOZZ.Proofs

end
