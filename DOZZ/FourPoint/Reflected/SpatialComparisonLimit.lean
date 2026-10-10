/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.CopiedGlobalGuard
/-! Passing the two-region comparison through a guarded spatial exhaustion. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- A retained guard controls inverse expectation limits even if the exhausted masses
can be infinite. Only the guard inverse moment must be integrable. -/
theorem reflected_guarded_inverse_expectation_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω → ℝ≥0∞) (L G : Ω → ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (hF : ∀ n, Measurable (F n)) (hlim : ∀ ω, Tendsto (fun n => F n ω) atTop (𝓝 (L ω)))
    (hguard : ∀ n ω, G ω ≤ F n ω) (hfinite : (∫⁻ ω, G ω^(-q) ∂P) ≠ ⊤) :
    Tendsto (fun n => ∫⁻ ω, F n ω^(-q) ∂P) atTop (𝓝 (∫⁻ ω, L ω^(-q) ∂P)) := by
  refine tendsto_lintegral_of_dominated_convergence (fun ω => G ω^(-q))
    (fun n => (hF n).pow_const (-q)) ?_ hfinite ?_
  · intro n
    exact ae_of_all P fun ω => by
      dsimp only
      rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow (hguard n ω) hq)
  · exact ae_of_all P fun ω => ENNReal.continuous_rpow_const.tendsto _ |>.comp (hlim ω)

/-- The same guard passes both comparison directions to full masses on the original and
independent-region models. These are limits of nonnegative expectations, without taking
an unsigned difference of realizations. -/
theorem reflected_two_region_inverse_limit
    {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω]
    (Q : Measure A) (P : Measure Ω) [IsProbabilityMeasure Q] [IsProbabilityMeasure P]
    (I₀ I₁ : ℕ → A × Ω → ℝ≥0∞) (L₀ L₁ G : A × Ω → ℝ≥0∞)
    (hI₀ : ∀ n, Measurable (I₀ n)) (hI₁ : ∀ n, Measurable (I₁ n)) (hG : Measurable G)
    (hl₀ : ∀ p, Tendsto (fun n => I₀ n p) atTop (𝓝 (L₀ p)))
    (hl₁ : ∀ p, Tendsto (fun n => I₁ n p) atTop (𝓝 (L₁ p)))
    (hguard : ∀ n p, G p ≤ I₁ n p) (q : ℝ) (hq : 0 ≤ q)
    (hfinite : (∫⁻ a, ∫⁻ ω, G (a, ω)^(-q) ∂P ∂Q) ≠ ⊤)
    (m : ℝ≥0∞) (hm : m ≠ ⊤)
    (hcmp : ∀ n,
      (∫⁻ p, (I₀ n p+I₁ n p)^(-q) ∂Q.prod P) ≤
        m*(∫⁻ p : A × (Ω × Ω), (I₀ n (p.1, p.2.1)+I₁ n (p.1, p.2.2))^(-q)
          ∂Q.prod (P.prod P)) ∧
      (∫⁻ p : A × (Ω × Ω), (I₀ n (p.1, p.2.1)+I₁ n (p.1, p.2.2))^(-q)
          ∂Q.prod (P.prod P)) ≤ m*(∫⁻ p, (I₀ n p+I₁ n p)^(-q) ∂Q.prod P)) :
    (∫⁻ p, (L₀ p+L₁ p)^(-q) ∂Q.prod P) ≤
      m*(∫⁻ p : A × (Ω × Ω), (L₀ (p.1, p.2.1)+L₁ (p.1, p.2.2))^(-q)
        ∂Q.prod (P.prod P)) ∧
    (∫⁻ p : A × (Ω × Ω), (L₀ (p.1, p.2.1)+L₁ (p.1, p.2.2))^(-q)
        ∂Q.prod (P.prod P)) ≤ m*(∫⁻ p, (L₀ p+L₁ p)^(-q) ∂Q.prod P) := by
  have hfin₀ : (∫⁻ p, G p^(-q) ∂Q.prod P) ≠ ⊤ := by
    rwa [lintegral_prod _ (hG.pow_const (-q)).aemeasurable]
  have hproj₀ : Measurable (fun p : A × (Ω × Ω) => (p.1, p.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hproj₁ : Measurable (fun p : A × (Ω × Ω) => (p.1, p.2.2)) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have hfin₁ : (∫⁻ p : A × (Ω × Ω), G (p.1, p.2.2)^(-q) ∂Q.prod (P.prod P)) ≠ ⊤ := by
    rw [lintegral_prod (fun p : A × (Ω × Ω) => G (p.1, p.2.2)^(-q))
      ((hG.comp hproj₁).pow_const (-q)).aemeasurable]
    have he (a : A) : (∫⁻ p : Ω × Ω, G (a, p.2)^(-q) ∂P.prod P) =
        ∫⁻ ω, G (a, ω)^(-q) ∂P := by
      rw [lintegral_prod (fun p : Ω × Ω => G (a, p.2)^(-q))
        ((hG.comp (measurable_const.prodMk measurable_snd)).pow_const (-q)).aemeasurable]
      simp only [lintegral_const, measure_univ, mul_one]
    simp_rw [he]
    exact hfinite
  have ht₀ := reflected_guarded_inverse_expectation_limit (Q.prod P)
    (fun n p => I₀ n p+I₁ n p) (fun p => L₀ p+L₁ p) G q hq
    (fun n => (hI₀ n).add (hI₁ n))
    (fun p => (hl₀ p).add (hl₁ p))
    (fun n p => (hguard n p).trans (le_add_left le_rfl)) hfin₀
  have ht₁ := reflected_guarded_inverse_expectation_limit (Q.prod (P.prod P))
    (fun n p => I₀ n (p.1, p.2.1)+I₁ n (p.1, p.2.2))
    (fun p => L₀ (p.1, p.2.1)+L₁ (p.1, p.2.2))
    (fun p => G (p.1, p.2.2)) q hq
    (fun n => ((hI₀ n).comp hproj₀).add ((hI₁ n).comp hproj₁))
    (fun p => (hl₀ (p.1, p.2.1)).add (hl₁ (p.1, p.2.2)))
    (fun n p => (hguard n (p.1, p.2.2)).trans (le_add_left le_rfl)) hfin₁
  exact ⟨le_of_tendsto_of_tendsto ht₀ ((ENNReal.continuous_const_mul hm).tendsto _ |>.comp ht₁)
      (Eventually.of_forall fun n => (hcmp n).1),
    le_of_tendsto_of_tendsto ht₁ ((ENNReal.continuous_const_mul hm).tendsto _ |>.comp ht₀)
      (Eventually.of_forall fun n => (hcmp n).2)⟩

end DOZZ.Proofs
