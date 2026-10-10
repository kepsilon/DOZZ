/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.RetainedAnnuliFatou

/-! Joint inverse-moment convergence from marginal fourth-order inverse bounds. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Products of real random variables preserve convergence in measure on a finite space. -/
theorem tendstoInMeasure_mul
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (f g : ℕ → Ω → ℝ) (F G : Ω → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) P) (hg : ∀ n, AEStronglyMeasurable (g n) P)
    (hF : TendstoInMeasure P f atTop F) (hG : TendstoInMeasure P g atTop G) :
    TendstoInMeasure P (fun n ω => f n ω * g n ω) atTop (fun ω => F ω * G ω) := by
  have hfg (n : ℕ) : AEStronglyMeasurable (fun ω => f n ω * g n ω) P := (hf n).mul (hg n)
  apply (exists_seq_tendstoInMeasure_atTop_iff hfg).mpr
  intro ns hns
  obtain ⟨s, hs, hsae⟩ := (exists_seq_tendstoInMeasure_atTop_iff hf).mp hF ns hns
  obtain ⟨t, ht, htae⟩ := (exists_seq_tendstoInMeasure_atTop_iff hg).mp hG (ns ∘ s)
    (hns.comp hs)
  refine ⟨s ∘ t, hs.comp ht, ?_⟩
  filter_upwards [hsae, htae] with ω hω hω'
  exact (hω.comp ht.tendsto_atTop).mul hω'

/-- A product is controlled by the two marginal squares, including at infinity. -/
theorem mul_le_square_sum (x y : ℝ≥0∞) : x * y ≤ x ^ 2 + y ^ 2 := by
  rcases le_total x y with h | h
  · exact (mul_le_mul' h le_rfl).trans (by simpa only [pow_two] using (show y * y ≤ x ^ 2 + y * y from le_add_self))
  · exact (mul_le_mul' le_rfl h).trans (by simpa only [pow_two] using (show x * x ≤ x * x + y ^ 2 from le_self_add))

/-- Uniform marginal fourth inverse moments give the uniform integrability of the product.
The underlying masses need not be independent. -/
theorem joint_inverse_moment_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f₀ f₁ : ℕ → Ω → ℝ≥0∞) (g₀ g₁ : Ω → ℝ≥0∞) (a b : ℝ)
    (hf₀ : ∀ n, AEMeasurable (f₀ n) P) (hf₁ : ∀ n, AEMeasurable (f₁ n) P)
    (hg₀ : ∀ᵐ ω ∂P, g₀ ω ≠ ⊤) (hg₁ : ∀ᵐ ω ∂P, g₁ ω ≠ ⊤)
    (hfp₀ : ∀ n, ∀ᵐ ω ∂P, f₀ n ω ^ (-a) ≠ ⊤)
    (hfp₁ : ∀ n, ∀ᵐ ω ∂P, f₁ n ω ^ (-b) ≠ ⊤)
    (hgp₀ : ∀ᵐ ω ∂P, g₀ ω ^ (-a) ≠ ⊤) (hgp₁ : ∀ᵐ ω ∂P, g₁ ω ^ (-b) ≠ ⊤)
    (hconv₀ : TendstoInMeasure P (fun n ω => (f₀ n ω).toReal) atTop (fun ω => (g₀ ω).toReal))
    (hconv₁ : TendstoInMeasure P (fun n ω => (f₁ n ω).toReal) atTop (fun ω => (g₁ ω).toReal))
    (C₀ C₁ : ℝ≥0∞) (hC₀ : C₀ ≠ ⊤) (hC₁ : C₁ ≠ ⊤)
    (hbound₀ : ∀ n, (∫⁻ ω, f₀ n ω ^ (-4 * a) ∂P) ≤ C₀)
    (hbound₁ : ∀ n, (∫⁻ ω, f₁ n ω ^ (-4 * b) ∂P) ≤ C₁) :
    Tendsto (fun n => ∫⁻ ω, f₀ n ω ^ (-a) * f₁ n ω ^ (-b) ∂P) atTop
      (𝓝 (∫⁻ ω, g₀ ω ^ (-a) * g₁ ω ^ (-b) ∂P)) := by
  let H : ℕ → Ω → ℝ≥0∞ := fun n ω => f₀ n ω ^ (-a) * f₁ n ω ^ (-b)
  let G : Ω → ℝ≥0∞ := fun ω => g₀ ω ^ (-a) * g₁ ω ^ (-b)
  have hHm (n : ℕ) : AEMeasurable (H n) P := ((hf₀ n).pow_const _).mul ((hf₁ n).pow_const _)
  have hHfin (n : ℕ) : ∀ᵐ ω ∂P, H n ω ≠ ⊤ := by
    filter_upwards [hfp₀ n, hfp₁ n] with ω hω hω'
    exact ENNReal.mul_ne_top hω hω'
  have hGfin : ∀ᵐ ω ∂P, G ω ≠ ⊤ := by
    filter_upwards [hgp₀, hgp₁] with ω hω hω'
    exact ENNReal.mul_ne_top hω hω'
  have hconv : TendstoInMeasure P (fun n ω => (H n ω).toReal) atTop (fun ω => (G ω).toReal) := by
    simpa only [H, G, ENNReal.toReal_mul] using tendstoInMeasure_mul P
      (fun n ω => (f₀ n ω ^ (-a)).toReal) (fun n ω => (f₁ n ω ^ (-b)).toReal)
      (fun ω => (g₀ ω ^ (-a)).toReal) (fun ω => (g₁ ω ^ (-b)).toReal)
      (fun n => (ENNReal.measurable_toReal.comp_aemeasurable ((hf₀ n).pow_const _)).aestronglyMeasurable)
      (fun n => (ENNReal.measurable_toReal.comp_aemeasurable ((hf₁ n).pow_const _)).aestronglyMeasurable)
      (momentConv_tendstoInMeasure_rpow P f₀ g₀ hf₀ hg₀ hconv₀ (-a) hgp₀)
      (momentConv_tendstoInMeasure_rpow P f₁ g₁ hf₁ hg₁ hconv₁ (-b) hgp₁)
  have hbound (n : ℕ) : (∫⁻ ω, H n ω ^ (2 : ℝ) ∂P) ≤ C₀ + C₁ := by
    calc
      _ ≤ ∫⁻ ω, f₀ n ω ^ (-4 * a) + f₁ n ω ^ (-4 * b) ∂P := by
        apply lintegral_mono
        intro ω
        dsimp only [H]
        rw [ENNReal.rpow_two, mul_pow]
        have hh := mul_le_square_sum ((f₀ n ω ^ (-a)) ^ 2) ((f₁ n ω ^ (-b)) ^ 2)
        simpa only [← ENNReal.rpow_two, ← ENNReal.rpow_mul, mul_assoc,
          show (-a) * (2 : ℝ) * 2 = -4 * a by ring,
          show (-b) * (2 : ℝ) * 2 = -4 * b by ring] using hh
      _ = (∫⁻ ω, f₀ n ω ^ (-4 * a) ∂P) + ∫⁻ ω, f₁ n ω ^ (-4 * b) ∂P :=
        lintegral_add_left' ((hf₀ n).pow_const _) _
      _ ≤ _ := add_le_add (hbound₀ n) (hbound₁ n)
  have hh := momentConv_tendsto_of_rpow_ne_top P H G hHm hGfin hconv
    (p := 1) (p' := 2) (by norm_num) (by norm_num) (ENNReal.add_ne_top.mpr ⟨hC₀, hC₁⟩)
    hbound (fun n => by simpa only [ENNReal.rpow_one] using hHfin n)
    (by simpa only [ENNReal.rpow_one] using hGfin)
  simpa only [ENNReal.rpow_one] using hh

/-- Every fixed pair of small disks has convergence of all joint nonpositive moments along
the integer cutoffs. Marginal fourth inverse moments supply the product integrability. -/
theorem gmc_joint_ball_inverse_moment_tendsto
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (u v : ℂ) (ρ σ a b : ℝ) (hρ : 0 < ρ) (hσ : 0 < σ)
    (hρ8 : ρ ≤ 1 / 8) (hσ8 : σ ≤ 1 / 8) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Tendsto (fun n : ℕ => ∫⁻ ω,
      (regularizedGMC P Xc γ n ω (Metric.ball u ρ)) ^ (-a) *
      (regularizedGMC P Xc γ n ω (Metric.ball v σ)) ^ (-b) ∂P) atTop
      (𝓝 (∫⁻ ω, (M ω (Metric.ball u ρ)) ^ (-a) * (M ω (Metric.ball v σ)) ^ (-b) ∂P)) := by
  have : IsProbabilityMeasure P := hX.1
  have hbulk : 0 < 4 / γ ^ 2 := div_pos (by norm_num) (sq_pos_of_pos hγ)
  have hbound (z : ℂ) (r s : ℝ) (hr : 0 < r) (hr8 : r ≤ 1 / 8) (hs : 0 ≤ s) :=
    regularizedGMC_ball_moment_uniform_any_center P X hX Xc hXc γ hγ hγ2 z r hr hr8
      (-4 * s) ((mul_nonpos_of_nonpos_of_nonneg (by norm_num) hs).trans_lt hbulk)
  obtain ⟨C₀, hC₀, hb₀⟩ := hbound u ρ a hρ hρ8 ha
  obtain ⟨C₁, hC₁, hb₁⟩ := hbound v σ b hσ hσ8 hb
  have hm (z : ℂ) (r : ℝ) (n : ℕ) :
      AEMeasurable (fun ω => regularizedGMC P Xc γ n ω (Metric.ball z r)) P :=
    ((Measure.measurable_coe Metric.isOpen_ball.measurableSet).comp
      (regularizedGMC_measurable P X hX Xc hXc γ n)).aemeasurable
  have hfp (z : ℂ) (r s : ℝ) (hs : 0 ≤ s) (C : ℝ≥0∞) (hC : C ≠ ⊤)
      (hh : ∀ r' : ℝ, 0 ≤ r' →
        gmcMassMoment P (regularizedGMC P Xc γ r') (Metric.ball z r) (-4 * s) ≤ C)
      (n : ℕ) : ∀ᵐ ω ∂P, regularizedGMC P Xc γ n ω (Metric.ball z r) ^ (-s) ≠ ⊤ := by
    by_cases hs0 : s = 0
    · filter_upwards [] with ω
      rw [hs0, neg_zero, ENNReal.rpow_zero]
      exact ENNReal.one_ne_top
    · have hs' : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
      exact momentConv_ae_rpow_ne_top_of_neg P _ (hm z r n) (neg_lt_zero.mpr hs')
        (mul_neg_of_neg_of_pos (by norm_num) hs') hC (hh n (Nat.cast_nonneg n))
  have hfin (D : Set ℂ) : ∀ᵐ ω ∂P, M ω D ≠ ⊤ := ae_of_all P fun ω => by
    let _ := hM.1 ω
    exact measure_ne_top _ _
  have hgp (z : ℂ) (r s : ℝ) (hr : 0 < r) : ∀ᵐ ω ∂P, M ω (Metric.ball z r) ^ (-s) ≠ ⊤ := by
    filter_upwards [gmc_ball_mass_pos_ae P X hX γ hγ hγ2 M hM z r hr,
      hfin (Metric.ball z r)] with ω hω hω'
    exact ENNReal.rpow_ne_top_of_ne_zero hω.ne' hω'
  exact joint_inverse_moment_tendsto P
    (fun n ω => regularizedGMC P Xc γ n ω (Metric.ball u ρ))
    (fun n ω => regularizedGMC P Xc γ n ω (Metric.ball v σ))
    (fun ω => M ω (Metric.ball u ρ)) (fun ω => M ω (Metric.ball v σ)) a b
    (hm u ρ) (hm v σ) (hfin _) (hfin _)
    (hfp u ρ a ha C₀ hC₀.ne hb₀) (hfp v σ b hb C₁ hC₁.ne hb₁)
    (hgp u ρ a hρ) (hgp v σ b hσ)
    (regularizedGMC_mass_toReal_tendstoInMeasure P X hX γ hγ hγ2 M hM Xc hXc _
      Metric.isOpen_ball.measurableSet _ (ball_subset_closedBall_norm_add u ρ))
    (regularizedGMC_mass_toReal_tendstoInMeasure P X hX γ hγ hγ2 M hM Xc hXc _
      Metric.isOpen_ball.measurableSet _ (ball_subset_closedBall_norm_add v σ))
    C₀ C₁ hC₀.ne hC₁.ne (fun n => hb₀ n (Nat.cast_nonneg n)) (fun n => hb₁ n (Nat.cast_nonneg n))

end DOZZ.Proofs
