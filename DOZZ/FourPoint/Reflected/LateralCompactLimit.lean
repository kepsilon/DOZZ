/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.CopiedTestLimit
public import DOZZ.FourPoint.Reflected.LateralCompactComparison
import Mathlib.Tactic
/-! Actual limiting lateral-chaos comparison on separated compact tests. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The actual limiting lateral chaos obeys the two-sided independent-region comparison.
Both cutoff convergence hypotheses are proved from its admissible-version carrier. -/
theorem reflected_lateral_compact_chaos_comparison
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ) (γ : ℝ) (N : Ω → Measure ℂ)
    (hN : IsAdmissibleGMCVersion P (originLateralChart ρ) originLateralPlaneDensity
      (originLateralCircleRegularization Xc ρ) γ N)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ originLateralChart ρ)
    (A : Set ℂ) (hA : MeasurableSet A)
    (R r η : ℝ) (hR0 : 0 ≤ R) (hR : R ≤ 1 / 2) (hr : 0 < r) (hη : 0 < η)
    (hinner : ∀ x ∈ K, x ∈ A → ‖x‖ ≤ R*r)
    (houter : ∀ x ∈ K, x ∉ A → r ≤ ‖x‖)
    (f₀ f₁ : BoundedContinuousFunction ℂ ℝ) (hf₀ : ∀ x, 0 ≤ f₀ x) (hf₁ : ∀ x, 0 ≤ f₁ x)
    (hf₀K : tsupport (f₀ : ℂ → ℝ) ⊆ K) (hf₁K : tsupport (f₁ : ℂ → ℝ) ⊆ K)
    (hf₀A : tsupport (f₀ : ℂ → ℝ) ⊆ A) (hf₁A : tsupport (f₁ : ℂ → ℝ) ⊆ Aᶜ)
    (q : ℝ) (hq : 0 < q) :
    let m := ENNReal.ofReal (Real.exp (γ^2*(2*R+η)/2*(q^2+q)))
    (∫⁻ ω, ENNReal.ofReal (∫ x, (f₀+f₁) x ∂N ω) ^ (-q) ∂P) ≤
      m * (∫⁻ ω : Ω × Ω, ENNReal.ofReal
        ((∫ x, f₀ x ∂N ω.1) + ∫ x, f₁ x ∂N ω.2) ^ (-q) ∂P.prod P) ∧
    (∫⁻ ω : Ω × Ω, ENNReal.ofReal
        ((∫ x, f₀ x ∂N ω.1) + ∫ x, f₁ x ∂N ω.2) ^ (-q) ∂P.prod P) ≤
      m * (∫⁻ ω, ENNReal.ofReal (∫ x, (f₀+f₁) x ∂N ω) ^ (-q) ∂P) := by
  let _ : IsProbabilityMeasure P := hX.1
  let Y := originLateralCircleRegularization Xc ρ
  have hY := originLateralCircleRegularization_admissible P X Xc hX hc hm ρ hρ
  have hs : 0 < (1-R)*r := mul_pos (by linarith) hr
  obtain ⟨d, hd, hb⟩ := reflected_lateral_cutoff_cross_bound P X Xc hX hc hm
    ρ hρ K hK hKU R ((1-R)*r) η hR hs hη
  let δ := min d (min ρ 1)
  have hδ : 0 < δ := lt_min hd (lt_min hρ (by norm_num))
  let R₀ := -Real.log δ
  have hR₀ : Real.exp (-R₀) = δ := by dsimp only [R₀]; rw [neg_neg, Real.exp_log hδ]
  have hR₀ρ : Real.exp (-R₀) ≤ min ρ 1 := hR₀ ▸ min_le_right _ _
  have hcut (a : ℝ) : Real.exp (-max a R₀) ≤ min d ρ := by
    apply (Real.exp_le_exp.mpr (neg_le_neg (le_max_right _ _))).trans
    rw [hR₀]
    exact le_min (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _))
  let Φ := fun a ω x => Y ω (Real.exp (-max a R₀)) x
  have hΦ (a : ℝ) : IsCenteredGaussianField P (Φ a) := by
    constructor
    · exact originLateralCircleRegularization_measurableAtScale Xc hm ρ hρ _
    · intro n xs
      exact originLateralCircleRegularization_gaussian P X Xc hX hc hm ρ hρ n
        (fun i => (Real.exp (-max a R₀), xs i))
  let f := f₀+f₁
  have hf : ∀ x, 0 ≤ f x := fun x => add_nonneg (hf₀ x) (hf₁ x)
  have hfK : tsupport (f : ℂ → ℝ) ⊆ K :=
    (tsupport_add f₀ f₁).trans (union_subset hf₀K hf₁K)
  obtain ⟨hν, hXc⟩ := reflected_admissible_field_test_limit P _ _ _ Y hY γ N hN
    K hK hKU f hf hfK R₀ hR₀ρ
  let ν := (logRegularizationReference (originLateralChart ρ) originLateralPlaneDensity).restrict K
  let _ := hν
  have hYc := reflected_admissible_copied_test_limit P _ _ _ Y hY γ N hN K hK hKU
    A hA f₀ f₁ hf₀ hf₁ hf₀K hf₁K hf₀A hf₁A R₀ hR₀ρ hΦ
  have ho (a : ℝ) (x y : ℂ) (hxK : x ∈ K) (hyK : y ∈ K)
      (hx : x ∉ A) (hy : y ∈ A) :
      |gaussianCovariance P (fun ω => Φ a ω x) (fun ω => Φ a ω y)| ≤ 2*R+η := by
    have hxo := houter x hxK hx
    have hyi := hinner y hyK hy
    have hrel : ‖y‖ ≤ R*‖x‖ := hyi.trans (mul_le_mul_of_nonneg_left hxo hR0)
    have hdist : (1-R)*r ≤ ‖x-y‖ := by
      have hh := norm_sub_norm_le x y
      linarith only [hxo, hyi, hh]
    exact hb _ _ (Real.exp_pos _) (hcut a) (Real.exp_pos _) (hcut a) x hxK y hyK hdist hrel
  have hbill : 0 ≤ 2*R+η := by linarith
  have hcross (a : ℝ) : ∀ᵐ xy ∂ν.prod ν, ¬(xy.1 ∈ A ↔ xy.2 ∈ A) →
      |gaussianCovariance P (fun ω => Φ a ω xy.1) (fun ω => Φ a ω xy.2)| ≤
        (Real.sqrt (2*R+η))^2 := by
    have hk : ∀ᵐ x ∂ν, x ∈ K := ae_restrict_mem hK.measurableSet
    have hk₁ : ∀ᵐ xy : ℂ × ℂ ∂ν.prod ν, xy.1 ∈ K := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := ν)).ae hk
    have hk₂ : ∀ᵐ xy : ℂ × ℂ ∂ν.prod ν, xy.2 ∈ K := (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := ν)).ae hk
    filter_upwards [hk₁, hk₂] with xy hxK hyK hne
    rw [Real.sq_sqrt hbill]
    by_cases hx : xy.1 ∈ A
    · have hy : xy.2 ∉ A := fun hy => hne ⟨fun _ => hy, fun _ => hx⟩
      have he : gaussianCovariance P (fun ω => Φ a ω xy.1) (fun ω => Φ a ω xy.2) =
          gaussianCovariance P (fun ω => Φ a ω xy.2) (fun ω => Φ a ω xy.1) := by
        unfold gaussianCovariance
        simp only [mul_comm]
      rw [he]
      exact ho a xy.2 xy.1 hyK hxK hy hx
    · have hy : xy.2 ∈ A := by
        by_contra hh
        exact hne ⟨fun h => False.elim (hx h), fun h => False.elim (hh h)⟩
      exact ho a xy.1 xy.2 hxK hyK hx hy
  have hh : Measurable (fun x => (f x).toNNReal) := f.continuous.measurable.real_toNNReal
  have hbound : ∃ b : ℝ≥0, ∀ x, (f x).toNNReal ≤ b :=
    ⟨‖f‖.toNNReal, fun x => Real.toNNReal_mono ((le_abs_self _).trans (f.norm_coe_le_norm x))⟩
  have hc' := reflected_kahane_decoupling_limit P Φ hΦ A hA ν (fun x => (f x).toNNReal)
    hh hbound γ q (Real.sqrt (2*R+η)) hq hcross _ _ hXc hYc
  simpa only [Real.sq_sqrt hbill] using hc'

end DOZZ.Proofs
