/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.CutoffUIBad
public import DOZZ.GMC.SharpMoments.LimitWeightedFatou
public import DOZZ.GMC.SharpMoments.LimitExteriorFatou
public import DOZZ.GMC.SharpMoments.WeightedUniformGrid

/-! # The bad region of limiting Coulomb masses

The limiting Coulomb mass of the bad region also has a small moment, uniformly over compact
parameter sets. Near a root the Coulomb weight is the root singularity times a bounded factor, so
the root disks are weighted local masses, whose moments are bounded by the uniform cutoff weighted
bounds through Fatou's lemma; the far exterior is bounded by the far exterior cutoff moments in
the same way. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Far exterior cutoff moments of the power weight at infinity, uniformly over a compact
parameter set. -/
theorem cutoffUI_far_exterior_moment_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (N : ℕ) (S : Set (ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ))) (hS : IsCompact S) {tst : ℝ}
    (htst : 0 < tst)
    (hinf : ∀ c ∈ S, 0 < weightedCutoffSlack (c.1, max c.2.2.2 0, tst))
    {E : ℝ} (hE : 0 ≤ E) (hEinf : ∀ c ∈ S, |c.1 * c.2.2.2| ≤ E) {R0 : ℝ} (hR0 : 2 ≤ R0) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ c ∈ S, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / R0 →
      ∀ r : ℝ, 0 ≤ r →
        ∫⁻ ω, (∫⁻ x in {x : ℂ | 1 / ρ ≤ ‖x‖}, ENNReal.ofReal (‖x‖ ^ max (c.1 * c.2.2.2) 0)
          ∂regularizedGMC P Xc c.1 r ω) ^ tst ∂P ≤ A * ENNReal.ofReal (ρ ^ κ) := by
  classical
  let _ : IsProbabilityMeasure P := hX.1
  have hadmInf : ∀ c ∈ S, 0 < c.1 ∧ c.1 < 2 ∧ 0 < tst ∧ tst < 4 / c.1 ^ 2 ∧
      tst < 2 / c.1 * (Q c.1 - max c.2.2.2 0) := by
    intro c hc
    have h := (weightedCutoffSlack_pos_iff _).mp (hinf c hc)
    exact ⟨h.1, h.2.1, h.2.2.2.1, (lt_min_iff.mp h.2.2.2.2).1, (lt_min_iff.mp h.2.2.2.2).2⟩
  have hζi : ∀ᶠ κ in 𝓝[>] (0 : ℝ), ∀ c ∈ S,
      κ ≤ 2 * tst + c.1 ^ 2 * tst / 2 - c.1 ^ 2 * tst ^ 2 / 2 - max (c.1 * c.2.2.2) 0 * tst := by
    refine eventually_le_of_isCompact_of_pos hS (by fun_prop) fun c hc => ?_
    obtain ⟨hγ0, -, -, -, htinf⟩ := hadmInf c hc
    have hmax : max (c.1 * c.2.2.2) 0 = c.1 * max c.2.2.2 0 := by
      rw [mul_max_of_nonneg _ _ hγ0.le, mul_zero]
    have hQ : c.1 * Q c.1 = 2 + c.1 ^ 2 / 2 := by
      rw [Q]
      field_simp
    have h1 : c.1 * tst / 2 < Q c.1 - max c.2.2.2 0 := by
      have h := mul_lt_mul_of_pos_left htinf (by positivity : (0 : ℝ) < c.1 / 2)
      have hl : c.1 / 2 * (2 / c.1 * (Q c.1 - max c.2.2.2 0)) = Q c.1 - max c.2.2.2 0 := by
        field_simp
      linarith
    have hexp : 2 * tst + c.1 ^ 2 * tst / 2 - c.1 ^ 2 * tst ^ 2 / 2 -
        max (c.1 * c.2.2.2) 0 * tst = c.1 * tst * ((Q c.1 - max c.2.2.2 0) - c.1 * tst / 2) := by
      rw [hmax]
      have h2 : 2 * tst + c.1 ^ 2 * tst / 2 = c.1 * Q c.1 * tst := by rw [hQ]; ring
      linear_combination h2
    rw [hexp]
    exact mul_pos (mul_pos hγ0 htst) (by linarith)
  obtain ⟨κ, hκi, hκ0⟩ := (hζi.and self_mem_nhdsWithin).exists
  have hκpos : 0 < κ := hκ0
  -- the zero-charge disk bound
  have hcont0 : ContinuousOn (fun c : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) =>
      (c.1, (0 : ℝ), tst)) S :=
    (continuous_fst.continuousOn).prodMk (continuousOn_const.prodMk continuousOn_const)
  have hadm0 : ∀ c ∈ S, 0 < weightedCutoffSlack (c.1, (0 : ℝ), tst) := by
    intro c hc
    obtain ⟨hγ0, hγ2, ht0, ht4, -⟩ := hadmInf c hc
    have hQ0 : 0 < Q c.1 := by rw [Q]; positivity
    refine (weightedCutoffSlack_pos_iff _).mpr ⟨hγ0, hγ2, by simpa using hQ0, ht0, ?_⟩
    refine lt_min ht4 ?_
    have : 4 / c.1 ^ 2 < 2 / c.1 * (Q c.1 - 0) := by
      rw [sub_zero, Q]
      field_simp
      linarith only [pow_pos hγ0 2]
    linarith
  obtain ⟨C0, hC0, hC0b⟩ := weightedCutoff_bound_uniform_compact P X hX Xc hXc _
    (hS.image_of_continuousOn hcont0) (by
      rintro _ ⟨c, hc, rfl⟩
      exact hadm0 c hc) (closedBall 0 0) (isCompact_closedBall _ _) (2 * R0 + 1) (by linarith)
  set K0 : ℝ≥0∞ := ENNReal.ofReal (C0 * (2 * R0 + 1) ^ (4 * tst)) with hK0
  have hdisk : ∀ c ∈ S, ∀ r : ℝ, 0 ≤ r →
      ∫⁻ ω, regularizedGMC P Xc c.1 r ω (Metric.ball 0 (2 * R0 + 1)) ^ tst ∂P ≤ K0 := by
    intro c hc r hr
    obtain ⟨hγ0, hγ2, -, -, -⟩ := hadmInf c hc
    have hδ : Real.exp (-r) ≤ 2 * R0 + 1 :=
      (Real.exp_le_one_iff.mpr (by linarith)).trans (by linarith)
    have h := hC0b _ ⟨c, hc, rfl⟩ 0 (mem_closedBall_self le_rfl) (Real.exp (-r)) (2 * R0 + 1)
      (Real.exp_pos _) hδ le_rfl
    simp only [cutoffWeightedGmcBallMass_zero_charge] at h
    refine h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC0.le))
    have hexp : c.1 * (Q c.1 - 0) * tst - c.1 ^ 2 * tst ^ 2 / 2 ≤ 4 * tst := by
      have hQ : c.1 * Q c.1 = 2 + c.1 ^ 2 / 2 := by rw [Q]; field_simp
      have hγsq : c.1 ^ 2 < 2 ^ 2 := pow_lt_pow_left₀ hγ2 hγ0.le two_ne_zero
      have hQt : c.1 * (Q c.1 - 0) * tst = (2 + c.1 ^ 2 / 2) * tst := by rw [sub_zero, hQ]
      have h1 : c.1 ^ 2 * tst < 2 ^ 2 * tst := mul_lt_mul_of_pos_right hγsq htst
      have h2 : 0 ≤ c.1 ^ 2 * tst ^ 2 := by positivity
      linarith only [hQt, h1, h2]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
  set Gm : ℝ≥0∞ := ((1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ κ) ^ (1 / max 1 tst)) ^ (max 1 tst))⁻¹
    with hGm
  refine ⟨ENNReal.ofReal (2 ^ (E * tst) * R0 ^ (4 * tst)) * K0 * Gm,
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
      (geometric_factor_lt_top hκpos), κ, hκpos, fun c hc ρ hρ hρR0 r hr => ?_⟩
  obtain ⟨hγ0, hγ2, -, -, -⟩ := hadmInf c hc
  have hρ1 : ρ ≤ 1 := hρR0.trans (by rw [div_le_one (by linarith)]; linarith)
  have hinvρ : R0 ≤ 1 / ρ := by
    rw [le_div_iff₀ hρ]
    rw [le_div_iff₀ (by linarith)] at hρR0
    linarith
  have hK0b : ∀ r' : ℝ, 0 ≤ r' →
      ∫⁻ ω, regularizedGMC P Xc c.1 r' ω (exteriorAnnulus R0 0) ^ tst ∂P ≤ K0 := by
    intro r' hr'
    refine le_trans (lintegral_mono fun ω => ENNReal.rpow_le_rpow (measure_mono ?_) htst.le)
      (hdisk c hc r' hr')
    intro x hx
    rw [Metric.mem_ball, dist_zero_right]
    have := hx.2
    simp only [zero_add, pow_one] at this
    linarith
  have hfar : ∀ r' : ℝ, 0 ≤ r' →
      ∫⁻ ω, regularizedGMC P Xc c.1 r' ω (exteriorAnnulus (1 / ρ) 0) ^ tst ∂P ≤
        ENNReal.ofReal ((1 / ρ / R0) ^ (-(2 * tst + c.1 ^ 2 * tst / 2 -
          c.1 ^ 2 * tst ^ 2 / 2))) * K0 := fun r' hr' =>
    exteriorAnnulus_moment_le_far P X hX Xc hXc c.1 hR0 hinvρ hK0b hr'
  have hext := cutoff_exterior_power_moment_le P X hX Xc hXc c.1 (le_trans hR0 hinvρ)
    (le_max_right (c.1 * c.2.2.2) 0) htst hfar hr
  refine hext.trans ?_
  have hβE : max (c.1 * c.2.2.2) 0 ≤ E := max_le ((le_abs_self _).trans (hEinf c hc)) hE
  have hξ : 2 * tst + c.1 ^ 2 * tst / 2 - c.1 ^ 2 * tst ^ 2 / 2 ≤ 4 * tst := by
    have hγsq : c.1 ^ 2 < 2 ^ 2 := pow_lt_pow_left₀ hγ2 hγ0.le two_ne_zero
    have h1 : c.1 ^ 2 * tst < 2 ^ 2 * tst := mul_lt_mul_of_pos_right hγsq htst
    have h2 : 0 ≤ c.1 ^ 2 * tst ^ 2 := by positivity
    linarith only [h1, h2]
  have hcoeff := farExterior_coeff_le (κ := κ) hρ hρ1 (by linarith : (1 : ℝ) ≤ R0)
    hβE htst hξ (by linarith [hκi c hc])
  have hG := geometric_factor_le hκpos (hκi c hc) (le_refl tst)
  calc ENNReal.ofReal ((2 * (1 / ρ)) ^ (max (c.1 * c.2.2.2) 0 * tst)) *
        (ENNReal.ofReal ((1 / ρ / R0) ^ (-(2 * tst + c.1 ^ 2 * tst / 2 -
          c.1 ^ 2 * tst ^ 2 / 2))) * K0) *
        ((1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ (2 * tst + c.1 ^ 2 * tst / 2 -
          c.1 ^ 2 * tst ^ 2 / 2 - max (c.1 * c.2.2.2) 0 * tst)) ^ (1 / max 1 tst)) ^
            (max 1 tst))⁻¹
      = ENNReal.ofReal ((2 * (1 / ρ)) ^ (max (c.1 * c.2.2.2) 0 * tst) *
          (1 / ρ / R0) ^ (-(2 * tst + c.1 ^ 2 * tst / 2 - c.1 ^ 2 * tst ^ 2 / 2))) * K0 *
        ((1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ (2 * tst + c.1 ^ 2 * tst / 2 -
          c.1 ^ 2 * tst ^ 2 / 2 - max (c.1 * c.2.2.2) 0 * tst)) ^ (1 / max 1 tst)) ^
            (max 1 tst))⁻¹ := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _), mul_assoc
          (ENNReal.ofReal _) (ENNReal.ofReal _) K0]
    _ ≤ ENNReal.ofReal (2 ^ (E * tst) * R0 ^ (4 * tst) * ρ ^ κ) * K0 * Gm := by
        gcongr
    _ = ENNReal.ofReal (2 ^ (E * tst) * R0 ^ (4 * tst)) * K0 * Gm * ENNReal.ofReal (ρ ^ κ) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        ring

/-- Limit moments of the bad part are uniformly small. -/
theorem cutoffUI_bad_limit_moment_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (Mfam : ℝ → Ω → Measure ℂ) (hMfam : ∀ γ ∈ Set.Ioo (0 : ℝ) 2, IsGMCOf P X γ (Mfam γ))
    (N : ℕ) (S : Set (ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ))) (hS : IsCompact S) {tst : ℝ}
    (htst : 0 < tst)
    (hrootp : ∀ c ∈ S, ∀ k, 0 < weightedCutoffSlack (c.1, max (c.2.2.1 k) 0, tst))
    (hinf : ∀ c ∈ S, 0 < weightedCutoffSlack (c.1, max c.2.2.2 0, tst))
    {ρs : ℝ} (hρs : 0 < ρs) (hρs1 : ρs ≤ 1)
    (hsep : ∀ c ∈ S, ∀ j k, j ≠ k → 2 * ρs ≤ ‖c.2.1 j - c.2.1 k‖) :
    ∃ ρ1 : ℝ, 0 < ρ1 ∧ ∃ A : ℝ≥0∞, A < ⊤ ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ c ∈ S, ∀ ρ : ℝ, 0 < ρ →
      ρ ≤ ρ1 →
        ∫⁻ ω, (∫⁻ x in coulombBadRegion c.2.1 ρ, coulombWeight c.1 c.2.2.1 c.2.1 c.2.2.2 x
          ∂Mfam c.1 ω) ^ tst ∂P ≤ A * ENNReal.ofReal (ρ ^ κ) := by
  classical
  let _ : IsProbabilityMeasure P := hX.1
  have hadmInf : ∀ c ∈ S, 0 < c.1 ∧ c.1 < 2 := fun c hc => by
    have h := (weightedCutoffSlack_pos_iff _).mp (hinf c hc)
    exact ⟨h.1, h.2.1⟩
  -- uniform sizes
  obtain ⟨Zs0, hZs0⟩ := hS.exists_bound_of_continuousOn
    (f := fun c : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) => ∑ j, ‖c.2.1 j‖) (by fun_prop)
  obtain ⟨E0, hE0⟩ := hS.exists_bound_of_continuousOn
    (f := fun c : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) =>
      ∑ j, |c.1 * c.2.2.1 j| + |c.1 * c.2.2.2|) (by fun_prop)
  set Zs : ℝ := max Zs0 0 with hZsdef
  set E : ℝ := max E0 0 with hEdef
  have hZs : 0 ≤ Zs := le_max_right _ _
  have hE : 0 ≤ E := le_max_right _ _
  have hZc : ∀ c ∈ S, ∑ j, ‖c.2.1 j‖ ≤ Zs := fun c hc => by
    have h := hZs0 c hc
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)] at h
    exact h.trans (le_max_left _ _)
  have hEsum : ∀ c ∈ S, ∑ j, |c.1 * c.2.2.1 j| + |c.1 * c.2.2.2| ≤ E := fun c hc => by
    have h := hE0 c hc
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (Finset.sum_nonneg fun j _ =>
      abs_nonneg _) (abs_nonneg _))] at h
    exact h.trans (le_max_left _ _)
  have hEinf : ∀ c ∈ S, |c.1 * c.2.2.2| ≤ E := fun c hc => by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => abs_nonneg (c.1 * c.2.2.1 j))
    linarith [hEsum c hc]
  have hSα : ∀ c ∈ S, ∑ j, |c.1 * c.2.2.1 j| ≤ N * E := fun c hc => by
    calc ∑ j, |c.1 * c.2.2.1 j| ≤ ∑ _j : Fin N, E := Finset.sum_le_sum fun j _ => by
          have := Finset.single_le_sum (f := fun j => |c.1 * c.2.2.1 j|)
            (fun j _ => abs_nonneg _) (Finset.mem_univ j)
          linarith [hEsum c hc, abs_nonneg (c.1 * c.2.2.2)]
      _ = N * E := by simp
  -- uniform decay rate at the roots
  have hne : ∀ c ∈ S, c.1 ≠ 0 := fun c hc => (hadmInf c hc).1.ne'
  have hconton : ∀ f : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) → ℝ,
      (∀ c ∈ S, ContinuousAt f c) → ContinuousOn f S := fun f hf c hc =>
    (hf c hc).continuousWithinAt
  have hζr : ∀ k, ∀ᶠ κ in 𝓝[>] (0 : ℝ), ∀ c ∈ S,
      κ ≤ c.1 * (Q c.1 - max (c.2.2.1 k) 0) * tst - c.1 ^ 2 * tst ^ 2 / 2 := by
    intro k
    refine eventually_le_of_isCompact_of_pos hS (hconton _ fun c hc => ?_) fun c hc => ?_
    · have h := hne c hc
      simp only [Q]
      fun_prop (disch := first | exact h | exact pow_ne_zero _ h)
    · have h := (weightedCutoffSlack_pos_iff _).mp (hrootp c hc k)
      obtain ⟨hγ0, -, -, -, ht⟩ := h
      have ht2 := (lt_min_iff.mp ht).2
      have h1 : c.1 * tst / 2 < Q c.1 - max (c.2.2.1 k) 0 := by
        have h := mul_lt_mul_of_pos_left ht2 (by positivity : (0 : ℝ) < c.1 / 2)
        have hl : c.1 / 2 * (2 / c.1 * (Q c.1 - max (c.2.2.1 k) 0)) =
            Q c.1 - max (c.2.2.1 k) 0 := by
          field_simp
        linarith
      have hexp : c.1 * (Q c.1 - max (c.2.2.1 k) 0) * tst - c.1 ^ 2 * tst ^ 2 / 2 =
          c.1 * tst * ((Q c.1 - max (c.2.2.1 k) 0) - c.1 * tst / 2) := by ring
      rw [hexp]
      exact mul_pos (mul_pos hγ0 htst) (by linarith)
  obtain ⟨κr, hκr, hκr0⟩ := ((eventually_all.mpr hζr).and self_mem_nhdsWithin).exists
  have hκrpos : 0 < κr := hκr0
  -- the far exterior
  set R0 : ℝ := 2 * Zs + 2 with hR0def
  have hR02 : 2 ≤ R0 := by linarith
  obtain ⟨Ae, hAe, κe, hκe, hfarb⟩ := cutoffUI_far_exterior_moment_le P X hX Xc hXc N S hS htst
    hinf hE hEinf hR02
  set κ : ℝ := min κr κe with hκdef
  have hκpos : 0 < κ := lt_min hκrpos hκe
  -- the uniform weighted cutoff bounds at the roots, for the nonnegative parts of the charges
  have hCk : ∀ k : Fin N, ∃ C : ℝ, 0 < C ∧ ∀ c ∈ S, ∀ δ R : ℝ, 0 < δ → δ ≤ R → R ≤ 1 →
      (∫⁻ ω, ENNReal.rpow (cutoffWeightedGmcBallMass P Xc c.1 (max (c.2.2.1 k) 0) (c.2.1 k) R δ
        ω) tst ∂P) ≤ ENNReal.ofReal (C * Real.rpow R
          (c.1 * (Q c.1 - max (c.2.2.1 k) 0) * tst - c.1 ^ 2 * tst ^ 2 / 2)) := by
    intro k
    have hcont : ContinuousOn (fun c : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) =>
        (c.1, max (c.2.2.1 k) 0, tst)) S := by
      refine (continuous_fst.continuousOn).prodMk (ContinuousOn.prodMk ?_ continuousOn_const)
      exact (Continuous.max (continuous_apply k |>.comp
        (continuous_fst.comp (continuous_snd.comp continuous_snd))) continuous_const).continuousOn
    obtain ⟨C, hC, hCb⟩ := weightedCutoff_bound_uniform_compact P X hX Xc hXc _
      (hS.image_of_continuousOn hcont) (by
        rintro _ ⟨c, hc, rfl⟩
        exact hrootp c hc k) (closedBall 0 Zs) (isCompact_closedBall _ _) 1 one_pos
    refine ⟨C, hC, fun c hc δ R hδ hδR hR1 => ?_⟩
    have hzk : c.2.1 k ∈ closedBall (0 : ℂ) Zs := by
      rw [mem_closedBall, dist_zero_right]
      exact (Finset.single_le_sum (f := fun j => ‖c.2.1 j‖) (fun j _ => norm_nonneg _)
        (Finset.mem_univ k)).trans (hZc c hc)
    exact hCb _ ⟨c, hc, rfl⟩ _ hzk δ R hδ hδR hR1
  choose Ck hCkpos hCkb using hCk
  -- the uniform constant
  set CRl : ℝ := ((2 + 2 * Zs) / ρs) ^ ((N + 1) * E) with hCRl
  set CEl : ℝ := (2 : ℝ) ^ (N * E) with hCEl
  set A : ℝ≥0∞ := 2 ^ tst * (2 ^ tst * ((N : ℝ≥0∞) ^ tst *
      ∑ k, ENNReal.ofReal CRl ^ tst * ENNReal.ofReal (Ck k)) + ENNReal.ofReal CEl ^ tst * Ae)
    with hA
  have hfin : ∀ x : ℝ≥0∞, x ≠ ⊤ → x ^ tst < ⊤ := fun x hx =>
    ENNReal.rpow_lt_top_of_nonneg htst.le hx
  refine ⟨min ρs (1 / R0), lt_min hρs (by positivity), A, ?_, κ, hκpos, ?_⟩
  · refine ENNReal.mul_lt_top (hfin _ (by norm_num)) (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
    · exact ENNReal.mul_lt_top (hfin _ (by norm_num)) (ENNReal.mul_lt_top
        (hfin _ (ENNReal.natCast_ne_top N)) (ENNReal.sum_lt_top.mpr fun k _ =>
          ENNReal.mul_lt_top (hfin _ ENNReal.ofReal_ne_top) ENNReal.ofReal_lt_top))
    · exact ENNReal.mul_lt_top (hfin _ ENNReal.ofReal_ne_top) hAe
  intro c hc ρ hρ hρ1
  obtain ⟨hγ0, hγ2⟩ := hadmInf c hc
  have hρs' : ρ ≤ ρs := hρ1.trans (min_le_left _ _)
  have hρR0 : ρ ≤ 1 / R0 := hρ1.trans (min_le_right _ _)
  have hρ1' : ρ ≤ 1 := hρs'.trans hρs1
  have hinvρ : R0 ≤ 1 / ρ := by
    rw [le_div_iff₀ hρ]
    rw [le_div_iff₀ (by linarith)] at hρR0
    linarith
  set M : Ω → Measure ℂ := Mfam c.1 with hMdef
  have hM : IsGMCOf P X c.1 M := hMfam c.1 ⟨hγ0, hγ2⟩
  have hatoms : ∀ᵐ ω ∂P, ∀ k, M ω {c.2.1 k} = 0 :=
    ae_all_iff.mpr fun k => gmc_singleton_mass_eq_zero_ae P X hX c.1 hγ0 hγ2 M hM (c.2.1 k)
  set W : Fin N → Ω → ℝ≥0∞ := fun k ω =>
    weightedGmcBallMass c.1 (M ω) (max (c.2.2.1 k) 0) (c.2.1 k) ρ with hW
  set V : Ω → ℝ≥0∞ := fun ω => ∫⁻ x in {x : ℂ | 1 / ρ ≤ ‖x‖},
    ENNReal.ofReal (‖x‖ ^ max (c.1 * c.2.2.2) 0) ∂M ω with hV
  -- constants are uniform
  have hS0 : 0 ≤ ∑ j, |c.1 * c.2.2.1 j| + |c.1 * c.2.2.2| :=
    add_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) (abs_nonneg _)
  have hSE : ∑ j, |c.1 * c.2.2.1 j| + |c.1 * c.2.2.2| ≤ (N + 1) * E := by
    linarith [hSα c hc, hEinf c hc]
  have hCRle : ENNReal.ofReal (((2 + 2 * ∑ j, ‖c.2.1 j‖) / ρs) ^
      (∑ j, |c.1 * c.2.2.1 j| + |c.1 * c.2.2.2|)) ≤ ENNReal.ofReal CRl := by
    refine ENNReal.ofReal_le_ofReal (real_rpow_le_rpow_of_le_of_le ?_ ?_ hS0 hSE)
    · rw [le_div_iff₀ hρs]
      linarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => norm_nonneg (c.2.1 j))]
    · exact div_le_div_of_nonneg_right (by linarith [hZc c hc]) hρs.le
  have hCEle : ENNReal.ofReal ((2 : ℝ) ^ (∑ j, |c.1 * c.2.2.1 j|)) ≤ ENNReal.ofReal CEl :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (by norm_num) (hSα c hc))
  have hzR : ∀ j, 2 * ‖c.2.1 j‖ ≤ 1 / ρ := fun j => by
    have := (Finset.single_le_sum (f := fun j => ‖c.2.1 j‖) (fun j _ => norm_nonneg _)
      (Finset.mem_univ j)).trans (hZc c hc)
    linarith
  -- the pointwise bound
  have hpt : ∀ᵐ ω ∂P, (∫⁻ x in coulombBadRegion c.2.1 ρ,
      coulombWeight c.1 c.2.2.1 c.2.1 c.2.2.2 x ∂M ω) ≤
        ∑ k, ENNReal.ofReal CRl * W k ω + 0 * 0 + ENNReal.ofReal CEl * V ω := by
    filter_upwards [hatoms] with ω hω
    refine (lintegral_coulombBadRegion_le (M ω) _ (measurable_coulombWeight _ _ _ _) c.2.1 ρ).trans
      ?_
    rw [mul_zero, add_zero]
    refine add_le_add (Finset.sum_le_sum fun k _ => ?_) ?_
    · have hw : Measurable fun x : ℂ =>
          ENNReal.rpow (ENNReal.ofReal ‖x - c.2.1 k‖) (-c.1 * max (c.2.2.1 k) 0) :=
        (ENNReal.continuous_rpow_const (y := -c.1 * max (c.2.2.1 k) 0)).measurable.comp
          (ENNReal.measurable_ofReal.comp (measurable_id.sub_const _).norm)
      rw [hW]
      simp only []
      rw [weightedGmcBallMass, ← lintegral_const_mul _ hw]
      have hne' : ∀ᵐ x ∂(M ω).restrict (Metric.ball (c.2.1 k) ρ), x ≠ c.2.1 k :=
        ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp (hω k))
      refine lintegral_mono_ae ?_
      filter_upwards [hne', ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hxk hx
      have hroot := coulombWeight_le_root c.1 c.2.2.1 c.2.1 c.2.2.2 k hρs hρs1
        (fun j hj => hsep c hc j k hj) (Metric.ball_subset_ball hρs' hx) hxk
      refine hroot.trans (mul_le_mul' hCRle ?_)
      have hxz : ENNReal.ofReal ‖x - c.2.1 k‖ ≤ 1 := by
        rw [Metric.mem_ball, dist_eq_norm] at hx
        exact ENNReal.ofReal_le_one.mpr (by linarith)
      refine ENNReal.rpow_le_rpow_of_exponent_ge hxz ?_
      have := mul_le_mul_of_nonneg_left (le_max_left (c.2.2.1 k) 0) hγ0.le
      linarith only [this]
    · rw [hV]
      simp only []
      have hpow : Measurable fun x : ℂ => ENNReal.ofReal (‖x‖ ^ max (c.1 * c.2.2.2) 0) :=
        ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)
      rw [← lintegral_const_mul _ hpow]
      calc ∫⁻ x in {x : ℂ | 1 / ρ < ‖x‖}, coulombWeight c.1 c.2.2.1 c.2.1 c.2.2.2 x ∂M ω
          ≤ ∫⁻ x in {x : ℂ | 1 / ρ < ‖x‖}, ENNReal.ofReal CEl *
              ENNReal.ofReal (‖x‖ ^ max (c.1 * c.2.2.2) 0) ∂M ω := by
            refine setLIntegral_mono' (measurableSet_lt measurable_const measurable_norm)
              fun x hx => ?_
            have hx1 : 1 ≤ ‖x‖ := by
              have : (1 : ℝ) ≤ 1 / ρ := by rw [le_div_iff₀ hρ]; linarith
              exact this.trans (le_of_lt hx)
            refine (coulombWeight_le_exterior c.1 c.2.2.1 c.2.1 c.2.2.2
              (by rw [le_div_iff₀ hρ]; linarith : (1 : ℝ) ≤ 1 / ρ) hzR hx).trans
              (mul_le_mul' hCEle ?_)
            rw [ENNReal.rpow_eq_pow, ENNReal.ofReal_rpow_of_pos (by linarith)]
            exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hx1
              (le_max_left _ _))
        _ ≤ ∫⁻ x in {x : ℂ | 1 / ρ ≤ ‖x‖}, ENNReal.ofReal CEl *
              ENNReal.ofReal (‖x‖ ^ max (c.1 * c.2.2.2) 0) ∂M ω :=
            lintegral_mono_set fun x hx =>
              (le_of_lt (show 1 / ρ < ‖x‖ from hx) : 1 / ρ ≤ ‖x‖)
  have hWm : ∀ k, AEMeasurable (W k) P := fun k =>
    gmc_weighted_mass_aemeasurable P X hX c.1 hγ0 hγ2 M hM _ _ _
  have hVm : AEMeasurable V P :=
    gmc_setLIntegral_aemeasurable P X hX c.1 hγ0 hγ2 M hM _
      (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)) _
      (measurableSet_le measurable_const measurable_norm)
  have hmom := lintegral_rpow_le_of_le_pieces _ W (fun _ => 0) V (fun _ => ENNReal.ofReal CRl) 0
    (ENNReal.ofReal CEl) hWm aemeasurable_const hVm hpt htst
  refine hmom.trans ?_
  -- the piece moments
  have hWb : ∀ k, ∫⁻ ω, W k ω ^ tst ∂P ≤ ENNReal.ofReal (Ck k) * ENNReal.ofReal (ρ ^ κ) := by
    intro k
    have h := weightedGmcBallMoment_le_of_cutoff P X hX c.1 hγ0 hγ2 M hM Xc hXc
      (max (c.2.2.1 k) 0) (le_max_right _ _) (c.2.1 k) ρ hρ tst htst
      (ENNReal.ofReal (Ck k) * ENNReal.ofReal (ρ ^ κ)) (fun δ hδ hδρ => by
        refine (hCkb k c hc δ ρ hδ hδρ hρ1').trans ?_
        rw [← ENNReal.ofReal_mul (hCkpos k).le]
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (hCkpos k).le)
        exact Real.rpow_le_rpow_of_exponent_ge hρ hρ1' ((min_le_left _ _).trans (hκr k c hc)))
    exact h
  have hVb : ∫⁻ ω, V ω ^ tst ∂P ≤ Ae * ENNReal.ofReal (ρ ^ κ) := by
    have h := gmc_exterior_power_moment_le_of_cutoff P X hX c.1 hγ0 hγ2 M hM Xc hXc
      (R := 1 / ρ) (le_max_right (c.1 * c.2.2.2) 0) htst (Ae * ENNReal.ofReal (ρ ^ κe))
      (fun r hr => hfarb c hc ρ hρ hρR0 r hr)
    refine h.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_))
    exact Real.rpow_le_rpow_of_exponent_ge hρ hρ1' (min_le_right _ _)
  simp only [ENNReal.zero_rpow_of_pos htst, zero_mul, add_zero]
  rw [hA]
  calc 2 ^ tst * (2 ^ tst * ((N : ℝ≥0∞) ^ tst *
        ∑ k, ENNReal.ofReal CRl ^ tst * ∫⁻ ω, W k ω ^ tst ∂P) +
        ENNReal.ofReal CEl ^ tst * ∫⁻ ω, V ω ^ tst ∂P)
      ≤ 2 ^ tst * (2 ^ tst * ((N : ℝ≥0∞) ^ tst *
        ∑ k, ENNReal.ofReal CRl ^ tst * (ENNReal.ofReal (Ck k) * ENNReal.ofReal (ρ ^ κ))) +
        ENNReal.ofReal CEl ^ tst * (Ae * ENNReal.ofReal (ρ ^ κ))) := by
        gcongr with k hk
        exact hWb k
    _ = _ := by
        rw [show ∑ k, ENNReal.ofReal CRl ^ tst * (ENNReal.ofReal (Ck k) *
            ENNReal.ofReal (ρ ^ κ)) = (∑ k, ENNReal.ofReal CRl ^ tst * ENNReal.ofReal (Ck k)) *
              ENNReal.ofReal (ρ ^ κ) by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by ring]
        ring

end DOZZ.Proofs
