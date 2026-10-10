/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.Power

/-!
# GaussianFields.LogCorrelated/ABK/MAlpha

Port of the corresponding GaussianFields source module.
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace GaussianFields


/-- Finite-interval integral of `t^(α-1)`. -/
theorem integral_interval_rpow_sub_one {α a b : ℝ} (hα : 0 < α) :
    (∫ t in a..b, t ^ (α - 1) ∂(volume : Measure ℝ)) =
      (b ^ α - a ^ α) / α := by
  rw [integral_rpow (Or.inl (by linarith : -1 < α - 1))]
  ring_nf

/-- Finite-interval integral of the Abel density `t^(α-1)`. -/
theorem integral_Ioc_rpow_sub_one {α A : ℝ} (hα : 0 < α) (hA : 0 ≤ A) :
    (∫ t in Set.Ioc (0 : ℝ) A, t ^ (α - 1) ∂(volume : Measure ℝ)) =
      A ^ α / α := by
  rw [← intervalIntegral.integral_of_le hA]
  rw [integral_interval_rpow_sub_one hα]
  have hzero : (0 : ℝ) ^ α = 0 := Real.zero_rpow hα.ne'
  rw [hzero]
  ring_nf

/-- Uniform bound for an Abel-density interval integral. -/
theorem abs_alpha_mul_integral_interval_rpow_mul_le {α a b C : ℝ}
    {F : ℝ → ℝ} (hα : 0 < α) (ha : 0 ≤ a) (hab : a ≤ b)
    (hbound : ∀ t ∈ Set.Ioc a b, |F t| ≤ C) :
    |α * ∫ t in a..b, t ^ (α - 1) * F t ∂(volume : Measure ℝ)| ≤
      C * (b ^ α - a ^ α) := by
  have hbound_ae :
      ∀ᵐ t : ℝ, t ∈ Set.Ioc a b →
        ‖t ^ (α - 1) * F t‖ ≤ C * t ^ (α - 1) := by
    filter_upwards with t ht
    have ht_pos : 0 < t := lt_of_le_of_lt ha ht.1
    have ht_nonneg : 0 ≤ t := ht_pos.le
    have hpow_nonneg : 0 ≤ t ^ (α - 1) := Real.rpow_nonneg ht_nonneg (α - 1)
    calc
      ‖t ^ (α - 1) * F t‖ = t ^ (α - 1) * |F t| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpow_nonneg]
      _ ≤ t ^ (α - 1) * C := mul_le_mul_of_nonneg_left (hbound t ht) hpow_nonneg
      _ = C * t ^ (α - 1) := by ring
  have hg_int :
      IntervalIntegrable (fun t : ℝ => C * t ^ (α - 1))
        (volume : Measure ℝ) a b :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < α - 1)).const_mul C
  have hnorm :=
    intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hab hbound_ae hg_int
  have hnonneg_mass : 0 ≤ b ^ α - a ^ α := by
    have hmono := Real.rpow_le_rpow ha hab hα.le
    exact sub_nonneg.mpr hmono
  have hmass :
      ∫ t in a..b, C * t ^ (α - 1) ∂(volume : Measure ℝ) =
        C * ((b ^ α - a ^ α) / α) := by
    rw [intervalIntegral.integral_const_mul, integral_interval_rpow_sub_one hα]
  calc
    |α * ∫ t in a..b, t ^ (α - 1) * F t ∂(volume : Measure ℝ)|
        = α * ‖∫ t in a..b, t ^ (α - 1) * F t ∂(volume : Measure ℝ)‖ := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos hα]
    _ ≤ α * ∫ t in a..b, C * t ^ (α - 1) ∂(volume : Measure ℝ) :=
          mul_le_mul_of_nonneg_left hnorm hα.le
    _ = α * (C * ((b ^ α - a ^ α) / α)) := by rw [hmass]
    _ = C * (b ^ α - a ^ α) := by
          field_simp [hα.ne']

/-- Abel-error estimate: if `F` is uniformly small near zero and bounded on `(0,A]`, then
`α ∫₀ᴬ t^(α-1) F(t) dt → 0` as `α → 0+`. -/
theorem tendsto_alpha_mul_integral_interval_rpow_mul_zero {A B : ℝ}
    {F : ℝ → ℝ} (hA : 0 < A)
    (hsmall : ∀ ε > 0, ∃ δ, 0 < δ ∧ δ ≤ A ∧ ∀ t ∈ Set.Ioc (0 : ℝ) δ, |F t| ≤ ε)
    (hbound : ∀ t ∈ Set.Ioc (0 : ℝ) A, |F t| ≤ B)
    (hint : ∀ α : ℝ, 0 < α →
      IntervalIntegrable (fun t : ℝ => t ^ (α - 1) * F t)
        (volume : Measure ℝ) 0 A) :
    Tendsto
      (fun α : ℝ =>
        α * ∫ t in (0 : ℝ)..A, t ^ (α - 1) * F t ∂(volume : Measure ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let η : ℝ := ε / 4
  have hη_pos : 0 < η := by dsimp [η]; positivity
  rcases hsmall η hη_pos with ⟨δ, hδ_pos, hδ_le, hδ_small⟩
  have hδ_nonneg : 0 ≤ δ := hδ_pos.le
  have hδ_ne : δ ≠ 0 := hδ_pos.ne'
  have hA_ne : A ≠ 0 := hA.ne'
  have hA_tendsto :
      Tendsto (fun α : ℝ => A ^ α) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h : ContinuousAt (fun α : ℝ => A ^ α) 0 :=
      Real.continuousAt_const_rpow (a := A) (b := 0) hA_ne
    simpa using h.mono_left nhdsWithin_le_nhds
  have hδ_tendsto :
      Tendsto (fun α : ℝ => δ ^ α) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h : ContinuousAt (fun α : ℝ => δ ^ α) 0 :=
      Real.continuousAt_const_rpow (a := δ) (b := 0) hδ_ne
    simpa using h.mono_left nhdsWithin_le_nhds
  have htail_tendsto :
      Tendsto (fun α : ℝ => B * (A ^ α - δ ^ α))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (hA_tendsto.sub hδ_tendsto).const_mul B
  have hnear_tendsto :
      Tendsto (fun α : ℝ => η * δ ^ α) (𝓝[>] (0 : ℝ)) (𝓝 η) := by
    simpa using hδ_tendsto.const_mul η
  have htail_eventually :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        dist (B * (A ^ α - δ ^ α)) 0 < ε / 2 :=
    (Metric.tendsto_nhds.mp htail_tendsto (ε / 2) (by positivity))
  have hnear_eventually :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), η * δ ^ α < ε / 2 :=
    hnear_tendsto.eventually (Iio_mem_nhds (by dsimp [η]; linarith))
  filter_upwards [self_mem_nhdsWithin, htail_eventually, hnear_eventually] with
    α hα_pos htail hnear
  have hα : 0 < α := hα_pos
  have hInt0A := hint α hα
  have hInt0δ :
      IntervalIntegrable (fun t : ℝ => t ^ (α - 1) * F t)
        (volume : Measure ℝ) 0 δ := by
    exact hInt0A.mono_set
      (Set.uIcc_subset_uIcc
        (by rw [Set.mem_uIcc]; exact Or.inl ⟨le_rfl, hA.le⟩)
        (by rw [Set.mem_uIcc]; exact Or.inl ⟨hδ_pos.le, hδ_le⟩))
  have hIntδA :
      IntervalIntegrable (fun t : ℝ => t ^ (α - 1) * F t)
        (volume : Measure ℝ) δ A := by
    exact hInt0A.mono_set
      (Set.uIcc_subset_uIcc
        (by rw [Set.mem_uIcc]; exact Or.inl ⟨hδ_pos.le, hδ_le⟩)
        (by rw [Set.mem_uIcc]; exact Or.inl ⟨hA.le, le_rfl⟩))
  have hsplit :
      (∫ t in (0 : ℝ)..A, t ^ (α - 1) * F t ∂(volume : Measure ℝ)) =
        (∫ t in (0 : ℝ)..δ, t ^ (α - 1) * F t ∂(volume : Measure ℝ)) +
          ∫ t in δ..A, t ^ (α - 1) * F t ∂(volume : Measure ℝ) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hInt0δ hIntδA]
  have hnear_bound :
      |α * ∫ t in (0 : ℝ)..δ, t ^ (α - 1) * F t ∂(volume : Measure ℝ)| ≤
        η * δ ^ α := by
    have h :=
      abs_alpha_mul_integral_interval_rpow_mul_le
        (α := α) (a := 0) (b := δ) (C := η) (F := F)
        hα (by norm_num) hδ_pos.le hδ_small
    have hzero : (0 : ℝ) ^ α = 0 := Real.zero_rpow hα.ne'
    simpa [hzero] using h
  have htail_bound :
      |α * ∫ t in δ..A, t ^ (α - 1) * F t ∂(volume : Measure ℝ)| ≤
        B * (A ^ α - δ ^ α) := by
    exact
      abs_alpha_mul_integral_interval_rpow_mul_le
        (α := α) (a := δ) (b := A) (C := B) (F := F)
        hα hδ_nonneg hδ_le (fun t ht => hbound t ⟨hδ_pos.trans ht.1, ht.2⟩)
  have htail_abs : |B * (A ^ α - δ ^ α)| < ε / 2 := by
    simpa [Real.dist_eq, Real.norm_eq_abs] using htail
  have hmain :
      |α * ∫ t in (0 : ℝ)..A, t ^ (α - 1) * F t ∂(volume : Measure ℝ)| < ε := by
    calc
      |α * ∫ t in (0 : ℝ)..A, t ^ (α - 1) * F t ∂(volume : Measure ℝ)|
          = |α * ∫ t in (0 : ℝ)..δ, t ^ (α - 1) * F t ∂(volume : Measure ℝ) +
              α * ∫ t in δ..A, t ^ (α - 1) * F t ∂(volume : Measure ℝ)| := by
            rw [hsplit]
            ring_nf
      _ ≤ |α * ∫ t in (0 : ℝ)..δ, t ^ (α - 1) * F t ∂(volume : Measure ℝ)| +
            |α * ∫ t in δ..A, t ^ (α - 1) * F t ∂(volume : Measure ℝ)| :=
            abs_add_le _ _
      _ ≤ η * δ ^ α + B * (A ^ α - δ ^ α) :=
            add_le_add hnear_bound htail_bound
      _ ≤ η * δ ^ α + |B * (A ^ α - δ ^ α)| :=
            by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_left (le_abs_self (B * (A ^ α - δ ^ α))) (η * δ ^ α)
      _ < ε / 2 + ε / 2 := add_lt_add hnear htail_abs
      _ = ε := by ring
  simpa [Real.dist_eq, Real.norm_eq_abs] using hmain

/-- Abel limit on a finite interval for a function continuous at the lower endpoint, stated in
terms of the small-neighborhood and bounded-error estimates used by the ABK self-convolution. -/
theorem tendsto_alpha_mul_integral_interval_rpow {A B : ℝ} {F : ℝ → ℝ}
    (hA : 0 < A)
    (hsmall :
      ∀ ε > 0, ∃ δ, 0 < δ ∧ δ ≤ A ∧
        ∀ t ∈ Set.Ioc (0 : ℝ) δ, |F t - F 0| ≤ ε)
    (hbound : ∀ t ∈ Set.Ioc (0 : ℝ) A, |F t - F 0| ≤ B)
    (hint : ∀ α : ℝ, 0 < α →
      IntervalIntegrable (fun t : ℝ => t ^ (α - 1) * (F t - F 0))
        (volume : Measure ℝ) 0 A) :
    Tendsto
      (fun α : ℝ =>
        α * ∫ t in (0 : ℝ)..A, t ^ (α - 1) * F t ∂(volume : Measure ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (F 0)) := by
  let G : ℝ → ℝ := fun t => F t - F 0
  have herror :
      Tendsto
        (fun α : ℝ =>
          α * ∫ t in (0 : ℝ)..A, t ^ (α - 1) * G t ∂(volume : Measure ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_alpha_mul_integral_interval_rpow_mul_zero
      (A := A) (B := B) (F := G) hA hsmall hbound hint
  have hA_ne : A ≠ 0 := hA.ne'
  have hA_tendsto :
      Tendsto (fun α : ℝ => A ^ α) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h : ContinuousAt (fun α : ℝ => A ^ α) 0 :=
      Real.continuousAt_const_rpow (a := A) (b := 0) hA_ne
    simpa using h.mono_left nhdsWithin_le_nhds
  have hconst :
      Tendsto (fun α : ℝ => F 0 * A ^ α) (𝓝[>] (0 : ℝ)) (𝓝 (F 0)) := by
    simpa using hA_tendsto.const_mul (F 0)
  have hsum := herror.add hconst
  have hsum' :
      Tendsto
        (fun α : ℝ =>
          α * ∫ t in (0 : ℝ)..A, t ^ (α - 1) * G t ∂(volume : Measure ℝ) +
            F 0 * A ^ α)
        (𝓝[>] (0 : ℝ)) (𝓝 (F 0)) := by
    simpa using hsum
  refine hsum'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with α hα_mem
  have hα : 0 < α := hα_mem
  have hG_int := hint α hα
  have hrpow_int :
      IntervalIntegrable (fun t : ℝ => t ^ (α - 1))
        (volume : Measure ℝ) 0 A :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < α - 1)
  have hconst_int :
      IntervalIntegrable (fun t : ℝ => F 0 * t ^ (α - 1))
        (volume : Measure ℝ) 0 A :=
    hrpow_int.const_mul (F 0)
  have hzero : (0 : ℝ) ^ α = 0 := Real.zero_rpow hα.ne'
  symm
  calc
    α * ∫ t in (0 : ℝ)..A, t ^ (α - 1) * F t ∂(volume : Measure ℝ)
        = α * ∫ t in (0 : ℝ)..A,
            (t ^ (α - 1) * G t + F 0 * t ^ (α - 1)) ∂(volume : Measure ℝ) := by
          congr 1
          refine intervalIntegral.integral_congr ?_
          intro t _ht
          dsimp [G]
          ring_nf
    _ = α *
        ((∫ t in (0 : ℝ)..A, t ^ (α - 1) * G t ∂(volume : Measure ℝ)) +
          ∫ t in (0 : ℝ)..A, F 0 * t ^ (α - 1) ∂(volume : Measure ℝ)) := by
          rw [intervalIntegral.integral_add hG_int hconst_int]
    _ = α * (∫ t in (0 : ℝ)..A, t ^ (α - 1) * G t ∂(volume : Measure ℝ)) +
        F 0 * A ^ α := by
          rw [intervalIntegral.integral_const_mul, integral_interval_rpow_sub_one hα, hzero]
          field_simp [hα.ne']
          ring

/-- After the reciprocal substitution, the `M_α^{-1}` integral is supported on `(0,2]`. -/
theorem abkMAlphaInv_eq_integral_Ioc_two {d : Nat} (hd : 0 < d)
    (ζ : ABKCutoff d) (α : ℝ) :
    abkMAlphaInv ζ α =
      ∫ t in Set.Ioc (0 : ℝ) 2,
        t ^ (α - 1) * abkCutoffSelfConvolution ζ (abkRadialPoint d t)
        ∂(volume : Measure ℝ) := by
  rw [abkMAlphaInv_eq_integral_rpow_selfConvolution ζ α]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi ?_ ?_
  · exact Set.Ioc_subset_Ioi_self
  · intro t ht
    have ht_pos : 0 < t := ht.1
    have ht_not_le : ¬ t ≤ 2 := by
      intro ht_le
      exact ht.2 ⟨ht_pos, ht_le⟩
    have ht_two : 2 < t := lt_of_not_ge ht_not_le
    rw [abkCutoffSelfConvolution_radial_eq_zero_of_two_lt hd ζ ht_two, mul_zero]

/-- The radial self-convolution profile is continuous. -/
theorem continuous_abkCutoffSelfConvolution_radialProfile {d : Nat}
    (ζ : ABKCutoff d) :
    Continuous (fun t : ℝ => abkCutoffSelfConvolution ζ (abkRadialPoint d t)) := by
  exact (continuous_abkCutoffSelfConvolution ζ).comp (by
    refine continuous_pi ?_
    intro i
    by_cases hi : (i : Nat) = 0
    · simp only [abkRadialPoint, ite_eq_left hi]
      continuity
    · simpa [abkRadialPoint, hi] using continuous_const)

/-- At radial parameter zero, the self-convolution profile is `M_0`. -/
theorem abkCutoffSelfConvolution_radialProfile_zero {d : Nat}
    (ζ : ABKCutoff d) :
    abkCutoffSelfConvolution ζ (abkRadialPoint d 0) = abkM0 ζ := by
  have hpoint : abkRadialPoint d 0 = (0 : Vec d) := by
    ext i
    simp [abkRadialPoint]
  rw [hpoint, abkCutoffSelfConvolution_zero]

/-- The Abel limit for the ABK radial self-convolution profile on `(0,2]`. -/
theorem tendsto_alpha_mul_integral_Ioc_two_abkSelfConvolution {d : Nat}
    (ζ : ABKCutoff d) :
    Tendsto
      (fun α : ℝ =>
        α * ∫ t in Set.Ioc (0 : ℝ) 2,
          t ^ (α - 1) * abkCutoffSelfConvolution ζ (abkRadialPoint d t)
          ∂(volume : Measure ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (abkM0 ζ)) := by
  let F : ℝ → ℝ := fun t => abkCutoffSelfConvolution ζ (abkRadialPoint d t)
  have hF_cont : Continuous F := continuous_abkCutoffSelfConvolution_radialProfile ζ
  have hF0 : F 0 = abkM0 ζ := abkCutoffSelfConvolution_radialProfile_zero ζ
  let H : ℝ → ℝ := fun t => |F t - F 0|
  have hH_cont : Continuous H := (hF_cont.sub continuous_const).abs
  have hBdd : BddAbove (H '' Set.Icc (0 : ℝ) 2) :=
    isCompact_Icc.bddAbove_image hH_cont.continuousOn
  rcases hBdd with ⟨B, hB⟩
  have hsmall :
      ∀ ε > 0, ∃ δ, 0 < δ ∧ δ ≤ (2 : ℝ) ∧
        ∀ t ∈ Set.Ioc (0 : ℝ) δ, |F t - F 0| ≤ ε := by
    intro ε hε
    have hF_tendsto : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (F 0)) :=
      hF_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    rcases (Metric.tendsto_nhdsWithin_nhds.mp hF_tendsto) ε hε with
      ⟨δ₀, hδ₀_pos, hδ₀⟩
    refine ⟨min (δ₀ / 2) 2, ?_, min_le_right _ _, ?_⟩
    · exact lt_min (half_pos hδ₀_pos) (by norm_num)
    · intro t ht
      have ht_pos : t ∈ Set.Ioi (0 : ℝ) := ht.1
      have hdist : dist t 0 < δ₀ := by
        calc
          dist t 0 = t := by
            rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1.le]
          _ ≤ min (δ₀ / 2) 2 := ht.2
          _ ≤ δ₀ / 2 := min_le_left _ _
          _ < δ₀ := by linarith
      have hf := hδ₀ ht_pos hdist
      exact le_of_lt (by simpa [Real.dist_eq, Real.norm_eq_abs, abs_sub_comm] using hf)
  have hbound : ∀ t ∈ Set.Ioc (0 : ℝ) 2, |F t - F 0| ≤ B := by
    intro t ht
    exact hB ⟨t, ⟨ht.1.le, ht.2⟩, rfl⟩
  have hint : ∀ α : ℝ, 0 < α →
      IntervalIntegrable (fun t : ℝ => t ^ (α - 1) * (F t - F 0))
        (volume : Measure ℝ) 0 2 := by
    intro α hα
    have hrpow :
        IntervalIntegrable (fun t : ℝ => t ^ (α - 1))
          (volume : Measure ℝ) 0 2 :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < α - 1)
    have hG_cont :
        ContinuousOn (fun t : ℝ => F t - F 0) (Set.uIcc (0 : ℝ) 2) :=
      (hF_cont.sub continuous_const).continuousOn
    exact hrpow.mul_continuousOn hG_cont
  have hlim :=
    tendsto_alpha_mul_integral_interval_rpow
      (A := (2 : ℝ)) (B := B) (F := F) (by norm_num : (0 : ℝ) < 2)
      hsmall hbound hint
  have hlim' :
      Tendsto
        (fun α : ℝ =>
          α * ∫ t in (0 : ℝ)..(2 : ℝ), t ^ (α - 1) * F t ∂(volume : Measure ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 (abkM0 ζ)) := by
    simpa [hF0] using hlim
  refine hlim'.congr' ?_
  filter_upwards with α
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]

/-- The Appendix A limit `α M_α^{-1} → M_0`. -/
theorem tendsto_alpha_mul_abkMAlphaInv {d : Nat} (hd : 0 < d)
    (ζ : ABKCutoff d) :
    Tendsto (fun α : ℝ => α * abkMAlphaInv ζ α)
      (𝓝[>] (0 : ℝ)) (𝓝 (abkM0 ζ)) := by
  have hlim := tendsto_alpha_mul_integral_Ioc_two_abkSelfConvolution ζ
  refine hlim.congr' ?_
  filter_upwards with α
  rw [abkMAlphaInv_eq_integral_Ioc_two hd ζ α]

/-- Scalar logarithmic limit used in the covariance computation:
`(ρ^{-α} - 1) / α → -log ρ` as `α → 0+`. -/
theorem tendsto_rpow_neg_sub_one_div_nhdsGT_zero {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun α : ℝ => (ρ ^ (-α) - 1) / α)
      (𝓝[>] (0 : ℝ)) (𝓝 (-Real.log ρ)) := by
  have hneg : HasDerivAt (fun α : ℝ => -α) (-1) 0 :=
    hasDerivAt_neg' (0 : ℝ)
  have hderiv : HasDerivAt (fun α : ℝ => ρ ^ (-α)) (-Real.log ρ) 0 := by
    have h := hneg.const_rpow hρ
    simpa [Real.rpow_zero] using h
  have hslope := hderiv.tendsto_slope_zero
  have hmono : 𝓝[>] (0 : ℝ) ≤ nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ) := by
    refine nhdsWithin_mono _ ?_
    intro x hx
    have hx_pos : 0 < x := hx
    simp [hx_pos.ne']
  refine (hslope.mono_left hmono).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with α hα
  rw [zero_add, neg_zero, Real.rpow_zero]
  change α⁻¹ * (ρ ^ (-α) - 1) = (ρ ^ (-α) - 1) / α
  rw [div_eq_mul_inv]
  ring

end GaussianFields

end
