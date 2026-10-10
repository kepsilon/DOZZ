/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.UnreflectedC
public import DOZZ.FourPoint.BPZ.StructureConstantGammaCont
public import DOZZ.GMC.Assembly.AdmissibleGMC
public import DOZZ.GMC.Construction.GMCUniqueAe

/-! # The unreflected `γ/2` formula on the whole range `0 < γ < 2`

The shift relation holds for `γ² < 2` (analytic continuation from the interval treated in
[KRV-local]) and for `2 < γ² < 4` (Taylor expansion with the rooted asymptotics). At `γ² = 2` both
sides of the shift relation are continuous in `γ` along a family of GMC measures
(`bpz_continuousAt_structureConstant_gamma`), so the relation passes to the limit. Together with
the diagonal formula at `χ = γ/2` this gives the unreflected formula.

The diagonal formula is the statement `DOZZ.degenerateFourPoint_diagonal_classification` (at
`χ = γ/2`); it enters here as a hypothesis, for all GMC measures, all `γ ∈ (0, 2)` and all first
charges of the unreflected domain. -/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- The constraints of the unreflected domain persist near `γ₀`. -/
theorem bpz_unreflected_domain_eventually {γ₀ α₁ α₂ α₃ : ℝ} (hγ : 0 < γ₀) (hγ2 : γ₀ < 2)
    (hαlo : γ₀ / 2 < α₁) (hαhi : α₁ < 2 / γ₀) (hα₂ : α₂ < Q γ₀) (hα₃ : α₃ < Q γ₀)
    (hs : 2 * Q γ₀ + γ₀ / 2 < α₁ + α₂ + α₃) :
    ∀ᶠ γ in 𝓝 γ₀, 0 < γ ∧ γ < 2 ∧ γ / 2 < α₁ ∧ α₁ < 2 / γ ∧ α₂ < Q γ ∧ α₃ < Q γ ∧
      2 * Q γ + γ / 2 < α₁ + α₂ + α₃ := by
  have hQc : ContinuousAt Q γ₀ := by
    show ContinuousAt (fun γ => 2 / γ + γ / 2) γ₀
    exact (continuousAt_const.div continuousAt_id hγ.ne').add (continuousAt_id.div_const 2)
  have hdiv : ContinuousAt (fun γ : ℝ => 2 / γ) γ₀ := continuousAt_const.div continuousAt_id hγ.ne'
  filter_upwards [continuousAt_const.eventually_lt continuousAt_id hγ,
    continuousAt_id.eventually_lt continuousAt_const hγ2,
    (continuousAt_id.div_const 2).eventually_lt continuousAt_const hαlo,
    continuousAt_const.eventually_lt hdiv hαhi,
    continuousAt_const.eventually_lt hQc hα₂, continuousAt_const.eventually_lt hQc hα₃,
    ((hQc.const_mul 2).add (continuousAt_id.div_const 2)).eventually_lt continuousAt_const hs]
    with γ h1 h2 h3 h4 h5 h6 h7
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- The three arguments of `lFun` in the planar constant are not integers. -/
theorem bpz_planar_args_nonint {γ t : ℝ} (hγ : 0 < γ) (hlo : γ / 2 < t) (hhi : t < 2 / γ) :
    (∀ n : ℤ, γ * t / 2 ≠ n) ∧ (∀ n : ℤ, -(γ ^ 2 / 2) / 2 ≠ n) ∧
      ∀ n : ℤ, 2 - γ * t / 2 + γ ^ 2 / 2 / 2 ≠ n := by
  have hγt1 : γ * t / 2 < 1 := by
    have := mul_lt_mul_of_pos_left hhi hγ
    have e : γ * (2 / γ) = 2 := by field_simp
    linarith
  have hγt0 : γ ^ 2 / 4 < γ * t / 2 := by
    have := mul_lt_mul_of_pos_left hlo hγ
    nlinarith
  have hpos : 0 < γ ^ 2 / 4 := by positivity
  have hγsq : γ ^ 2 < 4 := by nlinarith
  refine ⟨fun n hn => ?_, fun n hn => ?_, fun n hn => ?_⟩
  · have h0 : (0 : ℝ) < n := by rw [← hn]; linarith
    have h1 : (n : ℝ) < 1 := by rw [← hn]; exact hγt1
    have : (0 : ℤ) < n := by exact_mod_cast h0
    have : n < (1 : ℤ) := by exact_mod_cast h1
    omega
  · have h0 : (-1 : ℝ) < n := by rw [← hn]; linarith
    have h1 : (n : ℝ) < 0 := by rw [← hn]; linarith
    have : (-1 : ℤ) < n := by exact_mod_cast h0
    have : n < (0 : ℤ) := by exact_mod_cast h1
    omega
  · have h0 : (1 : ℝ) < n := by rw [← hn]; linarith
    have h1 : (n : ℝ) < 2 := by rw [← hn]; linarith
    have : (1 : ℤ) < n := by exact_mod_cast h0
    have : n < (2 : ℤ) := by exact_mod_cast h1
    omega

/-- The explicit coefficients of the shift relation are continuous in `γ`. -/
theorem bpz_continuousAt_shift_coefficients {γ₀ α₁ α₂ α₃ : ℝ} (hγ : 0 < γ₀) (hγ2 : γ₀ < 2)
    (hαlo : γ₀ / 2 < α₁) (hαhi : α₁ < 2 / γ₀) (hα₂ : α₂ < Q γ₀) (hα₃ : α₃ < Q γ₀)
    (hs : 2 * Q γ₀ + γ₀ / 2 < α₁ + α₂ + α₃) :
    ContinuousAt (fun γ => gaussCoefficientRatio (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
      (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁)) γ₀ ∧
    ContinuousAt (fun γ => (planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re) γ₀ := by
  have _ := hγ2
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    bpz_gauss_args_pos hγ hαlo hαhi hα₂ hα₃ hs
  have hQa : AnalyticAt ℝ Q γ₀ := by
    show AnalyticAt ℝ (fun γ => 2 / γ + γ / 2) γ₀
    exact (analyticAt_const.div analyticAt_id hγ.ne').add (analyticAt_id.div analyticAt_const
      two_ne_zero)
  have hA : AnalyticAt ℝ (fun γ => gaussParameterA γ (γ / 2) α₁ α₂ α₃) γ₀ := by
    unfold gaussParameterA
    have h := hQa
    fun_prop
  have hB : AnalyticAt ℝ (fun γ => gaussParameterB γ (γ / 2) α₁ α₂ α₃) γ₀ := by
    unfold gaussParameterB
    have h := hQa
    fun_prop
  have hC : AnalyticAt ℝ (fun γ => gaussParameterC γ (γ / 2) α₁) γ₀ := by
    unfold gaussParameterC
    have h := hQa
    fun_prop
  refine ⟨(bpz_analyticAt_gaussCoefficientRatio hA hB hC h1 h2 h3 h4 h5 h6 h7 h8 h9
    h10).continuousAt, ?_⟩
  obtain ⟨g1, g2, g3⟩ := bpz_planar_args_nonint hγ hαlo hαhi
  have hPGC := bpz_analyticAt_re_planarGaussConstant (k := fun γ => γ ^ 2 / 2)
    (β := fun γ => γ * α₁) (x₀ := γ₀) (by fun_prop) (by fun_prop)
    (by simpa [mul_div_assoc] using g1) (by simpa using g2) (by simpa [mul_div_assoc] using g3)
  exact hPGC.continuousAt

/-- The shift relation at a fixed `γ`, as a proposition (used only inside proofs). -/
theorem bpz_shift_all {Ω : Type*} [MeasurableSpace Ω] {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ)
    (γ μ α₁ α₂ α₃ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hαlo : γ / 2 < α₁) (hαhi : α₁ < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hdiag : ∀ (M' : Ω → Measure ℂ) (γ' t : ℝ), 0 < γ' → γ' < 2 → IsGMCOf P X γ' M' →
      γ' / 2 < t → t < 2 / γ' → α₂ < Q γ' → α₃ < Q γ' → 2 * Q γ' + γ' / 2 < t + α₂ + α₃ →
      ∀ z ∈ gaussCutPlane, fourPointT P M' γ' μ (-(γ' / 2)) t α₂ α₃ z =
        structureConstant P M' γ' μ (t - γ' / 2) α₂ α₃ *
          (‖gaussFMinus H (gaussParameterA γ' (γ' / 2) t α₂ α₃)
              (gaussParameterB γ' (γ' / 2) t α₂ α₃) (gaussParameterC γ' (γ' / 2) t) z‖ ^ 2 +
            gaussCoefficientRatio (gaussParameterA γ' (γ' / 2) t α₂ α₃)
                (gaussParameterB γ' (γ' / 2) t α₂ α₃) (gaussParameterC γ' (γ' / 2) t) *
              ‖gaussFPlus H (gaussParameterA γ' (γ' / 2) t α₂ α₃)
                (gaussParameterB γ' (γ' / 2) t α₂ α₃) (gaussParameterC γ' (γ' / 2) t) z‖ ^ 2)) :
    gaussCoefficientRatio (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
        (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁) *
          structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ =
        -μ * (planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re *
          structureConstant P M γ μ (α₁ + γ / 2) α₂ α₃ := by
  -- the non-critical cases
  have hnc : ∀ (M' : Ω → Measure ℂ) (γ' : ℝ), 0 < γ' → γ' < 2 → IsGMCOf P X γ' M' →
      γ' ^ 2 ≠ 2 → γ' / 2 < α₁ → α₁ < 2 / γ' → α₂ < Q γ' → α₃ < Q γ' →
      2 * Q γ' + γ' / 2 < α₁ + α₂ + α₃ →
      gaussCoefficientRatio (gaussParameterA γ' (γ' / 2) α₁ α₂ α₃)
          (gaussParameterB γ' (γ' / 2) α₁ α₂ α₃) (gaussParameterC γ' (γ' / 2) α₁) *
            structureConstant P M' γ' μ (α₁ - γ' / 2) α₂ α₃ =
          -μ * (planarGaussConstant (γ' ^ 2 / 2) (γ' * α₁)).re *
            structureConstant P M' γ' μ (α₁ + γ' / 2) α₂ α₃ := by
    intro M' γ' h0 h2 hM' hne hlo hhi h₂ h₃ hs'
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact bpz_shift_small_gamma hH P X M' γ' μ α₁ α₂ α₃ h0 hlt hμ hlo hhi h₂ h₃ hs' hX hM'
        fun t ht1 ht2 ht3 => hdiag M' γ' t h0 h2 hM' ht1 ht2 h₂ h₃ ht3
    · exact bpz_shift_large_gamma hH P X M' γ' μ α₁ α₂ α₃ h0 h2 hgt hμ hlo hhi h₂ h₃ hs' hX hM'
        (hdiag M' γ' α₁ h0 h2 hM' hlo hhi h₂ h₃ hs')
  by_cases hcrit : γ ^ 2 ≠ 2
  · exact hnc M γ hγ hγ2 hM hcrit hαlo hαhi hα₂ hα₃ hs
  push Not at hcrit
  -- a family of GMC measures
  have hex : ∀ γ' ∈ Ioo (0 : ℝ) 2, ∃ M' : Ω → Measure ℂ, IsGMCOf P X γ' M' := by
    intro γ' hγ'
    obtain ⟨_, M', -, hM'⟩ := equatorGFF_circle_average_GMC_exists P X hX γ' hγ'.1 hγ'.2
    exact ⟨M', hM'⟩
  let Mfam : ℝ → Ω → Measure ℂ := fun γ' =>
    if h : γ' ∈ Ioo (0 : ℝ) 2 then Classical.choose (hex γ' h) else M
  have hMfam : ∀ γ' ∈ Ioo (0 : ℝ) 2, IsGMCOf P X γ' (Mfam γ') := by
    intro γ' hγ'
    simp only [Mfam, hγ', ↓reduceDIte]
    exact Classical.choose_spec (hex γ' hγ')
  have hγmem : γ ∈ Ioo (0 : ℝ) 2 := ⟨hγ, hγ2⟩
  have hMγ : ∀ᵐ ω ∂P, Mfam γ ω = M ω :=
    equatorGFF_GMC_unique_ae P X hX γ (Mfam γ) M (hMfam γ hγmem) hM
  -- the two sides along the family
  set L : ℝ → ℝ := fun γ' => gaussCoefficientRatio (gaussParameterA γ' (γ' / 2) α₁ α₂ α₃)
      (gaussParameterB γ' (γ' / 2) α₁ α₂ α₃) (gaussParameterC γ' (γ' / 2) α₁) *
    structureConstant P (Mfam γ') γ' μ (α₁ - γ' / 2) α₂ α₃ with hL
  set R : ℝ → ℝ := fun γ' => -μ * (planarGaussConstant (γ' ^ 2 / 2) (γ' * α₁)).re *
    structureConstant P (Mfam γ') γ' μ (α₁ + γ' / 2) α₂ α₃ with hR
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  obtain ⟨hρc, hPc⟩ := bpz_continuousAt_shift_coefficients hγ hγ2 hαlo hαhi hα₂ hα₃ hs
  have hsm : 0 < sExp γ (α₁ - γ / 2) α₂ α₃ := by
    unfold sExp; exact div_pos (by linarith) hγ
  have hsp : 0 < sExp γ (α₁ + γ / 2) α₂ α₃ := by
    unfold sExp; exact div_pos (by linarith) hγ
  have hCm := bpz_continuousAt_structureConstant_gamma P X hX Mfam hMfam μ hμ
    (f := fun γ' => α₁ - γ' / 2) (by fun_prop) α₂ α₃ hγmem
    (by rw [hQ]; have : (0 : ℝ) < γ / 2 := by positivity
        have : α₁ < 2 / γ := hαhi
        linarith) hα₂ hα₃ hsm
  have hCp := bpz_continuousAt_structureConstant_gamma P X hX Mfam hMfam μ hμ
    (f := fun γ' => α₁ + γ' / 2) (by fun_prop) α₂ α₃ hγmem
    (by rw [hQ]; have : α₁ < 2 / γ := hαhi; linarith) hα₂ hα₃ hsp
  have hLc : ContinuousAt L γ := hρc.mul hCm
  have hRc : ContinuousAt R γ := (continuousAt_const.mul hPc).mul hCp
  -- equality off the critical point
  have hev : L =ᶠ[𝓝[≠] γ] R := by
    have hdom := bpz_unreflected_domain_eventually hγ hγ2 hαlo hαhi hα₂ hα₃ hs
    filter_upwards [nhdsWithin_le_nhds hdom, self_mem_nhdsWithin] with γ' h hne
    obtain ⟨h0, h2, hlo, hhi, h₂, h₃, hs'⟩ := h
    have hne2 : γ' ^ 2 ≠ 2 := by
      intro heq
      apply hne
      have : γ' ^ 2 = γ ^ 2 := by rw [heq, hcrit]
      exact (pow_left_inj₀ h0.le hγ.le two_ne_zero).mp this
    exact hnc (Mfam γ') γ' h0 h2 (hMfam γ' ⟨h0, h2⟩) hne2 hlo hhi h₂ h₃ hs'
  have hLR : L γ = R γ := tendsto_nhds_unique
    ((hLc.tendsto.mono_left nhdsWithin_le_nhds).congr' hev)
    (hRc.tendsto.mono_left nhdsWithin_le_nhds)
  simp only [hL, hR] at hLR
  rw [bpz_structureConstant_congr P hMγ, bpz_structureConstant_congr P hMγ] at hLR
  exact hLR

/-- **The unreflected `γ/2` formula, conditional on the diagonal formula.** -/
theorem bpz_gammaHalf_full_unreflected_formula_of_diag {Ω : Type*} [MeasurableSpace Ω]
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H)
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hαlo : γ / 2 < α₁) (hαhi : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hdiag : ∀ (M' : Ω → Measure ℂ) (γ' t : ℝ), 0 < γ' → γ' < 2 → IsGMCOf P X γ' M' →
      γ' / 2 < t → t < 2 / γ' → α₂ < Q γ' → α₃ < Q γ' → 2 * Q γ' + γ' / 2 < t + α₂ + α₃ →
      ∀ z ∈ gaussCutPlane, fourPointT P M' γ' μ (-(γ' / 2)) t α₂ α₃ z =
        structureConstant P M' γ' μ (t - γ' / 2) α₂ α₃ *
          (‖gaussFMinus H (gaussParameterA γ' (γ' / 2) t α₂ α₃)
              (gaussParameterB γ' (γ' / 2) t α₂ α₃) (gaussParameterC γ' (γ' / 2) t) z‖ ^ 2 +
            gaussCoefficientRatio (gaussParameterA γ' (γ' / 2) t α₂ α₃)
                (gaussParameterB γ' (γ' / 2) t α₂ α₃) (gaussParameterC γ' (γ' / 2) t) *
              ‖gaussFPlus H (gaussParameterA γ' (γ' / 2) t α₂ α₃)
                (gaussParameterB γ' (γ' / 2) t α₂ α₃) (gaussParameterC γ' (γ' / 2) t) z‖ ^ 2)) :
    let a := gaussParameterA γ (γ / 2) α₁ α₂ α₃
    let b := gaussParameterB γ (γ / 2) α₁ α₂ α₃
    let c := gaussParameterC γ (γ / 2) α₁
    ∀ z ∈ gaussCutPlane,
      fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z =
        structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ *
            ‖gaussFMinus H a b c z‖ ^ 2 +
          (-μ * (planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re) *
            structureConstant P M γ μ (α₁ + γ / 2) α₂ α₃ *
              ‖gaussFPlus H a b c z‖ ^ 2 := by
  intro a b c
  exact bpz_unreflected_of_shift P M γ μ α₁ α₂ α₃
    (hdiag M γ α₁ hγ hγ₂ hM hαlo hαhi hα₂ hα₃ hs)
    (bpz_shift_all hH P X M γ μ α₁ α₂ α₃ hγ hγ₂ hμ hαlo hαhi hα₂ hα₃ hs hX hM hdiag)

end DOZZ.Proofs
