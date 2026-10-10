module

public import DOZZ.GMC.WeightedCutoff.RootUniform
public import DOZZ.GMC.WeightedCutoff.AnnularRoot

/-! # Uniform positive-charge weighted cutoff estimates -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Compact parameter uniformity for positive charges and orders at least one. The compact
set may contain charges of either sign; the estimate is asserted at its positive charges. -/
theorem cutoffWeightedGmcBallMoment_positive_compact_gamma_chart
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (Γ : Set ℝ) (hΓ : IsCompact Γ) (hΓ2 : Γ ⊆ Set.Ioo (0 : ℝ) 2)
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hTadm : ∀ γ ∈ Γ, ∀ t ∈ T, 1 ≤ t.2 ∧
      t.2 < min (4 / γ ^ 2) (2 / γ * (Q γ - t.1)))
    (q : ℝ) (hq : 1 < q) (hcrit : ∀ γ ∈ Γ, q < 4 / γ ^ 2)
    (hordersBound : ∀ t ∈ T, t.2 ≤ q) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ γ ∈ Γ, ∀ t ∈ T, 0 < t.1 →
      ∀ z : ℂ, ∀ R : ℝ, 0 < R → R ≤ 1 / 2 → ‖z‖ + 2 * R ≤ 1 →
      ∀ δ : ℝ, 0 < δ → δ ≤ R →
      (∫⁻ ω, cutoffWeightedGmcBallMass P Xc γ t.1 z R δ ω ^ t.2 ∂P) ≤
        C * ENNReal.ofReal (R ^ weightedCutoffMomentScaleExponent γ t.1 t.2) := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  obtain ⟨Aroot, hAroot, hballRoot⟩ := regularizedGMC_openBall_root_bound_compact_gamma_chart
    P X hX Xc hXc Γ hΓ (fun γ hγ => (hΓ2 hγ).1) q hq hcrit
  let U : Set (ℝ × (ℝ × ℝ)) := Γ ×ˢ T
  have hU : IsCompact U := hΓ.prod hT
  have hQcont : ContinuousOn (fun γ : ℝ => Q γ) Γ := by
    dsimp [Q]
    apply ContinuousOn.add
    · exact continuousOn_const.div continuousOn_id (fun γ hγ => (hΓ2 hγ).1.ne')
    · exact continuousOn_id.div_const 2
  have hQcomp : ContinuousOn (fun u : ℝ × (ℝ × ℝ) => Q u.1) U :=
    hQcont.comp continuousOn_fst (fun u hu => hu.1)
  let eta : ℝ × (ℝ × ℝ) → ℝ := fun u => weightedCutoffMomentScaleExponent u.1 u.2.1 u.2.2
  have hetaCont : ContinuousOn eta U := by
    dsimp [eta, weightedCutoffMomentScaleExponent]
    fun_prop
  have hetaPos : ∀ u ∈ U, 0 < eta u := by
    intro u hu
    have hadm := hTadm u.1 hu.1 u.2 hu.2
    exact weightedGmcMomentExponent_pos_of_sharp_range (hΓ2 hu.1).1
      (lt_of_lt_of_le zero_lt_one hadm.1) hadm.2
  obtain ⟨ε₀, hε₀, hε₀lower⟩ := hU.exists_forall_le' hetaCont hetaPos
  let ε : ℝ := ε₀ / q
  have hε : 0 < ε := by dsimp [ε]; exact div_pos hε₀ hq0
  let halfRatio : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ) ^ ε)
  have hhalfReal : (1 / 2 : ℝ) ^ ε < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) hε
  have hhalfRatio : halfRatio < 1 :=
    ENNReal.ofReal_lt_one.mpr (by simpa [halfRatio] using hhalfReal)
  have hden : 1 - halfRatio ≠ 0 := by
    intro h
    exact (not_le_of_gt hhalfRatio) (tsub_eq_zero_iff_le.mp h)
  have hgeomTop : (1 - halfRatio)⁻¹ < ⊤ :=
    lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr hden)
  let D : ℝ≥0∞ := ENNReal.ofReal ((8 : ℝ) ^ (4 : ℝ)) +
    ENNReal.ofReal ((16 : ℝ) ^ (4 : ℝ)) * halfRatio * (1 - halfRatio)⁻¹
  have hD : D < ⊤ := by
    dsimp [D]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,
      ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
        hgeomTop⟩
  let B : ℝ≥0∞ := max 1 (Aroot * D)
  have hB : B < ⊤ := by
    dsimp [B]
    exact max_lt_iff.mpr ⟨ENNReal.one_lt_top, ENNReal.mul_lt_top hAroot hD⟩
  have hBone : 1 ≤ B := by dsimp [B]; exact le_max_left _ _
  let C : ℝ≥0∞ := B ^ q
  have hC : C < ⊤ := by
    dsimp [C]
    exact lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg hq0.le hB.ne)
  refine ⟨C, hC, ?_⟩
  intro γ hγmem t ht hα z R hR hRhi hchart δ hδ hδR
  have hγ : 0 < γ := (hΓ2 hγmem).1
  have hadm := hTadm γ hγmem t ht
  have hp0 : 0 < t.2 := lt_of_lt_of_le zero_lt_one hadm.1
  have hpq' : t.2 ≤ q := hordersBound t ht
  have hetaLower : ε₀ ≤ weightedCutoffMomentScaleExponent γ t.1 t.2 := by
    simpa [eta, weightedCutoffMomentScaleExponent] using hε₀lower (γ, t) ⟨hγmem, ht⟩
  have hmargin : ε ≤ weightedCutoffMomentScaleExponent γ t.1 t.2 / t.2 := by
    have hfirst : ε₀ / q ≤ ε₀ / t.2 := by
      apply (div_le_div_iff₀ hq0 hp0).2
      exact mul_le_mul_of_nonneg_left hpq' hε₀.le
    have hsecond := div_le_div_of_nonneg_right hetaLower hp0.le
    dsimp [ε]
    exact hfirst.trans hsecond
  have hpbulk : t.2 < 4 / γ ^ 2 := lt_of_lt_of_le hadm.2 (min_le_left _ _)
  have hβeq :
      (2 * t.2 + γ ^ 2 * t.2 / 2 - γ ^ 2 * t.2 ^ 2 / 2) / t.2 =
        2 + γ ^ 2 / 2 - γ ^ 2 * t.2 / 2 := by
    field_simp [ne_of_gt hp0]
  have hγsqP : γ ^ 2 * t.2 < 4 := by
    have h := (lt_div_iff₀ (sq_pos_of_pos hγ)).mp hpbulk
    nlinarith [h]
  have hγsq : γ ^ 2 < 4 := by
    have hle : γ ^ 2 ≤ γ ^ 2 * t.2 := by
      calc
        γ ^ 2 = γ ^ 2 * 1 := by ring
        _ ≤ γ ^ 2 * t.2 :=
          mul_le_mul_of_nonneg_left hadm.1 (sq_nonneg γ)
    linarith
  have hβupper :
      (2 * t.2 + γ ^ 2 * t.2 / 2 - γ ^ 2 * t.2 ^ 2 / 2) / t.2 ≤ 4 := by
    rw [hβeq]
    nlinarith [hγsq]
  have hcore : ENNReal.ofReal ((1 / 8 : ℝ)⁻¹ ^
      ((2 * t.2 + γ ^ 2 * t.2 / 2 - γ ^ 2 * t.2 ^ 2 / 2) / t.2)) ≤
      ENNReal.ofReal ((8 : ℝ) ^ (4 : ℝ)) := by
    apply ENNReal.ofReal_le_ofReal
    have h8 : ((1 / 8 : ℝ)⁻¹) = 8 := by norm_num
    rw [h8]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hβupper
  have hshell : ENNReal.ofReal ((2 / (1 / 8 : ℝ)) ^
      ((2 * t.2 + γ ^ 2 * t.2 / 2 - γ ^ 2 * t.2 ^ 2 / 2) / t.2)) ≤
      ENNReal.ofReal ((16 : ℝ) ^ (4 : ℝ)) := by
    apply ENNReal.ofReal_le_ofReal
    have h16 : 2 / (1 / 8 : ℝ) = 16 := by norm_num
    rw [h16]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hβupper
  have hDterm : ENNReal.ofReal ((1 / 8 : ℝ)⁻¹ ^
        ((2 * t.2 + γ ^ 2 * t.2 / 2 - γ ^ 2 * t.2 ^ 2 / 2) / t.2)) +
      ENNReal.ofReal ((2 / (1 / 8 : ℝ)) ^
        ((2 * t.2 + γ ^ 2 * t.2 / 2 - γ ^ 2 * t.2 ^ 2 / 2) / t.2)) * halfRatio *
        (1 - halfRatio)⁻¹ ≤ D := by
    dsimp [D]
    apply add_le_add hcore
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hshell (by positivity)) (by positivity)
  have hK : cutoffWeightedPositiveScaleRootBoundConstant Aroot γ t.2 ε ≤ B := by
    calc
      _ ≤ Aroot * D := by
        unfold cutoffWeightedPositiveScaleRootBoundConstant
        exact mul_le_mul_of_nonneg_left hDterm (by positivity)
      _ ≤ B := le_max_right _ _
  have hmain := cutoffWeightedGmcBallMoment_positive_scale_of_root_bound_ge_one
    P X hX Xc hXc γ t.1 t.2 hγ hα hadm.1 hadm.2
    ε hε hmargin Aroot hAroot
    (fun z R δ hR hRhalf hδ hδR hlocal =>
      hballRoot γ hγmem t.2 hadm.1 hpq' z R δ hR hRhalf hδ hδR hlocal)
  have hCpow : cutoffWeightedPositiveScaleRootBoundConstant Aroot γ t.2 ε ^ t.2 ≤ C := by
    calc
      _ ≤ B ^ t.2 := ENNReal.rpow_le_rpow hK (le_of_lt hp0)
      _ ≤ B ^ q := ENNReal.rpow_le_rpow_of_exponent_le hBone hpq'
      _ = C := by rfl
  exact (hmain.2 z R hR hRhi hchart δ hδ hδR).trans
    (mul_le_mul_of_nonneg_right hCpow (by positivity))

end DOZZ.Proofs
