/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.OpenSetScale
public import DOZZ.GMC.Moments.CriticalSuperadditivity

/-! # Divergence of the critical moment

At the critical order `p_c = 4/γ²` the scaling exponent is `ξ(p_c) = 2`, so the four half-size
open subsquares of a reference square carry together exactly the `p_c`-th moment of the square
(`4 · (1/2)² = 1`). If that moment were finite, strict superadditivity of `t ↦ t^{p_c}` on the event
that the subsquares all have positive mass would make it strictly larger than itself. Hence the
critical moment is infinite as soon as the subsquare masses are almost surely positive. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The open square of half-side `s` centered at the origin. -/
def gmcOpenSquare (s : ℝ) : Set ℂ := {z | |z.re| < s ∧ |z.im| < s}

/-- One of the four half-size subsquares, with center `(σ₁ s/2, σ₂ s/2)`. -/
noncomputable def gmcSubSquare (s σ₁ σ₂ : ℝ) : Set ℂ :=
  (fun y => (⟨σ₁ * s / 2, σ₂ * s / 2⟩ : ℂ) + (1 / 2 : ℝ) • y) '' gmcOpenSquare s

theorem isOpen_gmcOpenSquare (s : ℝ) : IsOpen (gmcOpenSquare s) := by
  have h1 : IsOpen {z : ℂ | |z.re| < s} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
  have h2 : IsOpen {z : ℂ | |z.im| < s} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  exact h1.inter h2

theorem mem_gmcSubSquare_iff (s σ₁ σ₂ : ℝ) (z : ℂ) :
    z ∈ gmcSubSquare s σ₁ σ₂ ↔
      |z.re - σ₁ * s / 2| < s / 2 ∧ |z.im - σ₂ * s / 2| < s / 2 := by
  constructor
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.re_ofReal_mul,
      Complex.im_ofReal_mul]
    constructor
    · rw [show σ₁ * s / 2 + 1 / 2 * y.re - σ₁ * s / 2 = (1 / 2) * y.re by ring, abs_mul]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith
    · rw [show σ₂ * s / 2 + 1 / 2 * y.im - σ₂ * s / 2 = (1 / 2) * y.im by ring, abs_mul]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith
  · rintro ⟨h1, h2⟩
    refine ⟨⟨2 * (z.re - σ₁ * s / 2), 2 * (z.im - σ₂ * s / 2)⟩, ⟨?_, ?_⟩, ?_⟩
    · change |2 * (z.re - σ₁ * s / 2)| < s
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    · change |2 * (z.im - σ₂ * s / 2)| < s
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    · apply Complex.ext
      · simp only [Complex.add_re, Complex.real_smul, Complex.re_ofReal_mul]
        ring
      · simp only [Complex.add_im, Complex.real_smul, Complex.im_ofReal_mul]
        ring

theorem gmcSubSquare_subset (s : ℝ) {σ₁ σ₂ : ℝ} (h₁ : |σ₁| = 1) (h₂ : |σ₂| = 1) :
    gmcSubSquare s σ₁ σ₂ ⊆ gmcOpenSquare s := by
  intro z hz
  rw [mem_gmcSubSquare_iff] at hz
  obtain ⟨hz1, hz2⟩ := hz
  have hs : 0 < s := by
    have := abs_nonneg (z.re - σ₁ * s / 2)
    linarith
  have hr : |σ₁ * s / 2| = s / 2 := by
    rw [abs_div, abs_mul, h₁, abs_of_pos hs]; norm_num
  have hi : |σ₂ * s / 2| = s / 2 := by
    rw [abs_div, abs_mul, h₂, abs_of_pos hs]; norm_num
  constructor
  · calc |z.re| = |(z.re - σ₁ * s / 2) + σ₁ * s / 2| := by ring_nf
      _ ≤ |z.re - σ₁ * s / 2| + |σ₁ * s / 2| := abs_add_le _ _
      _ < s / 2 + s / 2 := by rw [hr]; linarith
      _ = s := by ring
  · calc |z.im| = |(z.im - σ₂ * s / 2) + σ₂ * s / 2| := by ring_nf
      _ ≤ |z.im - σ₂ * s / 2| + |σ₂ * s / 2| := abs_add_le _ _
      _ < s / 2 + s / 2 := by rw [hi]; linarith
      _ = s := by ring

/-- Two subsquares whose first sign differs are disjoint. -/
theorem gmcSubSquare_disjoint_re (s σ₂ τ₂ : ℝ) :
    Disjoint (gmcSubSquare s 1 σ₂) (gmcSubSquare s (-1) τ₂) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  rw [mem_gmcSubSquare_iff] at hz hz'
  have h1 := (abs_lt.mp hz.1)
  have h2 := (abs_lt.mp hz'.1)
  linarith

/-- Two subsquares whose second sign differs are disjoint. -/
theorem gmcSubSquare_disjoint_im (s σ₁ τ₁ : ℝ) :
    Disjoint (gmcSubSquare s σ₁ 1) (gmcSubSquare s τ₁ (-1)) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  rw [mem_gmcSubSquare_iff] at hz hz'
  have h1 := (abs_lt.mp hz.2)
  have h2 := (abs_lt.mp hz'.2)
  linarith

theorem gmcOpenSquare_subset_closedBall (s : ℝ) :
    gmcOpenSquare s ⊆ Metric.closedBall 0 (2 * s) := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have := Complex.norm_le_abs_re_add_abs_im z
  linarith [hz.1, hz.2]

theorem norm_gmcSubSquare_center (s : ℝ) (hs : 0 ≤ s) {σ₁ σ₂ : ℝ} (h₁ : |σ₁| = 1)
    (h₂ : |σ₂| = 1) : ‖(⟨σ₁ * s / 2, σ₂ * s / 2⟩ : ℂ)‖ ≤ s := by
  have := Complex.norm_le_abs_re_add_abs_im (⟨σ₁ * s / 2, σ₂ * s / 2⟩ : ℂ)
  simp only at this
  rw [abs_div, abs_mul, abs_div, abs_mul, h₁, h₂, abs_of_nonneg hs] at this
  norm_num at this
  linarith

/-- At the critical order the scaling factor of a half-size subsquare is `1/4`. -/
theorem gmc_critical_exponent_eq_two (γ : ℝ) (hγ : γ ≠ 0) :
    2 * (4 / γ ^ 2) + γ ^ 2 * (4 / γ ^ 2) / 2 - γ ^ 2 * (4 / γ ^ 2) ^ 2 / 2 = 2 := by
  field_simp
  ring

/-- The critical moment of a subsquare is one quarter of the critical moment of the square. -/
theorem gmc_subSquare_critical_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (s : ℝ) (hs : 0 < s) (hs2 : s < 1 / 4) {σ₁ σ₂ : ℝ} (h₁ : |σ₁| = 1) (h₂ : |σ₂| = 1) :
    gmcMassMoment P M (gmcSubSquare s σ₁ σ₂) (4 / γ ^ 2) =
      ENNReal.ofReal (1 / 4) * gmcMassMoment P M (gmcOpenSquare s) (4 / γ ^ 2) := by
  have h := gmc_affine_openSet_moment_scale P X hX γ hγ hγ2 M hM
    (a := (⟨σ₁ * s / 2, σ₂ * s / 2⟩ : ℂ)) (c := 1 / 2) (R := 2 * s) (by norm_num) (by norm_num)
    (by linarith) (by linarith)
    (by have := norm_gmcSubSquare_center s hs.le h₁ h₂; linarith)
    (gmcOpenSquare s) (isOpen_gmcOpenSquare s) (gmcOpenSquare_subset_closedBall s) (4 / γ ^ 2)
  rw [gmc_critical_exponent_eq_two γ hγ.ne'] at h
  rw [show ((1 : ℝ) / 2) ^ (2 : ℝ) = 1 / 4 by norm_num] at h
  exact h

/-- If the four subsquare masses are almost surely positive, the critical moment of the square
is infinite. -/
theorem gmc_openSquare_critical_moment_eq_top
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (s : ℝ) (hs : 0 < s) (hs2 : s < 1 / 4)
    (hpos : ∀ᵐ ω ∂P, 0 < M ω (gmcSubSquare s 1 1) ∧ 0 < M ω (gmcSubSquare s (-1) 1) ∧
      0 < M ω (gmcSubSquare s (-1) (-1)) ∧ 0 < M ω (gmcSubSquare s 1 (-1))) :
    gmcMassMoment P M (gmcOpenSquare s) (4 / γ ^ 2) = ⊤ := by
  let _ : IsProbabilityMeasure P := hX.1
  set p : ℝ := 4 / γ ^ 2 with hpdef
  have hp1 : 1 < p := by
    rw [hpdef, lt_div_iff₀ (by positivity)]
    nlinarith
  have hp0 : 0 ≤ p := by linarith
  set T₁ := gmcSubSquare s 1 1
  set T₂ := gmcSubSquare s (-1) 1
  set T₃ := gmcSubSquare s (-1) (-1)
  set T₄ := gmcSubSquare s 1 (-1)
  have habs1 : |(1 : ℝ)| = 1 := abs_one
  have habsm1 : |(-1 : ℝ)| = 1 := by norm_num
  have hTopen : ∀ σ₁ σ₂ : ℝ, IsOpen (gmcSubSquare s σ₁ σ₂) := by
    intro σ₁ σ₂
    have hset : gmcSubSquare s σ₁ σ₂ =
        {z : ℂ | |z.re - σ₁ * s / 2| < s / 2 ∧ |z.im - σ₂ * s / 2| < s / 2} := by
      ext z
      exact mem_gmcSubSquare_iff s σ₁ σ₂ z
    rw [hset]
    exact (isOpen_lt (continuous_abs.comp (Complex.continuous_re.sub continuous_const))
      continuous_const).inter (isOpen_lt (continuous_abs.comp
        (Complex.continuous_im.sub continuous_const)) continuous_const)
  have hTmeas : ∀ σ₁ σ₂ : ℝ, MeasurableSet (gmcSubSquare s σ₁ σ₂) :=
    fun σ₁ σ₂ => (hTopen σ₁ σ₂).measurableSet
  have hSmeas : MeasurableSet (gmcOpenSquare s) := (isOpen_gmcOpenSquare s).measurableSet
  -- the four subsquares are disjoint subsets of the square
  have d12 : Disjoint T₁ T₂ := gmcSubSquare_disjoint_re s 1 1
  have d13 : Disjoint T₁ T₃ := gmcSubSquare_disjoint_re s 1 (-1)
  have d14 : Disjoint T₁ T₄ := gmcSubSquare_disjoint_im s 1 1
  have d23 : Disjoint T₂ T₃ := gmcSubSquare_disjoint_im s (-1) (-1)
  have d24 : Disjoint T₂ T₄ := (gmcSubSquare_disjoint_re s (-1) 1).symm
  have d34 : Disjoint T₃ T₄ := (gmcSubSquare_disjoint_re s (-1) (-1)).symm
  have hunion_sub : T₁ ∪ T₂ ∪ T₃ ∪ T₄ ⊆ gmcOpenSquare s := by
    refine Set.union_subset (Set.union_subset (Set.union_subset ?_ ?_) ?_) ?_
    · exact gmcSubSquare_subset s habs1 habs1
    · exact gmcSubSquare_subset s habsm1 habs1
    · exact gmcSubSquare_subset s habsm1 habsm1
    · exact gmcSubSquare_subset s habs1 habsm1
  have hsum_le : ∀ ω, M ω T₁ + M ω T₂ + M ω T₃ + M ω T₄ ≤ M ω (gmcOpenSquare s) := by
    intro ω
    have h1 : M ω (T₁ ∪ T₂ ∪ T₃ ∪ T₄) = M ω T₁ + M ω T₂ + M ω T₃ + M ω T₄ := by
      rw [measure_union (Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨d14, d24⟩,
          d34⟩) (hTmeas 1 (-1)),
        measure_union (Set.disjoint_union_left.mpr ⟨d13, d23⟩) (hTmeas (-1) (-1)),
        measure_union d12 (hTmeas (-1) 1)]
    rw [← h1]
    exact measure_mono hunion_sub
  -- scaling of the critical moments
  have hscale : ∀ σ₁ σ₂ : ℝ, |σ₁| = 1 → |σ₂| = 1 →
      gmcMassMoment P M (gmcSubSquare s σ₁ σ₂) p =
        ENNReal.ofReal (1 / 4) * gmcMassMoment P M (gmcOpenSquare s) p :=
    fun σ₁ σ₂ h₁ h₂ => gmc_subSquare_critical_moment P X hX γ hγ hγ2 M hM s hs hs2 h₁ h₂
  by_contra hfin
  set E : ℝ≥0∞ := gmcMassMoment P M (gmcOpenSquare s) p with hEdef
  have hEfin : E ≠ ⊤ := hfin
  have hmeasT : ∀ σ₁ σ₂ : ℝ, AEMeasurable (fun ω => M ω (gmcSubSquare s σ₁ σ₂) ^ p) P :=
    fun σ₁ σ₂ => (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM _
      (hTmeas σ₁ σ₂)).pow_const p
  -- the sum of the four subsquare moments equals the square moment
  have hsumE : ∫⁻ ω, (M ω T₁ ^ p + M ω T₂ ^ p + M ω T₃ ^ p + M ω T₄ ^ p) ∂P = E := by
    rw [lintegral_add_right' _ (hmeasT 1 (-1)), lintegral_add_right' _ (hmeasT (-1) (-1)),
      lintegral_add_right' _ (hmeasT (-1) 1)]
    change gmcMassMoment P M T₁ p + gmcMassMoment P M T₂ p + gmcMassMoment P M T₃ p +
      gmcMassMoment P M T₄ p = E
    rw [hscale 1 1 habs1 habs1, hscale (-1) 1 habsm1 habs1, hscale (-1) (-1) habsm1 habsm1,
      hscale 1 (-1) habs1 habsm1, ← add_mul, ← add_mul, ← add_mul,
      ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  -- strict superadditivity on the almost sure event of positive subsquare masses
  have hstrict : ∀ᵐ ω ∂P, (M ω T₁ ^ p + M ω T₂ ^ p + M ω T₃ ^ p + M ω T₄ ^ p) <
      (M ω T₁ + M ω T₂ + M ω T₃ + M ω T₄) ^ p := by
    filter_upwards [hpos] with ω ⟨h1, h2, h3, h4⟩
    have hfinω : IsFiniteMeasure (M ω) := hM.1 ω
    have t1 : M ω T₁ ≠ ⊤ := measure_ne_top _ _
    have t2 : M ω T₂ ≠ ⊤ := measure_ne_top _ _
    have t3 : M ω T₃ ≠ ⊤ := measure_ne_top _ _
    have t4 : M ω T₄ ≠ ⊤ := measure_ne_top _ _
    have hreal := rpow_four_sum_gt_sum_of_pos (ENNReal.toReal_pos h1.ne' t1)
      (ENNReal.toReal_pos h2.ne' t2) (ENNReal.toReal_pos h3.ne' t3)
      (ENNReal.toReal_pos h4.ne' t4) hp1
    have hpowE : ∀ t : ℝ≥0∞, t ≠ ⊤ → t ^ p = ENNReal.ofReal (t.toReal ^ p) := by
      intro t ht
      rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp0, ENNReal.ofReal_toReal ht]
    have hsumtop : M ω T₁ + M ω T₂ + M ω T₃ + M ω T₄ ≠ ⊤ := by
      simp only [ne_eq, ENNReal.add_eq_top, not_or]
      exact ⟨⟨⟨t1, t2⟩, t3⟩, t4⟩
    have hsumreal : (M ω T₁ + M ω T₂ + M ω T₃ + M ω T₄).toReal =
        (M ω T₁).toReal + (M ω T₂).toReal + (M ω T₃).toReal + (M ω T₄).toReal := by
      rw [ENNReal.toReal_add (by simp only [ne_eq, ENNReal.add_eq_top, not_or]; exact
          ⟨⟨t1, t2⟩, t3⟩) t4,
        ENNReal.toReal_add (by simp only [ne_eq, ENNReal.add_eq_top, not_or]; exact ⟨t1, t2⟩) t3,
        ENNReal.toReal_add t1 t2]
    rw [hpowE _ t1, hpowE _ t2, hpowE _ t3, hpowE _ t4, hpowE _ hsumtop, hsumreal,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (by positivity) hreal)).mpr hreal
  have hgmeas : AEMeasurable (fun ω => (M ω T₁ + M ω T₂ + M ω T₃ + M ω T₄) ^ p) P := by
    have hm := fun σ₁ σ₂ => gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM _
      (hTmeas σ₁ σ₂)
    exact ((((hm 1 1).add (hm (-1) 1)).add (hm (-1) (-1))).add (hm 1 (-1))).pow_const p
  have hlt := lintegral_strict_mono (IsProbabilityMeasure.ne_zero P) hgmeas
    (by rw [hsumE]; exact hEfin) hstrict
  rw [hsumE] at hlt
  have hle : ∫⁻ ω, (M ω T₁ + M ω T₂ + M ω T₃ + M ω T₄) ^ p ∂P ≤ E := by
    apply lintegral_mono
    intro ω
    exact ENNReal.rpow_le_rpow (hsum_le ω) hp0
  exact (lt_irrefl E) (hlt.trans_le hle)

end DOZZ.Proofs
