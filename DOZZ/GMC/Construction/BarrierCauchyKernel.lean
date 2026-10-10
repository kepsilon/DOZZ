/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.BarrierCauchyMass

/-! The two-point kernel of growing-barrier good masses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- Wick-pair tilting with a finite family of coarse rectangle constraints left visible. The
coarse coordinates may be any selected coordinates of the jointly Gaussian family; this is the
finite-barrier identity used to compare mixed cutoffs. -/
theorem finite_gaussian_wick_pair_tilt_with_coarse_rectangle
    {Ω : Type*} [MeasurableSpace Ω] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Measure Ω) (V : Ω → ι → ℝ)
    (hV : IsCenteredJointlyGaussian P V) (p q : ι) (γ : ℝ)
    (e : κ → ι) (barrier : κ → ℝ) :
    let F : (ι → ℝ) → ℝ≥0∞ := fun z =>
      Set.indicator {z | ∀ i, z (e i) ≤ barrier i}
        (fun _ => (1 : ℝ≥0∞)) z
    ∫⁻ ω,
      ENNReal.ofReal (Real.exp (γ * V ω p - γ ^ 2 / 2 *
        gaussianVariance P (fun ω => V ω p))) *
      ENNReal.ofReal (Real.exp (γ * V ω q - γ ^ 2 / 2 *
        gaussianVariance P (fun ω => V ω q))) *
      F (V ω) ∂P =
    ENNReal.ofReal (Real.exp (γ ^ 2 / 2 *
      (gaussianCovariance P (fun ω => V ω p) (fun ω => V ω q) +
        gaussianCovariance P (fun ω => V ω q) (fun ω => V ω p)))) *
      (∫⁻ ω, F (fun i => V ω i + γ *
          gaussianCovariance P (fun ω => V ω i) (fun ω => V ω p) + γ *
          gaussianCovariance P (fun ω => V ω i) (fun ω => V ω q)) ∂P) := by
  classical
  let F : (ι → ℝ) → ℝ≥0∞ := fun z =>
    Set.indicator {z | ∀ i, z (e i) ≤ barrier i}
      (fun _ => (1 : ℝ≥0∞)) z
  have hEq : (⋂ i : κ, {z : ι → ℝ | z (e i) ≤ barrier i}) =
      {z | ∀ i : κ, z (e i) ≤ barrier i} := by
    ext z
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  have hset : MeasurableSet {z : ι → ℝ | ∀ i : κ, z (e i) ≤ barrier i} := by
    rw [← hEq]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (measurable_pi_apply (e i)) measurable_const
  have hF : Measurable F := by
    dsimp [F]
    exact measurable_const.indicator hset
  simpa [F] using finite_gaussian_wick_pair_tilt P V hV p q γ F hF


/-- Every finite Gaussian rectangle indicator has expectation between zero and one. -/
theorem integral_gaussianRectangleIndicator_abs_le_one
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : IsCenteredJointlyGaussian P Z)
    (barrier shift : ι → ℝ) :
    |∫ ω, gaussianRectangleIndicator Z barrier shift ω ∂P| ≤ 1 := by
  classical
  let R : Set (ι → ℝ) := {z | ∀ i, z i + shift i ≤ barrier i}
  have hR : MeasurableSet R := by
    have hEq : (⋂ i, {z : ι → ℝ | z i + shift i ≤ barrier i}) = R := by
      ext z
      simp [R]
    rw [← hEq]
    apply MeasurableSet.iInter
    intro i
    have hcoord : Measurable (fun z : ι → ℝ => z i + shift i) := by fun_prop
    exact measurableSet_le hcoord measurable_const
  have hZae : AEMeasurable Z P := by
    apply AEMeasurable.of_eval
    intro i
    exact hZ.2.1 i
  let F : (ι → ℝ) → ℝ := fun z => if z ∈ R then 1 else 0
  have hF : Measurable F := by
    dsimp [F]
    exact Measurable.ite hR measurable_const measurable_const
  have hEq : gaussianRectangleIndicator Z barrier shift = F ∘ Z := by
    funext ω
    simp [gaussianRectangleIndicator, F, R]
  have hRect : AEStronglyMeasurable (gaussianRectangleIndicator Z barrier shift) P := by
    rw [hEq]
    exact (hF.comp_aemeasurable hZae).aestronglyMeasurable
  have hbound : ∀ᵐ ω ∂P, ‖gaussianRectangleIndicator Z barrier shift ω‖ ≤ 1 := by
    apply ae_of_all
    intro ω
    dsimp [gaussianRectangleIndicator]
    split_ifs <;> norm_num
  have hPfinite : IsFiniteMeasure P := by
    refine ⟨?_⟩
    rw [hZ.1.measure_univ]
    exact ENNReal.one_lt_top
  have hone : Integrable (fun _ : Ω => (1 : ℝ)) P := by
    exact (integrable_const_iff (μ := P) (c := (1 : ℝ))).2 (Or.inr hPfinite)
  have hRectIntegrable : Integrable (gaussianRectangleIndicator Z barrier shift) P :=
    hone.mono' hRect hbound
  have hnorm := norm_integral_le_integral_norm (μ := P)
    (gaussianRectangleIndicator Z barrier shift)
  have hnormBound :
      (∫ ω, ‖gaussianRectangleIndicator Z barrier shift ω‖ ∂P) ≤ 1 := by
    calc
      _ ≤ ∫ ω, (1 : ℝ) ∂P :=
        integral_mono_ae hRectIntegrable.norm hone hbound
      _ = 1 := by
        rw [integral_const, Measure.real_def, hZ.1.measure_univ]
        norm_num
  have hnormResult : ‖∫ ω, gaussianRectangleIndicator Z barrier shift ω ∂P‖ ≤ 1 :=
    hnorm.trans hnormBound
  simpa [Real.norm_eq_abs] using hnormResult

/-- Uniform convergence of the Wick prefactor and the finite-barrier probability implies uniform
convergence of their mixed two-point product. The probability factors are bounded by one; only
the limiting Wick prefactor needs a uniform bound. -/
theorem tendsto_uniformlyOn_product_of_tendsto_uniformlyOn
    {α : Type*} (S : Set α) (M : ℝ) (hM : 0 ≤ M)
    (F F₀ G G₀ : ℝ → ℝ → α → ℝ)
    (hF : ∀ δ : ℝ, 0 < δ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ε' : ℝ,
      0 < ε → ε ≤ ε₀ → 0 < ε' → ε' ≤ ε₀ → ∀ p ∈ S,
        |F ε ε' p - F₀ 0 0 p| < δ)
    (hGcloseFam : ∀ δ : ℝ, 0 < δ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ε' : ℝ,
      0 < ε → ε ≤ ε₀ → 0 < ε' → ε' ≤ ε₀ → ∀ p ∈ S,
        |G ε ε' p - G₀ 0 0 p| < δ)
    (hF₀ : ∀ p ∈ S, |F₀ 0 0 p| ≤ M)
    (hG₀ : ∀ p ∈ S, |G₀ 0 0 p| ≤ 1)
    :
    ∀ η' : ℝ, 0 < η' → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ε' : ℝ,
      0 < ε → ε ≤ ε₀ → 0 < ε' → ε' ≤ ε₀ → ∀ p ∈ S,
        |F ε ε' p * G ε ε' p - F₀ 0 0 p * G₀ 0 0 p| < η' := by
  intro η' hη'
  let δ : ℝ := min 1 (η' / (4 * (M + 1)))
  have hδ : 0 < δ := lt_min one_pos (div_pos hη' (by positivity))
  have hδone : δ ≤ 1 := min_le_left _ _
  have hδsmall : δ ≤ η' / (4 * (M + 1)) := min_le_right _ _
  obtain ⟨εF, hεF, hFclose⟩ := hF δ hδ
  obtain ⟨εG, hεG, hGclose⟩ := hGcloseFam δ hδ
  let ε₀ : ℝ := min εF εG
  have hε₀ : 0 < ε₀ := lt_min hεF hεG
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε ε' hε hεcut hε' hε'cut p hp
  have hFc : |F ε ε' p - F₀ 0 0 p| < δ :=
    hFclose ε ε' hε (le_trans hεcut (min_le_left _ _)) hε'
      (le_trans hε'cut (min_le_left _ _)) p hp
  have hGc : |G ε ε' p - G₀ 0 0 p| < δ :=
    hGclose ε ε' hε (le_trans hεcut (min_le_right _ _)) hε'
      (le_trans hε'cut (min_le_right _ _)) p hp
  have hFbound : |F ε ε' p| ≤ M + δ := by
    calc
      |F ε ε' p| = |(F ε ε' p - F₀ 0 0 p) + F₀ 0 0 p| := by
        congr 1
        ring
      _ ≤ |F ε ε' p - F₀ 0 0 p| + |F₀ 0 0 p| := abs_add_le _ _
      _ ≤ δ + M := add_le_add hFc.le (hF₀ p hp)
      _ = M + δ := by ring
  have hprod :
      |F ε ε' p * G ε ε' p - F₀ 0 0 p * G₀ 0 0 p| ≤
        (M + δ) * δ + δ := by
    calc
      _ = |F ε ε' p * (G ε ε' p - G₀ 0 0 p) +
            (F ε ε' p - F₀ 0 0 p) * G₀ 0 0 p| := by
              congr 1
              ring
      _ ≤ |F ε ε' p| * |G ε ε' p - G₀ 0 0 p| +
            |F ε ε' p - F₀ 0 0 p| * |G₀ 0 0 p| := by
              calc
                _ ≤ |F ε ε' p * (G ε ε' p - G₀ 0 0 p)| +
                    |(F ε ε' p - F₀ 0 0 p) * G₀ 0 0 p| := abs_add_le _ _
                _ = _ := by rw [abs_mul, abs_mul]
      _ ≤ (M + δ) * δ + δ := by
        apply add_le_add
        · exact mul_le_mul (hFbound) hGc.le (abs_nonneg _) (by positivity)
        · calc
            |F ε ε' p - F₀ 0 0 p| * |G₀ 0 0 p| ≤ δ * 1 :=
              mul_le_mul hFc.le (hG₀ p hp) (abs_nonneg _) (by positivity)
            _ = δ := by ring
  have hsmall : (M + δ) * δ + δ < η' := by
    have hMd : M * δ ≤ η' / 4 := by
      calc
        M * δ ≤ M * (η' / (4 * (M + 1))) :=
          mul_le_mul_of_nonneg_left hδsmall hM
        _ = η' * (M / (4 * (M + 1))) := by ring
        _ ≤ η' * (1 / 4) := by
          apply mul_le_mul_of_nonneg_left _ hη'.le
          apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (M + 1))
            (by norm_num : (0 : ℝ) < 4)).2
          nlinarith [hM]
        _ = η' / 4 := by ring
    have hδsmall' : δ ≤ η' / 4 := by
      calc
        δ ≤ η' / (4 * (M + 1)) := hδsmall
        _ ≤ η' / 4 := by
          apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (M + 1))
            (by norm_num : (0 : ℝ) < 4)).2
          nlinarith [hM, hη']
    have hδsq : δ ^ 2 ≤ δ := by nlinarith [hδone, sq_nonneg (δ - 1)]
    nlinarith [hMd, hδsmall', hδsq]
  exact lt_of_le_of_lt hprod hsmall

/-- One regularized Gaussian Wick weight, in nonnegative form for Tonelli arguments. -/
noncomputable def admissibleLogWickWeight
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ → ℂ → ℝ) (γ ε : ℝ) (x : ℂ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp
    (γ * Y ω ε x - γ ^ 2 / 2 * gaussianVariance P (fun ω' => Y ω' ε x)))

/-- Mixed two-root Wick kernel with the growing barrier imposed at each root. -/
noncomputable def compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (Y Z : Ω → ℝ → ℂ → ℝ) (γ a : ℝ) (k₀ : ℕ)
    (r s : ℝ) (x y : ℂ) (b₁ b₂ : Bool) : ℝ≥0∞ := by
  classical
  exact ∫⁻ ω,
    admissibleLogWickWeight P (if b₁ then Y else Z) γ (Real.exp (-r)) x ω *
    admissibleLogWickWeight P (if b₂ then Y else Z) γ (Real.exp (-s)) y ω *
    Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)
      (fun _ => (1 : ℝ≥0∞)) (ω, x) *
    Set.indicator (admissibleGrowingBarrierSet Y a k₀ s)
      (fun _ => (1 : ℝ≥0∞)) (ω, y) ∂P


/-- The mixed Wick kernel with both growing barriers truncated at the fixed integer level `m`.
This is the finite-dimensional approximation used on separated spatial slices. -/
noncomputable def compatibleAdmissibleSelectedFiniteBarrierPairKernel
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y Z : Ω → ℝ → ℂ → ℝ) (γ a : ℝ) (k₀ m : ℕ)
    (ε δ : ℝ) (x y : ℂ) (b₁ b₂ : Bool) : ℝ≥0∞ := by
  classical
  exact ∫⁻ ω,
    admissibleLogWickWeight P (if b₁ then Y else Z) γ ε x ω *
    admissibleLogWickWeight P (if b₂ then Y else Z) γ δ y ω *
    Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ))
      (fun _ => (1 : ℝ≥0∞)) (ω, x) *
    Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ))
      (fun _ => (1 : ℝ≥0∞)) (ω, y) ∂P

/-- Once both cutoffs include every scale through `m`, the full growing-barrier kernel is
dominated by its finite-barrier truncation. -/
theorem compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel_le_finiteBarrier
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y Z : Ω → ℝ → ℂ → ℝ) (γ a : ℝ) (k₀ m : ℕ)
    (r s : ℝ) (x y : ℂ) (b₁ b₂ : Bool)
    (hmr : (m : ℝ) ≤ r) (hms : (m : ℝ) ≤ s) :
    compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel P Y Z γ a k₀ r s x y b₁ b₂ ≤
      compatibleAdmissibleSelectedFiniteBarrierPairKernel P Y Z γ a k₀ m
        (Real.exp (-r)) (Real.exp (-s)) x y b₁ b₂ := by
  classical
  have hsubset (t : ℝ) (hmt : (m : ℝ) ≤ t) (ω : Ω) (z : ℂ) :
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ t)
          (fun _ => (1 : ℝ≥0∞)) (ω, z) ≤
        Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ))
          (fun _ => (1 : ℝ≥0∞)) (ω, z) := by
    by_cases hgood : (ω, z) ∈ admissibleGrowingBarrierSet Y a k₀ t
    · have hsmall : (ω, z) ∈ admissibleGrowingBarrierSet Y a k₀ (m : ℝ) := by
        intro k hk₀ hkm
        have hkt : (k : ℝ) ≤ t := le_trans hkm hmt
        exact hgood k hk₀ hkt
      simp [Set.indicator, hgood, hsmall]
    · simp [Set.indicator, hgood]
  unfold compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel
    compatibleAdmissibleSelectedFiniteBarrierPairKernel
  apply lintegral_mono
  intro ω
  let w₁ := admissibleLogWickWeight P (if b₁ then Y else Z) γ (Real.exp (-r)) x ω
  let w₂ := admissibleLogWickWeight P (if b₂ then Y else Z) γ (Real.exp (-s)) y ω
  change w₁ * w₂ *
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)
        (fun _ => (1 : ℝ≥0∞)) (ω, x) *
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ s)
        (fun _ => (1 : ℝ≥0∞)) (ω, y) ≤
    w₁ * w₂ * Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ))
      (fun _ => (1 : ℝ≥0∞)) (ω, x) *
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ))
        (fun _ => (1 : ℝ≥0∞)) (ω, y)
  have hbarrierProduct :
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)
          (fun _ => (1 : ℝ≥0∞)) (ω, x) *
        Set.indicator (admissibleGrowingBarrierSet Y a k₀ s)
          (fun _ => (1 : ℝ≥0∞)) (ω, y) ≤
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ))
          (fun _ => (1 : ℝ≥0∞)) (ω, x) *
        Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ))
          (fun _ => (1 : ℝ≥0∞)) (ω, y) := by
    calc
      _ = Set.indicator (admissibleGrowingBarrierSet Y a k₀ s)
            (fun _ => (1 : ℝ≥0∞)) (ω, y) *
          Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)
            (fun _ => (1 : ℝ≥0∞)) (ω, x) := mul_comm _ _
      _ ≤ Set.indicator (admissibleGrowingBarrierSet Y a k₀ s)
            (fun _ => (1 : ℝ≥0∞)) (ω, y) *
          Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ))
            (fun _ => (1 : ℝ≥0∞)) (ω, x) :=
          mul_le_mul_of_nonneg_left (hsubset r hmr ω x) (by positivity)
      _ = _ := mul_comm _ _
      _ ≤ Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ))
            (fun _ => (1 : ℝ≥0∞)) (ω, x) *
          Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ))
            (fun _ => (1 : ℝ≥0∞)) (ω, y) :=
          mul_le_mul_of_nonneg_left (hsubset s hms ω y) (by positivity)
  calc
    _ = (Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)
          (fun _ => (1 : ℝ≥0∞)) (ω, x) *
        Set.indicator (admissibleGrowingBarrierSet Y a k₀ s)
          (fun _ => (1 : ℝ≥0∞)) (ω, y)) * (w₁ * w₂) := by ac_rfl
    _ ≤ (Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ))
          (fun _ => (1 : ℝ≥0∞)) (ω, x) *
        Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ))
          (fun _ => (1 : ℝ≥0∞)) (ω, y)) * (w₁ * w₂) :=
      mul_le_mul_left hbarrierProduct (w₁ * w₂)
    _ = _ := by ac_rfl



end DOZZ.Proofs
