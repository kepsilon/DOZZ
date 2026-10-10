/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.GMCGeneralTiltRawCutoff
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.FactorsThrough

/-! Raw-measurable proxies for a countable determining family of GMC masses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set MeasurableSpace
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

noncomputable section

/-- The rational lower rectangle used to determine finite measures on the plane. -/
def gmcLowerBox (i : ℚ × ℚ) : Set ℂ :=
  Complex.measurableEquivRealProd ⁻¹' (Set.Iic (i.1 : ℝ) ×ˢ Set.Iic (i.2 : ℝ))

/-- Rational lower boxes are measurable in the standard Borel structure on the plane. -/
theorem gmcLowerBox_measurableSet (i : ℚ × ℚ) : MeasurableSet (gmcLowerBox i) := by
  change MeasurableSet
    (Complex.measurableEquivRealProd ⁻¹' (Set.Iic (i.1 : ℝ) ×ˢ Set.Iic (i.2 : ℝ)))
  exact Complex.measurableEquivRealProd.measurable
    (MeasurableSet.prod measurableSet_Iic measurableSet_Iic)

/-- One-dimensional continuous ramps for rational lower intervals. -/
def gmcLowerApprox (q : ℚ) (n : ℕ) (x : ℝ) : ℝ :=
  max 0 (min 1 (1 - (n : ℝ) * (x - q)))

/-- The rational lower-interval ramps are continuous. -/
theorem gmcLowerApprox_continuous (q : ℚ) (n : ℕ) :
    Continuous (gmcLowerApprox q n) := by
  change Continuous (fun x : ℝ => max 0 (min 1 (1 - (n : ℝ) * (x - q))))
  fun_prop

/-- The rational lower-interval ramps take values in `[0,1]`. -/
theorem gmcLowerApprox_bounds (q : ℚ) (n : ℕ) (x : ℝ) :
    0 ≤ gmcLowerApprox q n x ∧ gmcLowerApprox q n x ≤ 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le_iff.mpr ⟨by norm_num, min_le_left _ _⟩

/-- Pointwise convergence of the rational lower-interval ramps. -/
theorem gmcLowerApprox_tendsto (q : ℚ) (x : ℝ) :
    Tendsto (fun n : ℕ => gmcLowerApprox q n x) atTop
      (𝓝 (if x ≤ (q : ℝ) then 1 else 0)) := by
  by_cases hx : x ≤ (q : ℝ)
  · have heq : ∀ n, gmcLowerApprox q n x = 1 := by
      intro n
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hxq : x - (q : ℝ) ≤ 0 := sub_nonpos.mpr hx
      have harg : 1 ≤ 1 - (n : ℝ) * (x - q) := by nlinarith [mul_nonpos_of_nonneg_of_nonpos hn hxq]
      simp [gmcLowerApprox, min_eq_left harg]
    simp [hx, heq]
  · have hpos : 0 < x - (q : ℝ) := sub_pos.mpr (lt_of_not_ge hx)
    have hqx : (q : ℝ) < x := lt_of_not_ge hx
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (x - (q : ℝ)))
    have heventually : (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop] fun n => gmcLowerApprox q n x := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hNn : 1 / (x - (q : ℝ)) < (n : ℝ) := by exact lt_of_lt_of_le hN (by exact_mod_cast hn)
      have hprod : 1 ≤ (n : ℝ) * (x - (q : ℝ)) := by
        have := (div_lt_iff₀ hpos).mp hNn
        nlinarith
      have harg : 1 - (n : ℝ) * (x - (q : ℝ)) ≤ 0 := by linarith
      have hmin : min 1 (1 - (n : ℝ) * (x - (q : ℝ))) ≤ 0 :=
        le_trans (min_le_right _ _) harg
      simp [gmcLowerApprox, max_eq_left hmin]
    have hT : Tendsto (fun n : ℕ => gmcLowerApprox q n x) atTop (𝓝 0) :=
      Tendsto.congr' heventually tendsto_const_nhds
    convert hT using 1
    simp [not_le_of_gt hqx]

/-- The pointwise product form of the lower-box approximant. -/
def gmcLowerBoxApproxFun (i : ℚ × ℚ) (n : ℕ) (z : ℂ) : ℝ :=
  gmcLowerApprox i.1 n z.re * gmcLowerApprox i.2 n z.im

/-- Continuity of the pointwise lower-box approximant. -/
theorem gmcLowerBoxApproxFun_continuous (i : ℚ × ℚ) (n : ℕ) :
    Continuous (gmcLowerBoxApproxFun i n) := by
  exact ((gmcLowerApprox_continuous i.1 n).comp Complex.continuous_re).mul
    ((gmcLowerApprox_continuous i.2 n).comp Complex.continuous_im)

/-- Bounds for the continuous lower-box approximants. -/
theorem gmcLowerBoxApprox_bounds (i : ℚ × ℚ) (n : ℕ) (z : ℂ) :
    0 ≤ gmcLowerBoxApproxFun i n z ∧ gmcLowerBoxApproxFun i n z ≤ 1 := by
  have h₁ := gmcLowerApprox_bounds i.1 n z.re
  have h₂ := gmcLowerApprox_bounds i.2 n z.im
  constructor
  · exact mul_nonneg h₁.1 h₂.1
  · calc
      gmcLowerApprox i.1 n z.re * gmcLowerApprox i.2 n z.im ≤
          1 * gmcLowerApprox i.2 n z.im := mul_le_mul_of_nonneg_right h₁.2 h₂.1
      _ ≤ 1 := by simpa using h₂.2

/-- Continuous bounded approximants to a rational lower box. They converge pointwise to its
indicator and stay between zero and one. -/
def gmcLowerBoxApprox (i : ℚ × ℚ) (n : ℕ) : BoundedContinuousFunction ℂ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨gmcLowerBoxApproxFun i n, gmcLowerBoxApproxFun_continuous i n⟩
    1 (by
      intro z w
      have hz := gmcLowerBoxApprox_bounds i n z
      have hw := gmcLowerBoxApprox_bounds i n w
      change dist (gmcLowerBoxApproxFun i n z) (gmcLowerBoxApproxFun i n w) ≤ 1
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith)

/-- Pointwise convergence of the continuous lower-box approximants. -/
theorem gmcLowerBoxApprox_tendsto (i : ℚ × ℚ) (z : ℂ) :
    Tendsto (fun n : ℕ => gmcLowerBoxApprox i n z) atTop
      (𝓝 ((gmcLowerBox i).indicator (fun _ => (1 : ℝ)) z)) := by
  have hreal := gmcLowerApprox_tendsto i.1 z.re
  have himag := gmcLowerApprox_tendsto i.2 z.im
  have hmul := hreal.mul himag
  convert hmul using 1
  · rfl
  · by_cases hr : z.re ≤ (i.1 : ℝ) <;> by_cases hi : z.im ≤ (i.2 : ℝ) <;>
      simp [gmcLowerBox, Complex.measurableEquivRealProd_apply, Set.indicator, hr, hi]

/-- Under any finite measure, the integrals of the lower-box approximants converge to its box
mass. -/
theorem gmcLowerBoxApprox_integral_tendsto (i : ℚ × ℚ)
    (μ : Measure ℂ) [IsFiniteMeasure μ] :
    Tendsto (fun n : ℕ => ∫ z, gmcLowerBoxApprox i n z ∂μ) atTop
      (𝓝 (μ.real (gmcLowerBox i))) := by
  have hbound : Integrable (fun _ : ℂ => (1 : ℝ)) μ := integrable_const 1
  have hdom : ∀ n, ∀ᵐ z ∂μ, ‖gmcLowerBoxApprox i n z‖ ≤ (1 : ℝ) := by
    intro n
    filter_upwards [] with z
    have hz := gmcLowerBoxApprox_bounds i n z
    change |gmcLowerBoxApproxFun i n z| ≤ 1
    rw [abs_le]
    exact ⟨by linarith, hz.2⟩
  have hlim : ∀ᵐ z ∂μ,
      Tendsto (fun n : ℕ => gmcLowerBoxApprox i n z) atTop
        (𝓝 ((gmcLowerBox i).indicator (fun _ => (1 : ℝ)) z)) :=
    ae_of_all _ (gmcLowerBoxApprox_tendsto i)
  have hs : MeasurableSet (gmcLowerBox i) := by
    change MeasurableSet
      (Complex.measurableEquivRealProd ⁻¹' (Set.Iic (i.1 : ℝ) ×ˢ Set.Iic (i.2 : ℝ)))
    exact Complex.measurableEquivRealProd.measurable
      (MeasurableSet.prod measurableSet_Iic measurableSet_Iic)
  have hdomconv := tendsto_integral_of_dominated_convergence
    (fun _ : ℂ => (1 : ℝ))
    (fun n => (gmcLowerBoxApprox i n).continuous.measurable.aestronglyMeasurable)
    hbound hdom hlim
  rw [← integral_indicator_one hs]
  exact hdomconv

/-- The mass on a rational lower rectangle has a raw-measurable real proxy. -/
theorem equatorGFF_GMC_lowerBox_realMass_raw_version
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (i : ℚ × ℚ) :
    ∃ g : Ω → ℝ,
      Measurable[equatorGFFRawDistributionSigma X] g ∧
      (fun ω => (M ω (gmcLowerBox i)).toReal) =ᵐ[P] g := by
  have hseq : ∀ n, ∃ g : Ω → ℝ,
      Measurable[equatorGFFRawDistributionSigma X] g ∧
      (fun ω => ∫ z, gmcLowerBoxApprox i n z ∂M ω) =ᵐ[P] g := by
    intro n
    exact equatorGFF_GMC_testIntegral_raw_measurable_version_of_IsGMCOf
      P X hX γ M hM (gmcLowerBoxApprox i n)
  choose g hgmeas hgae using hseq
  let gLim : Ω → ℝ := fun ω => limUnder atTop (fun n => g n ω)
  have hgLim : Measurable[equatorGFFRawDistributionSigma X] gLim := by
    let : MeasurableSpace Ω := equatorGFFRawDistributionSigma X
    exact (StronglyMeasurable.limUnder (l := atTop)
      (fun n => (hgmeas n).stronglyMeasurable)).measurable
  have hAEproxy : ∀ᵐ ω ∂P, ∀ n,
      (∫ z, gmcLowerBoxApprox i n z ∂M ω) = g n ω := ae_all_iff.mpr hgae
  have hEq : (fun ω => (M ω (gmcLowerBox i)).toReal) =ᵐ[P] gLim := by
    filter_upwards [hAEproxy] with ω hω
    have hT : Tendsto (fun n => g n ω) atTop
        (𝓝 ((M ω (gmcLowerBox i)).toReal)) := by
      have hfinite : IsFiniteMeasure (M ω) := hM.1 ω
      exact (Filter.Tendsto.congr' (Filter.Eventually.of_forall hω)
        (gmcLowerBoxApprox_integral_tendsto i (M ω)))
    change (M ω (gmcLowerBox i)).toReal = limUnder atTop (fun n => g n ω)
    exact hT.limUnder_eq.symm
  exact ⟨gLim, hgLim, hEq⟩

/-- A rational lower-box mass of an `IsGMCOf` limit factors measurably through the field. -/
theorem equatorGFF_GMC_lowerBox_realMass_field_factor
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (i : ℚ × ℚ) :
    ∃ g : (TestFn → ℝ) → ℝ, Measurable g ∧
      (fun ω => (M ω (gmcLowerBox i)).toReal) =ᵐ[P]
        (fun ω => g (fun f => X ω f)) := by
  obtain ⟨gΩ, hgΩ, hEq⟩ := equatorGFF_GMC_lowerBox_realMass_raw_version P X hX γ M hM i
  let eval : Ω → TestFn → ℝ := fun ω f => X ω f
  have hgComap : Measurable[(MeasurableSpace.pi).comap eval] gΩ := by
    change Measurable[equatorGFFRawDistributionSigma X] gΩ at hgΩ
    simpa [equatorGFFRawDistributionSigma, eval] using hgΩ
  obtain ⟨g, hg, hFactor⟩ := hgComap.exists_eq_measurable_comp
  refine ⟨g, hg, ?_⟩
  filter_upwards [hEq] with ω hω
  rw [hFactor] at hω
  exact hω

/-- Coordinates that determine a finite measure on the plane. `none` records its total mass. -/
def gmcFiniteMeasureEval (μ : FiniteMeasure ℂ) : Option (ℚ × ℚ) → ℝ≥0∞ :=
  fun i => (μ : Measure ℂ) (match i with | none => Set.univ | some j => gmcLowerBox j)

private def gmcRatLowerIntervals : Set (Set ℝ) :=
  ⋃ q : ℚ, {Set.Iic (q : ℝ)}

private theorem gmcRatLowerIntervals_spanning : IsCountablySpanning gmcRatLowerIntervals := by
  refine ⟨fun n => Set.Iic (n : ℝ), ?_, ?_⟩
  · intro n
    exact Set.mem_iUnion.mpr ⟨(n : ℚ), Set.mem_singleton _⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt x
    exact ⟨n, le_of_lt hn⟩

private def gmcRatLowerRectangles : Set (Set (ℝ × ℝ)) :=
  Set.image2 (fun s t : Set ℝ => s ×ˢ t) gmcRatLowerIntervals gmcRatLowerIntervals

private theorem gmcRatLowerRectangles_generate :
    generateFrom gmcRatLowerRectangles = borel (ℝ × ℝ) := by
  have hreal : generateFrom gmcRatLowerIntervals = borel ℝ :=
    Real.borel_eq_generateFrom_Iic_rat.symm
  have hprod := generateFrom_eq_prod hreal hreal
    gmcRatLowerIntervals_spanning gmcRatLowerIntervals_spanning
  simpa only [gmcRatLowerRectangles, BorelSpace.measurable_eq] using hprod

private theorem gmcRatLowerRectangles_pi : IsPiSystem gmcRatLowerRectangles :=
  (Real.isPiSystem_Iic_rat).prod Real.isPiSystem_Iic_rat

private def gmcLowerBoxFamily : Set (Set ℂ) :=
  {s | ∃ t ∈ gmcRatLowerRectangles, Complex.measurableEquivRealProd ⁻¹' t = s}

private theorem gmcLowerBoxFamily_representation {s : Set ℂ} (hs : s ∈ gmcLowerBoxFamily) :
    ∃ i : ℚ × ℚ, gmcLowerBox i = s := by
  rcases hs with ⟨t, ht, rfl⟩
  change t ∈ Set.image2 (fun a b : Set ℝ => a ×ˢ b) gmcRatLowerIntervals gmcRatLowerIntervals at ht
  rcases Set.mem_image2.mp ht with ⟨a, ha, b, hb, rfl⟩
  rcases Set.mem_iUnion.mp ha with ⟨p, hp⟩
  rcases Set.mem_iUnion.mp hb with ⟨q, hq⟩
  simp only [Set.mem_singleton_iff] at hp hq
  subst a
  subst b
  exact ⟨(p, q), rfl⟩

private theorem gmcLowerBoxFamily_generate : generateFrom gmcLowerBoxFamily = borel ℂ := by
  calc
    generateFrom gmcLowerBoxFamily =
        MeasurableSpace.comap Complex.measurableEquivRealProd
          (generateFrom gmcRatLowerRectangles) := by
            rw [MeasurableSpace.comap_generateFrom]
            rfl
    _ = MeasurableSpace.comap Complex.measurableEquivRealProd (borel (ℝ × ℝ)) := by
          rw [gmcRatLowerRectangles_generate]
    _ = borel ℂ := by
          simpa only [BorelSpace.measurable_eq] using
            Complex.measurableEquivRealProd.measurableEmbedding.comap_eq

private theorem gmcLowerBoxFamily_pi : IsPiSystem gmcLowerBoxFamily :=
  gmcRatLowerRectangles_pi.comap Complex.measurableEquivRealProd

private def gmcBasisSet : Option (ℚ × ℚ) → Set ℂ
  | none => Set.univ
  | some i => gmcLowerBox i

private def gmcBasisFamily : Set (Set ℂ) := Set.range gmcBasisSet

private theorem gmcBasisFamily_eq :
    gmcBasisFamily = insert Set.univ gmcLowerBoxFamily := by
  ext s
  constructor
  · rintro ⟨i, rfl⟩
    cases i with
    | none => simp [gmcBasisSet]
    | some i =>
      right
      exact ⟨Set.Iic (i.1 : ℝ) ×ˢ Set.Iic (i.2 : ℝ), by
        exact Set.mem_image2_of_mem
          (Set.mem_iUnion.mpr ⟨i.1, Set.mem_singleton _⟩)
          (Set.mem_iUnion.mpr ⟨i.2, Set.mem_singleton _⟩), rfl⟩
  · intro hs
    rcases hs with hs | hs
    · subst s
      exact ⟨none, rfl⟩
    · obtain ⟨i, hi⟩ := gmcLowerBoxFamily_representation hs
      exact ⟨some i, hi⟩

private theorem gmcBasisFamily_pi : IsPiSystem gmcBasisFamily := by
  rw [gmcBasisFamily_eq]
  exact IsPiSystem.insert_univ gmcLowerBoxFamily_pi

private theorem gmcBasisFamily_generate : generateFrom gmcBasisFamily = borel ℂ := by
  rw [gmcBasisFamily_eq]
  apply le_antisymm
  · apply generateFrom_le
    intro s hs
    rcases hs with hs | hs
    · subst s
      exact MeasurableSet.univ
    · have hgen := gmcLowerBoxFamily_generate
      exact hgen ▸ GenerateMeasurable.basic s hs
  · rw [← gmcLowerBoxFamily_generate]
    exact generateFrom_mono (Set.subset_insert _ _)

/-- The finite-measure Giry sigma algebra is generated by total mass and lower-box masses. -/
theorem gmcFiniteMeasure_sigma_eq :
    (inferInstance : MeasurableSpace (FiniteMeasure ℂ)) =
      MeasurableSpace.comap gmcFiniteMeasureEval MeasurableSpace.pi := by
  classical
  let mFin : MeasurableSpace (FiniteMeasure ℂ) := inferInstance
  let mCoord : MeasurableSpace (Option (ℚ × ℚ) → ℝ≥0∞) := MeasurableSpace.pi
  let mBasis : MeasurableSpace (FiniteMeasure ℂ) :=
    MeasurableSpace.comap gmcFiniteMeasureEval mCoord
  have hcoe : @Measurable (FiniteMeasure ℂ) (Measure ℂ) mBasis _
      (fun μ => (μ : Measure ℂ)) := by
    apply Measurable.measure_of_isPiSystem (μ := fun μ : FiniteMeasure ℂ => (μ : Measure ℂ))
      (hgen := by simpa only [BorelSpace.measurable_eq] using gmcBasisFamily_generate.symm)
      (hpi := gmcBasisFamily_pi)
    · intro s hs
      rcases hs with ⟨i, rfl⟩
      have hE : @Measurable (FiniteMeasure ℂ) (Option (ℚ × ℚ) → ℝ≥0∞) mBasis mCoord
          gmcFiniteMeasureEval := Measurable.of_comap_le le_rfl
      have hEval : @Measurable (FiniteMeasure ℂ) ℝ≥0∞ mBasis _
          (fun μ => gmcFiniteMeasureEval μ i) :=
        (measurable_pi_apply i).comp hE
      simpa [gmcFiniteMeasureEval, gmcBasisSet] using hEval
    · have hE : @Measurable (FiniteMeasure ℂ) (Option (ℚ × ℚ) → ℝ≥0∞) mBasis mCoord
        gmcFiniteMeasureEval := Measurable.of_comap_le le_rfl
      have hEval : @Measurable (FiniteMeasure ℂ) ℝ≥0∞ mBasis _
          (fun μ => gmcFiniteMeasureEval μ none) :=
        (measurable_pi_apply none).comp hE
      simpa [gmcFiniteMeasureEval, gmcBasisSet] using hEval
  have hsub : mFin =
      MeasurableSpace.comap (fun μ : FiniteMeasure ℂ => (μ : Measure ℂ))
        (inferInstance : MeasurableSpace (Measure ℂ)) := rfl
  have hle₁ : mFin ≤ mBasis := by
    rw [hsub]
    exact hcoe.comap_le
  have hcoord : @Measurable (FiniteMeasure ℂ) (Option (ℚ × ℚ) → ℝ≥0∞) mFin mCoord
      gmcFiniteMeasureEval := by
    apply Measurable.of_comap_le
    change MeasurableSpace.comap gmcFiniteMeasureEval MeasurableSpace.pi ≤ mFin
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    apply iSup_le
    intro i
    have hEval : @Measurable (FiniteMeasure ℂ) ℝ≥0∞ mFin _
        (fun μ => gmcFiniteMeasureEval μ i) := by
      have hA : MeasurableSet
          (match i with | none => Set.univ | some j => gmcLowerBox j) := by
        cases i with
        | none => exact MeasurableSet.univ
        | some j =>
          change MeasurableSet
            (Complex.measurableEquivRealProd ⁻¹'
              (Set.Iic (j.1 : ℝ) ×ˢ Set.Iic (j.2 : ℝ)))
          exact Complex.measurableEquivRealProd.measurable
            (MeasurableSet.prod measurableSet_Iic measurableSet_Iic)
      exact (MeasureTheory.Measure.measurable_coe hA).comp
        (show @Measurable (FiniteMeasure ℂ) (Measure ℂ) mFin _
          (fun μ => (μ : Measure ℂ)) from measurable_subtype_coe)
    rw [MeasurableSpace.comap_comp]
    exact hEval.comap_le
  have hle₂ : mBasis ≤ mFin := by
    change MeasurableSpace.comap gmcFiniteMeasureEval mCoord ≤ mFin
    exact hcoord.comap_le
  exact le_antisymm hle₁ hle₂

/-- The joint coordinate map remembers both a test-field configuration and a finite measure. -/
def gmcJointFiniteEval :
    ((TestFn → ℝ) × FiniteMeasure ℂ) →
      (TestFn → ℝ) × (Option (ℚ × ℚ) → ℝ≥0∞) :=
  fun p => (p.1, gmcFiniteMeasureEval p.2)

/-- A measurable functional of a field and a finite measure depends measurably on the field and
the countable determining coordinates of that measure. -/
theorem gmc_measurable_function_factors_through_finite_eval
    (H : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun p : (TestFn → ℝ) × Measure ℂ => H p.1 p.2)) :
    ∃ G : (TestFn → ℝ) × (Option (ℚ × ℚ) → ℝ≥0∞) → ℝ≥0∞,
      Measurable G ∧
      (fun p : (TestFn → ℝ) × FiniteMeasure ℂ => H p.1 (p.2 : Measure ℂ)) =
        fun p => G (gmcJointFiniteEval p) := by
  let mQ : MeasurableSpace (TestFn → ℝ) := MeasurableSpace.pi
  let mFM : MeasurableSpace (FiniteMeasure ℂ) := inferInstance
  let mCoord : MeasurableSpace (Option (ℚ × ℚ) → ℝ≥0∞) := MeasurableSpace.pi
  let mTarget : MeasurableSpace
      ((TestFn → ℝ) × (Option (ℚ × ℚ) → ℝ≥0∞)) := mQ.prod mCoord
  have hSigma :
      MeasurableSpace.comap gmcJointFiniteEval mTarget = mQ.prod mFM := by
    rw [MeasurableSpace.comap_prodMk, MeasurableSpace.prod]
    rw [show mFM = MeasurableSpace.comap gmcFiniteMeasureEval mCoord from by
      simpa [mFM, mCoord] using gmcFiniteMeasure_sigma_eq]
    rw [MeasurableSpace.comap_comp]
    rfl
  have hInput : Measurable
      (fun p : (TestFn → ℝ) × FiniteMeasure ℂ => (p.1, (p.2 : Measure ℂ))) := by
    exact Measurable.prodMk measurable_fst
      (measurable_subtype_coe.comp measurable_snd)
  have hPull : Measurable
      (fun p : (TestFn → ℝ) × FiniteMeasure ℂ => H p.1 (p.2 : Measure ℂ)) :=
    hH.comp hInput
  have hPull' : @Measurable ((TestFn → ℝ) × FiniteMeasure ℂ) ℝ≥0∞
      (MeasurableSpace.comap gmcJointFiniteEval mTarget) _
      (fun p => H p.1 (p.2 : Measure ℂ)) := by
    rw [hSigma]
    exact hPull
  obtain ⟨G, hG, hGfactor⟩ := hPull'.exists_eq_measurable_comp
  refine ⟨G, hG, ?_⟩
  funext p
  exact congrFun hGfactor p

/-- Every coordinate of an `IsGMCOf` finite measure has a measurable field-space proxy. -/
theorem equatorGFF_GMC_finiteEval_field_proxy
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    ∃ E : (TestFn → ℝ) → (Option (ℚ × ℚ) → ℝ≥0∞),
      Measurable E ∧
      (fun ω => gmcFiniteMeasureEval ⟨M ω, hM.1 ω⟩) =ᵐ[P]
        fun ω => E (fun f => X ω f) := by
  have hfinite : ∀ ω, IsFiniteMeasure (M ω) := by
    change (∀ ω, IsFiniteMeasure (M ω)) ∧ _ at hM
    exact hM.1
  let eval : Ω → TestFn → ℝ := fun ω f => X ω f
  have hcoord : ∀ i : Option (ℚ × ℚ),
      ∃ g : (TestFn → ℝ) → ℝ≥0∞, Measurable g ∧
        (fun ω => gmcFiniteMeasureEval ⟨M ω, hfinite ω⟩ i) =ᵐ[P]
          fun ω => g (eval ω) := by
    intro i
    cases i with
    | some j =>
      obtain ⟨g, hg, hEq⟩ :=
        equatorGFF_GMC_lowerBox_realMass_field_factor P X hX γ M hM j
      let gE : (TestFn → ℝ) → ℝ≥0∞ := fun q => ENNReal.ofReal (max 0 (g q))
      have hgE : Measurable gE := by
        dsimp [gE]
        exact ENNReal.measurable_ofReal.comp (measurable_const.max hg)
      refine ⟨gE, hgE, ?_⟩
      filter_upwards [hEq] with ω hω
      have hω' : (M ω (gmcLowerBox j)).toReal = g (eval ω) := by
        simpa [eval] using hω
      have hmass : M ω (gmcLowerBox j) ≠ ∞ :=
        @MeasureTheory.measure_ne_top ℂ _ (M ω) (hfinite ω) (gmcLowerBox j)
      have hnonneg : 0 ≤ g (eval ω) := by
        rw [← hω']
        exact ENNReal.toReal_nonneg
      change M ω (gmcLowerBox j) = ENNReal.ofReal (max 0 (g (eval ω)))
      calc
        M ω (gmcLowerBox j) = ENNReal.ofReal ((M ω (gmcLowerBox j)).toReal) :=
          (ENNReal.ofReal_toReal hmass).symm
        _ = ENNReal.ofReal (max 0 (g (eval ω))) := by
          rw [max_eq_right hnonneg, hω']
    | none =>
      obtain ⟨gΩ, hgΩ, hInt⟩ :=
        equatorGFF_GMC_testIntegral_raw_measurable_version_of_IsGMCOf
          P X hX γ M hM (1 : BoundedContinuousFunction ℂ ℝ)
      have hgComap : Measurable[(MeasurableSpace.pi).comap eval] gΩ := by
        change Measurable[equatorGFFRawDistributionSigma X] gΩ at hgΩ
        simpa [equatorGFFRawDistributionSigma, eval] using hgΩ
      obtain ⟨g, hg, hFactor⟩ := hgComap.exists_eq_measurable_comp
      let gE : (TestFn → ℝ) → ℝ≥0∞ := fun q => ENNReal.ofReal (max 0 (g q))
      have hgE : Measurable gE := by
        dsimp [gE]
        exact ENNReal.measurable_ofReal.comp (measurable_const.max hg)
      have hMassEq : (fun ω => (M ω Set.univ).toReal) =ᵐ[P]
          fun ω => g (eval ω) := by
        filter_upwards [hInt] with ω hω
        have hconst : (∫ z, (1 : BoundedContinuousFunction ℂ ℝ) z ∂M ω) =
            (M ω Set.univ).toReal := by
          rw [← MeasureTheory.Measure.real_def]
          simp [integral_const]
        change (M ω Set.univ).toReal = g (eval ω)
        rw [hconst, hFactor] at hω
        simpa only [Function.comp_apply] using hω
      refine ⟨gE, hgE, ?_⟩
      filter_upwards [hMassEq] with ω hω
      have hmass : M ω Set.univ ≠ ∞ :=
        @MeasureTheory.measure_ne_top ℂ _ (M ω) (hfinite ω) Set.univ
      have hnonneg : 0 ≤ g (eval ω) := by
        rw [← hω]
        exact ENNReal.toReal_nonneg
      change M ω Set.univ = ENNReal.ofReal (max 0 (g (eval ω)))
      calc
        M ω Set.univ = ENNReal.ofReal ((M ω Set.univ).toReal) :=
          (ENNReal.ofReal_toReal hmass).symm
        _ = ENNReal.ofReal (max 0 (g (eval ω))) := by
          rw [max_eq_right hnonneg, hω]

  choose g hg hEq using hcoord
  let E : (TestFn → ℝ) → (Option (ℚ × ℚ) → ℝ≥0∞) := fun q i => g i q
  have hE : Measurable E := by
    apply measurable_pi_iff.mpr
    intro i
    exact (hg i)
  have hAE : (fun ω => gmcFiniteMeasureEval ⟨M ω, hfinite ω⟩) =ᵐ[P]
      fun ω => E (eval ω) := by
    filter_upwards [ae_all_iff.mpr hEq] with ω hω
    funext i
    exact hω i
  exact ⟨E, hE, hAE⟩

/-- Pulling a measurable field/finite-measure functional back along an `IsGMCOf` limit gives a
measurable function of the field, up to almost-sure equality. -/
theorem equatorGFF_GMC_function_field_proxy
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (H : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun p : (TestFn → ℝ) × Measure ℂ => H p.1 p.2)) :
    ∃ h : (TestFn → ℝ) → ℝ≥0∞, Measurable h ∧
      (fun ω => H (fun f => X ω f) (M ω)) =ᵐ[P]
        fun ω => h (fun f => X ω f) := by
  obtain ⟨G, hG, hGfactor⟩ := gmc_measurable_function_factors_through_finite_eval H hH
  obtain ⟨E, hE, hEae⟩ := equatorGFF_GMC_finiteEval_field_proxy P X hX γ M hM
  let eval : Ω → TestFn → ℝ := fun ω f => X ω f
  let h : (TestFn → ℝ) → ℝ≥0∞ := fun q => G (q, E q)
  have hh : Measurable h := by
    dsimp [h]
    exact hG.comp (Measurable.prodMk measurable_id hE)
  have hMfinite : ∀ ω, IsFiniteMeasure (M ω) := by
    change (∀ ω, IsFiniteMeasure (M ω)) ∧ _ at hM
    exact hM.1
  have hEq : (fun ω => H (eval ω) (M ω)) =ᵐ[P]
      fun ω => h (eval ω) := by
    filter_upwards [hEae] with ω hω
    have hfact := congrFun hGfactor (eval ω, ⟨M ω, hMfinite ω⟩)
    have hfact' : H (eval ω) (M ω) =
        G (eval ω, gmcFiniteMeasureEval ⟨M ω, hMfinite ω⟩) := by
      simpa [gmcJointFiniteEval] using hfact
    dsimp [h]
    rw [hfact', hω]
  exact ⟨h, hh, hEq⟩

end

end DOZZ.Proofs
