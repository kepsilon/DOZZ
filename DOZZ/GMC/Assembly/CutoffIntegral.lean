/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Assembly.CutoffCauchy

/-! The cutoff `L¹` Cauchy estimate over compact charge sets for signed Borel tests in real form, and the pointwise algebra of cutoff integrals in the test. -/

@[expose] public section

/-! ### Uniformity over compact charge sets

The cutoff `L¹` Cauchy estimate, uniformly over a compact set of charges in `(0, 2)` and over
signed bounded Borel tests supported in a compact chart.

Each charge has a neighbourhood with uniform barrier parameters; finitely many cover a compact
charge set. Signed tests split into positive and negative parts. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Assembly

open DOZZ.Proofs

/-- Every subcritical charge has a closed neighbourhood with common barrier parameters. -/
theorem exists_local_barrier_parameters (γ₀ : ℝ) (hγ₀ : 0 < γ₀) (hγ₀2 : γ₀ < 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ a η κ : ℝ, 0 < γ₀ - δ ∧ γ₀ + δ < a ∧ a < 2 * (γ₀ - δ) ∧
      0 < η ∧ η < 1 ∧ 0 < κ ∧ κ < 2 ∧
      ∀ g ∈ Icc (γ₀ - δ) (γ₀ + δ),
        g ^ 2 - ((1 - η) ^ 2 * (2 * g - a) ^ 2 / (2 * (1 + η))) ≤ κ := by
  obtain ⟨a, κ, η, hγa, ha2, hκ, hκ2, hη, hη1, hexp⟩ :=
    exists_fixed_charge_robust_barrier_parameters γ₀ hγ₀ hγ₀2
  set κ' : ℝ := (κ + 2) / 2 with hκ'def
  let φ : ℝ → ℝ := fun g => g ^ 2 - ((1 - η) ^ 2 * (2 * g - a) ^ 2 / (2 * (1 + η)))
  have hφ : Continuous φ := by fun_prop
  let V : Set ℝ := {g | 0 < g} ∩ {g | g < a} ∩ {g | a < 2 * g} ∩ {g | φ g < κ'}
  have hV : IsOpen V :=
    (((isOpen_lt continuous_const continuous_id).inter
      (isOpen_lt continuous_id continuous_const)).inter
      (isOpen_lt continuous_const (continuous_const.mul continuous_id))).inter
      (isOpen_lt hφ continuous_const)
  have hγ₀V : γ₀ ∈ V := ⟨⟨⟨hγ₀, hγa⟩, ha2⟩, lt_of_le_of_lt hexp (by rw [hκ'def]; linarith)⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV γ₀ hγ₀V
  have hmem (g : ℝ) (hg : g ∈ Icc (γ₀ - ε / 2) (γ₀ + ε / 2)) : g ∈ V := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hg.1, hg.2]
  have hlo := hmem (γ₀ - ε / 2) ⟨le_rfl, by linarith⟩
  have hhi := hmem (γ₀ + ε / 2) ⟨by linarith, le_rfl⟩
  refine ⟨ε / 2, half_pos hε, a, η, κ', hlo.1.1.1, hhi.1.1.2, hlo.1.2, hη, hη1,
    by rw [hκ'def]; linarith, by rw [hκ'def]; linarith, fun g hg => (hmem g hg).2.le⟩

/-- Full cutoff masses of tests with values in `[0, L]` are uniformly Cauchy in `L¹(P)` over a
compact set of subcritical charges. -/
theorem chartMass_L1_uniform_cauchy
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (I : Set ℝ) (hI : IsCompact I) (hI2 : I ⊆ Ioo 0 2)
    (L : ℝ) (hL : 0 ≤ L) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ r s : ℝ, R ≤ r → R ≤ s → ∀ g ∈ I, ∀ f : ℂ → ℝ, Measurable f →
      (∀ x, 0 ≤ f x) → (∀ x, f x ≤ L) →
      ∫⁻ ω, ennDist (chartMass P U dens K Y g r f ω) (chartMass P U dens K Y g s f ω) ∂P <
        ENNReal.ofReal ε := by
  classical
  have hloc : ∀ γ₀ : I, ∃ δ : ℝ, 0 < δ ∧ ∃ a η κ : ℝ, 0 < (γ₀ : ℝ) - δ ∧
      (γ₀ : ℝ) + δ < a ∧ a < 2 * ((γ₀ : ℝ) - δ) ∧ 0 < η ∧ η < 1 ∧ 0 < κ ∧ κ < 2 ∧
      ∀ g ∈ Icc ((γ₀ : ℝ) - δ) ((γ₀ : ℝ) + δ),
        g ^ 2 - ((1 - η) ^ 2 * (2 * g - a) ^ 2 / (2 * (1 + η))) ≤ κ :=
    fun γ₀ => exists_local_barrier_parameters γ₀ (hI2 γ₀.2).1 (hI2 γ₀.2).2
  choose δ hδ a η κ hlo hhi ha2 hη hη1 hκ hκ2 hexp using hloc
  have hR : ∀ γ₀ : I, ∃ R : ℝ, ∀ r s : ℝ, R ≤ r → R ≤ s →
      ∀ g ∈ Icc ((γ₀ : ℝ) - δ γ₀) ((γ₀ : ℝ) + δ γ₀), ∀ f : ℂ → ℝ, Measurable f →
      (∀ x, 0 ≤ f x) → (∀ x, f x ≤ L) →
      ∫⁻ ω, ennDist (chartMass P U dens K Y g r f ω) (chartMass P U dens K Y g s f ω) ∂P <
        ENNReal.ofReal ε := fun γ₀ =>
    chartMass_L1_uniform_cauchy_interval P U dens ε₀ Y hY K hK hKU _ _ (a γ₀) (η γ₀) (κ γ₀)
      (hlo γ₀) (by linarith [hδ γ₀]) (hhi γ₀) (ha2 γ₀) (hη γ₀) (hη1 γ₀) (hκ γ₀) (hκ2 γ₀)
      (hexp γ₀) L hL ε hε
  choose R hR using hR
  obtain ⟨t, ht⟩ := hI.elim_finite_subcover
    (fun γ₀ : I => Ioo ((γ₀ : ℝ) - δ γ₀) ((γ₀ : ℝ) + δ γ₀)) (fun _ => isOpen_Ioo)
    (fun g hg => Set.mem_iUnion.mpr ⟨⟨g, hg⟩, by
      constructor <;> linarith [hδ ⟨g, hg⟩]⟩)
  refine ⟨∑ i ∈ t, |R i|, ?_⟩
  intro r s hr hs g hg f hf hf0 hfL
  obtain ⟨i, hi, hgi⟩ := Set.mem_iUnion₂.mp (ht hg)
  have hRi : R i ≤ ∑ j ∈ t, |R j| :=
    (le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (R j)) hi)
  exact hR i r s (hRi.trans hr) (hRi.trans hs) g ⟨hgi.1.le, hgi.2.le⟩ f hf hf0 hfL

end DOZZ.Assembly

/-! ### Real cutoff integrals of signed tests

Real cutoff test integrals of signed bounded Borel tests are uniformly Cauchy in `L¹`.

The real cutoff integral of a nonnegative test supported in the chart is the real part of the
extended chart mass; a signed test splits into positive and negative parts, which are integrable
almost surely because the expected chart mass is finite. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Assembly

open DOZZ.Proofs

/-- The real cutoff test integral of an admissible regularization against a real test. -/
noncomputable def admissibleCutoffIntegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U : Set ℂ) (dens : ℂ → ℝ) (Y : Ω → ℝ → ℂ → ℝ) (g r : ℝ) (f : ℂ → ℝ) (ω : Ω) : ℝ :=
  ∫ x, f x * Real.exp (g * Y ω (Real.exp (-r)) x - g ^ 2 / 2 *
    ∫ ω', Y ω' (Real.exp (-r)) x ^ 2 ∂P) ∂logRegularizationReference U dens


/-- The Wick exponential in the cutoff integrand is the admissible Wick weight. -/
theorem ofReal_exp_eq_admissibleLogWickWeight
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ → ℂ → ℝ) (g ε : ℝ) (x : ℂ)
    (ω : Ω) :
    ENNReal.ofReal (Real.exp (g * Y ω ε x - g ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P)) =
      admissibleLogWickWeight P Y g ε x ω := by
  unfold admissibleLogWickWeight gaussianVariance gaussianCovariance
  simp only [pow_two]

/-- The cutoff integrand is measurable in the point. -/
theorem admissibleCutoff_integrand_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (g r : ℝ) (f : ℂ → ℝ)
    (hf : Measurable f) (ω : Ω) :
    Measurable (fun x => f x * Real.exp (g * Y ω (Real.exp (-r)) x - g ^ 2 / 2 *
      ∫ ω', Y ω' (Real.exp (-r)) x ^ 2 ∂P)) := by
  have hv := admissibleLogRegularization_variance_measurable P U dens ε₀ Y hY (Real.exp (-r))
  have hv' : Measurable (fun x => ∫ ω', Y ω' (Real.exp (-r)) x ^ 2 ∂P) := by
    have heq : (fun x => ∫ ω', Y ω' (Real.exp (-r)) x ^ 2 ∂P) =
        fun x => gaussianVariance P (fun ω => Y ω (Real.exp (-r)) x) := by
      funext x
      unfold gaussianVariance gaussianCovariance
      simp only [pow_two]
    rw [heq]; exact hv
  have hfield : Measurable (fun x : ℂ => Y ω (Real.exp (-r)) x) :=
    (hY.measurableAtScale (Real.exp (-r))).comp (measurable_const.prodMk measurable_id)
  fun_prop

/-- For a nonnegative test vanishing off the chart, the extended cutoff integral is the chart
mass. -/
theorem lintegral_cutoff_integrand_eq_chartMass
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ)
    (Y : Ω → ℝ → ℂ → ℝ) (K : Set ℂ) (g r : ℝ) (f : ℂ → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hfK : ∀ x ∉ K, f x = 0) (ω : Ω) :
    ∫⁻ x, ENNReal.ofReal (f x * Real.exp (g * Y ω (Real.exp (-r)) x - g ^ 2 / 2 *
        ∫ ω', Y ω' (Real.exp (-r)) x ^ 2 ∂P)) ∂logRegularizationReference U dens =
      chartMass P U dens K Y g r f ω := by
  rw [← setLIntegral_eq_of_support_subset (s := K)]
  · unfold chartMass wickEventMass
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_mul (hf0 x), ofReal_exp_eq_admissibleLogWickWeight,
      Set.indicator_of_mem (Set.mem_univ _), mul_one]
  · intro x hx
    by_contra hxK
    exact hx (by simp [hfK x hxK])

/-- For a nonnegative test vanishing off the chart, the real cutoff integral is the real part of
the chart mass. -/
theorem admissibleCutoffIntegral_eq_toReal_chartMass
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (K : Set ℂ) (g r : ℝ) (f : ℂ → ℝ)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfK : ∀ x ∉ K, f x = 0) (ω : Ω) :
    admissibleCutoffIntegral P U dens Y g r f ω = (chartMass P U dens K Y g r f ω).toReal := by
  unfold admissibleCutoffIntegral
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun x => mul_nonneg (hf0 x) (Real.exp_pos _).le)
    (admissibleCutoff_integrand_measurable P U dens ε₀ Y hY g r f hf ω).aestronglyMeasurable,
    lintegral_cutoff_integrand_eq_chartMass P U dens Y K g r f hf0 hfK ω]

/-- The admissible Wick weight has expectation one at every admissible cutoff. -/
theorem lintegral_admissibleLogWickWeight
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (g ε : ℝ) (hε : 0 < ε)
    (hεcut : ε ≤ ε₀) (x : ℂ) :
    ∫⁻ ω, admissibleLogWickWeight P Y g ε x ω ∂P = 1 := by
  have h := compatibleAdmissibleSelectedWickWeight_lintegral_eq_one P U dens ε₀ ε₀ Y Y hY hY
    true ε hε (by rw [min_self]; exact hεcut) x g
  simpa only [ite_self] using h

/-- The expected chart mass of a test with values in `[0, L]` is at most `L` times the reference
mass of the chart. -/
theorem lintegral_chartMass_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (K : Set ℂ) (g r : ℝ)
    (hr : Real.exp (-r) ≤ ε₀) (L : ℝ) (f : ℂ → ℝ) (hf : Measurable f) (hfL : ∀ x, f x ≤ L) :
    ∫⁻ ω, chartMass P U dens K Y g r f ω ∂P ≤
      ENNReal.ofReal L * logRegularizationReference U dens K := by
  have hF := wickEventMass_integrand_measurable P U dens ε₀ Y hY g r Set.univ
    MeasurableSet.univ f hf
  unfold chartMass wickEventMass
  rw [lintegral_lintegral_swap hF.aemeasurable]
  calc ∫⁻ x, ∫⁻ ω, ENNReal.ofReal (f x) * admissibleLogWickWeight P Y g (Real.exp (-r)) x ω *
        Set.indicator Set.univ (fun _ => (1 : ℝ≥0∞)) (ω, x) ∂P
        ∂(logRegularizationReference U dens).restrict K
      = ∫⁻ x, ENNReal.ofReal (f x) ∂(logRegularizationReference U dens).restrict K := by
        apply lintegral_congr
        intro x
        simp only [Set.indicator_univ, mul_one]
        rw [lintegral_const_mul _ (admissibleLogWickWeight_measurable_sample P U dens ε₀ Y hY g _
          x), lintegral_admissibleLogWickWeight P U dens ε₀ Y hY g _ (Real.exp_pos _) hr x,
          mul_one]
    _ ≤ ∫⁻ _, ENNReal.ofReal L ∂(logRegularizationReference U dens).restrict K :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hfL x)
    _ = ENNReal.ofReal L * logRegularizationReference U dens K := by
        rw [lintegral_const, Measure.restrict_apply_univ]

/-- The real distance of two real parts is at most the symmetric extended difference. -/
theorem ofReal_abs_toReal_sub_le_ennDist (x y : ℝ≥0∞) :
    ENNReal.ofReal |x.toReal - y.toReal| ≤ ennDist x y := by
  by_cases hx : x = ⊤
  · subst hx
    by_cases hy : y = ⊤
    · subst hy; simp
    · simp [ennDist, ENNReal.top_sub hy]
  by_cases hy : y = ⊤
  · subst hy; simp [ennDist, ENNReal.top_sub hx]
  rw [ennDist_eq_ofReal_abs hx hy]

/-- A signed test vanishing off the chart has an almost surely integrable cutoff integrand. -/
theorem admissibleCutoff_integrand_integrable_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) (g r : ℝ) (hr : Real.exp (-r) ≤ ε₀)
    (L : ℝ) (f : ℂ → ℝ) (hf : Measurable f) (hfL : ∀ x, |f x| ≤ L)
    (hfK : ∀ x ∉ K, f x = 0) :
    ∀ᵐ ω ∂P, Integrable (fun x => f x * Real.exp (g * Y ω (Real.exp (-r)) x - g ^ 2 / 2 *
      ∫ ω', Y ω' (Real.exp (-r)) x ^ 2 ∂P)) (logRegularizationReference U dens) := by
  have hσK := admissible_logRegularization_reference_measure_ne_top P U dens ε₀ Y hY K hK hKU
  have habs : Measurable (fun x => |f x|) := continuous_abs.measurable.comp hf
  have hmass := lintegral_chartMass_le P U dens ε₀ Y hY K g r hr L (fun x => |f x|) habs hfL
  have hmeas : Measurable (chartMass P U dens K Y g r (fun x => |f x|)) :=
    wickEventMass_measurable P U dens ε₀ Y hY _ g r Set.univ MeasurableSet.univ _ habs
  have hfin := ae_lt_top hmeas (ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hσK) hmass)
  filter_upwards [hfin] with ω hω
  refine ⟨(admissibleCutoff_integrand_measurable P U dens ε₀ Y hY g r f hf ω).aestronglyMeasurable,
    ?_⟩
  unfold HasFiniteIntegral
  have hnorm : (fun x => ‖f x * Real.exp (g * Y ω (Real.exp (-r)) x - g ^ 2 / 2 *
      ∫ ω', Y ω' (Real.exp (-r)) x ^ 2 ∂P)‖ₑ) = fun x => ENNReal.ofReal (|f x| *
      Real.exp (g * Y ω (Real.exp (-r)) x - g ^ 2 / 2 * ∫ ω', Y ω' (Real.exp (-r)) x ^ 2 ∂P)) := by
    funext x
    rw [← ofReal_norm, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  rw [hnorm, lintegral_cutoff_integrand_eq_chartMass P U dens Y K g r _ (fun x => abs_nonneg _)
    (fun x hx => by rw [hfK x hx, abs_zero]) ω]
  exact hω

/-- Real cutoff integrals of signed tests bounded by `L` and supported in a compact chart are
uniformly Cauchy in `L¹(P)` over a compact set of subcritical charges. -/
theorem admissibleCutoffIntegral_L1_uniform_cauchy
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (I : Set ℝ) (hI : IsCompact I) (hI2 : I ⊆ Ioo 0 2)
    (L : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ r s : ℝ, R ≤ r → R ≤ s → ∀ g ∈ I, ∀ f : ℂ → ℝ, Measurable f →
      (∀ x, |f x| ≤ L) → (∀ x ∉ K, f x = 0) →
      ∫⁻ ω, ENNReal.ofReal |admissibleCutoffIntegral P U dens Y g r f ω -
        admissibleCutoffIntegral P U dens Y g s f ω| ∂P < ENNReal.ofReal ε := by
  set L' := max L 0 with hL'def
  have hL' : 0 ≤ L' := le_max_right _ _
  obtain ⟨R₁, hR₁⟩ := chartMass_L1_uniform_cauchy P U dens ε₀ Y hY K hK hKU I hI hI2 L' hL'
    (ε / 2) (by linarith)
  refine ⟨max R₁ (-Real.log ε₀), ?_⟩
  intro r s hr hs g hg f hf hfL hfK
  have hcut (t : ℝ) (ht : max R₁ (-Real.log ε₀) ≤ t) : Real.exp (-t) ≤ ε₀ := by
    have h1 : -Real.log ε₀ ≤ t := le_trans (le_max_right _ _) ht
    calc Real.exp (-t) ≤ Real.exp (Real.log ε₀) := Real.exp_le_exp.mpr (by linarith)
      _ = ε₀ := Real.exp_log hY.cutoffPositive
  let fp : ℂ → ℝ := fun x => max (f x) 0
  let fm : ℂ → ℝ := fun x => max (-f x) 0
  have hfp : Measurable fp := hf.max measurable_const
  have hfm : Measurable fm := hf.neg.max measurable_const
  have hfp0 : ∀ x, 0 ≤ fp x := fun x => le_max_right _ _
  have hfm0 : ∀ x, 0 ≤ fm x := fun x => le_max_right _ _
  have hfpL : ∀ x, fp x ≤ L' := fun x =>
    max_le_max ((le_abs_self _).trans (hfL x)) le_rfl
  have hfmL : ∀ x, fm x ≤ L' := fun x =>
    max_le_max ((neg_le_abs _).trans (hfL x)) le_rfl
  have hfpK : ∀ x ∉ K, fp x = 0 := fun x hx => by simp [fp, hfK x hx]
  have hfmK : ∀ x ∉ K, fm x = 0 := fun x hx => by simp [fm, hfK x hx]
  have hsplit (x : ℂ) : f x = fp x - fm x := by
    simp only [fp, fm]
    rcases le_total 0 (f x) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hdecomp (t : ℝ) (ht : max R₁ (-Real.log ε₀) ≤ t) : ∀ᵐ ω ∂P,
      admissibleCutoffIntegral P U dens Y g t f ω =
        (chartMass P U dens K Y g t fp ω).toReal - (chartMass P U dens K Y g t fm ω).toReal := by
    have hfabs : ∀ x, |f x| ≤ L' := fun x => (hfL x).trans (le_max_left _ _)
    have hpInt := admissibleCutoff_integrand_integrable_ae P U dens ε₀ Y hY K hK hKU g t (hcut t ht)
      L' fp hfp (fun x => by rw [abs_of_nonneg (hfp0 x)]; exact hfpL x) hfpK
    have hmInt := admissibleCutoff_integrand_integrable_ae P U dens ε₀ Y hY K hK hKU g t (hcut t ht)
      L' fm hfm (fun x => by rw [abs_of_nonneg (hfm0 x)]; exact hfmL x) hfmK
    have _ := hfabs
    filter_upwards [hpInt, hmInt] with ω hp hm
    rw [← admissibleCutoffIntegral_eq_toReal_chartMass P U dens ε₀ Y hY K g t fp hfp hfp0 hfpK ω,
      ← admissibleCutoffIntegral_eq_toReal_chartMass P U dens ε₀ Y hY K g t fm hfm hfm0 hfmK ω]
    unfold admissibleCutoffIntegral
    rw [← integral_sub hp hm]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hsplit x]
    ring
  have hptwise : ∀ᵐ ω ∂P, ENNReal.ofReal |admissibleCutoffIntegral P U dens Y g r f ω -
      admissibleCutoffIntegral P U dens Y g s f ω| ≤
      ennDist (chartMass P U dens K Y g r fp ω) (chartMass P U dens K Y g s fp ω) +
        ennDist (chartMass P U dens K Y g r fm ω) (chartMass P U dens K Y g s fm ω) := by
    filter_upwards [hdecomp r hr, hdecomp s hs] with ω hrω hsω
    rw [hrω, hsω]
    set a := (chartMass P U dens K Y g r fp ω).toReal
    set b := (chartMass P U dens K Y g r fm ω).toReal
    set c := (chartMass P U dens K Y g s fp ω).toReal
    set d := (chartMass P U dens K Y g s fm ω).toReal
    calc ENNReal.ofReal |a - b - (c - d)| ≤ ENNReal.ofReal (|a - c| + |b - d|) := by
          apply ENNReal.ofReal_le_ofReal
          calc |a - b - (c - d)| = |(a - c) - (b - d)| := by ring_nf
            _ ≤ |a - c| + |b - d| := abs_sub _ _
      _ = ENNReal.ofReal |a - c| + ENNReal.ofReal |b - d| :=
          ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      _ ≤ _ := add_le_add (ofReal_abs_toReal_sub_le_ennDist _ _)
          (ofReal_abs_toReal_sub_le_ennDist _ _)
  have hR₁r : R₁ ≤ r := le_trans (le_max_left _ _) hr
  have hR₁s : R₁ ≤ s := le_trans (le_max_left _ _) hs
  have hmp (t : ℝ) : Measurable (chartMass P U dens K Y g t fp) :=
    wickEventMass_measurable P U dens ε₀ Y hY _ g t Set.univ MeasurableSet.univ fp hfp
  calc _ ≤ ∫⁻ ω, ennDist (chartMass P U dens K Y g r fp ω) (chartMass P U dens K Y g s fp ω) +
        ennDist (chartMass P U dens K Y g r fm ω) (chartMass P U dens K Y g s fm ω) ∂P :=
        lintegral_mono_ae hptwise
    _ = ∫⁻ ω, ennDist (chartMass P U dens K Y g r fp ω) (chartMass P U dens K Y g s fp ω) ∂P +
        ∫⁻ ω, ennDist (chartMass P U dens K Y g r fm ω) (chartMass P U dens K Y g s fm ω) ∂P :=
        lintegral_add_left (ennDist_measurable (hmp r) (hmp s)) _
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        ENNReal.add_lt_add (hR₁ r s hR₁r hR₁s g hg fp hfp hfp0 hfpL)
          (hR₁ r s hR₁r hR₁s g hg fm hfm hfm0 hfmL)
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1
        ring

end DOZZ.Assembly

/-! ### Algebra in the test

Pointwise algebra of admissible cutoff integrals in the test.

For a sample whose cutoff mass of the indicator of a compact chart is finite, cutoff integrals of
bounded Borel tests supported in that chart are integrable, linear and monotone in the test. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Assembly

open DOZZ.Proofs

/-- The cutoff integrand of a test. -/
noncomputable abbrev cutoffIntegrand {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ → ℂ → ℝ) (g r : ℝ) (f : ℂ → ℝ) (ω : Ω) (x : ℂ) : ℝ :=
  f x * Real.exp (g * Y ω (Real.exp (-r)) x - g ^ 2 / 2 * ∫ ω', Y ω' (Real.exp (-r)) x ^ 2 ∂P)

/-- The chart mass of the constant test one. -/
noncomputable abbrev chartUnitMass {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U : Set ℂ) (dens : ℂ → ℝ) (K : Set ℂ) (Y : Ω → ℝ → ℂ → ℝ) (g r : ℝ) (ω : Ω) : ℝ≥0∞ :=
  chartMass P U dens K Y g r (fun _ => 1) ω

/-- With finite unit chart mass, every bounded Borel test supported in the chart has an
integrable cutoff integrand. -/
theorem cutoffIntegrand_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (K : Set ℂ) (g r : ℝ) (ω : Ω)
    (hω : chartUnitMass P U dens K Y g r ω ≠ ⊤) (L : ℝ) (f : ℂ → ℝ) (hf : Measurable f)
    (hfL : ∀ x, |f x| ≤ L) (hfK : ∀ x ∉ K, f x = 0) :
    Integrable (cutoffIntegrand P Y g r f ω) (logRegularizationReference U dens) := by
  refine ⟨(admissibleCutoff_integrand_measurable P U dens ε₀ Y hY g r f hf ω).aestronglyMeasurable,
    ?_⟩
  unfold HasFiniteIntegral
  have hL : 0 ≤ L := (abs_nonneg _).trans (hfL 0)
  have hnorm : (fun x => ‖cutoffIntegrand P Y g r f ω x‖ₑ) = fun x => ENNReal.ofReal (|f x| *
      Real.exp (g * Y ω (Real.exp (-r)) x - g ^ 2 / 2 *
        ∫ ω', Y ω' (Real.exp (-r)) x ^ 2 ∂P)) := by
    funext x
    rw [← ofReal_norm, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  rw [hnorm, lintegral_cutoff_integrand_eq_chartMass P U dens Y K g r _ (fun x => abs_nonneg _)
    (fun x hx => by rw [hfK x hx, abs_zero]) ω]
  have hle : chartMass P U dens K Y g r (fun x => |f x|) ω ≤
      ENNReal.ofReal L * chartUnitMass P U dens K Y g r ω := by
    unfold chartUnitMass chartMass wickEventMass
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro x
    beta_reduce
    rw [ENNReal.ofReal_one, one_mul, ← mul_assoc]
    exact mul_le_mul_left (mul_le_mul_left (ENNReal.ofReal_le_ofReal (hfL x)) _) _
  exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hω))

/-- Additivity of the cutoff integral in the test. -/
theorem admissibleCutoffIntegral_add
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (K : Set ℂ) (g r : ℝ) (ω : Ω)
    (hω : chartUnitMass P U dens K Y g r ω ≠ ⊤) (L₁ L₂ : ℝ) (f₁ f₂ : ℂ → ℝ)
    (hf₁ : Measurable f₁) (hf₂ : Measurable f₂) (hf₁L : ∀ x, |f₁ x| ≤ L₁)
    (hf₂L : ∀ x, |f₂ x| ≤ L₂) (hf₁K : ∀ x ∉ K, f₁ x = 0) (hf₂K : ∀ x ∉ K, f₂ x = 0) :
    admissibleCutoffIntegral P U dens Y g r (fun x => f₁ x + f₂ x) ω =
      admissibleCutoffIntegral P U dens Y g r f₁ ω +
        admissibleCutoffIntegral P U dens Y g r f₂ ω := by
  unfold admissibleCutoffIntegral
  rw [← integral_add (cutoffIntegrand_integrable P U dens ε₀ Y hY K g r ω hω L₁ f₁ hf₁ hf₁L hf₁K)
    (cutoffIntegrand_integrable P U dens ε₀ Y hY K g r ω hω L₂ f₂ hf₂ hf₂L hf₂K)]
  congr 1
  funext x
  ring

/-- Homogeneity of the cutoff integral in the test. -/
theorem admissibleCutoffIntegral_smul
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ)
    (Y : Ω → ℝ → ℂ → ℝ) (g r : ℝ) (c : ℝ) (f : ℂ → ℝ) (ω : Ω) :
    admissibleCutoffIntegral P U dens Y g r (fun x => c * f x) ω =
      c * admissibleCutoffIntegral P U dens Y g r f ω := by
  unfold admissibleCutoffIntegral
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

/-- Monotonicity of the cutoff integral in the test. -/
theorem admissibleCutoffIntegral_mono
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (K : Set ℂ) (g r : ℝ) (ω : Ω)
    (hω : chartUnitMass P U dens K Y g r ω ≠ ⊤) (L₁ L₂ : ℝ) (f₁ f₂ : ℂ → ℝ)
    (hf₁ : Measurable f₁) (hf₂ : Measurable f₂) (hf₁L : ∀ x, |f₁ x| ≤ L₁)
    (hf₂L : ∀ x, |f₂ x| ≤ L₂) (hf₁K : ∀ x ∉ K, f₁ x = 0) (hf₂K : ∀ x ∉ K, f₂ x = 0)
    (hle : ∀ x, f₁ x ≤ f₂ x) :
    admissibleCutoffIntegral P U dens Y g r f₁ ω ≤
      admissibleCutoffIntegral P U dens Y g r f₂ ω := by
  unfold admissibleCutoffIntegral
  apply integral_mono (cutoffIntegrand_integrable P U dens ε₀ Y hY K g r ω hω L₁ f₁ hf₁ hf₁L hf₁K)
    (cutoffIntegrand_integrable P U dens ε₀ Y hY K g r ω hω L₂ f₂ hf₂ hf₂L hf₂K)
  intro x
  exact mul_le_mul_of_nonneg_right (hle x) (Real.exp_pos _).le

/-- Unit chart masses are finite almost surely at every admissible cutoff. -/
theorem chartUnitMass_ne_top_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) (g r : ℝ) (hr : Real.exp (-r) ≤ ε₀) :
    ∀ᵐ ω ∂P, chartUnitMass P U dens K Y g r ω ≠ ⊤ := by
  have hσK := admissible_logRegularization_reference_measure_ne_top P U dens ε₀ Y hY K hK hKU
  have hmass := lintegral_chartMass_le P U dens ε₀ Y hY K g r hr 1 (fun _ => 1) measurable_const
    (fun _ => le_rfl)
  have hmeas : Measurable (chartUnitMass P U dens K Y g r) :=
    wickEventMass_measurable P U dens ε₀ Y hY _ g r Set.univ MeasurableSet.univ _ measurable_const
  filter_upwards [ae_lt_top hmeas (ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hσK) hmass)] with ω hω
  exact hω.ne

end DOZZ.Assembly
