/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Mobius.RepinField
public import DOZZ.ShiftEquations.Mobius.RepinChaos
public import DOZZ.Statements.Defs.IsGMCOf
import DOZZ.GMC.CircleAverage
import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
import DOZZ.GMC.CompatibleAdmissibleGMCUnique
import DOZZ.GMC.CircleAverageCutoffIntensity
import DOZZ.GMC.Construction.ReferenceMeasureFinite

/-!
# The repinned chaos is the GMC of the repinned field

The regularized chaos of the repinned circle averages is, sample by sample, a tilt of the
regularized chaos of `X` at the shifted cutoff (`integral_regularizedGMC_repinCircle`). The tilt
weights converge uniformly to those of the repinned chaos, the regularized total masses have
bounded expectation, and the regularized chaos of `X` converges to `M` in probability against
bounded continuous tests. Hence the repinned regularized chaos converges to the repinned chaos.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Multiplying a family converging in measure by a fixed real random variable preserves the
convergence. -/
theorem tendstoInMeasure_const_mul {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {l : Filter ι} (E : Ω → ℝ) (hE : Measurable E) {F : ι → Ω → ℝ}
    {G : Ω → ℝ} (hF : TendstoInMeasure P F l G) :
    TendstoInMeasure P (fun i ω => E ω * F i ω) l (fun ω => E ω * G ω) := by
  rw [tendstoInMeasure_iff_norm] at hF ⊢
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  let T : ℕ → Set Ω := fun n => {ω | (n : ℝ) < |E ω|}
  have hTmeas (n : ℕ) : MeasurableSet (T n) :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp hE)
  have hTanti : Antitone T := fun n m hnm ω hω =>
    lt_of_le_of_lt (by exact_mod_cast hnm) (show (m : ℝ) < |E ω| from hω)
  have hTinter : (⋂ n, T n) = ∅ := by
    ext ω
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨n, hn⟩ := exists_nat_gt (|E ω|)
    exact ⟨n, fun h => (lt_asymm hn) h⟩
  have hTlimit : Tendsto (fun n => P (T n)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := P) (s := T)
      (fun n => (hTmeas n).nullMeasurableSet) hTanti ⟨0, measure_ne_top P _⟩
    rwa [hTinter, measure_empty] at h
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.mp hTlimit) (δ / 2)
    (ENNReal.div_pos_iff.mpr ⟨hδ.ne', by simp⟩)
  let K : ℝ := (N : ℝ) + 1
  have hK : 0 < K := by positivity
  have hKtail : P {ω | K < |E ω|} ≤ δ / 2 := by
    refine le_trans (measure_mono fun ω (hω : K < |E ω|) => ?_) (hN N le_rfl)
    show (N : ℝ) < |E ω|
    linarith
  have hbase := hF (ε / K) (div_pos hε hK)
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp hbase) (δ / 2)
    (ENNReal.div_pos_iff.mpr ⟨hδ.ne', by simp⟩)] with i hi
  have hsubset : {ω | ε ≤ ‖E ω * F i ω - E ω * G ω‖} ⊆
      {ω | K < |E ω|} ∪ {ω | ε / K ≤ ‖F i ω - G ω‖} := by
    intro ω hω
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt, not_le] at hnot
    have : ‖E ω * F i ω - E ω * G ω‖ < ε := by
      rw [← mul_sub, norm_mul, Real.norm_eq_abs]
      calc |E ω| * ‖F i ω - G ω‖ ≤ K * ‖F i ω - G ω‖ :=
            mul_le_mul_of_nonneg_right hnot.1 (norm_nonneg _)
        _ < K * (ε / K) := mul_lt_mul_of_pos_left hnot.2 hK
        _ = ε := by field_simp
    exact (not_le.mpr this) hω
  calc P {ω | ε ≤ ‖E ω * F i ω - E ω * G ω‖}
      ≤ P ({ω | K < |E ω|} ∪ {ω | ε / K ≤ ‖F i ω - G ω‖}) := measure_mono hsubset
    _ ≤ P {ω | K < |E ω|} + P {ω | ε / K ≤ ‖F i ω - G ω‖} := measure_union_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add hKtail hi
    _ = δ := ENNReal.add_halves δ

/-- **Error term.** Two families of uniformly close bounded continuous weights have regularized
chaos integrals that are close in probability, uniformly in the cutoff. -/
theorem tendstoInMeasure_regularizedGMC_integral_sub {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ)
    (hXc : IsCircleAverage P X Xc) (γ : ℝ) (u : ℝ → ℂ → ℝ) (v : ℂ → ℝ)
    (hu : ∀ r, Continuous (u r)) (hv : Continuous v) (Cu Cv : ℝ)
    (hub : ∀ r x, |u r x| ≤ Cu) (hvb : ∀ x, |v x| ≤ Cv)
    (huni : ∀ ε > 0, ∀ᶠ r in atTop, ∀ x, |u r x - v x| ≤ ε) (s : ℝ → ℝ) :
    TendstoInMeasure P (fun r ω => ∫ x, u r x ∂regularizedGMC P Xc γ (s r) ω -
      ∫ x, v x ∂regularizedGMC P Xc γ (s r) ω) atTop (fun _ => 0) := by
  have _ := hX.1
  set R : ℝ≥0∞ := gmcReferenceMeasure univ with hRdef
  have hRfin : R ≠ ⊤ := gmcReferenceMeasure_univ_ne_top
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro τ hτ
  by_cases hτtop : τ = ⊤
  · exact Eventually.of_forall fun r => hτtop ▸ le_top
  have hτr : 0 < τ.toReal := ENNReal.toReal_pos hτ.ne' hτtop
  set η : ℝ := ε * (τ.toReal / (R.toReal + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hητ : R * ENNReal.ofReal (η / ε) ≤ τ := by
    rw [hηdef, mul_div_cancel_left₀ _ hε.ne']
    calc R * ENNReal.ofReal (τ.toReal / (R.toReal + 1))
        = ENNReal.ofReal (R.toReal * (τ.toReal / (R.toReal + 1))) := by
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hRfin]
      _ ≤ ENNReal.ofReal τ.toReal := by
          apply ENNReal.ofReal_le_ofReal
          rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
          nlinarith [ENNReal.toReal_nonneg (a := R)]
      _ = τ := ENNReal.ofReal_toReal hτtop
  filter_upwards [huni η hη] with r hr
  set μ : Ω → Measure ℂ := fun ω => regularizedGMC P Xc γ (s r) ω with hμ
  have hfin := regularizedGMC_finite_ae P X hX Xc hXc γ (s r)
  have hmass : Measurable fun ω => μ ω univ :=
    (Measure.measurable_coe MeasurableSet.univ).comp
      (regularizedGMC_measurable P X hX Xc hXc γ (s r))
  have hsub : {ω | ε ≤ ‖(∫ x, u r x ∂μ ω - ∫ x, v x ∂μ ω) - 0‖} ⊆
      {ω | ¬ IsFiniteMeasure (μ ω)} ∪ {ω | ENNReal.ofReal (ε / η) ≤ μ ω univ} := by
    intro ω hω
    by_cases hF : IsFiniteMeasure (μ ω)
    · right
      have hiu : Integrable (u r) (μ ω) := Integrable.of_bound (hu r).aestronglyMeasurable Cu
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hub r x)
      have hiv : Integrable v (μ ω) := Integrable.of_bound hv.aestronglyMeasurable Cv
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hvb x)
      have hD : |∫ x, u r x ∂μ ω - ∫ x, v x ∂μ ω| ≤ η * (μ ω univ).toReal := by
        rw [← integral_sub hiu hiv]
        calc |∫ x, (u r x - v x) ∂μ ω| ≤ ∫ x, |u r x - v x| ∂μ ω :=
              abs_integral_le_integral_abs
          _ ≤ ∫ _x, η ∂μ ω :=
              integral_mono (hiu.sub hiv).abs (integrable_const η) fun x => hr x
          _ = η * (μ ω univ).toReal := by
              rw [integral_const, smul_eq_mul, mul_comm, measureReal_def]
      have hm : μ ω univ ≠ ⊤ := measure_ne_top _ _
      have hω' : ε ≤ |∫ x, u r x ∂μ ω - ∫ x, v x ∂μ ω| := by
        simpa only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs] using hω
      change ENNReal.ofReal (ε / η) ≤ μ ω univ
      rw [ENNReal.ofReal_le_iff_le_toReal hm, div_le_iff₀ hη]
      linarith
    · left
      exact hF
  calc P {ω | ε ≤ ‖(∫ x, u r x ∂μ ω - ∫ x, v x ∂μ ω) - 0‖}
      ≤ P ({ω | ¬ IsFiniteMeasure (μ ω)} ∪ {ω | ENNReal.ofReal (ε / η) ≤ μ ω univ}) :=
        measure_mono hsub
    _ ≤ P {ω | ¬ IsFiniteMeasure (μ ω)} + P {ω | ENNReal.ofReal (ε / η) ≤ μ ω univ} :=
        measure_union_le _ _
    _ = P {ω | ENNReal.ofReal (ε / η) ≤ μ ω univ} := by
        rw [show P {ω | ¬ IsFiniteMeasure (μ ω)} = 0 from ae_iff.mp hfin, zero_add]
    _ ≤ (∫⁻ ω, μ ω univ ∂P) / ENNReal.ofReal (ε / η) :=
        meas_ge_le_lintegral_div hmass.aemeasurable
          (ENNReal.ofReal_pos.mpr (div_pos hε hη)).ne' ENNReal.ofReal_ne_top
    _ = R * ENNReal.ofReal (η / ε) := by
        rw [hμ, regularizedGMC_lintegral_eq_reference P X hX Xc hXc γ (s r) univ
          MeasurableSet.univ, ← hRdef, div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos
          (div_pos hε hη), inv_div]
    _ ≤ τ := hητ

/-- Circle averages of the repinning potential. -/
noncomputable def repinPotentialAvg (a b : ℂ) (s : ℝ) (x : ℂ) : ℝ :=
  ∫ u, repinPotential a b u ∂circleMeasure x s

/-- A circle is the translate of the concentric circle at the origin. -/
theorem circleMeasure_eq_map_add (x : ℂ) (s : ℝ) :
    circleMeasure x s = (circleMeasure 0 s).map (fun u => u + x) := by
  have h := circleMeasure_map_affine 1 x one_ne_zero 0 s
  simp only [one_mul, mul_zero, zero_add, norm_one, Real.log_one, sub_zero] at h
  exact h.symm

theorem integrable_repinPotential_circle (a b : ℂ) (ha : a ≠ 0) (x : ℂ) (s : ℝ) :
    Integrable (repinPotential a b) (circleMeasure x s) := by
  have _ := circleMeasure_isProbability x s
  obtain ⟨B, hB⟩ := exists_abs_repinPotential_le a b ha
  exact Integrable.of_bound (continuous_repinPotential a b ha).aestronglyMeasurable B
    (ae_of_all _ fun u => by rw [Real.norm_eq_abs]; exact hB u)

theorem abs_repinPotentialAvg_le (a b : ℂ) (ha : a ≠ 0) {B : ℝ}
    (hB : ∀ x, |repinPotential a b x| ≤ B) (s : ℝ) (x : ℂ) :
    |repinPotentialAvg a b s x| ≤ B := by
  have _ := circleMeasure_isProbability x s
  unfold repinPotentialAvg
  calc |∫ u, repinPotential a b u ∂circleMeasure x s|
      ≤ ∫ u, |repinPotential a b u| ∂circleMeasure x s := abs_integral_le_integral_abs
    _ ≤ ∫ _u, B ∂circleMeasure x s :=
        integral_mono (integrable_repinPotential_circle a b ha x s).abs (integrable_const B)
          fun u => hB u
    _ = B := by simp

theorem continuous_repinPotentialAvg (a b : ℂ) (ha : a ≠ 0) (s : ℝ) :
    Continuous (repinPotentialAvg a b s) := by
  have _ := circleMeasure_isProbability 0 s
  have hc := continuous_repinPotential a b ha
  have hK : 0 ≤ ‖a‖⁻¹ + 1 := by positivity
  refine (LipschitzWith.of_dist_le_mul (K := ⟨‖a‖⁻¹ + 1, hK⟩) fun x x' => ?_).continuous
  have hrep : ∀ y, repinPotentialAvg a b s y = ∫ u, repinPotential a b (u + y) ∂circleMeasure 0 s :=
    fun y => by
      unfold repinPotentialAvg
      rw [circleMeasure_eq_map_add y s, integral_map (by fun_prop) hc.aestronglyMeasurable]
  have hint : ∀ y, Integrable (fun u => repinPotential a b (u + y)) (circleMeasure 0 s) :=
    fun y => by
      obtain ⟨B, hB⟩ := exists_abs_repinPotential_le a b ha
      exact Integrable.of_bound (hc.comp (continuous_id.add continuous_const)).aestronglyMeasurable
        B (ae_of_all _ fun u => by rw [Real.norm_eq_abs]; exact hB _)
  rw [Real.dist_eq, hrep, hrep, ← integral_sub (hint x) (hint x'), dist_eq_norm]
  calc |∫ u, (repinPotential a b (u + x) - repinPotential a b (u + x')) ∂circleMeasure 0 s|
      ≤ ∫ u, |repinPotential a b (u + x) - repinPotential a b (u + x')| ∂circleMeasure 0 s :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _u, (‖a‖⁻¹ + 1) * ‖x - x'‖ ∂circleMeasure 0 s := by
        refine integral_mono ((hint x).sub (hint x')).abs (integrable_const _) fun u => ?_
        have := abs_repinPotential_sub_le a b ha (u + x) (u + x')
        rwa [show u + x - (u + x') = x - x' by ring] at this
    _ = (‖a‖⁻¹ + 1) * ‖x - x'‖ := by rw [integral_const, probReal_univ, one_smul]

/-- The exponential tilt weights converge uniformly. -/
theorem eventually_abs_exp_repinPotentialAvg_sub_le (a b : ℂ) (ha : a ≠ 0) (γ : ℝ) :
    ∀ ε > 0, ∀ᶠ s in atTop, ∀ x, |Real.exp (γ ^ 2 * repinPotentialAvg a b s x) -
      Real.exp (γ ^ 2 * repinPotential a b x)| ≤ ε := by
  intro ε hε
  obtain ⟨B, hB⟩ := exists_abs_repinPotential_le a b ha
  set κ := γ ^ 2 + 1 with hκ
  have hκpos : 0 < κ := by positivity
  set A := Real.exp (γ ^ 2 * B) with hA
  have hA0 : 0 < A := Real.exp_pos _
  set δ := min (1 / κ) (ε / (2 * κ * A)) with hδ
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  have hu := tendstoUniformly_repinPotential a b ha
  rw [Metric.tendstoUniformly_iff] at hu
  filter_upwards [hu δ hδpos] with s hs x
  have hdist : |repinPotentialAvg a b s x - repinPotential a b x| < δ := by
    have := hs x
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this
  have hsmall : |γ ^ 2 * (repinPotentialAvg a b s x - repinPotential a b x)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg γ)]
    calc γ ^ 2 * |repinPotentialAvg a b s x - repinPotential a b x| ≤ κ * δ :=
          mul_le_mul (by linarith) hdist.le (abs_nonneg _) hκpos.le
      _ ≤ κ * (1 / κ) := mul_le_mul_of_nonneg_left (min_le_left _ _) hκpos.le
      _ = 1 := by field_simp
  have hexp := Real.abs_exp_sub_one_le hsmall
  have hcB : Real.exp (γ ^ 2 * repinPotential a b x) ≤ A :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hB x)) (sq_nonneg γ))
  rw [show γ ^ 2 * repinPotentialAvg a b s x =
      γ ^ 2 * repinPotential a b x + γ ^ 2 * (repinPotentialAvg a b s x - repinPotential a b x)
    by ring, Real.exp_add, ← mul_sub_one, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (γ ^ 2 * repinPotential a b x) *
        |Real.exp (γ ^ 2 * (repinPotentialAvg a b s x - repinPotential a b x)) - 1|
      ≤ A * (2 * |γ ^ 2 * (repinPotentialAvg a b s x - repinPotential a b x)|) :=
        mul_le_mul hcB hexp (abs_nonneg _) (Real.exp_pos _).le
    _ ≤ A * (2 * (κ * δ)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ two_pos.le) hA0.le
        rw [abs_mul, abs_of_nonneg (sq_nonneg γ)]
        exact mul_le_mul (by linarith) hdist.le (abs_nonneg _) hκpos.le
    _ ≤ A * (2 * (κ * (ε / (2 * κ * A)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (min_le_right _ _) hκpos.le) two_pos.le) hA0.le
    _ = ε := by field_simp

/-- A constant family converges in measure to its constant. -/
theorem tendstoInMeasure_zero_const {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (l : Filter ι) : TendstoInMeasure P (fun (_ : ι) (_ : Ω) => (0 : ℝ)) l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  simp only [sub_self, norm_zero]
  have : {x : Ω | ε ≤ 0} = ∅ := by
    ext x
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
    exact hε
  simp only [this, measure_empty]
  exact tendsto_const_nhds

/-- **The repinned chaos is the GMC of the repinned field.** -/
theorem isGMCOf_repinChaos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (M : Ω → Measure ℂ) (hMfin : ∀ ω, IsFiniteMeasure (M ω))
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (hconv : ∀ f : BoundedContinuousFunction ℂ ℝ, TendstoInMeasure P
      (fun r ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) atTop (fun ω => ∫ x, f x ∂M ω))
    (a b : ℂ) (ha : a ≠ 0) :
    IsGMCOf P (repinField X (fun ω => Xc ω b (-Real.log ‖a‖)) a b) γ
      (repinChaos M (fun ω => Xc ω b (-Real.log ‖a‖)) a b γ
        (∫ ω, Xc ω b (-Real.log ‖a‖) ^ 2 ∂P)) := by
  have _ := hX.1
  set L : Ω → ℝ := fun ω => Xc ω b (-Real.log ‖a‖) with hLdef
  set VL : ℝ := ∫ ω, L ω ^ 2 ∂P with hVL
  have hLmeas : Measurable L :=
    (hXc.1 (-Real.log ‖a‖)).comp (measurable_id.prodMk measurable_const)
  refine ⟨fun ω => isFiniteMeasure_repinChaos M L a b ha γ VL ω, repinCircle Xc L a b,
    isCircleAverage_repinField P X Xc a b hX hXc ha, fun f => ?_⟩
  obtain ⟨B, hB⟩ := exists_abs_repinPotential_le a b ha
  set W : ℝ := (‖a‖ + ‖b‖ + 1) ^ (4 : ℝ) / ‖a‖ ^ 2 with hW
  set E : Ω → ℝ := fun ω => Real.exp (-γ * L ω - γ ^ 2 / 2 * VL) with hE
  have hEmeas : Measurable E :=
    Real.measurable_exp.comp ((hLmeas.const_mul (-γ)).sub measurable_const)
  have hK : ∀ s x, ∫ ω', Xc ω' x s * L ω' ∂P = repinPotentialAvg a b s x := fun s x =>
    isCircleAverage_covariance P X hX Xc hXc x b s (-Real.log ‖a‖)
  set u : ℝ → ℂ → ℝ := fun r x => f (affineInv a b x) *
    Real.exp (γ ^ 2 * repinPotentialAvg a b (r - Real.log ‖a‖) x) * repinWeight a b x with hu
  set v : ℂ → ℝ := fun x => f (affineInv a b x) *
    Real.exp (γ ^ 2 * repinPotential a b x) * repinWeight a b x with hv
  have hid : ∀ r ω, ∫ y, f y ∂regularizedGMC P (repinCircle Xc L a b) γ r ω =
      E ω * ∫ x, u r x ∂regularizedGMC P Xc γ (r - Real.log ‖a‖) ω := fun r ω => by
    rw [integral_regularizedGMC_repinCircle P Xc L hXc.1 hLmeas hXc.2.1 (hXc.2.1 b _) a b ha γ
      r ω f]
    simp_rw [hK]
    rfl
  have hlim : ∀ ω, ∫ y, f y ∂repinChaos M L a b γ VL ω = E ω * ∫ x, v x ∂M ω := fun ω =>
    integral_repinChaos M L a b ha γ VL ω f.continuous
  have hWnn : 0 ≤ W := by rw [hW]; positivity
  have hwb : ∀ x, |repinWeight a b x| ≤ W := fun x => by
    rw [abs_of_pos (repinWeight_pos a b ha x)]
    exact repinWeight_le a b ha x
  have hexpb : ∀ t, |t| ≤ B → |Real.exp (γ ^ 2 * t)| ≤ Real.exp (γ ^ 2 * B) := fun t ht => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ((le_abs_self t).trans ht)
      (sq_nonneg γ))
  have hfb : ∀ y, |f y| ≤ ‖f‖ := fun y => by
    rw [← Real.norm_eq_abs]
    exact f.norm_coe_le_norm y
  have hcont_fi : Continuous fun x => f (affineInv a b x) :=
    f.continuous.comp (continuous_affineInv a b)
  have hv_cont : Continuous v := (hcont_fi.mul ((continuous_const.mul
    (continuous_repinPotential a b ha)).rexp)).mul (continuous_repinWeight a b ha)
  have hu_cont : ∀ r, Continuous (u r) := fun r => (hcont_fi.mul ((continuous_const.mul
    (continuous_repinPotentialAvg a b ha _)).rexp)).mul (continuous_repinWeight a b ha)
  have hbound : ∀ (t : ℝ) (x : ℂ), |t| ≤ B →
      |f (affineInv a b x) * Real.exp (γ ^ 2 * t) * repinWeight a b x| ≤
        ‖f‖ * Real.exp (γ ^ 2 * B) * W := fun t x ht => by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hfb _) (hexpb t ht) (abs_nonneg _) (norm_nonneg _))
      (hwb x) (abs_nonneg _) (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
  have hv_bd : ∀ x, |v x| ≤ ‖f‖ * Real.exp (γ ^ 2 * B) * W := fun x => hbound _ x (hB x)
  have hu_bd : ∀ r x, |u r x| ≤ ‖f‖ * Real.exp (γ ^ 2 * B) * W := fun r x =>
    hbound _ x (abs_repinPotentialAvg_le a b ha hB _ x)
  have hshift : Tendsto (fun r : ℝ => r - Real.log ‖a‖) atTop atTop :=
    tendsto_atTop_atTop.2 fun c => ⟨c + Real.log ‖a‖, fun r hr => by linarith⟩
  have huni : ∀ ε > 0, ∀ᶠ r in atTop, ∀ x, |u r x - v x| ≤ ε := by
    intro ε hε
    have hfW : 0 < ‖f‖ * W + 1 := by positivity
    filter_upwards [hshift.eventually (eventually_abs_exp_repinPotentialAvg_sub_le a b ha γ
      (ε / (‖f‖ * W + 1)) (div_pos hε hfW))] with r hr x
    have hx := hr x
    rw [show u r x - v x = f (affineInv a b x) * repinWeight a b x *
        (Real.exp (γ ^ 2 * repinPotentialAvg a b (r - Real.log ‖a‖) x) -
          Real.exp (γ ^ 2 * repinPotential a b x)) by simp only [hu, hv]; ring,
      abs_mul, abs_mul]
    calc |f (affineInv a b x)| * |repinWeight a b x| *
          |Real.exp (γ ^ 2 * repinPotentialAvg a b (r - Real.log ‖a‖) x) -
            Real.exp (γ ^ 2 * repinPotential a b x)|
        ≤ ‖f‖ * W * (ε / (‖f‖ * W + 1)) :=
          mul_le_mul (mul_le_mul (hfb _) (hwb x) (abs_nonneg _) (norm_nonneg _)) hx
            (abs_nonneg _) (mul_nonneg (norm_nonneg _) hWnn)
      _ ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ hfW]
          nlinarith [mul_nonneg (norm_nonneg f) hWnn]
  set V : BoundedContinuousFunction ℂ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup v
    hv_cont _ (fun x => by rw [Real.norm_eq_abs]; exact hv_bd x) with hVdef
  have h1 : TendstoInMeasure P (fun r ω => ∫ x, v x ∂regularizedGMC P Xc γ
      (r - Real.log ‖a‖) ω) atTop (fun ω => ∫ x, v x ∂M ω) := (hconv V).comp hshift
  have h2 := tendstoInMeasure_regularizedGMC_integral_sub P X hX Xc hXc γ u v hu_cont hv_cont
    _ _ hu_bd hv_bd huni (fun r => r - Real.log ‖a‖)
  have h2' := tendstoInMeasure_sub P _ _ _ _ (tendstoInMeasure_zero_const P atTop) h2
  have h3 := tendstoInMeasure_sub P _ _ _ _ h1 h2'
  have h4 := tendstoInMeasure_const_mul E hEmeas h3
  refine (h4.congr_left fun r => ae_of_all _ fun ω => ?_).congr_right (ae_of_all _ fun ω => ?_)
  · rw [hid r ω]
    ring
  · change _ = ∫ x, f x ∂repinChaos M L a b γ VL ω
    rw [hlim ω]
    ring

end DOZZ.Proofs

end
