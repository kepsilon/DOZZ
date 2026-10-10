/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.BarrierCauchy

/-! Omitted coarse barriers of two separated roots for one admissible regularization: self-compatibility, a charge-uniform double-root barrier tail, and truncation of the growing barrier at a fixed level. -/

@[expose] public section

/-! ### Self-compatibility

An admissible logarithmic regularization is compatible with itself, so the mixed-family
barrier estimates apply to one regularization with independently varying cutoffs. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Assembly

open DOZZ.Proofs

/-- Every admissible regularization is compatible with itself. -/
theorem isCompatibleAdmissibleRegularizations_self
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) :
    IsCompatibleAdmissibleRegularizations P U ε₀ ε₀ Y Y := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n q hq
    have h := hY.gaussian n (fun i => (q i).2)
      (fun i => ⟨(hq i).1, (hq i).2.trans (min_le_left _ _)⟩)
    simpa only [ite_self] using h
  · intro K hK hKU
    obtain ⟨C, hC, hcov⟩ := hY.covarianceBound K hK hKU
    exact ⟨C, hC, fun ε δ hε hεc hδ hδc x hx y hy => hcov ε δ hε hεc hδ hδc x hx y hy⟩
  · intro K hK hKU
    obtain ⟨C, hC, hmix⟩ := hY.coarseMixedBound K hK hKU
    exact ⟨C, hC, fun k hk ε hε hεk x hx =>
      hmix k hk ε hε (hεk.trans (min_le_right _ _)) x hx⟩
  · intro K _ _ s _ η hη
    exact ⟨1, one_pos, fun ε δ' _ _ _ _ x _ y _ _ => by simp [hη]⟩
  · intro K _ _ k _ η hη
    exact ⟨1, one_pos, fun ε _ _ x _ y _ => by simp [hη]⟩

end DOZZ.Assembly

/-! ### Charge-uniform double-root tail

Omitted coarse barriers for two separated Wick roots of one admissible regularization.

The threshold on the coarse scale is linear in the charge, so the estimate is uniform when the
charge ranges over a compact interval below the barrier slope. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Assembly

open DOZZ.Proofs

/-- Two separated Wick roots of one admissible regularization: the first root's coarse barrier at
scale `k` fails with exponentially small weight. The constant `C` depends only on the
regularization and the compact chart, and the scale condition is explicit in the charge. -/
theorem admissible_separated_double_root_tail_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, C < (k : ℝ) → Real.exp (-(k : ℝ)) ≤ ε₀ →
      ∀ x ∈ K, ∀ y ∈ K, ∀ L : ℝ, 0 < ‖x - y‖ → Real.log (1 / ‖x - y‖) ≤ L →
      ∀ ε δ : ℝ, 0 < ε → ε ≤ Real.exp (-(k : ℝ)) → 0 < δ → δ ≤ ε₀ →
      ∀ g a : ℝ, 0 < g → g < a → g * (|L| + 2 * C) ≤ (a - g) * (k : ℝ) / 2 →
      ∫⁻ ω, admissibleLogWickWeight P Y g ε x ω * admissibleLogWickWeight P Y g δ y ω *
          Set.indicator {ω | a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) x}
            (fun _ => (1 : ℝ≥0∞)) ω ∂P ≤
        ENNReal.ofReal (Real.exp (g ^ 2 * (L + C))) *
          ENNReal.ofReal (Real.exp (-((a - g) ^ 2 * (k : ℝ) / 16))) := by
  obtain ⟨Cv, hCv, hvar⟩ := hY.coarseVarianceBound K hK hKU
  obtain ⟨Cm, hCm, hmix⟩ := hY.coarseMixedBound K hK hKU
  obtain ⟨Cc, hCc, hcov⟩ := hY.covarianceBound K hK hKU
  refine ⟨max Cv (max Cm Cc), le_max_of_le_left hCv, ?_⟩
  intro k hkC hkcut x hx y hy L hxy hL ε δ hε hεk hδ hδcut g a hg hga hgap
  set C := max Cv (max Cm Cc) with hCdef
  have hCv' : Cv ≤ C := le_max_left _ _
  have hCm' : Cm ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCc' : Cc ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  have hC0 : 0 ≤ C := le_trans hCv hCv'
  have hεcut : ε ≤ ε₀ := hεk.trans hkcut
  have hkpos : 0 < (k : ℝ) := lt_of_le_of_lt hC0 hkC
  let q : Fin 3 → ℝ × ℂ := fun i =>
    if i = 0 then (Real.exp (-(k : ℝ)), x) else if i = 1 then (ε, x) else (δ, y)
  let V : Ω → Fin 3 → ℝ := fun ω i => Y ω (q i).1 (q i).2
  have hV : IsCenteredJointlyGaussian P V := by
    apply hY.gaussian 3 q
    intro i
    fin_cases i
    · exact ⟨Real.exp_pos _, hkcut⟩
    · exact ⟨hε, hεcut⟩
    · exact ⟨hδ, hδcut⟩
  have hV0 : (fun ω => V ω 0) = fun ω => Y ω (Real.exp (-(k : ℝ))) x := by
    funext ω; simp [V, q]
  have hV1 : (fun ω => V ω 1) = fun ω => Y ω ε x := by
    funext ω; simp [V, q]
  have hV2 : (fun ω => V ω 2) = fun ω => Y ω δ y := by
    funext ω; simp [V, q]
  -- covariance estimates for the three coordinates
  have hvarV : |gaussianVariance P (fun ω => V ω 0) - (k : ℝ)| ≤ C := by
    rw [hV0]; exact (hvar k hkcut x hx).trans hCv'
  have hcov01 : gaussianCovariance P (fun ω => V ω 0) (fun ω => V ω 1) ≤ (k : ℝ) + C := by
    rw [hV0, hV1]
    have h := (abs_le.mp ((hmix k hkcut ε hε hεk x hx).trans hCm')).2
    linarith
  have hlogmax (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
      Real.log (1 / max ‖x - y‖ (max u v)) ≤ L := by
    have hρpos : 0 < max ‖x - y‖ (max u v) := lt_of_lt_of_le hxy (le_max_left _ _)
    have harg : 1 / max ‖x - y‖ (max u v) ≤ 1 / ‖x - y‖ :=
      one_div_le_one_div_of_le hxy (le_max_left _ _)
    have _ := hu; have _ := hv
    exact (Real.log_le_log (one_div_pos.mpr hρpos) harg).trans hL
  have hcov02 : gaussianCovariance P (fun ω => V ω 0) (fun ω => V ω 2) ≤ L + C := by
    rw [hV0, hV2]
    have h := (abs_le.mp ((hcov (Real.exp (-(k : ℝ))) δ (Real.exp_pos _) hkcut hδ hδcut
      x hx y hy).trans hCc')).2
    have hl := hlogmax (Real.exp (-(k : ℝ))) δ (Real.exp_pos _) hδ
    linarith
  have hcov12 : gaussianCovariance P (fun ω => V ω 1) (fun ω => V ω 2) ≤ L + C := by
    rw [hV1, hV2]
    have h := (abs_le.mp ((hcov ε δ hε hεcut hδ hδcut x hx y hy).trans hCc')).2
    have hl := hlogmax ε δ hε hδ
    linarith
  -- the two-root tilt identity and the tilted Gaussian tail
  let B : Ω → ℝ≥0∞ := fun ω =>
    Set.indicator {ω | a * (k : ℝ) < V ω 0} (fun _ => (1 : ℝ≥0∞)) ω
  have hident := finite_gaussian_two_root_wick_tilt_integral_identity P V 1 2
    (by decide) g B
  let tilt : Fin 3 → ℝ := twoRootTilt 1 2 g
  have hmean : (∑ j : Fin 3, gaussianCovariance P (fun ω => V ω 0)
      (fun ω => V ω j) * tilt j) =
      g * gaussianCovariance P (fun ω => V ω 0) (fun ω => V ω 1) +
        g * gaussianCovariance P (fun ω => V ω 0) (fun ω => V ω 2) := by
    simp [Fin.sum_univ_three, tilt, twoRootTilt]
    ring
  have hmUpper : (∑ j : Fin 3, gaussianCovariance P (fun ω => V ω 0)
      (fun ω => V ω j) * tilt j) ≤ g * (k : ℝ) + g * (|L| + 2 * C) := by
    rw [hmean]
    have h1 := mul_le_mul_of_nonneg_left hcov01 hg.le
    have h2 := mul_le_mul_of_nonneg_left hcov02 hg.le
    have hLabs : L ≤ |L| := le_abs_self L
    have h3 : g * L ≤ g * |L| := mul_le_mul_of_nonneg_left hLabs hg.le
    linarith only [h1, h2, h3]
  have hgapStrict : (∑ j : Fin 3, gaussianCovariance P (fun ω => V ω 0)
      (fun ω => V ω j) * tilt j) < a * (k : ℝ) := by
    have hpos : 0 < (a - g) * (k : ℝ) / 2 := by
      have := sub_pos.mpr hga
      positivity
    linarith only [hmUpper, hgap, hpos]
  have hvpos : 0 < gaussianVariance P (fun ω => V ω 0) := by
    have h := (abs_le.mp hvarV).1
    linarith
  have hvle : gaussianVariance P (fun ω => V ω 0) ≤ 2 * (k : ℝ) := by
    have h := (abs_le.mp hvarV).2
    linarith
  have htail := finite_gaussian_tilt_barrier_tail_bound P V hV tilt 0 (a * (k : ℝ))
    hgapStrict hvpos
  have hrate := gaussian_barrier_tail_rate a g (g * (|L| + 2 * C))
    (∑ j : Fin 3, gaussianCovariance P (fun ω => V ω 0) (fun ω => V ω j) * tilt j)
    (gaussianVariance P (fun ω => V ω 0)) (k : ℝ) hga hkpos hgap hmUpper hvpos hvle
  have hfactor : ENNReal.ofReal (Real.exp (g ^ 2 * gaussianCovariance P
      (fun ω => V ω 1) (fun ω => V ω 2))) ≤ ENNReal.ofReal (Real.exp (g ^ 2 * (L + C))) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hcov12 (sq_nonneg g)
  have htilted : ∫⁻ ω, ENNReal.ofReal (Real.exp
        ((∑ i, twoRootTilt 1 2 g i * V ω i) -
          (∑ i, ∑ j, twoRootTilt 1 2 g i *
            gaussianCovariance P (fun ω => V ω i) (fun ω => V ω j) *
            twoRootTilt 1 2 g j) / 2)) * B ω ∂P ≤
      ENNReal.ofReal (Real.exp (-((a - g) ^ 2 * (k : ℝ) / 16))) := by
    refine le_trans htail ?_
    apply ENNReal.ofReal_le_ofReal
    simpa using hrate
  have hgoal : ∫⁻ ω, admissibleLogWickWeight P Y g ε x ω *
        admissibleLogWickWeight P Y g δ y ω *
        Set.indicator {ω | a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) x}
          (fun _ => (1 : ℝ≥0∞)) ω ∂P =
      ∫⁻ ω, ENNReal.ofReal (Real.exp
          (g * V ω 1 - g ^ 2 / 2 * gaussianVariance P (fun ω => V ω 1))) *
        ENNReal.ofReal (Real.exp
          (g * V ω 2 - g ^ 2 / 2 * gaussianVariance P (fun ω => V ω 2))) * B ω ∂P := by
    rw [hV1, hV2]
    rfl
  rw [hgoal, hident]
  exact mul_le_mul' hfactor htilted

end DOZZ.Assembly

/-! ### Truncating the growing barrier

Truncating the growing barrier at a fixed coarse level costs only the omitted barriers.

For two separated roots the omitted barriers have an exponentially small total weight, with a
threshold that is uniform for charges in a compact interval below the barrier slope. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Assembly

open DOZZ.Proofs

/-- Some coarse barrier strictly above level `m` and at most `r` fails at the point `x`. -/
def omittedBarrierEvent {Ω : Type*} (Y : Ω → ℝ → ℂ → ℝ) (a : ℝ) (m : ℕ) (r : ℝ)
    (x : ℂ) : Set Ω :=
  {ω | ∃ k : ℕ, m < k ∧ (k : ℝ) ≤ r ∧ a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) x}

/-- The growing barrier through level `r` holds whenever the level-`m` barrier holds and no
omitted barrier between `m` and `r` fails. -/
theorem mem_admissibleGrowingBarrierSet_of_not_omitted
    {Ω : Type*} (Y : Ω → ℝ → ℂ → ℝ) (a : ℝ) (k₀ m : ℕ) (r : ℝ) (ω : Ω) (x : ℂ)
    (hm : (ω, x) ∈ admissibleGrowingBarrierSet Y a k₀ (m : ℝ))
    (hno : ω ∉ omittedBarrierEvent Y a m r x) :
    (ω, x) ∈ admissibleGrowingBarrierSet Y a k₀ r := by
  intro k hk₀ hkr
  by_cases hkm : k ≤ m
  · exact hm k hk₀ (by exact_mod_cast hkm)
  · by_contra hbad
    exact hno ⟨k, Nat.lt_of_not_le hkm, hkr, lt_of_not_ge hbad⟩

/-- Pointwise comparison of barrier indicators at two roots. -/
theorem barrier_indicator_pair_le
    {Ω : Type*} (Y : Ω → ℝ → ℂ → ℝ) (a : ℝ) (k₀ m : ℕ) (r s : ℝ) (ω : Ω) (x y : ℂ) :
    Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ)) (fun _ => (1 : ℝ≥0∞)) (ω, x) *
        Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ))
          (fun _ => (1 : ℝ≥0∞)) (ω, y) ≤
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ r) (fun _ => (1 : ℝ≥0∞)) (ω, x) *
          Set.indicator (admissibleGrowingBarrierSet Y a k₀ s) (fun _ => (1 : ℝ≥0∞)) (ω, y) +
        Set.indicator (omittedBarrierEvent Y a m r x) (fun _ => (1 : ℝ≥0∞)) ω +
        Set.indicator (omittedBarrierEvent Y a m s y) (fun _ => (1 : ℝ≥0∞)) ω := by
  classical
  by_cases hmx : (ω, x) ∈ admissibleGrowingBarrierSet Y a k₀ (m : ℝ)
  · by_cases hmy : (ω, y) ∈ admissibleGrowingBarrierSet Y a k₀ (m : ℝ)
    · rw [Set.indicator_of_mem hmx, Set.indicator_of_mem hmy, one_mul]
      by_cases hox : ω ∈ omittedBarrierEvent Y a m r x
      · rw [Set.indicator_of_mem hox]
        exact le_trans le_add_self le_self_add
      · by_cases hoy : ω ∈ omittedBarrierEvent Y a m s y
        · rw [Set.indicator_of_mem hoy]
          exact le_add_self
        · have hrx := mem_admissibleGrowingBarrierSet_of_not_omitted Y a k₀ m r ω x hmx hox
          have hsy := mem_admissibleGrowingBarrierSet_of_not_omitted Y a k₀ m s ω y hmy hoy
          rw [Set.indicator_of_mem hrx, Set.indicator_of_mem hsy, one_mul]
          exact le_trans le_self_add le_self_add
    · simp [Set.indicator_of_notMem hmy]
  · simp [Set.indicator_of_notMem hmx]

/-- The Wick weight is measurable in the sample at each fixed point. -/
theorem admissibleLogWickWeight_measurable_sample
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (g ε : ℝ) (x : ℂ) :
    Measurable (fun ω => admissibleLogWickWeight P Y g ε x ω) := by
  have hfield : Measurable (fun ω => Y ω ε x) :=
    (hY.measurableAtScale ε).comp (measurable_id.prodMk measurable_const)
  unfold admissibleLogWickWeight
  fun_prop

/-- The coarse field at a fixed point is measurable in the sample. -/
theorem admissible_field_measurable_sample
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (ε : ℝ) (x : ℂ) :
    Measurable (fun ω => Y ω ε x) :=
  (hY.measurableAtScale ε).comp (measurable_id.prodMk measurable_const)

/-- Countable union bound for the omitted barriers at one root. -/
theorem lintegral_wick_pair_omitted_le_tsum
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (w : Ω → ℝ≥0∞) (hw : Measurable w) (a : ℝ) (m : ℕ) (r : ℝ) (x : ℂ) :
    ∫⁻ ω, w ω * Set.indicator (omittedBarrierEvent Y a m r x) (fun _ => (1 : ℝ≥0∞)) ω ∂P ≤
      ∑' k : ℕ, Set.indicator {k : ℕ | m < k ∧ (k : ℝ) ≤ r}
        (fun k => ∫⁻ ω, w ω * Set.indicator
          {ω | a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) x} (fun _ => (1 : ℝ≥0∞)) ω ∂P) k := by
  classical
  let bad : ℕ → Ω → Prop := fun k ω =>
    m < k ∧ (k : ℝ) ≤ r ∧ a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) x
  have hset (k : ℕ) : MeasurableSet {ω | bad k ω} := by
    have hlt : MeasurableSet {ω | a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) x} :=
      measurableSet_lt measurable_const
        (admissible_field_measurable_sample P U dens ε₀ Y hY _ x)
    by_cases hk : m < k ∧ (k : ℝ) ≤ r
    · have hEq : {ω | bad k ω} = {ω | a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) x} := by
        ext ω; simp [bad, hk]
      rw [hEq]; exact hlt
    · have hEq : {ω | bad k ω} = ∅ :=
        Set.eq_empty_of_forall_notMem fun ω h => hk ⟨h.1, h.2.1⟩
      rw [hEq]; exact MeasurableSet.empty
  have hmeas (k : ℕ) : AEMeasurable (fun ω => w ω *
      Set.indicator {ω | bad k ω} (fun _ => (1 : ℝ≥0∞)) ω) P :=
    (hw.mul (measurable_const.indicator (hset k))).aemeasurable
  have hbound := lintegral_mul_indicator_exists_le_tsum P w bad hmeas
  have hevent : {ω | ∃ k, bad k ω} = omittedBarrierEvent Y a m r x := by
    ext ω; simp [bad, omittedBarrierEvent]
  rw [hevent] at hbound
  refine hbound.trans (le_of_eq (tsum_congr fun k => ?_))
  by_cases hk : m < k ∧ (k : ℝ) ≤ r
  · have hEq : {ω | bad k ω} = {ω | a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) x} := by
      ext ω; simp [bad, hk]
    rw [hEq, Set.indicator_of_mem (show k ∈ {k : ℕ | m < k ∧ (k : ℝ) ≤ r} from hk)]
  · have hEq : {ω | bad k ω} = ∅ :=
      Set.eq_empty_of_forall_notMem fun ω h => hk ⟨h.1, h.2.1⟩
    rw [hEq, Set.indicator_of_notMem (show k ∉ {k : ℕ | m < k ∧ (k : ℝ) ≤ r} from hk)]
    simp

/-- Reindex a tail sum supported strictly above `m`. -/
theorem tsum_indicator_gt_le_tsum_nat_add (m : ℕ) (T f : ℕ → ℝ≥0∞) (S : Set ℕ)
    (hS : S ⊆ {k | m < k}) (hT : ∀ k ∈ S, T k ≤ f k) :
    ∑' k : ℕ, Set.indicator S T k ≤ ∑' j : ℕ, f (j + (m + 1)) := by
  classical
  have hle : ∀ k, Set.indicator S T k ≤ Set.indicator {k | m < k} f k := by
    intro k
    by_cases hk : k ∈ S
    · rw [Set.indicator_of_mem hk, Set.indicator_of_mem (hS hk)]
      exact hT k hk
    · rw [Set.indicator_of_notMem hk]
      exact zero_le
  refine (ENNReal.tsum_le_tsum hle).trans (le_of_eq ?_)
  have hinj : Function.Injective (fun j : ℕ => j + (m + 1)) := fun i j h => by
    simpa using h
  have hsupp : Function.support (Set.indicator {k : ℕ | m < k} f) ⊆
      Set.range (fun j : ℕ => j + (m + 1)) := by
    intro k hk
    have hkm : m < k := by
      by_contra h
      exact hk (Set.indicator_of_notMem h f)
    exact ⟨k - (m + 1), by show k - (m + 1) + (m + 1) = k; omega⟩
  rw [← hinj.tsum_eq hsupp]
  apply tsum_congr
  intro j
  rw [Set.indicator_of_mem (show j + (m + 1) ∈ {k : ℕ | m < k} from
    show m < j + (m + 1) by omega)]

/-- Truncating the growing barrier of a separated root pair at level `m` costs at most the
summed omitted-barrier tails. The constant depends only on the regularization and chart. -/
theorem finiteBarrierPairKernel_le_growing_add_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k₀ m : ℕ, C < (m : ℝ) → Real.exp (-(m : ℝ)) ≤ ε₀ →
      ∀ r s : ℝ, (m : ℝ) ≤ r → (m : ℝ) ≤ s →
      ∀ x ∈ K, ∀ y ∈ K, ∀ L : ℝ, 0 < ‖x - y‖ → Real.log (1 / ‖x - y‖) ≤ L →
      ∀ g a : ℝ, 0 < g → g < a → g * (|L| + 2 * C) ≤ (a - g) * (m : ℝ) / 2 →
      compatibleAdmissibleSelectedFiniteBarrierPairKernel P Y Y g a k₀ m
          (Real.exp (-r)) (Real.exp (-s)) x y true true ≤
        compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel P Y Y g a k₀ r s x y
            true true +
          2 * (ENNReal.ofReal (Real.exp (g ^ 2 * (L + C))) *
            ∑' j : ℕ, ENNReal.ofReal
              (Real.exp (-((a - g) ^ 2 * ((j + (m + 1) : ℕ) : ℝ) / 16)))) := by
  classical
  obtain ⟨C, hC, htail⟩ := admissible_separated_double_root_tail_uniform P U dens ε₀ Y hY K hK hKU
  refine ⟨C, hC, ?_⟩
  intro k₀ m hmC hmcut r s hmr hms x hx y hy L hxy hL g a hg hga hgap
  let Wx : Ω → ℝ≥0∞ := fun ω => admissibleLogWickWeight P Y g (Real.exp (-r)) x ω
  let Wy : Ω → ℝ≥0∞ := fun ω => admissibleLogWickWeight P Y g (Real.exp (-s)) y ω
  have hWx : Measurable Wx := admissibleLogWickWeight_measurable_sample P U dens ε₀ Y hY g _ x
  have hWy : Measurable Wy := admissibleLogWickWeight_measurable_sample P U dens ε₀ Y hY g _ y
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (g ^ 2 * (L + C)))
  let f : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (Real.exp (-((a - g) ^ 2 * (k : ℝ) / 16)))
  -- monotonicity of the scale conditions above `m`
  have hscale (k : ℕ) (hk : m < k) :
      C < (k : ℝ) ∧ Real.exp (-(k : ℝ)) ≤ ε₀ ∧
        g * (|L| + 2 * C) ≤ (a - g) * (k : ℝ) / 2 := by
    have hkm : (m : ℝ) ≤ k := by exact_mod_cast hk.le
    refine ⟨lt_of_lt_of_le hmC hkm, le_trans (Real.exp_le_exp.mpr (by linarith)) hmcut, ?_⟩
    have hag : 0 ≤ a - g := (sub_pos.mpr hga).le
    linarith only [hgap, mul_le_mul_of_nonneg_left hkm hag]
  have hlogyx : Real.log (1 / ‖y - x‖) ≤ L := by rwa [norm_sub_rev]
  have hxy' : 0 < ‖y - x‖ := by rwa [norm_sub_rev]
  -- the omitted-barrier sums at both roots
  have hfirst : ∫⁻ ω, Wx ω * Wy ω *
      Set.indicator (omittedBarrierEvent Y a m r x) (fun _ => (1 : ℝ≥0∞)) ω ∂P ≤
      c * ∑' j : ℕ, f (j + (m + 1)) := by
    refine (lintegral_wick_pair_omitted_le_tsum P U dens ε₀ Y hY (fun ω => Wx ω * Wy ω)
      (hWx.mul hWy) a m r x).trans ?_
    have hT := tsum_indicator_gt_le_tsum_nat_add m
      (fun k => ∫⁻ ω, Wx ω * Wy ω * Set.indicator
        {ω | a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) x} (fun _ => (1 : ℝ≥0∞)) ω ∂P)
      (fun k => c * f k) {k : ℕ | m < k ∧ (k : ℝ) ≤ r} (fun k hk => hk.1) (by
        intro k hk
        obtain ⟨hkC, hkcut, hkgap⟩ := hscale k hk.1
        have hrk : Real.exp (-r) ≤ Real.exp (-(k : ℝ)) := Real.exp_le_exp.mpr (by linarith [hk.2])
        have hscut : Real.exp (-s) ≤ ε₀ :=
          le_trans (Real.exp_le_exp.mpr (by linarith)) hmcut
        exact htail k hkC hkcut x hx y hy L hxy hL (Real.exp (-r)) (Real.exp (-s))
          (Real.exp_pos _) hrk (Real.exp_pos _) hscut g a hg hga hkgap)
    refine hT.trans (le_of_eq ?_)
    rw [ENNReal.tsum_mul_left]
  have hsecond : ∫⁻ ω, Wx ω * Wy ω *
      Set.indicator (omittedBarrierEvent Y a m s y) (fun _ => (1 : ℝ≥0∞)) ω ∂P ≤
      c * ∑' j : ℕ, f (j + (m + 1)) := by
    refine (lintegral_wick_pair_omitted_le_tsum P U dens ε₀ Y hY (fun ω => Wx ω * Wy ω)
      (hWx.mul hWy) a m s y).trans ?_
    have hT := tsum_indicator_gt_le_tsum_nat_add m
      (fun k => ∫⁻ ω, Wx ω * Wy ω * Set.indicator
        {ω | a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) y} (fun _ => (1 : ℝ≥0∞)) ω ∂P)
      (fun k => c * f k) {k : ℕ | m < k ∧ (k : ℝ) ≤ s} (fun k hk => hk.1) (by
        intro k hk
        obtain ⟨hkC, hkcut, hkgap⟩ := hscale k hk.1
        have hsk : Real.exp (-s) ≤ Real.exp (-(k : ℝ)) := Real.exp_le_exp.mpr (by linarith [hk.2])
        have hrcut : Real.exp (-r) ≤ ε₀ :=
          le_trans (Real.exp_le_exp.mpr (by linarith)) hmcut
        have h := htail k hkC hkcut y hy x hx L hxy' hlogyx (Real.exp (-s)) (Real.exp (-r))
          (Real.exp_pos _) hsk (Real.exp_pos _) hrcut g a hg hga hkgap
        calc
          ∫⁻ ω, Wx ω * Wy ω * Set.indicator
              {ω | a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) y} (fun _ => (1 : ℝ≥0∞)) ω ∂P =
            ∫⁻ ω, admissibleLogWickWeight P Y g (Real.exp (-s)) y ω *
              admissibleLogWickWeight P Y g (Real.exp (-r)) x ω * Set.indicator
                {ω | a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) y}
                (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
              apply lintegral_congr
              intro ω
              simp only [Wx, Wy]
              ring
          _ ≤ _ := h)
    refine hT.trans (le_of_eq ?_)
    rw [ENNReal.tsum_mul_left]
  -- assemble
  have hpoint (ω : Ω) :
      admissibleLogWickWeight P (if true = true then Y else Y) g (Real.exp (-r)) x ω *
          admissibleLogWickWeight P (if true = true then Y else Y) g (Real.exp (-s)) y ω *
          Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ))
            (fun _ => (1 : ℝ≥0∞)) (ω, x) *
          Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ))
            (fun _ => (1 : ℝ≥0∞)) (ω, y) ≤
        admissibleLogWickWeight P (if true = true then Y else Y) g (Real.exp (-r)) x ω *
            admissibleLogWickWeight P (if true = true then Y else Y) g (Real.exp (-s)) y ω *
            Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)
              (fun _ => (1 : ℝ≥0∞)) (ω, x) *
            Set.indicator (admissibleGrowingBarrierSet Y a k₀ s)
              (fun _ => (1 : ℝ≥0∞)) (ω, y) +
          Wx ω * Wy ω * Set.indicator (omittedBarrierEvent Y a m r x)
            (fun _ => (1 : ℝ≥0∞)) ω +
          Wx ω * Wy ω * Set.indicator (omittedBarrierEvent Y a m s y)
            (fun _ => (1 : ℝ≥0∞)) ω := by
    have h := barrier_indicator_pair_le Y a k₀ m r s ω x y
    simp only [ite_self, Wx, Wy]
    calc
      _ = admissibleLogWickWeight P Y g (Real.exp (-r)) x ω *
            admissibleLogWickWeight P Y g (Real.exp (-s)) y ω *
          (Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ))
            (fun _ => (1 : ℝ≥0∞)) (ω, x) *
          Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ))
            (fun _ => (1 : ℝ≥0∞)) (ω, y)) := by ring
      _ ≤ admissibleLogWickWeight P Y g (Real.exp (-r)) x ω *
            admissibleLogWickWeight P Y g (Real.exp (-s)) y ω *
          (Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)
              (fun _ => (1 : ℝ≥0∞)) (ω, x) *
            Set.indicator (admissibleGrowingBarrierSet Y a k₀ s)
              (fun _ => (1 : ℝ≥0∞)) (ω, y) +
            Set.indicator (omittedBarrierEvent Y a m r x) (fun _ => (1 : ℝ≥0∞)) ω +
            Set.indicator (omittedBarrierEvent Y a m s y) (fun _ => (1 : ℝ≥0∞)) ω) :=
          mul_le_mul_right h _
      _ = _ := by ring
  have hoMeas (t : ℝ) (z : ℂ) : MeasurableSet (omittedBarrierEvent Y a m t z) := by
    have hEq : omittedBarrierEvent Y a m t z =
        ⋃ k : ℕ, {ω | m < k ∧ (k : ℝ) ≤ t ∧ a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) z} := by
      ext ω; simp [omittedBarrierEvent]
    rw [hEq]
    refine MeasurableSet.iUnion fun k => ?_
    by_cases hk : m < k ∧ (k : ℝ) ≤ t
    · have hEq' : {ω | m < k ∧ (k : ℝ) ≤ t ∧ a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) z} =
          {ω | a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) z} := by
        ext ω; simp [hk]
      rw [hEq']
      exact measurableSet_lt measurable_const
        (admissible_field_measurable_sample P U dens ε₀ Y hY _ z)
    · have hEq' : {ω | m < k ∧ (k : ℝ) ≤ t ∧ a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) z} =
          ∅ := Set.eq_empty_of_forall_notMem fun ω h => hk ⟨h.1, h.2.1⟩
      rw [hEq']
      exact MeasurableSet.empty
  have hthird : Measurable (fun ω => Wx ω * Wy ω *
      Set.indicator (omittedBarrierEvent Y a m s y) (fun _ => (1 : ℝ≥0∞)) ω) :=
    (hWx.mul hWy).mul (measurable_const.indicator (hoMeas s y))
  have hsecondMeas : Measurable (fun ω => Wx ω * Wy ω *
      Set.indicator (omittedBarrierEvent Y a m r x) (fun _ => (1 : ℝ≥0∞)) ω) :=
    (hWx.mul hWy).mul (measurable_const.indicator (hoMeas r x))
  calc
    compatibleAdmissibleSelectedFiniteBarrierPairKernel P Y Y g a k₀ m
        (Real.exp (-r)) (Real.exp (-s)) x y true true ≤
      ∫⁻ ω, (admissibleLogWickWeight P (if true = true then Y else Y) g (Real.exp (-r)) x ω *
            admissibleLogWickWeight P (if true = true then Y else Y) g (Real.exp (-s)) y ω *
            Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)
              (fun _ => (1 : ℝ≥0∞)) (ω, x) *
            Set.indicator (admissibleGrowingBarrierSet Y a k₀ s)
              (fun _ => (1 : ℝ≥0∞)) (ω, y) +
          Wx ω * Wy ω * Set.indicator (omittedBarrierEvent Y a m r x)
            (fun _ => (1 : ℝ≥0∞)) ω) +
          Wx ω * Wy ω * Set.indicator (omittedBarrierEvent Y a m s y)
            (fun _ => (1 : ℝ≥0∞)) ω ∂P := lintegral_mono hpoint
    _ = compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel P Y Y g a k₀ r s x y
            true true +
          ∫⁻ ω, Wx ω * Wy ω * Set.indicator (omittedBarrierEvent Y a m r x)
            (fun _ => (1 : ℝ≥0∞)) ω ∂P +
          ∫⁻ ω, Wx ω * Wy ω * Set.indicator (omittedBarrierEvent Y a m s y)
            (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
      rw [lintegral_add_right _ hthird, lintegral_add_right _ hsecondMeas]
      rfl
    _ ≤ compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel P Y Y g a k₀ r s x y
            true true +
          c * ∑' j : ℕ, f (j + (m + 1)) + c * ∑' j : ℕ, f (j + (m + 1)) := by
      gcongr
    _ = _ := by
      simp only [c, f]
      ring

end DOZZ.Assembly
