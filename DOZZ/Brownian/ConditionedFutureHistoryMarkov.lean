/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedFutureKernelMarkov
public import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Full-history deterministic-time Markov property

The finite-schedule factorization extends from coordinate vectors to the complete path history
and rational future by the cylinder π-system.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The endpoint-conditioned rational future has the current value at every nonpositive
relative rational time, almost surely under the state disintegration. -/
theorem conditionedPositiveEndpointFutureKernel_nonpos_coordinate_ae
    {ν : ℝ} {P : Measure BrownianPath} [IsFiniteMeasure P]
    (t : ℝ≥0) (q : ℚ) (hq : (q : ℝ) ≤ 0) :
    ∀ᵐ z ∂((P.map (conditionedPositiveHistory t)) ⊗ₘ
      conditionedPositiveEndpointFutureKernel t P),
      z.2 q = z.1 ⟨t, le_rfl⟩ := by
  have _ := ν
  classical
  let X : BrownianPath → ℝ := conditionedPositiveStateAt t
  let Y : BrownianPath → (ℚ → ℝ) := conditionedPositiveFutureRationalEvals t
  have hX : Measurable X := (ContinuousMap.measurable_eval t).neg
  have hY : Measurable Y := measurable_conditionedPositiveFutureRationalEvals t
  have hstateJoint : (P.map X) ⊗ₘ conditionedPositiveFutureKernel t P =
      P.map (fun p => (X p, Y p)) := by
    simpa [X, Y] using conditionedPositiveFutureKernel_compProd t P
  have hpathDiag : ∀ᵐ p ∂P, Y p q = X p := by
    let s : ℝ≥0 := ⟨max (q : ℝ) 0, le_max_right _ _⟩
    have hs : s = 0 := by
      apply Subtype.ext
      simp [s, max_eq_right hq]
    filter_upwards with p
    change -(p (t + s)) = -(p t)
    rw [hs, add_zero]
  have hdiagSet : MeasurableSet {z : ℝ × (ℚ → ℝ) | z.2 q = z.1} :=
    measurableSet_eq_fun ((measurable_pi_apply q).comp measurable_snd) measurable_fst
  have hdiag : ∀ᵐ z ∂P.map (fun p => (X p, Y p)), z.2 q = z.1 := by
    rw [ae_map_iff (hX.prodMk hY).aemeasurable hdiagSet]
    exact hpathDiag
  have hstateDiag : ∀ᵐ x ∂P.map X, ∀ᵐ y ∂conditionedPositiveFutureKernel t P x,
      y q = x := by
    rw [← hstateJoint] at hdiag
    exact Measure.ae_ae_of_ae_compProd hdiag
  let endpoint : (Set.Iic t → ℝ) → ℝ := fun h => h ⟨t, le_rfl⟩
  have hendpoint : Measurable endpoint := measurable_pi_apply _
  have hstateMarg : (P.map (conditionedPositiveHistory t)).map endpoint = P.map X := by
    rw [Measure.map_map hendpoint (measurable_conditionedPositiveHistory t)]
    rfl
  have hstateDiagHistory : ∀ᵐ h ∂P.map (conditionedPositiveHistory t),
      ∀ᵐ y ∂conditionedPositiveFutureKernel t P (endpoint h), y q = endpoint h := by
    have h := Filter.Eventually.filter_mono
      ((P.map (conditionedPositiveHistory t)).tendsto_ae_map hendpoint.aemeasurable)
      (by rw [hstateMarg]; exact hstateDiag)
    exact h
  have hdiagHistory : ∀ᵐ z ∂((P.map (conditionedPositiveHistory t)) ⊗ₘ
      conditionedPositiveEndpointFutureKernel t P), z.2 q = endpoint z.1 := by
    apply Measure.ae_compProd_of_ae_ae
      (measurableSet_eq_fun ((measurable_pi_apply q).comp measurable_snd)
        (hendpoint.comp measurable_fst))
    filter_upwards [hstateDiagHistory] with h hh
    simpa [conditionedPositiveEndpointFutureKernel, endpoint,
      Kernel.comp_deterministic_eq_comap, Kernel.comap_apply] using hh
  simpa [endpoint] using hdiagHistory

/-- The full-history/rational-future composition measure agrees with the explicit finite-schedule
factorization on every pair of cylinder sets. -/
theorem conditionedPositiveFutureHistoryKernel_cylinder_rectangles
    {ν : ℝ} {P : Measure BrownianPath} [IsFiniteMeasure P]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    ∀ s ∈ MeasureTheory.measurableCylinders (fun _ : Set.Iic t => ℝ),
      ∀ u ∈ MeasureTheory.measurableCylinders (fun _ : ℚ => ℝ),
        P.map (fun p =>
          (conditionedPositiveHistory t p, conditionedPositiveFutureRationalEvals t p))
            (s ×ˢ u) =
          ((P.map (conditionedPositiveHistory t)) ⊗ₘ
            conditionedPositiveEndpointFutureKernel t P) (s ×ˢ u) := by
  intro s hs u hu
  classical
  obtain ⟨I, S, hS, rfl⟩ := (MeasureTheory.mem_measurableCylinders s).mp hs
  obtain ⟨J, T, hT, rfl⟩ := (MeasureTheory.mem_measurableCylinders u).mp hu
  let pastGrid : Finset (Set.Iic t) :=
    I.filter (fun i => 0 < (i : ℝ) ∧ (i : ℝ) < (t : ℝ))
  let futureGrid : Finset ℚ := J.filter (fun q => 0 < (q : ℝ))
  let k := pastGrid.card
  let n := futureGrid.card
  let pastTimes : Fin (k + 1) → ℝ≥0 := Fin.lastCases t
    (fun i => (pastGrid.orderIsoOfFin rfl i).val.val)
  let offsets : Fin n → ℚ := fun i => (futureGrid.orderIsoOfFin rfl i).val
  let futureTimes : Fin n → ℝ≥0 := fun i => t + (offsets i : ℝ).toNNReal
  have hLast : pastTimes (Fin.last k) = t := by
    simp only [pastTimes, Fin.lastCases_last]
  have hPastCast (i : Fin k) :
      pastTimes i.castSucc = (pastGrid.orderIsoOfFin rfl i).val.val := by
    simp [pastTimes, Fin.lastCases_castSucc]
  have hPastPos : ∀ i, 0 < (pastTimes i : ℝ) := by
    intro i
    cases i using Fin.lastCases with
    | last => rw [hLast]; exact ht
    | cast i =>
        have hi := (Finset.mem_filter.mp (pastGrid.orderIsoOfFin rfl i).2).2.1
        rw [hPastCast]
        exact_mod_cast hi
  have hPastBound : ∀ i, pastTimes i ≤ t := by
    intro i
    cases i using Fin.lastCases with
    | last => rw [hLast]
    | cast i =>
        have hi := (Finset.mem_filter.mp (pastGrid.orderIsoOfFin rfl i).2).2.2
        have hi' : (pastTimes i.castSucc : ℝ) < (t : ℝ) := by
          rw [hPastCast]
          exact_mod_cast hi
        exact NNReal.coe_le_coe.mpr hi'.le
  have hPastMono : StrictMono pastTimes := by
    intro i j hij
    cases i using Fin.lastCases with
    | last => exact False.elim ((not_lt_of_ge (Fin.le_last j)) hij)
    | cast i =>
        cases j using Fin.lastCases with
        | last =>
            have hi := (Finset.mem_filter.mp (pastGrid.orderIsoOfFin rfl i).2).2.2
            rw [hLast]
            have hi' : (pastTimes i.castSucc : ℝ) < (t : ℝ) := by
              rw [hPastCast]
              exact_mod_cast hi
            exact NNReal.coe_lt_coe.mpr hi'
        | cast j =>
            have hij' : i < j := by
              apply Fin.lt_def.mpr
              have hv := Fin.lt_def.mp hij
              simpa using hv
            have hij'' := (pastGrid.orderIsoOfFin rfl).strictMono hij'
            rw [hPastCast, hPastCast]
            exact_mod_cast hij''
  have hOffsetsPos : ∀ i, 0 < (offsets i : ℝ) := by
    intro i
    exact (Finset.mem_filter.mp (futureGrid.orderIsoOfFin rfl i).2).2
  have hOffsetsMono : StrictMono offsets := by
    intro i j hij
    simpa [offsets] using (futureGrid.orderIsoOfFin rfl).strictMono hij
  have hFutureMono : StrictMono futureTimes := by
    intro i j hij
    have hq := hOffsetsMono hij
    have hqReal : (offsets i : ℝ) < (offsets j : ℝ) := by exact_mod_cast hq
    have hqNN : (offsets i : ℝ).toNNReal < (offsets j : ℝ).toNNReal := by
      apply NNReal.coe_lt_coe.mp
      rw [Real.coe_toNNReal _ (hOffsetsPos i).le,
        Real.coe_toNNReal _ (hOffsetsPos j).le]
      exact hqReal
    simpa [futureTimes] using add_lt_add_left hqNN t
  have hMonoTotal : StrictMono (Fin.append pastTimes futureTimes) :=
    strictMono_finAppend_of_cross pastTimes futureTimes hPastMono hFutureMono
      (fun i j => lt_of_le_of_lt (hPastBound i) (by
        have hq : 0 < (offsets j : ℝ).toNNReal := by
          apply NNReal.coe_pos.mp
          rw [Real.coe_toNNReal _ (hOffsetsPos j).le]
          exact hOffsetsPos j
        simpa [futureTimes] using lt_add_of_pos_right t hq))
  have hOneMono : StrictMono (fun _ : Fin 1 => t) := by
    intro i j hij
    fin_cases i
    fin_cases j
    omega
  have hMonoEndpoint : StrictMono
      (Fin.append (fun _ : Fin 1 => t) futureTimes) :=
    strictMono_finAppend_of_cross (fun _ : Fin 1 => t) futureTimes hOneMono hFutureMono
      (fun _ j => by
        have hq : 0 < (offsets j : ℝ).toNNReal := by
          apply NNReal.coe_pos.mp
          rw [Real.coe_toNNReal _ (hOffsetsPos j).le]
          exact hOffsetsPos j
        simpa [futureTimes] using lt_add_of_pos_right t hq)
  let pastProject : (Set.Iic t → ℝ) → Fin (k + 1) → ℝ :=
    fun h i => h ⟨pastTimes i, hPastBound i⟩
  let futureProject : (ℚ → ℝ) → Fin n → ℝ := fun y i => y (offsets i)
  let pairProject : ((Set.Iic t → ℝ) × (ℚ → ℝ)) →
      ((Fin (k + 1) → ℝ) × (Fin n → ℝ)) :=
    fun z => (pastProject z.1, futureProject z.2)
  let readPast : (Fin (k + 1) → ℝ) → (∀ i : I, ℝ) := fun x i =>
    if h0 : (i : Set.Iic t) = ⟨0, t.property⟩ then 0
    else if ht' : (i : Set.Iic t) = ⟨t, le_rfl⟩ then x (Fin.last k)
    else
      x (((pastGrid.orderIsoOfFin rfl).symm ⟨i, by
        apply Finset.mem_filter.mpr
        refine ⟨i.property, ?_⟩
        constructor
        · have hi0 : (i : ℝ) ≠ 0 := by
            intro h
            apply h0
            apply Subtype.ext
            exact_mod_cast h
          exact lt_of_le_of_ne (NNReal.coe_nonneg _) (Ne.symm hi0)
        · have hit : (i : ℝ) ≠ (t : ℝ) := by
            intro h
            apply ht'
            apply Subtype.ext
            exact_mod_cast h
          have hibound : (i : ℝ) ≤ (t : ℝ) := by exact_mod_cast i.val.property
          exact lt_of_le_of_ne hibound hit
      ⟩).castSucc)
  let readFuture : ((Fin (k + 1) → ℝ) × (Fin n → ℝ)) → (∀ j : J, ℝ) :=
    fun z j => if hq : 0 < (j : ℝ) then
      z.2 ((futureGrid.orderIsoOfFin rfl).symm ⟨j, by
        exact Finset.mem_filter.mpr ⟨j.property, hq⟩⟩)
    else z.1 (Fin.last k)
  let readPair : ((Fin (k + 1) → ℝ) × (Fin n → ℝ)) →
      ((∀ i : I, ℝ) × (∀ j : J, ℝ)) := fun z => (readPast z.1, readFuture z)
  have hPastReadMeas : Measurable readPast := by
    apply measurable_pi_iff.mpr
    intro i
    by_cases h0 : (i : Set.Iic t) = ⟨0, t.property⟩
    · simp [readPast, h0]
    · by_cases ht' : (i : Set.Iic t) = ⟨t, le_rfl⟩
      · have ht0 : (⟨t, le_rfl⟩ : Set.Iic t) ≠ ⟨0, t.property⟩ := by
          intro he
          have he' := congrArg Subtype.val he
          exact (ne_of_gt ht) (by exact_mod_cast he')
        simp only [readPast, dite_eq_right h0, dite_eq_left ht']
        exact measurable_pi_apply _
      · simp only [readPast, dite_eq_right h0, dite_eq_right ht']
        exact measurable_pi_apply _
  have hFutureReadMeas : Measurable readFuture := by
    apply measurable_pi_iff.mpr
    intro j
    by_cases hq : 0 < (j : ℝ)
    · simp only [readFuture, dite_eq_left hq]
      exact (measurable_pi_apply _).comp measurable_snd
    · simp only [readFuture, dite_eq_right hq]
      exact (measurable_pi_apply _).comp measurable_fst
  have hReadPairMeas : Measurable readPair := by
    change Measurable (fun z => (readPast z.1, readFuture z))
    exact (hPastReadMeas.comp measurable_fst).prodMk hFutureReadMeas
  have hPastProjectMeas : Measurable pastProject := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_pi_apply (⟨pastTimes i, hPastBound i⟩ : Set.Iic t)
  have hFutureProjectMeas : Measurable futureProject := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_pi_apply (offsets i)
  have hPairProjectMeas : Measurable pairProject :=
    hPastProjectMeas.comp measurable_fst |>.prodMk
      (hFutureProjectMeas.comp measurable_snd)
  let μhist := P.map (conditionedPositiveHistory t)
  let κhist := conditionedPositiveEndpointFutureKernel t P
  let μpair := μhist ⊗ₘ κhist
  let pathPair : BrownianPath → ((Fin (k + 1) → ℝ) × (Fin n → ℝ)) :=
    fun p => (fun i => -(p (pastTimes i)), fun i => -(p (futureTimes i)))
  have hfiniteProjection : μpair.map pairProject = P.map pathPair := by
    simpa [μhist, κhist, pairProject, pastProject, futureProject, pathPair,
      pastTimes, futureTimes] using
      (conditionedPositiveFutureHistory_finite_projection_compProd
        hP t ht pastTimes hPastPos hPastBound hPastMono hLast offsets hOffsetsPos
        hMonoTotal hMonoEndpoint)
  have hReadLeftAE : ∀ᵐ z ∂μpair,
      readPair (pairProject z) =
        (I.restrict z.1, J.restrict z.2) := by
    let hzero : (Set.Iic t → ℝ) → ℝ := fun h => h ⟨0, t.property⟩
    have hzeroMeas : Measurable hzero :=
      measurable_pi_apply (⟨0, t.property⟩ : Set.Iic t)
    have hzeroAE : ∀ᵐ h ∂μhist, hzero h = 0 := by
      rw [ae_map_iff (measurable_conditionedPositiveHistory t).aemeasurable
        (measurableSet_eq_fun hzeroMeas measurable_const)]
      filter_upwards [hP.2.2.1] with p hp
      change -(p 0) = 0
      rw [hp]
      norm_num
    have hzeroPair : ∀ᵐ z ∂μpair, z.1 ⟨0, t.property⟩ = 0 := by
      exact Measure.ae_compProd_of_ae_fst κhist
        (measurableSet_eq_fun (measurable_pi_apply _) measurable_const) hzeroAE
    have hnonposPair : ∀ᵐ z ∂μpair, ∀ q : J, (q : ℝ) ≤ 0 →
        z.2 q = z.1 ⟨t, le_rfl⟩ := by
      apply ae_all_iff.mpr
      intro q
      by_cases hq : (q : ℝ) ≤ 0
      · have hqae := conditionedPositiveEndpointFutureKernel_nonpos_coordinate_ae
          (ν := ν) (P := P) t (q : ℚ) hq
        filter_upwards [hqae] with z hz
        intro _
        exact hz
      · exact Filter.Eventually.of_forall fun z hq' => False.elim (hq hq')
    filter_upwards [hzeroPair, hnonposPair] with z hz0 hzq
    apply Prod.ext
    · funext i
      by_cases hi0 : (i : Set.Iic t) = ⟨0, t.property⟩
      · simp [readPair, readPast, hi0, hz0]
      · by_cases hit : (i : Set.Iic t) = ⟨t, le_rfl⟩
        · have ht0 : (⟨t, le_rfl⟩ : Set.Iic t) ≠ ⟨0, t.property⟩ := by
            intro he
            have he' := congrArg Subtype.val he
            exact (ne_of_gt ht) (by exact_mod_cast he')
          have hpoint :
              (⟨pastTimes (Fin.last k), hPastBound (Fin.last k)⟩ : Set.Iic t) =
                ⟨t, le_rfl⟩ := by
            apply Subtype.ext
            exact_mod_cast hLast
          simp only [readPair, readPast, dite_eq_right hi0, dite_eq_left hit, pairProject, pastProject]
          change z.1 (⟨pastTimes (Fin.last k), hPastBound (Fin.last k)⟩ : Set.Iic t) =
            z.1 (i : Set.Iic t)
          rw [hpoint, ← hit]
        · have hiGrid : (i : Set.Iic t) ∈ pastGrid := by
            apply Finset.mem_filter.mpr
            refine ⟨i.property, ?_⟩
            constructor
            · have hi : (i : ℝ) ≠ 0 := by
                intro h
                apply hi0
                apply Subtype.ext
                exact_mod_cast h
              exact lt_of_le_of_ne (NNReal.coe_nonneg _) (Ne.symm hi)
            · have hi : (i : ℝ) ≠ (t : ℝ) := by
                intro h
                apply hit
                apply Subtype.ext
                exact_mod_cast h
              have hibound : (i : ℝ) ≤ (t : ℝ) := by exact_mod_cast i.val.property
              exact lt_of_le_of_ne hibound hi
          let j : Fin k := (pastGrid.orderIsoOfFin rfl).symm ⟨i, hiGrid⟩
          have hj : (pastGrid.orderIsoOfFin rfl j) = ⟨i, hiGrid⟩ :=
            (pastGrid.orderIsoOfFin rfl).apply_symm_apply ⟨i, hiGrid⟩
          have htime : pastTimes j.castSucc = i.val.val := by
            rw [hPastCast]
            exact congrArg (fun x : ↥pastGrid => x.val.val) hj
          have hidx :
              (pastGrid.orderEmbOfFin rfl j : Set.Iic t) = (i : Set.Iic t) := by
            rw [← Finset.coe_orderIsoOfFin_apply]
            exact congrArg Subtype.val hj
          simp only [readPair, readPast, dite_eq_right hi0, dite_eq_right hit]
          simp [pairProject, pastProject, j, htime,             ]
    · funext j
      by_cases hq : 0 < (j : ℝ)
      · have hjGrid : (j : ℚ) ∈ futureGrid :=
          Finset.mem_filter.mpr ⟨j.property, hq⟩
        let i : Fin n := (futureGrid.orderIsoOfFin rfl).symm ⟨j, hjGrid⟩
        have hi : (futureGrid.orderIsoOfFin rfl i) = ⟨j, hjGrid⟩ :=
          (futureGrid.orderIsoOfFin rfl).apply_symm_apply ⟨j, hjGrid⟩
        have hoff : offsets i = j := congrArg Subtype.val hi
        have hq' : 0 < (j : ℝ) := hq
        simp only [readPair, readFuture, dite_eq_left hq']
        simp [pairProject, futureProject, i, hoff]
      · have hz := hzq j (le_of_not_gt hq)
        have hq' : ¬ 0 < (j : ℝ) := hq
        simp only [readPair, readFuture, dite_eq_right hq']
        simp [pairProject, pastProject, hLast, hz]
  have hReadRightAE : ∀ᵐ p ∂P,
      readPair (pathPair p) =
        (I.restrict (conditionedPositiveHistory t p),
          J.restrict (conditionedPositiveFutureRationalEvals t p)) := by
    filter_upwards [hP.2.2.1] with p hp0
    apply Prod.ext
    · funext i
      by_cases hi0 : (i : Set.Iic t) = ⟨0, t.property⟩
      · simp [readPair, readPast, pathPair, hi0, hp0, conditionedPositiveHistory,
          conditionedPositiveProcessValue]
      · by_cases hit : (i : Set.Iic t) = ⟨t, le_rfl⟩
        · have ht0 : (⟨t, le_rfl⟩ : Set.Iic t) ≠ ⟨0, t.property⟩ := by
            intro he
            have he' := congrArg Subtype.val he
            exact (ne_of_gt ht) (by exact_mod_cast he')
          simp [readPair, readPast, pathPair, hit, ht0, hLast,
            conditionedPositiveHistory, conditionedPositiveProcessValue]
        · have hiGrid : (i : Set.Iic t) ∈ pastGrid := by
            apply Finset.mem_filter.mpr
            refine ⟨i.property, ?_⟩
            constructor
            · have hi : (i : ℝ) ≠ 0 := by
                intro h
                apply hi0
                apply Subtype.ext
                exact_mod_cast h
              exact lt_of_le_of_ne (NNReal.coe_nonneg _) (Ne.symm hi)
            · have hi : (i : ℝ) ≠ (t : ℝ) := by
                intro h
                apply hit
                apply Subtype.ext
                exact_mod_cast h
              have hibound : (i : ℝ) ≤ (t : ℝ) := by exact_mod_cast i.val.property
              exact lt_of_le_of_ne hibound hi
          let j : Fin k := (pastGrid.orderIsoOfFin rfl).symm ⟨i, hiGrid⟩
          have hj : (pastGrid.orderIsoOfFin rfl j) = ⟨i, hiGrid⟩ :=
            (pastGrid.orderIsoOfFin rfl).apply_symm_apply ⟨i, hiGrid⟩
          have htime : pastTimes j.castSucc = i.val.val := by
            simpa only [pastTimes, Fin.lastCases_castSucc] using
              congrArg (fun x : ↥pastGrid => x.val.val) hj
          have hidxSymm :
              (pastGrid.orderEmbOfFin rfl
                ((pastGrid.orderIsoOfFin rfl).symm ⟨i, hiGrid⟩) : Set.Iic t) = i := by
            rw [← Finset.coe_orderIsoOfFin_apply]
            exact congrArg Subtype.val
              ((pastGrid.orderIsoOfFin rfl).apply_symm_apply ⟨i, hiGrid⟩)
          simp [readPair, readPast, pathPair, hi0, hit,             hidxSymm, pastTimes, Fin.lastCases_castSucc, conditionedPositiveHistory,
            conditionedPositiveProcessValue]
    · funext j
      by_cases hq : 0 < (j : ℝ)
      · have hjGrid : (j : ℚ) ∈ futureGrid :=
          Finset.mem_filter.mpr ⟨j.property, hq⟩
        let i : Fin n := (futureGrid.orderIsoOfFin rfl).symm ⟨j, hjGrid⟩
        have hi : (futureGrid.orderIsoOfFin rfl i) = ⟨j, hjGrid⟩ :=
          (futureGrid.orderIsoOfFin rfl).apply_symm_apply ⟨j, hjGrid⟩
        have hoff : offsets i = j := congrArg Subtype.val hi
        let qtime : ℝ≥0 := (j : ℝ).toNNReal
        have hreal : (offsets i : ℝ) = (j : ℝ) := by exact_mod_cast hoff
        have hoffTime : (offsets i : ℝ).toNNReal = qtime := by
          apply Subtype.ext
          simp [Real.coe_toNNReal', qtime, hreal]
        have hqTime :
            (⟨max (j : ℝ) 0, le_max_right _ _⟩ : ℝ≥0) = qtime := by
          apply Subtype.ext
          simp [Real.coe_toNNReal', qtime]
        have hfutureEq : futureTimes i = t + qtime := by
          simp [futureTimes, hoffTime]
        simp only [readPair, readFuture, dite_eq_left hq]
        let s : ℝ≥0 := ⟨max (j : ℝ) 0, le_max_right _ _⟩
        change -(p (futureTimes i)) = -(p (t + s))
        rw [hfutureEq, ← hqTime]
      · have hq0 : (j : ℝ) ≤ 0 := le_of_not_gt hq
        simp only [readPair, readFuture, dite_eq_right hq]
        let s : ℝ≥0 := ⟨max (j : ℝ) 0, le_max_right _ _⟩
        have hs : s = 0 := by
          apply Subtype.ext
          simp [s, max_eq_right hq0]
        change -(p (pastTimes (Fin.last k))) = -(p (t + s))
        rw [hLast, hs, add_zero]
  have hmapEventLeft :
      μpair (cylinder I S ×ˢ cylinder J T) =
        (μpair.map pairProject).map readPair (S ×ˢ T) := by
    rw [Measure.map_map hReadPairMeas hPairProjectMeas,
      Measure.map_apply (hReadPairMeas.comp hPairProjectMeas)
        (MeasurableSet.prod hS hT)]
    apply (measure_congr ?_).symm
    filter_upwards [hReadLeftAE] with z hz
    simp [MeasureTheory.cylinder, hz]
  have hmapEventRight :
      P.map (fun p =>
          (conditionedPositiveHistory t p, conditionedPositiveFutureRationalEvals t p))
        (cylinder I S ×ˢ cylinder J T) =
      (P.map pathPair).map readPair (S ×ˢ T) := by
    have hOriginalMeas : Measurable (fun p =>
        (conditionedPositiveHistory t p, conditionedPositiveFutureRationalEvals t p)) := by
      exact (measurable_conditionedPositiveHistory t).prodMk
        (measurable_conditionedPositiveFutureRationalEvals t)
    have hset :
        (fun p =>
          (conditionedPositiveHistory t p, conditionedPositiveFutureRationalEvals t p)) ⁻¹'
            (cylinder I S ×ˢ cylinder J T) =ᵐ[P]
        (readPair ∘ pathPair) ⁻¹' (S ×ˢ T) := by
      filter_upwards [hReadRightAE] with p hp
      simp [MeasureTheory.cylinder, hp]
    calc
      P.map (fun p =>
          (conditionedPositiveHistory t p, conditionedPositiveFutureRationalEvals t p))
            (cylinder I S ×ˢ cylinder J T) =
        P ((fun p =>
            (conditionedPositiveHistory t p, conditionedPositiveFutureRationalEvals t p)) ⁻¹'
              (cylinder I S ×ˢ cylinder J T)) :=
        Measure.map_apply hOriginalMeas (MeasurableSet.prod hS.cylinder hT.cylinder)
      _ = P ((readPair ∘ pathPair) ⁻¹' (S ×ˢ T)) := measure_congr hset
      _ = (P.map pathPair).map readPair (S ×ˢ T) := by
        rw [Measure.map_map hReadPairMeas (by fun_prop),
          Measure.map_apply (hReadPairMeas.comp (by fun_prop)) (MeasurableSet.prod hS hT)]
  have hfiniteRead := congrArg (fun μ => μ.map readPair) hfiniteProjection
  calc
    P.map (fun p =>
        (conditionedPositiveHistory t p, conditionedPositiveFutureRationalEvals t p))
          (cylinder I S ×ˢ cylinder J T) =
        (P.map pathPair).map readPair (S ×ˢ T) := hmapEventRight
    _ = (μpair.map pairProject).map readPair (S ×ˢ T) := by
      rw [← hfiniteRead]
    _ = μpair (cylinder I S ×ˢ cylinder J T) := hmapEventLeft.symm

/-- The complete rational future conditioned on the path history through deterministic time `t`
depends on that history only through its endpoint. -/
theorem conditionedPositiveFutureHistoryKernel_ae_eq_endpoint
    {ν : ℝ} {P : Measure BrownianPath} [IsFiniteMeasure P]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    conditionedPositiveFutureHistoryKernel t P =ᵐ[P.map (conditionedPositiveHistory t)]
      conditionedPositiveEndpointFutureKernel t P := by
  apply conditionedPositiveFutureHistoryKernel_ae_eq_endpoint_of_cylinder_rectangles
  intro s hs u hu
  exact conditionedPositiveFutureHistoryKernel_cylinder_rectangles hP t ht s hs u hu

/-- Conditional expectation of any integrable rational-future functional given the complete
history through `t` is its endpoint-kernel integral. -/
theorem conditionedPositiveHistory_condExp_rationalFuture
    {ν : ℝ} {P : Measure BrownianPath} [IsFiniteMeasure P]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (G : (ℚ → ℝ) → ℝ) (hG : StronglyMeasurable G)
    (hGint : Integrable (fun p => G (conditionedPositiveFutureRationalEvals t p)) P) :
    P[fun p => G (conditionedPositiveFutureRationalEvals t p) |
        conditionedPositiveNaturalFiltration t] =ᵐ[P]
      fun p => ∫ y, G y ∂conditionedPositiveEndpointFutureKernel t P
        (conditionedPositiveHistory t p) := by
  have hk := conditionedPositiveFutureHistoryKernel_ae_eq_endpoint hP t ht
  have hkernel : ∀ᵐ p ∂P,
      conditionedPositiveFutureHistoryKernel t P (conditionedPositiveHistory t p) =
        conditionedPositiveFutureKernel t P (conditionedPositiveStateAt t p) := by
    have hk' := Filter.Eventually.filter_mono
      (P.tendsto_ae_map (measurable_conditionedPositiveHistory t).aemeasurable) hk
    filter_upwards [hk'] with p hp
    simpa [conditionedPositiveEndpointFutureKernel,
      Kernel.comp_deterministic_eq_comap, Kernel.comap_apply,
      conditionedPositiveHistory_current] using hp
  have hcond := conditionedPositiveFutureHistoryKernel_condExp_of_ae_eq_endpoint
    t P G hG hGint hkernel
  filter_upwards [hcond] with p hp
  simpa [conditionedPositiveEndpointFutureKernel,
    Kernel.comp_deterministic_eq_comap, Kernel.comap_apply,
    conditionedPositiveHistory_current] using hp

end DOZZ.Proofs

end
