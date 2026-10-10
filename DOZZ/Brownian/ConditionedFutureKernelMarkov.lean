/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedFutureKernel
public import DOZZ.Brownian.ConditionedFDDMeasure
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# Deterministic-time finite-future Markov factorization

The explicit entrance FDD density disintegrates each finite future vector against the state at a
deterministic time. This is the finite-coordinate input to the full-history cylinder argument.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Filter

namespace DOZZ.Proofs

/-- Strict monotonicity is preserved by concatenating two finite schedules when every value in
the first block precedes every value in the second. -/
theorem strictMono_finAppend_of_cross
    {α : Type*} [LinearOrder α] {m n : ℕ}
    (a : Fin m → α) (b : Fin n → α)
    (ha : StrictMono a) (hb : StrictMono b)
    (hcross : ∀ i j, a i < b j) : StrictMono (Fin.append a b) := by
  intro i j hij
  cases i using Fin.addCases with
  | left i =>
    cases j using Fin.addCases with
    | left j =>
      simp only [Fin.append_left]
      apply ha
      apply Fin.lt_def.mpr
      have hv := Fin.lt_def.mp hij
      simpa using hv
    | right j =>
      simp only [Fin.append_left, Fin.append_right]
      exact hcross i j
  | right i =>
    cases j using Fin.addCases with
    | left j =>
      have hv := Fin.lt_def.mp hij
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
      omega
    | right j =>
      simp only [Fin.append_right]
      apply hb
      apply Fin.lt_def.mpr
      have hv := Fin.lt_def.mp hij
      simp only [Fin.val_natAdd] at hv
      simpa using hv

/-- Mapping the unique-coordinate past in a composition product to its real value preserves the
product disintegration when the future kernel only depends on that value. -/
theorem map_finOne_compProd
    {β : Type*} [MeasurableSpace β]
    (μ : Measure (Fin 1 → ℝ)) [SFinite μ]
    (κ : Kernel (Fin 1 → ℝ) β) [IsSFiniteKernel κ]
    (κ' : Kernel ℝ β) [IsSFiniteKernel κ']
    (hκ : ∀ x, κ x = κ' (x 0))
    (hfinite : ((μ ⊗ₘ κ).map (fun z => (z.1 0, z.2))) Set.univ < ∞) :
    (μ ⊗ₘ κ).map (fun z => (z.1 0, z.2)) = (μ.map (fun x => x 0)) ⊗ₘ κ' := by
  let C : Set (Set (ℝ × β)) :=
    Set.image2 (· ×ˢ ·) {s | MeasurableSet s} {u | MeasurableSet u}
  have hgen : (inferInstance : MeasurableSpace (ℝ × β)) =
      MeasurableSpace.generateFrom C := by
    simpa [C] using (generateFrom_prod (α := ℝ) (β := β)).symm
  have hpi : IsPiSystem C := by
    intro a ha b hb hab
    rcases ha with ⟨s, hs, u, hu, rfl⟩
    rcases hb with ⟨s', hs', u', hu', rfl⟩
    change MeasurableSet s at hs
    change MeasurableSet s' at hs'
    change MeasurableSet u at hu
    change MeasurableSet u' at hu'
    refine ⟨s ∩ s', MeasurableSet.inter hs hs', u ∩ u', MeasurableSet.inter hu hu', ?_⟩
    ext z
    simp [and_assoc, and_left_comm]
  have hrect : ∀ (A : Set ℝ), MeasurableSet A → ∀ (B : Set β), MeasurableSet B →
      (μ ⊗ₘ κ).map (fun z => (z.1 0, z.2)) (A ×ˢ B) =
        ((μ.map fun x => x 0) ⊗ₘ κ') (A ×ˢ B) := by
    intro A hA B hB
    have hEval : Measurable (fun x : Fin 1 → ℝ => x 0) := measurable_pi_apply 0
    have hPair : Measurable (fun z : (Fin 1 → ℝ) × β => (z.1 0, z.2)) :=
      hEval.comp measurable_fst |>.prodMk measurable_snd
    rw [Measure.map_apply hPair (MeasurableSet.prod hA hB)]
    rw [show (fun z : (Fin 1 → ℝ) × β => (z.1 0, z.2)) ⁻¹' (A ×ˢ B) =
        ((fun x : Fin 1 → ℝ => x 0) ⁻¹' A) ×ˢ B by
      ext z
      simp]
    rw [Measure.compProd_apply_prod (hA.preimage hEval) hB,
      Measure.compProd_apply_prod hA hB]
    rw [MeasureTheory.setLIntegral_map hA (Kernel.measurable_coe κ' hB) hEval]
    exact MeasureTheory.setLIntegral_congr_fun (hA.preimage hEval) (fun x _ => by
      rw [hκ])
  have huniv : (μ ⊗ₘ κ).map (fun z => (z.1 0, z.2)) Set.univ =
      ((μ.map fun x => x 0) ⊗ₘ κ') Set.univ := by
    simpa using hrect Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
  let : IsFiniteMeasure ((μ ⊗ₘ κ).map (fun z => (z.1 0, z.2))) := ⟨hfinite⟩
  apply MeasureTheory.ext_of_generate_finite C hgen hpi ?_ huniv
  intro s hs
  rcases hs with ⟨A, hA, B, hB, rfl⟩
  exact hrect A hA B hB

/-- Every finite rational projection of the future kernel, conditioned on the current state,
is the explicit finite Doob transition-chain density. This statement is eventwise, which is the
form needed for measurable future cylinders. -/
theorem conditionedPositiveFutureKernel_finite_projection_eq_density
    {ν : ℝ} {P : Measure BrownianPath} [IsFiniteMeasure P]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (n : ℕ) (offsets : Fin n → ℚ)
    (hOffsetsPos : ∀ i, 0 < (offsets i : ℝ))
    (hMono : StrictMono (Fin.append (fun _ : Fin 1 => t)
      (fun i => t + (offsets i : ℝ).toNNReal)))
    (B : Set (Fin n → ℝ)) (hB : MeasurableSet B) :
    ∀ᵐ x ∂P.map (fun p => -(p t)),
      ((conditionedPositiveFutureKernel t P).map
        (fun y i => y (offsets i))) x B =
        ((Kernel.const ℝ (volume : Measure (Fin n → ℝ))).withDensity
          (fun x y => conditionedPositiveFutureVectorDensity ν
            (fun _ : Fin 1 => (t : ℝ)) (fun i => (t : ℝ) + (offsets i : ℝ))
            (fun _ => x) y)) x B := by
  let pastTimes : Fin 1 → ℝ≥0 := fun _ => t
  let offsetTime : Fin n → NNReal := fun i => (offsets i : ℝ).toNNReal
  let futureTimes : Fin n → NNReal := fun i => t + offsetTime i
  let pastVec : BrownianPath → Fin 1 → ℝ := fun p _ => -(p t)
  let futureVec : BrownianPath → Fin n → ℝ := fun p i => -(p (futureTimes i))
  let X : BrownianPath → ℝ := fun p => -(p t)
  let Y : BrownianPath → Fin n → ℝ := fun p i =>
    conditionedPositiveFutureRationalEvals t p (offsets i)
  let pastDensity : (Fin 1 → ℝ) → ℝ≥0∞ :=
    conditionedPositiveFDDVectorDensity ν (fun i => (pastTimes i : ℝ))
  let futureDensity : (Fin 1 → ℝ) → (Fin n → ℝ) → ℝ≥0∞ :=
    conditionedPositiveFutureVectorDensity ν (fun i => (pastTimes i : ℝ))
      (fun i => (futureTimes i : ℝ))
  let pastMeasure : Measure (Fin 1 → ℝ) :=
    (volume : Measure (Fin 1 → ℝ)).withDensity pastDensity
  let pastKernel : Kernel (Fin 1 → ℝ) (Fin n → ℝ) :=
    (Kernel.const (Fin 1 → ℝ) (volume : Measure (Fin n → ℝ))).withDensity futureDensity
  let stateKernel : Kernel ℝ (Fin n → ℝ) :=
    (Kernel.const ℝ (volume : Measure (Fin n → ℝ))).withDensity
      (fun x y => futureDensity (fun _ => x) y)
  let project : (ℚ → ℝ) → Fin n → ℝ := fun y i => y (offsets i)
  have hFuturePos : ∀ i, (t : ℝ) < (futureTimes i : ℝ) := by
    intro i
    have hq : 0 < (offsetTime i : ℝ) := by
      rw [Real.coe_toNNReal _ (hOffsetsPos i).le]
      exact hOffsetsPos i
    exact lt_add_of_pos_right _ hq
  have htimePos : ∀ i, 0 < ((pastTimes i : ℝ)) := by
    intro i
    fin_cases i
    exact ht
  have hmonoPast : StrictMono pastTimes := by
    intro i j hij
    fin_cases i
    fin_cases j
    norm_num at hij
  have hsplit := negativeConditionedLaw_finitePastFuture_compProd hP
    pastTimes futureTimes htimePos (fun i =>
      lt_of_le_of_lt t.property (hFuturePos i)) hMono
  have hstateMeas : Measurable X := (ContinuousMap.measurable_eval t).neg
  have hpastVecMeas : Measurable pastVec := by
    apply measurable_pi_iff.mpr
    intro i
    exact hstateMeas
  have hfutureVecMeas : Measurable futureVec := by
    apply measurable_pi_iff.mpr
    intro i
    exact (ContinuousMap.measurable_eval (futureTimes i)).neg
  have hYMeas : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_pi_apply (offsets i)).comp
      (measurable_conditionedPositiveFutureRationalEvals t)
  have hproject : Measurable project := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_pi_apply (offsets i)
  have hPastFDD : P.map pastVec = pastMeasure := by
    have hfd := negativeConditionedLaw_positiveFDD hP 1 (by norm_num)
      (fun _ : Fin 1 => t) (by intro i; fin_cases i; exact ht)
      (by intro i j hij; fin_cases i; fin_cases j; norm_num at hij)
    have hfd' : P.map pastVec = (volume : Measure (Fin 1 → ℝ)).withDensity
        (fun x => ENNReal.ofReal (max 0
          (conditionedPositiveFDDDensity ν [((t : ℝ))] [x 0]))) := by
      simpa [pastVec] using hfd
    have hden : (fun x : Fin 1 → ℝ => ENNReal.ofReal (max 0
        (conditionedPositiveFDDDensity ν [((t : ℝ))] [x 0]))) = pastDensity := by
      funext x
      simp [pastDensity, pastTimes, conditionedPositiveFDDVectorDensity]
    change P.map pastVec = (volume : Measure (Fin 1 → ℝ)).withDensity pastDensity
    rw [← hden]
    exact hfd'
  have hstateMarginal : P.map X = pastMeasure.map (fun z => z 0) := by
    calc
      P.map X = (P.map pastVec).map (fun z => z 0) := by
        rw [Measure.map_map (measurable_pi_apply 0) hpastVecMeas]
        rfl
      _ = pastMeasure.map (fun z => z 0) := by rw [hPastFDD]
  have hpastKernelEq : ∀ z, pastKernel z = stateKernel (z 0) := by
    intro z
    have hz : z = fun _ : Fin 1 => z 0 := by
      funext i
      fin_cases i
      rfl
    have hdensity : futureDensity z = futureDensity (fun _ => z 0) := by rw [hz]
    have hstateDensityMeas : Measurable (Function.uncurry
        (fun x y => futureDensity (fun _ => x) y)) := by
      change Measurable (fun w : ℝ × (Fin n → ℝ) =>
        futureDensity (fun _ : Fin 1 => w.1) w.2)
      have hinput : Measurable (fun w : ℝ × (Fin n → ℝ) =>
          ((fun _ : Fin 1 => w.1), w.2)) := by
        apply Measurable.prodMk
        · apply measurable_pi_iff.mpr
          intro i
          exact measurable_fst
        · exact measurable_snd
      exact (measurable_conditionedPositiveFutureVectorDensity ν
        (fun i => (pastTimes i : ℝ)) (fun i => (futureTimes i : ℝ))).comp hinput
    change ((Kernel.const (Fin 1 → ℝ) (volume : Measure (Fin n → ℝ))).withDensity
        futureDensity) z =
      ((Kernel.const ℝ (volume : Measure (Fin n → ℝ))).withDensity
        (fun x y => futureDensity (fun _ => x) y)) (z 0)
    rw [Kernel.withDensity_apply (Kernel.const (Fin 1 → ℝ)
        (volume : Measure (Fin n → ℝ)))
        (measurable_conditionedPositiveFutureVectorDensity ν
          (fun i => (pastTimes i : ℝ)) (fun i => (futureTimes i : ℝ))) z,
      Kernel.withDensity_apply (Kernel.const ℝ (volume : Measure (Fin n → ℝ)))
        hstateDensityMeas (z 0)]
    simpa [Kernel.const_apply] using congrArg
      (fun f => (volume : Measure (Fin n → ℝ)).withDensity f) hdensity
  have : IsSFiniteKernel pastKernel := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro z y
    exact ENNReal.ofReal_ne_top
  have : IsSFiniteKernel stateKernel := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro x y
    exact ENNReal.ofReal_ne_top
  have hpairMap :
      (P.map (fun p => (pastVec p, futureVec p))).map
          (fun z => (z.1 0, z.2)) = P.map (fun p => (X p, futureVec p)) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    apply congrArg (fun f => P.map f)
    funext p
    apply Prod.ext
    · rfl
    · rfl
  have hfinite : ((pastMeasure ⊗ₘ pastKernel).map
      (fun z => (z.1 0, z.2))) Set.univ < ∞ := by
    rw [← hsplit, hpairMap]
    simp
  have hpair : P.map (fun p => (X p, futureVec p)) = P.map X ⊗ₘ stateKernel := by
    calc
      P.map (fun p => (X p, futureVec p)) =
          (P.map (fun p => (pastVec p, futureVec p))).map
            (fun z => (z.1 0, z.2)) := hpairMap.symm
      _ = (pastMeasure ⊗ₘ pastKernel).map (fun z => (z.1 0, z.2)) := by
        rw [hsplit]
      _ = (pastMeasure.map (fun z => z 0)) ⊗ₘ stateKernel :=
        map_finOne_compProd pastMeasure pastKernel stateKernel hpastKernelEq hfinite
      _ = P.map X ⊗ₘ stateKernel := by rw [hstateMarginal]
  have hYeq : Y = fun p i => futureVec p i := by
    funext p i
    change conditionedPositiveFuturePath t p
      (⟨max (offsets i : ℝ) 0, le_max_right _ _⟩ : NNReal) =
        -(p (futureTimes i))
    have htime : (⟨max (offsets i : ℝ) 0, le_max_right _ _⟩ : NNReal) =
        offsetTime i := by
      apply Subtype.ext
      simp [offsetTime, max_eq_left (le_of_lt (hOffsetsPos i)),
        Real.coe_toNNReal _ (hOffsetsPos i).le]
    rw [htime]
    change -(p (t + offsetTime i)) = -(p (futureTimes i))
    rfl
  have hpairFun : (fun p => (X p, Y p)) =
      (fun p => (X p, futureVec p)) := by
    funext p
    apply Prod.ext
    · rfl
    · exact congrFun hYeq p
  have hpairY : P.map (fun p => (X p, Y p)) = P.map X ⊗ₘ stateKernel := by
    rw [hpairFun]
    exact hpair
  have : IsSFiniteKernel stateKernel := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro x y
    exact ENNReal.ofReal_ne_top
  have hcond : ∀ᵐ x ∂P.map X, condDistrib Y X P x B = stateKernel x B := by
    have hfst : (P.map (fun p => (X p, Y p))).fst = P.map X := by
      exact Measure.fst_map_prodMk hstateMeas hYMeas
    have hpairCond : P.map (fun p => (X p, Y p)) =
        (P.map (fun p => (X p, Y p))).fst ⊗ₘ stateKernel := by
      rw [hfst]
      exact hpairY
    have huniq := eq_condKernel_of_measure_eq_compProd' stateKernel hpairCond hB
    rw [hfst] at huniq
    filter_upwards [huniq] with x hx
    simpa [condDistrib] using hx.symm
  have hprojCond := conditionedPositiveFutureKernel_finite_projection t P offsets
  have hproj : condDistrib Y X P =ᵐ[P.map X]
      (conditionedPositiveFutureKernel t P).map project := by
    change condDistrib
        (fun p i => conditionedPositiveFutureRationalEvals t p (offsets i))
        (conditionedPositiveStateAt t) P =ᵐ[P.map (conditionedPositiveStateAt t)]
          (conditionedPositiveFutureKernel t P).map (fun y i => y (offsets i))
    exact hprojCond
  have hfutureTimesReal : (fun i => (futureTimes i : ℝ)) =
      (fun i => (t : ℝ) + (offsets i : ℝ)) := by
    funext i
    simp [futureTimes, offsetTime, Real.coe_toNNReal _ (hOffsetsPos i).le]
  have hstateKernelEq : stateKernel =
      (Kernel.const ℝ (volume : Measure (Fin n → ℝ))).withDensity
        (fun x y => conditionedPositiveFutureVectorDensity ν
          (fun _ : Fin 1 => (t : ℝ)) (fun i => (t : ℝ) + (offsets i : ℝ))
          (fun _ => x) y) := by
    unfold stateKernel
    congr 1
    funext x y
    simp [futureDensity, pastTimes, hfutureTimesReal]
  filter_upwards [hcond, hproj] with x hxcond hxproj
  rw [hxproj] at hxcond
  rw [hstateKernelEq] at hxcond
  simpa [project] using hxcond

/-- Finite measures on a product are equal once their values agree on measurable rectangles. -/
theorem measure_eq_of_prod_rectangles
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure (α × β))
    (hfinite : μ Set.univ < ∞)
    (hrect : ∀ A, MeasurableSet A → ∀ B, MeasurableSet B →
      μ (A ×ˢ B) = ν (A ×ˢ B))
    (huniv : μ Set.univ = ν Set.univ) : μ = ν := by
  let C : Set (Set (α × β)) :=
    Set.image2 (· ×ˢ ·) {A | MeasurableSet A} {B | MeasurableSet B}
  have hgen : (inferInstance : MeasurableSpace (α × β)) =
      MeasurableSpace.generateFrom C := by
    simpa [C] using (generateFrom_prod (α := α) (β := β)).symm
  have hpi : IsPiSystem C := by
    intro s hs t ht hst
    rcases hs with ⟨A, hA, B, hB, rfl⟩
    rcases ht with ⟨A', hA', B', hB', rfl⟩
    change MeasurableSet A at hA
    change MeasurableSet A' at hA'
    change MeasurableSet B at hB
    change MeasurableSet B' at hB'
    refine ⟨A ∩ A', MeasurableSet.inter hA hA', B ∩ B',
      MeasurableSet.inter hB hB', ?_⟩
    ext z
    simp [and_assoc, and_left_comm]
  let : IsFiniteMeasure μ := ⟨hfinite⟩
  apply MeasureTheory.ext_of_generate_finite C hgen hpi ?_ huniv
  intro s hs
  rcases hs with ⟨A, hA, B, hB, rfl⟩
  change MeasurableSet A at hA
  change MeasurableSet B at hB
  exact hrect A hA B hB

/-- After projecting the stopped history and rational future to any finite ordered schedule, the
joint law factors through the endpoint state. This is the product-rectangle finite-cylinder
factorization that will be extended to the full path history. -/
theorem conditionedPositiveFutureHistory_finite_projection_compProd
    {ν : ℝ} {P : Measure BrownianPath} [IsFiniteMeasure P]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) {k n : ℕ}
    (pastTimes : Fin (k + 1) → ℝ≥0)
    (hPastPos : ∀ i, 0 < (pastTimes i : ℝ))
    (hPastBound : ∀ i, pastTimes i ≤ t)
    (hPastMono : StrictMono pastTimes)
    (hLast : pastTimes (Fin.last k) = t)
    (offsets : Fin n → ℚ) (hOffsetsPos : ∀ i, 0 < (offsets i : ℝ))
    (hMonoTotal : StrictMono (Fin.append pastTimes
      (fun i => t + (offsets i : ℝ).toNNReal)))
    (hMonoEndpoint : StrictMono (Fin.append (fun _ : Fin 1 => t)
      (fun i => t + (offsets i : ℝ).toNNReal))) :
    ((P.map (conditionedPositiveHistory t)) ⊗ₘ
        conditionedPositiveEndpointFutureKernel t P).map
        (fun z => ((fun i => z.1 ⟨pastTimes i, hPastBound i⟩),
          (fun i => z.2 (offsets i))) ) =
      P.map (fun p => ((fun i => -(p (pastTimes i))),
        (fun i => -(p (t + (offsets i : ℝ).toNNReal))))) := by
  classical
  let pastVector : BrownianPath → Fin (k + 1) → ℝ :=
    fun p i => -(p (pastTimes i))
  let futureTimes : Fin n → ℝ≥0 := fun i => t + (offsets i : ℝ).toNNReal
  let futureVector : BrownianPath → Fin n → ℝ := fun p i => -(p (futureTimes i))
  let historyProject : (Set.Iic t → ℝ) → Fin (k + 1) → ℝ :=
    fun h i => h ⟨pastTimes i, hPastBound i⟩
  let futureProject : (ℚ → ℝ) → Fin n → ℝ := fun y i => y (offsets i)
  let pairProject : ((Set.Iic t → ℝ) × (ℚ → ℝ)) →
      ((Fin (k + 1) → ℝ) × (Fin n → ℝ)) :=
    fun z => (historyProject z.1, futureProject z.2)
  let f : (Fin (k + 1) → ℝ) → ℝ≥0∞ :=
    conditionedPositiveFDDVectorDensity ν (fun i => (pastTimes i : ℝ))
  let g : (Fin (k + 1) → ℝ) → (Fin n → ℝ) → ℝ≥0∞ :=
    conditionedPositiveFutureVectorDensity ν (fun i => (pastTimes i : ℝ))
      (fun i => (futureTimes i : ℝ))
  let pastMeasure : Measure (Fin (k + 1) → ℝ) :=
    (volume : Measure (Fin (k + 1) → ℝ)).withDensity f
  let pastKernel : Kernel (Fin (k + 1) → ℝ) (Fin n → ℝ) :=
    (Kernel.const (Fin (k + 1) → ℝ) (volume : Measure (Fin n → ℝ))).withDensity g
  let stateKernel : Kernel ℝ (Fin n → ℝ) :=
    (Kernel.const ℝ (volume : Measure (Fin n → ℝ))).withDensity
      (fun x y => conditionedPositiveFutureVectorDensity ν
        (fun _ : Fin 1 => (t : ℝ)) (fun i => (t : ℝ) + (offsets i : ℝ))
        (fun _ => x) y)
  have hpastVectorMeas : Measurable pastVector := by
    apply measurable_pi_iff.mpr
    intro i
    exact (ContinuousMap.measurable_eval (pastTimes i)).neg
  have hfutureVectorMeas : Measurable futureVector := by
    apply measurable_pi_iff.mpr
    intro i
    exact (ContinuousMap.measurable_eval (futureTimes i)).neg
  have hhistoryProjectMeas : Measurable historyProject := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_pi_apply (⟨pastTimes i, hPastBound i⟩ : Set.Iic t)
  have hfutureProjectMeas : Measurable futureProject := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_pi_apply (offsets i)
  have hpairProjectMeas : Measurable pairProject :=
    hhistoryProjectMeas.comp measurable_fst |>.prodMk
      (hfutureProjectMeas.comp measurable_snd)
  have hfuturePosition : ∀ i, (t : ℝ) < (futureTimes i : ℝ) := by
    intro i
    have hq : 0 < ((offsets i : ℝ).toNNReal : ℝ) := by
      rw [Real.coe_toNNReal _ (hOffsetsPos i).le]
      exact hOffsetsPos i
    simp only [futureTimes, NNReal.coe_add]
    exact lt_add_of_pos_right _ hq
  have hfuturePos : ∀ i, 0 < (futureTimes i : ℝ) := by
    intro i
    exact lt_of_le_of_lt t.property (hfuturePosition i)
  have hsplit := negativeConditionedLaw_finitePastFuture_compProd hP
    pastTimes futureTimes hPastPos hfuturePos hMonoTotal
  have hPastFDD : P.map pastVector = pastMeasure := by
    change P.map (fun p i => -(p (pastTimes i))) =
      (volume : Measure (Fin (k + 1) → ℝ)).withDensity
        (fun x => ENNReal.ofReal (max 0 (conditionedPositiveFDDDensity ν
          (List.ofFn fun i => (pastTimes i : ℝ)) (List.ofFn fun i => x i))))
    exact negativeConditionedLaw_positiveFDD hP (k + 1) (by omega)
      pastTimes hPastPos hPastMono
  have hPastKernelLast : ∀ x,
      pastKernel x = stateKernel (x (Fin.last k)) := by
    intro x
    have htimes : (fun i : Fin n => (futureTimes i : ℝ)) =
        (fun i => (t : ℝ) + (offsets i : ℝ)) := by
      funext i
      simp [futureTimes, Real.coe_toNNReal _ (hOffsetsPos i).le]
    have hden : g x = (fun y => conditionedPositiveFutureVectorDensity ν
        (fun _ : Fin 1 => (t : ℝ)) (fun i => (t : ℝ) + (offsets i : ℝ))
        (fun _ => x (Fin.last k)) y) := by
      funext y
      simp [g, conditionedPositiveFutureVectorDensity, hLast, htimes]
    have hgMeas := measurable_conditionedPositiveFutureVectorDensity ν
      (fun i => (pastTimes i : ℝ)) (fun i => (futureTimes i : ℝ))
    have hsMeas : Measurable (Function.uncurry
        (fun z y => conditionedPositiveFutureVectorDensity ν
          (fun _ : Fin 1 => (t : ℝ)) (fun i => (t : ℝ) + (offsets i : ℝ))
          (fun _ => z) y)) := by
      have hinput : Measurable (fun w : ℝ × (Fin n → ℝ) =>
          ((fun _ : Fin 1 => w.1), w.2)) := by
        apply Measurable.prodMk
        · apply measurable_pi_iff.mpr
          intro i
          exact measurable_fst
        · exact measurable_snd
      exact (measurable_conditionedPositiveFutureVectorDensity ν
        (fun _ : Fin 1 => (t : ℝ)) (fun i => (t : ℝ) + (offsets i : ℝ))).comp hinput
    change ((Kernel.const (Fin (k + 1) → ℝ) (volume : Measure (Fin n → ℝ))).withDensity g) x =
      ((Kernel.const ℝ (volume : Measure (Fin n → ℝ))).withDensity
        (fun z y => conditionedPositiveFutureVectorDensity ν
          (fun _ : Fin 1 => (t : ℝ)) (fun i => (t : ℝ) + (offsets i : ℝ))
          (fun _ => z) y)) (x (Fin.last k))
    rw [Kernel.withDensity_apply _ hgMeas x, Kernel.withDensity_apply _ hsMeas
      (x (Fin.last k))]
    simpa [Kernel.const_apply] using congrArg
      (fun d => (volume : Measure (Fin n → ℝ)).withDensity d) hden
  have : IsSFiniteKernel pastKernel := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro x y
    exact ENNReal.ofReal_ne_top
  have hprojCondB (B : Set (Fin n → ℝ)) (hB : MeasurableSet B) :
      ∀ᵐ x ∂P.map (fun p => -(p t)),
        ((conditionedPositiveFutureKernel t P).map futureProject) x B =
          stateKernel x B := by
    have h := conditionedPositiveFutureKernel_finite_projection_eq_density
      hP t ht n offsets hOffsetsPos hMonoEndpoint B hB
    simpa [futureProject] using h
  have hX : Measurable (fun p : BrownianPath => -(p t)) :=
    (ContinuousMap.measurable_eval t).neg
  have hpastProjPath : (historyProject ∘ conditionedPositiveHistory t) = pastVector := by
    funext p i
    rfl
  have hfutureProjPath : (futureProject ∘ conditionedPositiveFutureRationalEvals t) =
      futureVector := by
    funext p i
    have hoffset : (⟨max (offsets i : ℝ) 0, le_max_right _ _⟩ : NNReal) =
        (offsets i : ℝ).toNNReal := by
      apply Subtype.ext
      simp [max_eq_left (le_of_lt (hOffsetsPos i)),
        Real.coe_toNNReal _ (hOffsetsPos i).le]
    simp [futureProject, conditionedPositiveFutureRationalEvals,
      conditionedPositiveFuturePath, futureVector, futureTimes, hoffset]
  have hrectangle : ∀ D, MeasurableSet D → ∀ B, MeasurableSet B →
      (((P.map (conditionedPositiveHistory t)) ⊗ₘ
        conditionedPositiveEndpointFutureKernel t P).map pairProject) (D ×ˢ B) =
      (P.map (fun p => (pastVector p, futureVector p))) (D ×ˢ B) := by
    intro D hD B hB
    have hpre : pairProject ⁻¹' (D ×ˢ B) =
        (historyProject ⁻¹' D) ×ˢ (futureProject ⁻¹' B) := by
      ext z
      simp [pairProject]
    have hmap :
        (((P.map (conditionedPositiveHistory t)) ⊗ₘ
          conditionedPositiveEndpointFutureKernel t P).map pairProject) (D ×ˢ B) =
          ((P.map (conditionedPositiveHistory t)) ⊗ₘ
            conditionedPositiveEndpointFutureKernel t P)
            (pairProject ⁻¹' (D ×ˢ B)) :=
      Measure.map_apply hpairProjectMeas (MeasurableSet.prod hD hB)
    rw [hmap, hpre, Measure.compProd_apply_prod
      (hD.preimage hhistoryProjectMeas) (hB.preimage hfutureProjectMeas)]
    have hfutureKernelMeas : Measurable (fun h : Set.Iic t → ℝ =>
        conditionedPositiveEndpointFutureKernel t P h (futureProject ⁻¹' B)) :=
      (Kernel.measurable_coe _ (hB.preimage hfutureProjectMeas)).comp measurable_id
    rw [MeasureTheory.setLIntegral_map
      (hD.preimage hhistoryProjectMeas) hfutureKernelMeas
      (measurable_conditionedPositiveHistory t)]
    have hcondAE : ∀ᵐ p ∂P,
        conditionedPositiveEndpointFutureKernel t P
          (conditionedPositiveHistory t p) (futureProject ⁻¹' B) =
          stateKernel (-(p t)) B := by
      have hA := hprojCondB B hB
      have hmapAE : ∀ᵐ p ∂P,
          ((conditionedPositiveFutureKernel t P).map futureProject) (-(p t)) B =
            stateKernel (-(p t)) B :=
        Filter.Eventually.filter_mono (P.tendsto_ae_map hX.aemeasurable) hA
      filter_upwards [hmapAE] with p hp
      have hmapEval :
          ((conditionedPositiveFutureKernel t P).map futureProject) (-(p t)) B =
            conditionedPositiveFutureKernel t P (-(p t)) (futureProject ⁻¹' B) := by
        rw [Kernel.map_apply' _ hfutureProjectMeas _ hB]
      have hendpointEval :
          conditionedPositiveEndpointFutureKernel t P
            (conditionedPositiveHistory t p) (futureProject ⁻¹' B) =
          conditionedPositiveFutureKernel t P (-(p t)) (futureProject ⁻¹' B) := by
        simp [conditionedPositiveEndpointFutureKernel,
          Kernel.comp_deterministic_eq_comap, Kernel.comap_apply,
          conditionedPositiveStateAt]
      rw [hendpointEval, ← hmapEval]
      exact hp
    have hleft : (historyProject ∘ conditionedPositiveHistory t) = pastVector :=
      hpastProjPath
    have hright : (futureProject ∘ conditionedPositiveFutureRationalEvals t) = futureVector :=
      hfutureProjPath
    have hpathEval : (fun p => (historyProject (conditionedPositiveHistory t p),
        futureProject (conditionedPositiveFutureRationalEvals t p))) =
        fun p => (pastVector p, futureVector p) := by
      funext p
      exact Prod.ext (congrFun hleft p) (congrFun hright p)
    have hpathSet :
        conditionedPositiveHistory t ⁻¹' historyProject ⁻¹' D = pastVector ⁻¹' D := by
      ext p
      change historyProject (conditionedPositiveHistory t p) ∈ D ↔ pastVector p ∈ D
      have heval : historyProject (conditionedPositiveHistory t p) = pastVector p := by
        change (historyProject ∘ conditionedPositiveHistory t) p = pastVector p
        exact congrFun hpastProjPath p
      exact Iff.of_eq (congrArg (fun x => x ∈ D) heval)
    have hstateEnd : ∀ᵐ p ∂P,
        conditionedPositiveEndpointFutureKernel t P
          (conditionedPositiveHistory t p) (futureProject ⁻¹' B) =
          stateKernel (pastVector p (Fin.last k)) B := by
      filter_upwards [hcondAE] with p hp
      have hendpoint : pastVector p (Fin.last k) = -(p t) := by
        simp [pastVector, hLast]
      simpa [hendpoint] using hp
    calc
      ∫⁻ p in conditionedPositiveHistory t ⁻¹' historyProject ⁻¹' D,
          conditionedPositiveEndpointFutureKernel t P
            (conditionedPositiveHistory t p) (futureProject ⁻¹' B) ∂P =
        ∫⁻ p in pastVector ⁻¹' D,
          stateKernel (pastVector p (Fin.last k)) B ∂P := by
        rw [hpathSet]
        exact MeasureTheory.setLIntegral_congr_fun_ae
          (hD.preimage hpastVectorMeas) (hstateEnd.mono fun _ hp _ => hp)
      _ = ∫⁻ p in pastVector ⁻¹' D, pastKernel (pastVector p) B ∂P := by
        apply MeasureTheory.setLIntegral_congr_fun (hD.preimage hpastVectorMeas)
        intro p hp
        exact (congrArg (fun μ : Measure (Fin n → ℝ) => μ B)
          (hPastKernelLast (pastVector p))).symm
      _ = (P.map (fun p => (pastVector p, futureVector p))) (D ×ˢ B) := by
        have hjoint : P.map (fun p => (pastVector p, futureVector p)) =
            pastMeasure ⊗ₘ pastKernel := by
          simpa [pastVector, futureVector, futureTimes, pastMeasure, f, pastKernel, g] using hsplit
        rw [hjoint, Measure.compProd_apply_prod hD hB]
        rw [← hPastFDD]
        rw [MeasureTheory.setLIntegral_map hD
          (Kernel.measurable_coe pastKernel hB) hpastVectorMeas]
  have hfin : (((P.map (conditionedPositiveHistory t)) ⊗ₘ
      conditionedPositiveEndpointFutureKernel t P).map pairProject) Set.univ < ∞ := by
    rw [Measure.map_apply hpairProjectMeas MeasurableSet.univ]
    simp [Measure.compProd_apply_univ]
  exact measure_eq_of_prod_rectangles _ _ hfin hrectangle (by
    simpa using hrectangle Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ)

end DOZZ.Proofs

end
