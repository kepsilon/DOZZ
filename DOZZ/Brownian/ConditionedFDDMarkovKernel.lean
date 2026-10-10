/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedFDDMeasure
public import DOZZ.Brownian.ConditionedKernelProbability
public import DOZZ.Brownian.ConditionedEntranceProbability
public import Mathlib.Probability.Kernel.Composition.WithDensity
public import Mathlib.Probability.Kernel.CondDistrib

/-!
# Real-state transition kernel for the conditioned entrance process

The positive-state transition density is extended to a Markov kernel on all real states. The
extension below zero is chosen only to make the kernel total; the conditioned entrance law is
supported on positive states.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- A total real-state transition kernel. On positive states it is the explicit conditioned
Doob transition law; on nonpositive states it uses the positive entrance law at time one. -/
noncomputable def conditionedPositiveTransitionKernelOnReal (ν dt : ℝ) : Kernel ℝ ℝ :=
  Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ)) (fun x y =>
    if 0 < x then ENNReal.ofReal (conditionedPositiveTransitionDensity ν dt x y)
    else ENNReal.ofReal (conditionedPositiveEntranceDensity ν 1 y))

instance isSFiniteKernel_conditionedPositiveTransitionKernelDensity (ν dt : ℝ) :
    IsSFiniteKernel ((Kernel.const ℝ (volume : Measure ℝ)).withDensity
      (fun x y => if 0 < x then
        ENNReal.ofReal (conditionedPositiveTransitionDensity ν dt x y)
      else ENNReal.ofReal (conditionedPositiveEntranceDensity ν 1 y))) := by
  apply Kernel.IsSFiniteKernel.withDensity
  intro x y
  split_ifs <;> simp

theorem measurable_conditionedPositiveTransitionKernelOnReal_density (ν dt : ℝ) :
    Measurable (Function.uncurry (fun x y =>
      if 0 < x then ENNReal.ofReal (conditionedPositiveTransitionDensity ν dt x y)
      else ENNReal.ofReal (conditionedPositiveEntranceDensity ν 1 y))) := by
  change Measurable (fun z : ℝ × ℝ =>
    if 0 < z.1 then ENNReal.ofReal (conditionedPositiveTransitionDensity ν dt z.1 z.2)
    else ENNReal.ofReal (conditionedPositiveEntranceDensity ν 1 z.2))
  apply Measurable.ite
  · exact measurableSet_lt measurable_const measurable_fst
  · exact ENNReal.measurable_ofReal.comp
      (measurable_conditionedPositiveTransitionDensity_pair ν dt)
  · exact ENNReal.measurable_ofReal.comp
      ((measurable_conditionedPositiveEntranceDensity_arg ν 1).comp measurable_snd)

theorem conditionedPositiveTransitionKernelOnReal_apply_of_pos
    {ν dt x : ℝ} (hx : 0 < x) :
    conditionedPositiveTransitionKernelOnReal ν dt x =
      conditionedPositiveTransitionMeasure ν dt x := by
  rw [conditionedPositiveTransitionKernelOnReal, Kernel.withDensity_apply
    (Kernel.const ℝ (volume : Measure ℝ))
    (measurable_conditionedPositiveTransitionKernelOnReal_density ν dt), Kernel.const_apply]
  simp [conditionedPositiveTransitionMeasure, hx]

theorem conditionedPositiveTransitionKernelOnReal_apply_of_nonpos
    {ν dt x : ℝ} (hx : x ≤ 0) :
    conditionedPositiveTransitionKernelOnReal ν dt x =
      conditionedPositiveEntranceMeasure ν 1 := by
  rw [conditionedPositiveTransitionKernelOnReal, Kernel.withDensity_apply
    (Kernel.const ℝ (volume : Measure ℝ))
    (measurable_conditionedPositiveTransitionKernelOnReal_density ν dt), Kernel.const_apply]
  simp [conditionedPositiveEntranceMeasure, not_lt.mpr hx]

theorem isMarkovKernel_conditionedPositiveTransitionKernelOnReal
    (ν dt : ℝ) (hν : 0 ≤ ν) (hdt : 0 < dt) :
    IsMarkovKernel (conditionedPositiveTransitionKernelOnReal ν dt) := by
  refine ⟨fun x => ?_⟩
  by_cases hx : 0 < x
  · rw [conditionedPositiveTransitionKernelOnReal_apply_of_pos hx]
    exact isProbabilityMeasure_conditionedPositiveTransitionMeasure ν dt x hν hdt hx
  · have hx' : x ≤ 0 := le_of_not_gt hx
    rw [conditionedPositiveTransitionKernelOnReal_apply_of_nonpos hx']
    exact isProbabilityMeasure_conditionedPositiveEntranceMeasure ν 1 hν (by norm_num)

/-- The two-time law is the entrance marginal followed by the total real-state transition kernel.
This identifies the explicit FDD factorization with a composition product, the measure identity
needed for conditional-distribution uniqueness. -/
theorem negativeConditionedLaw_twoTime_compProd
    {ν : ℝ} {P : Measure BrownianPath} (hP : IsNegativeConditionedBrownianLaw ν P)
    (t₀ dt : NNReal) (ht₀ : 0 < (t₀ : ℝ)) (hdt : 0 < (dt : ℝ)) :
    P.map (fun p => (-(p t₀), -(p (t₀ + dt)))) =
      conditionedPositiveEntranceMeasure ν (t₀ : ℝ) ⊗ₘ
        conditionedPositiveTransitionKernelOnReal ν (dt : ℝ) := by
  have hentrance : Measurable (fun x : ℝ =>
      ENNReal.ofReal (conditionedPositiveEntranceDensity ν (t₀ : ℝ) x)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_conditionedPositiveEntranceDensity_arg ν (t₀ : ℝ))
  have htransition := measurable_conditionedPositiveTransitionKernelOnReal_density
    ν (dt : ℝ)
  have hdensity : (fun z : ℝ × ℝ =>
      ENNReal.ofReal (conditionedPositiveEntranceDensity ν (t₀ : ℝ) z.1) *
        (if 0 < z.1 then
          ENNReal.ofReal (conditionedPositiveTransitionDensity ν (dt : ℝ) z.1 z.2)
        else ENNReal.ofReal (conditionedPositiveEntranceDensity ν 1 z.2))) =
      (fun z => ENNReal.ofReal (max 0
        (conditionedPositiveEntranceDensity ν (t₀ : ℝ) z.1 *
          conditionedPositiveTransitionDensity ν (dt : ℝ) z.1 z.2))) := by
    funext z
    by_cases hx : 0 < z.1
    · have he : 0 ≤ conditionedPositiveEntranceDensity ν (t₀ : ℝ) z.1 :=
        conditionedPositiveEntranceDensity_nonneg hP.1 ht₀ z.1
      have ht : 0 ≤ conditionedPositiveTransitionDensity ν (dt : ℝ) z.1 z.2 :=
        conditionedPositiveTransitionDensity_nonneg hP.1 hdt hx z.2
      simp [hx, max_eq_right (mul_nonneg he ht)]
      rw [← ENNReal.ofReal_mul he]
    · have hx' : z.1 ≤ 0 := le_of_not_gt hx
      have he : conditionedPositiveEntranceDensity ν (t₀ : ℝ) z.1 = 0 := by
        simp [conditionedPositiveEntranceDensity, not_lt.mpr hx']
      simp [hx, he]
  have hcompAux :
      ((volume : Measure ℝ).withDensity
          (fun x => ENNReal.ofReal (conditionedPositiveEntranceDensity ν (t₀ : ℝ) x))) ⊗ₘ
        ((Kernel.const ℝ (volume : Measure ℝ)).withDensity
          (fun x y => if 0 < x then
            ENNReal.ofReal (conditionedPositiveTransitionDensity ν (dt : ℝ) x y)
          else ENNReal.ofReal (conditionedPositiveEntranceDensity ν 1 y))) =
        ((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity (fun z =>
          ENNReal.ofReal (conditionedPositiveEntranceDensity ν (t₀ : ℝ) z.1) *
          (if 0 < z.1 then
              ENNReal.ofReal (conditionedPositiveTransitionDensity ν (dt : ℝ) z.1 z.2)
            else ENNReal.ofReal (conditionedPositiveEntranceDensity ν 1 z.2))) := by
    calc
      _ = ((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity (fun z =>
          ENNReal.ofReal (conditionedPositiveEntranceDensity ν (t₀ : ℝ) z.1) *
            (if 0 < z.1 then
              ENNReal.ofReal (conditionedPositiveTransitionDensity ν (dt : ℝ) z.1 z.2)
            else ENNReal.ofReal (conditionedPositiveEntranceDensity ν 1 z.2))) := by
          rw [Measure.withDensity_compProd_withDensity
            (μ := (volume : Measure ℝ))
            (κ := Kernel.const ℝ (volume : Measure ℝ)) hentrance htransition,
            Measure.compProd_const]
      _ = _ := by rw [← Measure.volume_eq_prod ℝ ℝ]
  have hcomp : conditionedPositiveEntranceMeasure ν (t₀ : ℝ) ⊗ₘ
      conditionedPositiveTransitionKernelOnReal ν (dt : ℝ) =
        (volume : Measure (ℝ × ℝ)).withDensity (fun z =>
          ENNReal.ofReal (conditionedPositiveEntranceDensity ν (t₀ : ℝ) z.1) *
            (if 0 < z.1 then
              ENNReal.ofReal (conditionedPositiveTransitionDensity ν (dt : ℝ) z.1 z.2)
            else ENNReal.ofReal (conditionedPositiveEntranceDensity ν 1 z.2))) := by
    rw [conditionedPositiveEntranceMeasure, conditionedPositiveTransitionKernelOnReal,
      hcompAux, ← Measure.volume_eq_prod ℝ ℝ]
  rw [negativeConditionedLaw_twoTime_positiveFDD hP t₀ dt ht₀ hdt]
  rw [hcomp]
  congr 1
  funext z
  exact (congrFun hdensity z).symm

/-- At a deterministic positive time, the next state has the explicit Doob transition law
conditioned on the current state. This is the one-step conditional-distribution form of the FDD
factorization. -/
theorem negativeConditionedLaw_condDistrib_oneStep
    {ν : ℝ} {P : Measure BrownianPath} [IsFiniteMeasure P]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (t₀ dt : NNReal) (ht₀ : 0 < (t₀ : ℝ)) (hdt : 0 < (dt : ℝ)) :
    condDistrib (fun p : BrownianPath => -(p (t₀ + dt)))
        (fun p => -(p t₀)) P =ᵐ[P.map (fun p => -(p t₀))]
      conditionedPositiveTransitionKernelOnReal ν (dt : ℝ) := by
  have : IsMarkovKernel (conditionedPositiveTransitionKernelOnReal ν (dt : ℝ)) :=
    isMarkovKernel_conditionedPositiveTransitionKernelOnReal ν (dt : ℝ) hP.1 hdt
  have : IsProbabilityMeasure (conditionedPositiveEntranceMeasure ν (t₀ : ℝ)) :=
    isProbabilityMeasure_conditionedPositiveEntranceMeasure ν (t₀ : ℝ) hP.1 ht₀
  let X : BrownianPath → ℝ := fun p => -(p t₀)
  let Y : BrownianPath → ℝ := fun p => -(p (t₀ + dt))
  have hX : Measurable X := (ContinuousMap.measurable_eval t₀).neg
  have hY : Measurable Y := (ContinuousMap.measurable_eval (t₀ + dt)).neg
  have hpair := negativeConditionedLaw_twoTime_compProd hP t₀ dt ht₀ hdt
  have hstate : P.map X = conditionedPositiveEntranceMeasure ν (t₀ : ℝ) := by
    calc
      P.map X = (P.map fun p => (X p, Y p)).fst := by
        rw [Measure.fst_map_prodMk hX hY]
      _ = (conditionedPositiveEntranceMeasure ν (t₀ : ℝ) ⊗ₘ
          conditionedPositiveTransitionKernelOnReal ν (dt : ℝ)).fst :=
        congrArg Measure.fst hpair
      _ = conditionedPositiveEntranceMeasure ν (t₀ : ℝ) := Measure.fst_compProd _ _
  have hjoint : P.map (fun p => (X p, Y p)) = P.map X ⊗ₘ
      conditionedPositiveTransitionKernelOnReal ν (dt : ℝ) := by
    rw [hstate]
    exact hpair
  exact condDistrib_ae_eq_of_measure_eq_compProd hX.aemeasurable hY.aemeasurable hjoint


end DOZZ.Proofs

end
