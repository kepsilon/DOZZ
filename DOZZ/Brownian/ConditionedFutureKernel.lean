/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.IsNegativeConditionedBrownianLaw
public import DOZZ.Statements.Brownian.BrownianPathMeasurableSpaceEqISupComapEval
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Rational-coordinate kernel for a conditioned entrance future

Continuous-path space is not currently registered as a standard Borel space in this checkout.
The future is therefore disintegrated through its countable rational evaluation sequence. This
retains the path sigma algebra once the rational evaluations are shown to generate it, and avoids
any extension of finite-dimensional distributions.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Two finite measures on a product of coordinate spaces agree if they agree on every rectangle
whose factors are measurable cylinders. This is the π-system/monotone-class extension used to
turn finite past/future coordinate identities into a full path-history/future factorization. -/
theorem measure_eq_of_cylinder_rectangles
    {ι ι' : Type*} {α : ι → Type*} {β : ι' → Type*}
    [∀ i, MeasurableSpace (α i)] [∀ j, MeasurableSpace (β j)]
    (μ ν : Measure ((∀ i, α i) × (∀ j, β j))) [IsFiniteMeasure μ]
    (hrect : ∀ s ∈ MeasureTheory.measurableCylinders α,
      ∀ t ∈ MeasureTheory.measurableCylinders β, μ (s ×ˢ t) = ν (s ×ˢ t))
    (huniv : μ Set.univ = ν Set.univ) : μ = ν := by
  let C : Set (Set ((∀ i, α i) × (∀ j, β j))) :=
    Set.image2 (· ×ˢ ·) (MeasureTheory.measurableCylinders α)
      (MeasureTheory.measurableCylinders β)
  have hgen : (inferInstance : MeasurableSpace ((∀ i, α i) × (∀ j, β j))) =
      MeasurableSpace.generateFrom C := by
    have hαspan : IsCountablySpanning (MeasureTheory.measurableCylinders α) :=
      ⟨fun _ => Set.univ, fun _ => MeasureTheory.univ_mem_measurableCylinders α,
        by ext x; simp⟩
    have hβspan : IsCountablySpanning (MeasureTheory.measurableCylinders β) :=
      ⟨fun _ => Set.univ, fun _ => MeasureTheory.univ_mem_measurableCylinders β,
        by ext x; simp⟩
    exact (_root_.generateFrom_eq_prod
      (hC := MeasureTheory.generateFrom_measurableCylinders)
      (hD := MeasureTheory.generateFrom_measurableCylinders) hαspan hβspan).symm
  have hpi : IsPiSystem C := by
    intro u hu v hv huv
    rcases hu with ⟨s, hs, t, ht, rfl⟩
    rcases hv with ⟨s', hs', t', ht', rfl⟩
    refine ⟨s ∩ s', MeasureTheory.inter_mem_measurableCylinders hs hs',
      t ∩ t', MeasureTheory.inter_mem_measurableCylinders ht ht', ?_⟩
    ext z
    simp [and_assoc, and_left_comm]
  apply MeasureTheory.ext_of_generate_finite C hgen hpi ?_ huniv
  intro u hu
  rcases hu with ⟨s, hs, t, ht, rfl⟩
  exact hrect s hs t ht

/-- The positive-coordinate state of a negative conditioned path at time `t`. -/
def conditionedPositiveStateAt (t : ℝ≥0) (p : BrownianPath) : ℝ := -(p t)

/-- The positive-coordinate future path, with time origin moved to the deterministic time `t`. -/
def conditionedPositiveFuturePath (t : ℝ≥0) (p : BrownianPath) : BrownianPath :=
  ⟨fun s => -(p (t + s)), (p.continuous.comp (continuous_const.add continuous_id)).neg⟩

/-- The positive-coordinate future on nonnegative rational time offsets. -/
def conditionedPositiveFutureRationalEvals (t : ℝ≥0) (p : BrownianPath) : ℚ → ℝ :=
  fun q => conditionedPositiveFuturePath t p ⟨max (q : ℝ) 0, le_max_right _ _⟩

/-- The positive-coordinate process value at an absolute time. -/
def conditionedPositiveProcessValue (s : ℝ≥0) (p : BrownianPath) : ℝ := -(p s)

/-- The whole positive-coordinate history up to a deterministic time, recorded by its evaluations
on `Set.Iic t`. -/
def conditionedPositiveHistory (t : ℝ≥0) (p : BrownianPath) : Set.Iic t → ℝ :=
  fun s => conditionedPositiveProcessValue s.1 p

/-- The raw natural sigma algebra of the positive-coordinate process at time `t`. -/
@[instance_reducible]
def conditionedPositiveNaturalFiltration (t : ℝ≥0) : MeasurableSpace BrownianPath :=
  ⨆ s : ℝ≥0, ⨆ (_ : s ≤ t),
    MeasurableSpace.comap (conditionedPositiveProcessValue s) inferInstance

theorem measurable_conditionedPositiveProcessValue (s : ℝ≥0) :
    Measurable (conditionedPositiveProcessValue s) :=
  (ContinuousMap.measurable_eval s).neg

theorem measurable_conditionedPositiveHistory (t : ℝ≥0) :
    Measurable (conditionedPositiveHistory t) := by
  apply measurable_pi_iff.mpr
  intro s
  exact measurable_conditionedPositiveProcessValue s.1

/-- The stopped-history evaluation map generates precisely the raw natural sigma algebra. -/
theorem conditionedPositiveHistory_sigma_eq (t : ℝ≥0) :
    MeasurableSpace.comap (conditionedPositiveHistory t) inferInstance =
      conditionedPositiveNaturalFiltration t := by
  change MeasurableSpace.comap
      (fun p (s : Set.Iic t) => conditionedPositiveProcessValue s.1 p) inferInstance = _
  rw [MeasurableSpace.comap_process_pi]
  apply le_antisymm
  · refine iSup_le fun s => ?_
    exact le_iSup_of_le s.1 (le_iSup_of_le s.2 le_rfl)
  · refine iSup_le fun s => iSup_le fun hst => ?_
    exact le_iSup_of_le ⟨s, hst⟩ le_rfl

@[simp]
theorem conditionedPositiveHistory_current (t : ℝ≥0) (p : BrownianPath) :
    conditionedPositiveHistory t p ⟨t, le_rfl⟩ = conditionedPositiveStateAt t p := rfl

/-- The sigma algebra generated by all rational evaluations of the positive-coordinate future. -/
@[instance_reducible]
def conditionedPositiveFutureRationalSigma (t : ℝ≥0) : MeasurableSpace BrownianPath :=
  MeasurableSpace.comap (conditionedPositiveFutureRationalEvals t) inferInstance

@[fun_prop]
theorem measurable_conditionedPositiveStateAt (t : ℝ≥0) :
    Measurable (conditionedPositiveStateAt t) :=
  (ContinuousMap.measurable_eval t).neg

theorem measurable_conditionedPositiveFutureRationalEvals (t : ℝ≥0) :
    Measurable (conditionedPositiveFutureRationalEvals t) := by
  apply measurable_pi_iff.mpr
  intro q
  change Measurable (fun p : BrownianPath =>
    conditionedPositiveFuturePath t p ⟨max (q : ℝ) 0, le_max_right _ _⟩)
  exact (ContinuousMap.measurable_eval _).comp
    (by
      apply ContinuousMap.measurable_iff_eval.mpr
      intro s
      exact (ContinuousMap.measurable_eval (t + s)).neg)


/-- Rational future evaluations generate the whole Borel sigma algebra on continuous paths.
Each real future evaluation is the pointwise limit of rational future evaluations from above. -/
theorem conditionedPositiveFutureRationalSigma_eq (t : ℝ≥0) :
    conditionedPositiveFutureRationalSigma t =
      MeasurableSpace.comap (conditionedPositiveFuturePath t)
        ContinuousMap.measurableSpace := by
  let mRat := conditionedPositiveFutureRationalSigma t
  have hfutureEval (s : ℝ≥0) :
      Measurable[mRat] (fun p : BrownianPath => conditionedPositiveFuturePath t p s) := by
    let qfun : ℕ → ℚ := (Real.exists_seq_rat_strictAnti_tendsto (s : ℝ)).choose
    have hqfun : StrictAnti qfun ∧ (∀ n, (s : ℝ) < (qfun n : ℝ)) ∧
        Tendsto (fun n => (qfun n : ℝ)) atTop (𝓝 (s : ℝ)) :=
      (Real.exists_seq_rat_strictAnti_tendsto (s : ℝ)).choose_spec
    let rfun : ℕ → ℝ≥0 := fun n => ⟨(qfun n : ℝ),
      le_trans s.property (hqfun.2.1 n).le⟩
    have hrfun_coe : Tendsto (fun n => (rfun n : ℝ)) atTop (𝓝 (s : ℝ)) := hqfun.2.2
    have hrfun : Tendsto rfun atTop (𝓝 s) := NNReal.tendsto_coe.mp hrfun_coe
    have hseq : Measurable[mRat] (conditionedPositiveFutureRationalEvals t) := by
      exact comap_measurable (conditionedPositiveFutureRationalEvals t)
    have happrox : ∀ n, Measurable[mRat]
        (fun p : BrownianPath => conditionedPositiveFuturePath t p (rfun n)) := by
      intro n
      have hcoord : Measurable[mRat]
          (fun p => conditionedPositiveFutureRationalEvals t p (qfun n)) :=
        (measurable_pi_apply (qfun n)).comp hseq
      have hcoord_eq : (fun p : BrownianPath =>
          conditionedPositiveFutureRationalEvals t p (qfun n)) =
          fun p => conditionedPositiveFuturePath t p (rfun n) := by
        funext p
        simp [conditionedPositiveFutureRationalEvals, rfun,
          max_eq_left (le_trans s.property (hqfun.2.1 n).le)]
      rw [hcoord_eq] at hcoord
      exact hcoord
    have hlimit : ∀ p : BrownianPath,
        Tendsto (fun n => conditionedPositiveFuturePath t p (rfun n)) atTop
          (𝓝 (conditionedPositiveFuturePath t p s)) := by
      intro p
      exact (conditionedPositiveFuturePath t p).continuous.continuousAt.tendsto.comp hrfun
    have hlimitFun : Tendsto
        (fun n => fun p : BrownianPath => conditionedPositiveFuturePath t p (rfun n)) atTop
        (𝓝 fun p : BrownianPath => conditionedPositiveFuturePath t p s) :=
      tendsto_pi_nhds.mpr hlimit
    exact measurable_of_tendsto_metrizable happrox hlimitFun
  have hfutureMeas :
      Measurable[mRat, ContinuousMap.measurableSpace]
        (conditionedPositiveFuturePath t) := by
    exact ContinuousMap.measurable_iff_eval.mpr hfutureEval
  apply le_antisymm
  · have hseq : Measurable[MeasurableSpace.comap (conditionedPositiveFuturePath t)
        ContinuousMap.measurableSpace]
        (conditionedPositiveFutureRationalEvals t) := by
      let : MeasurableSpace BrownianPath :=
        MeasurableSpace.comap (conditionedPositiveFuturePath t)
          ContinuousMap.measurableSpace
      apply measurable_pi_iff.mpr
      intro q
      exact (ContinuousMap.measurable_eval
        (⟨max (q : ℝ) 0, le_max_right _ _⟩ : ℝ≥0)).comp
          (comap_measurable (m := ContinuousMap.measurableSpace)
            (conditionedPositiveFuturePath t))
    change MeasurableSpace.comap (conditionedPositiveFutureRationalEvals t)
      inferInstance ≤ MeasurableSpace.comap (conditionedPositiveFuturePath t)
        ContinuousMap.measurableSpace
    exact hseq.comap_le
  · change MeasurableSpace.comap (conditionedPositiveFuturePath t)
        ContinuousMap.measurableSpace ≤ mRat
    exact hfutureMeas.comap_le

/-- The conditional law of the rational future evaluation sequence given the current radial
state. -/
noncomputable def conditionedPositiveFutureKernel (t : ℝ≥0)
    (P : Measure BrownianPath) [IsFiniteMeasure P] : Kernel ℝ (ℚ → ℝ) :=
  condDistrib (conditionedPositiveFutureRationalEvals t)
    (conditionedPositiveStateAt t) P

/-- The regular conditional law of the rational future sequence given the complete path history
up to deterministic time `t`. -/
noncomputable def conditionedPositiveFutureHistoryKernel (t : ℝ≥0)
    (P : Measure BrownianPath) [IsFiniteMeasure P] :
    Kernel (Set.Iic t → ℝ) (ℚ → ℝ) :=
  condDistrib (conditionedPositiveFutureRationalEvals t)
    (conditionedPositiveHistory t) P

/-- The candidate Markov kernel that first reads the endpoint of a stopped history and then uses
the state-conditioned future kernel. -/
noncomputable def conditionedPositiveEndpointFutureKernel (t : ℝ≥0)
    (P : Measure BrownianPath) [IsFiniteMeasure P] :
    Kernel (Set.Iic t → ℝ) (ℚ → ℝ) :=
  conditionedPositiveFutureKernel t P ∘ₖ
    Kernel.deterministic (fun h : Set.Iic t → ℝ => h ⟨t, le_rfl⟩) (by fun_prop)

instance isMarkovKernel_conditionedPositiveFutureKernel (t : ℝ≥0)
    (P : Measure BrownianPath) [IsFiniteMeasure P] :
    IsMarkovKernel (conditionedPositiveFutureKernel t P) := by
  dsimp [conditionedPositiveFutureKernel]
  infer_instance

instance isMarkovKernel_conditionedPositiveFutureHistoryKernel (t : ℝ≥0)
    (P : Measure BrownianPath) [IsFiniteMeasure P] :
    IsMarkovKernel (conditionedPositiveFutureHistoryKernel t P) := by
  dsimp [conditionedPositiveFutureHistoryKernel]
  infer_instance

instance isMarkovKernel_conditionedPositiveEndpointFutureKernel (t : ℝ≥0)
    (P : Measure BrownianPath) [IsFiniteMeasure P] :
    IsMarkovKernel (conditionedPositiveEndpointFutureKernel t P) := by
  dsimp [conditionedPositiveEndpointFutureKernel]
  infer_instance

/-- The state/future-coordinate law is the composition product of the state marginal and its
regular conditional future kernel. -/
theorem conditionedPositiveFutureKernel_compProd (t : ℝ≥0)
    (P : Measure BrownianPath) [IsFiniteMeasure P] :
    (P.map (conditionedPositiveStateAt t)) ⊗ₘ conditionedPositiveFutureKernel t P =
      P.map (fun p =>
        (conditionedPositiveStateAt t p, conditionedPositiveFutureRationalEvals t p)) := by
  exact compProd_map_condDistrib
    (measurable_conditionedPositiveStateAt t).aemeasurable
    (measurable_conditionedPositiveFutureRationalEvals t).aemeasurable


/-- The full-history kernel is the endpoint kernel exactly when the joint history/future law
factorizes through that endpoint kernel. This is the measure identity to prove from the FDD split. -/
theorem conditionedPositiveFutureHistoryKernel_eq_endpoint_iff_compProd
    (t : ℝ≥0) (P : Measure BrownianPath) [IsFiniteMeasure P] :
    conditionedPositiveFutureHistoryKernel t P =ᵐ[P.map (conditionedPositiveHistory t)]
        conditionedPositiveEndpointFutureKernel t P ↔
      P.map (fun p =>
        (conditionedPositiveHistory t p, conditionedPositiveFutureRationalEvals t p)) =
        (P.map (conditionedPositiveHistory t)) ⊗ₘ
          conditionedPositiveEndpointFutureKernel t P := by
  simpa [conditionedPositiveFutureHistoryKernel] using
    (condDistrib_ae_eq_iff_measure_eq_compProd
      (μ := P)
      (hX := (measurable_conditionedPositiveHistory t).aemeasurable)
      (hY := (measurable_conditionedPositiveFutureRationalEvals t).aemeasurable)
      (κ := conditionedPositiveEndpointFutureKernel t P))

/-- It is enough to check the full-history/future composition-product identity on rectangles
whose history and future factors are finite-coordinate cylinders. The preceding general π-system
lemma extends that finite-coordinate check to the complete product sigma algebra. -/
theorem conditionedPositiveFutureHistoryKernel_ae_eq_endpoint_of_cylinder_rectangles
    (t : ℝ≥0) (P : Measure BrownianPath) [IsFiniteMeasure P]
    (hrect : ∀ s ∈ MeasureTheory.measurableCylinders
        (fun _ : Set.Iic t => ℝ),
      ∀ u ∈ MeasureTheory.measurableCylinders (fun _ : ℚ => ℝ),
        P.map (fun p =>
          (conditionedPositiveHistory t p, conditionedPositiveFutureRationalEvals t p))
            (s ×ˢ u) =
          ((P.map (conditionedPositiveHistory t)) ⊗ₘ
            conditionedPositiveEndpointFutureKernel t P) (s ×ˢ u)) :
    conditionedPositiveFutureHistoryKernel t P =ᵐ[P.map (conditionedPositiveHistory t)]
      conditionedPositiveEndpointFutureKernel t P := by
  have huniv := hrect Set.univ (MeasureTheory.univ_mem_measurableCylinders
      (fun _ : Set.Iic t => ℝ)) Set.univ
    (MeasureTheory.univ_mem_measurableCylinders (fun _ : ℚ => ℝ))
  have hcomp : P.map (fun p =>
      (conditionedPositiveHistory t p, conditionedPositiveFutureRationalEvals t p)) =
        (P.map (conditionedPositiveHistory t)) ⊗ₘ
          conditionedPositiveEndpointFutureKernel t P := by
    apply measure_eq_of_cylinder_rectangles
    · intro s hs u hu
      exact hrect s hs u hu
    · simpa using huniv
  exact (conditionedPositiveFutureHistoryKernel_eq_endpoint_iff_compProd t P).mpr hcomp


/-- A finite rational-time vector of the future, conditioned on the current state, is the
corresponding projection of the rational-sequence conditional kernel. -/
theorem conditionedPositiveFutureKernel_finite_projection (t : ℝ≥0)
    (P : Measure BrownianPath) [IsFiniteMeasure P] {n : ℕ}
    (times : Fin n → ℚ) :
    condDistrib (fun p i => conditionedPositiveFutureRationalEvals t p (times i))
        (conditionedPositiveStateAt t) P =ᵐ[P.map (conditionedPositiveStateAt t)]
      (conditionedPositiveFutureKernel t P).map (fun x i => x (times i)) := by
  let project : (ℚ → ℝ) → (Fin n → ℝ) := fun x i => x (times i)
  have hproject : Measurable project := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_pi_apply (times i)
  have h := condDistrib_comp (μ := P)
    (hX := (measurable_conditionedPositiveStateAt t).aemeasurable)
    (hY := (measurable_conditionedPositiveFutureRationalEvals t).aemeasurable)
    (f := project) hproject
  have hfun : (fun p i => conditionedPositiveFutureRationalEvals t p (times i)) =
      project ∘ conditionedPositiveFutureRationalEvals t := by
    funext p
    funext i
    rfl
  rw [hfun]
  simpa [conditionedPositiveFutureKernel, project] using h


/-- Every integrable measurable functional of the entire rational future sequence has conditional
expectation given the complete deterministic-time history equal to its integral under the history
kernel. -/
theorem conditionedPositiveFutureHistoryKernel_condExp (t : ℝ≥0)
    (P : Measure BrownianPath) [IsFiniteMeasure P]
    (G : (ℚ → ℝ) → ℝ) (hG : StronglyMeasurable G)
    (hGint : Integrable (fun p => G (conditionedPositiveFutureRationalEvals t p)) P) :
    P[fun p => G (conditionedPositiveFutureRationalEvals t p) |
        (inferInstance : MeasurableSpace (Set.Iic t → ℝ)).comap
          (conditionedPositiveHistory t)] =ᵐ[P]
      fun p => ∫ x, G x ∂conditionedPositiveFutureHistoryKernel t P
        (conditionedPositiveHistory t p) := by
  simpa [conditionedPositiveFutureHistoryKernel] using
    (condExp_ae_eq_integral_condDistrib
      (μ := P)
      (hX := measurable_conditionedPositiveHistory t)
      (hY := (measurable_conditionedPositiveFutureRationalEvals t).aemeasurable)
      (f := G) hG hGint)

/-- Once the history and endpoint conditional kernels are identified from the FDDs, the
full-filtration conditional expectation is the endpoint-kernel integral for every integrable
future functional. -/
theorem conditionedPositiveFutureHistoryKernel_condExp_of_ae_eq_endpoint
    (t : ℝ≥0) (P : Measure BrownianPath) [IsFiniteMeasure P]
    (G : (ℚ → ℝ) → ℝ) (hG : StronglyMeasurable G)
    (hGint : Integrable (fun p => G (conditionedPositiveFutureRationalEvals t p)) P)
    (hkernel : ∀ᵐ p ∂P,
      conditionedPositiveFutureHistoryKernel t P (conditionedPositiveHistory t p) =
        conditionedPositiveFutureKernel t P (conditionedPositiveStateAt t p)) :
    P[fun p => G (conditionedPositiveFutureRationalEvals t p) |
        conditionedPositiveNaturalFiltration t] =ᵐ[P]
      fun p => ∫ x, G x ∂conditionedPositiveFutureKernel t P
        (conditionedPositiveStateAt t p) := by
  rw [← conditionedPositiveHistory_sigma_eq t]
  have hHistory := conditionedPositiveFutureHistoryKernel_condExp t P G hG hGint
  filter_upwards [hHistory, hkernel] with p hp hk
  calc
    P[fun p => G (conditionedPositiveFutureRationalEvals t p) |
        (inferInstance : MeasurableSpace (Set.Iic t → ℝ)).comap
          (conditionedPositiveHistory t)] p =
      ∫ x, G x ∂conditionedPositiveFutureHistoryKernel t P
        (conditionedPositiveHistory t p) := hp
    _ = ∫ x, G x ∂conditionedPositiveFutureKernel t P
        (conditionedPositiveStateAt t p) := by rw [hk]

end DOZZ.Proofs

end
