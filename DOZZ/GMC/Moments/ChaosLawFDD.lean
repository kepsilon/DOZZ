/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.StrongLaw
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import DOZZ.GMC.Moments.ExactScale

/-! Transfer of laws through empirical approximations.

This is the limit step: once finite sampled chaos approximants have the same law and converge almost
surely to the Wick integrals, bounded continuous tests pass to the limit by dominated
convergence. -/

@[expose] public section

open MeasureTheory Filter Topology ProbabilityTheory Function
open scoped NNReal ENNReal

namespace DOZZ.Proofs

/-- Pointwise normalization of a Wick exponential under a centered Gaussian law. -/
theorem wickScalar_integrable_expectation_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : Ω → ℝ)
    (v : ℝ≥0) (hW : HasLaw W (gaussianReal (0 : ℝ) v) P) (γ : ℝ) :
    Integrable (fun ω => Real.exp (γ * W ω - γ ^ 2 / 2 * (v : ℝ))) P ∧
      (∫ ω, Real.exp (γ * W ω - γ ^ 2 / 2 * (v : ℝ)) ∂P) = 1 := by
  have hExpMap : Integrable (fun x : ℝ => Real.exp (γ * x)) (P.map W) := by
    rw [hW.map_eq]
    exact integrable_exp_mul_gaussianReal γ
  have hExp : Integrable (fun ω => Real.exp (γ * W ω)) P := by
    simpa only [Function.comp_def] using
      (integrable_map_measure hExpMap.aestronglyMeasurable hW.aemeasurable).mp hExpMap
  have hWick : Integrable
      (fun ω => Real.exp (γ * W ω - γ ^ 2 / 2 * (v : ℝ))) P := by
    convert hExp.const_mul (Real.exp (-(γ ^ 2 / 2 * (v : ℝ)))) using 1
    ext ω
    rw [show γ * W ω - γ ^ 2 / 2 * (v : ℝ) =
      -(γ ^ 2 / 2 * (v : ℝ)) + γ * W ω by ring, Real.exp_add]
  have hmgf : (∫ ω, Real.exp (γ * W ω) ∂P) =
      Real.exp ((v : ℝ) * γ ^ 2 / 2) :=
    gaussian_exponential_moment_of_hasLaw hW γ
  refine ⟨hWick, ?_⟩
  calc
    (∫ ω, Real.exp (γ * W ω - γ ^ 2 / 2 * (v : ℝ)) ∂P) =
        ∫ ω, Real.exp (-(γ ^ 2 / 2 * (v : ℝ))) * Real.exp (γ * W ω) ∂P := by
          apply integral_congr_ae
          filter_upwards [] with ω
          rw [show γ * W ω - γ ^ 2 / 2 * (v : ℝ) =
            -(γ ^ 2 / 2 * (v : ℝ)) + γ * W ω by ring, ← Real.exp_add]
    _ = Real.exp (-(γ ^ 2 / 2 * (v : ℝ))) *
          (∫ ω, Real.exp (γ * W ω) ∂P) := integral_const_mul _ _
    _ = Real.exp ((v : ℝ) * γ ^ 2 / 2 - γ ^ 2 / 2 * (v : ℝ)) := by
          rw [hmgf, ← Real.exp_add]
          congr 1
          ring
    _ = 1 := by rw [show (v : ℝ) * γ ^ 2 / 2 - γ ^ 2 / 2 * (v : ℝ) = 0 by ring,
      Real.exp_zero]

/-- Scalar spatial weights preserve integrability and multiply the Wick mean by their value. -/
theorem weightedWick_integrable_expectation_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : Ω → ℝ)
    (v : ℝ≥0) (hW : HasLaw W (gaussianReal (0 : ℝ) v) P) (γ w : ℝ) :
    Integrable (fun ω => w * Real.exp (γ * W ω - γ ^ 2 / 2 * (v : ℝ))) P ∧
      (∫ ω, w * Real.exp (γ * W ω - γ ^ 2 / 2 * (v : ℝ)) ∂P) = w := by
  obtain ⟨hInt, hMean⟩ := wickScalar_integrable_expectation_of_hasLaw P W v hW γ
  have hwInt : Integrable
      (fun ω => w * Real.exp (γ * W ω - γ ^ 2 / 2 * (v : ℝ))) P := by
    exact hInt.const_mul w
  refine ⟨hwInt, ?_⟩
  calc
    (∫ ω, w * Real.exp (γ * W ω - γ ^ 2 / 2 * (v : ℝ)) ∂P) =
        ∫ ω, Real.exp (γ * W ω - γ ^ 2 / 2 * (v : ℝ)) * w ∂P := by
          apply integral_congr_ae
          filter_upwards [] with ω
          ring
    _ = (∫ ω, Real.exp (γ * W ω - γ ^ 2 / 2 * (v : ℝ)) ∂P) * w :=
      integral_mul_const _ _
    _ = w := by rw [hMean]; ring

/-- An integrable nonnegative spatial weight times a Wick exponential has integrable spatial
sections almost surely. This is the Tonelli input for sampled-law transfer. -/
theorem ae_integrable_weighted_wick_sections
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (ν : Measure S) [IsProbabilityMeasure ν]
    (W : Ω → S → ℝ) (v : S → ℝ≥0) (w : S → ℝ) (γ : ℝ)
    (hW : Measurable (fun p : Ω × S => W p.1 p.2))
    (hv : Measurable v) (hw : Measurable w)
    (hLaw : ∀ x, HasLaw (fun ω => W ω x) (gaussianReal (0 : ℝ) (v x)) P)
    (hw_nonneg : ∀ x, 0 ≤ w x) (hw_int : Integrable w ν) :
    ∀ᵐ ω ∂P, Integrable (fun x => w x *
      Real.exp (γ * W ω x - γ ^ 2 / 2 * (v x : ℝ))) ν := by
  let g : Ω × S → ℝ := fun p => w p.2 *
    Real.exp (γ * W p.1 p.2 - γ ^ 2 / 2 * (v p.2 : ℝ))
  have hg : Measurable g := by
    dsimp [g]
    fun_prop
  have hpoint (x : S) : Integrable (fun ω => g (ω, x)) P ∧
      (∫ ω, g (ω, x) ∂P) = w x := by
    simpa [g] using
      (weightedWick_integrable_expectation_of_hasLaw P (fun ω => W ω x) (v x)
        (hLaw x) γ (w x))
  have hnorm (x : S) : (∫ ω, ‖g (ω, x)‖ ∂P) = w x := by
    have hnonneg : ∀ ω, 0 ≤ g (ω, x) := by
      intro ω
      dsimp [g]
      exact mul_nonneg (hw_nonneg x) (le_of_lt (Real.exp_pos _))
    calc
      (∫ ω, ‖g (ω, x)‖ ∂P) = ∫ ω, g (ω, x) ∂P := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => by
          simp [Real.norm_eq_abs, abs_of_nonneg (hnonneg ω)]
      _ = w x := (hpoint x).2
  have hprod : Integrable g (P.prod ν) := by
    apply (integrable_prod_iff' hg.aestronglyMeasurable).2
    refine ⟨?_, ?_⟩
    · exact Filter.Eventually.of_forall fun x => (hpoint x).1
    · exact hw_int.congr (Filter.Eventually.of_forall fun x => (hnorm x).symm)
  have hsections := hprod.prod_right_ae
  filter_upwards [hsections] with ω hω
  exact hω.congr (Filter.Eventually.of_forall fun x => rfl)

/-- Equality of the conditional laws at every sample point gives equality of the joint laws after
adjoining an independent sample from a common finite measure. -/
theorem map_prod_eq_of_section_maps
    {Ω Ω' S E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace S] [MeasurableSpace E]
    (P : Measure Ω) (P' : Measure Ω') (ν : Measure S)
    [IsFiniteMeasure P] [IsFiniteMeasure P'] [IsFiniteMeasure ν]
    (F : Ω → S → E) (G : Ω' → S → E)
    (hF : Measurable (fun p : Ω × S => F p.1 p.2))
    (hG : Measurable (fun p : Ω' × S => G p.1 p.2))
    (hsec : ∀ s, Measure.map (F · s) P = Measure.map (G · s) P') :
    Measure.map (fun p : Ω × S => F p.1 p.2) (P.prod ν) =
      Measure.map (fun p : Ω' × S => G p.1 p.2) (P'.prod ν) := by
  apply Measure.ext
  intro t ht
  rw [Measure.map_apply hF ht, Measure.map_apply hG ht,
    Measure.prod_apply_symm (hF ht),
    Measure.prod_apply_symm (hG ht)]
  apply lintegral_congr
  intro s
  have hFs : Measurable (F · s) := hF.comp (measurable_id.prodMk measurable_const)
  have hGs : Measurable (G · s) := hG.comp (measurable_id.prodMk measurable_const)
  change P ((F · s) ⁻¹' t) = P' ((G · s) ⁻¹' t)
  calc
    P ((F · s) ⁻¹' t) = (Measure.map (F · s) P) t :=
      (Measure.map_apply hFs ht).symm
    _ = (Measure.map (G · s) P') t := congrArg (fun μ => μ t) (hsec s)
    _ = P' ((G · s) ⁻¹' t) := Measure.map_apply hGs ht

private theorem ae_empirical_average_tendsto
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (ν : Measure S) [IsProbabilityMeasure ν]
    (f : Ω → S → ℝ)
    (hjoint : Measurable (fun p : Ω × S => f p.1 p.2))
    (hint : ∀ᵐ ω ∂P, Integrable (f ω) ν) :
    ∀ᵐ p ∂P.prod (Measure.infinitePi (fun _ : ℕ => ν)),
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, f p.1 (p.2 i.val))
        atTop (𝓝 (∫ x, f p.1 x ∂ν)) := by
  let Q : Measure (ℕ → S) := Measure.infinitePi (fun _ : ℕ => ν)
  have hQ : IsProbabilityMeasure Q := by infer_instance
  have hEvalIdent (i : ℕ) : IdentDistrib (fun q : ℕ → S => q i) id Q ν := by
    refine ⟨(measurable_pi_apply i).aemeasurable, aemeasurable_id, ?_⟩
    simpa [Q] using (Measure.infinitePi_map_eval (fun _ : ℕ => ν) i)
  have hCoordIdent (i : ℕ) :
      IdentDistrib (fun q : ℕ → S => q i) (fun q => q 0) Q Q := by
    exact (hEvalIdent i).trans (hEvalIdent 0).symm
  have hindepCoord : iIndepFun (fun i (q : ℕ → S) => q i) Q := by
    simpa [Q] using
      (iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ : ℕ => id)
        (by fun_prop))
  have hInner (ω : Ω) (hω : Integrable (f ω) ν) :
      ∀ᵐ q ∂Q,
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, f ω (q i.val))
          atTop (𝓝 (∫ x, f ω x ∂ν)) := by
    have hfmeas : Measurable (f ω) := by
      exact hjoint.comp (by fun_prop : Measurable fun x : S => (ω, x))
    have hindep := hindepCoord.comp (fun _ => f ω) (fun _ => hfmeas)
    have hindep' : Pairwise (fun i j =>
        (fun q => f ω (q i)) ⟂ᵢ[Q] (fun q => f ω (q j))) := by
      intro i j hij
      exact hindep.indepFun hij
    have hident : ∀ i, IdentDistrib (fun q => f ω (q i)) (fun q => f ω (q 0)) Q Q := by
      intro i
      exact (hCoordIdent i).comp hfmeas
    have hsampleIdent : IdentDistrib (fun q => f ω (q 0)) (f ω) Q ν :=
      (hEvalIdent 0).comp hfmeas
    have hsampleInt : Integrable (fun q => f ω (q 0)) Q :=
      hsampleIdent.integrable_iff.mpr hω
    have hmean : (∫ q, f ω (q 0) ∂Q) = ∫ x, f ω x ∂ν :=
      hsampleIdent.integral_eq
    have hlln := ProbabilityTheory.strong_law_ae (μ := Q)
      (fun i (q : ℕ → S) => f ω (q i)) hsampleInt hindep' hident
    filter_upwards [hlln] with q hq
    simpa only [smul_eq_mul, ← Fin.sum_univ_eq_sum_range, hmean] using hq
  have hIter : ∀ᵐ ω ∂P, ∀ᵐ q ∂Q,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, f ω (q i.val))
        atTop (𝓝 (∫ x, f ω x ∂ν)) := by
    filter_upwards [hint] with ω hω
    exact hInner ω hω
  have hsequence : ∀ n : ℕ, Measurable (fun p : Ω × (ℕ → S) =>
      (n : ℝ)⁻¹ * ∑ i : Fin n, f p.1 (p.2 i.val)) := by
    intro n
    fun_prop
  have hlimit : Measurable (fun p : Ω × (ℕ → S) => ∫ x, f p.1 x ∂ν) := by
    exact (hjoint.stronglyMeasurable.integral_prod_right').measurable.comp measurable_fst
  have hset : MeasurableSet {p : Ω × (ℕ → S) |
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        ∑ i : Fin n, f p.1 (p.2 i.val)) atTop
          (𝓝 (∫ x, f p.1 x ∂ν))} :=
    measurableSet_tendsto_fun (l := atTop) hsequence hlimit
  exact Measure.ae_prod_iff_ae_ae hset |>.2 hIter

/-- The vector of empirical weighted Wick sums associated with a finite list of sample points. -/
noncomputable def empiricalWickVector {S : Type*} [MeasurableSpace S] {k m n : ℕ}
    (z : Fin m → S → ℝ → ℝ) (u : ℕ → S)
    (w : (Fin k → ℝ) × (Fin n → ℝ)) :
    (Fin k → ℝ) × (Fin m → ℝ) :=
  (w.1, fun j => (n : ℝ)⁻¹ * ∑ i : Fin n, z j (u i.val) (w.2 i))

private theorem measurable_empiricalWickVector {S : Type*} [MeasurableSpace S]
    {k m n : ℕ} (z : Fin m → S → ℝ → ℝ) (u : ℕ → S)
    (hz : ∀ j, Measurable (fun p : S × ℝ => z j p.1 p.2)) :
    Measurable (empiricalWickVector z u :
      ((Fin k → ℝ) × (Fin n → ℝ)) → (Fin k → ℝ) × (Fin m → ℝ)) := by
  apply Measurable.prodMk measurable_fst
  apply measurable_pi_iff.2
  intro j
  apply Measurable.mul measurable_const
  apply Finset.measurable_sum
  intro i hi
  exact (hz j).comp (measurable_const.prodMk
    ((measurable_pi_apply i).comp measurable_snd))

/-- Finite dimensional laws determine the joint laws of the field coordinates and any finite
empirical vector of measurable weighted transforms. -/
theorem empiricalWick_map_eq_of_fdd
    {Ω Ω' S : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace S]
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (ν : Measure S) [IsProbabilityMeasure ν] {k m n : ℕ}
    (X : Ω → S → ℝ) (Y : Ω' → S → ℝ)
    (V : Ω → Fin k → ℝ) (V' : Ω' → Fin k → ℝ)
    (z : Fin m → S → ℝ → ℝ)
    (hV : Measurable V) (hV' : Measurable V')
    (hX : Measurable (fun p : Ω × S => X p.1 p.2))
    (hY : Measurable (fun p : Ω' × S => Y p.1 p.2))
    (hz : ∀ j, Measurable (fun p : S × ℝ => z j p.1 p.2))
    (hFDD : ∀ (r : ℕ) (xs : Fin r → S),
      Measure.map (fun ω => (V ω, fun i => X ω (xs i))) P =
        Measure.map (fun ω => (V' ω, fun i => Y ω (xs i))) P') :
    Measure.map (fun p : Ω × (ℕ → S) =>
      empiricalWickVector z p.2
          (V p.1, fun i : Fin n => X p.1 (p.2 i.val)))
        (P.prod (Measure.infinitePi (fun _ : ℕ => ν))) =
      Measure.map (fun p : Ω' × (ℕ → S) =>
      empiricalWickVector z p.2
          (V' p.1, fun i : Fin n => Y p.1 (p.2 i.val)))
        (P'.prod (Measure.infinitePi (fun _ : ℕ => ν))) := by
  let F : Ω → (ℕ → S) → (Fin k → ℝ) × (Fin m → ℝ) := fun ω u =>
    empiricalWickVector z u (V ω, fun i : Fin n => X ω (u i.val))
  let G : Ω' → (ℕ → S) → (Fin k → ℝ) × (Fin m → ℝ) := fun ω u =>
    empiricalWickVector z u (V' ω, fun i : Fin n => Y ω (u i.val))
  have hFjoint : Measurable (fun p : Ω × (ℕ → S) => F p.1 p.2) := by
    apply Measurable.prodMk (hV.comp measurable_fst)
    apply measurable_pi_iff.2
    intro j
    apply Measurable.mul measurable_const
    apply Finset.measurable_sum
    intro i hi
    have harg : Measurable (fun p : Ω × (ℕ → S) =>
        (p.2 i.val, X p.1 (p.2 i.val))) := by
      apply Measurable.prodMk
      · exact (measurable_pi_apply i.val).comp measurable_snd
      · exact hX.comp
          (measurable_fst.prodMk ((measurable_pi_apply i.val).comp measurable_snd))
    exact (hz j).comp harg
  have hGjoint : Measurable (fun p : Ω' × (ℕ → S) => G p.1 p.2) := by
    apply Measurable.prodMk (hV'.comp measurable_fst)
    apply measurable_pi_iff.2
    intro j
    apply Measurable.mul measurable_const
    apply Finset.measurable_sum
    intro i hi
    have harg : Measurable (fun p : Ω' × (ℕ → S) =>
        (p.2 i.val, Y p.1 (p.2 i.val))) := by
      apply Measurable.prodMk
      · exact (measurable_pi_apply i.val).comp measurable_snd
      · exact hY.comp
          (measurable_fst.prodMk ((measurable_pi_apply i.val).comp measurable_snd))
    exact (hz j).comp harg
  have hsection (u : ℕ → S) : Measure.map (F · u) P = Measure.map (G · u) P' := by
    have hbase : Measurable (fun ω : Ω =>
        (V ω, fun i : Fin n => X ω (u i.val))) := by
      apply Measurable.prodMk hV
      apply measurable_pi_iff.2
      intro i
      exact hX.comp (measurable_id.prodMk measurable_const)
    have hbase' : Measurable (fun ω : Ω' =>
        (V' ω, fun i : Fin n => Y ω (u i.val))) := by
      apply Measurable.prodMk hV'
      apply measurable_pi_iff.2
      intro i
      exact hY.comp (measurable_id.prodMk measurable_const)
    have htransform := measurable_empiricalWickVector (k := k) (m := m) (n := n) z u hz
    have hfd := hFDD n (fun i => u i.val)
    calc
      Measure.map (F · u) P =
          (Measure.map (fun ω : Ω => (V ω, fun i : Fin n => X ω (u i.val))) P).map
            (empiricalWickVector z u) := by
          change Measure.map
            (empiricalWickVector z u ∘ fun ω : Ω => (V ω, fun i : Fin n => X ω (u i.val))) P = _
          rw [Measure.map_map htransform hbase]
      _ = (Measure.map (fun ω : Ω' => (V' ω, fun i : Fin n => Y ω (u i.val))) P').map
            (empiricalWickVector z u) := by rw [hfd]
      _ = Measure.map (G · u) P' := by
          change _ = Measure.map
            (empiricalWickVector z u ∘ fun ω : Ω' => (V' ω, fun i : Fin n => Y ω (u i.val))) P'
          rw [Measure.map_map htransform hbase']
  exact map_prod_eq_of_section_maps P P' _ F G hFjoint hGjoint hsection

/-- If two sequences of random vectors have the same law at every index and converge almost
everywhere on their respective finite measure spaces, then their limits agree in law as tested
by every bounded continuous real function. -/
theorem integral_bcf_eq_of_map_eq_of_ae_tendsto
    {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace E] [PseudoEMetricSpace E] [BorelSpace E]
    {P : Measure Ω} {P' : Measure Ω'} [IsFiniteMeasure P] [IsFiniteMeasure P']
    (f : ℕ → Ω → E) (g : ℕ → Ω' → E) (fLimit : Ω → E) (gLimit : Ω' → E)
    (hf : ∀ n, AEMeasurable (f n) P) (hg : ∀ n, AEMeasurable (g n) P')
    (hmap : ∀ n, Measure.map (f n) P = Measure.map (g n) P')
    (hf_tendsto : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (fLimit ω)))
    (hg_tendsto : ∀ᵐ ω ∂P', Tendsto (fun n => g n ω) atTop (𝓝 (gLimit ω)))
    (φ : BoundedContinuousFunction E ℝ) :
    (∫ ω, φ (fLimit ω) ∂P) = ∫ ω, φ (gLimit ω) ∂P' := by
  have hboundP : Integrable (fun _ : Ω => (‖φ‖ : ℝ)) P := integrable_const _
  have hboundP' : Integrable (fun _ : Ω' => (‖φ‖ : ℝ)) P' := integrable_const _
  have hf_meas : ∀ n, AEStronglyMeasurable (fun ω => φ (f n ω)) P := by
    intro n
    exact φ.continuous.aestronglyMeasurable.comp_aemeasurable (hf n)
  have hg_meas : ∀ n, AEStronglyMeasurable (fun ω => φ (g n ω)) P' := by
    intro n
    exact φ.continuous.aestronglyMeasurable.comp_aemeasurable (hg n)
  have hf_bound : ∀ n, ∀ᵐ ω ∂P, ‖φ (f n ω)‖ ≤ ‖φ‖ := by
    intro n
    exact Filter.Eventually.of_forall fun ω => φ.norm_coe_le_norm (f n ω)
  have hg_bound : ∀ n, ∀ᵐ ω ∂P', ‖φ (g n ω)‖ ≤ ‖φ‖ := by
    intro n
    exact Filter.Eventually.of_forall fun ω => φ.norm_coe_le_norm (g n ω)
  have hf_limit : ∀ᵐ ω ∂P,
      Tendsto (fun n => φ (f n ω)) atTop (𝓝 (φ (fLimit ω))) := by
    filter_upwards [hf_tendsto] with ω hω
    exact φ.continuous.continuousAt.tendsto.comp hω
  have hg_limit : ∀ᵐ ω ∂P',
      Tendsto (fun n => φ (g n ω)) atTop (𝓝 (φ (gLimit ω))) := by
    filter_upwards [hg_tendsto] with ω hω
    exact φ.continuous.continuousAt.tendsto.comp hω
  have hP : Tendsto (fun n => ∫ ω, φ (f n ω) ∂P) atTop
      (𝓝 (∫ ω, φ (fLimit ω) ∂P)) :=
    tendsto_integral_of_dominated_convergence (fun _ => ‖φ‖)
      hf_meas hboundP hf_bound hf_limit
  have hP' : Tendsto (fun n => ∫ ω, φ (g n ω) ∂P') atTop
      (𝓝 (∫ ω, φ (gLimit ω) ∂P')) :=
    tendsto_integral_of_dominated_convergence (fun _ => ‖φ‖)
      hg_meas hboundP' hg_bound hg_limit
  have hterms : ∀ n, (∫ ω, φ (f n ω) ∂P) = ∫ ω, φ (g n ω) ∂P' := by
    intro n
    have hφP : AEStronglyMeasurable (fun x : E => φ x) (Measure.map (f n) P) :=
      φ.continuous.measurable.aestronglyMeasurable
    have hφP' : AEStronglyMeasurable (fun x : E => φ x) (Measure.map (g n) P') :=
      φ.continuous.measurable.aestronglyMeasurable
    calc
      (∫ ω, φ (f n ω) ∂P) = ∫ x, φ x ∂Measure.map (f n) P :=
        (integral_map (hf n) hφP).symm
      _ = ∫ x, φ x ∂Measure.map (g n) P' := by rw [hmap n]
      _ = ∫ ω, φ (g n ω) ∂P' := integral_map (hg n) hφP'
  apply tendsto_nhds_unique hP
  exact hP'.congr' (Filter.Eventually.of_forall fun n => (hterms n).symm)

/-- The law of finitely many Wick integrals, jointly with finitely many field coordinates, is
determined by the finite dimensional laws of a jointly measurable field. The weights and Wick
normalizations are encoded by the common measurable transforms `z`; the only analytic input is
almost-sure integrability of each transformed section. -/
theorem chaosLawFDD_of_integrable
    {Ω Ω' S : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace S]
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (ν : Measure S) [IsProbabilityMeasure ν] {k m : ℕ}
    (X : Ω → S → ℝ) (Y : Ω' → S → ℝ)
    (V : Ω → Fin k → ℝ) (V' : Ω' → Fin k → ℝ)
    (z : Fin m → S → ℝ → ℝ)
    (hV : Measurable V) (hV' : Measurable V')
    (hX : Measurable (fun p : Ω × S => X p.1 p.2))
    (hY : Measurable (fun p : Ω' × S => Y p.1 p.2))
    (hz : ∀ j, Measurable (fun p : S × ℝ => z j p.1 p.2))
    (hintX : ∀ j, ∀ᵐ ω ∂P, Integrable (fun x => z j x (X ω x)) ν)
    (hintY : ∀ j, ∀ᵐ ω ∂P', Integrable (fun x => z j x (Y ω x)) ν)
    (hFDD : ∀ (r : ℕ) (xs : Fin r → S),
      Measure.map (fun ω => (V ω, fun i => X ω (xs i))) P =
        Measure.map (fun ω => (V' ω, fun i => Y ω (xs i))) P')
    (φ : BoundedContinuousFunction ((Fin k → ℝ) × (Fin m → ℝ)) ℝ) :
    Measure.map (fun ω => (V ω, fun j => ∫ x, z j x (X ω x) ∂ν)) P =
      Measure.map (fun ω => (V' ω, fun j => ∫ x, z j x (Y ω x) ∂ν)) P' ∧
    (∫ ω, φ (V ω, fun j => ∫ x, z j x (X ω x) ∂ν) ∂P) =
      ∫ ω, φ (V' ω, fun j => ∫ x, z j x (Y ω x) ∂ν) ∂P' := by
  let Q : Measure (ℕ → S) := Measure.infinitePi (fun _ : ℕ => ν)
  let EX : ℕ → Ω × (ℕ → S) → (Fin k → ℝ) × (Fin m → ℝ) := fun r p =>
    empiricalWickVector z p.2
      (V p.1, fun i : Fin r => X p.1 (p.2 i.val))
  let EY : ℕ → Ω' × (ℕ → S) → (Fin k → ℝ) × (Fin m → ℝ) := fun r p =>
    empiricalWickVector z p.2
      (V' p.1, fun i : Fin r => Y p.1 (p.2 i.val))
  let LX : Ω → (Fin k → ℝ) × (Fin m → ℝ) := fun ω =>
    (V ω, fun j => ∫ x, z j x (X ω x) ∂ν)
  let LY : Ω' → (Fin k → ℝ) × (Fin m → ℝ) := fun ω =>
    (V' ω, fun j => ∫ x, z j x (Y ω x) ∂ν)
  have hXtransform : ∀ j, Measurable (fun p : Ω × S => z j p.2 (X p.1 p.2)) := by
    intro j
    exact (hz j).comp (measurable_snd.prodMk hX)
  have hYtransform : ∀ j, Measurable (fun p : Ω' × S => z j p.2 (Y p.1 p.2)) := by
    intro j
    exact (hz j).comp (measurable_snd.prodMk hY)
  have hEXmeas : ∀ r, Measurable (EX r) := by
    intro r
    change Measurable (fun p : Ω × (ℕ → S) =>
      empiricalWickVector z p.2
        (V p.1, fun i : Fin r => X p.1 (p.2 i.val)))
    apply Measurable.prodMk (hV.comp measurable_fst)
    apply measurable_pi_iff.2
    intro j
    apply Measurable.mul measurable_const
    apply Finset.measurable_sum
    intro i hi
    have harg : Measurable (fun p : Ω × (ℕ → S) =>
        (p.2 i.val, X p.1 (p.2 i.val))) := by
      apply Measurable.prodMk
      · exact (measurable_pi_apply i.val).comp measurable_snd
      · exact hX.comp
          (measurable_fst.prodMk ((measurable_pi_apply i.val).comp measurable_snd))
    exact (hz j).comp harg
  have hEYmeas : ∀ r, Measurable (EY r) := by
    intro r
    change Measurable (fun p : Ω' × (ℕ → S) =>
      empiricalWickVector z p.2
        (V' p.1, fun i : Fin r => Y p.1 (p.2 i.val)))
    apply Measurable.prodMk (hV'.comp measurable_fst)
    apply measurable_pi_iff.2
    intro j
    apply Measurable.mul measurable_const
    apply Finset.measurable_sum
    intro i hi
    have harg : Measurable (fun p : Ω' × (ℕ → S) =>
        (p.2 i.val, Y p.1 (p.2 i.val))) := by
      apply Measurable.prodMk
      · exact (measurable_pi_apply i.val).comp measurable_snd
      · exact hY.comp
          (measurable_fst.prodMk ((measurable_pi_apply i.val).comp measurable_snd))
    exact (hz j).comp harg
  have hmap : ∀ r,
      Measure.map (EX r) (P.prod Q) = Measure.map (EY r) (P'.prod Q) := by
    intro r
    exact empiricalWick_map_eq_of_fdd ν X Y V V' z hV hV' hX hY hz hFDD
  have hXscalar : ∀ j, ∀ᵐ p ∂P.prod Q,
      Tendsto (fun r : ℕ => (r : ℝ)⁻¹ *
        ∑ i : Fin r, z j (p.2 i.val) (X p.1 (p.2 i.val))) atTop
          (𝓝 (∫ x, z j x (X p.1 x) ∂ν)) := by
    intro j
    have hconv := ae_empirical_average_tendsto P ν
      (fun ω x => z j x (X ω x)) (hXtransform j) (hintX j)
    simpa [Q] using hconv
  have hYscalar : ∀ j, ∀ᵐ p ∂P'.prod Q,
      Tendsto (fun r : ℕ => (r : ℝ)⁻¹ *
        ∑ i : Fin r, z j (p.2 i.val) (Y p.1 (p.2 i.val))) atTop
          (𝓝 (∫ x, z j x (Y p.1 x) ∂ν)) := by
    intro j
    have hconv := ae_empirical_average_tendsto P' ν
      (fun ω x => z j x (Y ω x)) (hYtransform j) (hintY j)
    simpa [Q] using hconv
  have hXlim : ∀ᵐ p ∂P.prod Q, Tendsto (fun r => EX r p) atTop (𝓝 (LX p.1)) := by
    have hcoords : ∀ j, ∀ᵐ p ∂P.prod Q,
        Tendsto (fun r : ℕ => (r : ℝ)⁻¹ *
          ∑ i : Fin r, z j (p.2 i.val) (X p.1 (p.2 i.val))) atTop
            (𝓝 (∫ x, z j x (X p.1 x) ∂ν)) := hXscalar
    filter_upwards [ae_all_iff.2 hcoords] with p hp
    have hfirst : Tendsto (fun _ : ℕ => V p.1) atTop (𝓝 (V p.1)) := tendsto_const_nhds
    have hsecond : Tendsto
        (fun r : ℕ => fun j => (r : ℝ)⁻¹ *
          ∑ i : Fin r, z j (p.2 i.val) (X p.1 (p.2 i.val))) atTop
        (𝓝 (fun j => ∫ x, z j x (X p.1 x) ∂ν)) :=
      tendsto_pi_nhds.2 fun j => hp j
    have hpair : Tendsto (fun r : ℕ =>
        (V p.1, fun j => (r : ℝ)⁻¹ *
          ∑ i : Fin r, z j (p.2 i.val) (X p.1 (p.2 i.val)))) atTop
        (𝓝 (V p.1, fun j => ∫ x, z j x (X p.1 x) ∂ν)) :=
      (Prod.tendsto_iff (fun r : ℕ => (V p.1, fun j => (r : ℝ)⁻¹ *
          ∑ i : Fin r, z j (p.2 i.val) (X p.1 (p.2 i.val))))
        (V p.1, fun j => ∫ x, z j x (X p.1 x) ∂ν)).2 ⟨hfirst, hsecond⟩
    simpa [EX, LX, empiricalWickVector] using hpair
  have hYlim : ∀ᵐ p ∂P'.prod Q, Tendsto (fun r => EY r p) atTop (𝓝 (LY p.1)) := by
    have hcoords : ∀ j, ∀ᵐ p ∂P'.prod Q,
        Tendsto (fun r : ℕ => (r : ℝ)⁻¹ *
          ∑ i : Fin r, z j (p.2 i.val) (Y p.1 (p.2 i.val))) atTop
            (𝓝 (∫ x, z j x (Y p.1 x) ∂ν)) := hYscalar
    filter_upwards [ae_all_iff.2 hcoords] with p hp
    have hfirst : Tendsto (fun _ : ℕ => V' p.1) atTop (𝓝 (V' p.1)) := tendsto_const_nhds
    have hsecond : Tendsto
        (fun r : ℕ => fun j => (r : ℝ)⁻¹ *
          ∑ i : Fin r, z j (p.2 i.val) (Y p.1 (p.2 i.val))) atTop
        (𝓝 (fun j => ∫ x, z j x (Y p.1 x) ∂ν)) :=
      tendsto_pi_nhds.2 fun j => hp j
    have hpair : Tendsto (fun r : ℕ =>
        (V' p.1, fun j => (r : ℝ)⁻¹ *
          ∑ i : Fin r, z j (p.2 i.val) (Y p.1 (p.2 i.val)))) atTop
        (𝓝 (V' p.1, fun j => ∫ x, z j x (Y p.1 x) ∂ν)) :=
      (Prod.tendsto_iff (fun r : ℕ => (V' p.1, fun j => (r : ℝ)⁻¹ *
          ∑ i : Fin r, z j (p.2 i.val) (Y p.1 (p.2 i.val))))
        (V' p.1, fun j => ∫ x, z j x (Y p.1 x) ∂ν)).2 ⟨hfirst, hsecond⟩
    simpa [EY, LY, empiricalWickVector] using hpair
  have hLXmeas : Measurable LX := by
    apply Measurable.prodMk hV
    apply measurable_pi_iff.2
    intro j
    exact (hXtransform j).stronglyMeasurable.integral_prod_right'.measurable
  have hLYmeas : Measurable LY := by
    apply Measurable.prodMk hV'
    apply measurable_pi_iff.2
    intro j
    exact (hYtransform j).stronglyMeasurable.integral_prod_right'.measurable
  have htestAll : ∀ ψ : BoundedContinuousFunction
      ((Fin k → ℝ) × (Fin m → ℝ)) ℝ,
      (∫ ω, ψ (LX ω) ∂P) = ∫ ω, ψ (LY ω) ∂P' := by
    intro ψ
    have htest := integral_bcf_eq_of_map_eq_of_ae_tendsto EX EY
      (fun p => LX p.1) (fun p => LY p.1)
      (fun r => (hEXmeas r).aemeasurable) (fun r => (hEYmeas r).aemeasurable)
      hmap hXlim hYlim ψ
    have htestX : (∫ p, ψ (LX p.1) ∂P.prod Q) = ∫ ω, ψ (LX ω) ∂P := by
      have hφP : AEStronglyMeasurable (fun ω => ψ (LX ω)) P :=
        (ψ.continuous.measurable.comp hLXmeas).aestronglyMeasurable
      have hφ : AEStronglyMeasurable (fun ω => ψ (LX ω))
          (Measure.map Prod.fst (P.prod Q)) := by
        rw [Measure.map_fst_prod, measure_univ, one_smul]
        exact hφP
      have h := integral_map measurable_fst.aemeasurable hφ
      rw [Measure.map_fst_prod, measure_univ, one_smul] at h
      exact h.symm
    have htestY : (∫ p, ψ (LY p.1) ∂P'.prod Q) = ∫ ω, ψ (LY ω) ∂P' := by
      have hφP : AEStronglyMeasurable (fun ω => ψ (LY ω)) P' :=
        (ψ.continuous.measurable.comp hLYmeas).aestronglyMeasurable
      have hφ : AEStronglyMeasurable (fun ω => ψ (LY ω))
          (Measure.map Prod.fst (P'.prod Q)) := by
        rw [Measure.map_fst_prod, measure_univ, one_smul]
        exact hφP
      have h := integral_map measurable_fst.aemeasurable hφ
      rw [Measure.map_fst_prod, measure_univ, one_smul] at h
      exact h.symm
    calc
      (∫ ω, ψ (LX ω) ∂P) = ∫ p, ψ (LX p.1) ∂P.prod Q := htestX.symm
      _ = ∫ p, ψ (LY p.1) ∂P'.prod Q := htest
      _ = ∫ ω, ψ (LY ω) ∂P' := htestY
  have hmapLaw : Measure.map LX P = Measure.map LY P' := by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro ψ
    calc
      (∫ y, ψ y ∂Measure.map LX P) = ∫ ω, ψ (LX ω) ∂P :=
        integral_map hLXmeas.aemeasurable ψ.continuous.measurable.aestronglyMeasurable
      _ = ∫ ω, ψ (LY ω) ∂P' := htestAll ψ
      _ = ∫ y, ψ y ∂Measure.map LY P' :=
        (integral_map hLYmeas.aemeasurable
          ψ.continuous.measurable.aestronglyMeasurable).symm
  exact ⟨by simpa [LX, LY] using hmapLaw, htestAll φ⟩


/-- Finite dimensional field laws determine jointly the law of any finite list of Wick
integrals, including an auxiliary finite vector. The weights may be unbounded provided the
resulting spatial integrals are almost surely integrable. -/
theorem chaosLawFDD_weightedWick
    {Ω Ω' S : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace S]
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (ν : Measure S) [IsProbabilityMeasure ν] {k m : ℕ}
    (X : Ω → S → ℝ) (Y : Ω' → S → ℝ)
    (V : Ω → Fin k → ℝ) (V' : Ω' → Fin k → ℝ)
    (variance : S → ℝ≥0) (weight : Fin m → S → ℝ) (γ : ℝ)
    (hV : Measurable V) (hV' : Measurable V')
    (hX : Measurable (fun p : Ω × S => X p.1 p.2))
    (hY : Measurable (fun p : Ω' × S => Y p.1 p.2))
    (hvariance : Measurable variance)
    (hweight : ∀ j, Measurable (weight j))
    (hweight_nonneg : ∀ j x, 0 ≤ weight j x)
    (hXlaw : ∀ x, HasLaw (fun ω => X ω x)
      (gaussianReal 0 (variance x)) P)
    (hYlaw : ∀ x, HasLaw (fun ω => Y ω x)
      (gaussianReal 0 (variance x)) P')
    (hintX : ∀ j, Integrable (weight j) ν)
    (hintY : ∀ j, Integrable (weight j) ν)
    (hFDD : ∀ (r : ℕ) (xs : Fin r → S),
      Measure.map (fun ω => (V ω, fun i => X ω (xs i))) P =
        Measure.map (fun ω => (V' ω, fun i => Y ω (xs i))) P')
    (φ : BoundedContinuousFunction ((Fin k → ℝ) × (Fin m → ℝ)) ℝ) :
    (∫ ω, φ (V ω, fun j => ∫ x, weight j x *
      Real.exp (γ * X ω x - γ ^ 2 / 2 * (variance x : ℝ)) ∂ν) ∂P) =
      ∫ ω, φ (V' ω, fun j => ∫ x, weight j x *
      Real.exp (γ * Y ω x - γ ^ 2 / 2 * (variance x : ℝ)) ∂ν) ∂P' := by
  let z : Fin m → S → ℝ → ℝ := fun j x t =>
    weight j x * Real.exp (γ * t - γ ^ 2 / 2 * (variance x : ℝ))
  have hz : ∀ j, Measurable (fun p : S × ℝ => z j p.1 p.2) := by
    intro j
    dsimp [z]
    fun_prop
  have hIntX : ∀ j, ∀ᵐ ω ∂P, Integrable (fun x =>
      weight j x * Real.exp (γ * X ω x - γ ^ 2 / 2 * (variance x : ℝ))) ν := by
    intro j
    exact ae_integrable_weighted_wick_sections ν (W := X) variance (weight j) γ hX
      hvariance (hweight j) hXlaw (hweight_nonneg j) (hintX j)
  have hIntY : ∀ j, ∀ᵐ ω ∂P', Integrable (fun x =>
      weight j x * Real.exp (γ * Y ω x - γ ^ 2 / 2 * (variance x : ℝ))) ν := by
    intro j
    exact ae_integrable_weighted_wick_sections ν (W := Y) variance (weight j) γ hY
      hvariance (hweight j) hYlaw (hweight_nonneg j) (hintY j)
  have hLaw := chaosLawFDD_of_integrable ν X Y V V' z hV hV' hX hY hz
    (by simpa [z] using hIntX) (by simpa [z] using hIntY) hFDD φ
  exact hLaw.2


/-- Finite reference measure version of `chaosLawFDD_weightedWick`. Sampling uses the normalized
probability measure; multiplying each weight by the total mass recovers the original integral. This
permits finite, non-probability reference spaces. -/
theorem chaosLawFDD_finiteReference
    {Ω Ω' S : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace S]
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (ν : FiniteMeasure S) [Nonempty S] {k m : ℕ}
    (X : Ω → S → ℝ) (Y : Ω' → S → ℝ)
    (V : Ω → Fin k → ℝ) (V' : Ω' → Fin k → ℝ)
    (variance : S → ℝ≥0) (weight : Fin m → S → ℝ) (γ : ℝ)
    (hV : Measurable V) (hV' : Measurable V')
    (hX : Measurable (fun p : Ω × S => X p.1 p.2))
    (hY : Measurable (fun p : Ω' × S => Y p.1 p.2))
    (hvariance : Measurable variance)
    (hweight : ∀ j, Measurable (weight j))
    (hweight_nonneg : ∀ j x, 0 ≤ weight j x)
    (hXlaw : ∀ x, HasLaw (fun ω => X ω x)
      (gaussianReal 0 (variance x)) P)
    (hYlaw : ∀ x, HasLaw (fun ω => Y ω x)
      (gaussianReal 0 (variance x)) P')
    (hintX : ∀ j, Integrable (weight j) (ν.normalize : Measure S))
    (hintY : ∀ j, Integrable (weight j) (ν.normalize : Measure S))
    (hFDD : ∀ (r : ℕ) (xs : Fin r → S),
      Measure.map (fun ω => (V ω, fun i => X ω (xs i))) P =
        Measure.map (fun ω => (V' ω, fun i => Y ω (xs i))) P')
    (φ : BoundedContinuousFunction ((Fin k → ℝ) × (Fin m → ℝ)) ℝ) :
    (∫ ω, φ (V ω, fun j => ∫ x, weight j x *
      Real.exp (γ * X ω x - γ ^ 2 / 2 * (variance x : ℝ)) ∂(ν : Measure S)) ∂P) =
      ∫ ω, φ (V' ω, fun j => ∫ x, weight j x *
      Real.exp (γ * Y ω x - γ ^ 2 / 2 * (variance x : ℝ)) ∂(ν : Measure S)) ∂P' := by
  let weight' : Fin m → S → ℝ := fun j x => (ν.mass : ℝ) * weight j x
  have hweight' : ∀ j, Measurable (weight' j) := by
    intro j
    exact measurable_const.mul (hweight j)
  have hweight'_nonneg : ∀ j x, 0 ≤ weight' j x := by
    intro j x
    exact mul_nonneg (by positivity) (hweight_nonneg j x)
  have hintX' : ∀ j, Integrable (weight' j) (ν.normalize : Measure S) := by
    intro j
    simpa [weight'] using (hintX j).const_mul (ν.mass : ℝ)
  have hintY' : ∀ j, Integrable (weight' j) (ν.normalize : Measure S) := by
    intro j
    simpa [weight'] using (hintY j).const_mul (ν.mass : ℝ)
  have hnormalized := chaosLawFDD_weightedWick (ν.normalize : Measure S) X Y V V'
    variance weight' γ hV hV' hX hY hvariance hweight' hweight'_nonneg
    hXlaw hYlaw hintX' hintY' hFDD φ
  have hmassIntegralX (ω : Ω) (j : Fin m) :
      (∫ x, weight j x * Real.exp
        (γ * X ω x - γ ^ 2 / 2 * (variance x : ℝ)) ∂(ν : Measure S)) =
      ∫ x, weight' j x * Real.exp
        (γ * X ω x - γ ^ 2 / 2 * (variance x : ℝ)) ∂(ν.normalize : Measure S) := by
    let f : S → ℝ := fun x => weight j x * Real.exp
      (γ * X ω x - γ ^ 2 / 2 * (variance x : ℝ))
    have hmeasure : (ν : Measure S) =
        (ν.mass : ℝ≥0) • (ν.normalize : Measure S) := by
      exact congrArg (fun μ : FiniteMeasure S => (μ : Measure S))
        ν.self_eq_mass_smul_normalize
    calc
      (∫ x, f x ∂(ν : Measure S)) =
          ∫ x, f x ∂((ν.mass : ℝ≥0) • (ν.normalize : Measure S)) := by
            rw [hmeasure]
      _ = (ν.mass : ℝ) * ∫ x, f x ∂(ν.normalize : Measure S) := by
            rw [integral_smul_nnreal_measure]
            rfl
      _ = ∫ x, (ν.mass : ℝ) * f x ∂(ν.normalize : Measure S) := by
            rw [integral_const_mul]
      _ = ∫ x, weight' j x * Real.exp
          (γ * X ω x - γ ^ 2 / 2 * (variance x : ℝ)) ∂(ν.normalize : Measure S) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x => by
              dsimp [f, weight']
              ring
  have hmassIntegralY (ω : Ω') (j : Fin m) :
      (∫ x, weight j x * Real.exp
        (γ * Y ω x - γ ^ 2 / 2 * (variance x : ℝ)) ∂(ν : Measure S)) =
      ∫ x, weight' j x * Real.exp
        (γ * Y ω x - γ ^ 2 / 2 * (variance x : ℝ)) ∂(ν.normalize : Measure S) := by
    let f : S → ℝ := fun x => weight j x * Real.exp
      (γ * Y ω x - γ ^ 2 / 2 * (variance x : ℝ))
    have hmeasure : (ν : Measure S) =
        (ν.mass : ℝ≥0) • (ν.normalize : Measure S) := by
      exact congrArg (fun μ : FiniteMeasure S => (μ : Measure S))
        ν.self_eq_mass_smul_normalize
    calc
      (∫ x, f x ∂(ν : Measure S)) =
          ∫ x, f x ∂((ν.mass : ℝ≥0) • (ν.normalize : Measure S)) := by
            rw [hmeasure]
      _ = (ν.mass : ℝ) * ∫ x, f x ∂(ν.normalize : Measure S) := by
            rw [integral_smul_nnreal_measure]
            rfl
      _ = ∫ x, (ν.mass : ℝ) * f x ∂(ν.normalize : Measure S) := by
            rw [integral_const_mul]
      _ = ∫ x, weight' j x * Real.exp
          (γ * Y ω x - γ ^ 2 / 2 * (variance x : ℝ)) ∂(ν.normalize : Measure S) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x => by
              dsimp [f, weight']
              ring
  calc
    (∫ ω, φ (V ω, fun j => ∫ x, weight j x * Real.exp
        (γ * X ω x - γ ^ 2 / 2 * (variance x : ℝ)) ∂(ν : Measure S)) ∂P) =
        ∫ ω, φ (V ω, fun j => ∫ x, weight' j x * Real.exp
        (γ * X ω x - γ ^ 2 / 2 * (variance x : ℝ)) ∂(ν.normalize : Measure S)) ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      apply congrArg φ
      exact Prod.ext rfl (funext (hmassIntegralX ω))
    _ = ∫ ω', φ (V' ω', fun j => ∫ x, weight' j x * Real.exp
        (γ * Y ω' x - γ ^ 2 / 2 * (variance x : ℝ)) ∂(ν.normalize : Measure S)) ∂P' :=
      hnormalized
    _ = ∫ ω', φ (V' ω', fun j => ∫ x, weight j x * Real.exp
        (γ * Y ω' x - γ ^ 2 / 2 * (variance x : ℝ)) ∂(ν : Measure S)) ∂P' := by
      apply integral_congr_ae
      filter_upwards [] with ω'
      apply congrArg φ
      exact Prod.ext rfl (funext fun j => (hmassIntegralY ω' j).symm)

/-- Bounded nonnegative weights on a finite reference space satisfy the integrability hypotheses
of `chaosLawFDD_finiteReference` automatically. -/
theorem chaosLawFDD_boundedWeights
    {Ω Ω' S : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace S]
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (ν : FiniteMeasure S) [Nonempty S] {k m : ℕ}
    (X : Ω → S → ℝ) (Y : Ω' → S → ℝ)
    (V : Ω → Fin k → ℝ) (V' : Ω' → Fin k → ℝ)
    (variance : S → ℝ≥0) (weight : Fin m → S → ℝ) (γ : ℝ)
    (hV : Measurable V) (hV' : Measurable V')
    (hX : Measurable (fun p : Ω × S => X p.1 p.2))
    (hY : Measurable (fun p : Ω' × S => Y p.1 p.2))
    (hvariance : Measurable variance)
    (hweight : ∀ j, Measurable (weight j))
    (hweight_nonneg : ∀ j x, 0 ≤ weight j x)
    (hweight_bdd : ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, weight j x ≤ C)
    (hXlaw : ∀ x, HasLaw (fun ω => X ω x)
      (gaussianReal 0 (variance x)) P)
    (hYlaw : ∀ x, HasLaw (fun ω => Y ω x)
      (gaussianReal 0 (variance x)) P')
    (hFDD : ∀ (r : ℕ) (xs : Fin r → S),
      Measure.map (fun ω => (V ω, fun i => X ω (xs i))) P =
        Measure.map (fun ω => (V' ω, fun i => Y ω (xs i))) P')
    (φ : BoundedContinuousFunction ((Fin k → ℝ) × (Fin m → ℝ)) ℝ) :
    (∫ ω, φ (V ω, fun j => ∫ x, weight j x *
      Real.exp (γ * X ω x - γ ^ 2 / 2 * (variance x : ℝ)) ∂(ν : Measure S)) ∂P) =
      ∫ ω, φ (V' ω, fun j => ∫ x, weight j x *
      Real.exp (γ * Y ω x - γ ^ 2 / 2 * (variance x : ℝ)) ∂(ν : Measure S)) ∂P' := by
  have hweight_int : ∀ j, Integrable (weight j) (ν.normalize : Measure S) := by
    intro j
    obtain ⟨C, hC0, hC⟩ := hweight_bdd j
    refine (integrable_const C).mono' (hweight j).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (hweight_nonneg j x)] using hC x
  exact chaosLawFDD_finiteReference ν X Y V V' variance weight γ hV hV' hX hY
    hvariance hweight hweight_nonneg hXlaw hYlaw hweight_int hweight_int hFDD φ

end DOZZ.Proofs
