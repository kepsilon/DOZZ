/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.LateralUnitBlockMass
public import DOZZ.Brownian.MeasureTranslationFinite
public import DOZZ.Brownian.Barrier.ZeroDrift

/-!
# Measurability of the unit block with a varying initial time

The lateral measure is locally finite rather than finite on the whole line. Integrate over
the existing disjoint compact-shell exhaustion to obtain a measurable representative of
the literal block mass. On locally finite lateral measures the representative agrees with
the original mass, including at a random initial time.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The supplied continuous Brownian path has a Brownian pushforward law on its own carrier. -/
theorem lateralUnitBlock_brownianPath_map_isBrownian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : Ω → BrownianPath)
    (hB : IsBrownianReal (fun t ω => B ω t) P) :
    IsBrownianReal (fun t p => p t) (P.map B) := by
  have hm := aemeasurable_brownianPath_of_eval hB.aemeasurable
  refine ⟨⟨?_⟩, ae_of_all _ (fun p => p.continuous)⟩
  intro I
  have he : Measurable (fun p : BrownianPath => I.restrict (fun t => p t)) :=
    (Finset.measurable_restrict I).comp
      (Measurable.of_eval (fun t => ContinuousMap.measurable_eval t))
  refine ⟨he.aemeasurable, ?_⟩
  exact (AEMeasurable.map_map_of_aemeasurable he.aemeasurable hm).trans (hB.hasLaw I).map_eq

/-- The endpoint formula uses the literal two continuous-path evaluations. -/
theorem lateralUnitBlock_endpoint_eq {Ω : Type*} (B : Ω → BrownianPath)
    (F : ℝ → ℝ) (a : ℝ≥0) (ω : Ω) :
    lateralUnitBlockEndpointIncrement B F a ω =
      B ω (a + 1) - B ω a + F ((a : ℝ) + 1) - F a := by
  unfold lateralUnitBlockEndpointIncrement
  have heval (t : ℝ≥0) : brownianPathValue B ω (t : ℝ) = B ω t := by
    rw [brownianPathValue, dite_eq_left t.coe_nonneg]
    congr 1
  rw [show (a : ℝ) + 1 = ((a + 1 : ℝ≥0) : ℝ) by simp, heval, heval]

/-- The endpoint is AE measurable even when the initial time is random. -/
theorem lateralUnitBlock_endpoint_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : Ω → BrownianPath) (hB : AEMeasurable B P)
    (F : ℝ → ℝ) (hF : Measurable F) (a : Ω → ℝ≥0) (ha : AEMeasurable a P) :
    AEMeasurable (fun ω => lateralUnitBlockEndpointIncrement B F (a ω) ω) P := by
  have heval : Measurable (fun z : BrownianPath × ℝ≥0 => z.1 z.2) :=
    continuous_eval.measurable
  have hm := ((heval.comp_aemeasurable (hB.prodMk (ha.add_const 1))).sub
    (heval.comp_aemeasurable (hB.prodMk ha))).add
      (hF.comp_aemeasurable ((NNReal.continuous_coe.measurable.comp_aemeasurable ha).add_const 1))
  have hm' := hm.sub (hF.comp_aemeasurable
    (NNReal.continuous_coe.measurable.comp_aemeasurable ha))
  exact hm'.congr (ae_of_all _ (fun ω => (lateralUnitBlock_endpoint_eq B F (a ω) ω).symm))

/-- The measurable unit-block integrand on the actual continuous-path carrier. -/
noncomputable def lateralUnitBlock_blockIntegrand (γ : ℝ) (F : ℝ → ℝ)
    (z : (ℝ≥0 × BrownianPath) × ℝ) : ℝ≥0∞ :=
  if z.2 ∈ Icc (z.1.1 : ℝ) ((z.1.1 : ℝ) + 1) then
    ENNReal.ofReal (Real.exp (γ *
      (z.1.2 (Real.toNNReal z.2) + F z.2 - (z.1.2 z.1.1 + F z.1.1)))) else 0

/-- The integrand is jointly measurable in the time, path and integration variable. -/
theorem measurable_lateralUnitBlock_blockIntegrand (γ : ℝ) (F : ℝ → ℝ) (hF : Measurable F) :
    Measurable (lateralUnitBlock_blockIntegrand γ F) := by
  have heval : Measurable (fun z : (ℝ≥0 × BrownianPath) × ℝ =>
      z.1.2 (Real.toNNReal z.2)) :=
    continuous_eval.measurable.comp
      ((measurable_snd.comp measurable_fst).prodMk
        ((by fun_prop : Measurable Real.toNNReal).comp measurable_snd))
  have hstart : Measurable (fun z : (ℝ≥0 × BrownianPath) × ℝ => z.1.2 z.1.1) :=
    continuous_eval.measurable.comp
      ((measurable_snd.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_fst))
  have ha : Measurable (fun z : (ℝ≥0 × BrownianPath) × ℝ => (z.1.1 : ℝ)) :=
    NNReal.continuous_coe.measurable.comp (measurable_fst.comp measurable_fst)
  have hset : MeasurableSet {z : (ℝ≥0 × BrownianPath) × ℝ |
      z.2 ∈ Icc (z.1.1 : ℝ) ((z.1.1 : ℝ) + 1)} :=
    (measurableSet_le ha measurable_snd).inter
      (measurableSet_le measurable_snd (ha.add_const 1))
  exact Measurable.ite hset
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul ((heval.add (hF.comp measurable_snd)).sub
        (hstart.add (hF.comp ha)))))) measurable_const

/-- One finite shell contribution to the block mass. -/
noncomputable def lateralUnitBlock_blockShell (γ : ℝ) (F : ℝ → ℝ) (n : ℕ)
    (z : (ℝ≥0 × BrownianPath) × Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ s, lateralUnitBlock_blockIntegrand γ F (z.1, s)
    ∂(finiteRestrictionOnSet (translationShell n) z.2 : Measure ℝ)

/-- The shell sum is a measurable representative of the block mass. -/
noncomputable def lateralUnitBlock_blockShellSum (γ : ℝ) (F : ℝ → ℝ)
    (z : (ℝ≥0 × BrownianPath) × Measure ℝ) : ℝ≥0∞ :=
  ∑' n, lateralUnitBlock_blockShell γ F n z

theorem measurable_lateralUnitBlock_blockShell (γ : ℝ) (F : ℝ → ℝ) (hF : Measurable F) (n : ℕ) :
    Measurable (lateralUnitBlock_blockShell γ F n) := by
  exact (measurable_lintegral_finiteMeasure_parameter
    (measurable_lateralUnitBlock_blockIntegrand γ F hF)).comp
      (measurable_fst.prodMk
        ((measurable_finiteRestrictionOnSet _ (measurableSet_translationShell n)).comp
          measurable_snd))

theorem measurable_lateralUnitBlock_blockShellSum (γ : ℝ) (F : ℝ → ℝ) (hF : Measurable F) :
    Measurable (lateralUnitBlock_blockShellSum γ F) :=
  Measurable.tsum (fun n => measurable_lateralUnitBlock_blockShell γ F hF n)

/-- The measurable integrand agrees with the integrand of `DOZZ.lateralUnitBlockMass` at all real
times. -/
theorem lateralUnitBlock_blockIntegrand_eq {Ω : Type*} (γ : ℝ) (B : Ω → BrownianPath)
    (F : ℝ → ℝ) (a : ℝ≥0) (ω : Ω) (s : ℝ) :
    lateralUnitBlock_blockIntegrand γ F ((a, B ω), s) =
      (if s ∈ Icc (a : ℝ) ((a : ℝ) + 1) then
        ENNReal.ofReal (Real.exp (γ *
          (brownianPathValue B ω s + F s - (brownianPathValue B ω a + F a)))) else 0) := by
  unfold lateralUnitBlock_blockIntegrand
  split_ifs with hs
  · have hs0 : 0 ≤ s := a.coe_nonneg.trans hs.1
    have he : Real.toNNReal s = (⟨s, hs0⟩ : ℝ≥0) := by
      apply NNReal.eq
      exact Real.coe_toNNReal _ hs0
    simp only [brownianPathValue, dite_eq_left hs0, dite_eq_left a.coe_nonneg, he]
    congr 5
  · rfl

/-- Local finiteness justifies the shell representative without a cutoff approximation. -/
theorem lateralUnitBlock_unitBlockMass_eq_shellSum {Ω : Type*} (γ : ℝ)
    (B : Ω → BrownianPath) (F : ℝ → ℝ) (Z : Ω → Measure ℝ)
    (a : ℝ≥0) (ω : Ω) (hlocal : LocallyFiniteOnTranslationWindows (Z ω)) :
    lateralUnitBlockMass γ B F Z a ω = lateralUnitBlock_blockShellSum γ F ((a, B ω), Z ω) := by
  let f : ℝ → ℝ≥0∞ := fun s => lateralUnitBlock_blockIntegrand γ F ((a, B ω), s)
  have hshell (n : ℕ) : Z ω (translationShell n) < ⊤ :=
    lt_of_le_of_lt (measure_mono (translationShell_subset_window n)) (hlocal n)
  have hrestriction (n : ℕ) :
      (finiteRestrictionOnSet (translationShell n) (Z ω) : Measure ℝ) =
        (Z ω).restrict (translationShell n) := by
    simp [finiteRestrictionOnSet, hshell n]
  have hdecomp : Measure.sum (fun n => (Z ω).restrict (translationShell n)) = Z ω := by
    rw [← Measure.restrict_iUnion translationShell_pairwise_disjoint
      (fun n => measurableSet_translationShell n), translationShell_iUnion,
      Measure.restrict_univ]
  change (∫⁻ s, _ ∂Z ω) = _
  rw [show (fun s => if s ∈ Icc (a : ℝ) ((a : ℝ) + 1) then
      ENNReal.ofReal (Real.exp (γ *
        (brownianPathValue B ω s + F s - (brownianPathValue B ω a + F a)))) else 0) = f
      from funext (fun s => (lateralUnitBlock_blockIntegrand_eq γ B F a ω s).symm)]
  calc
    (∫⁻ s, f s ∂Z ω) = ∫⁻ s, f s ∂Measure.sum
        (fun n => (Z ω).restrict (translationShell n)) := by rw [hdecomp]
    _ = ∑' n, ∫⁻ s, f s ∂(Z ω).restrict (translationShell n) :=
      lintegral_sum_measure f _
    _ = lateralUnitBlock_blockShellSum γ F ((a, B ω), Z ω) := by
      apply tsum_congr
      intro n
      change (∫⁻ s, f s ∂(Z ω).restrict (translationShell n)) =
        ∫⁻ s, f s ∂(finiteRestrictionOnSet (translationShell n) (Z ω) : Measure ℝ)
      rw [hrestriction]

/-- The literal unit-block mass is AE measurable for an arbitrary AE measurable initial time. -/
theorem lateralUnitBlock_unitBlockMass_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) (B : Ω → BrownianPath) (hB : AEMeasurable B P)
    (F : ℝ → ℝ) (hF : Measurable F) (Z : Ω → Measure ℝ) (hZ : AEMeasurable Z P)
    (a : Ω → ℝ≥0) (ha : AEMeasurable a P)
    (hlocal : ∀ᵐ ω ∂P, LocallyFiniteOnTranslationWindows (Z ω)) :
    AEMeasurable (fun ω => lateralUnitBlockMass γ B F Z (a ω) ω) P := by
  have hrep := (measurable_lateralUnitBlock_blockShellSum γ F hF).comp_aemeasurable
    ((ha.prodMk hB).prodMk hZ)
  apply hrep.congr
  filter_upwards [hlocal] with ω hω
  exact (lateralUnitBlock_unitBlockMass_eq_shellSum γ B F Z (a ω) ω hω).symm

end DOZZ.Proofs

end
