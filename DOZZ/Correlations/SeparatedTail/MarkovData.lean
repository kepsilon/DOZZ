/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GFFStructure.ExistsExteriorPinnedMarkovUniform
public import DOZZ.Correlations.SeparatedTail.DirichletCutoff
public import DOZZ.Correlations.SeparatedTail.EnvelopePower
public import Mathlib.Probability.Moments.Covariance

/-! Extract just the finite-circle clauses used by the separated joint-tail estimate from the
exterior-pinned Markov theorem `DOZZ.exists_exteriorPinned_markov_uniform`. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Metric Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The data below are obtained on the original probability space from exterior-pinned Markov.
The restoration scalar is retained literally, and is absent from the independence assertion. -/
structure SeparatedTailMarkovData {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ) (c : Fin 2 → ℂ)
    (R : ℝ) (hR : 1 < R) (C : ℝ → ℝ) where
  D : Fin 2 → Ω → Distr
  H : Fin 2 → Ω → ℂ → ℝ
  Dc : Fin 2 → Ω → ℂ → ℝ → ℝ
  measurable_D : ∀ i, Measurable (fun ω => fun f : TestFn => D i ω f)
  measurable_H : ∀ i, Measurable (fun q : Ω × ℂ => H i q.1 q.2)
  continuous_H : ∀ i, ∀ᵐ ω ∂P, ContinuousOn (H i ω) (closedBall (c i) 1)
  independent_D : IndepFun (fun ω => fun f : TestFn => D 0 ω f)
    (fun ω => fun f : TestFn => D 1 ω f) P
  measurable_Dc : ∀ i, Measurable[(MeasurableSpace.comap
    (fun ω => fun f : TestFn => D i ω f) MeasurableSpace.pi).prod inferInstance]
      (fun q : Ω × (ℂ × ℝ) => Dc i q.1 q.2.1 q.2.2)
  gaussian_Dc : ∀ i, IsGaussianProcess
    (fun q : {q : ℂ × ℝ // ‖q.1-c i‖+Real.exp (-q.2) < 5/4} =>
      fun ω => Dc i ω q.1.1 q.1.2) P
  mean_Dc : ∀ i x r, ‖x-c i‖+Real.exp (-r) < 5/4 → (∫ ω, Dc i ω x r ∂P) = 0
  split : ∀ i x r, ‖x-c i‖+Real.exp (-r) < 5/4 →
    (fun ω => Xc ω x r) =ᵐ[P] fun ω => Dc i ω x r+H i ω x-
      equatorRestorationScalar Xc R (by linarith) ω
  covariance_Dc : ∀ i x y r s, ‖x-c i‖+Real.exp (-r) < 5/4 →
    ‖y-c i‖+Real.exp (-s) < 5/4 →
    (∫ ω, Dc i ω x r*Dc i ω y s ∂P) =
      ∫ v, ∫ w, diskGreenKernel (c i) (5/4) (by norm_num) v w
        ∂circleMeasure y s ∂circleMeasure x r
  envelope_bound : ∀ i l, 0 < l →
    (∫⁻ ω, separatedTail_harmonicEnvelope (c i) (H i)
      (equatorRestorationScalar Xc R (by linarith)) l ω ∂P) ≤ ENNReal.ofReal (C l)

/-- One realization-independent envelope bound supports all separated center pairs. This lemma
applies `DOZZ.exists_exteriorPinned_markov_uniform` and discards only clauses unused by the
cutoff transfer. -/
theorem separatedTail_exists_markov_data (R : ℝ) (hR : 1 < R) :
    ∃ C : ℝ → ℝ, (∀ l, 0 < l → 0 < C l) ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
        (Xc : Ω → ℂ → ℝ → ℝ), IsEquatorGFF P X → IsCircleAverage P X Xc →
        ∀ c : Fin 2 → ℂ, (∀ i, ‖c i‖+5/4+1/4 ≤ R) →
          (∀ i j, i ≠ j → 3 ≤ ‖c i-c j‖) → Nonempty (SeparatedTailMarkovData P Xc c R hR C) := by
  obtain ⟨C,hC,h⟩ := DOZZ.exists_exteriorPinned_markov_uniform 2 R (5/4) 1 (1/4) hR
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C,hC,fun Ω _ P X Xc hX hc c hpin hsep => ?_⟩
  let _ : IsProbabilityMeasure P := hX.1
  have hsep' : ∀ i j, i ≠ j → 2*(5/4 : ℝ)+1/4 ≤ dist (c i) (c j) := by
    intro i j hij
    rw [dist_eq_norm]
    linarith [hsep i j hij]
  obtain ⟨D,H,Hi,Dc,ε,q,p,hε,hεδ,hq,hp,hlim,hD,hH,hHm,hHi,hHim,hHic,
    hdecomp,hind,hDext,henv,hDcm,hDcg,hDcs,hDcc⟩ := h Ω P X Xc hX hc c hpin hsep'
  refine ⟨{
    D := D
    H := Hi
    Dc := Dc
    measurable_D := fun i => Measurable.of_eval (fun f => ((hD i).2.1 f).1)
    measurable_H := hHi
    continuous_H := ?_
    independent_D := ?_
    measurable_Dc := hDcm
    gaussian_Dc := hDcg
    mean_Dc := fun i x r hx => (hDcs i x r hx).2.1
    split := fun i x r hx => (hDcs i x r hx).2.2
    covariance_Dc := ?_
    envelope_bound := ?_ }⟩
  · intro i
    filter_upwards [hdecomp] with ω hω
    exact (hω.2.2.1 i).2.continuousOn.mono (closedBall_subset_ball (by norm_num))
  · exact hind.indepFun (show (some (0 : Fin 2) : Option (Fin 2)) ≠ some 1 by decide)
  · intro i x y r s hx hy
    have hv := hDcc i x y r s hx hy
    rw [covariance_eq_sub (hDcs i x r hx).1 (hDcs i y s hy).1,
      (hDcs i x r hx).2.1, (hDcs i y s hy).2.1, zero_mul, sub_zero] at hv
    exact hv
  · intro i l hl
    simpa only [separatedTail_harmonicEnvelope, iSup_subtype] using henv i l hl

end DOZZ.Proofs
