/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.ChaosLawFDD

/-! Finite-reference spatial integral laws for the inversion regularization. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- Measurable fields with equal finite-dimensional laws have equal finite vectors of spatial
integrals against a finite reference measure, whenever the transformed sections are integrable. -/
theorem spatialIntegral_vector_law_of_fdd_finite
    {Ω Ω' S : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace S] [Nonempty S]
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (ν : FiniteMeasure S) {m : ℕ} (X : Ω → S → ℝ) (Y : Ω' → S → ℝ)
    (z : Fin m → S → ℝ → ℝ)
    (hX : Measurable (fun p : Ω × S => X p.1 p.2))
    (hY : Measurable (fun p : Ω' × S => Y p.1 p.2))
    (hz : ∀ j, Measurable (fun p : S × ℝ => z j p.1 p.2))
    (hintX : ∀ j, ∀ᵐ ω ∂P, Integrable (fun x => z j x (X ω x)) (ν : Measure S))
    (hintY : ∀ j, ∀ᵐ ω ∂P', Integrable (fun x => z j x (Y ω x)) (ν : Measure S))
    (hFDD : ∀ n (xs : Fin n → S), P.map (fun ω i => X ω (xs i)) =
      P'.map (fun ω i => Y ω (xs i))) :
    P.map (fun ω j => ∫ x, z j x (X ω x) ∂(ν : Measure S)) =
      P'.map (fun ω j => ∫ x, z j x (Y ω x) ∂(ν : Measure S)) := by
  classical
  let V : Ω → Fin 0 → ℝ := fun _ i => Fin.elim0 i
  let V' : Ω' → Fin 0 → ℝ := fun _ i => Fin.elim0 i
  let z' : Fin m → S → ℝ → ℝ := fun j x t => (ν.mass : ℝ) * z j x t
  have hmeasure : (ν : Measure S) = (ν.mass : ℝ≥0) • (ν.normalize : Measure S) :=
    congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) ν.self_eq_mass_smul_normalize
  have hiX j : ∀ᵐ ω ∂P, Integrable (fun x => z' j x (X ω x)) (ν.normalize : Measure S) := by
    by_cases hm : ν.mass = 0
    · exact ae_of_all _ fun ω => by simp only [z', hm, NNReal.coe_zero, zero_mul]; exact integrable_zero _ _ _
    · filter_upwards [hintX j] with ω hω
      rw [hmeasure] at hω
      have ht : Integrable (fun x => z j x (X ω x)) (ν.normalize : Measure S) :=
        (integrable_smul_measure (ENNReal.coe_ne_zero.mpr hm) (by finiteness)).mp hω
      exact ht.const_mul _
  have hiY j : ∀ᵐ ω ∂P', Integrable (fun x => z' j x (Y ω x)) (ν.normalize : Measure S) := by
    by_cases hm : ν.mass = 0
    · exact ae_of_all _ fun ω => by simp only [z', hm, NNReal.coe_zero, zero_mul]; exact integrable_zero _ _ _
    · filter_upwards [hintY j] with ω hω
      rw [hmeasure] at hω
      have ht : Integrable (fun x => z j x (Y ω x)) (ν.normalize : Measure S) :=
        (integrable_smul_measure (ENNReal.coe_ne_zero.mpr hm) (by finiteness)).mp hω
      exact ht.const_mul _
  have hfdd : ∀ n (xs : Fin n → S),
      P.map (fun ω => (V ω, fun i => X ω (xs i))) =
      P'.map (fun ω => (V' ω, fun i => Y ω (xs i))) := by
    intro n xs
    let L : (Fin n → ℝ) → (Fin 0 → ℝ) × (Fin n → ℝ) := fun a => (fun i => Fin.elim0 i, a)
    have hL : Measurable L := measurable_const.prodMk measurable_id
    have hmX : Measurable (fun ω i => X ω (xs i)) :=
      measurable_pi_iff.mpr (fun i => hX.comp (measurable_id.prodMk measurable_const))
    have hmY : Measurable (fun ω i => Y ω (xs i)) :=
      measurable_pi_iff.mpr (fun i => hY.comp (measurable_id.prodMk measurable_const))
    have he := congrArg (fun μ => μ.map L) (hFDD n xs)
    simpa only [Measure.map_map hL hmX, Measure.map_map hL hmY, L, V, V', Function.comp_def] using he
  have he := (chaosLawFDD_of_integrable (ν.normalize : Measure S) X Y V V' z'
    measurable_const measurable_const hX hY
    (fun j => measurable_const.mul (hz j)) hiX hiY hfdd
    (0 : BoundedContinuousFunction ((Fin 0 → ℝ) × (Fin m → ℝ)) ℝ)).1
  have hmass (a : S → ℝ) : (∫ x, (ν.mass : ℝ) * a x ∂(ν.normalize : Measure S)) =
      ∫ x, a x ∂(ν : Measure S) := by
    rw [hmeasure, integral_smul_nnreal_measure, integral_const_mul]
    rfl
  simp only [z', hmass] at he
  have hmX : Measurable (fun ω => (V ω, fun j => ∫ x, z j x (X ω x) ∂(ν : Measure S))) := by
    apply measurable_const.prodMk
    apply measurable_pi_iff.mpr
    intro j
    exact ((hz j).comp (measurable_snd.prodMk hX)).stronglyMeasurable.integral_prod_right'.measurable
  have hmY : Measurable (fun ω => (V' ω, fun j => ∫ x, z j x (Y ω x) ∂(ν : Measure S))) := by
    apply measurable_const.prodMk
    apply measurable_pi_iff.mpr
    intro j
    exact ((hz j).comp (measurable_snd.prodMk hY)).stronglyMeasurable.integral_prod_right'.measurable
  have hsnd := congrArg (fun μ => μ.map Prod.snd) he
  simpa only [Measure.map_map measurable_snd hmX, Measure.map_map measurable_snd hmY,
    Function.comp_def] using hsnd

end DOZZ.Proofs
