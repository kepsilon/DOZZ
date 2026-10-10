/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.RootedMarkedL1Limit
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Nonnegative measurable representatives preserve finite extended-real moments. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal

namespace DOZZ.Proofs

theorem nonnegative_moment_version
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (J : Ω → ℝ≥0∞)
    (hJ : AEMeasurable J P) (hf : ∀ᵐ ω ∂P, J ω ≠ ⊤) :
    ∃ f : Ω → ℝ, Measurable f ∧ (∀ ω, 0 ≤ f ω) ∧
      f =ᵐ[P] (fun ω => (J ω).toReal) ∧
      ∀ p : ℝ, 0 ≤ p → (∫⁻ ω, J ω^p ∂P) < ⊤ →
        Integrable (fun ω => f ω^p) P ∧
          (∫ ω, f ω^p ∂P) = (∫⁻ ω, J ω^p ∂P).toReal := by
  have hm := hJ.ennreal_toReal
  let g := hm.mk (fun ω => (J ω).toReal)
  let f := fun ω => max (g ω) 0
  have hfm : Measurable f := hm.measurable_mk.max measurable_const
  have hfg : f =ᵐ[P] (fun ω => (J ω).toReal) := by
    filter_upwards [hm.ae_eq_mk] with ω hω
    dsimp [f,g]
    rw [← hω,max_eq_left ENNReal.toReal_nonneg]
  refine ⟨f,hfm,fun ω => le_max_right _ _,hfg,?_⟩
  intro p hp hmean
  have he : (fun ω => f ω^p) =ᵐ[P] (fun ω => (J ω^p).toReal) :=
    hfg.mono fun ω hω => by
      change f ω^p = (J ω^p).toReal
      change f ω = (J ω).toReal at hω
      rw [hω,ENNReal.toReal_rpow]
  have hi := integrable_mass_toReal_of_finite_expectation P (fun ω => J ω^p)
    (hJ.pow_const p) (hf.mono fun ω hω => (ENNReal.rpow_lt_top_of_nonneg hp hω).ne) hmean
  refine ⟨hi.congr he.symm,?_⟩
  rw [integral_congr_ae he,integral_toReal (hJ.pow_const p)
    (hf.mono fun ω hω => ENNReal.rpow_lt_top_of_nonneg hp hω)]


end DOZZ.Proofs
