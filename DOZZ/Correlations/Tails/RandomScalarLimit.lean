/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Scalar pin removal in the cutoff-to-limit passage. No independence is needed. -/

@[expose] public section

open MeasureTheory Filter Topology

namespace DOZZ.Proofs

/-- A finite measurable random scalar preserves convergence in measure on the source space. -/
theorem tendstoInMeasure_mul_left
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (f : ℕ → Ω → ℝ) (g W : Ω → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) P) (hW : AEStronglyMeasurable W P)
    (hfg : TendstoInMeasure P f atTop g) :
    TendstoInMeasure P (fun n ω => W ω * f n ω) atTop (fun ω => W ω * g ω) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun n => hW.mul (hf n))).mpr
  intro ns hns
  obtain ⟨ks, hks, hae⟩ := (hfg.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ks, hks, ?_⟩
  filter_upwards [hae] with ω hω
  exact tendsto_const_nhds.mul hω


end DOZZ.Proofs
