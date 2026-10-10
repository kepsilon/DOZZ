/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.KahaneAffineMaxL1

/-! Passing affine-max expectations through convergence in L1. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DOZZ.Proofs

/-- An L1 limit of integrable functions is integrable when it is almost everywhere measurable. -/
theorem integrable_of_eLpNorm_sub_tendsto
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ι → Ω → ℝ) (g : Ω → ℝ) (l : Filter ι) [NeBot l]
    (hf : ∀ i, Integrable (f i) P) (_hg : AEMeasurable g P)
    (hL1 : Tendsto (fun i => eLpNorm (fun ω => f i ω - g ω) 1 P) l (𝓝 0)) :
    Integrable g P := by
  obtain ⟨i, hi⟩ := (hL1.eventually (gt_mem_nhds (by simp : (0 : ℝ≥0∞) < 1))).exists
  have hdiff : MemLp (fun ω => f i ω - g ω) 1 P :=
    lt_trans hi (by simp)
  have hI := (hf i).sub (memLp_one_iff_integrable.mp hdiff)
  convert hI using 1
  funext ω
  simp

/-- Affine-max expectations pass through L1 convergence along any filter. -/
theorem affineMax_integral_tendsto_of_eLpNorm
    {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype κ] [Nonempty κ]
    (P : Measure Ω) [IsFiniteMeasure P] (f : ι → Ω → ℝ) (g : Ω → ℝ)
    (l : Filter ι) (hf : ∀ i, Integrable (f i) P) (hg : AEMeasurable g P)
    (hL1 : Tendsto (fun i => eLpNorm (fun ω => f i ω - g ω) 1 P) l (𝓝 0))
    (a b : κ → ℝ) :
    Tendsto (fun i => ∫ ω, affineMax a b (f i ω) ∂P) l
      (𝓝 (∫ ω, affineMax a b (g ω) ∂P)) := by
  obtain ⟨C, hC, hbound⟩ := affineMax_abs_sub_le a b
  apply tendsto_integral_of_L1 _
    ((affineMax_continuous a b).measurable.comp_aemeasurable hg).aestronglyMeasurable
    (Eventually.of_forall fun i => affineMax_comp_integrable P (f i) (hf i) a b)
  have hupper : Tendsto (fun i => ENNReal.ofReal C * eLpNorm (fun ω => f i ω - g ω) 1 P) l (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) hL1
      (Or.inr ENNReal.ofReal_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper
    (fun _ => bot_le) (fun i => ?_)
  rw [eLpNorm_one_eq_lintegral_enorm (f := fun ω => f i ω - g ω)
    (((hf i).aemeasurable.sub hg).aestronglyMeasurable)]
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal C * ‖f i ω - g ω‖ₑ ∂P := by
      apply lintegral_mono
      intro ω
      simpa only [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul hC, Function.comp_def] using
        ENNReal.ofReal_le_ofReal (hbound (f i ω) (g ω))
    _ = ENNReal.ofReal C * ∫⁻ ω, ‖f i ω - g ω‖ₑ ∂P :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end DOZZ.Proofs
