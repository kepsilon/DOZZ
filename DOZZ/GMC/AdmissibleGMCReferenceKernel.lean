/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.PowerKernelIntegrability
public import DOZZ.Statements.GMC.IsAdmissibleLogRegularization
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! Compact Riesz-kernel integrability for the reference measure of an admissible chart. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- A planar Riesz kernel with exponent below two is integrable against the product of the
reference measure restricted to a compact chart piece. The continuous reference density is bounded
on that compact set, so the product reference measure is dominated by a constant multiple of
restricted planar volume. -/
theorem admissible_logRegularization_reference_pair_kernel_lintegrable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∫⁻ p : ℂ × ℂ,
      ENNReal.ofReal (‖p.1 - p.2‖ ^ (-κ)) ∂
        ((logRegularizationReference U dens).restrict K).prod
          ((logRegularizationReference U dens).restrict K) ≠ ∞ := by
  let ν : Measure ℂ := (logRegularizationReference U dens).restrict K
  let volK : Measure ℂ := volume.restrict K
  let c : ℝ≥0∞ := ENNReal.ofReal
      (max ((hK.bddAbove_image (hY.densityContinuous.mono hKU)).choose) 0)
  have hν : ν = volK.withDensity (fun x => ENNReal.ofReal (dens x)) := by
    dsimp [ν, volK, logRegularizationReference]
    rw [restrict_withDensity hK.measurableSet,
      Measure.restrict_restrict_of_subset hKU]
  have hdenBound : ∀ x ∈ K, ENNReal.ofReal (dens x) ≤ c := by
    intro x hx
    dsimp [c]
    have hbdd := (hK.bddAbove_image (hY.densityContinuous.mono hKU)).choose_spec
    have hle : dens x ≤ max
        ((hK.bddAbove_image (hY.densityContinuous.mono hKU)).choose) 0 := by
      exact le_trans (hbdd (Set.mem_image_of_mem dens hx)) (le_max_left _ _)
    exact ENNReal.ofReal_le_ofReal hle
  have hνle : ν ≤ c • volK := by
    rw [hν, ← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact hdenBound x hx
  have hνSFinite : SFinite ν := by
    rw [hν]
    infer_instance
  have hprod : ν.prod ν ≤ (c * c) • (volK.prod volK) := by
    calc
      ν.prod ν ≤ (c • volK).prod (c • volK) :=
        @Measure.prod_mono ℂ ℂ _ _ ν (c • volK) ν (c • volK)
          hνSFinite (by infer_instance) hνle hνle
      _ = (c * c) • (volK.prod volK) := by
        rw [Measure.prod_smul_left, Measure.prod_smul_right]
        simp [smul_smul]
  obtain ⟨B, hB, hpair⟩ :=
    complex_norm_pair_neg_rpow_lintegral_isCompact K hK κ hκ hκ2
  have hbase :
      ∫⁻ p : ℂ × ℂ,
        ENNReal.ofReal (‖p.1 - p.2‖ ^ (-κ)) ∂(volK.prod volK) ≠ ∞ := by
    have hrewrite : volK.prod volK =
        (volume.prod volume).restrict (K ×ˢ K) := by
      exact Measure.prod_restrict K K
    rw [hrewrite]
    change (∫⁻ p in K ×ˢ K,
      ENNReal.ofReal (‖p.1 - p.2‖ ^ (-κ)) ∂(volume.prod volume)) ≠ ∞
    exact ne_top_of_le_ne_top hB hpair
  have hlin :
      ∫⁻ p : ℂ × ℂ,
        ENNReal.ofReal (‖p.1 - p.2‖ ^ (-κ)) ∂(ν.prod ν) ≤
      ∫⁻ p : ℂ × ℂ,
        ENNReal.ofReal (‖p.1 - p.2‖ ^ (-κ)) ∂((c * c) • (volK.prod volK)) :=
    lintegral_mono' hprod (fun _ => le_rfl)
  have hcctop : c * c ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hlin' :
      ∫⁻ p : ℂ × ℂ,
        ENNReal.ofReal (‖p.1 - p.2‖ ^ (-κ)) ∂((c * c) • (volK.prod volK)) =
      c * c * ∫⁻ p : ℂ × ℂ,
        ENNReal.ofReal (‖p.1 - p.2‖ ^ (-κ)) ∂(volK.prod volK) := by
    rw [lintegral_smul_measure]
    simp only [smul_eq_mul]
  have hbaseLeB :
      (∫⁻ p : ℂ × ℂ,
        ENNReal.ofReal (‖p.1 - p.2‖ ^ (-κ)) ∂(volK.prod volK)) ≤ B := by
    rw [show volK.prod volK = (volume.prod volume).restrict (K ×ˢ K) by
      exact Measure.prod_restrict K K]
    change (∫⁻ p in K ×ˢ K,
      ENNReal.ofReal (‖p.1 - p.2‖ ^ (-κ)) ∂(volume.prod volume)) ≤ B
    exact hpair
  have hscaled : c * c *
      (∫⁻ p : ℂ × ℂ,
        ENNReal.ofReal (‖p.1 - p.2‖ ^ (-κ)) ∂(volK.prod volK)) ≤ c * c * B := by
    calc
      c * c * (∫⁻ p : ℂ × ℂ,
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-κ)) ∂(volK.prod volK)) =
          (∫⁻ p : ℂ × ℂ,
            ENNReal.ofReal (‖p.1 - p.2‖ ^ (-κ)) ∂(volK.prod volK)) * (c * c) := by ac_rfl
      _ ≤ B * (c * c) := mul_le_mul_left hbaseLeB (c * c)
      _ = c * c * B := by ac_rfl
  apply ne_top_of_le_ne_top (ENNReal.mul_ne_top hcctop hB)
  exact hlin.trans (hlin'.le.trans hscaled)


end DOZZ.Proofs
