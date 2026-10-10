/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardLimitConvC

/-! # The symmetrized cutoff Ward identity at integer cutoffs

For every integer cutoff below the separation scale, the cutoff Ward identity holds with the
cutoff chaos replaced by its finite version and the right side written through the antisymmetrized
cutoff kernel and the far-region test function. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]
variable {γ q δ : ℝ} {ρ kt k₂ φ : ℂ → ℝ} {D : Set ℂ}
variable {P : Measure Ω} {X : Ω → Distr} {M : Ω → Measure ℂ} {Xc : Ω → ℂ → ℝ → ℝ}

namespace BPZLimitData

/-- Uniform bounds for the cutoff-region weights. -/
theorem cutWeight_mul_bdd (hd : BPZLimitData γ q δ ρ kt k₂ φ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) x, |φ x * bpzWardCutWeight γ q n kt x| ≤ C ∧
      |ρ x * bpzWardCutWeight γ q n kt x| ≤ C := by
  obtain ⟨K, hK0, hK⟩ := hd.cutWeight_bound
  obtain ⟨B, hB0, hB⟩ := hd.phi_bdd
  refine ⟨(B + 1) * K, by positivity, fun n x => ?_⟩
  have h := (hd.rho_abs_cutWeight_le hK hK0 n x).1
  constructor
  · rw [abs_mul]
    calc |φ x| * |bpzWardCutWeight γ q n kt x| ≤ B * ρ x * |bpzWardCutWeight γ q n kt x| :=
          mul_le_mul_of_nonneg_right (hd.abs_phi_le hB x) (abs_nonneg _)
      _ = B * (ρ x * |bpzWardCutWeight γ q n kt x|) := by ring
      _ ≤ B * K := mul_le_mul_of_nonneg_left h hB0
      _ ≤ (B + 1) * K := by nlinarith
  · rw [abs_mul, abs_of_nonneg (hd.ρ_nonneg x)]
    calc ρ x * |bpzWardCutWeight γ q n kt x| ≤ K := h
      _ ≤ (B + 1) * K := by nlinarith

/-- The cutoff Ward identity in symmetrized form, with the finite cutoff chaos. -/
theorem cutoff_identity_sym (hd : BPZLimitData γ q δ ρ kt k₂ φ D)
    (hp : BPZWardProb P X γ M Xc ρ k₂ D) (v : ℂ) {n : ℕ}
    (hn : BPZWardData γ q n δ ρ kt k₂ φ D) :
    ∫ ω, bpzMixedReal ρ (bpzWardCutWeight γ q n kt) k₂ (bpzCutChaos P Xc γ n ω) (M ω) ^ (-q) *
        ∫ x, bpzWardLeftWeight γ q n kt φ v x ∂bpzCutChaos P Xc γ n ω ∂P =
      ∫ ω, q * (bpzMixedReal ρ (bpzWardCutWeight γ q n kt) k₂ (bpzCutChaos P Xc γ n ω) (M ω) ^
        (-q - 1) * (γ ^ 2 * ((∫ x, ∫ y, bpzSymKer φ ρ (bpzWardCutWeight γ q n kt)
          (fun w => bpzLamDeriv n w v) x y ∂bpzCutChaos P Xc γ n ω ∂bpzCutChaos P Xc γ n ω) +
          ∫ x, bpzMixTest φ ρ (bpzWardCutWeight γ q n kt) k₂ (fun w => bpzTruncLogDeriv n w v)
            (M ω) x ∂bpzCutChaos P Xc γ n ω))) ∂P := by
  have hid := bpzWard_cutoff_identity hn hp v
  rw [← integral_const_mul] at hid
  have hae := bpzCutChaos_ae_eq P X hp.hX Xc hp.hXc γ n
  obtain ⟨C, hC0, hC⟩ := hd.cutWeight_mul_bdd
  calc _ = ∫ ω, bpzMixedReal ρ (bpzWardCutWeight γ q n kt) k₂ (regularizedGMC P Xc γ n ω)
          (M ω) ^ (-q) * ∫ x, bpzWardLeftWeight γ q n kt φ v x ∂regularizedGMC P Xc γ n ω ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with ω hω
        rw [hω]
    _ = _ := hid
    _ = _ := by
        refine integral_congr_ae ?_
        filter_upwards [hae, hp.k₂_int] with ω hω h2
        have := bpzCutChaos_isFiniteMeasure P Xc γ n ω
        have := hp.hM.1 ω
        rw [← hω, bpz_cutoff_sym_identity hd.phi_cont.measurable hd.ρ_meas
          (hd.measurable_cutWeight n) hd.k₂_meas (fun x => (hC n x).1) (fun x => (hC n x).2) h2 v]

end BPZLimitData

end DOZZ.Proofs
