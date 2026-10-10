/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.RetainedZeroDeletedWeight
public import DOZZ.FourPoint.Dual.RetainedZeroRelations
public import DOZZ.FourPoint.ReflectedOuter.InverseDifference
import Mathlib.Tactic
/-! # The actual deleted-disk inverse-expectation error -/
public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The retained zero inverse expectation differs from the full zero inverse expectation
by at most the deleted-disk radial power. -/
theorem dual_retainedZero_deleted_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hp : 0 < p)
    (hα₁ : α₁ - 2 / γ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hβ : γ * α₁ < 4) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
      |(∫⁻ ω, dualRetainedZeroMass γ α₁ α₂ α₃ r (M ω) ^ (-p) ∂P).toReal -
        (∫⁻ ω, coulombMass γ (M ω) ![-2 / γ, α₁, α₂] ![0, 0, 1] α₃ ^ (-p) ∂P).toReal| ≤
          C * r ^ (4 - γ * α₁) := by
  let e : ℝ := 4 - γ * α₁
  obtain ⟨Cd, hCd, hdb⟩ := dual_retainedZero_deleted_weight_bound
    P X hX γ hγ hγ₂ M hM α₁ α₂ α₃ (p + 1) (by linarith only [hp]) hβ
  obtain ⟨Cs, _, hsb⟩ := dual_retainedZero_inverse_moment_uniform
    P X hX γ hγ hγ₂ M hM α₁ α₂ α₃ p hp.le
  refine ⟨p * Cd, mul_pos hp hCd, ?_⟩
  intro r hr hr₀
  have hr₁ : r ≤ 1 := by linarith only [hr₀]
  let S : Ω → ℝ≥0∞ := fun ω => dualRetainedZeroMass γ α₁ α₂ α₃ r (M ω)
  let F : Ω → ℝ≥0∞ := fun ω => coulombMass γ (M ω) ![-2 / γ, α₁, α₂] ![0, 0, 1] α₃
  let I : Ω → ℝ≥0∞ := fun ω => ∫⁻ x in Metric.ball (0 : ℂ) r,
    ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ 0 x) ∂M ω
  let R : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal p * (I ω * S ω ^ (-(p + 1)))
  have hm := gmc_measure_aemeasurable_of_isGMCOf P X hX γ hγ hγ₂ M hM
  have hSm : AEMeasurable S P :=
    (dual_retainedZero_measure_measurable γ α₁ α₂ α₃ r).comp_aemeasurable hm
  have hFm : AEMeasurable F P :=
    gmc_coulombMass_aemeasurable P X hX γ hγ hγ₂ M hM _ _ _
  have hSt : (∫⁻ ω, S ω ^ (-p) ∂P) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hsb r hr₁)
  have hFt : (∫⁻ ω, F ω ^ (-p) ∂P) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hSt
    exact lintegral_mono fun ω => ennreal_rpow_antitone_of_nonpos
      (dual_retainedZero_le_full γ α₁ α₂ α₃ r (M ω)) (neg_nonpos.mpr hp.le)
  have hRb : (∫⁻ ω, R ω ∂P) ≤ ENNReal.ofReal ((p * Cd) * r ^ e) := by
    dsimp only [R]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc
      _ ≤ ENNReal.ofReal p * ENNReal.ofReal (Cd * r ^ e) := mul_le_mul' le_rfl (hdb r hr hr₀)
      _ = _ := by rw [← ENNReal.ofReal_mul hp.le]; congr 1; ring
  have hRt := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hRb
  have hSF : ∀ᵐ ω ∂P, S ω ^ (-p) ≤ F ω ^ (-p) + R ω := by
    filter_upwards [dual_retainedZero_ae_positive_finite P X hX γ hγ hγ₂ M hM
      α₁ α₂ α₃ r hr₁ hα₁ hα₂ hα₃,
      gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ₂ M hM 0,
      gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ₂ M hM 1] with ω hpf h0 h1
    have he : F ω = S ω + I ω := dual_retainedZero_split γ α₁ α₂ α₃ r hγ.ne' (M ω) h0 h1
    have hsfin : S ω ≠ ⊤ := ne_top_of_le_ne_top hpf.2.ne
      (dual_retainedZero_le_full γ α₁ α₂ α₃ r (M ω))
    have hifin : I ω ≠ ⊤ := ne_top_of_le_ne_top hpf.2.ne (le_add_self.trans_eq he.symm)
    rw [he]
    simpa only [R, mul_assoc] using reflected_ennreal_inverse_add_bound p hp (S ω) (I ω)
      hpf.1.ne' hsfin hifin
  have hFS : ∀ᵐ ω ∂P, F ω ^ (-p) ≤ S ω ^ (-p) + R ω := Filter.Eventually.of_forall fun ω =>
    (ennreal_rpow_antitone_of_nonpos (dual_retainedZero_le_full γ α₁ α₂ α₃ r (M ω))
      (neg_nonpos.mpr hp.le)).trans le_self_add
  have hh := reflected_lintegral_toReal_difference_bound P (fun ω => S ω ^ (-p))
    (fun ω => F ω ^ (-p)) R (hSm.pow_const _) (hFm.pow_const _) hSt hFt hRt hSF hFS
  calc
    _ ≤ (∫⁻ ω, R ω ∂P).toReal := hh
    _ ≤ ((p * Cd) * r ^ e) := by
      have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hRb
      simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (p * Cd) * r ^ e)] using ht

end DOZZ.Proofs
