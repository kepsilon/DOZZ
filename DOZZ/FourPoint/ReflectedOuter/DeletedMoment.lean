/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.ReflectedOuter.DeletedDisk
public import DOZZ.FourPoint.ReflectedOuter.ZeroMassRelations
public import DOZZ.FourPoint.ReflectedOuter.InverseDifference
public import DOZZ.Statements.FourPoint.GammaHalfMoment
import Mathlib.Tactic

/-! # The deleted-disk bound for the literal inverse moment -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The inverse moment of the retained zero mass differs from the full zero moment by the
freezing power `κ+δ`, uniformly as the retained radius tends to zero. -/
theorem reflected_retainedZero_deleted_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hreflect : Q γ - α₁ < γ / 2) (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ r : ℝ, 0 < r → r < ε₀ →
      |(∫⁻ ω, (reflectedRetainedZeroMass γ α₁ α₂ α₃ r (M ω)) ^
          (-((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ)) ∂P).toReal -
        gammaHalfMoment P M γ α₁ α₂ α₃
          ((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ) 0| ≤
        C * r ^ (γ * (Q γ - α₁) + (α₁ + γ / 2 - Q γ) ^ 2 / 2) := by
  let p : ℝ := (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ
  let e : ℝ := γ * (Q γ - α₁) + (α₁ + γ / 2 - Q γ) ^ 2 / 2
  have hp : 0 < p := div_pos (by linarith only [hs]) hγ
  obtain ⟨Cd, εd, hCd, hεd, hdb⟩ := reflected_deleted_disk_weight_bound
    P X M γ α₁ α₂ α₃ hγ hγ₂ hα₁ hreflect hs hX hM
  obtain ⟨Cs, _, hsb⟩ := reflected_retainedZero_inverse_moment_uniform
    P X hX γ hγ hγ₂ M hM α₁ α₂ α₃ p hp.le
  refine ⟨p * Cd, min εd 1, mul_pos hp hCd, lt_min hεd zero_lt_one, ?_⟩
  intro r hr hr₀
  have hrd : r < εd := (lt_min_iff.mp hr₀).1
  have hr₁ : r ≤ 1 := (lt_min_iff.mp hr₀).2.le
  let S : Ω → ℝ≥0∞ := fun ω => reflectedRetainedZeroMass γ α₁ α₂ α₃ r (M ω)
  let F : Ω → ℝ≥0∞ := fun ω => coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃
  let I : Ω → ℝ≥0∞ := fun ω => ∫⁻ x in Metric.ball (0 : ℂ) r,
    ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x) ∂M ω
  let R : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal p * (I ω * S ω ^ (-(p + 1)))
  have hm := gmc_measure_aemeasurable_of_isGMCOf P X hX γ hγ hγ₂ M hM
  have hSm : AEMeasurable S P :=
    (reflected_retainedZero_measure_measurable γ α₁ α₂ α₃ r).comp_aemeasurable hm
  have hFm : AEMeasurable F P :=
    gmc_coulombMass_aemeasurable P X hX γ hγ hγ₂ M hM _ _ _
  have hSt : (∫⁻ ω, S ω ^ (-p) ∂P) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hsb r hr₁)
  have hFt : (∫⁻ ω, F ω ^ (-p) ∂P) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hSt
    exact lintegral_mono fun ω => ennreal_rpow_antitone_of_nonpos
      (reflected_retainedZero_le_full γ α₁ α₂ α₃ r (M ω)) (neg_nonpos.mpr hp.le)
  have hRb : (∫⁻ ω, R ω ∂P) ≤ ENNReal.ofReal ((p * Cd) * r ^ e) := by
    dsimp only [R]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc
      _ ≤ ENNReal.ofReal p * ENNReal.ofReal (Cd * r ^ e) := mul_le_mul' le_rfl (hdb r hr hrd)
      _ = _ := by rw [← ENNReal.ofReal_mul hp.le]; congr 1; ring
  have hRt := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hRb
  have hSF : ∀ᵐ ω ∂P, S ω ^ (-p) ≤ F ω ^ (-p) + R ω := by
    filter_upwards [reflected_retainedZero_ae_positive_finite P X hX γ hγ hγ₂ M hM
      α₁ α₂ α₃ r hr₁ (by linarith only [hα₁, hγ]) hα₂ hα₃,
      gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ₂ M hM 0,
      gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ₂ M hM 1] with ω hpf h0 h1
    have he : F ω = S ω + I ω := reflected_retainedZero_split γ α₁ α₂ α₃ r (M ω) h0 h1
    have hsfin : S ω ≠ ⊤ := ne_top_of_le_ne_top hpf.2.ne
      (reflected_retainedZero_le_full γ α₁ α₂ α₃ r (M ω))
    have hifin : I ω ≠ ⊤ := ne_top_of_le_ne_top hpf.2.ne (le_add_self.trans_eq he.symm)
    rw [he]
    simpa only [R, mul_assoc] using reflected_ennreal_inverse_add_bound p hp (S ω) (I ω)
      hpf.1.ne' hsfin hifin
  have hFS : ∀ᵐ ω ∂P, F ω ^ (-p) ≤ S ω ^ (-p) + R ω := Filter.Eventually.of_forall fun ω =>
    (ennreal_rpow_antitone_of_nonpos (reflected_retainedZero_le_full γ α₁ α₂ α₃ r (M ω))
      (neg_nonpos.mpr hp.le)).trans le_self_add
  have hh := reflected_lintegral_toReal_difference_bound P (fun ω => S ω ^ (-p))
    (fun ω => F ω ^ (-p)) R (hSm.pow_const _) (hFm.pow_const _) hSt hFt hRt hSF hFS
  calc
    _ ≤ (∫⁻ ω, R ω ∂P).toReal := hh
    _ ≤ ((p * Cd) * r ^ e) := by
      have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hRb
      simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (p * Cd) * r ^ e)] using ht

end DOZZ.Proofs
