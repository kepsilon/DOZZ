/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.WilliamsIncrementSqueeze
public import DOZZ.FourPoint.Reflected.InverseIncrementIntegrable
import Mathlib.Tactic
/-! Integrating the signed Williams sandwich without a moment of the maximum. -/
@[expose] public section
open MeasureTheory
namespace DOZZ.Proofs

/-- The actual last-cut sandwich integrates with precisely the retained inverse moment,
first-order source weight and full reflection first moment. -/
theorem reflected_williams_expectation_squeeze
    {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (R : Measure Λ) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (p γ H : ℝ) (hp : 0 < p) (hγ : 0 ≤ γ)
    (A b : Ω → ℝ) (m J K j : Λ → ℝ)
    (hA : ∀ᵐ ω ∂P, 0 < A ω) (hb : ∀ᵐ ω ∂P, 0 ≤ b ω)
    (hcut : ∀ᵐ v ∂R, 0 ≤ j v ∧ j v ≤ J v ∧ 0 ≤ K v ∧ K v ≤ J v ∧ (H < m v → K v ≤ j v))
    (hAm : AEMeasurable A P) (hbm : AEMeasurable b P)
    (hm : AEMeasurable m R) (hJm : AEMeasurable J R)
    (hKm : AEMeasurable K R) (hjm : AEMeasurable j R)
    (hInv : Integrable (fun ω => (A ω)^(-p)) P)
    (hF : Integrable (fun ω => b ω*(A ω)^(-p-1)) P) (hJ : Integrable J R) :
    let D := fun S : Λ → ℝ => fun v : Ω × Λ =>
      (A v.1+b v.1*Real.exp (γ*m v.2)*S v.2)^(-p)-(A v.1)^(-p)
    Integrable (D j) (P.prod R) ∧
    (∫ v, D J v ∂P.prod R) ≤ (∫ v, D j v ∂P.prod R) ∧
    (∫ v, D j v ∂P.prod R) ≤ (∫ v, D K v ∂P.prod R)+
      p*Real.exp (γ*H)*(∫ ω, b ω*(A ω)^(-p-1) ∂P)*(∫ v, J v ∂R) := by
  let D := fun S : Λ → ℝ => fun v : Ω × Λ =>
    (A v.1+b v.1*Real.exp (γ*m v.2)*S v.2)^(-p)-(A v.1)^(-p)
  have hAp := (measurePreserving_fst (μ := P) (ν := R)).quasiMeasurePreserving.ae hA
  have hbp := (measurePreserving_fst (μ := P) (ν := R)).quasiMeasurePreserving.ae hb
  have hcp := (measurePreserving_snd (μ := P) (ν := R)).quasiMeasurePreserving.ae hcut
  have hApm := hAm.comp_quasiMeasurePreserving
    (measurePreserving_fst (μ := P) (ν := R)).quasiMeasurePreserving
  have hbpm := hbm.comp_quasiMeasurePreserving
    (measurePreserving_fst (μ := P) (ν := R)).quasiMeasurePreserving
  have hemp := ((hm.const_mul γ).exp).comp_quasiMeasurePreserving
    (measurePreserving_snd (μ := P) (ν := R)).quasiMeasurePreserving
  have hInvp : Integrable (fun v : Ω × Λ => (A v.1)^(-p)) (P.prod R) := by
    simpa only [mul_one] using hInv.mul_prod (integrable_const (1 : ℝ))
  have hi (S : Λ → ℝ) (hS : ∀ᵐ v ∂R, 0 ≤ S v) (hSm : AEMeasurable S R) :
      Integrable (D S) (P.prod R) := by
    have hSp := (measurePreserving_snd (μ := P) (ν := R)).quasiMeasurePreserving.ae hS
    have hT : ∀ᵐ v : Ω × Λ ∂P.prod R, 0 ≤ b v.1*Real.exp (γ*m v.2)*S v.2 := by
      filter_upwards [hbp,hSp] with v hv hSv
      exact mul_nonneg (mul_nonneg hv (Real.exp_pos _).le) hSv
    exact reflected_inverse_increment_integrable (P.prod R) p hp _ _ hAp hT hApm
      ((hbpm.mul hemp).mul (hSm.comp_quasiMeasurePreserving
        (measurePreserving_snd (μ := P) (ν := R)).quasiMeasurePreserving)) hInvp
  have hiJ := hi J (hcut.mono fun _ h => h.1.trans h.2.1) hJm
  have hiK := hi K (hcut.mono fun _ h => h.2.2.1) hKm
  have hij := hi j (hcut.mono fun _ h => h.1) hjm
  let F := fun ω => b ω*(A ω)^(-p-1)
  let E := fun v : Ω × Λ => (p*Real.exp (γ*H))*(F v.1*J v.2)
  have hiE : Integrable E (P.prod R) := (hF.mul_prod hJ).const_mul _
  have hbnd : ∀ᵐ v : Ω × Λ ∂P.prod R,
      D J v ≤ D j v ∧ D j v ≤ D K v+E v := by
    filter_upwards [hAp,hbp,hcp] with v hAv hbv hcv
    have hs := reflected_williams_increment_squeeze p (A v.1) (b v.1) γ H (m v.2)
      (J v.2) (K v.2) (j v.2) hp hAv hbv hγ hcv.1 hcv.2.1 hcv.2.2.1
        hcv.2.2.2.1 hcv.2.2.2.2
    refine ⟨hs.1, ?_⟩
    convert hs.2 using 1
    dsimp only [D,E,F]
    ring
  refine ⟨hij,integral_mono_ae hiJ hij (hbnd.mono fun _ h => h.1), ?_⟩
  have hh := integral_mono_ae hij (hiK.add hiE) (hbnd.mono fun _ h => h.2)
  simp only [Pi.add_apply] at hh
  rw [integral_add hiK hiE] at hh
  have he : (∫ v, E v ∂P.prod R) =
      p*Real.exp (γ*H)*(∫ ω, F ω ∂P)*(∫ v, J v ∂R) := by
    rw [show E = (fun v : Ω × Λ => (p*Real.exp (γ*H))*(F v.1*J v.2)) from rfl,
      integral_const_mul,integral_prod_mul]
    ring
  rw [he] at hh
  exact hh

end DOZZ.Proofs
