/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.IncrementIntegrability
import Mathlib.Tactic
/-! Integrated signed maximum sandwich with its explicit first-order error. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
namespace DOZZ.Proofs

/-- Integrating the Williams cut sandwich preserves its signs. The bounded maximum costs
only the already controlled first-order retained moment times the full reflection moment. -/
theorem dual_williams_increment_expectation_sandwich
    {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (R : Measure Λ) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (p γ c : ℝ) (hp : 0 < p) (hγ : 0 ≤ γ)
    (A b : Ω → ℝ) (m J Jc j : Λ → ℝ)
    (hA : ∀ᵐ ω ∂P, 0 < A ω) (hb : ∀ᵐ ω ∂P, 0 ≤ b ω)
    (hcut : ∀ᵐ v ∂R, 0 ≤ j v ∧ j v ≤ J v ∧ 0 ≤ Jc v ∧ Jc v ≤ J v ∧
      (c ≤ m v → Jc v ≤ j v))
    (hAm : AEMeasurable A P) (hbm : AEMeasurable b P)
    (hmm : AEMeasurable m R) (hJm : AEMeasurable J R)
    (hJcm : AEMeasurable Jc R) (hjm : AEMeasurable j R)
    (hInv : Integrable (fun ω => (A ω)^(-p)) P)
    (hF : Integrable (fun ω => b ω*(A ω)^(-p-1)) P) (hJ : Integrable J R) :
    let E := fun (S : Λ → ℝ) (v : Ω × Λ) =>
      (A v.1+b v.1*(Real.exp (γ*m v.2)*S v.2))^(-p)-(A v.1)^(-p)
    (∫ v, E J v ∂P.prod R) ≤ (∫ v, E j v ∂P.prod R) ∧
    (∫ v, E j v ∂P.prod R) ≤ (∫ v, E Jc v ∂P.prod R) +
      p*Real.exp (γ*c)*(∫ ω, b ω*(A ω)^(-p-1) ∂P)*(∫ v, J v ∂R) := by
  classical
  let E := fun (S : Λ → ℝ) (v : Ω × Λ) =>
    (A v.1+b v.1*(Real.exp (γ*m v.2)*S v.2))^(-p)-(A v.1)^(-p)
  have hInt (S : Λ → ℝ) (hSm : AEMeasurable S R) (hS : ∀ᵐ v ∂R, 0 ≤ S v) :
      Integrable (E S) (P.prod R) := by
    let H : Λ → ℝ := fun v => Real.exp (γ*m v)*S v
    have hHm : AEMeasurable H R := by
      convert (hmm.const_mul γ).exp.mul hSm using 1
    have hH : ∀ᵐ v ∂R, 0 ≤ H v :=
      hS.mono fun v hv => mul_nonneg (Real.exp_pos _).le hv
    exact dual_negative_increment_integrable P R p hp.le A b H hA hb hH hAm hbm hHm hInv
  have hJi := hInt J hJm (hcut.mono fun _ hv => hv.1.trans hv.2.1)
  have hji := hInt j hjm (hcut.mono fun _ hv => hv.1)
  have hJci := hInt Jc hJcm (hcut.mono fun _ hv => hv.2.2.1)
  let G := fun v : Ω × Λ =>
    (p*Real.exp (γ*c))*((b v.1*(A v.1)^(-p-1))*J v.2)
  have hGi : Integrable G (P.prod R) := (hF.mul_prod hJ).const_mul _
  have hbound : ∀ᵐ v : Ω × Λ ∂P.prod R,
      E J v ≤ E j v ∧ E j v ≤ E Jc v + G v := by
    filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae hA,
      measurePreserving_fst.quasiMeasurePreserving.ae hb,
      measurePreserving_snd.quasiMeasurePreserving.ae hcut] with v hAv hbv hv
    have hs := dual_negative_increment_sandwich p (A v.1) (b v.1) γ c (m v.2)
      (J v.2) (Jc v.2) (j v.2) hp hAv hbv hγ hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2
    have hg : (if m v.2 < c then
        p*(A v.1)^(-p-1)*b v.1*Real.exp (γ*c)*J v.2 else 0) ≤ G v := by
      dsimp only [G]
      split_ifs
      · ring_nf
        exact le_rfl
      · have hJv : 0 ≤ J v.2 := hv.1.trans hv.2.1
        positivity
    dsimp only [E]
    simp only [mul_assoc] at hs hg
    exact ⟨hs.1, hs.2.trans (add_le_add le_rfl hg)⟩
  have he : (∫ v, G v ∂P.prod R) =
      p*Real.exp (γ*c)*(∫ ω, b ω*(A ω)^(-p-1) ∂P)*(∫ v, J v ∂R) := by
    dsimp only [G]
    rw [integral_const_mul]
    rw [integral_prod_mul (fun ω => b ω*(A ω)^(-p-1)) J]
    ring
  refine ⟨integral_mono_ae hJi hji (hbound.mono fun _ hv => hv.1), ?_⟩
  have hu := integral_mono_ae hji (hJci.add hGi) (hbound.mono fun _ hv => hv.2)
  change (∫ v, E j v ∂P.prod R) ≤ (∫ v, E Jc v + G v ∂P.prod R) at hu
  rw [integral_add hJci hGi, he] at hu
  exact hu

end DOZZ.Proofs
