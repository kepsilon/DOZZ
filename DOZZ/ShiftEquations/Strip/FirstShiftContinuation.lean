/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Strip.FirstShiftSeed
public import DOZZ.ShiftEquations.Strip.Representative
public import DOZZ.ShiftEquations.Shift.ShiftGluing
import DOZZ.ShiftEquations.Quotient.Divisors
import DOZZ.ShiftEquations.Rbar.Multiplier
import DOZZ.Brownian.Reflection.RtheorAnalytic
import Mathlib.Tactic

/-! # Continuation of the first structure shift

Reflection of the charge variable converts the forward recurrence to the existing translated
rectangle continuation theorem. Cutting off outside a thinner strip supplies the literal
whole-plane codiscrete equation without changing any physical real value.
-/

@[expose] public section
open MeasureTheory Filter Topology Set
namespace DOZZ.Proofs

/-- Affine reflection transports punctured neighborhoods. -/
theorem firstStrip_tendsto_reflection (z b : ℂ) :
    Tendsto (fun w : ℂ => b - w) (𝓝[≠] z) (𝓝[≠] (b - z)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((continuous_const.sub continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with w hw
  simpa only [mem_compl_iff, mem_singleton_iff, Pi.sub_apply, id_eq, sub_right_inj] using hw

/-- The continuation from the G7 seed, retaining the supplied-space physical values. -/
theorem firstStrip_continuation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ η α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hη : 0 < η ∧ Q γ - 2 * η > γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (h₂ : Q γ - η < α₂ ∧ α₂ < Q γ)
    (h₃ : Q γ - η < α₃ ∧ α₃ < Q γ) :
    ∃ h : ℝ, 0 < h ∧ ∃ C : ℂ → ℂ,
      MeromorphicOn C (horizontalStrip h) ∧
      (∀ a : ℝ, 2 * η < a → a < Q γ →
        C (a : ℂ) = (structureConstant P M γ μ a α₂ α₃ : ℂ)) ∧
      ∀ᶠ z in codiscrete ℂ,
        C (z + γ / 2) = -(1 / (Real.pi * μ)) *
          shiftCoeffA γ (γ / 2) z α₂ α₃ * C (z - γ / 2) := by
  obtain ⟨V, hV, hVI, g, hg, hgeq⟩ := firstStrip_holomorphic_physical
    P X M γ μ η α₂ α₃ hγ hγ2 hμ h₂ h₃ hX hM
  let W := (fun z : ℂ => -z) ⁻¹' V
  let f : ℂ → ℂ := fun z => g (-z)
  let A : ℂ → ℂ := fun z => -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z α₂ α₃
  let m : ℂ → ℂ := fun z => A (γ / 2 - z)
  have hAm : MeromorphicOn A univ :=
    MeromorphicOn.const _ |>.mul (meromorphicOn_shiftCoeffA γ (γ / 2) α₂ α₃)
  have hmm : MeromorphicOn m univ := by
    intro z _
    exact (hAm _ (mem_univ _)).comp_analyticAt (analyticAt_const.sub analyticAt_id)
  have hπμ : (-(1 / (Real.pi * μ)) : ℂ) ≠ 0 := by
    exact neg_ne_zero.mpr (one_div_ne_zero (mul_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (Complex.ofReal_ne_zero.mpr hμ.ne')))
  have hconst : lFun (-((γ : ℂ) / 2) ^ 2) ≠ 0 := by
    have he : -((γ : ℂ) / 2) ^ 2 = ((-(γ ^ 2) / 4 : ℝ) : ℂ) := by push_cast; ring
    rw [he, lFun_ofReal_eq_lR, Complex.ofReal_ne_zero]
    exact lR_ne_zero_of_mem_neg (by nlinarith) (by nlinarith)
  have hAn : ∀ᶠ z in codiscrete ℂ, A z ≠ 0 := by
    filter_upwards [eventually_shiftCoeffA_ne_zero γ (α₂ : ℂ) (α₃ : ℂ)
      (by exact_mod_cast (show γ / 2 ≠ 0 by positivity)) hconst] with z hz
    exact mul_ne_zero hπμ hz
  have hmn : ∀ z : ℂ, ∀ᶠ w in 𝓝[≠] z, m w ≠ 0 := by
    intro z
    exact (firstStrip_tendsto_reflection z (γ / 2)).eventually
      (eventually_nhdsNE_of_eventually_codiscrete hAn (γ / 2 - z))
  have hm0 : ∃ z₀ : ℂ, AnalyticAt ℂ m z₀ ∧ m z₀ ≠ 0 := by
    exact ((hmm 0 (mem_univ 0)).eventually_analyticAt.and (hmn 0)).exists
  have hW : IsOpen W := hV.preimage continuous_neg
  have hWI : ∀ x : ℝ, -Q γ < x → x < -(2 * η) → (x : ℂ) ∈ W := by
    intro x h1 h2
    change -(x : ℂ) ∈ V
    rw [← Complex.ofReal_neg]
    exact hVI (-x) (by linarith) (by linarith)
  have hf : DifferentiableOn ℂ f W := hg.comp differentiable_neg.differentiableOn
    (fun z hz => hz)
  have hrel : ∀ x : ℝ, γ / 2 - 2 / γ < x → x < -(2 * η) →
      f ((x : ℂ) - γ) = m x * f x := by
    intro x h1 h2
    have hseed := firstStrip_shift_seed P X M γ μ η α₂ α₃ hγ hγ2 hμ hη
      hX hM h₂ h₃ (γ / 2 - x) (by linarith) (by linarith)
    dsimp only [f, m, A]
    have e1 : -((x : ℂ) - γ) = ((γ / 2 - x + γ / 2 : ℝ) : ℂ) := by push_cast; ring
    have e2 : -(x : ℂ) = ((γ / 2 - x - γ / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2, hgeq _ (by linarith) (by unfold Q at *; linarith),
      hgeq _ (by linarith) (by unfold Q at *; linarith)]
    convert hseed using 1
    push_cast
    ring
  obtain ⟨H, hH, G, hGm, hGf, hGrel⟩ := exists_meromorphicOn_strip_of_shift
    (c := γ) (a := -Q γ) (b := -(2 * η))
    (d₁ := γ / 2 - 2 / γ) (d₂ := -(2 * η)) hγ (by linarith [hη.2])
    (by unfold Q; linarith) (by unfold Q at *; linarith [hη.2]) le_rfl
    hW hWI hf hmm hm0 hrel
  let F : ℂ → ℂ := fun z => G (-z)
  have hFm : MeromorphicOn F (horizontalStrip H) := by
    intro z hz
    have hz' : -z ∈ horizontalStrip H := by simpa [horizontalStrip] using hz
    exact (hGm _ hz').comp_analyticAt analyticAt_id.neg
  have hFv : ∀ a : ℝ, 2 * η < a → a < Q γ →
      F a = (structureConstant P M γ μ a α₂ α₃ : ℂ) := by
    intro a h1 h2
    dsimp only [F]
    rw [← Complex.ofReal_neg, hGf (-a) (by linarith) (by linarith)]
    simpa only [f, Complex.ofReal_neg, neg_neg] using hgeq a h1 h2
  have hshift : ∀ᶠ z in codiscreteWithin (horizontalStrip H),
      F (z + γ / 2) = A z * F (z - γ / 2) := by
    apply eventually_codiscreteWithin_iff_forall_eventually_nhdsNE.mpr
    intro z hz
    have hz' : (γ : ℂ) / 2 - z ∈ horizontalStrip H := by
      simpa [horizontalStrip, Complex.sub_im, Complex.div_ofNat_im, abs_neg] using hz
    have ht := (firstStrip_tendsto_reflection z (γ / 2)).eventually
      (hGrel _ hz')
    filter_upwards [ht] with w hw _
    dsimp only [F, m] at hw ⊢
    have e1 : γ / 2 - w - (γ : ℂ) = -(w + γ / 2) := by ring
    have e2 : (γ : ℂ) / 2 - w = -(w - γ / 2) := by ring
    have e3 : (γ : ℂ) / 2 - (γ / 2 - w) = w := by ring
    rw [e1, e3, e2] at hw
    exact hw
  obtain ⟨C, hCm, hCF, hCs⟩ := exists_wholePlane_strip_representative
    F A (γ / 2) H (H / 2) (by linarith) hFm (by simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hshift)
  refine ⟨H / 2, half_pos hH, C, hCm, ?_, ?_⟩
  · intro a h1 h2
    rw [hCF (by simpa [horizontalStrip] using half_pos hH)]
    exact hFv a h1 h2
  · simpa only [A, Complex.ofReal_div, Complex.ofReal_ofNat] using hCs

end DOZZ.Proofs
