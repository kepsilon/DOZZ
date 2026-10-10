/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.DualR.StarGSegment
public import DOZZ.ShiftEquations.DualR.ReflectedShiftFull
import DOZZ.Correlations.Analytic.StructureConstantHolomorphic
import DOZZ.ShiftEquations.Rbar.Continuation
import DOZZ.Brownian.Reflection.RtheorAnalytic

/-!
# The crossed second dual seed near `(γ/2, γ/2, Q - γ/2)`

Starting from a good point `p_s = (γ/2 + σ₁, γ/2 + σ₃, 2/γ + σ)` (`σ₃ > σ₁ + σ`) where the second
dual seed holds in its shifted form (`starG_eventually`), the shifted seed continues along the
segment to `P = (ε, γ/2 + η, Q - ε)` with `ε = γ/2 - θ < γ/2`: there every ingredient is
meromorphic, since the shifted structure constant `C(2Q - ε - 2/γ - γ, α, α')` stays in the extended
Seiberg domain. At `P` the reflected shift (`reflectedShift_full`) turns the shifted form back into
`R(Q + θ) C(Q - θ, γ/2 + η, Q - ε)`. This is the identity [KRV, (TKEA)]:
`R(ε) R(2Q - ε - 2/γ) C(ε + 2/γ, γ/2 + η, Q - ε) = L R(γ/2 + η) C(ε, Q - η, Q - ε)`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- A meromorphic function is analytic at some real point of any open interval around a real point
of its strip of meromorphy. -/
theorem exists_analyticAt_near {R : ℂ → ℂ} {z₀ : ℝ} (hR : MeromorphicAt R (z₀ : ℂ)) {a b : ℝ}
    (ha : a < z₀) (hb : z₀ < b) : ∃ z : ℝ, z ∈ Ioo a b ∧ AnalyticAt ℂ R (z : ℂ) := by
  have hev := eventually_analyticAt_affine hR (a := 1) one_ne_zero
  have hI : Ioo (a - z₀) (b - z₀) ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) (by linarith)
  obtain ⟨u, hu1, hu2⟩ := (hev.and (nhdsWithin_le_nhds hI)).exists
  refine ⟨z₀ + u, ⟨by linarith [hu2.1], by linarith [hu2.2]⟩, ?_⟩
  simpa using hu1


section Arith

variable {γ : ℝ}

/-- Extended Seiberg bounds at the start point `(γ/2 + σ₁, γ/2 + σ₃, 2/γ + σ)`. -/
theorem tkea_start_seiberg {σ es as : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hσ₁ : σ ≤ γ / 12) (hσ₂ : σ ≤ (4 / γ - γ) / 16) (hes₁ : γ / 2 + σ / 2 < es)
    (hes₂ : es < γ / 2 + σ) (has₁ : γ / 2 + 3 * σ < as) (has₂ : as < γ / 2 + 4 * σ) :
    ExtendedSeiberg3 γ (2 * Q γ - es - 2 / γ) as (2 / γ + σ) ∧
      ExtendedSeiberg3 γ es (2 * Q γ - as - 2 / γ) (2 / γ + σ) ∧
      ExtendedSeiberg3 γ (2 * Q γ - es - 2 / γ - γ) as (2 / γ + σ) := by
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hγh : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ (by norm_num) hγ]
    exact mul_self_lt_mul_self hγ.le hγ2
  have h42 : 4 / γ = 2 * (2 / γ) := by ring
  -- division-free forms of the hypotheses, with `2 / γ` abstracted, so that `linarith` has no
  -- denominators to cancel
  set k := 2 / γ with hk
  have hQ' : 2 * Q γ = 2 * k + γ := by rw [hQ]; ring
  have hγh' : γ < 2 * k := by linarith only [hγh]
  have hσ₁' : 12 * σ ≤ γ := by linarith only [hσ₁]
  have hσ₂' : 16 * σ ≤ 2 * k - γ := by rw [h42] at hσ₂; linarith only [hσ₂]
  have hes₁' : γ + σ < 2 * es := by linarith only [hes₁]
  have hes₂' : 2 * es < γ + 2 * σ := by linarith only [hes₂]
  have has₁' : γ + 6 * σ < 2 * as := by linarith only [has₁]
  have has₂' : 2 * as < γ + 8 * σ := by linarith only [has₂]
  clear_value k
  clear hQ hγh hσ₁ hσ₂ hes₁ hes₂ has₁ has₂ hk
  refine ⟨?_, ?_, ?_⟩
  · exact extendedSeiberg3_of_lt hγ (by linarith) (by linarith) (by linarith)
      (by rw [h42]; linarith) (by linarith) (by linarith) (by linarith)
  · exact extendedSeiberg3_of_lt hγ (by linarith) (by linarith) (by linarith)
      (by rw [h42]; linarith) (by linarith) (by linarith) (by linarith)
  · exact extendedSeiberg3_of_lt hγ (by linarith) (by linarith) (by linarith)
      (by rw [h42]; linarith) (by linarith) (by linarith) (by linarith)

/-- `Γ`- and shift-coefficient conditions at the start point. -/
theorem tkea_start_gamma {σ es as : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hσ₁ : σ ≤ γ / 12) (hσ₂ : σ ≤ (4 / γ - γ) / 16) (hes₁ : γ / 2 + σ / 2 < es)
    (hes₂ : es < γ / 2 + σ) (has₁ : γ / 2 + 3 * σ < as) (has₂ : as < γ / 2 + 4 * σ) :
    AnalyticAt ℂ Complex.Gamma (sExp γ (2 * Q γ - es - 2 / γ) as (2 / γ + σ) : ℂ) ∧
      AnalyticAt ℂ Complex.Gamma (sExp γ es (2 * Q γ - as - 2 / γ) (2 / γ + σ) : ℂ) ∧
      AnalyticAt ℂ Complex.Gamma (sExp γ (2 * Q γ - es - 2 / γ - γ) as (2 / γ + σ) : ℂ) ∧
      AnalyticAt ℂ Complex.Gamma (dualArg₂ γ (as : ℂ)) ∧
      AnalyticAt ℂ Complex.Gamma (1 - dualArg₃ γ (es : ℂ) (as : ℂ) ((2 / γ + σ : ℝ) : ℂ)) ∧
      AnalyticAt ℂ Complex.Gamma (1 - dualArg₄ γ (es : ℂ) (as : ℂ) ((2 / γ + σ : ℝ) : ℂ)) ∧
      ShiftCoeffGood γ (((2 * Q γ - es - 2 / γ : ℝ) : ℂ) - γ / 2) as ((2 / γ + σ : ℝ) : ℂ) := by
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hγh : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ (by norm_num) hγ]
    exact mul_self_lt_mul_self hγ.le hγ2
  have h42 : 4 / γ = 2 * (2 / γ) := by ring
  have e₃ : -2 / γ ^ 2 - (es - as - (2 / γ + σ)) / γ = (as + σ - es) / γ := by
    field_simp
    ring
  have e₄ : 1 + 2 / γ ^ 2 - (es - as + (2 / γ + σ)) / γ = 1 + (as - es - σ) / γ := by
    field_simp
    ring
  -- division-free forms of the hypotheses, with `2 / γ` abstracted, so that `linarith` has no
  -- denominators to cancel
  set k := 2 / γ with hk
  have hQ' : 2 * Q γ = 2 * k + γ := by rw [hQ]; ring
  have hγh' : γ < 2 * k := by linarith only [hγh]
  have hσ₁' : 12 * σ ≤ γ := by linarith only [hσ₁]
  have hσ₂' : 16 * σ ≤ 2 * k - γ := by rw [h42] at hσ₂; linarith only [hσ₂]
  have hes₁' : γ + σ < 2 * es := by linarith only [hes₁]
  have hes₂' : 2 * es < γ + 2 * σ := by linarith only [hes₂]
  have has₁' : γ + 6 * σ < 2 * as := by linarith only [has₁]
  have has₂' : 2 * as < γ + 8 * σ := by linarith only [has₂]
  clear_value k
  clear hQ hγh hσ₁ hσ₂ hes₁ hes₂ has₁ has₂ hk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine analyticAt_Gamma_ofReal_pos ?_
    unfold sExp
    exact div_pos (by linarith) hγ
  · refine analyticAt_Gamma_ofReal_neg_one_lt ?_ ?_
    · unfold sExp
      rw [lt_div_iff₀ hγ]
      linarith
    · unfold sExp
      exact div_neg_of_neg_of_pos (by linarith) hγ
  · refine analyticAt_Gamma_ofReal_neg_one_lt ?_ ?_
    · unfold sExp
      rw [lt_div_iff₀ hγ]
      linarith
    · unfold sExp
      exact div_neg_of_neg_of_pos (by linarith) hγ
  · rw [dualArg₂_ofReal]
    refine analyticAt_Gamma_ofReal_pos ?_
    have e : 2 + 4 / γ ^ 2 - 2 * as / γ = 4 / γ ^ 2 + 2 * (γ - as) / γ := by
      field_simp
      ring
    rw [e]
    have : 0 < 2 * (γ - as) / γ := div_pos (by linarith) hγ
    positivity
  · rw [one_sub_dualArg₃_ofReal]
    refine analyticAt_Gamma_ofReal_pos ?_
    rw [e₃]
    exact div_pos (by linarith) hγ
  · rw [one_sub_dualArg₄_ofReal]
    refine analyticAt_Gamma_ofReal_pos ?_
    rw [e₄]
    have : 0 < (as - es - σ) / γ := div_pos (by linarith) hγ
    linarith
  · exact shiftCoeffGood_of_lt hγ (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith)

/-- Extended Seiberg bounds at the end point `(γ/2 - θ, γ/2 + η, 2/γ + θ)`. -/
theorem tkea_end_seiberg {θ η : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hθ₁ : 0 < θ) (hθ₂ : θ < γ / 4)
    (hη₁ : 0 < η) (hη₂ : η < γ / 2) (hη₃ : η < 4 / γ - γ) :
    ExtendedSeiberg3 γ (2 * Q γ - (γ / 2 - θ) - 2 / γ - γ) (γ / 2 + η) (2 / γ + θ) ∧
      ExtendedSeiberg3 γ (γ / 2 - θ) (2 * Q γ - (γ / 2 + η) - 2 / γ) (2 / γ + θ) ∧
      ExtendedSeiberg3 γ (2 * Q γ - (2 * Q γ - (γ / 2 - θ) - 2 / γ)) (γ / 2 + η) (2 / γ + θ) := by
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hγh : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ (by norm_num) hγ]
    exact mul_self_lt_mul_self hγ.le hγ2
  have h42 : 4 / γ = 2 * (2 / γ) := by ring
  -- division-free forms of the hypotheses, with `2 / γ` abstracted, so that `linarith` has no
  -- denominators to cancel
  set k := 2 / γ with hk
  have hQ' : 2 * Q γ = 2 * k + γ := by rw [hQ]; ring
  have hγh' : γ < 2 * k := by linarith only [hγh]
  have hθ₂' : 4 * θ < γ := by linarith only [hθ₂]
  have hη₂' : 2 * η < γ := by linarith only [hη₂]
  have hη₃' : η < 2 * k - γ := by rw [h42] at hη₃; exact hη₃
  clear_value k
  clear hQ hγh hθ₂ hη₂ hη₃ hk
  refine ⟨?_, ?_, ?_⟩
  · exact extendedSeiberg3_of_lt hγ (by linarith) (by linarith) (by linarith)
      (by rw [h42]; linarith) (by linarith) (by linarith) (by linarith)
  · exact extendedSeiberg3_of_lt hγ (by linarith) (by linarith) (by linarith)
      (by rw [h42]; linarith) (by linarith) (by linarith) (by linarith)
  · exact extendedSeiberg3_of_lt hγ (by linarith) (by linarith) (by linarith)
      (by rw [h42]; linarith) (by linarith) (by linarith) (by linarith)

/-- `Γ`- and shift-coefficient conditions at the end point. -/
theorem tkea_end_gamma {θ η : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hθ₁ : 0 < θ) (hθ₂ : θ < γ / 4)
    (hη₁ : 0 < η) (hη₂ : η < γ / 2) (hη₃ : η < 4 / γ - γ) :
    AnalyticAt ℂ Complex.Gamma
        (sExp γ (2 * Q γ - (γ / 2 - θ) - 2 / γ - γ) (γ / 2 + η) (2 / γ + θ) : ℂ) ∧
      AnalyticAt ℂ Complex.Gamma
        (sExp γ (γ / 2 - θ) (2 * Q γ - (γ / 2 + η) - 2 / γ) (2 / γ + θ) : ℂ) ∧
      AnalyticAt ℂ Complex.Gamma
        (sExp γ (2 * Q γ - (2 * Q γ - (γ / 2 - θ) - 2 / γ)) (γ / 2 + η) (2 / γ + θ) : ℂ) ∧
      AnalyticAt ℂ Complex.Gamma (dualArg₂ γ ((γ / 2 + η : ℝ) : ℂ)) ∧
      AnalyticAt ℂ Complex.Gamma (1 - dualArg₃ γ ((γ / 2 - θ : ℝ) : ℂ) ((γ / 2 + η : ℝ) : ℂ)
        ((2 / γ + θ : ℝ) : ℂ)) ∧
      AnalyticAt ℂ Complex.Gamma (1 - dualArg₄ γ ((γ / 2 - θ : ℝ) : ℂ) ((γ / 2 + η : ℝ) : ℂ)
        ((2 / γ + θ : ℝ) : ℂ)) ∧
      ShiftCoeffGood γ (((2 * Q γ - (γ / 2 - θ) - 2 / γ : ℝ) : ℂ) - γ / 2)
        ((γ / 2 + η : ℝ) : ℂ) ((2 / γ + θ : ℝ) : ℂ) := by
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hγh : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ (by norm_num) hγ]
    exact mul_self_lt_mul_self hγ.le hγ2
  have h42 : 4 / γ = 2 * (2 / γ) := by ring
  have e₃ : -2 / γ ^ 2 - (γ / 2 - θ - (γ / 2 + η) - (2 / γ + θ)) / γ = (2 * θ + η) / γ := by
    field_simp
    ring
  have e₄ : 1 + 2 / γ ^ 2 - (γ / 2 - θ - (γ / 2 + η) + (2 / γ + θ)) / γ = 1 + η / γ := by
    field_simp
    ring
  -- division-free forms of the hypotheses, with `2 / γ` abstracted, so that `linarith` has no
  -- denominators to cancel
  set k := 2 / γ with hk
  have hQ' : 2 * Q γ = 2 * k + γ := by rw [hQ]; ring
  have hγh' : γ < 2 * k := by linarith only [hγh]
  have hθ₂' : 4 * θ < γ := by linarith only [hθ₂]
  have hη₂' : 2 * η < γ := by linarith only [hη₂]
  have hη₃' : η < 2 * k - γ := by rw [h42] at hη₃; exact hη₃
  clear_value k
  clear hQ hγh hθ₂ hη₂ hη₃ hk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine analyticAt_Gamma_ofReal_neg_one_lt ?_ ?_
    · unfold sExp
      rw [lt_div_iff₀ hγ]
      linarith
    · unfold sExp
      exact div_neg_of_neg_of_pos (by linarith) hγ
  · refine analyticAt_Gamma_ofReal_neg_one_lt ?_ ?_
    · unfold sExp
      rw [lt_div_iff₀ hγ]
      linarith
    · unfold sExp
      exact div_neg_of_neg_of_pos (by linarith) hγ
  · refine analyticAt_Gamma_ofReal_pos ?_
    unfold sExp
    exact div_pos (by linarith) hγ
  · rw [dualArg₂_ofReal]
    refine analyticAt_Gamma_ofReal_pos ?_
    have e : 2 + 4 / γ ^ 2 - 2 * (γ / 2 + η) / γ = 4 / γ ^ 2 + 2 * (γ / 2 - η) / γ := by
      field_simp
      ring
    rw [e]
    have : 0 < 2 * (γ / 2 - η) / γ := div_pos (by linarith) hγ
    positivity
  · rw [one_sub_dualArg₃_ofReal]
    refine analyticAt_Gamma_ofReal_pos ?_
    rw [e₃]
    exact div_pos (by linarith) hγ
  · rw [one_sub_dualArg₄_ofReal]
    refine analyticAt_Gamma_ofReal_pos ?_
    rw [e₄]
    have : 0 < η / γ := div_pos hη₁ hγ
    linarith
  · exact shiftCoeffGood_of_lt hγ (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith)

end Arith

/-- **A good start point**: real `es` and `as` in the prescribed windows where `R` is analytic and
`l(2(es - Q)/γ)` is analytic. -/
theorem exists_tkea_start {γ σ : ℝ} (hγ : 0 < γ) (hσ₀ : 0 < σ) {hR : ℝ} (hhR : 0 < hR)
    {R : ℂ → ℂ} (hRm : MeromorphicOn R (horizontalStrip hR)) :
    ∃ es as : ℝ, es ∈ Ioo (γ / 2 + σ / 2) (γ / 2 + σ) ∧
      as ∈ Ioo (γ / 2 + 3 * σ) (γ / 2 + 4 * σ) ∧ AnalyticAt ℂ R (es : ℂ) ∧
      AnalyticAt ℂ R (as : ℂ) ∧ AnalyticAt ℂ Complex.Gamma (dualArg₁ γ (es : ℂ)) := by
  obtain ⟨e₁, he₁, hRe₁, hge₁⟩ : ∃ e₁ : ℝ, e₁ ∈ Ioo (γ / 2 + σ / 2) (γ / 2 + σ) ∧
      AnalyticAt ℂ R (e₁ : ℂ) ∧ AnalyticAt ℂ Complex.Gamma (dualArg₁ γ (e₁ : ℂ)) := by
    set z₀ : ℝ := γ / 2 + 3 * σ / 4 with hz₀
    have hm1 : MeromorphicAt R (z₀ : ℂ) := hRm _ (ofReal_mem_horizontalStrip hhR z₀)
    have hm2 : MeromorphicAt Complex.Gamma (dualArg₁ γ (z₀ : ℂ)) := Meromorphic.Gamma _
    have ev1 := eventually_analyticAt_affine hm1 (a := 1) one_ne_zero
    have ev2 := eventually_analyticAt_affine hm2 (a := 2 / (γ : ℂ))
      (div_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr hγ.ne'))
    have hI : Ioo (-(σ / 4)) (σ / 4) ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) (by linarith)
    obtain ⟨u, ⟨hu1, hu2⟩, hu3⟩ := ((ev1.and ev2).and (nhdsWithin_le_nhds hI)).exists
    refine ⟨z₀ + u, ⟨by rw [hz₀]; linarith [hu3.1], by rw [hz₀]; linarith [hu3.2]⟩, ?_, ?_⟩
    · simpa using hu1
    · convert hu2 using 1
      unfold dualArg₁
      push_cast
      ring
  obtain ⟨a₁, ha₁, hRa₁⟩ : ∃ a₁ : ℝ, a₁ ∈ Ioo (γ / 2 + 3 * σ) (γ / 2 + 4 * σ) ∧
      AnalyticAt ℂ R (a₁ : ℂ) :=
    exists_analyticAt_near (z₀ := γ / 2 + 7 * σ / 2)
      (hRm _ (ofReal_mem_horizontalStrip hhR _)) (by linarith) (by linarith)
  exact ⟨e₁, a₁, he₁, ha₁, hRe₁, hRa₁, hge₁⟩

/-- **The crossed second dual seed (`TKEA`).** For `ε = γ/2 - θ` slightly below `γ/2` and
`α = γ/2 + η` with small `η > 0`, at points where `R` is analytic and the `l`-factor
`l(2(ε - Q)/γ)` is analytic:
`R(ε) R(Q + θ) C(Q - θ, γ/2 + η, 2/γ + θ) = L(ε, γ/2 + η, 2/γ + θ) R(γ/2 + η) C(ε, Q - η, 2/γ + θ)`.
-/
theorem tkea {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hSeed : ∀ α ε α' : ℝ, α < Q γ → ε < Q γ → α' < Q γ → 2 * Q γ + 2 / γ < α + ε + α' →
      ∃ Bε Bα : Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧ IsReflectionData P γ ε Bε Z ∧
          IsReflectionData P γ α Bα Z ∧
          reflectionR P γ μ ε Bε Z * structureConstant P M γ μ (2 * Q γ - ε - 2 / γ) α α' =
            dualCrossingL γ ε α α' * reflectionR P γ μ α Bα Z *
              structureConstant P M γ μ ε (2 * Q γ - α - 2 / γ) α')
    (hShiftGluing : ∀ η : ℝ, (0 < η ∧ Q γ - 2 * η > γ) → ∀ α₂ α₃ : ℝ,
      (Q γ - η < α₂ ∧ α₂ < Q γ) → (Q γ - η < α₃ ∧ α₃ < Q γ) →
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α : ℝ, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ C R : ℂ → ℂ,
              MeromorphicOn C {z | |z.im| < h} ∧
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, 2 * η < α → α < Q γ →
                C (α : ℂ) = (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) = (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              (∀ᶠ z in codiscrete ℂ, C z = R z * C (2 * Q γ - z)) ∧
              (∀ᶠ z in codiscrete ℂ,
                R (z + γ / 2) * C (2 * Q γ - z - γ / 2) =
                  -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) *
                    C (z - γ / 2)))
    {hR : ℝ} (hhR : 0 < hR) {R : ℂ → ℂ} (hRm : MeromorphicOn R (horizontalStrip hR))
    {BR : ℝ → Ω → BrownianPath × BrownianPath} {ZR : Ω → Measure ℝ}
    (hBR : ∀ α : ℝ, γ / 2 < α → α < Q γ → IsReflectionData P γ α (BR α) ZR)
    (hRv : ∀ α : ℝ, γ / 2 < α → α < Q γ → R (α : ℂ) = (reflectionR P γ μ α (BR α) ZR : ℂ))
    {θ η : ℝ} (hθ₁ : 0 < θ) (hθ₂ : θ < γ / 4) (hη₁ : 0 < η) (hη₂ : η < γ / 2)
    (hη₃ : η < 4 / γ - γ)
    (hRe : AnalyticAt ℂ R ((γ / 2 - θ : ℝ) : ℂ)) (hRx : AnalyticAt ℂ R ((Q γ + θ : ℝ) : ℂ))
    (hRa : AnalyticAt ℂ R ((γ / 2 + η : ℝ) : ℂ))
    (hg₁ : AnalyticAt ℂ Complex.Gamma (dualArg₁ γ ((γ / 2 - θ : ℝ) : ℂ))) :
    R ((γ / 2 - θ : ℝ) : ℂ) * R ((Q γ + θ : ℝ) : ℂ) *
        (structureConstant P M γ μ (Q γ - θ) (γ / 2 + η) (2 / γ + θ) : ℂ) =
      dualLC γ ((γ / 2 - θ : ℝ) : ℂ) ((γ / 2 + η : ℝ) : ℂ) ((2 / γ + θ : ℝ) : ℂ) *
        R ((γ / 2 + η : ℝ) : ℂ) *
          (structureConstant P M γ μ (γ / 2 - θ) (Q γ - η) (2 / γ + θ) : ℂ) := by
  have hγh : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ (by norm_num) hγ]
    exact mul_self_lt_mul_self hγ.le hγ2
  set σ : ℝ := min (γ / 12) ((4 / γ - γ) / 16) with hσ
  have hσ₀ : 0 < σ := lt_min (by linarith) (by linarith)
  obtain ⟨es, as, hes, has, hRes, hRas, hgS1⟩ := exists_tkea_start hγ hσ₀ hhR hRm
  obtain ⟨hS1, hS2, hS3⟩ := tkea_start_seiberg hγ hγ2 (min_le_left _ _) (min_le_right _ _)
    hes.1 hes.2 has.1 has.2
  obtain ⟨hsS1, hsS2, hsS3, hgS2, hgS3, hgS4, hAS⟩ := tkea_start_gamma hγ hγ2
    (min_le_left _ _) (min_le_right _ _) hes.1 hes.2 has.1 has.2
  obtain ⟨hP1, hP2, hP3⟩ := tkea_end_seiberg hγ hγ2 hθ₁ hθ₂ hη₁ hη₂ hη₃
  obtain ⟨hsP1, hsP2, hsP3, hgP2, hgP3, hgP4, hAP⟩ :=
    tkea_end_gamma hγ hγ2 hθ₁ hθ₂ hη₁ hη₂ hη₃
  have hxf : 2 * Q γ - (γ / 2 - θ) - 2 / γ = Q γ + θ := by
    rw [show Q γ = 2 / γ + γ / 2 from rfl]
    ring
  have key := starG_segment P X M hγ hγ2 hμ hX hM hSeed hShiftGluing hhR hRm hBR hRv hS1 hS2 hS3 hRes
    hRas hsS1 hsS2 hsS3 hgS1 hgS2 (by exact_mod_cast hgS3) (by exact_mod_cast hgS4)
    (by exact_mod_cast hAS) hP1 hP2 hRe hRa hsP1 hsP2 hg₁ hgP2 hgP3 hgP4 hAP
  have hrefl := reflectedShift_full P X M hγ hγ2 hμ hX hM hShiftGluing hhR hRm hBR hRv
    (x := 2 * Q γ - (γ / 2 - θ) - 2 / γ) hP3 hP1 (by rw [hxf]; exact hRx) hsP3 hsP1 hAP
  rw [← hrefl] at key
  rw [show 2 * Q γ - (2 * Q γ - (γ / 2 - θ) - 2 / γ) = Q γ - θ by
      rw [show Q γ = 2 / γ + γ / 2 from rfl]; ring,
    show 2 * Q γ - (γ / 2 + η) - 2 / γ = Q γ - η by rw [show Q γ = 2 / γ + γ / 2 from rfl]; ring,
    hxf] at key
  rw [← key]
  ring

end DOZZ.Proofs

end
