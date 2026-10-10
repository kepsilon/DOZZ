/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.KahaneConvexAffineApproximation
public import DOZZ.GMC.KahaneFiniteAffineMax

/-! Closure of affine-maximum comparison under arbitrary integrable convex tests. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The maximum of the first `n+1` supporting affine functions. -/
noncomputable def initialAffineMax (a b : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  affineMax (fun i : Fin (n + 1) => a i.val) (fun i : Fin (n + 1) => b i.val) x

theorem initialAffineMax_mono (a b : ℕ → ℝ) (x : ℝ) :
    Monotone (fun n => initialAffineMax a b n x) := by
  classical
  intro n m hnm
  unfold initialAffineMax affineMax
  refine Finset.sup'_le Finset.univ_nonempty _ ?_
  intro i hi
  let j : Fin (m + 1) := ⟨i.val, by omega⟩
  exact affineMax_le (fun i : Fin (m + 1) => a i.val)
    (fun i : Fin (m + 1) => b i.val) x j

theorem initialAffineMax_zero_le (a b : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    a 0 * x + b 0 ≤ initialAffineMax a b n x :=
  affineMax_le (fun i : Fin (n + 1) => a i.val)
    (fun i : Fin (n + 1) => b i.val) x 0

theorem initialAffineMax_tendsto
    (a b : ℕ → ℝ) (x z : ℝ) (hle : ∀ n, a n * x + b n ≤ z)
    (hsup : (⨆ n, a n * x + b n) = z) :
    Tendsto (fun n => initialAffineMax a b n x) atTop (𝓝 z) := by
  classical
  have hHle (n : ℕ) : initialAffineMax a b n x ≤ z := by
    unfold initialAffineMax affineMax
    exact Finset.sup'_le Finset.univ_nonempty _ (fun i _ => hle i.val)
  have hbdd : BddAbove (range (fun n => initialAffineMax a b n x)) :=
    ⟨z, fun y ⟨n, hn⟩ => hn ▸ hHle n⟩
  have hHeq : (⨆ n, initialAffineMax a b n x) = z := by
    apply le_antisymm (ciSup_le hHle)
    rw [← hsup]
    apply ciSup_le
    intro n
    have hn : a n * x + b n ≤ initialAffineMax a b n x :=
      affineMax_le (fun i : Fin (n + 1) => a i.val)
        (fun i : Fin (n + 1) => b i.val) x ⟨n, by omega⟩
    exact hn.trans (le_ciSup hbdd n)
  simpa only [hHeq] using tendsto_atTop_ciSup (initialAffineMax_mono a b x) hbdd

/-- On positive integrable masses of equal mean, affine-maximum order implies comparison and
integrability for every convex test whose expectation on the larger side is integrable. -/
theorem convex_comparison_of_affine_max_order
    {ΩX ΩY : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    (PX : Measure ΩX) (PY : Measure ΩY) [IsProbabilityMeasure PX] [IsProbabilityMeasure PY]
    (MX : ΩX → ℝ) (MY : ΩY → ℝ) (hMX : Integrable MX PX) (hMY : Integrable MY PY)
    (hMXpos : ∀ᵐ ω ∂PX, 0 < MX ω) (hMYpos : ∀ᵐ ω ∂PY, 0 < MY ω)
    (hmean : (∫ ω, MX ω ∂PX) = ∫ ω, MY ω ∂PY)
    (horder : ∀ (n : ℕ) (a b : Fin (n + 1) → ℝ),
      (∫ ω, affineMax a b (MX ω) ∂PX) ≤ ∫ ω, affineMax a b (MY ω) ∂PY)
    (F : ℝ → ℝ) (hF : Measurable F) (hconvex : ConvexOn ℝ (Ici 0) F)
    (hIY : Integrable (fun ω => F (MY ω)) PY) :
    Integrable (fun ω => F (MX ω)) PX ∧
      (∫ ω, F (MX ω) ∂PX) ≤ ∫ ω, F (MY ω) ∂PY := by
  classical
  obtain ⟨a, b, hle, hsup⟩ := convex_positive_countable_affine_minorants F hconvex
  let LX : ΩX → ℝ := fun ω => a 0 * MX ω + b 0
  let LY : ΩY → ℝ := fun ω => a 0 * MY ω + b 0
  have hLX : Integrable LX PX := (hMX.const_mul _).add (integrable_const _)
  have hLY : Integrable LY PY := (hMY.const_mul _).add (integrable_const _)
  have hLeq : (∫ ω, LX ω ∂PX) = ∫ ω, LY ω ∂PY := by
    dsimp [LX, LY]
    rw [integral_add (hMX.const_mul _) (integrable_const _),
      integral_add (hMY.const_mul _) (integrable_const _), integral_const_mul,
      integral_const_mul, hmean]
    simp
  let GX : ℕ → ΩX → ℝ := fun n ω => initialAffineMax a b n (MX ω) - LX ω
  let GY : ℕ → ΩY → ℝ := fun n ω => initialAffineMax a b n (MY ω) - LY ω
  let GXlim : ΩX → ℝ := fun ω => F (MX ω) - LX ω
  let GYlim : ΩY → ℝ := fun ω => F (MY ω) - LY ω
  have hGXint (n : ℕ) : Integrable (GX n) PX :=
    (affineMax_comp_integrable PX MX hMX (fun i : Fin (n + 1) => a i.val)
      (fun i : Fin (n + 1) => b i.val)).sub hLX
  have hGYint (n : ℕ) : Integrable (GY n) PY :=
    (affineMax_comp_integrable PY MY hMY (fun i : Fin (n + 1) => a i.val)
      (fun i : Fin (n + 1) => b i.val)).sub hLY
  have hGXnonneg (n : ℕ) (ω : ΩX) : 0 ≤ GX n ω :=
    sub_nonneg.mpr (initialAffineMax_zero_le a b n (MX ω))
  have hGYnonneg (n : ℕ) (ω : ΩY) : 0 ≤ GY n ω :=
    sub_nonneg.mpr (initialAffineMax_zero_le a b n (MY ω))
  have hGXlimnonneg : 0 ≤ᵐ[PX] GXlim := by
    filter_upwards [hMXpos] with ω hω
    exact sub_nonneg.mpr (hle 0 (MX ω) hω)
  have hGYlimnonneg : 0 ≤ᵐ[PY] GYlim := by
    filter_upwards [hMYpos] with ω hω
    exact sub_nonneg.mpr (hle 0 (MY ω) hω)
  have hGYlimint : Integrable GYlim PY := hIY.sub hLY
  have hGXorder (n : ℕ) : (∫ ω, GX n ω ∂PX) ≤ ∫ ω, GY n ω ∂PY := by
    have h := horder n (fun i => a i.val) (fun i => b i.val)
    change (∫ ω, initialAffineMax a b n (MX ω) ∂PX) ≤
      ∫ ω, initialAffineMax a b n (MY ω) ∂PY at h
    rw [integral_sub, integral_sub]
    · linarith only [h, hLeq]
    · exact affineMax_comp_integrable PY MY hMY _ _
    · exact hLY
    · exact affineMax_comp_integrable PX MX hMX _ _
    · exact hLX
  have hGXlinorder (n : ℕ) : (∫⁻ ω, ENNReal.ofReal (GX n ω) ∂PX) ≤
      ∫⁻ ω, ENNReal.ofReal (GYlim ω) ∂PY := by
    calc
      _ = ENNReal.ofReal (∫ ω, GX n ω ∂PX) :=
        (ofReal_integral_eq_lintegral_ofReal (hGXint n) (ae_of_all _ (hGXnonneg n))).symm
      _ ≤ ENNReal.ofReal (∫ ω, GY n ω ∂PY) := ENNReal.ofReal_le_ofReal (hGXorder n)
      _ = ∫⁻ ω, ENNReal.ofReal (GY n ω) ∂PY :=
        ofReal_integral_eq_lintegral_ofReal (hGYint n) (ae_of_all _ (hGYnonneg n))
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [hMYpos] with ω hω
        apply ENNReal.ofReal_le_ofReal
        apply sub_le_sub_right
        unfold initialAffineMax affineMax
        exact Finset.sup'_le Finset.univ_nonempty _ (fun i _ => hle i.val (MY ω) hω)
  have hGXtend : ∀ᵐ ω ∂PX,
      Tendsto (fun n => ENNReal.ofReal (GX n ω)) atTop (𝓝 (ENNReal.ofReal (GXlim ω))) := by
    filter_upwards [hMXpos] with ω hω
    exact ENNReal.tendsto_ofReal ((initialAffineMax_tendsto a b (MX ω) (F (MX ω))
      (fun n => hle n (MX ω) hω) (hsup (MX ω) hω)).sub_const (LX ω))
  have hGXmono : ∀ᵐ ω ∂PX, Monotone (fun n => ENNReal.ofReal (GX n ω)) := by
    filter_upwards [] with ω n m hnm
    exact ENNReal.ofReal_le_ofReal (sub_le_sub_right (initialAffineMax_mono a b (MX ω) hnm) _)
  have hlimit := lintegral_tendsto_of_tendsto_of_monotone
    (fun n => (hGXint n).aemeasurable.ennreal_ofReal) hGXmono hGXtend
  have hL : (∫⁻ ω, ENNReal.ofReal (GXlim ω) ∂PX) ≤
      ∫⁻ ω, ENNReal.ofReal (GYlim ω) ∂PY :=
    le_of_tendsto hlimit (Filter.Eventually.of_forall hGXlinorder)
  have hGXlimint : Integrable GXlim PX := by
    refine ⟨((hF.comp_aemeasurable hMX.aemeasurable).sub hLX.aemeasurable).aestronglyMeasurable, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal hGXlimnonneg).mpr
    exact hL.trans_lt ((hasFiniteIntegral_iff_ofReal hGYlimnonneg).mp hGYlimint.hasFiniteIntegral)
  have hIX : Integrable (fun ω => F (MX ω)) PX := by
    apply (hGXlimint.add hLX).congr
    filter_upwards [] with ω
    exact sub_add_cancel _ _
  refine ⟨hIX, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hGXlimint hGXlimnonneg,
    ← ofReal_integral_eq_lintegral_ofReal hGYlimint hGYlimnonneg] at hL
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hL
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hGXlimnonneg),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hGYlimnonneg)] at hreal
  rw [integral_sub hIX hLX, integral_sub hIY hLY] at hreal
  linarith only [hreal, hLeq]


end DOZZ.Proofs
