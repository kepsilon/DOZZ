/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.RandomParameterLimit
public import DOZZ.Brownian.Lateral.WickReinsertion
public import DOZZ.GMC.Assembly.CircleIntensity

/-! Spatial cutoff limits for compact tests depending on a correlated real parameter. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- Integrating a compact parameter family preserves its pointwise parameter error bound. -/
theorem parameter_integral_grid_error
    (F : ℝ → BoundedContinuousFunction ℂ ℝ) (K : Set ℂ)
    (hK : MeasurableSet K) (hFK : ∀ t, tsupport (F t : ℂ → ℝ) ⊆ K)
    (Lcoef : ℝ → ℝ) (hLcoef : ∀ t, 0 ≤ Lcoef t)
    (hLip : ∀ t u, |t-u| ≤ 1 → ∀ x ∈ K, |F t x - F u x| ≤ Lcoef t * |t-u|)
    (μ : Measure ℂ) (k : ℕ) (t : ℝ) :
    ENNReal.ofReal ‖(∫ x, F t x ∂μ) - ∫ x, F (parameterGrid k t) x ∂μ‖ ≤
      ENNReal.ofReal (1 / ((k : ℝ) + 1)) * (ENNReal.ofReal (Lcoef t) * μ K) := by
  have hgrid := parameter_grid_error k t
  have hstep : 1 / ((k : ℝ) + 1) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (k : ℝ) + 1)).mpr
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hpoint (x : ℂ) : ENNReal.ofReal |F t x - F (parameterGrid k t) x| ≤
      K.indicator (fun _ => ENNReal.ofReal (Lcoef t * (1 / ((k : ℝ) + 1)))) x := by
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      exact ENNReal.ofReal_le_ofReal ((hLip t _ (hgrid.trans hstep) x hx).trans
        (mul_le_mul_of_nonneg_left hgrid (hLcoef t)))
    · rw [Set.indicator_of_notMem hx]
      have h1 := image_eq_zero_of_notMem_tsupport (fun h => hx (hFK t h))
      have h2 := image_eq_zero_of_notMem_tsupport
        (fun h => hx (hFK (parameterGrid k t) h))
      simp only [h1, h2, sub_self, abs_zero, ENNReal.ofReal_zero, le_refl]
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal |F t x - F (parameterGrid k t) x| ∂μ := by
      simpa only [Real.norm_eq_abs] using DOZZ.Assembly.ofReal_abs_integral_sub_le_lintegral μ
        (F t) (F (parameterGrid k t)) (F t).continuous.measurable
          (F (parameterGrid k t)).continuous.measurable
    _ ≤ ∫⁻ x, K.indicator (fun _ =>
        ENNReal.ofReal (Lcoef t * (1 / ((k : ℝ) + 1)))) x ∂μ := lintegral_mono hpoint
    _ = _ := by
      rw [lintegral_indicator hK, lintegral_const, Measure.restrict_apply_univ,
        ENNReal.ofReal_mul (hLcoef t)]
      ac_rfl

/-- Deterministic compact-test convergence passes to a correlated parameter family.
The required mixed first-moment bound is exactly on the parameter envelope times the
mass of the compact support. -/
theorem tendstoInMeasure_parameter_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (N : ℕ → Ω → Measure ℂ) (M : Ω → Measure ℂ)
    (hN : ∀ n, Measurable (N n)) (hM : Measurable M)
    (K : Set ℂ) (hK : IsCompact K)
    (hNfin : ∀ n ω, N n ω K < ⊤) (hMfin : ∀ ω, M ω K < ⊤)
    (F : ℝ → BoundedContinuousFunction ℂ ℝ)
    (hF : Measurable (fun p : ℝ × ℂ => F p.1 p.2))
    (hFK : ∀ t, tsupport (F t : ℂ → ℝ) ⊆ K)
    (θ : Ω → ℝ) (hθ : Measurable θ)
    (hconv : ∀ t, TendstoInMeasure P (fun n ω => ∫ x, F t x ∂N n ω)
      atTop (fun ω => ∫ x, F t x ∂M ω))
    (Lcoef : ℝ → ℝ) (hLcoef : ∀ t, 0 ≤ Lcoef t)
    (hLip : ∀ t u, |t-u| ≤ 1 → ∀ x ∈ K, |F t x - F u x| ≤ Lcoef t * |t-u|)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hbound : ∀ n, ∫⁻ ω, ENNReal.ofReal (Lcoef (θ ω)) * N n ω K ∂P ≤ C)
    (hboundlim : ∫⁻ ω, ENNReal.ofReal (Lcoef (θ ω)) * M ω K ∂P ≤ C) :
    TendstoInMeasure P (fun n ω => ∫ x, F (θ ω) x ∂N n ω)
      atTop (fun ω => ∫ x, F (θ ω) x ∂M ω) := by
  have hleft n : Measurable (fun p : ℝ × Ω => ∫ x, F p.1 x ∂N n p.2) :=
    measurable_compact_parameter_integral F hF K hK hFK (N n) (hN n) (hNfin n)
  have hright : Measurable (fun p : ℝ × Ω => ∫ x, F p.1 x ∂M p.2) :=
    measurable_compact_parameter_integral F hF K hK hFK M hM hMfin
  have hgrid k : Measurable (fun ω => parameterGrid k (θ ω)) :=
    ((measurable_of_countable (fun i : ℤ => (i : ℝ))).comp
      (Int.measurable_floor.comp (hθ.const_mul _))).div_const _
  apply tendstoInMeasure_random_parameter P
    (fun n ω t => ∫ x, F t x ∂N n ω) (fun ω t => ∫ x, F t x ∂M ω)
      θ hθ hconv (fun n ω => ENNReal.ofReal (Lcoef (θ ω)) * N n ω K)
        (fun ω => ENNReal.ofReal (Lcoef (θ ω)) * M ω K) C hC hbound hboundlim
  · intro k n
    exact ((hleft n |>.comp (hθ.prodMk measurable_id)).sub
      (hleft n |>.comp ((hgrid k).prodMk measurable_id))).norm.ennreal_ofReal.aemeasurable
  · intro k
    exact ((hright.comp ((hgrid k).prodMk measurable_id)).sub
      (hright.comp (hθ.prodMk measurable_id))).norm.ennreal_ofReal.aemeasurable
  · intro k n ω
    exact parameter_integral_grid_error F K hK.measurableSet hFK Lcoef hLcoef hLip (N n ω) k (θ ω)
  · intro k ω
    rw [norm_sub_rev]
    exact parameter_integral_grid_error F K hK.measurableSet hFK Lcoef hLcoef hLip (M ω) k (θ ω)


end DOZZ.Proofs
