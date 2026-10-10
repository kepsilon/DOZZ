/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Second-order Taylor formula with a singular endpoint

* `bpz_taylor_singular`: for a function `g` that is `C²` only on `(0, t]`, with one-sided limits
  `g₀` of `g` and `d₀` of `g'` at `0` and an integrable second derivative `g''` on `(0, t]`,
  `g t = g₀ + d₀ * t + ∫ u in 0..t, (t - u) * g'' u`. The proof applies the improper fundamental
  theorem of calculus to `φ u = g u + (t - u) * g' u`, whose derivative on `(0, t)` is
  `(t - u) * g'' u` (the terms in `g'` cancel).
* `bpz_taylor_remainder_subst`, `bpz_taylor_remainder_subst_complex`: the substitution `u = s t`
  in the Taylor remainder, `∫ u in 0..t, (t - u) * f u = t ^ 2 * ∫ s in Icc 0 1, (1 - s) * f (s t)`.
  No integrability of `f` is needed, since an affine change of variables is valid for all
  Bochner integrals (non-integrable integrands have value `0` on both sides). -/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-! ### The Taylor formula -/

/-- The weighted second derivative `u ↦ (t - u) * g'' u` is interval integrable on `[0, t]` when
`g''` is integrable on `(0, t]`: the weight `t - u` is continuous, hence bounded on `[0, t]`. -/
theorem bpzTS_intervalIntegrable_mul {g'' : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hint : IntegrableOn g'' (Ioc 0 t)) :
    IntervalIntegrable (fun u => (t - u) * g'' u) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
  exact hint.continuousOn_mul_of_subset (g := fun u : ℝ => t - u) (K := Icc 0 t)
    (by fun_prop) isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self

/-- The Taylor primitive `u ↦ g u + (t - u) * g' u` has derivative `(t - u) * g'' u`. -/
theorem bpzTS_hasDerivAt_primitive {g g' g'' : ℝ → ℝ} {t u : ℝ}
    (hg : HasDerivAt g (g' u) u) (hg' : HasDerivAt g' (g'' u) u) :
    HasDerivAt (fun v => g v + (t - v) * g' v) ((t - u) * g'' u) u := by
  have h1 : HasDerivAt (fun v : ℝ => t - v) (-1) u := by
    simpa using (hasDerivAt_id u).const_sub t
  convert hg.add (h1.mul hg') using 1
  ring

/-- Second-order Taylor formula on `[0, t]` for a function that is `C²` only on `(0, t]`, with
one-sided limits of the function and its derivative at `0` and an integrable second derivative. -/
theorem bpz_taylor_singular {g g' g'' : ℝ → ℝ} {t g₀ d₀ : ℝ} (ht : 0 < t)
    (hg : ∀ u ∈ Ioc (0 : ℝ) t, HasDerivAt g (g' u) u)
    (hg' : ∀ u ∈ Ioc (0 : ℝ) t, HasDerivAt g' (g'' u) u)
    (hg0 : Tendsto g (𝓝[>] 0) (𝓝 g₀)) (hg'0 : Tendsto g' (𝓝[>] 0) (𝓝 d₀))
    (hint : IntegrableOn g'' (Ioc 0 t)) :
    g t = g₀ + d₀ * t + ∫ u in (0 : ℝ)..t, (t - u) * g'' u := by
  have htmem : t ∈ Ioc (0 : ℝ) t := ⟨ht, le_rfl⟩
  -- the primitive `u ↦ g u + (t - u) * g' u` tends to `g₀ + t * d₀` at `0⁺`
  have hlim0 : Tendsto (fun u => g u + (t - u) * g' u) (𝓝[>] 0) (𝓝 (g₀ + (t - 0) * d₀)) := by
    have hw : Tendsto (fun u : ℝ => t - u) (𝓝[>] 0) (𝓝 (t - 0)) :=
      ((continuous_const.sub continuous_id).tendsto 0).mono_left nhdsWithin_le_nhds
    exact hg0.add (hw.mul hg'0)
  -- and to `g t` at `t⁻`, by continuity of `g` and `g'` at `t`
  have hlimt : Tendsto (fun u => g u + (t - u) * g' u) (𝓝[<] t) (𝓝 (g t)) := by
    have hgc := (hg t htmem).continuousAt
    have hg'c := (hg' t htmem).continuousAt
    have hcont : ContinuousAt (fun u => g u + (t - u) * g' u) t := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ht
    (fun u hu => bpzTS_hasDerivAt_primitive (hg u (Ioo_subset_Ioc_self hu))
      (hg' u (Ioo_subset_Ioc_self hu)))
    (bpzTS_intervalIntegrable_mul ht hint) hlim0 hlimt
  rw [hftc]
  ring

/-! ### Substitution in the Taylor remainder -/

/-- The substitution `u = s t` in the Taylor remainder, for a function with values in a real
normed space. -/
theorem bpzTS_subst_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    {t : ℝ} (ht : 0 < t) :
    ∫ u in (0 : ℝ)..t, (t - u) • f u = t ^ 2 • ∫ s in Icc (0 : ℝ) 1, (1 - s) • f (s * t) := by
  have h1 := intervalIntegral.integral_comp_mul_right (a := 0) (b := 1)
    (fun u : ℝ => (t - u) • f u) ht.ne'
  have h2 : ∫ s in (0 : ℝ)..1, (t - s * t) • f (s * t) =
      t • ∫ s in (0 : ℝ)..1, (1 - s) • f (s * t) := by
    rw [← intervalIntegral.integral_smul]
    congr 1
    funext s
    rw [smul_smul]
    congr 1
    ring
  rw [zero_mul, one_mul, h2] at h1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, pow_two,
    mul_smul, h1, smul_inv_smul₀ ht.ne']

/-- The Taylor remainder after the substitution `u = s t`. -/
theorem bpz_taylor_remainder_subst {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) :
    ∫ u in (0 : ℝ)..t, (t - u) * f u = t ^ 2 * ∫ s in Icc (0 : ℝ) 1, (1 - s) * f (s * t) := by
  simpa only [smul_eq_mul] using bpzTS_subst_smul (f := f) ht

/-- Complex-valued version of the substitution, for later use with complex integrands. -/
theorem bpz_taylor_remainder_subst_complex {f : ℝ → ℂ} {t : ℝ} (ht : 0 < t) :
    ∫ u in (0 : ℝ)..t, ((t - u : ℝ) : ℂ) * f u =
      ((t ^ 2 : ℝ) : ℂ) * ∫ s in Icc (0 : ℝ) 1, ((1 - s : ℝ) : ℂ) * f (s * t) := by
  simpa only [Complex.real_smul] using bpzTS_subst_smul (f := f) ht

end DOZZ.Proofs
