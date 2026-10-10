/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Annulus.ReferenceIntensity
public import DOZZ.GMC.Moments.LimitFatou

/-! # Convergence of extended moments

Moments of order `p` of nonnegative extended random variables converge along a sequence converging
in measure, provided a moment of an order `p'` beyond `p` is uniformly bounded. For `p < 0` the
uniform bound also makes the variables and their limit almost surely positive, so that the power
function is continuous at the limit. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- For negative orders `r` and `s`, finiteness of `x ^ s` implies finiteness of `x ^ r`: both
just say that `x ≠ 0`. -/
theorem momentConv_rpow_ne_top_of_neg {x : ℝ≥0∞} {r s : ℝ} (hr : r < 0) (hs : s < 0)
    (h : x ^ s ≠ ⊤) : x ^ r ≠ ⊤ := by
  intro hx
  rcases ENNReal.rpow_eq_top_iff.mp hx with ⟨h0, -⟩ | ⟨-, hpos⟩
  · exact h (ENNReal.rpow_eq_top_iff.mpr (Or.inl ⟨h0, hs⟩))
  · exact absurd hpos (not_lt.mpr hr.le)

/-- A finite bound on a negative-order moment makes every negative-order power almost surely
finite, i.e. makes the variable almost surely nonzero. -/
theorem momentConv_ae_rpow_ne_top_of_neg
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → ℝ≥0∞) (hf : AEMeasurable f P)
    {r s : ℝ} (hr : r < 0) (hs : s < 0) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∫⁻ ω, f ω ^ s ∂P ≤ C) : ∀ᵐ ω ∂P, f ω ^ r ≠ ⊤ := by
  have hlt : ∀ᵐ ω ∂P, f ω ^ s < ⊤ :=
    ae_lt_top' (hf.pow_const s) (ne_top_of_le_ne_top hC hbound)
  filter_upwards [hlt] with ω hω
  exact momentConv_rpow_ne_top_of_neg hr hs hω.ne

/-- Fatou for extended powers: a uniform bound on `∫⁻ (f n) ^ r` passes to a limit in measure of the
real parts, for every real order `r`. -/
theorem momentConv_lintegral_rpow_limit_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ≥0∞) (g : Ω → ℝ≥0∞)
    (hf : ∀ n, AEMeasurable (f n) P)
    (hfin : ∀ n, ∀ᵐ ω ∂P, f n ω ≠ ⊤) (hgfin : ∀ᵐ ω ∂P, g ω ≠ ⊤)
    (hconv : TendstoInMeasure P (fun n ω => (f n ω).toReal) atTop (fun ω => (g ω).toReal))
    (r : ℝ) (C : ℝ≥0∞) (hbound : ∀ n, ∫⁻ ω, f n ω ^ r ∂P ≤ C) :
    ∫⁻ ω, g ω ^ r ∂P ≤ C := by
  have hmax : ∀ x : ℝ≥0∞, max x.toReal 0 = x.toReal := fun x => max_eq_left ENNReal.toReal_nonneg
  have hae : ∀ n, (fun ω => ENNReal.rpow (ENNReal.ofReal (max (f n ω).toReal 0)) r) =ᵐ[P]
      fun ω => f n ω ^ r := by
    intro n
    filter_upwards [hfin n] with ω hω
    simp only [hmax, ENNReal.ofReal_toReal hω, ENNReal.rpow_eq_pow]
  have hfmeas : ∀ n, AEMeasurable
      (fun ω => ENNReal.rpow (ENNReal.ofReal (max (f n ω).toReal 0)) r) P :=
    fun n => ((hf n).pow_const r).congr (hae n).symm
  have hlim := lintegral_ennreal_rpow_le_of_tendstoInMeasure P (fun n ω => (f n ω).toReal)
    (fun ω => (g ω).toReal) r C hconv hfmeas (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
    (fun n => (lintegral_congr_ae (hae n)).trans_le (hbound n))
  refine le_trans (le_of_eq (lintegral_congr_ae ?_)) hlim
  filter_upwards [hgfin] with ω hω
  simp only [ENNReal.ofReal_toReal hω, ENNReal.rpow_eq_pow]

/-- The real power function is continuous at the real part of any `x` such that `x` and `x ^ r`
are finite. -/
theorem momentConv_continuousAt_rpow {x : ℝ≥0∞} {r : ℝ} (hx : x ≠ ⊤) (hxr : x ^ r ≠ ⊤) :
    ContinuousAt (fun t : ℝ => t ^ r) x.toReal := by
  refine Real.continuousAt_rpow_const _ _ ?_
  rcases le_or_gt 0 r with hr | hr
  · exact Or.inr hr
  · refine Or.inl fun h0 => hxr ?_
    have hx0 : x = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff x).mp h0 with h | h
      · exact h
      · exact absurd h hx
    rw [hx0, ENNReal.zero_rpow_of_neg hr]

/-- Real parts of extended powers converge in measure when the real parts converge in measure,
provided the limit has an almost surely finite power. -/
theorem momentConv_tendstoInMeasure_rpow
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ≥0∞) (g : Ω → ℝ≥0∞) (hf : ∀ n, AEMeasurable (f n) P)
    (hgfin : ∀ᵐ ω ∂P, g ω ≠ ⊤)
    (hconv : TendstoInMeasure P (fun n ω => (f n ω).toReal) atTop (fun ω => (g ω).toReal))
    (r : ℝ) (hgr : ∀ᵐ ω ∂P, g ω ^ r ≠ ⊤) :
    TendstoInMeasure P (fun n ω => (f n ω ^ r).toReal) atTop (fun ω => (g ω ^ r).toReal) := by
  have hreal : ∀ n, AEStronglyMeasurable (fun ω => (f n ω).toReal) P := fun n =>
    (ENNReal.measurable_toReal.comp_aemeasurable (hf n)).aestronglyMeasurable
  have hpow : ∀ n, AEStronglyMeasurable (fun ω => (f n ω ^ r).toReal) P := fun n =>
    (ENNReal.measurable_toReal.comp_aemeasurable ((hf n).pow_const r)).aestronglyMeasurable
  rw [exists_seq_tendstoInMeasure_atTop_iff hpow]
  intro ns hns
  obtain ⟨ns', hns', hae⟩ := (exists_seq_tendstoInMeasure_atTop_iff hreal).mp hconv ns hns
  refine ⟨ns', hns', ?_⟩
  filter_upwards [hae, hgfin, hgr] with ω hω hω1 hω2
  have h : Tendsto (fun i => ((f (ns (ns' i)) ω).toReal) ^ r) atTop (𝓝 ((g ω).toReal ^ r)) :=
    (momentConv_continuousAt_rpow hω1 hω2).tendsto.comp hω
  simpa only [← ENNReal.toReal_rpow] using h

/-- Pointwise, `x ≤ 1 + x ^ q` for every exponent `q ≥ 1`. -/
theorem momentConv_le_one_add_rpow (x : ℝ≥0∞) {q : ℝ} (hq : 1 ≤ q) : x ≤ 1 + x ^ q := by
  rcases le_total x 1 with hx | hx
  · exact hx.trans le_self_add
  · calc x = x ^ (1 : ℝ) := (ENNReal.rpow_one x).symm
      _ ≤ x ^ q := ENNReal.rpow_le_rpow_of_exponent_le hx hq
      _ ≤ 1 + x ^ q := le_add_self

/-- On a probability space, a finite bound on a moment of order `q ≥ 1` gives integrability. -/
theorem momentConv_integrable_of_rpow_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Ω → ℝ) (hF : AEStronglyMeasurable F P) {q : ℝ} (hq : 1 ≤ q) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∫⁻ ω, ‖F ω‖ₑ ^ q ∂P ≤ C) : Integrable F P := by
  refine ⟨hF, ?_⟩
  show ∫⁻ ω, ‖F ω‖ₑ ∂P < ⊤
  calc ∫⁻ ω, ‖F ω‖ₑ ∂P ≤ ∫⁻ ω, (1 + ‖F ω‖ₑ ^ q) ∂P :=
        lintegral_mono fun ω => momentConv_le_one_add_rpow _ hq
    _ = 1 + ∫⁻ ω, ‖F ω‖ₑ ^ q ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, lt_of_le_of_lt hbound hC.lt_top⟩

/-- The extended moment of a variable with almost surely finite power is the lift of the Bochner
integral of the real part of that power, whenever the latter is integrable. -/
theorem momentConv_lintegral_eq_ofReal_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → ℝ≥0∞) (r : ℝ)
    (hfr : ∀ᵐ ω ∂P, f ω ^ r ≠ ⊤) (hint : Integrable (fun ω => (f ω ^ r).toReal) P) :
    ∫⁻ ω, f ω ^ r ∂P = ENNReal.ofReal (∫ ω, (f ω ^ r).toReal ∂P) := by
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)]
  exact lintegral_congr_ae (hfr.mono fun ω h => (ENNReal.ofReal_toReal h).symm)

/-- Moment convergence once the powers of order `p` are known to be almost surely finite. -/
theorem momentConv_tendsto_of_rpow_ne_top
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ≥0∞) (g : Ω → ℝ≥0∞)
    (hf : ∀ n, AEMeasurable (f n) P) (hgfin : ∀ᵐ ω ∂P, g ω ≠ ⊤)
    (hconv : TendstoInMeasure P (fun n ω => (f n ω).toReal) atTop (fun ω => (g ω).toReal))
    {p p' : ℝ} (hp : p ≠ 0) (hq : 1 < p' / p) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ n, ∫⁻ ω, f n ω ^ p' ∂P ≤ C)
    (hfp : ∀ n, ∀ᵐ ω ∂P, f n ω ^ p ≠ ⊤) (hgp : ∀ᵐ ω ∂P, g ω ^ p ≠ ⊤) :
    Tendsto (fun n => ∫⁻ ω, f n ω ^ p ∂P) atTop (𝓝 (∫⁻ ω, g ω ^ p ∂P)) := by
  have hFm : ∀ n, AEMeasurable (fun ω => (f n ω ^ p).toReal) P := fun n =>
    ENNReal.measurable_toReal.comp_aemeasurable ((hf n).pow_const p)
  have hFq : ∀ n, ∫⁻ ω, ‖(f n ω ^ p).toReal‖ₑ ^ (p' / p) ∂P ≤ C := by
    intro n
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) (hbound n)
    filter_upwards [hfp n] with ω hω
    rw [Real.enorm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hω,
      ← ENNReal.rpow_mul, mul_div_cancel₀ _ hp]
  obtain ⟨hGint, hlim⟩ := gmc_integral_limit_of_higher_moment P (fun n ω => (f n ω ^ p).toReal)
    (fun ω => (g ω ^ p).toReal) (fun n => (hFm n).aestronglyMeasurable)
    (momentConv_tendstoInMeasure_rpow P f g hf hgfin hconv p hgp) (p' / p) hq C hC.lt_top hFq
  have hFint : ∀ n, Integrable (fun ω => (f n ω ^ p).toReal) P := fun n =>
    momentConv_integrable_of_rpow_bound P _ (hFm n).aestronglyMeasurable hq.le hC (hFq n)
  have h1 : (fun n => ∫⁻ ω, f n ω ^ p ∂P) =
      fun n => ENNReal.ofReal (∫ ω, (f n ω ^ p).toReal ∂P) :=
    funext fun n => momentConv_lintegral_eq_ofReal_integral P (f n) p (hfp n) (hFint n)
  rw [h1, momentConv_lintegral_eq_ofReal_integral P g p hgp hGint]
  exact (ENNReal.continuous_ofReal.tendsto _).comp hlim

/-- Moments of order `p` converge along a sequence converging in measure, provided a moment of an
order `p'` beyond `p` (larger if `p > 0`, smaller if `p < 0`) is uniformly bounded. -/
theorem lintegral_rpow_tendsto_of_uniform_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ≥0∞) (g : Ω → ℝ≥0∞)
    (hf : ∀ n, AEMeasurable (f n) P) (hg : AEMeasurable g P)
    (hfin : ∀ n, ∀ᵐ ω ∂P, f n ω ≠ ⊤) (hgfin : ∀ᵐ ω ∂P, g ω ≠ ⊤)
    (hconv : TendstoInMeasure P (fun n ω => (f n ω).toReal) atTop (fun ω => (g ω).toReal))
    (p p' : ℝ) (hp : (0 < p ∧ p < p') ∨ (p' < p ∧ p < 0)) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hbound : ∀ n, ∫⁻ ω, f n ω ^ p' ∂P ≤ C) :
    Tendsto (fun n => ∫⁻ ω, f n ω ^ p ∂P) atTop (𝓝 (∫⁻ ω, g ω ^ p ∂P)) := by
  rcases hp with ⟨hp0, hpp'⟩ | ⟨hp'p, hp0⟩
  · refine momentConv_tendsto_of_rpow_ne_top P f g hf hgfin hconv hp0.ne'
      ((one_lt_div hp0).mpr hpp') hC hbound (fun n => ?_) ?_
    · filter_upwards [hfin n] with ω hω
      exact ENNReal.rpow_ne_top_of_nonneg hp0.le hω
    · filter_upwards [hgfin] with ω hω
      exact ENNReal.rpow_ne_top_of_nonneg hp0.le hω
  · have hp'0 : p' < 0 := hp'p.trans hp0
    have hglim : ∫⁻ ω, g ω ^ p' ∂P ≤ C :=
      momentConv_lintegral_rpow_limit_le P f g hf hfin hgfin hconv p' C hbound
    exact momentConv_tendsto_of_rpow_ne_top P f g hf hgfin hconv hp0.ne
      ((one_lt_div_of_neg hp0).mpr hp'p) hC hbound
      (fun n => momentConv_ae_rpow_ne_top_of_neg P (f n) (hf n) hp0 hp'0 hC (hbound n))
      (momentConv_ae_rpow_ne_top_of_neg P g hg hp0 hp'0 hC hglim)

end DOZZ.Proofs
