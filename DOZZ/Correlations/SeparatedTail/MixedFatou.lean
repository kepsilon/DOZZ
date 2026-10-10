/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.MomentConvergence
public import DOZZ.Correlations.SeparatedTail.MixedMoment

/-! A common subsequence carries out the passage from cutoff mixed moments to limiting masses in
the separated joint-tail estimate. -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DOZZ.Proofs

/-- Fatou passes a two-variable mixed moment bound through convergence in probability.
The same subsequence is used for both variables. No independence of the limits is needed. -/
theorem separatedTail_mixed_moment_le_of_tendstoInMeasure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f2 f3 : ℕ → Ω → ℝ≥0∞) (g2 g3 : Ω → ℝ≥0∞)
    (hf2 : ∀ n, AEMeasurable (f2 n) P) (hf3 : ∀ n, AEMeasurable (f3 n) P)
    (hfin2 : ∀ n, ∀ᵐ ω ∂P, f2 n ω ≠ ⊤)
    (hfin3 : ∀ n, ∀ᵐ ω ∂P, f3 n ω ≠ ⊤)
    (hgfin2 : ∀ᵐ ω ∂P, g2 ω ≠ ⊤) (hgfin3 : ∀ᵐ ω ∂P, g3 ω ≠ ⊤)
    (hconv2 : TendstoInMeasure P (fun n ω => (f2 n ω).toReal) atTop
      (fun ω => (g2 ω).toReal))
    (hconv3 : TendstoInMeasure P (fun n ω => (f3 n ω).toReal) atTop
      (fun ω => (g3 ω).toReal))
    (a2 a3 : ℝ) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3)
    (C : ℝ≥0∞) (hbound : ∀ n, (∫⁻ ω, f2 n ω ^ a2 * f3 n ω ^ a3 ∂P) ≤ C) :
    (∫⁻ ω, g2 ω ^ a2 * g3 ω ^ a3 ∂P) ≤ C := by
  obtain ⟨ns, hns, h2⟩ := hconv2.exists_seq_tendsto_ae
  obtain ⟨ms, _hms, h3⟩ := (hconv3.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  have hfinite2 : ∀ᵐ ω ∂P, ∀ n, f2 n ω ≠ ⊤ := ae_all_iff.mpr hfin2
  have hfinite3 : ∀ᵐ ω ∂P, ∀ n, f3 n ω ≠ ⊤ := ae_all_iff.mpr hfin3
  have hlim : ∀ᵐ ω ∂P, Tendsto
      (fun n => f2 (ns (ms n)) ω ^ a2 * f3 (ns (ms n)) ω ^ a3) atTop
      (𝓝 (g2 ω ^ a2 * g3 ω ^ a3)) := by
    filter_upwards [h2, h3, hfinite2, hfinite3, hgfin2, hgfin3]
      with ω h2ω h3ω hf2ω hf3ω hg2ω hg3ω
    have hp2 := ((Real.continuousAt_rpow_const (g2 ω).toReal a2 (Or.inr ha2)).tendsto.comp
      (h2ω.comp _hms.tendsto_atTop))
    have hp3 := ((Real.continuousAt_rpow_const (g3 ω).toReal a3 (Or.inr ha3)).tendsto.comp h3ω)
    have hreal := ENNReal.tendsto_ofReal (hp2.mul hp3)
    have heq (x y : ℝ≥0∞) (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
        ENNReal.ofReal (x.toReal ^ a2 * y.toReal ^ a3) = x ^ a2 * y ^ a3 := by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg ENNReal.toReal_nonneg _)]
      rw [ENNReal.toReal_rpow, ENNReal.toReal_rpow,
        ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg ha2 hx),
        ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg ha3 hy)]
    simpa only [Function.comp_def, heq _ _ (hf2ω _) (hf3ω _),
      heq _ _ hg2ω hg3ω] using hreal
  calc
    _ = ∫⁻ ω, liminf (fun n => f2 (ns (ms n)) ω ^ a2 * f3 (ns (ms n)) ω ^ a3) atTop ∂P :=
      lintegral_congr_ae (hlim.mono fun ω hω => hω.liminf_eq.symm)
    _ ≤ liminf (fun n => ∫⁻ ω, f2 (ns (ms n)) ω ^ a2 * f3 (ns (ms n)) ω ^ a3 ∂P) atTop :=
      lintegral_liminf_le' (fun n => ((hf2 _).pow_const a2).mul ((hf3 _).pow_const a3))
    _ ≤ limsup (fun n => ∫⁻ ω, f2 (ns (ms n)) ω ^ a2 * f3 (ns (ms n)) ω ^ a3 ∂P) atTop :=
      liminf_le_limsup
    _ ≤ C := limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun n => hbound _)

end DOZZ.Proofs
