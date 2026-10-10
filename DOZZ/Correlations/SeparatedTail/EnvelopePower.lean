/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.SeparatedTail.HarmonicEnvelope
public import DOZZ.Correlations.SeparatedTail.MixedMoment

/-! Powers and uniform moment bounds of the actual correlated restoration/harmonic envelope. -/

@[expose] public section
open MeasureTheory Metric Set
open scoped ENNReal
namespace DOZZ.Proofs

noncomputable def separatedTail_harmonicEnvelope {Ω : Type*} (c : ℂ)
    (H : Ω → ℂ → ℝ) (L : Ω → ℝ) (l : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (l*|L ω|)) *
    ⨆ z : closedBall c 1, ENNReal.ofReal (Real.exp (l*|H ω z|))

theorem separatedTail_harmonicEnvelope_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (c : ℂ)
    (H : Ω → ℂ → ℝ) (L : Ω → ℝ)
    (hH : Measurable (fun q : Ω × ℂ => H q.1 q.2)) (hL : Measurable L)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (H ω) (closedBall c 1)) (l : ℝ) :
    AEMeasurable (separatedTail_harmonicEnvelope c H L l) P := by
  have hm := separatedTail_harmonic_envelope_aemeasurable P c H hH hcont l
  have hm' : AEMeasurable (fun ω => ⨆ z : closedBall c 1,
      ENNReal.ofReal (Real.exp (l*|H ω z|))) P := by
    simpa only [iSup_subtype] using hm
  exact (measurable_ofReal_exp_mul_abs L hL l).aemeasurable.mul hm'

/-- The envelope's power is the same envelope at the multiplied linear order. -/
theorem separatedTail_harmonicEnvelope_rpow
    {Ω : Type*} (c : ℂ) (H : Ω → ℂ → ℝ) (L : Ω → ℝ)
    (l r : ℝ) (hr : 0 < r) (ω : Ω) :
    separatedTail_harmonicEnvelope c H L l ω ^ r = separatedTail_harmonicEnvelope c H L (l*r) ω := by
  unfold separatedTail_harmonicEnvelope
  rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le]
  have hi : (⨆ z : closedBall c 1, ENNReal.ofReal (Real.exp (l*|H ω z|))) ^ r =
      ⨆ z : closedBall c 1, ENNReal.ofReal (Real.exp (l*|H ω z|)) ^ r :=
    (ENNReal.orderIsoRpow r hr).map_iSup _
  rw [hi]
  have he (v : ℝ) : ENNReal.ofReal (Real.exp (l*|v|)) ^ r =
      ENNReal.ofReal (Real.exp ((l*r)*|v|)) := by
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
    congr 2
    ring
  simp_rw [he]

/-- The envelope increases with its linear order. -/
theorem separatedTail_harmonicEnvelope_mono
    {Ω : Type*} (c : ℂ) (H : Ω → ℂ → ℝ) (L : Ω → ℝ)
    {l m : ℝ} (hlm : l ≤ m) (ω : Ω) :
    separatedTail_harmonicEnvelope c H L l ω ≤ separatedTail_harmonicEnvelope c H L m ω := by
  apply mul_le_mul'
  · exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hlm (abs_nonneg _)))
  · apply iSup_mono
    intro z
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hlm (abs_nonneg _)))

/-- Every point in the closed unit disk is dominated by the correlated envelope. -/
theorem separatedTail_exp_harmonic_sub_le_envelope
    {Ω : Type*} (c : ℂ) (H : Ω → ℂ → ℝ) (L : Ω → ℝ)
    (l : ℝ) (hl : 0 ≤ l) (ω : Ω) (x : ℂ) (hx : x ∈ closedBall c 1) :
    ENNReal.ofReal (Real.exp (l*(H ω x-L ω))) ≤ separatedTail_harmonicEnvelope c H L l ω := by
  have h := mul_le_mul_of_nonneg_left
    (show H ω x-L ω ≤ |H ω x|+|L ω| by linarith [le_abs_self (H ω x), neg_le_abs (L ω)]) hl
  calc
    _ ≤ ENNReal.ofReal (Real.exp (l*(|H ω x|+|L ω|))) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr h)
    _ = ENNReal.ofReal (Real.exp (l*|L ω|))*ENNReal.ofReal (Real.exp (l*|H ω x|)) := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_right (le_iSup
      (fun z : closedBall c 1 => ENNReal.ofReal (Real.exp (l*|H ω z|))) ⟨x,hx⟩) _

/-- A uniform all-linear-order bound from the exterior-pinned Markov decomposition controls the
product envelope in Hölder's inequality, including the correlated scalar in both factors. -/
theorem separatedTail_product_envelope_moment_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (c2 c3 : ℂ) (H2 H3 : Ω → ℂ → ℝ) (L : Ω → ℝ)
    (hE2 : ∀ l, AEMeasurable (separatedTail_harmonicEnvelope c2 H2 L l) P)
    (C : ℝ → ℝ)
    (hC2 : ∀ l, 0 < l → (∫⁻ ω, separatedTail_harmonicEnvelope c2 H2 L l ω ∂P) ≤ ENNReal.ofReal (C l))
    (hC3 : ∀ l, 0 < l → (∫⁻ ω, separatedTail_harmonicEnvelope c3 H3 L l ω ∂P) ≤ ENNReal.ofReal (C l))
    (l2 l3 p T : ℝ) (hp : 0 < p) (hT : 0 < T) (hl2 : l2*p ≤ T) (hl3 : l3*p ≤ T) :
    (∫⁻ ω, (separatedTail_harmonicEnvelope c2 H2 L l2 ω *
      separatedTail_harmonicEnvelope c3 H3 L l3 ω)^p ∂P) ≤ 2*ENNReal.ofReal (C (2*T)) := by
  have hdom : ∀ ω, (separatedTail_harmonicEnvelope c2 H2 L l2 ω *
      separatedTail_harmonicEnvelope c3 H3 L l3 ω)^p ≤
      separatedTail_harmonicEnvelope c2 H2 L T ω * separatedTail_harmonicEnvelope c3 H3 L T ω := by
    intro ω
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le,
      separatedTail_harmonicEnvelope_rpow _ _ _ _ _ hp,
      separatedTail_harmonicEnvelope_rpow _ _ _ _ _ hp]
    exact mul_le_mul' (separatedTail_harmonicEnvelope_mono _ _ _ hl2 _) (separatedTail_harmonicEnvelope_mono _ _ _ hl3 _)
  have h2 : (∫⁻ ω, separatedTail_harmonicEnvelope c2 H2 L T ω ^ (2 : ℝ) ∂P) ≤
      ENNReal.ofReal (C (2*T)) := by
    simpa only [separatedTail_harmonicEnvelope_rpow _ _ _ T 2 (by norm_num), mul_comm T 2] using
      hC2 (2*T) (by positivity)
  have h3 : (∫⁻ ω, separatedTail_harmonicEnvelope c3 H3 L T ω ^ (2 : ℝ) ∂P) ≤
      ENNReal.ofReal (C (2*T)) := by
    simpa only [separatedTail_harmonicEnvelope_rpow _ _ _ T 2 (by norm_num), mul_comm T 2] using
      hC3 (2*T) (by positivity)
  exact (lintegral_mono hdom).trans ((separatedTail_correlated_envelope_product_le P _ _ (hE2 T) _ _
    h2 h3).trans_eq (by exact (two_mul _).symm))

end DOZZ.Proofs
