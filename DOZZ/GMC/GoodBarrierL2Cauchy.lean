/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The mixed second-moment criterion for L² Cauchy convergence of cutoff masses. -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace DOZZ.Proofs

/-- If diagonal and mixed second moments of a real cutoff family have the same limit, then the
mean square difference between two independently varying cutoffs tends to zero. This is the final
algebraic step in the good-mass mixed-cutoff argument. -/
theorem tendsto_integral_sq_sub_of_mixed_second_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (J : ℝ → Ω → ℝ) (L : ℝ)
    (hsq : ∀ r, Integrable (fun ω => (J r ω) ^ 2) P)
    (hmul : ∀ r s, Integrable (fun ω => J r ω * J s ω) P)
    (hdiag : Tendsto (fun r => ∫ ω, (J r ω) ^ 2 ∂P) atTop (𝓝 L))
    (hmixed : Tendsto (fun p : ℝ × ℝ => ∫ ω, J p.1 ω * J p.2 ω ∂P)
      (atTop ×ˢ atTop) (𝓝 L)) :
    Tendsto (fun p : ℝ × ℝ => ∫ ω, (J p.1 ω - J p.2 ω) ^ 2 ∂P)
      (atTop ×ˢ atTop) (𝓝 0) := by
  have hdiag₁ : Tendsto
      (fun p : ℝ × ℝ => ∫ ω, (J p.1 ω) ^ 2 ∂P)
      (atTop ×ˢ atTop) (𝓝 L) := hdiag.comp tendsto_fst
  have hdiag₂ : Tendsto
      (fun p : ℝ × ℝ => ∫ ω, (J p.2 ω) ^ 2 ∂P)
      (atTop ×ˢ atTop) (𝓝 L) := hdiag.comp tendsto_snd
  have hcross₂ : Tendsto
      (fun p : ℝ × ℝ => 2 * ∫ ω, J p.1 ω * J p.2 ω ∂P)
      (atTop ×ˢ atTop) (𝓝 (2 * L)) := by
    simpa using hmixed.const_mul (2 : ℝ)
  have hlim : Tendsto
      (fun p : ℝ × ℝ =>
        (∫ ω, (J p.1 ω) ^ 2 ∂P) + (∫ ω, (J p.2 ω) ^ 2 ∂P) -
          2 * ∫ ω, J p.1 ω * J p.2 ω ∂P)
      (atTop ×ˢ atTop) (𝓝 0) := by
    have hsum := hdiag₁.add hdiag₂
    have hsub := hsum.sub hcross₂
    convert hsub using 1
    ring_nf
  apply hlim.congr'
  filter_upwards [] with p
  have hsum : Integrable (fun ω => (J p.1 ω) ^ 2 + (J p.2 ω) ^ 2) P :=
    (hsq p.1).add (hsq p.2)
  have hcross : Integrable (fun ω => 2 * (J p.1 ω * J p.2 ω)) P :=
    (hmul p.1 p.2).const_mul 2
  have hpoint (ω : Ω) :
      (J p.1 ω - J p.2 ω) ^ 2 =
        ((J p.1 ω) ^ 2 + (J p.2 ω) ^ 2) - 2 * (J p.1 ω * J p.2 ω) := by ring
  calc
    (∫ ω, (J p.1 ω) ^ 2 ∂P) + (∫ ω, (J p.2 ω) ^ 2 ∂P) -
        2 * ∫ ω, J p.1 ω * J p.2 ω ∂P =
        ∫ ω, (J p.1 ω - J p.2 ω) ^ 2 ∂P := by
          symm
          calc
            ∫ ω, (J p.1 ω - J p.2 ω) ^ 2 ∂P =
                ∫ ω, ((J p.1 ω) ^ 2 + (J p.2 ω) ^ 2) -
                  2 * (J p.1 ω * J p.2 ω) ∂P := by
                    apply integral_congr_ae
                    exact ae_of_all P hpoint
            _ = (∫ ω, (J p.1 ω) ^ 2 ∂P) + (∫ ω, (J p.2 ω) ^ 2 ∂P) -
                  2 * ∫ ω, J p.1 ω * J p.2 ω ∂P := by
                    rw [integral_sub hsum hcross, integral_add (hsq p.1) (hsq p.2),
                      integral_const_mul]

/-- For two cutoff families, matching diagonal and mixed second moments imply that every mixed
mean-square difference tends to zero. -/
theorem compatible_mixed_cutoff_L2_cauchy_of_second_moment_limits
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (J : Bool → ℝ → Ω → ℝ) (L : ℝ)
    (hsq : ∀ b r, Integrable (fun ω => (J b r ω) ^ 2) P)
    (hmul : ∀ b b' r s, Integrable (fun ω => J b r ω * J b' s ω) P)
    (hdiag : ∀ b, Tendsto (fun r => ∫ ω, (J b r ω) ^ 2 ∂P) atTop (𝓝 L))
    (hmixed : ∀ b b', Tendsto
      (fun p : ℝ × ℝ => ∫ ω, J b p.1 ω * J b' p.2 ω ∂P)
      (atTop ×ˢ atTop) (𝓝 L)) :
    ∀ b b', Tendsto
      (fun p : ℝ × ℝ => ∫ ω, (J b p.1 ω - J b' p.2 ω) ^ 2 ∂P)
      (atTop ×ˢ atTop) (𝓝 0) := by
  intro b b'
  have hdiag₁ : Tendsto
      (fun p : ℝ × ℝ => ∫ ω, (J b p.1 ω) ^ 2 ∂P)
      (atTop ×ˢ atTop) (𝓝 L) := (hdiag b).comp tendsto_fst
  have hdiag₂ : Tendsto
      (fun p : ℝ × ℝ => ∫ ω, (J b' p.2 ω) ^ 2 ∂P)
      (atTop ×ˢ atTop) (𝓝 L) := (hdiag b').comp tendsto_snd
  have hcross₂ : Tendsto
      (fun p : ℝ × ℝ => 2 * ∫ ω, J b p.1 ω * J b' p.2 ω ∂P)
      (atTop ×ˢ atTop) (𝓝 (2 * L)) := by
    simpa using (hmixed b b').const_mul (2 : ℝ)
  have hlim : Tendsto
      (fun p : ℝ × ℝ =>
        (∫ ω, (J b p.1 ω) ^ 2 ∂P) + (∫ ω, (J b' p.2 ω) ^ 2 ∂P) -
          2 * ∫ ω, J b p.1 ω * J b' p.2 ω ∂P)
      (atTop ×ˢ atTop) (𝓝 0) := by
    have hsum := hdiag₁.add hdiag₂
    have hsub := hsum.sub hcross₂
    convert hsub using 1
    ring_nf
  apply hlim.congr'
  filter_upwards [] with p
  have hsum : Integrable (fun ω => (J b p.1 ω) ^ 2 + (J b' p.2 ω) ^ 2) P :=
    (hsq b p.1).add (hsq b' p.2)
  have hcross : Integrable (fun ω => 2 * (J b p.1 ω * J b' p.2 ω)) P :=
    (hmul b b' p.1 p.2).const_mul 2
  have hpoint (ω : Ω) :
      (J b p.1 ω - J b' p.2 ω) ^ 2 =
        ((J b p.1 ω) ^ 2 + (J b' p.2 ω) ^ 2) -
          2 * (J b p.1 ω * J b' p.2 ω) := by ring
  calc
    (∫ ω, (J b p.1 ω) ^ 2 ∂P) + (∫ ω, (J b' p.2 ω) ^ 2 ∂P) -
        2 * ∫ ω, J b p.1 ω * J b' p.2 ω ∂P =
        ∫ ω, (J b p.1 ω - J b' p.2 ω) ^ 2 ∂P := by
          symm
          calc
            ∫ ω, (J b p.1 ω - J b' p.2 ω) ^ 2 ∂P =
                ∫ ω, ((J b p.1 ω) ^ 2 + (J b' p.2 ω) ^ 2) -
                  2 * (J b p.1 ω * J b' p.2 ω) ∂P := by
                    apply integral_congr_ae
                    exact ae_of_all P hpoint
            _ = (∫ ω, (J b p.1 ω) ^ 2 ∂P) + (∫ ω, (J b' p.2 ω) ^ 2 ∂P) -
                  2 * ∫ ω, J b p.1 ω * J b' p.2 ω ∂P := by
                    rw [integral_sub hsum hcross, integral_add (hsq b p.1) (hsq b' p.2),
                      integral_const_mul]


end DOZZ.Proofs
