/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.CircleEnergyGapBilinear
public import DOZZ.GMC.Construction.CircleAverageL2Family

/-!
# Covariance of the canonical circle L² family

Mixed test energies converge to the double-circle kernel pairing. Consequently the coordinatewise
L² limits are centered, jointly Gaussian, and have the geometric covariance needed for
Kolmogorov continuity.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace DOZZ.Proofs

/-- The coordinatewise L² circle limits have their deterministic double-circle covariance. -/
theorem exists_equatorGFF_circle_L2_geometry
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : Ω → Distr) (hX : IsEquatorGFF P X) :
    ∃ f : (ℂ × ℝ) → ℕ → TestFn, ∃ W : (ℂ × ℝ) → Lp ℝ 2 P,
    ∃ Y : (ℂ × ℝ) → Ω → ℝ,
      (∀ p, Tendsto (fun n => circleEnergyGap p.1 p.2 (f p n)) atTop (𝓝 0)) ∧
      (∀ p y s, Tendsto (fun n => circleCross y s (f p n)) atTop
        (𝓝 (∫ z, ∫ w, gffKernel z w ∂circleMeasure y s ∂circleMeasure p.1 p.2))) ∧
      (∀ p, Tendsto (fun n => (equatorGFF_test_memLp X hX (f p n)).toLp
        (fun ω => X ω (f p n))) atTop (𝓝 (W p))) ∧
      (∀ p, Measurable[equatorGFFRawDistributionSigma X] (Y p) ∧
        Measurable (Y p) ∧ MemLp (Y p) 2 P ∧ Y p =ᵐ[P] ⇑(W p) ∧
          Tendsto (fun n => eLpNorm (fun ω => X ω (f p n) - Y p ω) 2 P)
            atTop (𝓝 0)) ∧
      IsGaussianProcess (fun p ω => Y p ω) P ∧
      (∀ p, (∫ ω, Y p ω ∂P) = 0) ∧
      (∀ p q, covariance (Y p) (Y q) P =
        ∫ z, ∫ w, gffKernel z w ∂circleMeasure p.1 p.2 ∂circleMeasure q.1 q.2) := by
  let : IsProbabilityMeasure P := hX.1
  obtain ⟨f, W, Y, hgap, hcross, hW, hY, hproc⟩ := exists_equatorGFF_circle_L2_family X hX
  refine ⟨f, W, Y, hgap, hcross, hW, hY, hproc, ?_, ?_⟩
  · intro p
    apply integral_eq_zero_of_eLpNorm_sub
      (fun n => equatorGFF_test_memLp X hX (f p n)) (hY p).2.2.1
      (fun n => equatorGFF_test_integral X hX (f p n)) (hY p).2.2.2.2
  · intro p q
    have henergyErr : Tendsto
        (fun n => gffCov (f p n) (f q n) - circleCross p.1 p.2 (f q n)) atTop (𝓝 0) :=
      tendsto_gffCov_test_circleCross_of_gap p.1 p.2 q.1 q.2 (f p) (f q)
        (hgap p) (hgap q) (by
          simpa only [circleSelfEnergy] using (hcross q q.1 q.2))
    have hpair : Tendsto (fun n => gffCov (f p n) (f q n)) atTop
        (𝓝 (∫ z, ∫ w, gffKernel z w ∂circleMeasure p.1 p.2
          ∂circleMeasure q.1 q.2)) := by
      have h := henergyErr.add (hcross q p.1 p.2)
      have he n : (gffCov (f p n) (f q n) - circleCross p.1 p.2 (f q n)) +
          circleCross p.1 p.2 (f q n) = gffCov (f p n) (f q n) := by ring
      have h' := h.congr' (Filter.Eventually.of_forall he)
      simpa only [zero_add] using h'
    have hcovlim := tendsto_covariance_of_eLpNorm_sub
      (fun n => equatorGFF_test_memLp X hX (f p n))
      (fun n => equatorGFF_test_memLp X hX (f q n))
      (hY p).2.2.1 (hY q).2.2.1 (hY p).2.2.2.2 (hY q).2.2.2.2
    have hcovseq : Tendsto
        (fun n => covariance (fun ω => X ω (f p n)) (fun ω => X ω (f q n)) P)
        atTop (𝓝 (covariance (Y p) (Y q) P)) := hcovlim
    have hcovseq' := hcovseq.congr' (Filter.Eventually.of_forall fun n =>
      equatorGFF_test_covariance X hX (f p n) (f q n))
    exact tendsto_nhds_unique hcovseq' hpair

end DOZZ.Proofs
