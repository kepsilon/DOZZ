/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.TorusH2CoefficientCLM
public import DOZZ.GFF.LocalModeFunctional
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# DOZZ.GFF.TorusLocalDistribution

On each concrete torus chart, square-summable random Fourier coordinates define a continuous
linear functional. The scalar evaluation is also defined as a measurable limit of finite Fourier
sums, so it remains measurable before restricting to the full-measure square-summability event.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace Topology lp

namespace DOZZ

/-- A square-summable complex sequence as an element of complex `ℓ²`. -/
noncomputable def gffComplexLpOfSummableNormSquares {ι : Type*} (f : ι → ℂ)
    (h : Summable fun i => ‖f i‖ ^ 2) : lp (fun _ : ι => ℂ) (2 : ℝ≥0∞) := by
  have hmem : Memℓp f (2 : ℝ≥0∞) := by
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simpa using h
  exact ⟨f, hmem⟩

/-- The complex local random mode vector. Its coordinates are the normalized cosine evaluation
minus `i` times the normalized sine evaluation. -/
noncomputable def equatorHaarCommonComplexEvalLp (R : ℕ)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)
    (hcos : Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω) ^ 2)
    (hsin : Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω) ^ 2) :
    lp (fun _ : Fin 2 → ℤ => ℂ) (2 : ℝ≥0∞) := by
  let b : (Fin 2 → ℤ) → ℂ := fun k =>
    (equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω : ℂ) -
      Complex.I * (equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω : ℂ)
  have hpoint (k : Fin 2 → ℤ) : ‖b k‖ ^ 2 =
      (equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω) ^ 2 +
        (equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [b, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  have hb : Summable fun k : Fin 2 → ℤ => ‖b k‖ ^ 2 := by
    refine (hcos.add hsin).congr fun k => ?_
    rw [hpoint]
  exact gffComplexLpOfSummableNormSquares b hb

@[simp]
theorem equatorHaarCommonComplexEvalLp_apply (R : ℕ)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)
    (hcos : Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω) ^ 2)
    (hsin : Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω) ^ 2)
    (k : Fin 2 → ℤ) :
    equatorHaarCommonComplexEvalLp R ω hcos hsin k =
      (equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω : ℂ) -
        Complex.I * (equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω : ℂ) := rfl

/-- Pair a local complex Fourier coefficient vector with the sample's complex mode vector and
take the real component. -/
noncomputable def equatorLocalFourierPairingCLM (R : ℕ)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)
    (hcos : Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω) ^ 2)
    (hsin : Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω) ^ 2) :
    lp (fun _ : Fin 2 → ℤ => ℂ) (2 : ℝ≥0∞) →L[ℝ] ℝ :=
  Complex.reCLM.comp (ContinuousLinearMap.restrictScalars ℝ
    (innerSL ℂ (equatorHaarCommonComplexEvalLp R ω hcos hsin)))

@[simp]
theorem equatorLocalFourierPairingCLM_apply (R : ℕ)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)
    (hcos : Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω) ^ 2)
    (hsin : Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω) ^ 2)
    (c : lp (fun _ : Fin 2 → ℤ => ℂ) (2 : ℝ≥0∞)) :
    equatorLocalFourierPairingCLM R ω hcos hsin c =
      (⟪equatorHaarCommonComplexEvalLp R ω hcos hsin, c⟫_ℂ).re := rfl

/-- The local chart distribution obtained by pairing the sample mode vector with the weighted
Fourier coefficient map. -/
noncomputable def equatorLocalFourierDistributionCLM (R : ℕ)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)
    (hcos : Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω) ^ 2)
    (hsin : Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω) ^ 2) :
    TestFn →L[ℝ] ℝ :=
  (equatorLocalFourierPairingCLM R ω hcos hsin).comp
    (torusH2WeightedFourierCoeffCLM (gffLocalModeBoxSide R))

/-- A finite Fourier sum for one test, written in real cosine and sine coordinates. -/
noncomputable def equatorLocalFourierPartialEval (R : ℕ) (f : TestFn)
    (s : Finset (Fin 2 → ℤ))
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2) : ℝ :=
  s.sum fun k =>
    (torusH2WeightedFourierCoeffCLM (gffLocalModeBoxSide R) f k).re *
        equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω -
        (torusH2WeightedFourierCoeffCLM (gffLocalModeBoxSide R) f k).im *
          equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω

theorem equatorLocalFourierPartialEval_insert (R : ℕ) (f : TestFn)
    (s : Finset (Fin 2 → ℤ)) (k : Fin 2 → ℤ) (hk : k ∉ s)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2) :
    equatorLocalFourierPartialEval R f (insert k s) ω =
      ((torusH2WeightedFourierCoeffCLM (gffLocalModeBoxSide R) f k).re *
          equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω -
        (torusH2WeightedFourierCoeffCLM (gffLocalModeBoxSide R) f k).im *
          equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω) +
    equatorLocalFourierPartialEval R f s ω := by
  simp only [equatorLocalFourierPartialEval, Finset.sum_insert hk]

/-- The measurable scalar Fourier limit on a local chart, defined for every sample by a filter
limit of finite sums. -/
noncomputable def equatorLocalFourierEval (R : ℕ) (f : TestFn)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2) : ℝ :=
  limUnder atTop (equatorLocalFourierPartialEval R f · ω)

theorem measurable_equatorLocalFourierPartialEval (R : ℕ) (f : TestFn)
    (s : Finset (Fin 2 → ℤ)) :
    Measurable (equatorLocalFourierPartialEval R f s) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact measurable_const
  | @insert k s hk ih =>
      have hm : Measurable (fun ω =>
          (torusH2WeightedFourierCoeffCLM (gffLocalModeBoxSide R) f k).re *
              equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω -
            (torusH2WeightedFourierCoeffCLM (gffLocalModeBoxSide R) f k).im *
            equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω) := by
        exact (measurable_const.mul
          (measurable_equatorHaarCommonEval _)).sub
          (measurable_const.mul (measurable_equatorHaarCommonEval _))
      have heq : equatorLocalFourierPartialEval R f (insert k s) = fun ω =>
          (torusH2WeightedFourierCoeffCLM (gffLocalModeBoxSide R) f k).re *
              equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω -
            (torusH2WeightedFourierCoeffCLM (gffLocalModeBoxSide R) f k).im *
              equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω +
            equatorLocalFourierPartialEval R f s ω := by
        funext ω
        exact equatorLocalFourierPartialEval_insert R f s k hk ω
      rw [heq]
      exact hm.add ih

theorem measurable_equatorLocalFourierEval (R : ℕ) (f : TestFn) :
    Measurable (equatorLocalFourierEval R f) := by
  have hstrong : ∀ s : Finset (Fin 2 → ℤ),
      StronglyMeasurable (equatorLocalFourierPartialEval R f s) :=
    fun s => (measurable_equatorLocalFourierPartialEval R f s).stronglyMeasurable
  exact (StronglyMeasurable.limUnder (l := atTop) hstrong).measurable

/-- The finite real Fourier pairing is the real part of the complex `ℓ²` inner product. -/
theorem hasSum_equatorLocalFourierPartialEval (R : ℕ) (f : TestFn)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)
    (hcos : Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω) ^ 2)
    (hsin : Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω) ^ 2) :
    HasSum (fun k : Fin 2 → ℤ =>
      (torusH2WeightedFourierCoeffCLM (gffLocalModeBoxSide R) f k).re *
          equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω -
        (torusH2WeightedFourierCoeffCLM (gffLocalModeBoxSide R) f k).im *
          equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω)
      (equatorLocalFourierPairingCLM R ω hcos hsin
        (torusH2WeightedFourierCoeffCLM (gffLocalModeBoxSide R) f)) := by
  let b := equatorHaarCommonComplexEvalLp R ω hcos hsin
  let c := torusH2WeightedFourierCoeffCLM (gffLocalModeBoxSide R) f
  have hinner : HasSum (fun k : Fin 2 → ℤ => ⟪b k, c k⟫_ℂ) ⟪b, c⟫_ℂ :=
    lp.hasSum_inner b c
  have hreal := hinner.mapL Complex.reCLM
  have hterms (k : Fin 2 → ℤ) : (⟪b k, c k⟫_ℂ).re =
      (torusH2WeightedFourierCoeffCLM (gffLocalModeBoxSide R) f k).re *
          equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω -
    (torusH2WeightedFourierCoeffCLM (gffLocalModeBoxSide R) f k).im *
          equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω := by
    rw [RCLike.inner_apply]
    change (c k * star
      ((equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω : ℂ) -
        Complex.I * (equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω : ℂ))).re = _
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have hsum : HasSum (fun k : Fin 2 → ℤ =>
      (torusH2WeightedFourierCoeffCLM (gffLocalModeBoxSide R) f k).re *
          equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω -
        (torusH2WeightedFourierCoeffCLM (gffLocalModeBoxSide R) f k).im *
          equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω)
      (Complex.re ⟪b, c⟫_ℂ) := by
    change HasSum (fun k : Fin 2 → ℤ => (⟪b k, c k⟫_ℂ).re)
      ((⟪b, c⟫_ℂ).re) at hreal
    simpa only [hterms] using hreal
  simpa [b, c, equatorLocalFourierPairingCLM_apply] using hsum

/-- On the square-summability event, the measurable local scalar limit equals the continuous
Fourier-pairing functional. -/
theorem equatorLocalFourierEval_eq_distributionCLM_apply (R : ℕ) (f : TestFn)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)
    (hcos : Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω) ^ 2)
    (hsin : Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω) ^ 2) :
    equatorLocalFourierEval R f ω =
      equatorLocalFourierDistributionCLM R ω hcos hsin f := by
  have hsum := hasSum_equatorLocalFourierPartialEval R f ω hcos hsin
  have hlim : Tendsto (fun s => equatorLocalFourierPartialEval R f s ω) atTop
      (𝓝 ((equatorLocalFourierPairingCLM R ω hcos hsin)
        (torusH2WeightedFourierCoeffCLM (gffLocalModeBoxSide R) f))) := by
    exact hsum
  change limUnder atTop (equatorLocalFourierPartialEval R f · ω) = _
  rw [hlim.limUnder_eq]
  rfl

/-- The nonnegative extended-real square sum of the local cosine coordinates. -/
noncomputable def equatorHaarCommonCosEnergyTsum (R : ℕ)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2) : ℝ≥0∞ :=
  ∑' k : Fin 2 → ℤ,
    ENNReal.ofReal ((equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω : ℝ) ^ 2)

/-- The nonnegative extended-real square sum of the local sine coordinates. -/
noncomputable def equatorHaarCommonSinEnergyTsum (R : ℕ)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2) : ℝ≥0∞ :=
  ∑' k : Fin 2 → ℤ,
    ENNReal.ofReal ((equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω : ℝ) ^ 2)

/-- The common full-measure event on which every local cosine and sine coordinate sequence is in
`ℓ²`. The definition by extended-real sums makes the event measurable. -/
def equatorHaarCommonGood (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2) : Prop :=
  ∀ R : ℕ, equatorHaarCommonCosEnergyTsum R ω ≠ ∞ ∧
    equatorHaarCommonSinEnergyTsum R ω ≠ ∞

theorem measurable_equatorHaarCommonCosEnergyTsum (R : ℕ) :
    Measurable (equatorHaarCommonCosEnergyTsum R) := by
  apply Measurable.tsum
  intro k
  exact ENNReal.measurable_ofReal.comp
    ((measurable_equatorHaarCommonEval _).pow_const 2)

theorem measurable_equatorHaarCommonSinEnergyTsum (R : ℕ) :
    Measurable (equatorHaarCommonSinEnergyTsum R) := by
  apply Measurable.tsum
  intro k
  exact ENNReal.measurable_ofReal.comp
    ((measurable_equatorHaarCommonEval _).pow_const 2)

theorem measurableSet_equatorHaarCommonGood :
    MeasurableSet {ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2 |
      equatorHaarCommonGood ω} := by
  change MeasurableSet {ω | ∀ R : ℕ,
    equatorHaarCommonCosEnergyTsum R ω ≠ ∞ ∧
      equatorHaarCommonSinEnergyTsum R ω ≠ ∞}
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun (R : ℕ) => ?_
  rw [Set.ofPred_and]
  refine MeasurableSet.inter ?_ ?_
  · exact MeasurableSet.preimage (MeasurableSet.compl (measurableSet_singleton ∞))
      (measurable_equatorHaarCommonCosEnergyTsum R)
  · exact MeasurableSet.preimage (MeasurableSet.compl (measurableSet_singleton ∞))
      (measurable_equatorHaarCommonSinEnergyTsum R)

theorem equatorHaarCommonCosEnergyTsum_ne_top_of_summable (R : ℕ)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)
    (h : Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω) ^ 2) :
    equatorHaarCommonCosEnergyTsum R ω ≠ ∞ := by
  unfold equatorHaarCommonCosEnergyTsum
  exact h.tsum_ofReal_ne_top

theorem equatorHaarCommonSinEnergyTsum_ne_top_of_summable (R : ℕ)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)
    (h : Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω) ^ 2) :
    equatorHaarCommonSinEnergyTsum R ω ≠ ∞ := by
  unfold equatorHaarCommonSinEnergyTsum
  exact h.tsum_ofReal_ne_top

theorem ae_equatorHaarCommonGood :
    ∀ᵐ ω ∂GaussianFields.scaleSpaceWhiteNoiseMeasure 2,
      equatorHaarCommonGood ω := by
  have hcos : ∀ᵐ ω ∂GaussianFields.scaleSpaceWhiteNoiseMeasure 2,
      ∀ R : ℕ, Summable fun k : Fin 2 → ℤ =>
        (equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω) ^ 2 :=
    ae_all_iff.mpr ae_summable_equatorHaarCommonCosEval
  have hsin : ∀ᵐ ω ∂GaussianFields.scaleSpaceWhiteNoiseMeasure 2,
      ∀ R : ℕ, Summable fun k : Fin 2 → ℤ =>
        (equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω) ^ 2 :=
    ae_all_iff.mpr ae_summable_equatorHaarCommonSinEval
  filter_upwards [hcos, hsin] with ω hcos hsin
  change ∀ R : ℕ,
    equatorHaarCommonCosEnergyTsum R ω ≠ ∞ ∧
      equatorHaarCommonSinEnergyTsum R ω ≠ ∞
  intro R
  constructor
  · exact equatorHaarCommonCosEnergyTsum_ne_top_of_summable R ω (hcos R)
  · exact equatorHaarCommonSinEnergyTsum_ne_top_of_summable R ω (hsin R)

theorem equatorHaarCommonCosEval_summable_of_good (R : ℕ)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)
    (hω : equatorHaarCommonGood ω) :
    Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalCosSobolevModeTest R k) ω) ^ 2 := by
  change ∀ R : ℕ,
    equatorHaarCommonCosEnergyTsum R ω ≠ ∞ ∧
      equatorHaarCommonSinEnergyTsum R ω ≠ ∞ at hω
  have h := ENNReal.summable_toReal (hω R).1
  simpa only [equatorHaarCommonCosEnergyTsum, ENNReal.toReal_ofReal (sq_nonneg _)] using h

theorem equatorHaarCommonSinEval_summable_of_good (R : ℕ)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)
    (hω : equatorHaarCommonGood ω) :
    Summable fun k : Fin 2 → ℤ =>
      (equatorHaarCommonEval (gffLocalSinSobolevModeTest R k) ω) ^ 2 := by
  change ∀ R : ℕ,
    equatorHaarCommonCosEnergyTsum R ω ≠ ∞ ∧
      equatorHaarCommonSinEnergyTsum R ω ≠ ∞ at hω
  have h := ENNReal.summable_toReal (hω R).2
  simpa only [equatorHaarCommonSinEnergyTsum, ENNReal.toReal_ofReal (sq_nonneg _)] using h

end DOZZ

end
