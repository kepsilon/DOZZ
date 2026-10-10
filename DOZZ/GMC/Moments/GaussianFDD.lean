/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteGaussianTilt

/-! Equality of finite-dimensional laws for centered jointly Gaussian families. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DOZZ.Proofs

/-- Adding one independent centered Gaussian coordinate to every entry of a centered jointly
Gaussian family preserves joint Gaussianity. The common-coordinate dependence is retained. -/
theorem isCenteredJointlyGaussian_add_independent_scalar
    {Ω Λ ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    [Fintype ι] {P : Measure Ω} {Q : Measure Λ} [IsProbabilityMeasure Q]
    (X : Ω → ι → ℝ) (W : Λ → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian P X)
    {σ : ℝ≥0} (hW : HasLaw W (gaussianReal 0 σ) Q) :
    DOZZ.IsCenteredJointlyGaussian (P.prod Q)
      (fun p i => X p.1 i + W p.2) := by
  classical
  let : IsProbabilityMeasure P := hX.1
  refine ⟨inferInstance, ?_, ?_⟩
  · intro i
    have hfst : Measure.map Prod.fst (P.prod Q) = P := measurePreserving_fst.map_eq
    have hsnd : Measure.map Prod.snd (P.prod Q) = Q := measurePreserving_snd.map_eq
    have hXi : AEMeasurable (fun p : Ω × Λ => X p.1 i) (P.prod Q) := by
      have hm : AEMeasurable (fun ω => X ω i) (Measure.map Prod.fst (P.prod Q)) := by
        rw [hfst]
        exact hX.2.1 i
      exact hm.comp_measurable measurable_fst
    have hWi : AEMeasurable (fun p : Ω × Λ => W p.2) (P.prod Q) := by
      have hm : AEMeasurable W (Measure.map Prod.snd (P.prod Q)) := by
        rw [hsnd]
        exact hW.aemeasurable
      exact hm.comp_measurable measurable_snd
    exact hXi.add hWi
  · intro a
    obtain ⟨hUm, ⟨vU, hUmap⟩⟩ := hX.2.2 a
    let U : Ω → ℝ := fun ω => ∑ i, a i * X ω i
    let S : ℝ := ∑ i, a i
    let V : Λ → ℝ := fun ω => S * W ω
    let vV : ℝ≥0 := NNReal.mk (S ^ 2) (sq_nonneg S) * σ
    have hUlaw : HasLaw U (gaussianReal 0 vU) P := ⟨hUm.aemeasurable, hUmap⟩
    have hVlaw : HasLaw V (gaussianReal 0 vV) Q := by
      simpa [V, vV, zero_mul] using gaussianReal_const_mul hW S
    have hUprod : HasLaw (fun p : Ω × Λ => U p.1) (gaussianReal 0 vU) (P.prod Q) :=
      hUlaw.comp measurePreserving_fst.hasLaw
    have hVprod : HasLaw (fun p : Ω × Λ => V p.2) (gaussianReal 0 vV) (P.prod Q) :=
      hVlaw.comp measurePreserving_snd.hasLaw
    have hIndep : (fun p : Ω × Λ => U p.1) ⟂ᵢ[P.prod Q]
        (fun p => V p.2) := indepFun_prod₀ hUm.aemeasurable hVlaw.aemeasurable
    have hSumLaw : HasLaw (fun p : Ω × Λ => U p.1 + V p.2)
        (gaussianReal 0 (vU + vV)) (P.prod Q) := by
      refine ⟨?_, ?_⟩
      · exact hUprod.aemeasurable.add hVprod.aemeasurable
      · convert gaussianReal_add_gaussianReal_of_indepFun hIndep hUprod hVprod using 1; simp
    have hsum : (fun p : Ω × Λ => ∑ i, a i * (X p.1 i + W p.2)) =
        fun p => U p.1 + V p.2 := by
      funext p
      calc
        (∑ i, a i * (X p.1 i + W p.2)) =
            ∑ i, (a i * X p.1 i + a i * W p.2) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (∑ i, a i * X p.1 i) + ∑ i, a i * W p.2 := Finset.sum_add_distrib
        _ = U p.1 + V p.2 := by
          dsimp [U, V, S]
          rw [Finset.sum_mul]
    have hsumLp : MemLp (fun p : Ω × Λ => ∑ i, a i * (X p.1 i + W p.2)) 2 (P.prod Q) := by
      rw [hsum]
      exact hSumLaw.memLp (ProbabilityTheory.memLp_id_gaussianReal 2)
    refine ⟨hsumLp, ⟨vU + vV, ?_⟩⟩
    rw [hsum]
    exact hSumLaw.map_eq

/-- Centered jointly Gaussian finite families with the same covariance matrix have the same
law. The result is stated on the ordinary function space, which is the interface used by the
finite-dimensional chaos-law transfer lemma. -/
theorem map_eq_of_centeredJointlyGaussian_of_covariance_eq
    {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) (P' : Measure Ω') (X : Ω → ι → ℝ) (Y : Ω' → ι → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian P X)
    (hY : DOZZ.IsCenteredJointlyGaussian P' Y)
    (hcov : ∀ i j, DOZZ.gaussianCovariance P (fun ω => X ω i) (fun ω => X ω j) =
      DOZZ.gaussianCovariance P' (fun ω => Y ω i) (fun ω => Y ω j)) :
    Measure.map X P = Measure.map Y P' := by
  classical
  obtain ⟨SX, hSX, hXLaw, hXEntry⟩ := represent P X hX
  obtain ⟨SY, hSY, hYLaw, hYEntry⟩ := represent P' Y hY
  have hS : SX = SY := by
    ext i j
    rw [hXEntry, hYEntry, hcov]
  let Xe : Ω → EuclideanSpace ℝ ι := fun ω => WithLp.toLp 2 (X ω)
  let Ye : Ω' → EuclideanSpace ℝ ι := fun ω => WithLp.toLp 2 (Y ω)
  have hXeu : Measure.map Xe P = multivariateGaussian 0 SX := by
    simpa only [Xe] using hXLaw
  have hYeu : Measure.map Ye P' = multivariateGaussian 0 SY := by
    simpa only [Ye] using hYLaw
  have hE : Measure.map Xe P = Measure.map Ye P' := by
    rw [hXeu, hYeu, hS]
  have hXmeas : AEMeasurable Xe P := by
    exact (WithLp.measurable_toLp 2 (ι → ℝ)).aemeasurable.comp_aemeasurable
      (by apply AEMeasurable.of_eval; intro i; exact hX.2.1 i)
  have hYmeas : AEMeasurable Ye P' := by
    exact (WithLp.measurable_toLp 2 (ι → ℝ)).aemeasurable.comp_aemeasurable
      (by apply AEMeasurable.of_eval; intro i; exact hY.2.1 i)
  have hXraw : Measure.map X P = (Measure.map Xe P).map (fun z : EuclideanSpace ℝ ι => z.ofLp) := by
    rw [AEMeasurable.map_map_of_aemeasurable
      (WithLp.measurable_ofLp 2 (ι → ℝ)).aemeasurable hXmeas]
    congr 1
  have hYraw : Measure.map Y P' = (Measure.map Ye P').map (fun z : EuclideanSpace ℝ ι => z.ofLp) := by
    rw [AEMeasurable.map_map_of_aemeasurable
      (WithLp.measurable_ofLp 2 (ι → ℝ)).aemeasurable hYmeas]
    congr 1
  rw [hXraw, hYraw, hE]

end DOZZ.Proofs
