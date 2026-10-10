/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosGaussianLaplace

/-! Finite Laplace Kahane comparison for arbitrary finite index types. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal

namespace DOZZ.Proofs

/-- Reindexing a finite family preserves centered joint Gaussianity. -/
theorem centeredJointlyGaussian_reindex
    {Ω κ ι : Type*} [MeasurableSpace Ω] [Fintype κ] [Fintype ι]
    (P : Measure Ω) (e : κ ≃ ι) (Z : Ω → ι → ℝ)
    (hZ : DOZZ.IsCenteredJointlyGaussian P Z) :
    DOZZ.IsCenteredJointlyGaussian P (fun ω k => Z ω (e k)) := by
  refine ⟨hZ.1, ?_, ?_⟩
  · intro k
    exact hZ.2.1 (e k)
  · intro a
    let b : ι → ℝ := fun i => a (e.symm i)
    have hsum (ω : Ω) :
        (∑ k, a k * Z ω (e k)) = ∑ i, b i * Z ω i := by
      calc
        ∑ k, a k * Z ω (e k) = ∑ i, (a (e.symm i) * Z ω (e (e.symm i))) :=
          (e.symm.sum_comp (fun k => a k * Z ω (e k))).symm
        _ = ∑ i, b i * Z ω i := by simp [b]
    have hsumFun : (fun ω => ∑ k, a k * Z ω (e k)) =
        fun ω => ∑ i, b i * Z ω i := funext hsum
    obtain ⟨v, hmap⟩ := (hZ.2.2 b).2
    refine ⟨hsumFun ▸ (hZ.2.2 b).1, v, ?_⟩
    rw [hsumFun]
    exact hmap

/-- The finite Laplace Kahane comparison for arbitrary finite families of coordinates. Empty
families have zero chaos mass; nonempty families are reindexed by `Fin (card ι)`. -/
theorem kahane_finite_laplace_lintegral_fintype
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian PX X) (hY : DOZZ.IsCenteredJointlyGaussian PY Y)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ s : ℝ) (hs : 0 ≤ s)
    (hcov : ∀ i j, DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
      DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-s * DOZZ.finiteChaosMass PX X a γ ω)) ∂PX ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-s * DOZZ.finiteChaosMass PY Y a γ ω)) ∂PY := by
  classical
  by_cases hι : Nonempty ι
  · have hcardNe : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
    have hcardLe : 1 ≤ Fintype.card ι := Nat.one_le_iff_ne_zero.mpr hcardNe
    let n : ℕ := Fintype.card ι - 1
    have hcard : Fintype.card ι = n + 1 := by
      dsimp [n]
      omega
    let e : Fin (n + 1) ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
    let X' : ΩX → Fin (n + 1) → ℝ := fun ω i => X ω (e i)
    let Y' : ΩY → Fin (n + 1) → ℝ := fun ω i => Y ω (e i)
    let a' : Fin (n + 1) → ℝ := fun i => a (e i)
    have hX' := centeredJointlyGaussian_reindex PX e X hX
    have hY' := centeredJointlyGaussian_reindex PY e Y hY
    have ha' : ∀ i, 0 ≤ a' i := fun i => ha (e i)
    have hcov' : ∀ i j, DOZZ.gaussianCovariance PX (fun ω => X' ω i)
        (fun ω => X' ω j) ≤ DOZZ.gaussianCovariance PY (fun ω => Y' ω i)
          (fun ω => Y' ω j) := by
      intro i j
      exact hcov (e i) (e j)
    have hmassX (ω : ΩX) : DOZZ.finiteChaosMass PX X' a' γ ω =
        DOZZ.finiteChaosMass PX X a γ ω := by
      simp only [DOZZ.finiteChaosMass, X', a']
      exact e.sum_comp (fun i => a i * Real.exp
        (γ * X ω i - γ ^ 2 / 2 * DOZZ.gaussianVariance PX (fun ω => X ω i)))
    have hmassY (ω : ΩY) : DOZZ.finiteChaosMass PY Y' a' γ ω =
        DOZZ.finiteChaosMass PY Y a γ ω := by
      simp only [DOZZ.finiteChaosMass, Y', a']
      exact e.sum_comp (fun i => a i * Real.exp
        (γ * Y ω i - γ ^ 2 / 2 * DOZZ.gaussianVariance PY (fun ω => Y ω i)))
    have hfin := kahane_finite_laplace_lintegral PX PY X' Y' hX' hY' a' ha' γ s hs hcov'
    have hconvertX : (∫⁻ ω, ENNReal.ofReal
        (Real.exp (-s * DOZZ.finiteChaosMass PX X' a' γ ω)) ∂PX) =
        ∫⁻ ω, ENNReal.ofReal
          (Real.exp (-s * DOZZ.finiteChaosMass PX X a γ ω)) ∂PX := by
      apply lintegral_congr_ae
      exact ae_of_all PX fun ω => by simp only [hmassX ω]
    have hconvertY : (∫⁻ ω, ENNReal.ofReal
        (Real.exp (-s * DOZZ.finiteChaosMass PY Y' a' γ ω)) ∂PY) =
        ∫⁻ ω, ENNReal.ofReal
          (Real.exp (-s * DOZZ.finiteChaosMass PY Y a γ ω)) ∂PY := by
      apply lintegral_congr_ae
      exact ae_of_all PY fun ω => by simp only [hmassY ω]
    rw [← hconvertX, ← hconvertY]
    exact hfin
  · have hmassX (ω : ΩX) : DOZZ.finiteChaosMass PX X a γ ω = 0 := by
      have huniv : (Finset.univ : Finset ι) = ∅ :=
        Finset.eq_empty_iff_forall_notMem.mpr (fun i _ => hι ⟨i⟩)
      simp [DOZZ.finiteChaosMass, huniv]
    have hmassY (ω : ΩY) : DOZZ.finiteChaosMass PY Y a γ ω = 0 := by
      have huniv : (Finset.univ : Finset ι) = ∅ :=
        Finset.eq_empty_iff_forall_notMem.mpr (fun i _ => hι ⟨i⟩)
      simp [DOZZ.finiteChaosMass, huniv]
    simp only [hmassX, hmassY, mul_zero, Real.exp_zero, ENNReal.ofReal_one,
      lintegral_const, hX.1.measure_univ, hY.1.measure_univ, one_mul]
    exact le_rfl


end DOZZ.Proofs
