/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosMultiLaplace
public import DOZZ.GMC.FiniteChaosMellin
public import DOZZ.GMC.FiniteMultiMellin
public import DOZZ.Statements.GMC.FiniteChaosMass
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Multiblock negative-power comparison from a multivariate Mellin formula. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped Distributions ENNReal

namespace DOZZ.Proofs

private theorem finiteChaosMass_aemeasurable
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : DOZZ.IsCenteredJointlyGaussian P Z)
    (a : ι → ℝ) (γ : ℝ) :
    AEMeasurable (fun ω => DOZZ.finiteChaosMass P Z a γ ω) P := by
  classical
  have hterm (i : ι) : AEMeasurable
      (fun ω => a i * Real.exp (γ * Z ω i - γ ^ 2 / 2 *
        DOZZ.gaussianVariance P (fun ω => Z ω i))) P := by
    have harg : AEMeasurable (fun ω => γ * Z ω i - γ ^ 2 / 2 *
        DOZZ.gaussianVariance P (fun ω => Z ω i)) P :=
      (hZ.2.1 i).const_mul γ |>.sub_const _
    exact (Real.measurable_exp.comp_aemeasurable harg).const_mul (a i)
  change AEMeasurable (fun ω => ∑ i, a i * Real.exp
    (γ * Z ω i - γ ^ 2 / 2 * DOZZ.gaussianVariance P (fun ω => Z ω i))) P
  exact Finset.aemeasurable_fun_sum _ fun i _ => hterm i

private theorem finiteChaosMass_nonneg
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (γ : ℝ) (ω : Ω) : 0 ≤ DOZZ.finiteChaosMass P Z a γ ω := by
  unfold DOZZ.finiteChaosMass
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (ha i) (Real.exp_nonneg _)

private theorem finiteChaosMultiNegativeProduct_eq_top_of_zero_block
    {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (block : ι → κ) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (γ : ℝ) (q : κ → ℝ) (hq : ∀ k, 0 ≤ q k)
    (k₀ : κ) (hq₀ : 0 < q k₀)
    (hzero : ∀ ω, DOZZ.finiteChaosMass P Z
      (fun i => if block i = k₀ then a i else 0) γ ω = 0)
    (hMassNN : ∀ ω k, 0 ≤ DOZZ.finiteChaosMass P Z
      (fun i => if block i = k then a i else 0) γ ω) :
    ∀ ω, ∏ k, ENNReal.rpow (ENNReal.ofReal
      (DOZZ.finiteChaosMass P Z (fun i => if block i = k then a i else 0) γ ω)) (-q k) = ∞ := by
  intro ω
  have hfactor_ne_zero (k : κ) : ENNReal.rpow (ENNReal.ofReal
      (DOZZ.finiteChaosMass P Z (fun i => if block i = k then a i else 0) γ ω))
      (-q k) ≠ 0 := by
    let ak : ι → ℝ := fun i => if block i = k then a i else 0
    have hak : ∀ i, 0 ≤ ak i := by
      intro i
      simp [ak]
      split_ifs <;> simp [ha]
    have hmass := hMassNN ω k
    by_cases hmass0 : DOZZ.finiteChaosMass P Z ak γ ω = 0
    · by_cases hq0 : q k = 0
      · simp [hq0]
      · have hqpos : 0 < q k := lt_of_le_of_ne (hq k) (Ne.symm hq0)
        have hmass0' : DOZZ.finiteChaosMass P Z
            (fun i => if block i = k then a i else 0) γ ω = 0 := by
          simpa [ak] using hmass0
        rw [hmass0']
        simp [ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr hqpos)]
    · have hmasspos : 0 < DOZZ.finiteChaosMass P Z ak γ ω :=
        lt_of_le_of_ne hmass (Ne.symm hmass0)
      change ENNReal.ofReal (DOZZ.finiteChaosMass P Z ak γ ω) ^ (-q k) ≠ 0
      rw [ENNReal.ofReal_rpow_of_pos hmasspos]
      exact (ne_of_gt (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos hmasspos _)))
  have hfactor_top : ENNReal.rpow (ENNReal.ofReal
      (DOZZ.finiteChaosMass P Z (fun i => if block i = k₀ then a i else 0) γ ω))
      (-q k₀) = ∞ := by
    rw [hzero ω]
    simp [ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr hq₀)]
  change (∏ k ∈ Finset.univ, ENNReal.rpow (ENNReal.ofReal
      (DOZZ.finiteChaosMass P Z (fun i => if block i = k then a i else 0) γ ω))
      (-q k)) = ∞
  exact WithTop.prod_eq_top (Finset.mem_univ k₀) hfactor_top
    (fun k hk => hfactor_ne_zero k)

/-- The multiblock negative-power comparison when every exponent is positive and each block has
positive total weight. -/
theorem kahane_finite_multi_negative_power_of_pos_weights
    {ΩX ΩY ι κ : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian PX X)
    (hY : DOZZ.IsCenteredJointlyGaussian PY Y)
    (block : ι → κ) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ : ℝ)
    (q : κ → ℝ) (hq : ∀ k, 0 < q k)
    (hweight : ∀ k, ∃ i, block i = k ∧ 0 < a i)
    (hcov : ∀ i j,
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
        DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)) :
    ∫⁻ ω, ∏ k, ENNReal.rpow (ENNReal.ofReal
        (DOZZ.finiteChaosMass PX X (fun i => if block i = k then a i else 0) γ ω)) (-q k) ∂PX ≤
      ∫⁻ ω, ∏ k, ENNReal.rpow (ENNReal.ofReal
        (DOZZ.finiteChaosMass PY Y (fun i => if block i = k then a i else 0) γ ω)) (-q k) ∂PY := by
  classical
  let : IsProbabilityMeasure PX := hX.1
  let : IsProbabilityMeasure PY := hY.1
  let b : κ → ι → ℝ := fun k i => if block i = k then a i else 0
  let mX : ΩX → κ → ℝ := fun ω k => DOZZ.finiteChaosMass PX X (b k) γ ω
  let mY : ΩY → κ → ℝ := fun ω k => DOZZ.finiteChaosMass PY Y (b k) γ ω
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let νκ : κ → Measure ℝ := fun _ => ν
  let T : Measure (κ → ℝ) := Measure.pi νκ
  let c : κ → ℝ≥0∞ := fun k => ENNReal.ofReal (1 / Real.Gamma (q k))
  let C : ℝ≥0∞ := ∏ k, c k
  let fX : ΩX → (κ → ℝ) → ℝ≥0∞ := fun ω t =>
    ∏ k, ENNReal.ofReal (t k ^ (q k - 1) * Real.exp (-(mX ω k * t k)))
  let fY : ΩY → (κ → ℝ) → ℝ≥0∞ := fun ω t =>
    ∏ k, ENNReal.ofReal (t k ^ (q k - 1) * Real.exp (-(mY ω k * t k)))
  have hb_nonneg (k : κ) (i : ι) : 0 ≤ b k i := by
    simp only [b]
    split_ifs <;> simp [ha]
  have hmX (k : κ) : AEMeasurable (fun ω => mX ω k) PX := by
    simpa [mX, b] using finiteChaosMass_aemeasurable PX X hX (b k) γ
  have hmY (k : κ) : AEMeasurable (fun ω => mY ω k) PY := by
    simpa [mY, b] using finiteChaosMass_aemeasurable PY Y hY (b k) γ
  have hmXpos (ω : ΩX) (k : κ) : 0 < mX ω k := by
    obtain ⟨i, hik, hai⟩ := hweight k
    have hterm : 0 < (if block i = k then a i else 0) * Real.exp
        (γ * X ω i - γ ^ 2 / 2 * DOZZ.gaussianVariance PX (fun ω => X ω i)) := by
      rw [ite_eq_left hik]
      exact mul_pos hai (Real.exp_pos _)
    dsimp [mX, b, DOZZ.finiteChaosMass]
    exact lt_of_lt_of_le hterm (Finset.single_le_sum
      (fun j _ => mul_nonneg (hb_nonneg k j) (Real.exp_nonneg
        (γ * X ω j - γ ^ 2 / 2 * DOZZ.gaussianVariance PX (fun ω => X ω j))))
      (Finset.mem_univ i))
  have hmYpos (ω : ΩY) (k : κ) : 0 < mY ω k := by
    obtain ⟨i, hik, hai⟩ := hweight k
    have hterm : 0 < (if block i = k then a i else 0) * Real.exp
        (γ * Y ω i - γ ^ 2 / 2 * DOZZ.gaussianVariance PY (fun ω => Y ω i)) := by
      rw [ite_eq_left hik]
      exact mul_pos hai (Real.exp_pos _)
    dsimp [mY, b, DOZZ.finiteChaosMass]
    exact lt_of_lt_of_le hterm (Finset.single_le_sum
      (fun j _ => mul_nonneg (hb_nonneg k j) (Real.exp_nonneg
        (γ * Y ω j - γ ^ 2 / 2 * DOZZ.gaussianVariance PY (fun ω => Y ω j))))
      (Finset.mem_univ i))
  have hmXprod : AEMeasurable (Function.uncurry fX) (PX.prod T) := by
    apply Finset.aemeasurable_fun_prod Finset.univ
    intro k hk
    have hm : AEMeasurable (fun z : ΩX × (κ → ℝ) => mX z.1 k) (PX.prod T) :=
      (hmX k).comp_fst
    have ht : Measurable (fun z : ΩX × (κ → ℝ) => z.2 k) :=
      (measurable_pi_apply k).comp measurable_snd
    have harg : AEMeasurable (fun z : ΩX × (κ → ℝ) =>
        -(mX z.1 k * z.2 k)) (PX.prod T) := (hm.mul ht.aemeasurable).neg
    have hpow : Measurable (fun z : ΩX × (κ → ℝ) => z.2 k ^ (q k - 1)) := by fun_prop
    have hreal : AEMeasurable (fun z : ΩX × (κ → ℝ) =>
        z.2 k ^ (q k - 1) * Real.exp (-(mX z.1 k * z.2 k))) (PX.prod T) :=
      hpow.aemeasurable.mul (Real.measurable_exp.comp_aemeasurable harg)
    exact hreal.ennreal_ofReal
  have hmYprod : AEMeasurable (Function.uncurry fY) (PY.prod T) := by
    apply Finset.aemeasurable_fun_prod Finset.univ
    intro k hk
    have hm : AEMeasurable (fun z : ΩY × (κ → ℝ) => mY z.1 k) (PY.prod T) :=
      (hmY k).comp_fst
    have ht : Measurable (fun z : ΩY × (κ → ℝ) => z.2 k) :=
      (measurable_pi_apply k).comp measurable_snd
    have harg : AEMeasurable (fun z : ΩY × (κ → ℝ) =>
        -(mY z.1 k * z.2 k)) (PY.prod T) := (hm.mul ht.aemeasurable).neg
    have hpow : Measurable (fun z : ΩY × (κ → ℝ) => z.2 k ^ (q k - 1)) := by fun_prop
    have hreal : AEMeasurable (fun z : ΩY × (κ → ℝ) =>
        z.2 k ^ (q k - 1) * Real.exp (-(mY z.1 k * z.2 k))) (PY.prod T) :=
      hpow.aemeasurable.mul (Real.measurable_exp.comp_aemeasurable harg)
    exact hreal.ennreal_ofReal
  have hIX : AEMeasurable (fun ω => ∫⁻ t, fX ω t ∂T) PX := hmXprod.lintegral_prod_right
  have hIY : AEMeasurable (fun ω => ∫⁻ t, fY ω t ∂T) PY := hmYprod.lintegral_prod_right
  have hscalarX (ω : ΩX) (k : κ) :
      ENNReal.rpow (ENNReal.ofReal (mX ω k)) (-q k) = c k *
        ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (t ^ (q k - 1) * Real.exp (-(mX ω k * t))) ∂volume := by
    change ENNReal.ofReal (mX ω k) ^ (-q k) = _
    rw [ENNReal.ofReal_rpow_of_pos (hmXpos ω k)]
    simpa [c] using ofReal_rpow_neg_eq_mellin_lintegral (hmXpos ω k) (hq k)
  have hscalarY (ω : ΩY) (k : κ) :
      ENNReal.rpow (ENNReal.ofReal (mY ω k)) (-q k) = c k *
        ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (t ^ (q k - 1) * Real.exp (-(mY ω k * t))) ∂volume := by
    change ENNReal.ofReal (mY ω k) ^ (-q k) = _
    rw [ENNReal.ofReal_rpow_of_pos (hmYpos ω k)]
    simpa [c] using ofReal_rpow_neg_eq_mellin_lintegral (hmYpos ω k) (hq k)
  have hpiX (ω : ΩX) : ∫⁻ t, fX ω t ∂T =
      ∏ k, ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (s ^ (q k - 1) * Real.exp (-(mX ω k * s))) ∂volume := by
    have h := lintegral_pi_prod νκ
      (fun k s => ENNReal.ofReal (s ^ (q k - 1) * Real.exp (-(mX ω k * s))))
      (fun k => by infer_instance) (fun k => by fun_prop)
    simpa [T, ν, νκ, fX] using h
  have hpiY (ω : ΩY) : ∫⁻ t, fY ω t ∂T =
      ∏ k, ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (s ^ (q k - 1) * Real.exp (-(mY ω k * s))) ∂volume := by
    have h := lintegral_pi_prod νκ
      (fun k s => ENNReal.ofReal (s ^ (q k - 1) * Real.exp (-(mY ω k * s))))
      (fun k => by infer_instance) (fun k => by fun_prop)
    simpa [T, ν, νκ, fY] using h
  have hpointX (ω : ΩX) :
      (∏ k, ENNReal.rpow (ENNReal.ofReal (mX ω k)) (-q k)) =
        C * ∫⁻ t, fX ω t ∂T := by
    calc
      _ = ∏ k, (c k * ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (t ^ (q k - 1) * Real.exp (-(mX ω k * t))) ∂volume) := by
            apply Finset.prod_congr rfl
            intro k hk
            exact hscalarX ω k
      _ = C * ∏ k, ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (t ^ (q k - 1) * Real.exp (-(mX ω k * t))) ∂volume := by
            simp [C, Finset.prod_mul_distrib]
      _ = C * ∫⁻ t, fX ω t ∂T := by
            rw [← hpiX ω]
  have hpointY (ω : ΩY) :
      (∏ k, ENNReal.rpow (ENNReal.ofReal (mY ω k)) (-q k)) =
        C * ∫⁻ t, fY ω t ∂T := by
    calc
      _ = ∏ k, (c k * ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (t ^ (q k - 1) * Real.exp (-(mY ω k * t))) ∂volume) := by
            apply Finset.prod_congr rfl
            intro k hk
            exact hscalarY ω k
      _ = C * ∏ k, ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (t ^ (q k - 1) * Real.exp (-(mY ω k * t))) ∂volume := by
            simp [C, Finset.prod_mul_distrib]
      _ = C * ∫⁻ t, fY ω t ∂T := by
            rw [← hpiY ω]
  have hcoordPos (k : κ) : ∀ᵐ t ∂T, 0 < t k := by
    rw [ae_iff]
    have hnull : ν (Iic (0 : ℝ)) = 0 := by
      change (volume.restrict (Ioi (0 : ℝ))) (Iic (0 : ℝ)) = 0
      rw [Measure.restrict_apply measurableSet_Iic]
      rw [Set.inter_comm, Ioi_inter_Iic]
      simp
    simpa [Function.eval, Set.preimage, Set.mem_Iic] using
      (Measure.pi_eval_preimage_null νκ hnull)
  have hcoordsPos : ∀ᵐ t ∂T, ∀ k, 0 < t k := ae_all_iff.2 hcoordPos
  have hinner (t : κ → ℝ) (ht : ∀ k, 0 < t k) :
      ∫⁻ ω, fX ω t ∂PX ≤ ∫⁻ ω, fY ω t ∂PY := by
    have hLap := kahane_finite_multi_block_laplace_lintegral PX PY X Y hX hY
      block a ha t (fun k => (ht k).le) γ hcov
    have hcoef : 0 ≤ ∏ k, t k ^ (q k - 1) :=
      Finset.prod_nonneg fun k hk => Real.rpow_nonneg (le_of_lt (ht k)) _
    have hkernelX : ∀ ω : ΩX, fX ω t =
        ENNReal.ofReal (∏ k, t k ^ (q k - 1)) *
          ENNReal.ofReal (Real.exp (-∑ k, t k * mX ω k)) := by
      intro ω
      change (∏ k, ENNReal.ofReal
        (t k ^ (q k - 1) * Real.exp (-(mX ω k * t k)))) = _
      have hExp : (∏ k, Real.exp (-(mX ω k * t k))) =
          Real.exp (-∑ k, t k * mX ω k) := by
        rw [← Real.exp_sum]
        congr 1
        calc
          ∑ k, -(mX ω k * t k) = -(∑ k, mX ω k * t k) := by rw [Finset.sum_neg_distrib]
          _ = -(∑ k, t k * mX ω k) := by
                congr 1
                apply Finset.sum_congr rfl
                intro k hk
                ring
      calc
        _ = ∏ k, (ENNReal.ofReal (t k ^ (q k - 1)) *
            ENNReal.ofReal (Real.exp (-(mX ω k * t k)))) := by
              apply Finset.prod_congr rfl
              intro k hk
              rw [ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt (ht k)) _)]
        _ = (∏ k, ENNReal.ofReal (t k ^ (q k - 1))) *
            ∏ k, ENNReal.ofReal (Real.exp (-(mX ω k * t k))) := Finset.prod_mul_distrib
        _ = ENNReal.ofReal (∏ k, t k ^ (q k - 1)) *
            ENNReal.ofReal (Real.exp (-∑ k, t k * mX ω k)) := by
              rw [← ENNReal.ofReal_prod_of_nonneg
                (fun k hk => Real.rpow_nonneg (le_of_lt (ht k)) _),
                ← ENNReal.ofReal_prod_of_nonneg
                  (fun k hk => Real.exp_nonneg (-(mX ω k * t k))), hExp]
    have hkernelY : ∀ ω : ΩY, fY ω t =
        ENNReal.ofReal (∏ k, t k ^ (q k - 1)) *
          ENNReal.ofReal (Real.exp (-∑ k, t k * mY ω k)) := by
      intro ω
      change (∏ k, ENNReal.ofReal
        (t k ^ (q k - 1) * Real.exp (-(mY ω k * t k)))) = _
      have hExp : (∏ k, Real.exp (-(mY ω k * t k))) =
          Real.exp (-∑ k, t k * mY ω k) := by
        rw [← Real.exp_sum]
        congr 1
        calc
          ∑ k, -(mY ω k * t k) = -(∑ k, mY ω k * t k) := by rw [Finset.sum_neg_distrib]
          _ = -(∑ k, t k * mY ω k) := by
                congr 1
                apply Finset.sum_congr rfl
                intro k hk
                ring
      calc
        _ = ∏ k, (ENNReal.ofReal (t k ^ (q k - 1)) *
            ENNReal.ofReal (Real.exp (-(mY ω k * t k)))) := by
              apply Finset.prod_congr rfl
              intro k hk
              rw [ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt (ht k)) _)]
        _ = (∏ k, ENNReal.ofReal (t k ^ (q k - 1))) *
            ∏ k, ENNReal.ofReal (Real.exp (-(mY ω k * t k))) := Finset.prod_mul_distrib
        _ = ENNReal.ofReal (∏ k, t k ^ (q k - 1)) *
            ENNReal.ofReal (Real.exp (-∑ k, t k * mY ω k)) := by
              rw [← ENNReal.ofReal_prod_of_nonneg
                (fun k hk => Real.rpow_nonneg (le_of_lt (ht k)) _),
                ← ENNReal.ofReal_prod_of_nonneg
                  (fun k hk => Real.exp_nonneg (-(mY ω k * t k))), hExp]
    rw [show (fun ω : ΩX => fX ω t) = fun ω =>
      ENNReal.ofReal (∏ k, t k ^ (q k - 1)) *
        ENNReal.ofReal (Real.exp (-∑ k, t k * mX ω k)) by funext ω; exact hkernelX ω,
      show (fun ω : ΩY => fY ω t) = fun ω =>
      ENNReal.ofReal (∏ k, t k ^ (q k - 1)) *
        ENNReal.ofReal (Real.exp (-∑ k, t k * mY ω k)) by funext ω; exact hkernelY ω]
    have hcoeff : ENNReal.ofReal (∏ k, t k ^ (q k - 1)) ≠ ∞ := ENNReal.ofReal_ne_top
    rw [lintegral_const_mul' _ _ hcoeff, lintegral_const_mul' _ _ hcoeff]
    gcongr
  have houter :
      ∫⁻ t, ∫⁻ ω, fX ω t ∂PX ∂T ≤
        ∫⁻ t, ∫⁻ ω, fY ω t ∂PY ∂T := by
    apply lintegral_mono_ae
    filter_upwards [hcoordsPos] with t ht
    exact hinner t ht
  have hMomentX :
      ∫⁻ ω, ∏ k, ENNReal.rpow (ENNReal.ofReal (mX ω k)) (-q k) ∂PX =
        C * ∫⁻ t, ∫⁻ ω, fX ω t ∂PX ∂T := by
    calc
      _ = ∫⁻ ω, C * (∫⁻ t, fX ω t ∂T) ∂PX := by
            apply lintegral_congr_ae
            exact ae_of_all _ hpointX
      _ = C * ∫⁻ ω, ∫⁻ t, fX ω t ∂T ∂PX := lintegral_const_mul'' C hIX
      _ = C * ∫⁻ t, ∫⁻ ω, fX ω t ∂PX ∂T := by
            congr 1
            exact lintegral_lintegral_swap hmXprod
  have hMomentY :
      ∫⁻ ω, ∏ k, ENNReal.rpow (ENNReal.ofReal (mY ω k)) (-q k) ∂PY =
        C * ∫⁻ t, ∫⁻ ω, fY ω t ∂PY ∂T := by
    calc
      _ = ∫⁻ ω, C * (∫⁻ t, fY ω t ∂T) ∂PY := by
            apply lintegral_congr_ae
            exact ae_of_all _ hpointY
      _ = C * ∫⁻ ω, ∫⁻ t, fY ω t ∂T ∂PY := lintegral_const_mul'' C hIY
      _ = C * ∫⁻ t, ∫⁻ ω, fY ω t ∂PY ∂T := by
            congr 1
            exact lintegral_lintegral_swap hmYprod
  rw [hMomentX, hMomentY]
  gcongr

/-- Full multiblock finite Kahane comparison for products of nonpositive powers. Zero exponents
drop out, while a zero-weight block with positive exponent makes both extended expectations
infinite. -/
theorem kahane_finite_multi_negative_power
    {ΩX ΩY ι κ : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian PX X)
    (hY : DOZZ.IsCenteredJointlyGaussian PY Y)
    (block : ι → κ) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ : ℝ)
    (q : κ → ℝ) (hq : ∀ k, 0 ≤ q k)
    (hcov : ∀ i j,
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
        DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)) :
    ∫⁻ ω, ∏ k, ENNReal.rpow (ENNReal.ofReal
        (DOZZ.finiteChaosMass PX X (fun i => if block i = k then a i else 0) γ ω)) (-q k) ∂PX ≤
      ∫⁻ ω, ∏ k, ENNReal.rpow (ENNReal.ofReal
        (DOZZ.finiteChaosMass PY Y (fun i => if block i = k then a i else 0) γ ω)) (-q k) ∂PY := by
  classical
  let : IsProbabilityMeasure PX := hX.1
  let : IsProbabilityMeasure PY := hY.1
  let K := {k : κ // 0 < q k}
  by_cases hK : Nonempty K
  · obtain ⟨kdefault⟩ := hK
    let : Nonempty K := ⟨kdefault⟩
    let p : κ → Prop := fun k => 0 < q k
    let blockK : ι → K := fun i =>
      if hi : 0 < q (block i) then ⟨block i, hi⟩ else kdefault
    let aK : ι → ℝ := fun i => if 0 < q (block i) then a i else 0
    have haK : ∀ i, 0 ≤ aK i := by
      intro i
      by_cases hi : 0 < q (block i) <;> simp [aK, hi, ha]
    have hblockWeight (k : K) (i : ι) :
        (if blockK i = k then aK i else 0) =
          (if block i = k.1 then a i else 0) := by
      by_cases hqpos : 0 < q (block i)
      · have hval : (blockK i).val = block i := by simp [blockK, hqpos]
        by_cases hik : block i = k.1
        · have hki : blockK i = k := by
            apply Subtype.ext
            simpa [blockK, hqpos] using hik
          rw [ite_eq_left hki, ite_eq_left hik]
          simp [aK, hqpos]
        · have hki : blockK i ≠ k := by
            intro heq
            apply hik
            exact hval.symm.trans (congrArg Subtype.val heq)
          simp [hki, hik]
      · have haK0 : aK i = 0 := by simp [aK, hqpos]
        have hik : block i ≠ k.1 := by
          intro hik
          apply hqpos
          simpa [hik] using k.2
        simp [haK0, hik]
    have hmassX (ω : ΩX) (k : K) :
        DOZZ.finiteChaosMass PX X (fun i => if blockK i = k then aK i else 0) γ ω =
          DOZZ.finiteChaosMass PX X (fun i => if block i = k.1 then a i else 0) γ ω := by
      simp only [DOZZ.finiteChaosMass]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hblockWeight k i]
    have hmassY (ω : ΩY) (k : K) :
        DOZZ.finiteChaosMass PY Y (fun i => if blockK i = k then aK i else 0) γ ω =
          DOZZ.finiteChaosMass PY Y (fun i => if block i = k.1 then a i else 0) γ ω := by
      simp only [DOZZ.finiteChaosMass]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hblockWeight k i]
    let zX : ΩX → κ → ℝ≥0∞ := fun ω k => ENNReal.rpow (ENNReal.ofReal
      (DOZZ.finiteChaosMass PX X (fun i => if block i = k then a i else 0) γ ω)) (-q k)
    let zY : ΩY → κ → ℝ≥0∞ := fun ω k => ENNReal.rpow (ENNReal.ofReal
      (DOZZ.finiteChaosMass PY Y (fun i => if block i = k then a i else 0) γ ω)) (-q k)
    let zKX : ΩX → K → ℝ≥0∞ := fun ω k => ENNReal.rpow (ENNReal.ofReal
      (DOZZ.finiteChaosMass PX X (fun i => if blockK i = k then aK i else 0) γ ω))
      (-q k.1)
    let zKY : ΩY → K → ℝ≥0∞ := fun ω k => ENNReal.rpow (ENNReal.ofReal
      (DOZZ.finiteChaosMass PY Y (fun i => if blockK i = k then aK i else 0) γ ω))
      (-q k.1)
    have hzXinactive (ω : ΩX) (k : {k : κ // ¬ p k}) : zX ω k.1 = 1 := by
      have hq0 : q k.1 = 0 := le_antisymm (le_of_not_gt k.2) (hq k.1)
      simp [zX, hq0]
    have hzYinactive (ω : ΩY) (k : {k : κ // ¬ p k}) : zY ω k.1 = 1 := by
      have hq0 : q k.1 = 0 := le_antisymm (le_of_not_gt k.2) (hq k.1)
      simp [zY, hq0]
    have hprodX (ω : ΩX) :
        (∏ k, zX ω k) = ∏ k : K, zKX ω k := by
      calc
        (∏ k : κ, zX ω k) =
            (∏ k : K, zX ω k.1) * ∏ k : {k : κ // ¬ p k}, zX ω k.1 :=
              (Fintype.prod_subtype_mul_prod_subtype p (zX ω)).symm
        _ = ∏ k : K, zX ω k.1 := by simp [hzXinactive]
        _ = ∏ k : K, zKX ω k := by
              apply Finset.prod_congr rfl
              intro k hk
              simp [zX, zKX, hmassX]
    have hprodY (ω : ΩY) :
        (∏ k, zY ω k) = ∏ k : K, zKY ω k := by
      calc
        (∏ k : κ, zY ω k) =
            (∏ k : K, zY ω k.1) * ∏ k : {k : κ // ¬ p k}, zY ω k.1 :=
              (Fintype.prod_subtype_mul_prod_subtype p (zY ω)).symm
        _ = ∏ k : K, zY ω k.1 := by simp [hzYinactive]
        _ = ∏ k : K, zKY ω k := by
              apply Finset.prod_congr rfl
              intro k hk
              simp [zY, zKY, hmassY]
    by_cases hweights : ∀ k : K, ∃ i, block i = k.1 ∧ 0 < a i
    · have hactive := kahane_finite_multi_negative_power_of_pos_weights
        PX PY X Y hX hY blockK aK haK γ (fun k : K => q k.1) (fun k => k.2)
        (by
          intro k
          obtain ⟨i, hik, hai⟩ := hweights k
          refine ⟨i, ?_, ?_⟩
          · have hqpos : 0 < q (block i) := by simpa [hik] using k.2
            apply Subtype.ext
            simpa [blockK, hqpos] using hik
          · have hqpos : 0 < q (block i) := by simpa [hik] using k.2
            simpa [aK, hqpos] using hai) hcov
      calc
        ∫⁻ ω, ∏ k, zX ω k ∂PX = ∫⁻ ω, ∏ k : K, zKX ω k ∂PX := by
          apply lintegral_congr_ae
          exact ae_of_all _ hprodX
        _ ≤ ∫⁻ ω, ∏ k : K, zKY ω k ∂PY := hactive
        _ = ∫⁻ ω, ∏ k, zY ω k ∂PY := by
          apply lintegral_congr_ae
          exact ae_of_all _ fun ω => (hprodY ω).symm
    · push Not at hweights
      obtain ⟨kbad, hkbad⟩ := hweights
      have hzeroX (ω : ΩX) :
          DOZZ.finiteChaosMass PX X
            (fun i => if block i = kbad.1 then a i else 0) γ ω = 0 := by
        unfold DOZZ.finiteChaosMass
        apply Finset.sum_eq_zero
        intro i hi
        by_cases hik : block i = kbad.1
        · have hai : a i = 0 := by
            by_contra hne
            have hpos : 0 < a i := lt_of_le_of_ne (ha i) (Ne.symm hne)
            exact (not_lt_of_ge (hkbad i hik) hpos)
          simp [hik, hai]
        · simp [hik]
      have hzeroY (ω : ΩY) :
          DOZZ.finiteChaosMass PY Y
            (fun i => if block i = kbad.1 then a i else 0) γ ω = 0 := by
        unfold DOZZ.finiteChaosMass
        apply Finset.sum_eq_zero
        intro i hi
        by_cases hik : block i = kbad.1
        · have hai : a i = 0 := by
            by_contra hne
            have hpos : 0 < a i := lt_of_le_of_ne (ha i) (Ne.symm hne)
            exact (not_lt_of_ge (hkbad i hik) hpos)
          simp [hik, hai]
        · simp [hik]
      have hmassNNX (ω : ΩX) (k : κ) :
          0 ≤ DOZZ.finiteChaosMass PX X
            (fun i => if block i = k then a i else 0) γ ω :=
        finiteChaosMass_nonneg PX X (fun i => if block i = k then a i else 0)
          (fun i => by split_ifs <;> simp [ha]) γ ω
      have hmassNNY (ω : ΩY) (k : κ) :
          0 ≤ DOZZ.finiteChaosMass PY Y
            (fun i => if block i = k then a i else 0) γ ω :=
        finiteChaosMass_nonneg PY Y (fun i => if block i = k then a i else 0)
          (fun i => by split_ifs <;> simp [ha]) γ ω
      have htopX := finiteChaosMultiNegativeProduct_eq_top_of_zero_block
        PX X block a ha γ q hq kbad.1 kbad.2 hzeroX hmassNNX
      have htopY := finiteChaosMultiNegativeProduct_eq_top_of_zero_block
        PY Y block a ha γ q hq kbad.1 kbad.2 hzeroY hmassNNY
      have hIX : ∫⁻ ω, ∏ k, zX ω k ∂PX = ∞ := by
        have hfun : (fun ω => ∏ k, zX ω k) = fun _ => (∞ : ℝ≥0∞) := by
          funext ω
          exact htopX ω
        rw [hfun, lintegral_const]
        simp
      have hIY : ∫⁻ ω, ∏ k, zY ω k ∂PY = ∞ := by
        have hfun : (fun ω => ∏ k, zY ω k) = fun _ => (∞ : ℝ≥0∞) := by
          funext ω
          exact htopY ω
        rw [hfun, lintegral_const]
        simp
      rw [hIX, hIY]
  · have hqzero (k : κ) : q k = 0 := by
      by_contra hne
      have hkpos : 0 < q k := lt_of_le_of_ne (hq k) (Ne.symm hne)
      exact hK ⟨⟨k, hkpos⟩⟩
    simp [hqzero]


end DOZZ.Proofs
