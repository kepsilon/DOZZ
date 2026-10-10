/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.KahaneNegativeMellin
public import DOZZ.GMC.FiniteMultiMellin

/-! Multivariate Mellin comparison for nonnegative measurable masses, including zero values. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The scalar Mellin formula at nonnegative masses, including the infinite value at zero. -/
theorem nonneg_rpow_neg_eq_mellin_lintegral
    {m q : ℝ} (hm : 0 ≤ m) (hq : 0 < q) :
    ENNReal.rpow (ENNReal.ofReal m) (-q) = ENNReal.ofReal (1 / Real.Gamma q) *
      ∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (t ^ (q - 1) * Real.exp (-(m * t))) ∂volume := by
  have h := nonneg_rpow_neg_lintegral_eq_weighted_laplace
    (Measure.dirac ()) (fun _ : Unit => m) (fun _ => hm)
    measurable_const.aemeasurable q hq
  simp only [lintegral_const, measure_univ, mul_one] at h
  rw [h]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]

/-- Multivariate Laplace order implies comparison of products of strictly negative powers. -/
theorem nonneg_multi_negative_power_le_of_laplace
    {ΩX ΩY κ : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [Fintype κ]
    (PX : Measure ΩX) (PY : Measure ΩY)
    [IsProbabilityMeasure PX] [IsProbabilityMeasure PY]
    (mX : ΩX → κ → ℝ) (mY : ΩY → κ → ℝ)
    (hmX : ∀ k, AEMeasurable (fun ω => mX ω k) PX)
    (hmY : ∀ k, AEMeasurable (fun ω => mY ω k) PY)
    (hmXnonneg : ∀ ω k, 0 ≤ mX ω k) (hmYnonneg : ∀ ω k, 0 ≤ mY ω k)
    (q : κ → ℝ) (hq : ∀ k, 0 < q k)
    (hLaplace : ∀ t : κ → ℝ, (∀ k, 0 ≤ t k) →
      (∫⁻ ω, ENNReal.ofReal (Real.exp (-∑ k, t k * mX ω k)) ∂PX) ≤
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-∑ k, t k * mY ω k)) ∂PY) :
    (∫⁻ ω, ∏ k, ENNReal.rpow (ENNReal.ofReal (mX ω k)) (-q k) ∂PX) ≤
      ∫⁻ ω, ∏ k, ENNReal.rpow (ENNReal.ofReal (mY ω k)) (-q k) ∂PY := by
  classical
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let νκ : κ → Measure ℝ := fun _ => ν
  let T : Measure (κ → ℝ) := Measure.pi νκ
  let c : κ → ℝ≥0∞ := fun k => ENNReal.ofReal (1 / Real.Gamma (q k))
  let C : ℝ≥0∞ := ∏ k, c k
  let fX : ΩX → (κ → ℝ) → ℝ≥0∞ := fun ω t =>
    ∏ k, ENNReal.ofReal (t k ^ (q k - 1) * Real.exp (-(mX ω k * t k)))
  let fY : ΩY → (κ → ℝ) → ℝ≥0∞ := fun ω t =>
    ∏ k, ENNReal.ofReal (t k ^ (q k - 1) * Real.exp (-(mY ω k * t k)))
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
    simpa [c] using nonneg_rpow_neg_eq_mellin_lintegral
      (hmXnonneg ω k) (hq k)
  have hscalarY (ω : ΩY) (k : κ) :
      ENNReal.rpow (ENNReal.ofReal (mY ω k)) (-q k) = c k *
        ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (t ^ (q k - 1) * Real.exp (-(mY ω k * t))) ∂volume := by
    simpa [c] using nonneg_rpow_neg_eq_mellin_lintegral
      (hmYnonneg ω k) (hq k)
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
    have hLap := hLaplace t (fun k => (ht k).le)
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

/-- Zero exponents can be omitted from the multivariate Mellin comparison. -/
theorem nonneg_multi_nonpositive_power_le_of_laplace
    {ΩX ΩY κ : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [Fintype κ]
    (PX : Measure ΩX) (PY : Measure ΩY)
    [IsProbabilityMeasure PX] [IsProbabilityMeasure PY]
    (mX : ΩX → κ → ℝ) (mY : ΩY → κ → ℝ)
    (hmX : ∀ k, AEMeasurable (fun ω => mX ω k) PX)
    (hmY : ∀ k, AEMeasurable (fun ω => mY ω k) PY)
    (hmXnonneg : ∀ ω k, 0 ≤ mX ω k) (hmYnonneg : ∀ ω k, 0 ≤ mY ω k)
    (q : κ → ℝ) (hq : ∀ k, 0 ≤ q k)
    (hLaplace : ∀ t : κ → ℝ, (∀ k, 0 ≤ t k) →
      (∫⁻ ω, ENNReal.ofReal (Real.exp (-∑ k, t k * mX ω k)) ∂PX) ≤
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-∑ k, t k * mY ω k)) ∂PY) :
    (∫⁻ ω, ∏ k, ENNReal.rpow (ENNReal.ofReal (mX ω k)) (-q k) ∂PX) ≤
      ∫⁻ ω, ∏ k, ENNReal.rpow (ENNReal.ofReal (mY ω k)) (-q k) ∂PY := by
  classical
  let p : κ → Prop := fun k => 0 < q k
  let K := {k : κ // p k}
  have hLap (t : K → ℝ) (ht : ∀ k, 0 ≤ t k) :
      (∫⁻ ω, ENNReal.ofReal (Real.exp (-∑ k : K, t k * mX ω k.val)) ∂PX) ≤
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-∑ k : K, t k * mY ω k.val)) ∂PY := by
    let t' : κ → ℝ := fun k => if hk : p k then t ⟨k, hk⟩ else 0
    have ht' (k : κ) : 0 ≤ t' k := by
      dsimp [t']
      split_ifs with hk
      · exact ht ⟨k, hk⟩
      · exact le_rfl
    have hsum (m : κ → ℝ) : (∑ k : κ, t' k * m k) = ∑ k : K, t k * m k.val := by
      rw [← Fintype.sum_subtype_add_sum_subtype p (fun k => t' k * m k)]
      have hactive (k : K) : t' k.val = t k := dite_eq_left k.property
      have hinactive (k : {k : κ // ¬ p k}) : t' k.val = 0 := dite_eq_right k.property
      simp only [hactive, hinactive, zero_mul, Finset.sum_const_zero, add_zero]
      rfl
    simpa only [hsum] using hLaplace t' ht'
  have h := nonneg_multi_negative_power_le_of_laplace PX PY
    (fun ω (k : K) => mX ω k.val) (fun ω (k : K) => mY ω k.val)
    (fun k => hmX k.val) (fun k => hmY k.val)
    (fun ω k => hmXnonneg ω k.val) (fun ω k => hmYnonneg ω k.val)
    (fun k => q k.val) (fun k => k.property) hLap
  have hprod (m : κ → ℝ) :
      (∏ k : κ, ENNReal.rpow (ENNReal.ofReal (m k)) (-q k)) =
        ∏ k : K, ENNReal.rpow (ENNReal.ofReal (m k.val)) (-q k.val) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype p
      (fun k => ENNReal.rpow (ENNReal.ofReal (m k)) (-q k))]
    have hinactive (k : {k : κ // ¬ p k}) : q k.val = 0 :=
      le_antisymm (le_of_not_gt k.property) (hq k.val)
    simp [hinactive, K]
  simpa only [← hprod] using h


end DOZZ.Proofs
