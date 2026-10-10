/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionEulerSeries
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Real-variable substitution lemmas for Euler's hypergeometric integral. -/

@[expose] public section

open MeasureTheory Set

namespace DOZZ.Proofs

/-- The real Euler integrand for parameters `(a,b,c)` at a real argument `x`. -/
noncomputable def realGaussEulerKernel (a b c x t : ℝ) : ℝ :=
  t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a)

/-- The integrand for the Euler-transformed parameters `(c-a,c-b,c)`. -/
noncomputable def realGaussEulerTransformedKernel (a b c x u : ℝ) : ℝ :=
  u ^ (c - b - 1) * (1 - u) ^ (b - 1) * (1 - x * u) ^ (-(c - a))

/-- The decreasing Mobius map used to exchange the two beta endpoints. -/
noncomputable def realGaussEulerMobius (x t : ℝ) : ℝ :=
  (1 - t) / (1 - x * t)

private theorem realGaussEulerKernel_integrableOn_Icc_aux (a b c x : ℝ)
    (hb : 0 < b) (hcb : 0 < c - b) (hx : x < 1) :
    IntegrableOn (realGaussEulerKernel a b c x) (Icc 0 1) := by
  have hweight := realEulerBetaWeight_integrable b (c - b) hb hcb
  have hfactor : ContinuousOn (fun t : ℝ => (1 - x * t) ^ (-a)) (Icc 0 1) := by
    apply ContinuousOn.rpow_const (by fun_prop)
    intro t ht
    left
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    by_cases hx0 : 0 ≤ x
    · have hxt : x * t ≤ x := mul_le_of_le_one_right hx0 ht1
      exact ne_of_gt (by nlinarith [hx, hxt])
    · have hxneg : x < 0 := lt_of_not_ge hx0
      have hxt : x * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hxneg.le ht0
      exact ne_of_gt (by nlinarith [hxt])
  have hweightIcc : IntegrableOn
      (fun t : ℝ => t ^ (b - 1) * (1 - t) ^ (c - b - 1)) (Icc 0 1) := by
    exact (integrableOn_Icc_iff_integrableOn_Ioc).2 hweight
  have hprod := hweightIcc.mul_continuousOn hfactor isCompact_Icc
  change IntegrableOn (fun t : ℝ =>
    t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a)) (Icc 0 1)
  exact hprod

/-- The real Euler kernel is integrable on the closed beta interval whenever its two beta
parameters are positive and `x < 1`. -/
theorem realGaussEulerKernel_integrableOn_Icc (a b c x : ℝ)
    (hb : 0 < b) (hcb : 0 < c - b) (hx : x < 1) :
    IntegrableOn (realGaussEulerKernel a b c x) (Icc 0 1) :=
  realGaussEulerKernel_integrableOn_Icc_aux a b c x hb hcb hx

/-- The Mobius substitution used in Euler's transformation, including its Jacobian identity on
the open interval. -/
theorem realGaussEulerMobius_kernel_identity (a b c x t : ℝ)
    (hx : 0 < x) (hx1 : x < 1) (ht : 0 < t) (ht1 : t < 1) :
    realGaussEulerTransformedKernel a b c x (realGaussEulerMobius x t) *
        (-(1 - x) / (1 - x * t) ^ 2) =
      -((1 - x) ^ (-(c - a - b))) * realGaussEulerKernel a b c x t := by
  let q : ℝ := 1 - x * t
  let r : ℝ := 1 - x
  have hq : 0 < q := by dsimp [q]; nlinarith
  have hr : 0 < r := by dsimp [r]; linarith
  have h1t : 0 < 1 - t := by linarith
  have hrt : 0 < t * r := mul_pos ht hr
  have hphi : realGaussEulerMobius x t = (1 - t) / q := by
    simp [realGaussEulerMobius, q]
  have h1phi : 1 - realGaussEulerMobius x t = t * r / q := by
    rw [hphi]
    field_simp [ne_of_gt hq]
    ring
  have hxphi : 1 - x * realGaussEulerMobius x t = r / q := by
    rw [hphi]
    field_simp [ne_of_gt hq]
    ring
  have hphiPow : realGaussEulerMobius x t ^ (c - b - 1) =
      (1 - t) ^ (c - b - 1) * q ^ (-(c - b - 1)) := by
    rw [hphi, Real.div_rpow (le_of_lt h1t) (le_of_lt hq), div_eq_mul_inv,
      ← Real.rpow_neg hq.le (c - b - 1)]
  have h1phiPow : (1 - realGaussEulerMobius x t) ^ (b - 1) =
      t ^ (b - 1) * r ^ (b - 1) * q ^ (-(b - 1)) := by
    rw [h1phi, Real.div_rpow (le_of_lt hrt) (le_of_lt hq), Real.mul_rpow ht.le hr.le,
      div_eq_mul_inv, ← Real.rpow_neg hq.le (b - 1)]
  have hxphiPow : (1 - x * realGaussEulerMobius x t) ^ (-(c - a)) =
      r ^ (-(c - a)) * q ^ (c - a) := by
    rw [hxphi, Real.div_rpow hr.le hq.le, div_eq_mul_inv,
      Real.rpow_neg hr.le, Real.rpow_neg hq.le, inv_inv]
  have hqneg2 : q ^ (-(2 : ℝ)) = (q ^ (2 : ℝ))⁻¹ :=
    Real.rpow_neg hq.le (2 : ℝ)
  have hqpow2 : q ^ (2 : ℝ) = q ^ 2 := Real.rpow_natCast q 2
  have hqneg2' : q ^ (-(2 : ℝ)) = (q ^ 2)⁻¹ := by
    rw [hqneg2, hqpow2]
  have hderiv : (-(1 - x) / (1 - x * t) ^ 2) = -r * q ^ (-(2 : ℝ)) := by
    rw [hqneg2']
    dsimp [r, q]
    field_simp
  have hqpow : q ^ (-(c - b - 1)) * q ^ (-(b - 1)) * q ^ (c - a) *
      q ^ (-(2 : ℝ)) = q ^ (-a) := by
    calc
      q ^ (-(c - b - 1)) * q ^ (-(b - 1)) * q ^ (c - a) * q ^ (-(2 : ℝ)) =
          q ^ (-(c - b - 1) - (b - 1) + (c - a) - 2) := by
            rw [← Real.rpow_add hq, ← Real.rpow_add hq, ← Real.rpow_add hq]
            have hqexp : -(c - b - 1) + -(b - 1) + (c - a) + (-(2 : ℝ)) =
                -(c - b - 1) - (b - 1) + (c - a) - 2 := by ring
            rw [hqexp]
      _ = q ^ (-a) := by
        rw [show -(c - b - 1) - (b - 1) + (c - a) - 2 = -a by ring]
  have hrpow : r ^ (b - 1) * r ^ (-(c - a)) * r = r ^ (-(c - a - b)) := by
    calc
      r ^ (b - 1) * r ^ (-(c - a)) * r = r ^ (b - 1 - (c - a) + 1) := by
        calc
          r ^ (b - 1) * r ^ (-(c - a)) * r =
              r ^ (b - 1) * r ^ (-(c - a)) * r ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = r ^ (b - 1 - (c - a)) * r ^ (1 : ℝ) := by
            rw [← Real.rpow_add hr]
            rw [show b - 1 + -(c - a) = b - 1 - (c - a) by ring]
          _ = r ^ (b - 1 - (c - a) + 1) :=
            (Real.rpow_add hr (b - 1 - (c - a)) 1).symm
      _ = r ^ (-(c - a - b)) := by
        rw [show b - 1 - (c - a) + 1 = -(c - a - b) by ring]
  rw [realGaussEulerTransformedKernel, realGaussEulerKernel,
    hphiPow, h1phiPow, hxphiPow, hderiv]
  calc
    _ = -(r ^ (-(c - a - b))) *
        (t ^ (b - 1) * (1 - t) ^ (c - b - 1) * q ^ (-a)) := by
      rw [mul_assoc, mul_assoc]
      rw [← hrpow, ← hqpow]
      ring
    _ = -((1 - x) ^ (-(c - a - b))) *
        realGaussEulerKernel a b c x t := by
      simp [realGaussEulerKernel, q, r]

private theorem realGaussEulerMobius_mem_Icc (x t : ℝ)
    (hx : 0 < x) (hx1 : x < 1) (ht : t ∈ Icc 0 1) :
    realGaussEulerMobius x t ∈ Icc 0 1 := by
  rcases ht with ⟨ht0, ht1⟩
  have hden : 0 < 1 - x * t := by
    have hxt : x * t ≤ x := mul_le_of_le_one_right hx.le ht1
    linarith
  have hnum : 0 ≤ 1 - t := by linarith
  have hxtt : x * t ≤ t := mul_le_of_le_one_left ht0 hx1.le
  constructor
  · exact div_nonneg hnum hden.le
  · rw [realGaussEulerMobius, div_le_one hden]
    linarith

private theorem realGaussEulerMobius_mem_Ioo (x t : ℝ)
    (hx : 0 < x) (hx1 : x < 1) (ht : t ∈ Ioo 0 1) :
    realGaussEulerMobius x t ∈ Ioo 0 1 := by
  rcases ht with ⟨ht0, ht1⟩
  have hden : 0 < 1 - x * t := by
    have hxt : x * t ≤ x := mul_le_of_le_one_right hx.le ht1.le
    linarith
  have hnum : 0 < 1 - t := by linarith
  have hxtt : x * t < t := by
    calc
      x * t < 1 * t := mul_lt_mul_of_pos_right hx1 ht0
      _ = t := one_mul _
  constructor
  · exact div_pos hnum hden
  · rw [realGaussEulerMobius, div_lt_one hden]
    linarith

/-- Euler's real integral transformation. The beta normalization is unchanged because its two
parameters are exchanged; the kernel identity follows from the decreasing Mobius substitution. -/
theorem realGaussEulerIntegral_eulerTransform (a b c x : ℝ)
    (hb : 0 < b) (hcb : 0 < c - b)
    (hx : 0 < x) (hx1 : x < 1) :
    (Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))) *
        realGaussEulerKernelIntegral a b c x =
      (1 - x) ^ (c - a - b) *
        ((Real.Gamma c / (Real.Gamma (c - b) * Real.Gamma b)) *
          realGaussEulerKernelIntegral (c - a) (c - b) c x) := by
  let φ : ℝ → ℝ := realGaussEulerMobius x
  let g : ℝ → ℝ := realGaussEulerTransformedKernel a b c x
  let d : ℝ → ℝ := fun t => -(1 - x) / (1 - x * t) ^ 2
  have hden (t : ℝ) (ht : t ∈ Icc 0 1) : 1 - x * t ≠ 0 := by
    have hmem := realGaussEulerMobius_mem_Icc x t hx hx1 ht
    have hxt : x * t ≤ x := by
      rcases ht with ⟨ht0, ht1⟩
      exact mul_le_of_le_one_right hx.le ht1
    exact ne_of_gt (by nlinarith [hx1, hxt])
  have hφcont : ContinuousOn φ (Icc 0 1) := by
    change ContinuousOn (fun t : ℝ => (1 - t) / (1 - x * t)) (Icc 0 1)
    refine (continuousOn_const.sub continuousOn_id).div
      (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) ?_
    intro t ht
    exact hden t ht
  have hφderiv (t : ℝ) (ht : t ∈ Ioo 0 1) : HasDerivWithinAt φ (d t) (Ioi t) t := by
    have hdenpos : 0 < 1 - x * t := by
      have htIcc : t ∈ Icc 0 1 := ⟨ht.1.le, ht.2.le⟩
      have := realGaussEulerMobius_mem_Icc x t hx hx1 htIcc
      have hxt : x * t ≤ x := mul_le_of_le_one_right hx.le ht.2.le
      nlinarith [hx1, hxt]
    have hnum : HasDerivAt (fun u : ℝ => 1 - u) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
    have hxt : HasDerivAt (fun u : ℝ => x * u) x t := by
      simpa using (hasDerivAt_id t).const_mul x
    have hden' : HasDerivAt (fun u : ℝ => 1 - x * u) (-x) t := by
      change HasDerivAt ((fun _ : ℝ => (1 : ℝ)) - (fun u => x * u)) (-x) t
      simpa only [zero_sub] using (hasDerivAt_const t (1 : ℝ)).sub hxt
    have hquot := hnum.div hden' (ne_of_gt hdenpos)
    have hquot' : HasDerivAt (fun u : ℝ => (1 - u) / (1 - x * u)) (d t) t := by
      convert hquot using 1
      dsimp [d]
      field_simp
      ring
    exact hquot'.hasDerivWithinAt
  have hgcont : ContinuousOn g (Ioo 0 1) := by
    change ContinuousOn (fun u : ℝ =>
      u ^ (c - b - 1) * (1 - u) ^ (b - 1) * (1 - x * u) ^ (-(c - a)))
      (Ioo 0 1)
    have hpow1 : ContinuousOn (fun u : ℝ => u ^ (c - b - 1)) (Ioo 0 1) := by
      apply ContinuousOn.rpow_const continuousOn_id
      intro u hu
      exact Or.inl (ne_of_gt hu.1)
    have hpow2 : ContinuousOn (fun u : ℝ => (1 - u) ^ (b - 1)) (Ioo 0 1) := by
      apply ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
      intro u hu
      exact Or.inl (ne_of_gt (sub_pos.mpr hu.2))
    have hpow3 : ContinuousOn (fun u : ℝ => (1 - x * u) ^ (-(c - a))) (Ioo 0 1) := by
      apply ContinuousOn.rpow_const (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
      intro u hu
      have hxu : x * u ≤ x := mul_le_of_le_one_right hx.le hu.2.le
      have hpos : 0 < 1 - x * u := by nlinarith [hx1, hxu]
      exact Or.inl (ne_of_gt hpos)
    exact (hpow1.mul hpow2).mul hpow3
  have htransIcc : IntegrableOn g (Icc 0 1) := by
    have hbc : 0 < c - (c - b) := by simpa only [show c - (c - b) = b by ring] using hb
    have h := realGaussEulerKernel_integrableOn_Icc (c - a) (c - b) c x hcb hbc hx1
    change IntegrableOn (realGaussEulerTransformedKernel a b c x) (Icc 0 1)
    change IntegrableOn (realGaussEulerKernel (c - a) (c - b) c x) (Icc 0 1) at h
    have hk : realGaussEulerKernel (c - a) (c - b) c x =
        realGaussEulerTransformedKernel a b c x := by
      funext u
      simp only [realGaussEulerKernel, realGaussEulerTransformedKernel]
      rw [show c - (c - b) - 1 = b - 1 by ring]
    exact hk ▸ h
  have htransImage : IntegrableOn g (φ '' Icc 0 1) :=
    htransIcc.mono_set (by
      rintro u ⟨t, ht, rfl⟩
      exact realGaussEulerMobius_mem_Icc x t hx hx1 ht)
  have htransImage' : IntegrableOn g (φ '' uIcc (0 : ℝ) 1) := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using htransImage
  have hgcontImage : ContinuousOn g (φ '' Ioo 0 1) :=
    hgcont.mono (by
      rintro u ⟨t, ht, rfl⟩
      exact realGaussEulerMobius_mem_Ioo x t hx hx1 ht)
  have hgcontImage' : ContinuousOn g (φ '' Ioo (min (0 : ℝ) 1) (max 0 1)) := by
    simpa using hgcontImage
  have hkernelIcc := realGaussEulerKernel_integrableOn_Icc a b c x hb hcb hx1
  have hkernelIoc : IntegrableOn (realGaussEulerKernel a b c x) (Ioc 0 1) :=
    hkernelIcc.mono_set Ioc_subset_Icc_self
  have hcompIoc : IntegrableOn (fun t => g (φ t) * d t) (Ioc 0 1) := by
    have hEq : (fun t => g (φ t) * d t) =ᵐ[volume.restrict (Ioc 0 1)]
        (fun t => -((1 - x) ^ (-(c - a - b))) * realGaussEulerKernel a b c x t) := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [volume.ae_ne (1 : ℝ)] with t ht1 hmem
      exact realGaussEulerMobius_kernel_identity a b c x t hx hx1 hmem.1
        (lt_of_le_of_ne hmem.2 ht1)
    exact (hkernelIoc.const_mul (-((1 - x) ^ (-(c - a - b))))) |>.congr hEq.symm
  have hcompIcc : IntegrableOn (fun t => g (φ t) * d t) (Icc 0 1) := by
    exact (integrableOn_Icc_iff_integrableOn_Ioc).2 hcompIoc
  have hcompIcc' : IntegrableOn (fun t => (g ∘ φ) t * d t) (uIcc (0 : ℝ) 1) := by
    simpa [Function.comp_def, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hcompIcc
  have hφderiv' : ∀ t ∈ Ioo (min (0 : ℝ) 1) (max 0 1),
      HasDerivWithinAt φ (d t) (Ioi t) t := by simpa using hφderiv
  have hφcont' : ContinuousOn φ (uIcc (0 : ℝ) 1) := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hφcont
  have hsub := intervalIntegral.integral_comp_mul_deriv''' (f := φ) (f' := d) (g := g)
    (a := (0 : ℝ)) (b := 1) hφcont' hφderiv' hgcontImage' htransImage' hcompIcc'
  have hφ0 : φ 0 = 1 := by simp [φ, realGaussEulerMobius]
  have hφ1 : φ 1 = 0 := by simp [φ, realGaussEulerMobius]
  have hsub' :
      (∫ t in (0 : ℝ)..1, g (φ t) * d t) =
        -(∫ u in (0 : ℝ)..1, g u) := by
    rw [hφ0, hφ1] at hsub
    have hsymm : (∫ u in (1 : ℝ)..0, g u) = -(∫ u in (0 : ℝ)..1, g u) := by
      rw [intervalIntegral.integral_symm]
    exact hsub.trans hsymm
  have hkernelEq :
      (∫ t in (0 : ℝ)..1, g (φ t) * d t) =
        -((1 - x) ^ (-(c - a - b))) * realGaussEulerKernelIntegral a b c x := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    have hEq : (fun t => g (φ t) * d t) =ᵐ[volume.restrict (Ioc 0 1)]
        (fun t => -((1 - x) ^ (-(c - a - b))) * realGaussEulerKernel a b c x t) := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [volume.ae_ne (1 : ℝ)] with t ht1 hmem
      exact realGaussEulerMobius_kernel_identity a b c x t hx hx1 hmem.1
        (lt_of_le_of_ne hmem.2 ht1)
    rw [integral_congr_ae hEq]
    rw [integral_const_mul]
    rfl
  have hkernelTrans :
      (∫ u in (0 : ℝ)..1, g u) =
        realGaussEulerKernelIntegral (c - a) (c - b) c x := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    simp [realGaussEulerKernelIntegral, g, realGaussEulerTransformedKernel]
  have hraw :
      realGaussEulerKernelIntegral (c - a) (c - b) c x =
        (1 - x) ^ (-(c - a - b)) * realGaussEulerKernelIntegral a b c x := by
    rw [← hkernelTrans]
    calc
      (∫ u in (0 : ℝ)..1, g u) = -(∫ t in (0 : ℝ)..1, g (φ t) * d t) := by
        rw [hsub']
        ring
      _ = (1 - x) ^ (-(c - a - b)) * realGaussEulerKernelIntegral a b c x := by
        rw [hkernelEq]
        ring
  have hnorm : Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b)) =
      Real.Gamma c / (Real.Gamma (c - b) * Real.Gamma b) := by ring
  have hpow : (1 - x) ^ (c - a - b) * (1 - x) ^ (-(c - a - b)) = 1 := by
    rw [← Real.rpow_add (by linarith : 0 < 1 - x)]
    simp
  rw [hnorm, hraw]
  calc
    Real.Gamma c / (Real.Gamma (c - b) * Real.Gamma b) *
        realGaussEulerKernelIntegral a b c x =
      ((1 - x) ^ (c - a - b) * (1 - x) ^ (-(c - a - b))) *
        (Real.Gamma c / (Real.Gamma (c - b) * Real.Gamma b) *
          realGaussEulerKernelIntegral a b c x) := by rw [hpow]; simp
    _ = (1 - x) ^ (c - a - b) *
        (Real.Gamma c / (Real.Gamma (c - b) * Real.Gamma b) *
          ((1 - x) ^ (-(c - a - b)) * realGaussEulerKernelIntegral a b c x)) := by ring

/-- Euler's transformation for the characterized Gauss family on the positive real interval. The
real Euler integral represents both parameter triples, and the Mobius integral identity connects
them. -/
theorem realGaussEulerTransform_family
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c x : ℝ) (ha : 0 < a) (hb : 0 < b) (hca : 0 < c - a)
    (hcb : 0 < c - b) (hx : 0 < x) (hx1 : x < 1) :
    H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) =
      (1 - (x : ℂ)) ^ ((c : ℂ) - (a : ℂ) - (b : ℂ)) *
        H (c - a : ℝ) (c - b : ℝ) (c : ℝ) (x : ℝ) := by
  let N : ℝ := Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))
  let N' : ℝ := Real.Gamma c / (Real.Gamma (c - b) * Real.Gamma b)
  have hbc : 0 < c - (c - b) := by simpa only [show c - (c - b) = b by ring] using hb
  have hOrig := realGaussEulerIntegral_eq_family hH a b c x ha hb hcb hx hx1
  have hTrans := realGaussEulerIntegral_eq_family hH (c - a) (c - b) c x
    hca hcb hbc hx hx1
  have hcb' : c - (c - b) = b := by ring
  have hTrans' : (N' : ℂ) *
      (realGaussEulerKernelIntegral (c - a) (c - b) c x : ℂ) =
        H (c - a : ℝ) (c - b : ℝ) (c : ℝ) (x : ℝ) := by
    simpa [N', realGaussEulerKernelIntegral, hcb'] using hTrans
  have hOrig' : (N : ℂ) * (realGaussEulerKernelIntegral a b c x : ℂ) =
      H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) := by
    simpa [N, realGaussEulerKernelIntegral] using hOrig
  have hraw := realGaussEulerIntegral_eulerTransform a b c x hb hcb hx hx1
  have hrawC := congrArg (fun y : ℝ => (y : ℂ)) hraw
  rw [Complex.ofReal_mul, Complex.ofReal_mul] at hrawC
  have hδcast : ((c - a - b : ℝ) : ℂ) = (c : ℂ) - (a : ℂ) - (b : ℂ) := by
    push_cast
    ring
  have hpowCast : ((1 - x) ^ (c - a - b) : ℝ) =
      (1 - (x : ℂ)) ^ ((c : ℂ) - (a : ℂ) - (b : ℂ)) := by
    rw [← hδcast, show (1 : ℂ) - (x : ℝ) = ((1 - x : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by linarith : 0 ≤ 1 - x)]
  have hrawC' : (N : ℂ) * (realGaussEulerKernelIntegral a b c x : ℂ) =
      (1 - (x : ℂ)) ^ ((c : ℂ) - (a : ℂ) - (b : ℂ)) *
        ((N' : ℂ) * (realGaussEulerKernelIntegral (c - a) (c - b) c x : ℂ)) := by
    simpa only [N, N', Complex.ofReal_mul, hpowCast] using hrawC
  calc
    H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) =
        (N : ℂ) * (realGaussEulerKernelIntegral a b c x : ℂ) := hOrig'.symm
    _ = ((1 - x) ^ (c - a - b) : ℝ) *
        ((N' : ℂ) * (realGaussEulerKernelIntegral (c - a) (c - b) c x : ℂ)) := by
      rw [hpowCast]
      exact hrawC'
    _ = (1 - (x : ℂ)) ^ ((c : ℂ) - (a : ℂ) - (b : ℂ)) *
        H (c - a : ℝ) (c - b : ℝ) (c : ℝ) (x : ℝ) := by
          rw [hpowCast, hTrans']

end DOZZ.Proofs
