/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionEulerTransform
public import DOZZ.Hypergeom.ODE.ConnectionEndpointLimits
public import DOZZ.Hypergeom.ODE.ConnectionGammaCoefficients

/-! Evaluation of the second zero-basis connection coefficient from Euler's transformation. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter Set
open scoped Topology

/-- On the negative-excess real Euler region, the second midpoint Cramer coefficient is the
second Gamma coefficient. Euler's transformation converts the endpoint into a positive-excess
Euler integral, where dominated convergence applies. -/
theorem connectionMinusSecondCramer_eq_gamma_of_real
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hca : 0 < c - a) (hcb : 0 < c - b) (hδ : c - a - b < 0)
    (hcInt : (c : ℂ) ∈ gaussConnectionIntegerRangeᶜ)
    (hδInt : ((c - a - b : ℝ) : ℂ) ∈ gaussConnectionIntegerRangeᶜ) :
    connectionMinusSecondCramerCoefficient H (a, b, c) =
      gaussConnectionMinusGammaCoefficient₂ (a, b, c) := by
  let p : ℂ × ℂ × ℂ := (a, b, c)
  have hc : 0 < c := by linarith
  have heta : 0 < a + b - c := by linarith
  have hp : p ∈ gaussConnectionParameterDomain := by
    change (∀ n : ℤ, (c : ℂ) ≠ (n : ℂ)) ∧
      ∀ n : ℤ, (c : ℂ) - (a : ℂ) - (b : ℂ) ≠ (n : ℂ)
    constructor
    · intro n heq
      apply hcInt
      exact ⟨n, heq.symm⟩
    · intro n heq
      apply hδInt
      refine ⟨n, ?_⟩
      calc
        (n : ℂ) = (c : ℂ) - (a : ℂ) - (b : ℂ) := heq.symm
        _ = ((c - a - b : ℝ) : ℂ) := by push_cast; ring
  let F : Filter ℝ := 𝓝[Iio 1] 1
  let η : ℝ := a + b - c
  have hη : η = c - (c - a) - (c - b) := by dsimp [η]; ring
  have hη' : c - (c - a) - (c - b) = η := hη.symm
  have hca' : c - (c - a) = a := by ring
  have hcb' : c - (c - b) = b := by ring
  have hη'' : a - (c - b) = η := by dsimp [η]; ring
  have hcbTrans : 0 < c - (c - b) := by
    rw [hcb']
    exact hb
  have hEulerValue := realGaussEulerKernelIntegral_tendsto_gauss_value
    (c - a) (c - b) c hca hcb (by rw [show c - (c - a) - (c - b) = a + b - c by ring]; exact heta)
  have hEulerValueC : Tendsto
      (fun x : ℝ =>
        ((Real.Gamma c / (Real.Gamma (c - b) * Real.Gamma b) : ℂ) *
          (realGaussEulerKernelIntegral (c - a) (c - b) c x : ℂ)))
      F
      (𝓝 ((Real.Gamma c * Real.Gamma η /
        (Real.Gamma a * Real.Gamma b) : ℝ) : ℂ)) := by
    have hvalue' : Tendsto
        (fun x : ℝ =>
          (Real.Gamma c / (Real.Gamma (c - b) * Real.Gamma b)) *
            realGaussEulerKernelIntegral (c - a) (c - b) c x)
        F (𝓝 (Real.Gamma c * Real.Gamma η /
          (Real.Gamma a * Real.Gamma b))) := by
      simpa only [hca', hcb', hη''] using hEulerValue
    have hvalueC0 : Tendsto
        (fun x : ℝ =>
          (((Real.Gamma c / (Real.Gamma (c - b) * Real.Gamma b) : ℝ) *
            realGaussEulerKernelIntegral (c - a) (c - b) c x : ℝ) : ℂ))
        F (𝓝 ((Real.Gamma c * Real.Gamma η /
          (Real.Gamma a * Real.Gamma b) : ℝ) : ℂ)) := by
      simpa only [Function.comp_def] using
        (Complex.continuous_ofReal.continuousAt.tendsto.comp hvalue')
    have hEq : (fun x : ℝ =>
        (((Real.Gamma c / (Real.Gamma (c - b) * Real.Gamma b) : ℝ) *
          realGaussEulerKernelIntegral (c - a) (c - b) c x : ℝ) : ℂ)) =ᶠ[F]
        (fun x : ℝ =>
          ((Real.Gamma c / (Real.Gamma (c - b) * Real.Gamma b) : ℂ) *
            (realGaussEulerKernelIntegral (c - a) (c - b) c x : ℂ))) := by
      filter_upwards with x
      rw [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_mul]
    exact hvalueC0.congr' hEq
  have hxpos : ∀ᶠ x : ℝ in F, 0 < x := by
    dsimp [F]
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))
  have hxlt : ∀ᶠ x : ℝ in F, x < 1 := by
    dsimp [F]
    change ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x ∈ Iio 1
    simpa only [mem_Iio] using
      (eventually_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x ∈ Iio 1)
  have hδcast : ((c - a - b : ℝ) : ℂ) = (c : ℂ) - (a : ℂ) - (b : ℂ) := by
    push_cast
    ring
  have hEulerEq :
      (fun x : ℝ => (1 - (x : ℂ)) ^ (-((c : ℂ) - (a : ℂ) - (b : ℂ))) *
        gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)) =ᶠ[F]
      (fun x : ℝ =>
        (Real.Gamma c : ℂ) /
          ((Real.Gamma (c - b) : ℂ) * (Real.Gamma b : ℂ)) *
          (realGaussEulerKernelIntegral (c - a) (c - b) c x : ℂ)) := by
    filter_upwards [hxpos, hxlt] with x hx hx1
    have htransform := realGaussEulerTransform_family hH a b c x ha hb hca hcb hx hx1
    have hfamily := realGaussEulerIntegral_eq_family hH (c - a) (c - b) c x
      hca hcb hcbTrans hx hx1
    have hbase : (1 : ℂ) - (x : ℂ) ≠ 0 := by
      apply sub_ne_zero.mpr
      exact_mod_cast (ne_of_lt hx1).symm
    have hcancel :
        (1 - (x : ℂ)) ^ (-((c : ℂ) - (a : ℂ) - (b : ℂ))) *
          ((1 - (x : ℂ)) ^ ((c : ℂ) - (a : ℂ) - (b : ℂ)) *
            H (c - a : ℝ) (c - b : ℝ) (c : ℝ) (x : ℝ)) =
          H (c - a : ℝ) (c - b : ℝ) (c : ℝ) (x : ℝ) := by
      rw [← mul_assoc, ← Complex.cpow_add _ _ hbase, neg_add_cancel,
        Complex.cpow_zero, one_mul]
    calc
      _ = (1 - (x : ℂ)) ^ (-((c : ℂ) - (a : ℂ) - (b : ℂ))) *
          ((1 - (x : ℂ)) ^ ((c : ℂ) - (a : ℂ) - (b : ℂ)) *
            H (c - a : ℝ) (c - b : ℝ) (c : ℝ) (x : ℝ)) := by
        rw [show gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) =
          H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) by rfl, htransform]
      _ = H (c - a : ℝ) (c - b : ℝ) (c : ℝ) (x : ℝ) := hcancel
      _ = (Real.Gamma c : ℂ) /
          ((Real.Gamma (c - b) : ℂ) * (Real.Gamma b : ℂ)) *
          (realGaussEulerKernelIntegral (c - a) (c - b) c x : ℂ) := by
        simpa [realGaussEulerKernelIntegral, Complex.ofReal_div,
          Complex.ofReal_mul] using hfamily.symm
  have hscaled : Tendsto
      (fun x : ℝ => (1 - (x : ℂ)) ^
        (-((c : ℂ) - (a : ℂ) - (b : ℂ))) *
          gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ))
      F (𝓝 ((Real.Gamma c * Real.Gamma η /
        (Real.Gamma a * Real.Gamma b) : ℝ) : ℂ)) :=
    hEulerValueC.congr' hEulerEq.symm
  have hcastEta : p.1 + p.2.1 - p.2.2 = ((a + b - c : ℝ) : ℂ) := by
    change (a : ℂ) + (b : ℂ) - (c : ℂ) = ((a + b - c : ℝ) : ℂ)
    push_cast
    ring
  have hδendpoint : 0 < (p.1 + p.2.1 - p.2.2).re := by
    rw [hcastEta]
    simp only [Complex.ofReal_re]
    exact heta
  have hcoeff := connectionMinusSecondCramer_eq_of_scaled_endpoint_limit
    hH hp hδendpoint (by simpa [F, p, η] using hscaled)
  have hGamma :
      ((Real.Gamma c * Real.Gamma η /
          (Real.Gamma a * Real.Gamma b) : ℝ) : ℂ) =
        gaussConnectionMinusGammaCoefficient₂ p := by
    have hΓc : Real.Gamma c ≠ 0 := (Real.Gamma_pos_of_pos hc).ne'
    have hΓη : Real.Gamma η ≠ 0 := (Real.Gamma_pos_of_pos heta).ne'
    have hΓa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
    have hΓb : Real.Gamma b ≠ 0 := (Real.Gamma_pos_of_pos hb).ne'
    dsimp [gaussConnectionMinusGammaCoefficient₂, p, η]
    rw [show (a : ℂ) + (b : ℂ) - (c : ℂ) = ((a + b - c : ℝ) : ℂ) by
      push_cast; ring,
      Complex.Gamma_ofReal c, Complex.Gamma_ofReal (a + b - c),
      Complex.Gamma_ofReal a, Complex.Gamma_ofReal b]
    push_cast
    field_simp [hΓc, hΓη, hΓa, hΓb]
  have hGamma' :
      (Real.Gamma c : ℂ) * (Real.Gamma η : ℂ) /
          ((Real.Gamma a : ℂ) * (Real.Gamma b : ℂ)) =
        gaussConnectionMinusGammaCoefficient₂ p := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_div] using hGamma
  simpa [p] using hcoeff.trans hGamma'

end DOZZ.Proofs
