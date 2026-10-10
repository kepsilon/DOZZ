/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorWeightedMoments
public import DOZZ.FourPoint.TaylorFixedDisk
public import DOZZ.GMC.SharpMoments.SeibergMoment

/-! Holder interpolation on the same supplied GMC for intermediate-region Taylor moments. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- A weighted local positive mass and the full inverse mass have their sharp joint radius bound.
The measures are the same supplied GMC; the only decoupling is Holder's inequality. -/
theorem weighted_ball_coulomb_mixed_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p s q : ℝ) (hα₁ : α₁ < Q γ) (hp : 0 ≤ p) (hs : 0 < s) (hq : 1 < q)
    (hrange : q * s < min (4 / γ ^ 2) (2 / γ * (Q γ - α₁))) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖z‖ ≤ 1 / 4 → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 2 →
      (∫⁻ ω, (weightedGmcBallMass γ (M ω) α₁ 0 ρ) ^ s *
        (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃) ^ (-p - s) ∂P) ≤
          ENNReal.ofReal (C * ρ ^ ((γ * (Q γ - α₁) * (q * s) -
            γ ^ 2 * (q * s) ^ 2 / 2) / q)) := by
  have hqpos : 0 < q := zero_lt_one.trans hq
  let q' : ℝ := q.conjExponent
  have hHolder : Real.HolderConjugate q q' := Real.HolderConjugate.conjExponent hq
  have hq' : 0 < q' := hHolder.symm.pos
  obtain ⟨CA, hCA, hA⟩ := weighted_ball_moment_small_radius_bound P X hX γ hγ hγ2 M hM
    α₁ (q * s) hα₁ (mul_pos hqpos hs) hrange
  obtain ⟨CB, hCB, hB⟩ := coulomb_inverse_moment_uniform_roots P X hX γ hγ hγ2 M hM
    ![-γ / 2, α₁, α₂] α₃ (q' * (p + s)) (mul_nonneg hq'.le (by linarith only [hp, hs]))
  let C : ℝ := CA ^ (1 / q) * CB ^ (1 / q')
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro z hz ρ hρ hρ2
  have hy : ∀ i : Fin 3, ‖(![z, 0, 1] : Fin 3 → ℂ) i‖ ≤ 1 := by
    intro i
    fin_cases i
    · change ‖z‖ ≤ 1
      linarith only [hz]
    · change ‖(0 : ℂ)‖ ≤ 1
      norm_num
    · change ‖(1 : ℂ)‖ ≤ 1
      norm_num
  have hW := gmc_weighted_mass_aemeasurable P X hX γ hγ hγ2 M hM α₁ 0 ρ
  have hI := gmc_coulombMass_aemeasurable P X hX γ hγ hγ2 M hM ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P hHolder (hW.pow_const s) (hI.pow_const (-p - s))
  have heB : (-p - s) * q' = -(q' * (p + s)) := by ring
  simp only [← ENNReal.rpow_mul, mul_comm s q, heB] at h
  have h1 := ENNReal.rpow_le_rpow (hA ρ hρ hρ2) (by positivity : 0 ≤ 1 / q)
  have h2 := ENNReal.rpow_le_rpow (hB ![z, 0, 1] hy) (by positivity : 0 ≤ 1 / q')
  let E : ℝ := γ * (Q γ - α₁) * (q * s) - γ ^ 2 * (q * s) ^ 2 / 2
  have hscale : 0 < CA * ρ ^ E := mul_pos hCA (Real.rpow_pos_of_pos hρ _)
  have htotal := h.trans (mul_le_mul' h1 h2)
  calc
    _ ≤ (ENNReal.ofReal (CA * ρ ^ E)) ^ (1 / q) * (ENNReal.ofReal CB) ^ (1 / q') := htotal
    _ = ENNReal.ofReal (C * ρ ^ (E / q)) := by
      rw [ENNReal.ofReal_rpow_of_pos hscale, ENNReal.ofReal_rpow_of_pos hCB,
        ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hscale _).le,
        Real.mul_rpow hCA.le (Real.rpow_nonneg hρ.le _), ← Real.rpow_mul hρ.le]
      congr 1
      dsimp only [C]
      rw [show E * (1 / q) = E / q by ring]
      ring

end DOZZ.Proofs
