/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.FreezingAnnulusNegativeMomentLocal

/-! Extending local freezing to every cutoff in `(0,1]` with a fixed retained disk. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- Enlarging the outer domain of a freezing mass can only decrease its inverse moments. -/
theorem freezing_local_le_global (γ α ε R : ℝ) (M : Measure ℂ) (z : ℂ) :
    freezingAnnulusMassLocal γ α M z ε R ≤ freezingAnnulusMass γ α M z ε :=
  lintegral_mono_set (fun _ hx => hx.1)

/-- The supercritical freezing negative-moment estimate [KRV, (freezingannulus)], with its exact
charge threshold and the constant uniform in `0 < ε ≤ 1`. -/
theorem freezing_annulus_negative_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ α p : ℝ) (z : ℂ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hX : IsEquatorGFF P X)
    (hGMC : IsGMCOf P X γ M)
    (hα : Q γ < α) (hp : 0 < p) (hthreshold : α - Q γ < γ * p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        (∫⁻ ω, ENNReal.rpow
          (freezingAnnulusMass γ α (M ω) z ε) (-p) ∂P) ≤
            ENNReal.ofReal (C * ε ^ ((α - Q γ) ^ 2 / 2)) := by
  obtain ⟨C₀, ε₀, hC₀, hε₀, hlocal⟩ := freezing_annulus_negative_moment_local
    P M X γ α p 4 {z} (isCompact_singleton) hγ hγ₂ hX hGMC (by norm_num) hα hp hthreshold
  let η : ℝ := min ε₀ 1
  have hη : 0 < η := lt_min hε₀ zero_lt_one
  have hηε : η ≤ ε₀ := min_le_left _ _
  let d : ℝ := (α - Q γ) ^ 2 / 2
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  let u : ℂ := z + (2 : ℂ)
  let A : Set ℂ := Metric.ball u (1 / 8)
  have hQ : 0 < Q γ := by
    unfold Q
    exact add_pos (div_pos (by norm_num) hγ) (div_pos hγ (by norm_num))
  have hγα : 0 < γ * α := mul_pos hγ (hQ.trans hα)
  let w : ℝ := (3 : ℝ) ^ (-(γ * α))
  have hw : 0 < w := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨Cb, hCb, hball⟩ := equatorGFF_GMC_ball_moment_bound
    P X hX γ hγ hγ₂ M hGMC (-p)
    ((neg_nonpos.mpr hp.le).trans_lt (div_pos (by norm_num) (sq_pos_of_pos hγ)))
    {u} isCompact_singleton
  have hm := (hball u (mem_singleton u) (1 / 8) (by norm_num) (by norm_num)).2
  let D : ℝ := w ^ (-p) * (Cb * (1 / 8 : ℝ) ^
    (γ * Q γ * (-p) - γ ^ 2 * (-p) ^ 2 / 2))
  have hD : 0 < D := by dsimp only [D]; positivity
  have hcoarse (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
      (∫⁻ ω, freezingAnnulusMass γ α (M ω) z ε ^ (-p) ∂P) ≤ ENNReal.ofReal D := by
    have hlower (ω : Ω) : ENNReal.ofReal w * M ω A ≤
        freezingAnnulusMass γ α (M ω) z ε := by
      apply le_trans (b := freezingAnnulusMassLocal γ α (M ω) z ε 4)
      · apply freezing_retained_lower_bound γ α ε 4 w (M ω) z u (1 / 8)
        · intro x hx
          obtain ⟨hl, hu⟩ := retained_disk_radial_bounds z 2 (1 / 8)
            (by norm_num) x hx
          constructor <;> linarith only [hl, hu, hε1]
        · intro x hx
          obtain ⟨hl, hu⟩ := retained_disk_radial_bounds z 2 (1 / 8)
            (by norm_num) x hx
          exact Real.rpow_le_rpow_of_nonpos (by linarith only [hl])
            (by linarith only [hu]) (neg_nonpos.mpr hγα.le)
      · exact freezing_local_le_global γ α ε 4 (M ω) z
    have hfinite (ω : Ω) : M ω A ≠ ⊤ := by
      let _ := hGMC.1 ω
      exact measure_ne_top _ _
    have hh := retained_moment_allocation P
      (fun ω => freezingAnnulusMass γ α (M ω) z ε) (fun ω => M ω A) (fun _ => 0)
      hfinite (fun _ => ENNReal.zero_ne_top) w 1 p 0 hw zero_lt_one hp.le le_rfl
      hlower (fun _ => by simp)
    simp only [add_zero, neg_zero, ENNReal.rpow_zero, mul_one, Real.one_rpow] at hh
    have hh' := hh.trans (mul_le_mul' le_rfl hm)
    exact hh'.trans_eq (ENNReal.ofReal_mul (Real.rpow_pos_of_pos hw _).le).symm
  let C : ℝ := C₀ + D * η ^ (-d)
  have hC : 0 < C := add_pos hC₀ (mul_pos hD (Real.rpow_pos_of_pos hη _))
  refine ⟨C, hC, ?_⟩
  intro ε hε hε1
  by_cases hsmall : ε < η
  · have hl := hlocal z (mem_singleton z) ε hε (hsmall.trans_le hηε)
    have hanti : (∫⁻ ω, freezingAnnulusMass γ α (M ω) z ε ^ (-p) ∂P) ≤
        ∫⁻ ω, freezingAnnulusMassLocal γ α (M ω) z ε 4 ^ (-p) ∂P := by
      apply lintegral_mono
      intro ω
      dsimp only
      rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow
        (freezing_local_le_global γ α ε 4 (M ω) z) hp.le)
    refine (hanti.trans hl).trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_pos_of_pos hε _).le
    exact le_add_of_nonneg_right (mul_nonneg hD.le (Real.rpow_pos_of_pos hη _).le)
  · have hηε' : η ≤ ε := le_of_not_gt hsmall
    have hr : η ^ d ≤ ε ^ d := Real.rpow_le_rpow hη.le hηε' hd
    have hc : D ≤ C * ε ^ d := by
      calc
        D = D * η ^ (-d) * η ^ d := by
          rw [mul_assoc, ← Real.rpow_add hη]
          simp
        _ ≤ D * η ^ (-d) * ε ^ d := mul_le_mul_of_nonneg_left hr (by positivity)
        _ ≤ C * ε ^ d := mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left hC₀.le) (Real.rpow_pos_of_pos hε _).le
    exact (hcoarse ε hε hε1).trans (ENNReal.ofReal_le_ofReal hc)

end DOZZ.Proofs
