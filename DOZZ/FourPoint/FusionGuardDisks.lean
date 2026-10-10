/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.RetainedAnnuliGeometry
public import DOZZ.Statements.FourPoint.FourFusionMass

/-! A finite family of disks supplies a uniform disk avoiding four insertion roots. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Five equally spaced candidates cannot all lie within the guard radius of four roots. -/
theorem four_root_guard_center (y : Fin 4 → ℂ) (z : ℂ) (r t : ℝ) (hr : 0 < r) :
    ∃ j : Fin 5, ∀ i : Fin 4,
      r / 20 ≤ ‖(z + (((t + (j.val : ℝ) / 5) * r : ℝ) : ℂ)) - y i‖ := by
  classical
  by_contra h
  push Not at h
  choose f hf using h
  have hinj : Function.Injective f := by
    intro j k heq
    by_contra hne
    have hdist :
        ‖(z + (((t + (j.val : ℝ) / 5) * r : ℝ) : ℂ)) -
          (z + (((t + (k.val : ℝ) / 5) * r : ℝ) : ℂ))‖ < r / 10 := by
      have hh := norm_sub_le_norm_sub_add_norm_sub
        (z + (((t + (j.val : ℝ) / 5) * r : ℝ) : ℂ)) (y (f j))
        (z + (((t + (k.val : ℝ) / 5) * r : ℝ) : ℂ))
      rw [norm_sub_rev (y (f j))] at hh
      have hk := hf k
      rw [← heq] at hk
      linarith only [hh, hf j, hk]
    have he : (z + (((t + (j.val : ℝ) / 5) * r : ℝ) : ℂ)) -
        (z + (((t + (k.val : ℝ) / 5) * r : ℝ) : ℂ)) =
        (((((j.val : ℝ) - (k.val : ℝ)) / 5) * r : ℝ) : ℂ) := by
      push_cast
      ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_div,
      abs_of_pos hr] at hdist
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 5)] at hdist
    have hdiff : |(j.val : ℝ) - (k.val : ℝ)| < 1 / 2 := by
      nlinarith only [hdist, hr]
    have hval : j.val ≠ k.val := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hval with hjk | hkj
    · have hh : (j.val : ℝ) + 1 ≤ (k.val : ℝ) := by exact_mod_cast hjk
      have hab := (abs_lt.mp hdiff).1
      linarith only [hh, hab]
    · have hh : (k.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast hkj
      have hab := (abs_lt.mp hdiff).2
      linarith only [hh, hab]
  have hcard := Fintype.card_le_of_injective f hinj
  norm_num at hcard

/-- Every point of the selected disk remains a positive distance from all four roots. -/
theorem guard_disk_root_distance (y : Fin 4 → ℂ) (z : ℂ) (r t : ℝ)
    (j : Fin 5)
    (hj : ∀ i : Fin 4, r / 20 ≤ ‖(z + (((t + (j.val : ℝ) / 5) * r : ℝ) : ℂ)) - y i‖)
    (x : ℂ) (hx : x ∈ Metric.ball (z + (((t + (j.val : ℝ) / 5) * r : ℝ) : ℂ)) (r / 100)) :
    ∀ i : Fin 4, r / 25 < ‖x - y i‖ := by
  intro i
  have hx' : ‖x - (z + (((t + (j.val : ℝ) / 5) * r : ℝ) : ℂ))‖ < r / 100 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hh := norm_sub_le_norm_sub_add_norm_sub (z + (((t + (j.val : ℝ) / 5) * r : ℝ) : ℂ)) x (y i)
  rw [norm_sub_rev _ x] at hh
  linarith only [hh, hx', hj i]

/-- A kernel lower bound on a retained disk supplies a lower mass for the literal fusion mass. -/
theorem four_fusion_retained_lower (γ R w : ℝ) (M : Measure ℂ)
    (α : Fin 4 → ℝ) (y : Fin 4 → ℂ) (u : ℂ) (ρ : ℝ)
    (hsub : Metric.ball u ρ ⊆ Metric.ball (y 0) R)
    (hw : ∀ x ∈ Metric.ball u ρ, w ≤ 1 / ∏ i : Fin 4, ‖x - y i‖ ^ (γ * α i)) :
    ENNReal.ofReal w * M (Metric.ball u ρ) ≤ fourFusionMass γ M α y R := by
  calc
    _ = ∫⁻ x in Metric.ball u ρ, ENNReal.ofReal w ∂M := by simp
    _ ≤ ∫⁻ x in Metric.ball u ρ,
        ENNReal.ofReal (1 / ∏ i : Fin 4, ‖x - y i‖ ^ (γ * α i)) ∂M := by
      apply setLIntegral_mono' Metric.isOpen_ball.measurableSet
      intro x hx
      exact ENNReal.ofReal_le_ofReal (hw x hx)
    _ ≤ fourFusionMass γ M α y R := lintegral_mono_set hsub

end DOZZ.Proofs
