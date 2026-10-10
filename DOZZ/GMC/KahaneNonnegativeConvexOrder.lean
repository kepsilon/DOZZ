/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.KahaneConvexOrderClosure
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Convex power comparison for nonnegative limits, including atoms at zero. -/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- Shifting away from zero allows the affine supporting-function argument to compare
nonnegative masses which may vanish. -/
theorem nonneg_power_comparison_of_affine_max_order
    {ΩX ΩY : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    (PX : Measure ΩX) (PY : Measure ΩY) [IsProbabilityMeasure PX] [IsProbabilityMeasure PY]
    (MX : ΩX → ℝ) (MY : ΩY → ℝ) (hMX : Integrable MX PX) (hMY : Integrable MY PY)
    (hMX0 : ∀ᵐ ω ∂PX, 0 ≤ MX ω) (hMY0 : ∀ᵐ ω ∂PY, 0 ≤ MY ω)
    (hmean : (∫ ω, MX ω ∂PX) = ∫ ω, MY ω ∂PY)
    (horder : ∀ (n : ℕ) (a b : Fin (n + 1) → ℝ),
      (∫ ω, affineMax a b (MX ω) ∂PX) ≤ ∫ ω, affineMax a b (MY ω) ∂PY)
    (p : ℝ) (hp : 1 ≤ p) :
    (∫⁻ ω, ENNReal.ofReal (MX ω) ^ p ∂PX) ≤ ∫⁻ ω, ENNReal.ofReal (MY ω) ^ p ∂PY := by
  classical
  let F : ℝ → ℝ := fun x => (max (x - 1) 0) ^ p
  have hF : Measurable F := by fun_prop
  have hinner : ConvexOn ℝ (Ici (0 : ℝ)) (fun x => max (x - 1) 0) :=
    by
      have hid : ConvexOn ℝ (Ici (0 : ℝ)) (fun x : ℝ => x - 1) := by
        convert (convexOn_id (𝕜 := ℝ) (convex_Ici (0 : ℝ))).add_const (-1) using 1
        funext x
        rfl
      exact hid.sup (convexOn_const 0 (convex_Ici (0 : ℝ)))
  have himage : (fun x : ℝ => max (x - 1) 0) '' Ici 0 = Ici 0 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact le_max_right _ _
    · intro hy
      refine ⟨y + 1, by simp only [mem_Ici] at hy ⊢; linarith, ?_⟩
      simp only [add_sub_cancel_right, max_eq_left hy]
  have hconvex : ConvexOn ℝ (Ici 0) F := by
    have hout : ConvexOn ℝ ((fun x : ℝ => max (x - 1) 0) '' Ici 0) (fun x => x ^ p) := by
      rw [himage]
      exact convexOn_rpow hp
    have hmono : MonotoneOn (fun x : ℝ => x ^ p) ((fun x : ℝ => max (x - 1) 0) '' Ici 0) := by
      rw [himage]
      exact Real.monotoneOn_rpow_Ici_of_exponent_nonneg (by linarith)
    exact hout.comp hinner hmono
  have hFX : ∀ᵐ ω ∂PX, ENNReal.ofReal (MX ω) ^ p = ENNReal.ofReal (F (MX ω + 1)) := by
    filter_upwards [hMX0] with ω hω
    dsimp [F]
    rw [add_sub_cancel_right, max_eq_left hω, ENNReal.ofReal_rpow_of_nonneg hω (by linarith)]
  have hFY : ∀ᵐ ω ∂PY, ENNReal.ofReal (MY ω) ^ p = ENNReal.ofReal (F (MY ω + 1)) := by
    filter_upwards [hMY0] with ω hω
    dsimp [F]
    rw [add_sub_cancel_right, max_eq_left hω, ENNReal.ofReal_rpow_of_nonneg hω (by linarith)]
  rw [lintegral_congr_ae hFX, lintegral_congr_ae hFY]
  by_cases htop : (∫⁻ ω, ENNReal.ofReal (F (MY ω + 1)) ∂PY) = ∞
  · rw [htop]
    exact le_top
  have hFY0 (ω : ΩY) : 0 ≤ F (MY ω + 1) := Real.rpow_nonneg (le_max_right _ _) _
  have hFX0 (ω : ΩX) : 0 ≤ F (MX ω + 1) := Real.rpow_nonneg (le_max_right _ _) _
  have hIY : Integrable (fun ω => F (MY ω + 1)) PY :=
    ⟨(hF.comp_aemeasurable (hMY.aemeasurable.add_const 1)).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ hFY0)).2 (lt_top_iff_ne_top.mpr htop)⟩
  have hshift (n : ℕ) (a b : Fin (n + 1) → ℝ) (x : ℝ) :
      affineMax a b (x + 1) = affineMax a (fun i => a i + b i) x := by
    unfold affineMax
    congr 1
    funext i
    ring
  have hmean' : (∫ ω, MX ω + 1 ∂PX) = ∫ ω, MY ω + 1 ∂PY := by
    rw [integral_add hMX (integrable_const 1), integral_add hMY (integrable_const 1), hmean]
    simp
  have hcmp := convex_comparison_of_affine_max_order PX PY
    (fun ω => MX ω + 1) (fun ω => MY ω + 1)
    (hMX.add (integrable_const 1)) (hMY.add (integrable_const 1))
    (hMX0.mono fun ω hω => by linarith) (hMY0.mono fun ω hω => by linarith)
    hmean' (fun n a b => by simpa only [hshift] using horder n a (fun i => a i + b i))
    F hF hconvex hIY
  rw [← ofReal_integral_eq_lintegral_ofReal hcmp.1 (ae_of_all _ hFX0),
    ← ofReal_integral_eq_lintegral_ofReal hIY (ae_of_all _ hFY0)]
  exact ENNReal.ofReal_le_ofReal hcmp.2

end DOZZ.Proofs
