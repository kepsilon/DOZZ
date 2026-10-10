/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Mobius.InversionMoment
public import DOZZ.GMC.SharpMoments.SeibergWeight
import DOZZ.GMC.Moments.InversionLaw

/-!
# Inversion exchanges the charges at the origin and at infinity

Under `x ↦ 1/x` the ratio `|x|_+/|x|` becomes `|y|_+`, the background `|x|_+` becomes
`|y|_+/|y|`, and a nonzero root `z` becomes `1/z` with the factor `|z|^{-1}`. With the inversion
law of the chaos, the real moments of the Coulomb mass with a root at the origin (charge `β₀`)
and a charge `βinf` at infinity equal those with the two charges exchanged and the other roots
inverted, times `∏ₖ |zₖ|^{-γ αₖ q}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The background `|y|_+` under inversion, away from the origin. -/
private theorem inversionZero_normPlus_inv {y : ℂ} (hy : y ≠ 0) :
    normPlus y⁻¹ = normPlus y / ‖y‖ := by
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  unfold normPlus
  rw [norm_inv, ← max_div_div_right hyn.le, div_self hyn.ne', one_div, max_comm]

/-- The ratio at the root `0` becomes the background `|y|_+`. -/
private theorem inversionZero_origin_ratio {y : ℂ} (hy : y ≠ 0) :
    normPlus y⁻¹ / ‖y⁻¹ - 0‖ = normPlus y := by
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  rw [inversionZero_normPlus_inv hy, sub_zero, norm_inv]
  field_simp

/-- The ratio at a nonzero root `w` becomes the ratio at the root `w⁻¹`, divided by `|w|`. -/
private theorem inversionZero_root_ratio {y w : ℂ} (hy : y ≠ 0) (hw : w ≠ 0) (hyw : y ≠ w⁻¹) :
    normPlus y⁻¹ / ‖y⁻¹ - w‖ = normPlus y / (‖w‖ * ‖y - w⁻¹‖) := by
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hd : 0 < ‖y - w⁻¹‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyw)
  have hsub : ‖y⁻¹ - w‖ = ‖w‖ * ‖y - w⁻¹‖ / ‖y‖ := by
    rw [show y⁻¹ - w = -w * (y - w⁻¹) / y by field_simp; ring, norm_div, norm_mul, norm_neg]
  rw [inversionZero_normPlus_inv hy, hsub]
  field_simp

/-- The factor `|w|` of the distance to a root splits off with the opposite exponent. -/
private theorem inversionZero_rpow_factor {a n d : ℝ} (ha : 0 < a) (hn : 0 < n) (hd : 0 < d)
    (e : ℝ) :
    ENNReal.rpow (ENNReal.ofReal (a / (n * d))) e =
      ENNReal.rpow (ENNReal.ofReal n) (-e) * ENNReal.rpow (ENNReal.ofReal (a / d)) e := by
  rw [coulombWeight_rpow_ofReal_div ha (mul_pos hn hd), coulombWeight_rpow_ofReal_div ha hd]
  simp only [ENNReal.rpow_eq_pow]
  rw [ENNReal.ofReal_mul hn.le,
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
  ring

/-- **The Coulomb weight through inversion**, with the root at the origin. -/
theorem coulombWeight_inv_cons {N : ℕ} (γ β₀ βinf : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ)
    (hz : ∀ k, z k ≠ 0) {y : ℂ} (hy : y ≠ 0) (hyz : ∀ k, y ≠ (z k)⁻¹) :
    coulombWeight γ (Fin.cons β₀ α : Fin (N + 1) → ℝ) (Fin.cons 0 z : Fin (N + 1) → ℂ) βinf
        y⁻¹ =
      (∏ k, ENNReal.rpow (ENNReal.ofReal ‖z k‖) (-(γ * α k))) *
        coulombWeight γ (Fin.cons βinf α : Fin (N + 1) → ℝ)
          (Fin.cons 0 (fun k => (z k)⁻¹) : Fin (N + 1) → ℂ) β₀ y := by
  have hyp : 0 < normPlus y := lt_of_lt_of_le one_pos (le_max_left _ _)
  unfold coulombWeight
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have hprod : ∏ k, ENNReal.rpow (ENNReal.ofReal (normPlus y⁻¹ / ‖y⁻¹ - z k‖)) (γ * α k) =
      (∏ k, ENNReal.rpow (ENNReal.ofReal ‖z k‖) (-(γ * α k))) *
        ∏ k, ENNReal.rpow (ENNReal.ofReal (normPlus y / ‖y - (z k)⁻¹‖)) (γ * α k) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [inversionZero_root_ratio hy (hz k) (hyz k)]
    exact inversionZero_rpow_factor hyp (norm_pos_iff.mpr (hz k))
      (norm_pos_iff.mpr (sub_ne_zero.mpr (hyz k))) _
  rw [hprod, inversionZero_origin_ratio hy, inversionZero_normPlus_inv hy, sub_zero]
  ring

/-- The constant of the inversion identity is nonzero. -/
private theorem inversionZero_const_ne_zero {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ)
    (hz : ∀ k, z k ≠ 0) :
    (∏ k, ENNReal.rpow (ENNReal.ofReal ‖z k‖) (-(γ * α k))) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro k _
  exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr (hz k)))
    ENNReal.ofReal_ne_top).ne'

/-- The constant of the inversion identity is finite. -/
private theorem inversionZero_const_ne_top {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ)
    (hz : ∀ k, z k ≠ 0) :
    (∏ k, ENNReal.rpow (ENNReal.ofReal ‖z k‖) (-(γ * α k))) ≠ ⊤ :=
  ENNReal.prod_ne_top fun k _ => ENNReal.rpow_ne_top_of_ne_zero
    (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr (hz k))).ne' ENNReal.ofReal_ne_top

/-- The inversion identity integrates against a measure without atoms at `0` and at the inverted
roots. -/
private theorem inversionZero_map_lintegral {N : ℕ} (γ β₀ βinf : ℝ) (α : Fin N → ℝ)
    (z : Fin N → ℂ) (hz : ∀ k, z k ≠ 0) (μ : Measure ℂ) (h0 : μ {0} = 0)
    (hk : ∀ k, μ {(z k)⁻¹} = 0) :
    ∫⁻ x, coulombWeight γ (Fin.cons β₀ α : Fin (N + 1) → ℝ) (Fin.cons 0 z : Fin (N + 1) → ℂ)
        βinf x ∂μ.map (fun x => x⁻¹) =
      (∏ k, ENNReal.rpow (ENNReal.ofReal ‖z k‖) (-(γ * α k))) *
        coulombMass γ μ (Fin.cons βinf α : Fin (N + 1) → ℝ)
          (Fin.cons 0 (fun k => (z k)⁻¹) : Fin (N + 1) → ℂ) β₀ := by
  rw [lintegral_map (measurable_coulombWeight _ _ _ _) measurable_inv,
    coulombMass_eq_lintegral_coulombWeight,
    ← lintegral_const_mul' _ _ (inversionZero_const_ne_top γ α z hz)]
  apply lintegral_congr_ae
  have hnull : μ ({0} ∪ ⋃ k, {(z k)⁻¹}) = 0 :=
    measure_union_null h0 (measure_iUnion_null hk)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with y hy
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_iUnion, not_or, not_exists] at hy
  exact coulombWeight_inv_cons γ β₀ βinf α z hz hy.1 fun k h => hy.2 k h

/-- **Coulomb moments through inversion**, exchanging the charges at `0` and `∞`. -/
theorem coulombMass_inv_moment_cons {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) {N : ℕ} (β₀ βinf : ℝ) (α : Fin N → ℝ)
    (z : Fin N → ℂ) (hz : ∀ k, z k ≠ 0) (q : ℝ) :
    ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) (Fin.cons β₀ α : Fin (N + 1) → ℝ)
        (Fin.cons 0 z : Fin (N + 1) → ℂ) βinf) q ∂P =
      ENNReal.rpow (∏ k, ENNReal.rpow (ENNReal.ofReal ‖z k‖) (-(γ * α k))) q *
        ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) (Fin.cons βinf α : Fin (N + 1) → ℝ)
          (Fin.cons 0 (fun k => (z k)⁻¹) : Fin (N + 1) → ℂ) β₀) q ∂P := by
  have hc0 := inversionZero_const_ne_zero γ α z hz
  have hct := inversionZero_const_ne_top γ α z hz
  have hH : Measurable fun μ : Measure ℂ =>
      ENNReal.rpow (∫⁻ x, coulombWeight γ (Fin.cons β₀ α : Fin (N + 1) → ℝ)
        (Fin.cons 0 z : Fin (N + 1) → ℂ) βinf x ∂μ) q :=
    (Measure.measurable_lintegral (measurable_coulombWeight _ _ _ _)).pow_const q
  have hlaw := equatorGFF_GMC_inversion_law P X hX γ hγ hγ2 M hM _ hH
  -- almost surely no atom at the origin or at any inverted root
  have hatoms : ∀ᵐ ω ∂P, M ω {0} = 0 ∧ ∀ k, M ω {(z k)⁻¹} = 0 := by
    have h0 := gmc_atomless_of_isGMCOf P X hX γ hγ hγ2 M hM 0
    have hk : ∀ᵐ ω ∂P, ∀ k, M ω {(z k)⁻¹} = 0 :=
      ae_all_iff.2 fun k => gmc_atomless_of_isGMCOf P X hX γ hγ hγ2 M hM (z k)⁻¹
    filter_upwards [h0, hk] with ω h1 h2 using ⟨h1, h2⟩
  calc
    ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) (Fin.cons β₀ α : Fin (N + 1) → ℝ)
        (Fin.cons 0 z : Fin (N + 1) → ℂ) βinf) q ∂P
        = ∫⁻ ω, ENNReal.rpow (∫⁻ x, coulombWeight γ (Fin.cons β₀ α : Fin (N + 1) → ℝ)
            (Fin.cons 0 z : Fin (N + 1) → ℂ) βinf x ∂M ω) q ∂P := by
      congr 1
    _ = ∫⁻ ω, ENNReal.rpow ((∏ k, ENNReal.rpow (ENNReal.ofReal ‖z k‖) (-(γ * α k))) *
          coulombMass γ (M ω) (Fin.cons βinf α : Fin (N + 1) → ℝ)
            (Fin.cons 0 (fun k => (z k)⁻¹) : Fin (N + 1) → ℂ) β₀) q ∂P := by
      rw [← hlaw]
      apply lintegral_congr_ae
      filter_upwards [hatoms] with ω hω
      rw [inversionZero_map_lintegral γ β₀ βinf α z hz (M ω) hω.1 hω.2]
    _ = ∫⁻ ω, ENNReal.rpow (∏ k, ENNReal.rpow (ENNReal.ofReal ‖z k‖) (-(γ * α k))) q *
          ENNReal.rpow (coulombMass γ (M ω) (Fin.cons βinf α : Fin (N + 1) → ℝ)
            (Fin.cons 0 (fun k => (z k)⁻¹) : Fin (N + 1) → ℂ) β₀) q ∂P := by
      congr 1
      funext ω
      exact inversionMoment_mul_rpow hc0 hct _ q
    _ = _ := lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero hc0 hct)

end DOZZ.Proofs

end
