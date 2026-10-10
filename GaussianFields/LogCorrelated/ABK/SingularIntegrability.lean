/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import GaussianFields.LogCorrelated.ABK.KernelPairing

/-!
# GaussianFields.LogCorrelated/ABK/SingularIntegrability

Port of the corresponding GaussianFields source module.
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace GaussianFields


/-- The one-dimensional singular exponent used for a concrete integrable majorant. -/
@[expose]
noncomputable def abkSingularMajorantExponent : ℝ := -(3 / 4 : ℝ)

/-- Elementary bound used to control difference quotients of powers. -/
theorem real_exp_sub_one_le_mul_exp_of_nonneg {t : ℝ} (_ht : 0 ≤ t) :
    Real.exp t - 1 ≤ t * Real.exp t := by
  have hneg := Real.add_one_le_exp (-t)
  have hunit : 1 - Real.exp (-t) ≤ t := by linarith
  have hmul := mul_le_mul_of_nonneg_right hunit (le_of_lt (Real.exp_pos t))
  calc
    Real.exp t - 1 = Real.exp t * (1 - Real.exp (-t)) := by
      rw [mul_sub, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
    _ ≤ Real.exp t * t := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    _ = t * Real.exp t := by ring_nf

/-- On a bounded interval away from infinity, the centered Riesz slope is dominated by the
integrable singular power `ρ^{-3/4}`. -/
theorem abs_rpow_neg_sub_one_div_le_abkSingularMajorant {α ρ R : ℝ}
    (hα_pos : 0 < α) (hα_le : α ≤ 1 / 2)
    (hρ_pos : 0 < ρ) (hρR : ρ ≤ R) (hR : 1 ≤ R) :
    |(ρ ^ (-α) - 1) / α| ≤
      (4 + Real.log R) * (1 + ρ ^ abkSingularMajorantExponent) := by
  have hlogR_nonneg : 0 ≤ Real.log R :=
    Real.log_nonneg hR
  have hcoef_nonneg : 0 ≤ 4 + Real.log R := by linarith
  have hsing_nonneg : 0 ≤ ρ ^ abkSingularMajorantExponent :=
    Real.rpow_nonneg hρ_pos.le _
  by_cases hρ_le_one : ρ ≤ 1
  · let u : ℝ := ρ⁻¹
    have hu_pos : 0 < u := inv_pos.mpr hρ_pos
    have hu_one : 1 ≤ u := by
      dsimp [u]
      exact (one_le_inv₀ hρ_pos).mpr hρ_le_one
    have hu_pow_ge : 1 ≤ u ^ α :=
      Real.one_le_rpow hu_one hα_pos.le
    have hslope_nonneg : 0 ≤ (ρ ^ (-α) - 1) / α := by
      rw [Real.rpow_neg_eq_inv_rpow]
      exact div_nonneg (sub_nonneg.mpr hu_pow_ge) hα_pos.le
    have hslope_eq :
        |(ρ ^ (-α) - 1) / α| = (u ^ α - 1) / α := by
      rw [abs_of_nonneg hslope_nonneg, Real.rpow_neg_eq_inv_rpow]
    have hlogu_nonneg : 0 ≤ Real.log u :=
      Real.log_nonneg hu_one
    have hv_nonneg : 0 ≤ α * Real.log u :=
      mul_nonneg hα_pos.le hlogu_nonneg
    have hpow_sub :
        u ^ α - 1 ≤ (α * Real.log u) * u ^ α := by
      rw [Real.rpow_def_of_pos hu_pos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        real_exp_sub_one_le_mul_exp_of_nonneg hv_nonneg
    have hdiv :
        (u ^ α - 1) / α ≤ Real.log u * u ^ α := by
      rw [div_le_iff₀ hα_pos]
      calc
        u ^ α - 1 ≤ (α * Real.log u) * u ^ α := hpow_sub
        _ = α * (Real.log u * u ^ α) := by ring_nf
        _ = Real.log u * u ^ α * α := by ring_nf
    have hlog_bound : Real.log u ≤ 4 * u ^ (1 / 4 : ℝ) := by
      have h := Real.log_le_rpow_div hu_pos.le (by norm_num : (0 : ℝ) < 1 / 4)
      calc
        Real.log u ≤ u ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) := h
        _ = 4 * u ^ (1 / 4 : ℝ) := by ring_nf
    have hpow_le : u ^ α ≤ u ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hu_one hα_le
    have hmain :
        |(ρ ^ (-α) - 1) / α| ≤ 4 * ρ ^ abkSingularMajorantExponent := by
      rw [hslope_eq]
      calc
        (u ^ α - 1) / α ≤ Real.log u * u ^ α := hdiv
        _ ≤ (4 * u ^ (1 / 4 : ℝ)) * u ^ (1 / 2 : ℝ) := by
          exact mul_le_mul hlog_bound hpow_le
            (Real.rpow_nonneg hu_pos.le _)
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
              (Real.rpow_nonneg hu_pos.le _))
        _ = 4 * u ^ (3 / 4 : ℝ) := by
          calc
            (4 * u ^ (1 / 4 : ℝ)) * u ^ (1 / 2 : ℝ)
                = 4 * (u ^ (1 / 4 : ℝ) * u ^ (1 / 2 : ℝ)) := by ring_nf
            _ = 4 * u ^ ((1 / 4 : ℝ) + (1 / 2 : ℝ)) := by
              rw [Real.rpow_add hu_pos]
            _ = 4 * u ^ (3 / 4 : ℝ) := by ring_nf
        _ = 4 * ρ ^ abkSingularMajorantExponent := by
          have hpow_eq : u ^ (3 / 4 : ℝ) = ρ ^ abkSingularMajorantExponent := by
            dsimp [u, abkSingularMajorantExponent]
            rw [← Real.rpow_neg_eq_inv_rpow]
          rw [hpow_eq]
    calc
      |(ρ ^ (-α) - 1) / α| ≤ 4 * ρ ^ abkSingularMajorantExponent := hmain
      _ ≤ (4 + Real.log R) * ρ ^ abkSingularMajorantExponent := by
        exact mul_le_mul_of_nonneg_right (by linarith) hsing_nonneg
      _ ≤ (4 + Real.log R) * (1 + ρ ^ abkSingularMajorantExponent) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hcoef_nonneg
  · have hρ_ge_one : 1 ≤ ρ := le_of_not_ge hρ_le_one
    have hpow_le_one : ρ ^ (-α) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hρ_ge_one (neg_nonpos.mpr hα_pos.le)
    have hslope_nonpos : (ρ ^ (-α) - 1) / α ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hpow_le_one) hα_pos.le
    have hslope_eq :
        |(ρ ^ (-α) - 1) / α| = (1 - ρ ^ (-α)) / α := by
      rw [abs_of_nonpos hslope_nonpos]
      ring_nf
    have hlogρ_nonneg : 0 ≤ Real.log ρ :=
      Real.log_nonneg hρ_ge_one
    have hsub_le :
        1 - ρ ^ (-α) ≤ α * Real.log ρ := by
      have h :=
        Real.add_one_le_exp (-(α * Real.log ρ))
      have hpow_exp : ρ ^ (-α) = Real.exp (-(α * Real.log ρ)) := by
        rw [Real.rpow_def_of_pos hρ_pos]
        congr 1
        ring_nf
      linarith
    have hdiv :
        (1 - ρ ^ (-α)) / α ≤ Real.log ρ := by
      rw [div_le_iff₀ hα_pos]
      calc
        1 - ρ ^ (-α) ≤ α * Real.log ρ := hsub_le
        _ = Real.log ρ * α := by ring_nf
    have hlog_le : Real.log ρ ≤ Real.log R :=
      Real.log_le_log hρ_pos hρR
    calc
      |(ρ ^ (-α) - 1) / α| = (1 - ρ ^ (-α)) / α := hslope_eq
      _ ≤ Real.log ρ := hdiv
      _ ≤ Real.log R := hlog_le
      _ ≤ 4 + Real.log R := by linarith
      _ ≤ (4 + Real.log R) * (1 + ρ ^ abkSingularMajorantExponent) := by
        calc
          4 + Real.log R = (4 + Real.log R) * 1 := by ring_nf
          _ ≤ (4 + Real.log R) * (1 + ρ ^ abkSingularMajorantExponent) := by
            exact mul_le_mul_of_nonneg_left (by linarith) hcoef_nonneg

/-- The one-dimensional function `|x|^{-3/4}`, restricted to a symmetric interval. -/
@[expose]
noncomputable def abkOneDimensionalSingularMajorant (R : ℝ) (x : ℝ) : ℝ :=
  (Set.Icc (-R) R).indicator (fun t : ℝ => |t| ^ abkSingularMajorantExponent) x

/-- A coordinate-box majorant with one singular coordinate and bounded indicators in all other
coordinates. -/
@[expose]
noncomputable def abkCoordinateBoxSingularMajorant {d : Nat} (i : Fin d) (R : ℝ)
    (x : Vec d) : ℝ :=
  ∏ j : Fin d,
    if j = i then
      abkOneDimensionalSingularMajorant R (x j)
    else
      (Set.Icc (-R) R).indicator (fun _ : ℝ => (1 : ℝ)) (x j)

/-- Indicator of the coordinate box `[-R,R]^d`, written as a product of one-dimensional
indicators. -/
@[expose]
noncomputable def abkBoxIndicatorVec {d : Nat} (R : ℝ) (x : Vec d) : ℝ :=
  ∏ j : Fin d, (Set.Icc (-R) R).indicator (fun _ : ℝ => (1 : ℝ)) (x j)

/-- Pair-space singular majorant after the additive shear `(x,y) ↦ (x-y,y)`. -/
@[expose]
noncomputable def abkPairDifferenceBoxSingularMajorant {d : Nat} (i : Fin d) (R : ℝ)
    (p : Vec d × Vec d) : ℝ :=
  abkCoordinateBoxSingularMajorant i (2 * R) (p.1 - p.2) *
    abkBoxIndicatorVec R p.2

/-- Pair-space bounded box majorant after the additive shear `(x,y) ↦ (x-y,y)`. -/
@[expose]
noncomputable def abkPairDifferenceBoxMajorant {d : Nat} (R : ℝ)
    (p : Vec d × Vec d) : ℝ :=
  abkBoxIndicatorVec (2 * R) (p.1 - p.2) *
    abkBoxIndicatorVec R p.2

/-- The coordinate-box indicator is one on the coordinate box. -/
theorem abkBoxIndicatorVec_eq_one_of_forall_abs_apply_le {d : Nat}
    {R : ℝ} {x : Vec d} (hx : ∀ j : Fin d, |x j| ≤ R) :
    abkBoxIndicatorVec R x = 1 := by
  unfold abkBoxIndicatorVec
  refine Finset.prod_eq_one ?_
  intro j _hj
  have hj : x j ∈ Set.Icc (-R) R := by
    exact (abs_le.mp (hx j))
  rw [Set.indicator_of_mem hj]

/-- The one-dimensional singular majorant equals `|x|^{-3/4}` inside the box. -/
theorem abkOneDimensionalSingularMajorant_eq_rpow_of_abs_le
    {R x : ℝ} (hx : |x| ≤ R) :
    abkOneDimensionalSingularMajorant R x =
      |x| ^ abkSingularMajorantExponent := by
  unfold abkOneDimensionalSingularMajorant
  have hxmem : x ∈ Set.Icc (-R) R := abs_le.mp hx
  rw [Set.indicator_of_mem hxmem]

/-- The coordinate-box singular majorant reduces to the singular coordinate inside the box. -/
theorem abkCoordinateBoxSingularMajorant_eq_abs_apply_rpow_of_forall_abs_apply_le
    {d : Nat} (i : Fin d) {R : ℝ} {x : Vec d}
    (hx : ∀ j : Fin d, |x j| ≤ R) :
    abkCoordinateBoxSingularMajorant i R x =
      |x i| ^ abkSingularMajorantExponent := by
  unfold abkCoordinateBoxSingularMajorant
  rw [Fintype.prod_eq_single i]
  · rw [ite_eq_left rfl]
    exact abkOneDimensionalSingularMajorant_eq_rpow_of_abs_le (hx i)
  · intro j hji
    rw [ite_eq_right hji]
    have hj : x j ∈ Set.Icc (-R) R := abs_le.mp (hx j)
    rw [Set.indicator_of_mem hj]

/-- The one-dimensional singular majorant is nonnegative. -/
theorem abkOneDimensionalSingularMajorant_nonneg (R x : ℝ) :
    0 ≤ abkOneDimensionalSingularMajorant R x := by
  unfold abkOneDimensionalSingularMajorant
  by_cases hx : x ∈ Set.Icc (-R) R
  · rw [Set.indicator_of_mem hx]
    exact Real.rpow_nonneg (abs_nonneg x) _
  · rw [Set.indicator_of_notMem hx]

/-- The coordinate-box indicator is nonnegative. -/
theorem abkBoxIndicatorVec_nonneg {d : Nat} (R : ℝ) (x : Vec d) :
    0 ≤ abkBoxIndicatorVec R x := by
  unfold abkBoxIndicatorVec
  refine Finset.prod_nonneg ?_
  intro j _hj
  by_cases hx : x j ∈ Set.Icc (-R) R
  · rw [Set.indicator_of_mem hx]
    norm_num
  · rw [Set.indicator_of_notMem hx]

/-- The coordinate-box singular majorant is nonnegative. -/
theorem abkCoordinateBoxSingularMajorant_nonneg {d : Nat} (i : Fin d)
    (R : ℝ) (x : Vec d) :
    0 ≤ abkCoordinateBoxSingularMajorant i R x := by
  unfold abkCoordinateBoxSingularMajorant
  refine Finset.prod_nonneg ?_
  intro j _hj
  by_cases hji : j = i
  · rw [ite_eq_left hji]
    exact abkOneDimensionalSingularMajorant_nonneg R (x j)
  · rw [ite_eq_right hji]
    by_cases hx : x j ∈ Set.Icc (-R) R
    · rw [Set.indicator_of_mem hx]
      norm_num
    · rw [Set.indicator_of_notMem hx]

/-- The pair-space bounded box majorant is nonnegative. -/
theorem abkPairDifferenceBoxMajorant_nonneg {d : Nat} (R : ℝ)
    (p : Vec d × Vec d) :
    0 ≤ abkPairDifferenceBoxMajorant (d := d) R p := by
  unfold abkPairDifferenceBoxMajorant
  exact mul_nonneg (abkBoxIndicatorVec_nonneg (2 * R) (p.1 - p.2))
    (abkBoxIndicatorVec_nonneg R p.2)

/-- The pair-space singular box majorant is nonnegative. -/
theorem abkPairDifferenceBoxSingularMajorant_nonneg {d : Nat} (i : Fin d)
    (R : ℝ) (p : Vec d × Vec d) :
    0 ≤ abkPairDifferenceBoxSingularMajorant i R p := by
  unfold abkPairDifferenceBoxSingularMajorant
  exact mul_nonneg
    (abkCoordinateBoxSingularMajorant_nonneg i (2 * R) (p.1 - p.2))
    (abkBoxIndicatorVec_nonneg R p.2)

/-- The pair-space bounded box majorant is one inside the corresponding pair box. -/
theorem abkPairDifferenceBoxMajorant_eq_one_of_forall_abs_apply_le
    {d : Nat} {R : ℝ} {p : Vec d × Vec d}
    (hdiff : ∀ j : Fin d, |(p.1 - p.2) j| ≤ 2 * R)
    (hy : ∀ j : Fin d, |p.2 j| ≤ R) :
    abkPairDifferenceBoxMajorant R p = 1 := by
  unfold abkPairDifferenceBoxMajorant
  rw [abkBoxIndicatorVec_eq_one_of_forall_abs_apply_le hdiff,
    abkBoxIndicatorVec_eq_one_of_forall_abs_apply_le hy, mul_one]

/-- The pair-space singular box majorant is the singular coordinate inside the pair box. -/
theorem abkPairDifferenceBoxSingularMajorant_eq_abs_apply_rpow_of_forall_abs_apply_le
    {d : Nat} (i : Fin d) {R : ℝ} {p : Vec d × Vec d}
    (hdiff : ∀ j : Fin d, |(p.1 - p.2) j| ≤ 2 * R)
    (hy : ∀ j : Fin d, |p.2 j| ≤ R) :
    abkPairDifferenceBoxSingularMajorant i R p =
      |(p.1 - p.2) i| ^ abkSingularMajorantExponent := by
  unfold abkPairDifferenceBoxSingularMajorant
  rw [abkCoordinateBoxSingularMajorant_eq_abs_apply_rpow_of_forall_abs_apply_le i hdiff,
    abkBoxIndicatorVec_eq_one_of_forall_abs_apply_le hy, mul_one]

/-- The one-dimensional singular majorant is integrable on every bounded symmetric interval. -/
theorem integrableOn_abs_rpow_abkSingularMajorantExponent_Icc (R : ℝ) (hR : 0 ≤ R) :
    IntegrableOn
      (fun x : ℝ => |x| ^ abkSingularMajorantExponent)
      (Set.Icc (-R) R) (volume : Measure ℝ) := by
  have hexp : (-1 : ℝ) < abkSingularMajorantExponent := by
    norm_num [abkSingularMajorantExponent]
  have hpos_interval :
      IntervalIntegrable
        (fun x : ℝ => x ^ abkSingularMajorantExponent)
        volume 0 R :=
    intervalIntegral.intervalIntegrable_rpow' hexp
  have hpos :
      IntegrableOn
        (fun x : ℝ => |x| ^ abkSingularMajorantExponent)
        (Set.Icc 0 R) (volume : Measure ℝ) := by
    have hpow :
        IntegrableOn
          (fun x : ℝ => x ^ abkSingularMajorantExponent)
          (Set.Icc 0 R) (volume : Measure ℝ) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hR).mp hpos_interval
    refine hpow.congr_fun ?_ measurableSet_Icc
    intro x hx
    simp [abs_of_nonneg hx.1]
  have hneg_interval :
      IntervalIntegrable
        (fun x : ℝ => (-x) ^ abkSingularMajorantExponent)
        volume (-R) 0 := by
    have hcomp :
        IntervalIntegrable
          (fun x : ℝ => (-x) ^ abkSingularMajorantExponent)
          volume 0 (-R) :=
      (show -0 = (0 : ℝ) by norm_num) ▸
        (IntervalIntegrable.iff_comp_neg
        (f := fun x : ℝ => x ^ abkSingularMajorantExponent)
        (a := 0) (b := R)).mp hpos_interval
    exact hcomp.symm
  have hneg :
      IntegrableOn
        (fun x : ℝ => |x| ^ abkSingularMajorantExponent)
        (Set.Icc (-R) 0) (volume : Measure ℝ) := by
    have hle : -R ≤ 0 := neg_nonpos.mpr hR
    have hpow :
        IntegrableOn
          (fun x : ℝ => (-x) ^ abkSingularMajorantExponent)
          (Set.Icc (-R) 0) (volume : Measure ℝ) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hle).mp hneg_interval
    refine hpow.congr_fun ?_ measurableSet_Icc
    intro x hx
    simp [abs_of_nonpos hx.2]
  have hcover : Set.Icc (-R) R = Set.Icc (-R) 0 ∪ Set.Icc 0 R := by
    ext x
    constructor
    · intro hx
      rcases le_total x 0 with hx0 | h0x
      · exact Or.inl ⟨hx.1, hx0⟩
      · exact Or.inr ⟨h0x, hx.2⟩
    · intro hx
      rcases hx with hx | hx
      · exact ⟨hx.1, hx.2.trans hR⟩
      · exact ⟨(neg_nonpos.mpr hR).trans hx.1, hx.2⟩
  rw [hcover]
  exact hneg.union hpos

/-- The one-dimensional singular majorant, extended by zero off the box, is integrable. -/
theorem integrable_abkOneDimensionalSingularMajorant (R : ℝ) (hR : 0 ≤ R) :
    Integrable (abkOneDimensionalSingularMajorant R) (volume : Measure ℝ) := by
  unfold abkOneDimensionalSingularMajorant
  exact (integrableOn_abs_rpow_abkSingularMajorantExponent_Icc R hR).integrable_indicator
    measurableSet_Icc

/-- The bounded one-dimensional box indicator is integrable. -/
theorem integrable_indicator_Icc_one (R : ℝ) (_hR : 0 ≤ R) :
    Integrable
      ((Set.Icc (-R) R).indicator (fun _ : ℝ => (1 : ℝ)))
      (volume : Measure ℝ) := by
  have hint : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc (-R) R)
      (volume : Measure ℝ) := by
    exact continuousOn_const.integrableOn_Icc
  exact hint.integrable_indicator measurableSet_Icc

/-- The coordinate-box singular majorant is integrable on `Vec d`. -/
theorem integrable_abkCoordinateBoxSingularMajorant {d : Nat} (i : Fin d)
    (R : ℝ) (hR : 0 ≤ R) :
    Integrable (abkCoordinateBoxSingularMajorant i R)
      (volume : Measure (Vec d)) := by
  let f : Fin d → ℝ → ℝ := fun j x =>
    if j = i then
      abkOneDimensionalSingularMajorant R x
    else
      (Set.Icc (-R) R).indicator (fun _ : ℝ => (1 : ℝ)) x
  have hf : ∀ j : Fin d, Integrable (f j) (volume : Measure ℝ) := fun j => by
    by_cases hji : j = i
    · subst hji
      simpa [f] using integrable_abkOneDimensionalSingularMajorant R hR
    · simpa [f, hji] using integrable_indicator_Icc_one R hR
  have hprod :
      Integrable (fun x : Fin d → ℝ => ∏ j : Fin d, f j (x j))
        (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) :=
    Integrable.fintype_prod hf
  rw [MeasureTheory.volume_pi]
  unfold abkCoordinateBoxSingularMajorant
  simpa only [f] using hprod

/-- The coordinate-box indicator is integrable on `Vec d`. -/
theorem integrable_abkBoxIndicatorVec {d : Nat} (R : ℝ) (hR : 0 ≤ R) :
    Integrable (abkBoxIndicatorVec (d := d) R) (volume : Measure (Vec d)) := by
  let f : Fin d → ℝ → ℝ := fun _ x =>
    (Set.Icc (-R) R).indicator (fun _ : ℝ => (1 : ℝ)) x
  have hf : ∀ j : Fin d, Integrable (f j) (volume : Measure ℝ) := fun _ =>
    integrable_indicator_Icc_one R hR
  have hprod :
      Integrable (fun x : Fin d → ℝ => ∏ j : Fin d, f j (x j))
        (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) :=
    Integrable.fintype_prod hf
  rw [MeasureTheory.volume_pi]
  unfold abkBoxIndicatorVec
  simpa only [f] using hprod

/-- The pair-space difference singular majorant is integrable. -/
theorem integrable_abkPairDifferenceBoxSingularMajorant {d : Nat} (i : Fin d)
    (R : ℝ) (hR : 0 ≤ R) :
    Integrable (abkPairDifferenceBoxSingularMajorant i R)
      ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) := by
  let μ : Measure (Vec d × Vec d) :=
    (volume : Measure (Vec d)).prod (volume : Measure (Vec d))
  let T : Vec d × Vec d → Vec d × Vec d := fun p => (p.1 - p.2, p.2)
  have h2R : 0 ≤ 2 * R := mul_nonneg (by norm_num) hR
  have hprod :
      Integrable
        (fun q : Vec d × Vec d =>
          abkCoordinateBoxSingularMajorant i (2 * R) q.1 *
            abkBoxIndicatorVec R q.2)
        μ := by
    simpa [μ] using
      (integrable_abkCoordinateBoxSingularMajorant i (2 * R) h2R).mul_prod
        (integrable_abkBoxIndicatorVec (d := d) R hR)
  have hT : MeasurePreserving T μ μ := by
    simpa [T, μ] using
      (measurePreserving_sub_prod
        (volume : Measure (Vec d)) (volume : Measure (Vec d)))
  unfold abkPairDifferenceBoxSingularMajorant
  change Integrable
    (fun p : Vec d × Vec d =>
      abkCoordinateBoxSingularMajorant i (2 * R) (p.1 - p.2) *
        abkBoxIndicatorVec R p.2) μ
  exact hT.integrable_comp_of_integrable hprod

/-- The pair-space bounded box majorant is integrable. -/
theorem integrable_abkPairDifferenceBoxMajorant {d : Nat}
    (R : ℝ) (hR : 0 ≤ R) :
    Integrable (abkPairDifferenceBoxMajorant (d := d) R)
      ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) := by
  let μ : Measure (Vec d × Vec d) :=
    (volume : Measure (Vec d)).prod (volume : Measure (Vec d))
  let T : Vec d × Vec d → Vec d × Vec d := fun p => (p.1 - p.2, p.2)
  have h2R : 0 ≤ 2 * R := mul_nonneg (by norm_num) hR
  have hprod :
      Integrable
        (fun q : Vec d × Vec d =>
          abkBoxIndicatorVec (d := d) (2 * R) q.1 *
            abkBoxIndicatorVec R q.2)
        μ := by
    simpa [μ] using
      (integrable_abkBoxIndicatorVec (d := d) (2 * R) h2R).mul_prod
        (integrable_abkBoxIndicatorVec (d := d) R hR)
  have hT : MeasurePreserving T μ μ := by
    simpa [T, μ] using
      (measurePreserving_sub_prod
        (volume : Measure (Vec d)) (volume : Measure (Vec d)))
  unfold abkPairDifferenceBoxMajorant
  change Integrable
    (fun p : Vec d × Vec d =>
      abkBoxIndicatorVec (2 * R) (p.1 - p.2) * abkBoxIndicatorVec R p.2) μ
  exact hT.integrable_comp_of_integrable hprod

/-- After the additive shear, any fixed coordinate of the difference is nonzero a.e. -/
theorem ae_sub_apply_ne_zero_volume_prod {d : Nat} (i : Fin d) :
    ∀ᵐ p : Vec d × Vec d
      ∂((volume : Measure (Vec d)).prod (volume : Measure (Vec d))),
      (p.1 - p.2) i ≠ 0 := by
  let μ : Measure (Vec d × Vec d) :=
    (volume : Measure (Vec d)).prod (volume : Measure (Vec d))
  let T : Vec d × Vec d → Vec d × Vec d := fun p => (p.1 - p.2, p.2)
  have hcoord : ∀ᵐ v : Vec d ∂(volume : Measure (Vec d)), v i ≠ 0 := by
    simpa [MeasureTheory.volume_pi] using
      (Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) i (0 : ℝ))
  have hprod : ∀ᵐ q : Vec d × Vec d ∂μ, q.1 i ≠ 0 := by
    have hmeas : MeasurableSet {q : Vec d × Vec d | q.1 i ≠ 0} := by
      exact (isClosed_eq ((continuous_apply i).comp continuous_fst) continuous_const).measurableSet.compl
    rw [Measure.ae_prod_iff_ae_ae hmeas]
    filter_upwards [hcoord] with v hv
    exact Filter.Eventually.of_forall fun _ => hv
  have hT : MeasurePreserving T μ μ := by
    simpa [T, μ] using
      (measurePreserving_sub_prod
        (volume : Measure (Vec d)) (volume : Measure (Vec d)))
  simpa [T, μ] using hT.quasiMeasurePreserving.ae hprod

/-- The centered Riesz slope integrand is a.e. strongly measurable for nonzero `α`. -/
theorem aestronglyMeasurable_abkCenteredRieszSlopeKernel_integrand_of_ne
    {d : Nat} (hd : 0 < d) (ψ φ : MeanZeroTestFunction d) {α : ℝ}
    (hα : α ≠ 0) :
    AEStronglyMeasurable
      (fun p : Vec d × Vec d =>
        ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2)
      ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) := by
  let μ : Measure (Vec d × Vec d) :=
    (volume : Measure (Vec d)).prod (volume : Measure (Vec d))
  let s : Set (Vec d × Vec d) := {p | p.1 ≠ p.2}
  have hs : MeasurableSet s := by
    exact (isClosed_eq continuous_fst continuous_snd).measurableSet.compl
  have hfull : ∀ᵐ p : Vec d × Vec d ∂μ, p ∈ s := by
    simpa [s, μ] using ae_fst_ne_snd_volume_prod hd
  have hnorm :
      ContinuousOn (fun p : Vec d × Vec d => euclideanNorm (p.1 - p.2)) s := by
    exact ((continuous_euclideanNorm (d := d)).comp
      (continuous_fst.sub continuous_snd)).continuousOn
  have hpow :
      ContinuousOn
        (fun p : Vec d × Vec d => (euclideanNorm (p.1 - p.2)) ^ (-α)) s := by
    refine hnorm.rpow_const ?_
    intro p hp
    left
    have hdiff : p.1 - p.2 ≠ 0 := by
      intro hzero
      exact hp (sub_eq_zero.mp hzero)
    exact ne_of_gt (abkEuclideanNorm_pos_of_ne_zero hdiff)
  have hslope :
      ContinuousOn
        (fun p : Vec d × Vec d =>
          abkCenteredRieszSlopeKernel α p.1 p.2) s := by
    unfold abkCenteredRieszSlopeKernel
    exact (hpow.sub continuousOn_const).div continuousOn_const
      (fun _ _ => hα)
  have hcont :
      ContinuousOn
        (fun p : Vec d × Vec d =>
          ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2) s := by
    exact (((ψ.continuous.comp continuous_fst).continuousOn).mul
      ((φ.continuous.comp continuous_snd).continuousOn)).mul hslope
  have hsm := hcont.aestronglyMeasurable (μ := μ) hs
  rw [Measure.restrict_eq_self_of_ae_mem hfull] at hsm
  simpa [μ] using hsm

/-- Near `α = 0+`, the centered Riesz slope integrands are a.e. strongly measurable. -/
theorem eventually_aestronglyMeasurable_abkCenteredRieszSlopeKernel_integrand
    {d : Nat} (hd : 0 < d) (ψ φ : MeanZeroTestFunction d) :
    ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable
        (fun p : Vec d × Vec d =>
          ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2)
        ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) := by
  filter_upwards [self_mem_nhdsWithin] with α hα
  exact aestronglyMeasurable_abkCenteredRieszSlopeKernel_integrand_of_ne
    hd ψ φ hα.ne'

/-- Pointwise domination of the centered Riesz slope integrand by the concrete pair-box
majorant, assuming explicit support and uniform bounds for the two test functions. -/
theorem norm_abkCenteredRieszSlopeKernel_integrand_le_pair_majorant
    {d : Nat} (i : Fin d) (ψ φ : MeanZeroTestFunction d)
    {R Mψ Mφ α : ℝ}
    (hR : 1 ≤ R)
    (hMψ_nonneg : 0 ≤ Mψ) (hMφ_nonneg : 0 ≤ Mφ)
    (hψ_bound : ∀ x : Vec d, |ψ x| ≤ Mψ)
    (hφ_bound : ∀ x : Vec d, |φ x| ≤ Mφ)
    (hψ_support : Function.support ψ ⊆ {x : Vec d | euclideanNorm x ≤ R})
    (hφ_support : Function.support φ ⊆ {x : Vec d | euclideanNorm x ≤ R})
    (hα_pos : 0 < α) (hα_le : α ≤ 1 / 2)
    {p : Vec d × Vec d} (hp_coord : (p.1 - p.2) i ≠ 0) :
    ‖ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2‖ ≤
      (Mψ * Mφ * (4 + Real.log (2 * R))) *
        (abkPairDifferenceBoxMajorant R p +
          abkPairDifferenceBoxSingularMajorant i R p) := by
  let C : ℝ := Mψ * Mφ * (4 + Real.log (2 * R))
  have h2R : 1 ≤ 2 * R := by nlinarith
  have hcoef_nonneg : 0 ≤ 4 + Real.log (2 * R) := by
    have hlog : 0 ≤ Real.log (2 * R) := Real.log_nonneg h2R
    linarith
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg hMψ_nonneg hMφ_nonneg) hcoef_nonneg
  have hsum_nonneg :
      0 ≤ abkPairDifferenceBoxMajorant R p +
        abkPairDifferenceBoxSingularMajorant i R p :=
    add_nonneg (abkPairDifferenceBoxMajorant_nonneg R p)
      (abkPairDifferenceBoxSingularMajorant_nonneg i R p)
  by_cases hψ_zero : ψ p.1 = 0
  · calc
      ‖ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2‖ = 0 := by
        simp [hψ_zero]
      _ ≤ C *
          (abkPairDifferenceBoxMajorant R p +
            abkPairDifferenceBoxSingularMajorant i R p) :=
        mul_nonneg hC_nonneg hsum_nonneg
  by_cases hφ_zero : φ p.2 = 0
  · calc
      ‖ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2‖ = 0 := by
        simp [hφ_zero]
      _ ≤ C *
          (abkPairDifferenceBoxMajorant R p +
            abkPairDifferenceBoxSingularMajorant i R p) :=
        mul_nonneg hC_nonneg hsum_nonneg
  have hx_norm : euclideanNorm p.1 ≤ R := hψ_support hψ_zero
  have hy_norm : euclideanNorm p.2 ≤ R := hφ_support hφ_zero
  have hy_box : ∀ j : Fin d, |p.2 j| ≤ R := by
    intro j
    exact (abs_apply_le_euclideanNorm p.2 j).trans hy_norm
  have hρ_le : euclideanNorm (p.1 - p.2) ≤ 2 * R := by
    have hsub : p.1 - p.2 = p.1 + (-p.2) := by
      ext j
      simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
      ring_nf
    calc
      euclideanNorm (p.1 - p.2) = euclideanNorm (p.1 + (-p.2)) := by rw [hsub]
      _ ≤ euclideanNorm p.1 + euclideanNorm (-p.2) := euclideanNorm_add_le p.1 (-p.2)
      _ = euclideanNorm p.1 + euclideanNorm p.2 := by rw [euclideanNorm_neg]
      _ ≤ R + R := add_le_add hx_norm hy_norm
      _ = 2 * R := by ring_nf
  have hdiff_box : ∀ j : Fin d, |(p.1 - p.2) j| ≤ 2 * R := by
    intro j
    exact (abs_apply_le_euclideanNorm (p.1 - p.2) j).trans hρ_le
  have hbox :
      abkPairDifferenceBoxMajorant R p = 1 :=
    abkPairDifferenceBoxMajorant_eq_one_of_forall_abs_apply_le hdiff_box hy_box
  have hsing :
      abkPairDifferenceBoxSingularMajorant i R p =
        |(p.1 - p.2) i| ^ abkSingularMajorantExponent :=
    abkPairDifferenceBoxSingularMajorant_eq_abs_apply_rpow_of_forall_abs_apply_le
      i hdiff_box hy_box
  have hdiff_ne : p.1 - p.2 ≠ 0 := by
    intro hzero
    exact hp_coord (by rw [hzero]; rfl)
  have hρ_pos : 0 < euclideanNorm (p.1 - p.2) :=
    abkEuclideanNorm_pos_of_ne_zero hdiff_ne
  have hslope_abs :
      |((euclideanNorm (p.1 - p.2)) ^ (-α) - 1) / α| ≤
        (4 + Real.log (2 * R)) *
          (1 + (euclideanNorm (p.1 - p.2)) ^ abkSingularMajorantExponent) :=
    abs_rpow_neg_sub_one_div_le_abkSingularMajorant
      (α := α) (ρ := euclideanNorm (p.1 - p.2)) (R := 2 * R)
      hα_pos hα_le hρ_pos hρ_le h2R
  have hcoord_pos : 0 < |(p.1 - p.2) i| := abs_pos.mpr hp_coord
  have hcoord_le : |(p.1 - p.2) i| ≤ euclideanNorm (p.1 - p.2) :=
    abs_apply_le_euclideanNorm (p.1 - p.2) i
  have hexp_nonpos : abkSingularMajorantExponent ≤ 0 := by
    norm_num [abkSingularMajorantExponent]
  have hρ_sing_le :
      (euclideanNorm (p.1 - p.2)) ^ abkSingularMajorantExponent ≤
        |(p.1 - p.2) i| ^ abkSingularMajorantExponent :=
    Real.rpow_le_rpow_of_nonpos hcoord_pos hcoord_le hexp_nonpos
  have hψ_norm : ‖ψ p.1‖ ≤ Mψ := by
    simpa [Real.norm_eq_abs] using hψ_bound p.1
  have hφ_norm : ‖φ p.2‖ ≤ Mφ := by
    simpa [Real.norm_eq_abs] using hφ_bound p.2
  have hslope_norm :
      ‖abkCenteredRieszSlopeKernel α p.1 p.2‖ ≤
        (4 + Real.log (2 * R)) *
          (1 + (euclideanNorm (p.1 - p.2)) ^ abkSingularMajorantExponent) := by
    rw [abkCenteredRieszSlopeKernel, Real.norm_eq_abs]
    exact hslope_abs
  have hψφ_norm : ‖ψ p.1‖ * ‖φ p.2‖ ≤ Mψ * Mφ := by
    exact mul_le_mul hψ_norm hφ_norm (norm_nonneg _) hMψ_nonneg
  have htarget_nonneg :
      0 ≤ (4 + Real.log (2 * R)) *
          (1 + (euclideanNorm (p.1 - p.2)) ^ abkSingularMajorantExponent) := by
    exact mul_nonneg hcoef_nonneg
      (add_nonneg zero_le_one (Real.rpow_nonneg (euclideanNorm_nonneg _) _))
  calc
    ‖ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2‖
        ≤ ‖ψ p.1‖ * ‖φ p.2‖ *
            ‖abkCenteredRieszSlopeKernel α p.1 p.2‖ := norm_mul₃_le
    _ ≤ (Mψ * Mφ) *
          ((4 + Real.log (2 * R)) *
            (1 + (euclideanNorm (p.1 - p.2)) ^ abkSingularMajorantExponent)) := by
          exact mul_le_mul hψφ_norm hslope_norm (norm_nonneg _)
            (mul_nonneg hMψ_nonneg hMφ_nonneg)
    _ = C * (1 + (euclideanNorm (p.1 - p.2)) ^ abkSingularMajorantExponent) := by
          dsimp [C]
          ring_nf
    _ ≤ C * (1 + |(p.1 - p.2) i| ^ abkSingularMajorantExponent) := by
          exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hρ_sing_le) hC_nonneg
    _ = C *
          (abkPairDifferenceBoxMajorant R p +
            abkPairDifferenceBoxSingularMajorant i R p) := by
          rw [hbox, hsing]

/-- Concrete integrable dominated-convergence majorant for the centered Riesz slope
integrands associated to two ABK test functions. -/
theorem exists_integrable_bound_abkCenteredRieszSlopeKernel_integrand
    {d : Nat} (hd : 0 < d) (ψ φ : MeanZeroTestFunction d) :
    ∃ bound : Vec d × Vec d → ℝ,
      Integrable bound
        ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) ∧
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        ∀ᵐ p : Vec d × Vec d
          ∂((volume : Measure (Vec d)).prod (volume : Measure (Vec d))),
          ‖ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2‖ ≤ bound p := by
  let i : Fin d := ⟨0, hd⟩
  rcases exists_support_subset_euclideanClosedBall_meanZeroTestFunction ψ with
    ⟨Rψ, _hRψ_nonneg, hψ_support₀⟩
  rcases exists_support_subset_euclideanClosedBall_meanZeroTestFunction φ with
    ⟨Rφ, _hRφ_nonneg, hφ_support₀⟩
  rcases exists_abs_meanZeroTestFunction_le ψ with
    ⟨Mψ, hMψ_nonneg, hψ_bound⟩
  rcases exists_abs_meanZeroTestFunction_le φ with
    ⟨Mφ, hMφ_nonneg, hφ_bound⟩
  let R : ℝ := max 1 (max Rψ Rφ)
  have hR : 1 ≤ R := le_max_left _ _
  have hR_nonneg : 0 ≤ R := zero_le_one.trans hR
  have hRψ_le : Rψ ≤ R := by
    exact (le_max_left Rψ Rφ).trans (le_max_right 1 (max Rψ Rφ))
  have hRφ_le : Rφ ≤ R := by
    exact (le_max_right Rψ Rφ).trans (le_max_right 1 (max Rψ Rφ))
  have hψ_support : Function.support ψ ⊆ {x : Vec d | euclideanNorm x ≤ R} := by
    intro x hx
    exact (hψ_support₀ hx).trans hRψ_le
  have hφ_support : Function.support φ ⊆ {x : Vec d | euclideanNorm x ≤ R} := by
    intro x hx
    exact (hφ_support₀ hx).trans hRφ_le
  let C : ℝ := Mψ * Mφ * (4 + Real.log (2 * R))
  let bound : Vec d × Vec d → ℝ := fun p =>
    C * (abkPairDifferenceBoxMajorant R p +
      abkPairDifferenceBoxSingularMajorant i R p)
  refine ⟨bound, ?_, ?_⟩
  · have hsum :
        Integrable
          (fun p : Vec d × Vec d =>
            abkPairDifferenceBoxMajorant R p +
              abkPairDifferenceBoxSingularMajorant i R p)
          ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) :=
      (integrable_abkPairDifferenceBoxMajorant (d := d) R hR_nonneg).add
        (integrable_abkPairDifferenceBoxSingularMajorant i R hR_nonneg)
    simpa [bound, C] using hsum.const_mul C
  · filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with α hα
    filter_upwards [ae_sub_apply_ne_zero_volume_prod i] with p hp_coord
    simpa [bound, C] using
      norm_abkCenteredRieszSlopeKernel_integrand_le_pair_majorant
        i ψ φ hR hMψ_nonneg hMφ_nonneg hψ_bound hφ_bound
        hψ_support hφ_support hα.1 hα.2 hp_coord

/-- For each fixed small positive `α`, the centered Riesz slope integrand is integrable. -/
theorem integrable_abkCenteredRieszSlopeKernel_integrand_of_pos_le_half
    {d : Nat} (hd : 0 < d) (ψ φ : MeanZeroTestFunction d) {α : ℝ}
    (hα_pos : 0 < α) (hα_le : α ≤ 1 / 2) :
    Integrable
      (fun p : Vec d × Vec d =>
        ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2)
      ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) := by
  let i : Fin d := ⟨0, hd⟩
  rcases exists_support_subset_euclideanClosedBall_meanZeroTestFunction ψ with
    ⟨Rψ, _hRψ_nonneg, hψ_support₀⟩
  rcases exists_support_subset_euclideanClosedBall_meanZeroTestFunction φ with
    ⟨Rφ, _hRφ_nonneg, hφ_support₀⟩
  rcases exists_abs_meanZeroTestFunction_le ψ with
    ⟨Mψ, hMψ_nonneg, hψ_bound⟩
  rcases exists_abs_meanZeroTestFunction_le φ with
    ⟨Mφ, hMφ_nonneg, hφ_bound⟩
  let R : ℝ := max 1 (max Rψ Rφ)
  have hR : 1 ≤ R := le_max_left _ _
  have hR_nonneg : 0 ≤ R := zero_le_one.trans hR
  have hRψ_le : Rψ ≤ R := by
    exact (le_max_left Rψ Rφ).trans (le_max_right 1 (max Rψ Rφ))
  have hRφ_le : Rφ ≤ R := by
    exact (le_max_right Rψ Rφ).trans (le_max_right 1 (max Rψ Rφ))
  have hψ_support : Function.support ψ ⊆ {x : Vec d | euclideanNorm x ≤ R} := by
    intro x hx
    exact (hψ_support₀ hx).trans hRψ_le
  have hφ_support : Function.support φ ⊆ {x : Vec d | euclideanNorm x ≤ R} := by
    intro x hx
    exact (hφ_support₀ hx).trans hRφ_le
  let C : ℝ := Mψ * Mφ * (4 + Real.log (2 * R))
  let bound : Vec d × Vec d → ℝ := fun p =>
    C * (abkPairDifferenceBoxMajorant R p +
      abkPairDifferenceBoxSingularMajorant i R p)
  have hbound_int :
      Integrable bound
        ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) := by
    have hsum :
        Integrable
          (fun p : Vec d × Vec d =>
            abkPairDifferenceBoxMajorant R p +
              abkPairDifferenceBoxSingularMajorant i R p)
          ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) :=
      (integrable_abkPairDifferenceBoxMajorant (d := d) R hR_nonneg).add
        (integrable_abkPairDifferenceBoxSingularMajorant i R hR_nonneg)
    simpa [bound, C] using hsum.const_mul C
  have hmeas :
      AEStronglyMeasurable
        (fun p : Vec d × Vec d =>
          ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2)
        ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) :=
    aestronglyMeasurable_abkCenteredRieszSlopeKernel_integrand_of_ne
      hd ψ φ hα_pos.ne'
  refine hbound_int.mono' hmeas ?_
  filter_upwards [ae_sub_apply_ne_zero_volume_prod i] with p hp_coord
  simpa [bound, C] using
    norm_abkCenteredRieszSlopeKernel_integrand_le_pair_majorant
      i ψ φ hR hMψ_nonneg hMφ_nonneg hψ_bound hφ_bound
      hψ_support hφ_support hα_pos hα_le hp_coord

/-- For each fixed small positive `α`, the Riesz kernel integrand is integrable. -/
theorem integrable_abkRieszKernel_integrand_of_pos_le_half
    {d : Nat} (hd : 0 < d) (ψ φ : MeanZeroTestFunction d) {α : ℝ}
    (hα_pos : 0 < α) (hα_le : α ≤ 1 / 2) :
    Integrable
      (fun p : Vec d × Vec d => ψ p.1 * φ p.2 * abkRieszKernel α p.1 p.2)
      ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) := by
  let μ : Measure (Vec d × Vec d) :=
    (volume : Measure (Vec d)).prod (volume : Measure (Vec d))
  have hslope :
      Integrable
        (fun p : Vec d × Vec d =>
          ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2) μ :=
    integrable_abkCenteredRieszSlopeKernel_integrand_of_pos_le_half
      hd ψ φ hα_pos hα_le
  have hconst :
      Integrable (fun p : Vec d × Vec d => ψ p.1 * φ p.2 * (1 : ℝ)) μ :=
    integrable_abkKernelPairing_const_one ψ φ
  have hsum :
      Integrable
        (fun p : Vec d × Vec d =>
          α * (ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2) +
            ψ p.1 * φ p.2 * (1 : ℝ)) μ :=
    (hslope.const_mul α).add hconst
  refine hsum.congr ?_
  filter_upwards with p
  have hα_ne : α ≠ 0 := hα_pos.ne'
  simp [abkCenteredRieszSlopeKernel, abkRieszKernel]
  field_simp [hα_ne]
  ring_nf

/-- Dominated convergence for the concrete ABK centered Riesz slope pairings. -/
theorem tendsto_abkCenteredRieszSlopePairing
    {d : Nat} (hd : 0 < d) (ψ φ : MeanZeroTestFunction d) :
    Tendsto (fun α : ℝ => abkCenteredRieszSlopePairing ψ φ α)
      (𝓝[>] (0 : ℝ)) (𝓝 (abkLogCovariancePairing ψ φ)) := by
  rcases exists_integrable_bound_abkCenteredRieszSlopeKernel_integrand hd ψ φ with
    ⟨bound, hbound_int, hbound⟩
  exact tendsto_abkCenteredRieszSlopePairing_of_dominated
    hd ψ φ bound
    (eventually_aestronglyMeasurable_abkCenteredRieszSlopeKernel_integrand hd ψ φ)
    hbound hbound_int

/-- The ABK reciprocal normalization times the centered Riesz difference pairing converges to
the logarithmic covariance pairing with the `M₀` prefactor. -/
theorem tendsto_abkMAlphaInv_mul_centeredRieszDifferencePairing
    {d : Nat} (hd : 0 < d) (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) :
    Tendsto
      (fun α : ℝ =>
        abkMAlphaInv ζ α * abkCenteredRieszDifferencePairing ψ φ α)
      (𝓝[>] (0 : ℝ))
      (𝓝 (abkM0 ζ * abkLogCovariancePairing ψ φ)) := by
  rcases exists_integrable_bound_abkCenteredRieszSlopeKernel_integrand hd ψ φ with
    ⟨bound, hbound_int, hbound⟩
  exact tendsto_abkMAlphaInv_mul_centeredRieszDifferencePairing_of_dominated
    hd ζ ψ φ bound
    (eventually_aestronglyMeasurable_abkCenteredRieszSlopeKernel_integrand hd ψ φ)
    hbound hbound_int

end GaussianFields

end
