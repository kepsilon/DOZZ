/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # The explicit profile `A₀ (φ(u) + ρ u^κ ψ(u))` near `0⁺`

For `φ, ψ` of class `C²` on `(-1, 1)` and `1 < κ < 2`, the profile has explicit first and second
derivatives on `(0, 1)`; the profile and its first derivative have limits at `0⁺`, the second
derivative is integrable near `0`, and the Taylor remainder `φ(t) - φ(0) - φ'(0) t` is
`o(t^κ)`. -/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- First and second derivatives of a `C²` function on `(-1, 1)` at interior points. -/
theorem bpzEP_hasDerivAt {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 2 φ (Ioo (-1) 1)) {u : ℝ}
    (hu : u ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt φ (deriv φ u) u ∧ HasDerivAt (deriv φ) (deriv (deriv φ) u) u := by
  have hmem : Ioo (-1 : ℝ) 1 ∈ 𝓝 u := isOpen_Ioo.mem_nhds hu
  have h1 : DifferentiableAt ℝ φ u :=
    (hφ.differentiableOn (by norm_num)).differentiableAt hmem
  have hd : ContDiffOn ℝ 1 (deriv φ) (Ioo (-1) 1) :=
    hφ.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have h2 : DifferentiableAt ℝ (deriv φ) u :=
    (hd.differentiableOn (by norm_num)).differentiableAt hmem
  exact ⟨h1.hasDerivAt, h2.hasDerivAt⟩

/-- Continuity of `φ`, `φ'` and `φ''` on `(-1, 1)`. -/
theorem bpzEP_continuousOn {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 2 φ (Ioo (-1) 1)) :
    ContinuousOn φ (Ioo (-1) 1) ∧ ContinuousOn (deriv φ) (Ioo (-1) 1) ∧
      ContinuousOn (deriv (deriv φ)) (Ioo (-1) 1) := by
  have hd : ContDiffOn ℝ 1 (deriv φ) (Ioo (-1) 1) :=
    hφ.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hdd : ContDiffOn ℝ 0 (deriv (deriv φ)) (Ioo (-1) 1) :=
    hd.deriv_of_isOpen isOpen_Ioo (by norm_num)
  exact ⟨hφ.continuousOn, hd.continuousOn, hdd.continuousOn⟩

/-- The first derivative of the profile. -/
theorem bpzEP_hasDerivAt_profile {φ ψ : ℝ → ℝ} (hφ : ContDiffOn ℝ 2 φ (Ioo (-1) 1))
    (hψ : ContDiffOn ℝ 2 ψ (Ioo (-1) 1)) (A₀ ρ κ : ℝ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (fun v => A₀ * (φ v + ρ * (v ^ κ * ψ v)))
      (A₀ * (deriv φ u + ρ * (κ * u ^ (κ - 1) * ψ u + u ^ κ * deriv ψ u))) u := by
  have hu : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hu1⟩
  have h1 := (bpzEP_hasDerivAt hφ hu).1
  have h2 := (bpzEP_hasDerivAt hψ hu).1
  have hp : HasDerivAt (fun v : ℝ => v ^ κ) (κ * u ^ (κ - 1)) u :=
    Real.hasDerivAt_rpow_const (Or.inl hu0.ne')
  exact ((h1.add ((hp.mul h2).const_mul ρ)).const_mul A₀)

/-- The second derivative of the profile. -/
theorem bpzEP_hasDerivAt_profile' {φ ψ : ℝ → ℝ} (hφ : ContDiffOn ℝ 2 φ (Ioo (-1) 1))
    (hψ : ContDiffOn ℝ 2 ψ (Ioo (-1) 1)) (A₀ ρ κ : ℝ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (fun v => A₀ * (deriv φ v + ρ * (κ * v ^ (κ - 1) * ψ v + v ^ κ * deriv ψ v)))
      (A₀ * (deriv (deriv φ) u + ρ * (κ * (κ - 1) * u ^ (κ - 2) * ψ u +
        2 * (κ * u ^ (κ - 1) * deriv ψ u) + u ^ κ * deriv (deriv ψ) u))) u := by
  have hu : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hu1⟩
  obtain ⟨hψ1, hψ2⟩ := bpzEP_hasDerivAt hψ hu
  have hφ2 := (bpzEP_hasDerivAt hφ hu).2
  have hp : HasDerivAt (fun v : ℝ => v ^ κ) (κ * u ^ (κ - 1)) u :=
    Real.hasDerivAt_rpow_const (Or.inl hu0.ne')
  have hp1 : HasDerivAt (fun v : ℝ => v ^ (κ - 1)) ((κ - 1) * u ^ (κ - 1 - 1)) u :=
    Real.hasDerivAt_rpow_const (Or.inl hu0.ne')
  have h := (hφ2.add ((((hp1.const_mul κ).mul hψ1).add (hp.mul hψ2)).const_mul ρ)).const_mul A₀
  refine h.congr_deriv ?_
  rw [show κ - 1 - 1 = κ - 2 by ring]
  ring

/-- The profile tends to `A₀ φ(0)` at `0⁺` (for `κ > 0`). -/
theorem bpzEP_tendsto_profile {φ ψ : ℝ → ℝ} (hφ : ContDiffOn ℝ 2 φ (Ioo (-1) 1))
    (hψ : ContDiffOn ℝ 2 ψ (Ioo (-1) 1)) (A₀ ρ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun v => A₀ * (φ v + ρ * (v ^ κ * ψ v))) (𝓝[>] 0) (𝓝 (A₀ * φ 0)) := by
  have hmem : Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hφc : Tendsto φ (𝓝[>] 0) (𝓝 (φ 0)) :=
    ((bpzEP_continuousOn hφ).1.continuousAt hmem).tendsto.mono_left nhdsWithin_le_nhds
  have hψc : Tendsto ψ (𝓝[>] 0) (𝓝 (ψ 0)) :=
    ((bpzEP_continuousOn hψ).1.continuousAt hmem).tendsto.mono_left nhdsWithin_le_nhds
  have hpow : Tendsto (fun v : ℝ => v ^ κ) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).rpow_const_nhds_zero hκ
  have h := ((hφc.add ((hpow.mul hψc).const_mul ρ)).const_mul A₀)
  simpa using h

/-- The first derivative of the profile tends to `A₀ φ'(0)` at `0⁺` (for `κ > 1`). -/
theorem bpzEP_tendsto_profile' {φ ψ : ℝ → ℝ} (hφ : ContDiffOn ℝ 2 φ (Ioo (-1) 1))
    (hψ : ContDiffOn ℝ 2 ψ (Ioo (-1) 1)) (A₀ ρ : ℝ) {κ : ℝ} (hκ : 1 < κ) :
    Tendsto (fun v => A₀ * (deriv φ v + ρ * (κ * v ^ (κ - 1) * ψ v + v ^ κ * deriv ψ v)))
      (𝓝[>] 0) (𝓝 (A₀ * deriv φ 0)) := by
  have hmem : Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hφc : Tendsto (deriv φ) (𝓝[>] 0) (𝓝 (deriv φ 0)) :=
    ((bpzEP_continuousOn hφ).2.1.continuousAt hmem).tendsto.mono_left nhdsWithin_le_nhds
  have hψc : Tendsto ψ (𝓝[>] 0) (𝓝 (ψ 0)) :=
    ((bpzEP_continuousOn hψ).1.continuousAt hmem).tendsto.mono_left nhdsWithin_le_nhds
  have hψ'c : Tendsto (deriv ψ) (𝓝[>] 0) (𝓝 (deriv ψ 0)) :=
    ((bpzEP_continuousOn hψ).2.1.continuousAt hmem).tendsto.mono_left nhdsWithin_le_nhds
  have hid : Tendsto (fun v : ℝ => v) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left
    nhdsWithin_le_nhds
  have hpow : Tendsto (fun v : ℝ => v ^ κ) (𝓝[>] 0) (𝓝 0) :=
    hid.rpow_const_nhds_zero (by linarith)
  have hpow1 : Tendsto (fun v : ℝ => v ^ (κ - 1)) (𝓝[>] 0) (𝓝 0) :=
    hid.rpow_const_nhds_zero (by linarith)
  have h := ((hφc.add ((((hpow1.const_mul κ).mul hψc).add (hpow.mul hψ'c)).const_mul ρ)).const_mul
    A₀)
  simpa using h

/-- The second derivative of the profile is integrable on `(0, t]` (for `κ > 1`, `t < 1`). -/
theorem bpzEP_integrableOn_profile'' {φ ψ : ℝ → ℝ} (hφ : ContDiffOn ℝ 2 φ (Ioo (-1) 1))
    (hψ : ContDiffOn ℝ 2 ψ (Ioo (-1) 1)) (A₀ ρ : ℝ) {κ : ℝ} (hκ : 1 < κ) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) :
    IntegrableOn (fun u => A₀ * (deriv (deriv φ) u + ρ * (κ * (κ - 1) * u ^ (κ - 2) * ψ u +
        2 * (κ * u ^ (κ - 1) * deriv ψ u) + u ^ κ * deriv (deriv ψ) u))) (Ioc 0 t) := by
  have hK : Icc (0 : ℝ) t ⊆ Ioo (-1) 1 := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨hψc, hψ'c, hψ''c⟩ := bpzEP_continuousOn hψ
  have hφ''c := (bpzEP_continuousOn hφ).2.2
  have hcomp : IsCompact (Icc (0 : ℝ) t) := isCompact_Icc
  have hsub : Ioc (0 : ℝ) t ⊆ Icc 0 t := Ioc_subset_Icc_self
  -- bounded continuous pieces
  have hc1 : IntegrableOn (deriv (deriv φ)) (Ioc 0 t) :=
    ((hφ''c.mono hK).integrableOn_compact hcomp).mono_set hsub
  have hpowc1 : ContinuousOn (fun u : ℝ => u ^ (κ - 1)) (Icc 0 t) := fun x _ =>
    (Real.continuousAt_rpow_const x (κ - 1) (Or.inr (by linarith))).continuousWithinAt
  have hpowc : ContinuousOn (fun u : ℝ => u ^ κ) (Icc 0 t) := fun x _ =>
    (Real.continuousAt_rpow_const x κ (Or.inr (by linarith))).continuousWithinAt
  have hc2 : IntegrableOn (fun u => 2 * (κ * u ^ (κ - 1) * deriv ψ u)) (Ioc 0 t) :=
    ((((hpowc1.const_smul κ).mul (hψ'c.mono hK)).const_smul (2 : ℝ)).integrableOn_compact
      hcomp).mono_set hsub
  have hc3 : IntegrableOn (fun u => u ^ κ * deriv (deriv ψ) u) (Ioc 0 t) :=
    ((hpowc.mul (hψ''c.mono hK)).integrableOn_compact hcomp).mono_set hsub
  -- the singular piece
  have hsing : IntegrableOn (fun u : ℝ => u ^ (κ - 2)) (Ioc 0 t) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff ht0).mpr (by linarith)
  have hc4 : IntegrableOn (fun u => κ * (κ - 1) * u ^ (κ - 2) * ψ u) (Ioc 0 t) := by
    have h := hsing.mul_continuousOn_of_subset (hψc.mono hK) measurableSet_Ioc hcomp hsub
    have e : (fun u => κ * (κ - 1) * u ^ (κ - 2) * ψ u) =
        fun u => κ * (κ - 1) * (u ^ (κ - 2) * ψ u) := by
      funext u; ring
    rw [e]
    exact h.const_mul (κ * (κ - 1))
  have hsum := hc1.add (((hc4.add hc2).add hc3).const_mul ρ)
  exact hsum.const_mul A₀

/-- The Taylor remainder `φ(t) - φ(0) - φ'(0) t` is `o(t^κ)` at `0⁺` for `κ < 2`. -/
theorem bpzEP_tendsto_taylor {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 2 φ (Ioo (-1) 1)) {κ : ℝ}
    (hκ : κ < 2) :
    Tendsto (fun t => (φ t - φ 0 - deriv φ 0 * t) / t ^ κ) (𝓝[>] 0) (𝓝 0) := by
  have hK : Icc (0 : ℝ) (1 / 2) ⊆ Ioo (-1) 1 := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨-, hφ'c, hφ''c⟩ := bpzEP_continuousOn hφ
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hφ''c.mono hK)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, by norm_num⟩)
  -- `|φ'(s) - φ'(0)| ≤ C s` on `[0, 1/2]`
  have h1 : ∀ s ∈ Icc (0 : ℝ) (1 / 2), ‖deriv φ s - deriv φ 0‖ ≤ C * (s - 0) := by
    refine norm_image_sub_le_of_norm_deriv_le_segment' (f := deriv φ)
      (f' := deriv (deriv φ)) (fun x hx => ?_) (fun x hx => hC x (Ico_subset_Icc_self hx))
    exact ((bpzEP_hasDerivAt hφ (hK hx)).2).hasDerivWithinAt
  -- `|φ(t) - φ(0) - φ'(0) t| ≤ C t²` on `[0, 1/2]`
  have h2 : ∀ t ∈ Icc (0 : ℝ) (1 / 2), ‖φ t - φ 0 - deriv φ 0 * t‖ ≤ C * t * t := by
    intro t ht
    have hseg : ∀ x ∈ Icc (0 : ℝ) t, HasDerivWithinAt (fun s => φ s - φ 0 - deriv φ 0 * s)
        (deriv φ x - deriv φ 0) (Icc 0 t) x := by
      intro x hx
      have hx' : x ∈ Icc (0 : ℝ) (1 / 2) := ⟨hx.1, hx.2.trans ht.2⟩
      have h := ((bpzEP_hasDerivAt hφ (hK hx')).1.sub_const (φ 0)).sub
        ((hasDerivAt_id' x).const_mul (deriv φ 0))
      convert h.hasDerivWithinAt using 1
      ring
    have hbound : ∀ x ∈ Ico (0 : ℝ) t, ‖deriv φ x - deriv φ 0‖ ≤ C * t := by
      intro x hx
      have hx' : x ∈ Icc (0 : ℝ) (1 / 2) := ⟨hx.1, hx.2.le.trans ht.2⟩
      calc ‖deriv φ x - deriv φ 0‖ ≤ C * (x - 0) := h1 x hx'
        _ ≤ C * t := by gcongr; linarith [hx.2]
    have h := norm_image_sub_le_of_norm_deriv_le_segment' hseg hbound t ⟨ht.1, le_rfl⟩
    simpa using h
  -- squeeze
  have hlim : Tendsto (fun t : ℝ => C * t ^ (2 - κ)) (𝓝[>] 0) (𝓝 0) := by
    have hid : Tendsto (fun v : ℝ => v) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left
      nhdsWithin_le_nhds
    simpa using (hid.rpow_const_nhds_zero (by linarith)).const_mul C
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with t ht
  have htk : 0 < t ^ κ := Real.rpow_pos_of_pos ht.1 κ
  rw [norm_div, Real.norm_of_nonneg htk.le, div_le_iff₀ htk]
  calc ‖φ t - φ 0 - deriv φ 0 * t‖ ≤ C * t * t := h2 t ⟨ht.1.le, ht.2.le⟩
    _ = C * t ^ (2 - κ) * t ^ κ := by
      have e : t ^ (2 - κ) * t ^ κ = t * t := by
        rw [← Real.rpow_add ht.1, sub_add_cancel, Real.rpow_two, sq]
      rw [mul_assoc C (t ^ (2 - κ)) (t ^ κ), e]
      ring

end DOZZ.Proofs
