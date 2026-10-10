/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Residual.Joint
public import DOZZ.Statements.Defs.DozzFormula
public import DOZZ.Statements.Defs.IsUpsilon
import DOZZ.ShiftEquations.Quotient.RemovablePeriodic
import DOZZ.Complex.Basic
import DOZZ.ShiftEquations.Shift.Reflection

/-!
# The quotient is constant on each slice

For fixed `α₂, α₃` near `Q`, a joint representative `C` of `α₁ ↦ C(α₁, α₂, α₃)` with both shifts
gives, through the removable-periodic quotient
(`structureConstant_DOZZ_quotient_removable_periodic`), a factor `Ψ` with periods `γ` and `4/γ` and
`Ψ D = C` off a discrete set. Since `γ²` is irrational the periods are dense, so `Ψ` is a constant
`c`, and `C(t, α₂, α₃) = c D(t, α₂, α₃)` near every point of `(2η, Q)`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- The two periods `γ` and `4/γ` are incommensurable when `γ²` is irrational. -/
theorem periods_irrational {γ : ℝ} (hγ : 0 < γ) (hγirr : Irrational (γ ^ 2)) :
    ∀ q : ℚ, γ / (4 / γ) ≠ (q : ℝ) := by
  intro q hq
  apply hγirr
  refine ⟨4 * q, ?_⟩
  have h : γ / (4 / γ) = γ ^ 2 / 4 := by field_simp
  rw [h] at hq
  push_cast
  linarith

/-- **The quotient is constant on a slice.** -/
theorem slice_constant_of_joint {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) {γ μ η α₂ α₃ : ℝ} {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hγirr : Irrational (γ ^ 2)) (hμ : 0 < μ) (hη : 0 < η ∧ Q γ - 2 * η > γ)
    (hα₂ : Q γ - η < α₂ ∧ α₂ < Q γ) (hα₃ : Q γ - η < α₃ ∧ α₃ < Q γ) (hU : IsUpsilon γ U)
    (hjoint : ∃ h : ℝ, 0 < h ∧ ∃ C : ℂ → ℂ, MeromorphicOn C (horizontalStrip h) ∧
      (∀ α : ℝ, 2 * η < α → α < Q γ → C (α : ℂ) = (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
      (∀ᶠ z in codiscrete ℂ, C (z + γ / 2) =
        -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) * C (z - γ / 2)) ∧
      ∀ᶠ z in codiscrete ℂ, C (z + 2 / γ) =
        -(1 / (Real.pi * dualMu γ μ)) * shiftCoeffA γ (2 / γ) z (α₂ : ℂ) (α₃ : ℂ) *
          C (z - 2 / γ)) :
    ∃ c : ℂ, ∀ x : ℝ, 2 * η < x → x < Q γ → ∀ᶠ t : ℝ in 𝓝[≠] x,
      (structureConstant P M γ μ t α₂ α₃ : ℂ) = c * dozzFormula γ μ U t α₂ α₃ := by
  obtain ⟨h, hh, C, hCm, hCv, hfirst, hdual⟩ := hjoint
  obtain ⟨Ψ, hΨd, hΨD, hΨper⟩ := structureConstant_DOZZ_quotient_removable_periodic γ μ η U
    α₂ α₃ h hh hγ hγ2 hγirr hμ hη hα₂ hα₃ hU C hCm hfirst hdual
  have hSo : IsOpen (horizontalStrip h) := isOpen_horizontalStrip h
  have hΨm : MeromorphicOn Ψ (horizontalStrip h) := fun z hz =>
    (hΨd.analyticAt (hSo.mem_nhds hz)).meromorphicAt
  have hp₁ : ∀ z ∈ horizontalStrip h, (fun w => Ψ (w + ((γ : ℝ) : ℂ))) =ᶠ[𝓝[≠] z] Ψ :=
    fun z hz => eventually_nhdsWithin_of_eventually_nhds
      (eventually_of_mem (hSo.mem_nhds hz) fun w hw => (hΨper w hw).1)
  have hp₂ : ∀ z ∈ horizontalStrip h, (fun w => Ψ (w + ((4 / γ : ℝ) : ℂ))) =ᶠ[𝓝[≠] z] Ψ :=
    fun z hz => eventually_nhdsWithin_of_eventually_nhds
      (eventually_of_mem (hSo.mem_nhds hz) fun w hw => by
        have := (hΨper w hw).2
        push_cast
        exact this)
  obtain ⟨c, hc, -⟩ := meromorphicOn_strip_constant_of_dense_periods h hh Ψ hΨm γ (4 / γ) hγ
    (by positivity) (periods_irrational hγ hγirr) hp₁ hp₂
  have hΨc : ∀ z ∈ horizontalStrip h, Ψ z = c := fun z hz =>
    tendsto_nhds_unique
      ((hΨd.differentiableAt (hSo.mem_nhds hz)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (hc z hz).symm)
  refine ⟨c, fun x hx1 hx2 => ?_⟩
  have hxS : (x : ℂ) ∈ horizontalStrip h := by
    change |((x : ℝ) : ℂ).im| < h
    simpa using hh
  have hloc := (eventually_codiscrete_iff_forall_eventually_nhdsNE.mp hΨD) (x : ℂ)
  have hS : ∀ᶠ z in 𝓝[≠] (x : ℂ), z ∈ horizontalStrip h :=
    nhdsWithin_le_nhds (hSo.mem_nhds hxS)
  have hreal := (tendsto_ofReal_nhdsNE_slice x).eventually (hloc.and hS)
  have hI : ∀ᶠ t : ℝ in 𝓝[≠] x, 2 * η < t ∧ t < Q γ :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_of_mem (Ioo_mem_nhds hx1 hx2)
      fun t ht => ht)
  filter_upwards [hreal, hI] with t ht hIt
  rw [← hCv t hIt.1 hIt.2, ← ht.1, hΨc _ ht.2]

end DOZZ.Proofs

end
