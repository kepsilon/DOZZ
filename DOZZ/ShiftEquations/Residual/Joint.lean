/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.ShiftCoeffA
public import DOZZ.Statements.Defs.DualMu
public import DOZZ.Statements.Defs.StructureConstant
public import DOZZ.Statements.Complex.HorizontalStrip
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Topology.DiscreteSubset
import DOZZ.ShiftEquations.Shift.ShiftGluing
import DOZZ.ShiftEquations.Shift.Reflection
import DOZZ.ShiftEquations.Gluing.Meromorphy
import DOZZ.Complex.Basic

/-!
# One representative with both shifts

The first structure shift (`structureConstant_first_shift_strip`) and the first-case dual structure
shift (`structureConstant_dual_shift_strip_first_case`, `η ≤ γ/4`) are separate existential
statements. Their functions agree with the structure constant on `(2η, Q)`, hence as germs on a
common strip. Cutting one of them off outside a thinner strip gives a single function, meromorphic
on the thinner strip, that satisfies both shifts along the codiscrete filter of `ℂ`
(`exists_joint_representative`).
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- The cut-off of `F` outside the strip `S_k`. -/
noncomputable def cutoffStrip (k : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  if |z.im| < k then F z else 0

theorem cutoffStrip_of_lt {k : ℝ} {F : ℂ → ℂ} {z : ℂ} (hz : |z.im| < k) :
    cutoffStrip k F z = F z := by
  simp [cutoffStrip, hz]

theorem cutoffStrip_of_not_lt {k : ℝ} {F : ℂ → ℂ} {z : ℂ} (hz : ¬ |z.im| < k) :
    cutoffStrip k F z = 0 := by
  simp [cutoffStrip, hz]

theorem abs_im_add_ofReal (z : ℂ) (t : ℝ) : |(z + (t : ℂ)).im| = |z.im| := by
  simp

/-- **Cut-off representatives.** A relation `F (z + t₁) = m z * F (z + t₂)` with real `t₁, t₂`,
holding near every point of `S_h`, holds along the codiscrete filter of `ℂ` for the cut-off of
`F` outside `S_{h/2}`. -/
theorem cutoff_relation_codiscrete {F m : ℂ → ℂ} {h : ℝ} (hh : 0 < h) (t₁ t₂ : ℝ)
    (hrel : ∀ w ∈ horizontalStrip h, ∀ᶠ z in 𝓝[≠] w, F (z + t₁) = m z * F (z + t₂)) :
    ∀ᶠ z in codiscrete ℂ,
      cutoffStrip (h / 2) F (z + t₁) = m z * cutoffStrip (h / 2) F (z + t₂) := by
  have hzero : ∀ z : ℂ, ¬ |z.im| < h / 2 →
      cutoffStrip (h / 2) F (z + t₁) = m z * cutoffStrip (h / 2) F (z + t₂) := fun z hz => by
    rw [cutoffStrip_of_not_lt (by rwa [abs_im_add_ofReal]),
      cutoffStrip_of_not_lt (by rwa [abs_im_add_ofReal]), mul_zero]
  rw [eventually_codiscrete_iff_forall_eventually_nhdsNE]
  intro x
  by_cases hx : |x.im| < h
  · filter_upwards [hrel x hx] with z hz
    by_cases hzk : |z.im| < h / 2
    · rw [cutoffStrip_of_lt (by rwa [abs_im_add_ofReal]),
        cutoffStrip_of_lt (by rwa [abs_im_add_ofReal])]
      exact hz
    · exact hzero z hzk
  · have hopen : IsOpen {w : ℂ | h / 2 < |w.im|} :=
      isOpen_lt continuous_const Complex.continuous_im.abs
    have hxo : h / 2 < |x.im| := by
      have := not_lt.mp hx
      linarith
    filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hxo)] with z hz
    exact hzero z (not_lt.mpr (le_of_lt hz))

/-- The cut-off is meromorphic on the thinner strip. -/
theorem meromorphicOn_cutoffStrip {F : ℂ → ℂ} {h : ℝ} (hF : MeromorphicOn F (horizontalStrip h))
    {k : ℝ} (hk : k ≤ h) : MeromorphicOn (cutoffStrip k F) (horizontalStrip k) := by
  intro z hz
  have hz' : |z.im| < k := hz
  refine (hF z (lt_of_lt_of_le hz' hk)).congr ?_
  have hopen : IsOpen {w : ℂ | |w.im| < k} := isOpen_horizontalStrip k
  filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hz')] with w hw
  exact (cutoffStrip_of_lt hw).symm

/-- **The joint representative**: from a γ/2-shift function and a 2/γ-shift function, both equal to
the structure constant on `(2η, Q)`, one function meromorphic on a strip with both shifts along the
codiscrete filter of `ℂ`. -/
theorem exists_joint_representative {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) {γ μ η α₂ α₃ : ℝ} (hηQ : 2 * η < Q γ)
    (h51 : ∃ h : ℝ, 0 < h ∧ ∃ C : ℂ → ℂ, MeromorphicOn C {z | |z.im| < h} ∧
      (∀ α : ℝ, 2 * η < α → α < Q γ → C (α : ℂ) = (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
      ∀ᶠ z in codiscrete ℂ, C (z + γ / 2) =
        -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) * C (z - γ / 2))
    (hDualStripFirstCase : ∃ h : ℝ, 0 < h ∧ ∃ C : ℂ → ℂ, MeromorphicOn C {z | |z.im| < h} ∧
      (∀ α : ℝ, 2 * η < α → α < Q γ → C (α : ℂ) = (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
      ∀ᶠ z in codiscrete ℂ, C (z + 2 / γ) =
        -(1 / (Real.pi * dualMu γ μ)) * shiftCoeffA γ (2 / γ) z (α₂ : ℂ) (α₃ : ℂ) *
          C (z - 2 / γ)) :
    ∃ h : ℝ, 0 < h ∧ ∃ C : ℂ → ℂ, MeromorphicOn C (horizontalStrip h) ∧
      (∀ α : ℝ, 2 * η < α → α < Q γ → C (α : ℂ) = (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
      (∀ᶠ z in codiscrete ℂ, C (z + γ / 2) =
        -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) * C (z - γ / 2)) ∧
      ∀ᶠ z in codiscrete ℂ, C (z + 2 / γ) =
        -(1 / (Real.pi * dualMu γ μ)) * shiftCoeffA γ (2 / γ) z (α₂ : ℂ) (α₃ : ℂ) *
          C (z - 2 / γ) := by
  obtain ⟨h₁, hh₁, C₁, hC₁m, hC₁v, hC₁s⟩ := h51
  obtain ⟨h₂, hh₂, C₂, hC₂m, hC₂v, hC₂s⟩ := hDualStripFirstCase
  set h := min h₁ h₂ with hhdef
  have hh : 0 < h := lt_min hh₁ hh₂
  have hC₁m' : MeromorphicOn C₁ (horizontalStrip h) := fun z hz =>
    hC₁m z (show |z.im| < h₁ from lt_of_lt_of_le (show |z.im| < h from hz) (min_le_left _ _))
  have hC₂m' : MeromorphicOn C₂ (horizontalStrip h) := fun z hz =>
    hC₂m z (show |z.im| < h₂ from lt_of_lt_of_le (show |z.im| < h from hz) (min_le_right _ _))
  -- the two functions have the same germs on the strip
  set x₀ : ℝ := (2 * η + Q γ) / 2 with hx₀
  have hx₀1 : 2 * η < x₀ := by rw [hx₀]; linarith
  have hx₀2 : x₀ < Q γ := by rw [hx₀]; linarith
  have hx₀S : (x₀ : ℂ) ∈ horizontalStrip h := by
    change |((x₀ : ℝ) : ℂ).im| < h
    simpa using hh
  have hev : ∀ᶠ t : ℝ in 𝓝[≠] x₀, C₁ (t : ℂ) = C₂ (t : ℂ) :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_of_mem (Ioo_mem_nhds hx₀1 hx₀2)
      fun t ht => (hC₁v t ht.1 ht.2).trans (hC₂v t ht.1 ht.2).symm)
  have hgerm : ∀ w ∈ horizontalStrip h, C₁ =ᶠ[𝓝[≠] w] C₂ := fun w hw =>
    ShiftGluing.meromorphicOn_eventuallyEq_of_frequently hC₁m' hC₂m'
      (isPreconnected_horizontalStrip h) hx₀S hw
      ((tendsto_ofReal_nhdsNE_slice x₀).frequently hev.frequently)
  -- the first shift near every point, in translation form
  have hfirst : ∀ w ∈ horizontalStrip h, ∀ᶠ z in 𝓝[≠] w,
      C₁ (z + ((γ / 2 : ℝ) : ℂ)) = (-(1 / (Real.pi * μ)) *
        shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ)) * C₁ (z + ((-(γ / 2) : ℝ) : ℂ)) :=
    fun w _ => ((eventually_codiscrete_iff_forall_eventually_nhdsNE.mp hC₁s) w).mono
      fun z hz => by
        rw [show z + ((γ / 2 : ℝ) : ℂ) = z + γ / 2 by push_cast; ring,
          show z + ((-(γ / 2) : ℝ) : ℂ) = z - γ / 2 by push_cast; ring]
        exact hz
  -- the dual shift near every point, transported from the second function
  have hdual : ∀ w ∈ horizontalStrip h, ∀ᶠ z in 𝓝[≠] w,
      C₁ (z + ((2 / γ : ℝ) : ℂ)) = (-(1 / (Real.pi * dualMu γ μ)) *
        shiftCoeffA γ (2 / γ) z (α₂ : ℂ) (α₃ : ℂ)) * C₁ (z + ((-(2 / γ)) : ℝ)) := by
    intro w hw
    have hp := ShiftGluing.eventually_comp_add (z := w) ((2 / γ : ℝ) : ℂ)
      (hgerm _ (add_ofReal_mem_horizontalStrip_glue hw (2 / γ)))
    have hm := ShiftGluing.eventually_comp_add (z := w) ((-(2 / γ) : ℝ) : ℂ)
      (hgerm _ (add_ofReal_mem_horizontalStrip_glue hw (-(2 / γ))))
    filter_upwards [hp, hm, (eventually_codiscrete_iff_forall_eventually_nhdsNE.mp hC₂s) w]
      with z h1 h2 h3
    rw [h1, h2, show z + ((2 / γ : ℝ) : ℂ) = z + 2 / γ by push_cast; ring,
      show z + ((-(2 / γ)) : ℝ) = z - 2 / γ by push_cast; ring]
    exact h3
  refine ⟨h / 2, half_pos hh, cutoffStrip (h / 2) C₁,
    meromorphicOn_cutoffStrip hC₁m' (half_le_self hh.le), fun α h1 h2 => ?_, ?_, ?_⟩
  · rw [cutoffStrip_of_lt (by simpa using half_pos hh)]
    exact hC₁v α h1 h2
  · refine (cutoff_relation_codiscrete hh (γ / 2) (-(γ / 2)) hfirst).mono fun z hz => ?_
    rw [show z + γ / 2 = z + ((γ / 2 : ℝ) : ℂ) by push_cast; ring,
      show z - γ / 2 = z + ((-(γ / 2) : ℝ) : ℂ) by push_cast; ring]
    exact hz
  · refine (cutoff_relation_codiscrete hh (2 / γ) (-(2 / γ)) hdual).mono fun z hz => ?_
    rw [show z + 2 / γ = z + ((2 / γ : ℝ) : ℂ) by push_cast; ring,
      show z - 2 / γ = z + ((-(2 / γ)) : ℝ) by push_cast; ring]
    exact hz

end DOZZ.Proofs

end
