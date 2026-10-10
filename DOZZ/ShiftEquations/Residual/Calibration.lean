/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Residual.Slice
public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
public import DOZZ.Statements.Defs.IsEquatorGFF
public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.Statements.Defs.SExp
public import DOZZ.Statements.Correlations.ComplexifyNCharges
import DOZZ.ShiftEquations.Residual.ZeroModeLimit
import DOZZ.Correlations.Analytic.StructureConstantHolomorphic
import DOZZ.Roots.FormulaRegularity
import DOZZ.ShiftEquations.Rbar.Continuation
import DOZZ.ShiftEquations.Shift.ShiftGluing
import DOZZ.ShiftEquations.Shift.Reflection
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Calibration of the slice constant at the zero mode

Fix `α₂, α₃` near `Q` and suppose `C(t, α₂, α₃) = c D(t, α₂, α₃)` near every point of `(2η, Q)`.
Along the line `z ↦ (z, α₂, α₃)` the holomorphic extension `C̄ₕ` of the unit-volume structure
constant (`unitVolumeStructureConstant_holomorphic_near_extended_domain`) and `c` times the
normalized companion `μ^s Γ(s)⁻¹ D` agree near `(2η, Q)`, hence on the connected component through
the real interval `(|α₂ - α₃|, Q)`. That interval contains the zero mode `α₁⁰ = 2Q - α₂ - α₃`
(`s = 0`), where `C̄ = (2/γ) E[ρ⁰] = 2/γ` and the normalized companion tends to `2/γ`. Hence `c = 1`
and `C̄ = μ^s Γ(s)⁻¹ D` on the slice.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace DOZZ.Proofs

/-- The charge line `z ↦ (z, v, w)`. -/
noncomputable def tripleFirst (v w : ℂ) (z : ℂ) : Fin 3 → ℂ := ![z, v, w]

theorem differentiable_tripleFirst (v w : ℂ) : Differentiable ℂ (tripleFirst v w) := by
  rw [differentiable_pi]
  intro i
  fin_cases i
  · exact differentiable_id
  · exact differentiable_const _
  · exact differentiable_const _

theorem tripleFirst_ofReal (t v w : ℝ) :
    tripleFirst v w (t : ℂ) = complexifyNCharges ![t, v, w] := by
  funext i
  fin_cases i <;> simp [tripleFirst, complexifyNCharges]

/-- **The unit-volume structure constant at the zero mode** is `2/γ`. -/
theorem unitVolumeStructureConstant_zeroMode {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (M : Ω → Measure ℂ) {γ α₁ α₂ α₃ : ℝ}
    (hs : sExp γ α₁ α₂ α₃ = 0) : unitVolumeStructureConstant P M γ α₁ α₂ α₃ = 2 / γ := by
  unfold unitVolumeStructureConstant
  rw [hs, neg_zero]
  simp

/-- The structure constant is `μ^{-s} Γ(s) C̄`. -/
theorem structureConstant_eq_mul_unitVolume {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) (γ μ α₁ α₂ α₃ : ℝ) :
    structureConstant P M γ μ α₁ α₂ α₃ =
      μ ^ (-sExp γ α₁ α₂ α₃) * Real.Gamma (sExp γ α₁ α₂ α₃) *
        unitVolumeStructureConstant P M γ α₁ α₂ α₃ := by
  unfold structureConstant unitVolumeStructureConstant
  ring

/-- For `s > 0`, `C̄ = μ^s Γ(s)⁻¹ C` as complex numbers. -/
theorem unitVolume_eq_normalized {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) {γ μ α₁ α₂ α₃ : ℝ} (hμ : 0 < μ) (hs : 0 < sExp γ α₁ α₂ α₃) :
    (unitVolumeStructureConstant P M γ α₁ α₂ α₃ : ℂ) =
      ((μ : ℂ) ^ (sExp γ α₁ α₂ α₃ : ℂ) / Complex.Gamma (sExp γ α₁ α₂ α₃)) *
        (structureConstant P M γ μ α₁ α₂ α₃ : ℂ) := by
  have hΓ : Real.Gamma (sExp γ α₁ α₂ α₃) ≠ 0 := (Real.Gamma_pos_of_pos hs).ne'
  have hμs : μ ^ sExp γ α₁ α₂ α₃ * μ ^ (-sExp γ α₁ α₂ α₃) = 1 := by
    rw [← Real.rpow_add hμ, add_neg_cancel, Real.rpow_zero]
  have hreal : unitVolumeStructureConstant P M γ α₁ α₂ α₃ =
      μ ^ sExp γ α₁ α₂ α₃ / Real.Gamma (sExp γ α₁ α₂ α₃) *
        structureConstant P M γ μ α₁ α₂ α₃ := by
    rw [structureConstant_eq_mul_unitVolume]
    calc unitVolumeStructureConstant P M γ α₁ α₂ α₃
        = (μ ^ sExp γ α₁ α₂ α₃ * μ ^ (-sExp γ α₁ α₂ α₃)) *
            (Real.Gamma (sExp γ α₁ α₂ α₃) / Real.Gamma (sExp γ α₁ α₂ α₃)) *
              unitVolumeStructureConstant P M γ α₁ α₂ α₃ := by
          rw [hμs, div_self hΓ]
          ring
      _ = _ := by ring
  rw [hreal, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_cpow hμ.le,
    Complex.Gamma_ofReal]

/-- The slice `(t, α₂, α₃)` lies in the extended domain for `|α₂ - α₃| < t < Q`. -/
theorem extendedSeiberg3_slice {γ η α₂ α₃ t : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hη : 0 < η ∧ Q γ - 2 * η > γ) (hα₂ : Q γ - η < α₂ ∧ α₂ < Q γ)
    (hα₃ : Q γ - η < α₃ ∧ α₃ < Q γ) (ht₁ : max (α₂ - α₃) (α₃ - α₂) < t) (ht₂ : t < Q γ) :
    ExtendedSeiberg3 γ t α₂ α₃ := by
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hQ2 : 2 * Q γ = 4 / γ + γ := by rw [hQ]; ring
  have hγh : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ (by norm_num) hγ]
    nlinarith
  have h42 : 4 / γ = 2 * (2 / γ) := by ring
  have hm1 := le_max_left (α₂ - α₃) (α₃ - α₂)
  have hm2 := le_max_right (α₂ - α₃) (α₃ - α₂)
  refine extendedSeiberg3_of_lt hγ ht₂ hα₂.2 hα₃.2 ?_ ?_ ?_ ?_ <;> linarith [hη.1, hη.2]

/-- **The calibrated slice identity.** If the structure constant is `c` times the DOZZ formula
near every point of `(2η, Q)` on the slice `(·, α₂, α₃)`, then the unit-volume structure constant
equals the normalized companion `μ^s Γ(s)⁻¹ D` at every point of that interval (and `c = 1`). -/
theorem slice_identity_calibrated {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (M : Ω → Measure ℂ) {γ μ η α₂ α₃ : ℝ} {U : ℂ → ℂ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (hμ : 0 < μ) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hU : IsUpsilon γ U) (hη : 0 < η ∧ Q γ - 2 * η > γ) (hα₂ : Q γ - η < α₂ ∧ α₂ < Q γ)
    (hα₃ : Q γ - η < α₃ ∧ α₃ < Q γ) {c : ℂ}
    (hslice : ∀ x : ℝ, 2 * η < x → x < Q γ → ∀ᶠ t : ℝ in 𝓝[≠] x,
      (structureConstant P M γ μ t α₂ α₃ : ℂ) = c * dozzFormula γ μ U t α₂ α₃) :
    ∀ α₁ : ℝ, 2 * η < α₁ → α₁ < Q γ →
      (unitVolumeStructureConstant P M γ α₁ α₂ α₃ : ℂ) =
        ((μ : ℂ) ^ (sExp γ α₁ α₂ α₃ : ℂ) / Complex.Gamma (sExp γ α₁ α₂ α₃)) *
          dozzFormula γ μ U α₁ α₂ α₃ := by
  have : IsProbabilityMeasure P := hX.1
  obtain ⟨hη0, hηQ⟩ := hη
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hQη : 2 * η < Q γ := by linarith
  -- the holomorphic extension along the line `z ↦ (z, α₂, α₃)`
  obtain ⟨V₃, hV₃, hV₃mem, f₃, hf₃, hf₃eq⟩ :=
    unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM
  set L₀ : ℝ := max (α₂ - α₃) (α₃ - α₂) with hL₀
  have hL₀η : L₀ < 2 * η := by
    have : L₀ < η := max_lt (by linarith [hα₂.2, hα₃.1]) (by linarith [hα₂.1, hα₃.2])
    linarith
  have hES : ∀ t : ℝ, L₀ < t → t < Q γ → ExtendedSeiberg3 γ t α₂ α₃ := fun t h1 h2 =>
    extendedSeiberg3_slice hγ hγ2 ⟨hη0, hηQ⟩ hα₂ hα₃ h1 h2
  set ℓ := tripleFirst (α₂ : ℂ) (α₃ : ℂ) with hℓ
  set D₀ : Set ℂ := ℓ ⁻¹' V₃ with hD₀
  have hD₀o : IsOpen D₀ := hV₃.preimage (differentiable_tripleFirst _ _).continuous
  have hD₀mem : ∀ t : ℝ, L₀ < t → t < Q γ → (t : ℂ) ∈ D₀ := fun t h1 h2 => by
    change tripleFirst (α₂ : ℂ) (α₃ : ℂ) (t : ℂ) ∈ V₃
    rw [tripleFirst_ofReal]
    exact hV₃mem ![t, α₂, α₃] (hES t h1 h2)
  set g : ℂ → ℂ := fun z => f₃ (ℓ z) with hg
  have hgval : ∀ t : ℝ, L₀ < t → t < Q γ →
      g t = (unitVolumeStructureConstant P M γ t α₂ α₃ : ℂ) := fun t h1 h2 => by
    change f₃ (tripleFirst (α₂ : ℂ) (α₃ : ℂ) (t : ℂ)) = _
    rw [tripleFirst_ofReal]
    exact hf₃eq ![t, α₂, α₃] (hES t h1 h2)
  have hgd : DifferentiableOn ℂ g D₀ :=
    hf₃.comp (differentiable_tripleFirst _ _).differentiableOn fun _ hz => hz
  have hgan : ∀ z ∈ D₀, AnalyticAt ℂ g z := fun z hz => hgd.analyticAt (hD₀o.mem_nhds hz)
  -- the normalized companion along the same line
  set A : Fin 3 → ℂ → ℂ := ![fun z => z, fun _ => (α₂ : ℂ), fun _ => (α₃ : ℂ)] with hA
  have hAd : ∀ i, Differentiable ℂ (A i) := by
    intro i
    fin_cases i
    · exact differentiable_id
    · exact differentiable_const _
    · exact differentiable_const _
  set N : ℂ → ℂ := fun z => ((μ : ℂ) ^ ((A 0 z + A 1 z + A 2 z - 2 * Q γ) / γ) /
      Complex.Gamma ((A 0 z + A 1 z + A 2 z - 2 * Q γ) / γ)) *
        dozzFormula γ μ U (A 0 z) (A 1 z) (A 2 z) with hN
  have hNm : MeromorphicOn N univ := roots_formula_line_meromorphic hγ hγ2 hμ hU A hAd
  have hNval : ∀ t : ℝ, N t = ((μ : ℂ) ^ (sExp γ t α₂ α₃ : ℂ) /
      Complex.Gamma (sExp γ t α₂ α₃)) * dozzFormula γ μ U t α₂ α₃ := fun t => by
    have hexp : ((t : ℂ) + (α₂ : ℂ) + (α₃ : ℂ) - 2 * Q γ) / γ = (sExp γ t α₂ α₃ : ℂ) := by
      unfold sExp
      push_cast
      ring
    change ((μ : ℂ) ^ (((t : ℂ) + (α₂ : ℂ) + (α₃ : ℂ) - 2 * Q γ) / γ) /
      Complex.Gamma (((t : ℂ) + (α₂ : ℂ) + (α₃ : ℂ) - 2 * Q γ) / γ)) *
        dozzFormula γ μ U (t : ℂ) (α₂ : ℂ) (α₃ : ℂ) = _
    rw [hexp]
  -- agreement near a point of `(2η, Q)`
  set x₁ : ℝ := (2 * η + Q γ) / 2 with hx₁
  have hx₁1 : 2 * η < x₁ := by rw [hx₁]; linarith
  have hx₁2 : x₁ < Q γ := by rw [hx₁]; linarith
  have hagree : ∀ᶠ t : ℝ in 𝓝[≠] x₁, g t = c * N t := by
    filter_upwards [hslice x₁ hx₁1 hx₁2, eventually_nhdsWithin_of_eventually_nhds
      (eventually_of_mem (Ioo_mem_nhds hx₁1 hx₁2) fun t ht => ht)] with t ht hIt
    have hs : 0 < sExp γ t α₂ α₃ := by
      unfold sExp
      exact div_pos (by linarith [hα₂.1, hα₃.1, hIt.1]) hγ
    rw [hgval t (by linarith [hIt.1]) hIt.2, unitVolume_eq_normalized P M hμ hs, ht, hNval]
    ring
  -- the identity theorem along the connected component through the slice
  set W := connectedComponentIn D₀ (x₁ : ℂ) with hW
  have hWo : IsOpen W := hD₀o.connectedComponentIn
  have hWsub : W ⊆ D₀ := connectedComponentIn_subset D₀ _
  have hx₁W : (x₁ : ℂ) ∈ W := mem_connectedComponentIn (hD₀mem x₁ (by linarith) hx₁2)
  have hgm : MeromorphicOn g W := fun z hz => (hgan z (hWsub hz)).meromorphicAt
  have hNcm : MeromorphicOn (fun z => c * N z) W := fun z _ =>
    (MeromorphicAt.const c z).mul (hNm z (mem_univ z))
  have hEq : ∀ w ∈ W, g =ᶠ[𝓝[≠] w] (fun z => c * N z) := fun w hw =>
    ShiftGluing.meromorphicOn_eventuallyEq_of_frequently hgm hNcm
      isPreconnected_connectedComponentIn hx₁W hw
      ((tendsto_ofReal_nhdsNE_slice x₁).frequently hagree.frequently)
  have hIW : ∀ t : ℝ, L₀ < t → t < Q γ → (t : ℂ) ∈ W := by
    intro t h1 h2
    have hsub : (fun s : ℝ => (s : ℂ)) '' Ioo L₀ (Q γ) ⊆ W :=
      (isPreconnected_Ioo.image _ Complex.continuous_ofReal.continuousOn).subset_connectedComponentIn
        ⟨x₁, ⟨by linarith, hx₁2⟩, rfl⟩ (image_subset_iff.mpr fun s hs => hD₀mem s hs.1 hs.2)
    exact hsub ⟨t, ⟨h1, h2⟩, rfl⟩
  -- calibration at the zero mode `s = 0`
  set t₀ : ℝ := 2 * Q γ - α₂ - α₃ with ht₀
  have ht₀1 : L₀ < t₀ := max_lt (by linarith [hα₃.2]) (by linarith [hα₂.2])
  have ht₀2 : t₀ < Q γ := by linarith [hα₂.1, hα₃.1]
  have hs₀ : sExp γ t₀ α₂ α₃ = 0 := by
    unfold sExp
    rw [ht₀]
    ring_nf
  have hlim₁ : Tendsto (fun t : ℝ => g t) (𝓝[≠] t₀) (𝓝 ((2 / γ : ℝ) : ℂ)) := by
    have h : Tendsto (fun t : ℝ => g t) (𝓝[≠] t₀) (𝓝 (g t₀)) :=
      ((hgan (t₀ : ℂ) (hD₀mem t₀ ht₀1 ht₀2)).continuousAt.tendsto.comp
        (Complex.continuous_ofReal.tendsto t₀)).mono_left nhdsWithin_le_nhds
    rw [hgval t₀ ht₀1 ht₀2, unitVolumeStructureConstant_zeroMode P M hs₀] at h
    exact h
  have hlim₂ : Tendsto (fun t : ℝ => c * N t) (𝓝[≠] t₀) (𝓝 (c * (2 / γ))) := by
    have hL1 := dozzFormula_zeroMode_limit hγ hγ2 hμ hU (α₂ := α₂) (α₃ := α₃)
      (by linarith [hα₂.1]) hα₂.2 (by linarith [hα₃.1]) hα₃.2 (by linarith [hα₂.2, hα₃.2])
      (by linarith [hα₂.1, hα₃.1])
    exact (hL1.const_mul c).congr fun t => by rw [hNval]
  have hev : ∀ᶠ t : ℝ in 𝓝[≠] t₀, g t = c * N t :=
    (tendsto_ofReal_nhdsNE_slice t₀).eventually (hEq _ (hIW t₀ ht₀1 ht₀2))
  have hc1 : c = 1 := by
    have h := tendsto_nhds_unique (hlim₁.congr' hev) hlim₂
    have hγ0 : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ.ne'
    have h2γ : (2 / (γ : ℂ)) ≠ 0 := div_ne_zero two_ne_zero hγ0
    have h' : (c - 1) * (2 / (γ : ℂ)) = 0 := by
      rw [sub_mul, one_mul, ← h]
      push_cast
      ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right h2γ)
  -- pointwise identity on the slice
  intro α₁ h1 h2
  have hL₀α : L₀ < α₁ := by linarith
  have hs : 0 < sExp γ α₁ α₂ α₃ := by
    unfold sExp
    exact div_pos (by linarith [hα₂.1, hα₃.1]) hγ
  have hcont₁ : ContinuousAt g (α₁ : ℂ) := (hgan _ (hD₀mem α₁ hL₀α h2)).continuousAt
  have hNan : AnalyticAt ℂ N (α₁ : ℂ) :=
    roots_formula_line_analyticAt hγ hγ2 hμ hU A (α₁ : ℂ) (fun i => (hAd i).analyticAt _)
      α₁ α₂ α₃ rfl rfl rfl (hES α₁ hL₀α h2)
      (fun n hn => by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)
  have hcont₂ : ContinuousAt (fun z => c * N z) (α₁ : ℂ) :=
    (analyticAt_const.mul hNan).continuousAt
  have hpt : g α₁ = c * N α₁ :=
    tendsto_nhds_unique (hcont₁.tendsto.mono_left nhdsWithin_le_nhds)
      ((hcont₂.tendsto.mono_left nhdsWithin_le_nhds).congr' (hEq _ (hIW α₁ hL₀α h2)).symm)
  rw [hgval α₁ hL₀α h2, hNval, hc1, one_mul] at hpt
  exact hpt

end DOZZ.Proofs

end
