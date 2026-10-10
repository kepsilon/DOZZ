/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Rbar.Multiplier
public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
public import DOZZ.Statements.Defs.ExtendedSeiberg3
public import DOZZ.Statements.Correlations.ComplexifyNCharges
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The diagonal γ/2 crossing, continued in the charge

The unit-volume γ/2 crossing on the diagonal `α' = α = a` holds on the crossing region
`2Q < 2a + ε - γ/2`. Both sides are restrictions of holomorphic functions of `a`: the left side is
the holomorphic extension of `C̄` (`unitVolumeStructureConstant_holomorphic_near_extended_domain`)
along `z ↦ (z - γ/2, ε, z)`, the right side the analytic multiplier times the extension along
`z ↦ (z, ε + γ/2, z)`. Both triples lie in the extended domain for `γ/4 + ε/2 < a < Q`, an interval
containing the crossing region, so the identity theorem continues the crossing to that whole
interval.
-/

@[expose] public section

open Filter Topology Set

namespace DOZZ.Proofs

/-- Sufficient linear conditions for the extended Seiberg bounds. -/
theorem extendedSeiberg3_of_lt {γ α₁ α₂ α₃ : ℝ} (hγ : 0 < γ) (h₁ : α₁ < Q γ) (h₂ : α₂ < Q γ)
    (h₃ : α₃ < Q γ) (h0 : 2 * Q γ - (α₁ + α₂ + α₃) < 4 / γ)
    (hk₁ : 2 * Q γ - (α₁ + α₂ + α₃) < 2 * (Q γ - α₁))
    (hk₂ : 2 * Q γ - (α₁ + α₂ + α₃) < 2 * (Q γ - α₂))
    (hk₃ : 2 * Q γ - (α₁ + α₂ + α₃) < 2 * (Q γ - α₃)) :
    ExtendedSeiberg3 γ α₁ α₂ α₃ := by
  have hs : -sExp γ α₁ α₂ α₃ = (2 * Q γ - (α₁ + α₂ + α₃)) / γ := by
    unfold sExp
    ring
  refine ⟨h₁, h₂, h₃, ?_⟩
  rw [hs]
  refine lt_min ?_ (lt_min ?_ (lt_min ?_ ?_))
  · have h := div_lt_div_of_pos_right h0 hγ
    rwa [div_div, ← sq] at h
  · have h := div_lt_div_of_pos_right hk₁ hγ
    rwa [show 2 * (Q γ - α₁) / γ = 2 / γ * (Q γ - α₁) by ring] at h
  · have h := div_lt_div_of_pos_right hk₂ hγ
    rwa [show 2 * (Q γ - α₂) / γ = 2 / γ * (Q γ - α₂) by ring] at h
  · have h := div_lt_div_of_pos_right hk₃ hγ
    rwa [show 2 * (Q γ - α₃) / γ = 2 / γ * (Q γ - α₃) by ring] at h

/-- The shifted triple `(a - γ/2, ε, a)` is in the extended domain for `γ/4 + ε/2 < a < Q`. -/
theorem extendedSeiberg3_shift {γ ε a : ℝ} (hγ : 0 < γ) (hε₁ : γ / 2 < ε) (hε₂ : ε < 2 / γ)
    (ha₁ : γ / 4 + ε / 2 < a) (ha₂ : a < Q γ) : ExtendedSeiberg3 γ (a - γ / 2) ε a := by
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hQ2 : 2 * Q γ = 4 / γ + γ := by
    rw [hQ]
    ring
  refine extendedSeiberg3_of_lt hγ (by linarith) (by rw [hQ]; linarith) ha₂ ?_ ?_ ?_ ?_ <;>
    linarith

/-- The raised triple `(a, ε + γ/2, a)` is in the extended domain for `γ/4 + ε/2 < a < Q`. -/
theorem extendedSeiberg3_raise {γ ε a : ℝ} (hγ : 0 < γ) (hε₁ : γ / 2 < ε) (hε₂ : ε < 2 / γ)
    (ha₁ : γ / 4 + ε / 2 < a) (ha₂ : a < Q γ) : ExtendedSeiberg3 γ a (ε + γ / 2) a := by
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hQ2 : 2 * Q γ = 4 / γ + γ := by
    rw [hQ]
    ring
  refine extendedSeiberg3_of_lt hγ ha₂ (by rw [hQ]; linarith) ha₂ ?_ ?_ ?_ ?_ <;> linarith

/-- The charge triple `(z - γ/2, ε, z)`. -/
noncomputable def shiftTriple (γ ε : ℝ) (z : ℂ) : Fin 3 → ℂ := ![z - (γ : ℂ) / 2, (ε : ℂ), z]

/-- The charge triple `(z, ε + γ/2, z)`. -/
noncomputable def raiseTriple (γ ε : ℝ) (z : ℂ) : Fin 3 → ℂ := ![z, (ε : ℂ) + (γ : ℂ) / 2, z]

theorem differentiable_shiftTriple (γ ε : ℝ) : Differentiable ℂ (shiftTriple γ ε) := by
  rw [differentiable_pi]
  intro i
  fin_cases i
  · exact differentiable_id.sub_const _
  · exact differentiable_const _
  · exact differentiable_id

theorem differentiable_raiseTriple (γ ε : ℝ) : Differentiable ℂ (raiseTriple γ ε) := by
  rw [differentiable_pi]
  intro i
  fin_cases i
  · exact differentiable_id
  · exact differentiable_const _
  · exact differentiable_id

theorem shiftTriple_ofReal (γ ε t : ℝ) :
    shiftTriple γ ε (t : ℂ) = complexifyNCharges ![t - γ / 2, ε, t] := by
  funext i
  fin_cases i <;> simp [shiftTriple, complexifyNCharges]

theorem raiseTriple_ofReal (γ ε t : ℝ) :
    raiseTriple γ ε (t : ℂ) = complexifyNCharges ![t, ε + γ / 2, t] := by
  funext i
  fin_cases i <;> simp [raiseTriple, complexifyNCharges]

/-- **The diagonal γ/2 crossing, continued in the charge** from the crossing region
`2Q < 2a + ε - γ/2` to `γ/4 + ε/2 < a < Q`, by the identity theorem. -/
theorem unitVolume_crossing_diag_continued {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (M : Ω → MeasureTheory.Measure ℂ) {γ ε : ℝ} (hγ : 0 < γ)
    (hε₁ : γ / 2 < ε) (hε₂ : ε < 2 / γ)
    (hCross : ∀ a : ℝ, a < Q γ → 2 * Q γ < a + a + ε - γ / 2 →
      unitVolumeStructureConstant P M γ (a - γ / 2) ε a =
        gammaHalfUnitCrossingMultiplier γ 1 a ε a *
          unitVolumeStructureConstant P M γ a (ε + γ / 2) a)
    {V₃ : Set (Fin 3 → ℂ)} (hV₃ : IsOpen V₃)
    (hV₃mem : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) →
      complexifyNCharges α ∈ V₃)
    {f₃ : (Fin 3 → ℂ) → ℂ} (hf₃ : DifferentiableOn ℂ f₃ V₃)
    (hf₃eq : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) →
      f₃ (complexifyNCharges α) = (unitVolumeStructureConstant P M γ (α 0) (α 1) (α 2) : ℂ))
    {a : ℝ} (ha₁ : γ / 4 + ε / 2 < a) (ha₂ : a < Q γ) :
    unitVolumeStructureConstant P M γ (a - γ / 2) ε a =
      crossingMultiplierReal γ ε a * unitVolumeStructureConstant P M γ a (ε + γ / 2) a := by
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have h2γ : 0 < 2 / γ := by positivity
  set J : Set ℝ := Ioo (γ / 4 + ε / 2) (Q γ) with hJ
  -- the domain of both holomorphic sides
  set D : Set ℂ := reflectionStrip γ ∩ shiftTriple γ ε ⁻¹' V₃ ∩ raiseTriple γ ε ⁻¹' V₃ with hD
  have hDo : IsOpen D := ((isOpen_reflectionStrip γ).inter
    (hV₃.preimage (differentiable_shiftTriple γ ε).continuous)).inter
      (hV₃.preimage (differentiable_raiseTriple γ ε).continuous)
  have hS : ∀ t ∈ J, f₃ (shiftTriple γ ε (t : ℂ)) =
      (unitVolumeStructureConstant P M γ (t - γ / 2) ε t : ℂ) := fun t ht => by
    rw [shiftTriple_ofReal]
    exact hf₃eq ![t - γ / 2, ε, t] (extendedSeiberg3_shift hγ hε₁ hε₂ ht.1 ht.2)
  have hR : ∀ t ∈ J, f₃ (raiseTriple γ ε (t : ℂ)) =
      (unitVolumeStructureConstant P M γ t (ε + γ / 2) t : ℂ) := fun t ht => by
    rw [raiseTriple_ofReal]
    exact hf₃eq ![t, ε + γ / 2, t] (extendedSeiberg3_raise hγ hε₁ hε₂ ht.1 ht.2)
  have hJD : ∀ t ∈ J, (t : ℂ) ∈ D := fun t ht => by
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [Complex.ofReal_re]
      linarith [ht.1]
    · rw [Complex.ofReal_re]
      exact ht.2
    · change shiftTriple γ ε (t : ℂ) ∈ V₃
      rw [shiftTriple_ofReal]
      exact hV₃mem ![t - γ / 2, ε, t] (extendedSeiberg3_shift hγ hε₁ hε₂ ht.1 ht.2)
    · change raiseTriple γ ε (t : ℂ) ∈ V₃
      rw [raiseTriple_ofReal]
      exact hV₃mem ![t, ε + γ / 2, t] (extendedSeiberg3_raise hγ hε₁ hε₂ ht.1 ht.2)
  -- the two holomorphic sides
  set g₁ : ℂ → ℂ := fun z => f₃ (shiftTriple γ ε z) with hg₁
  set g₂ : ℂ → ℂ := fun z => crossingMultiplierDiag γ ε z * f₃ (raiseTriple γ ε z) with hg₂
  have hg₁d : DifferentiableOn ℂ g₁ D :=
    hf₃.comp (differentiable_shiftTriple γ ε).differentiableOn fun _ hz => hz.1.2
  have hg₂d : DifferentiableOn ℂ g₂ D :=
    ((differentiableOn_crossingMultiplierDiag hγ hε₁).mono fun _ hz => hz.1.1).mul
      (hf₃.comp (differentiable_raiseTriple γ ε).differentiableOn fun _ hz => hz.2)
  -- they agree on the crossing region
  have hcross : ∀ t : ℝ, Q γ - (ε - γ / 2) / 2 < t → t < Q γ → g₁ (t : ℂ) = g₂ (t : ℂ) := by
    intro t ht1 ht2
    have htJ : t ∈ J := ⟨by rw [hQ] at ht1; linarith, ht2⟩
    have hx : 0 < (2 * t + ε - γ / 2 - 2 * Q γ) / γ := div_pos (by linarith) hγ
    simp only [hg₁, hg₂]
    rw [hS t htJ, hR t htJ, hCross t ht2 (by linarith), Complex.ofReal_mul,
      gammaHalfUnitCrossingMultiplier_eq_diag hγ one_pos hε₁ hε₂ hx]
  -- the identity theorem on the component of `D` through a crossing point
  set a₀ : ℝ := Q γ - (ε - γ / 2) / 4 with ha₀
  have ha₀J : a₀ ∈ J := ⟨by rw [ha₀, hQ]; linarith, by rw [ha₀]; linarith⟩
  set U := connectedComponentIn D (a₀ : ℂ) with hU
  have hUo : IsOpen U := hDo.connectedComponentIn
  have hUD : U ⊆ D := connectedComponentIn_subset D _
  have ha₀U : (a₀ : ℂ) ∈ U := mem_connectedComponentIn (hJD a₀ ha₀J)
  have hev : ∀ᶠ t : ℝ in 𝓝[≠] a₀, g₁ (t : ℂ) = g₂ (t : ℂ) :=
    eventually_nhdsWithin_of_eventually_nhds
      (eventually_of_mem (Ioo_mem_nhds (show Q γ - (ε - γ / 2) / 2 < a₀ by rw [ha₀]; linarith)
        (show a₀ < Q γ by rw [ha₀]; linarith)) fun t ht => hcross t ht.1 ht.2)
  have htend : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] a₀) (𝓝[≠] (a₀ : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun t ht => by
        simpa [Complex.ofReal_inj] using ht)
  have hEq : EqOn g₁ g₂ U :=
    ((hg₁d.mono hUD).analyticOnNhd hUo).eqOn_of_preconnected_of_frequently_eq
      ((hg₂d.mono hUD).analyticOnNhd hUo) isPreconnected_connectedComponentIn ha₀U
      (htend.frequently hev.frequently)
  -- the real interval lies in that component
  have hJU : (fun t : ℝ => (t : ℂ)) '' J ⊆ U :=
    (isPreconnected_Ioo.image _ Complex.continuous_ofReal.continuousOn).subset_connectedComponentIn
      ⟨a₀, ha₀J, rfl⟩ (image_subset_iff.mpr fun t ht => hJD t ht)
  have haJ : a ∈ J := ⟨ha₁, ha₂⟩
  have h := hEq (hJU ⟨a, haJ, rfl⟩)
  simp only [hg₁, hg₂] at h
  rw [hS a haJ, hR a haJ, crossingMultiplierDiag_ofReal hγ] at h
  exact_mod_cast h

end DOZZ.Proofs

end
