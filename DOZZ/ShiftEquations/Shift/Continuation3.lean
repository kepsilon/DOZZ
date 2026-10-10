/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Shift.Multiplier3
public import DOZZ.ShiftEquations.Rbar.Continuation
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The γ/2 crossing on the two-pole slice

Write `α' = Q - η` and `α = 2/γ + η` (the charges of the two-pole expansion
`structureConstant_two_pole_expansion`). The unit-volume γ/2 crossing holds on its crossing region
`2Q < α + α' + ε - γ/2`. Continuing first in the third charge (along `z ↦ (Q - η, ε, z)` for fixed
`γ/2 + η < ε < 2/γ`, on `2/γ < Re z < Q`) and then in the middle charge (along
`z ↦ (Q - η, z, 2/γ + η)`, on `2η < Re z < 2/γ`), where both sides are holomorphic
(`unitVolumeStructureConstant_holomorphic_near_extended_domain` and the analytic multiplier), gives
the crossing `C̄(Q - η - γ/2, x, 2/γ + η) = T(Q - η, x, 2/γ + η) C̄(Q - η, x + γ/2, 2/γ + η)` for
`2η < x < 2/γ` ([KRV, §10.2]).
-/

@[expose] public section

open Filter Topology Set

namespace DOZZ.Proofs

/-- **The identity theorem along a real interval.** -/
theorem eq_of_real_interval {D : Set ℂ} (hD : IsOpen D) {g₁ g₂ : ℂ → ℂ}
    (hg₁ : DifferentiableOn ℂ g₁ D) (hg₂ : DifferentiableOn ℂ g₂ D) {a b c d : ℝ}
    (hJD : ∀ t : ℝ, a < t → t < b → (t : ℂ) ∈ D) (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b)
    (heq : ∀ t : ℝ, c < t → t < d → g₁ t = g₂ t) {t : ℝ} (ht₁ : a < t) (ht₂ : t < b) :
    g₁ t = g₂ t := by
  set x₀ : ℝ := (c + d) / 2 with hx₀
  have hx₀D : (x₀ : ℂ) ∈ D := hJD x₀ (by rw [hx₀]; linarith) (by rw [hx₀]; linarith)
  set U := connectedComponentIn D (x₀ : ℂ) with hU
  have hUo : IsOpen U := hD.connectedComponentIn
  have hUD : U ⊆ D := connectedComponentIn_subset D _
  have hev : ∀ᶠ s : ℝ in 𝓝[≠] x₀, g₁ (s : ℂ) = g₂ (s : ℂ) :=
    eventually_nhdsWithin_of_eventually_nhds
      (eventually_of_mem (Ioo_mem_nhds (show c < x₀ by rw [hx₀]; linarith)
        (show x₀ < d by rw [hx₀]; linarith)) fun s hs => heq s hs.1 hs.2)
  have htend : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[≠] x₀) (𝓝[≠] (x₀ : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun s hs => by
        simpa [Complex.ofReal_inj] using hs)
  have hEq : EqOn g₁ g₂ U :=
    ((hg₁.mono hUD).analyticOnNhd hUo).eqOn_of_preconnected_of_frequently_eq
      ((hg₂.mono hUD).analyticOnNhd hUo) isPreconnected_connectedComponentIn
      (mem_connectedComponentIn hx₀D) (htend.frequently hev.frequently)
  have hJU : (fun s : ℝ => (s : ℂ)) '' Ioo a b ⊆ U :=
    (isPreconnected_Ioo.image _ Complex.continuous_ofReal.continuousOn).subset_connectedComponentIn
      ⟨x₀, ⟨by rw [hx₀]; linarith, by rw [hx₀]; linarith⟩, rfl⟩
      (image_subset_iff.mpr fun s hs => hJD s hs.1 hs.2)
  exact hEq (hJU ⟨t, ⟨ht₁, ht₂⟩, rfl⟩)

/-- The charge line `z ↦ (u, v, z)`. -/
noncomputable def tripleThird (u v : ℂ) (z : ℂ) : Fin 3 → ℂ := ![u, v, z]

/-- The charge line `z ↦ (u, z + s, w)`. -/
noncomputable def tripleSecond (u s w : ℂ) (z : ℂ) : Fin 3 → ℂ := ![u, z + s, w]

theorem differentiable_tripleThird (u v : ℂ) : Differentiable ℂ (tripleThird u v) := by
  rw [differentiable_pi]
  intro i
  fin_cases i
  · exact differentiable_const _
  · exact differentiable_const _
  · exact differentiable_id

theorem differentiable_tripleSecond (u s w : ℂ) : Differentiable ℂ (tripleSecond u s w) := by
  rw [differentiable_pi]
  intro i
  fin_cases i
  · exact differentiable_const _
  · exact differentiable_id.add_const _
  · exact differentiable_const _

theorem tripleThird_ofReal (u v t : ℝ) :
    tripleThird u v (t : ℂ) = complexifyNCharges ![u, v, t] := by
  funext i
  fin_cases i <;> simp [tripleThird, complexifyNCharges]

theorem tripleSecond_ofReal (u s w t : ℝ) :
    tripleSecond u s w (t : ℂ) = complexifyNCharges ![u, t + s, w] := by
  funext i
  fin_cases i <;> simp [tripleSecond, complexifyNCharges]

theorem crossA3_add_one_re (γ : ℝ) (a' e a : ℂ) :
    (crossA3 γ a' e a + 1).re = γ / 4 * (a'.re + e.re + a.re - Q γ - γ) + 1 / 2 := by
  unfold crossA3
  simp [Complex.mul_re]
  ring

theorem crossB3_re (γ : ℝ) (a' e a : ℂ) :
    (crossB3 γ a' e a).re = γ / 4 * (a'.re + e.re - a.re - Q γ) + 1 / 2 := by
  unfold crossB3
  simp [Complex.mul_re]

theorem one_sub_crossC3_re (γ : ℝ) (a' : ℂ) :
    (1 - crossC3 γ a').re = γ / 2 * (Q γ - a'.re) := by
  unfold crossC3
  simp [Complex.mul_re]

theorem one_sub_mul_half_re (γ : ℝ) (e : ℂ) : (1 - (γ : ℂ) * e / 2).re = 1 - γ * e.re / 2 := by
  simp [Complex.mul_re]

/-- The basic window facts for the slice `(Q - η, ·, 2/γ + η)`. -/
theorem slice_facts {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    Q γ = 2 / γ + γ / 2 ∧ 2 * Q γ = 4 / γ + γ ∧ γ / 2 < 2 / γ ∧ 4 / γ = 2 * (2 / γ) ∧
      0 < 2 / γ := by
  have hγh : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ (by norm_num) hγ]
    nlinarith
  refine ⟨rfl, by rw [Q]; ring, hγh, by ring, by positivity⟩

theorem extendedSeiberg3_sliceA_left {γ η ε t : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hη : 0 < η)
    (hε₁ : γ / 2 + η < ε) (hε₂ : ε < 2 / γ) (ht₁ : 2 / γ < t) (ht₂ : t < Q γ) :
    ExtendedSeiberg3 γ (Q γ - η - γ / 2) ε t := by
  obtain ⟨hQ, hQ2, hγh, h42, h2⟩ := slice_facts hγ hγ2
  refine extendedSeiberg3_of_lt hγ (by linarith) (by rw [hQ]; linarith) ht₂ ?_ ?_ ?_ ?_ <;>
    linarith

theorem extendedSeiberg3_sliceA_right {γ η ε t : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hη : 0 < η)
    (hε₁ : γ / 2 + η < ε) (hε₂ : ε < 2 / γ) (ht₁ : 2 / γ < t) (ht₂ : t < Q γ) :
    ExtendedSeiberg3 γ (Q γ - η) (ε + γ / 2) t := by
  obtain ⟨hQ, hQ2, hγh, h42, h2⟩ := slice_facts hγ hγ2
  refine extendedSeiberg3_of_lt hγ (by linarith) (by rw [hQ]; linarith) ht₂ ?_ ?_ ?_ ?_ <;>
    linarith

theorem extendedSeiberg3_sliceB_left {γ η x : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hη : 0 < η)
    (hη2 : η < γ / 2) (hx₁ : 2 * η < x) (hx₂ : x < 2 / γ) :
    ExtendedSeiberg3 γ (Q γ - η - γ / 2) x (2 / γ + η) := by
  obtain ⟨hQ, hQ2, hγh, h42, h2⟩ := slice_facts hγ hγ2
  refine extendedSeiberg3_of_lt hγ (by linarith) (by rw [hQ]; linarith) (by rw [hQ]; linarith)
    ?_ ?_ ?_ ?_ <;> rw [hQ] at * <;> linarith

theorem extendedSeiberg3_sliceB_right {γ η x : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hη : 0 < η)
    (hη4 : η < γ / 4) (hx₁ : -(2 * η) < x) (hx₂ : x < 2 / γ) :
    ExtendedSeiberg3 γ (Q γ - η) (x + γ / 2) (2 / γ + η) := by
  obtain ⟨hQ, hQ2, hγh, h42, h2⟩ := slice_facts hγ hγ2
  refine extendedSeiberg3_of_lt hγ (by linarith) (by rw [hQ]; linarith) (by rw [hQ]; linarith)
    ?_ ?_ ?_ ?_ <;> rw [hQ] at * <;> linarith

/-- `γ/4 · (2/γ) = 1/2`-type bound used for the multiplier conditions. -/
theorem quarter_mul_lt {γ u v : ℝ} (hγ : 0 < γ) (h : u < v) : γ / 4 * u < γ / 4 * v :=
  mul_lt_mul_of_pos_left h (by positivity)

/-- **Step A**: the crossing at `(Q - η, ε, t)` for `γ/2 + η < ε < 2/γ` and `2/γ < t < Q`,
continued from the crossing region in the third charge. -/
theorem unitVolume_crossing_sliceA {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (M : Ω → MeasureTheory.Measure ℂ) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2)
    (hCross : ∀ μ α' ε α : ℝ, 0 < μ → γ / 2 < ε → ε < 2 / γ → α < Q γ → α' < Q γ →
      2 * Q γ < α + α' + ε - γ / 2 →
      unitVolumeStructureConstant P M γ (α' - γ / 2) ε α =
        gammaHalfUnitCrossingMultiplier γ μ α' ε α *
          unitVolumeStructureConstant P M γ α' (ε + γ / 2) α)
    {V₃ : Set (Fin 3 → ℂ)} (hV₃ : IsOpen V₃)
    (hV₃mem : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) →
      complexifyNCharges α ∈ V₃)
    {f₃ : (Fin 3 → ℂ) → ℂ} (hf₃ : DifferentiableOn ℂ f₃ V₃)
    (hf₃eq : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) →
      f₃ (complexifyNCharges α) = (unitVolumeStructureConstant P M γ (α 0) (α 1) (α 2) : ℂ))
    {η ε : ℝ} (hη : 0 < η) (hε₁ : γ / 2 + η < ε) (hε₂ : ε < 2 / γ)
    {t : ℝ} (ht₁ : 2 / γ < t) (ht₂ : t < Q γ) :
    unitVolumeStructureConstant P M γ (Q γ - η - γ / 2) ε t =
      crossingMultiplier3Real γ (Q γ - η) ε t *
        unitVolumeStructureConstant P M γ (Q γ - η) (ε + γ / 2) t := by
  obtain ⟨hQ, hQ2, hγh, h42, h2⟩ := slice_facts hγ hγ2
  set u₁ : ℂ := ((Q γ - η - γ / 2 : ℝ) : ℂ) with hu₁
  set u₂ : ℂ := ((Q γ - η : ℝ) : ℂ) with hu₂
  set v₂ : ℂ := ((ε + γ / 2 : ℝ) : ℂ) with hv₂
  set D : Set ℂ := {z | 2 / γ < z.re ∧ z.re < Q γ} ∩ tripleThird u₁ ε ⁻¹' V₃ ∩
    tripleThird u₂ v₂ ⁻¹' V₃ with hD
  have hDo : IsOpen D :=
    (((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).inter
      (hV₃.preimage (differentiable_tripleThird _ _).continuous)).inter
      (hV₃.preimage (differentiable_tripleThird _ _).continuous)
  have hL : ∀ s : ℝ, 2 / γ < s → s < Q γ → f₃ (tripleThird u₁ ε (s : ℂ)) =
      (unitVolumeStructureConstant P M γ (Q γ - η - γ / 2) ε s : ℂ) := fun s h1 h2 => by
    rw [hu₁, tripleThird_ofReal]
    exact hf₃eq ![Q γ - η - γ / 2, ε, s]
      (extendedSeiberg3_sliceA_left hγ hγ2 hη hε₁ hε₂ h1 h2)
  have hR : ∀ s : ℝ, 2 / γ < s → s < Q γ → f₃ (tripleThird u₂ v₂ (s : ℂ)) =
      (unitVolumeStructureConstant P M γ (Q γ - η) (ε + γ / 2) s : ℂ) := fun s h1 h2 => by
    rw [hu₂, hv₂, tripleThird_ofReal]
    exact hf₃eq ![Q γ - η, ε + γ / 2, s]
      (extendedSeiberg3_sliceA_right hγ hγ2 hη hε₁ hε₂ h1 h2)
  have hJD : ∀ s : ℝ, 2 / γ < s → s < Q γ → (s : ℂ) ∈ D := fun s h1 h2 => by
    refine ⟨⟨⟨by rw [Complex.ofReal_re]; exact h1, by rw [Complex.ofReal_re]; exact h2⟩, ?_⟩, ?_⟩
    · change tripleThird u₁ ε (s : ℂ) ∈ V₃
      rw [hu₁, tripleThird_ofReal]
      exact hV₃mem ![Q γ - η - γ / 2, ε, s]
        (extendedSeiberg3_sliceA_left hγ hγ2 hη hε₁ hε₂ h1 h2)
    · change tripleThird u₂ v₂ (s : ℂ) ∈ V₃
      rw [hu₂, hv₂, tripleThird_ofReal]
      exact hV₃mem ![Q γ - η, ε + γ / 2, s]
        (extendedSeiberg3_sliceA_right hγ hγ2 hη hε₁ hε₂ h1 h2)
  -- the multiplier is holomorphic on the domain
  have hT : DifferentiableOn ℂ (fun z => crossingMultiplier3 γ u₂ ε z) D := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    obtain ⟨⟨⟨hz1, hz2⟩, -⟩, -⟩ := hz
    refine differentiableAt_crossingMultiplier3 (φ₁ := fun _ => u₂) (φ₂ := fun _ => (ε : ℂ))
      (φ₃ := id) (differentiableAt_const _) (differentiableAt_const _) differentiableAt_id
      ?_ ?_ ?_ ?_
    · rw [crossA3_add_one_re, hu₂, Complex.ofReal_re, Complex.ofReal_re]
      have : 0 < γ / 4 * (Q γ - η + ε + (id z).re - Q γ - γ) :=
        mul_pos (by positivity) (by simp only [id]; linarith)
      linarith
    · rw [crossB3_re, hu₂, Complex.ofReal_re, Complex.ofReal_re]
      have h1 := quarter_mul_lt (u := -(2 / γ)) (v := Q γ - η + ε - (id z).re - Q γ) hγ
        (by simp only [id]; linarith)
      have h2' : γ / 4 * -(2 / γ) = -(1 / 2) := by field_simp; ring
      linarith
    · rw [one_sub_crossC3_re, hu₂, Complex.ofReal_re]
      exact mul_pos (by positivity) (by linarith)
    · rw [one_sub_mul_half_re, Complex.ofReal_re]
      have : γ * ε < γ * (2 / γ) := mul_lt_mul_of_pos_left hε₂ hγ
      rw [mul_div_cancel₀ _ hγ.ne'] at this
      linarith
  have hg₁ : DifferentiableOn ℂ (fun z => f₃ (tripleThird u₁ ε z)) D :=
    hf₃.comp (differentiable_tripleThird _ _).differentiableOn fun _ hz => hz.1.2
  have hg₂ : DifferentiableOn ℂ (fun z => crossingMultiplier3 γ u₂ ε z *
      f₃ (tripleThird u₂ v₂ z)) D :=
    hT.mul (hf₃.comp (differentiable_tripleThird _ _).differentiableOn fun _ hz => hz.2)
  -- agreement on the crossing region
  set c₀ : ℝ := max (2 / γ) (Q γ + η + γ / 2 - ε) with hc₀
  have hc₀Q : c₀ < Q γ := max_lt (by rw [hQ]; linarith) (by linarith)
  have heq : ∀ s : ℝ, c₀ < s → s < Q γ → f₃ (tripleThird u₁ ε (s : ℂ)) =
      crossingMultiplier3 γ u₂ ε s * f₃ (tripleThird u₂ v₂ (s : ℂ)) := by
    intro s hs1 hs2
    have hs3 : 2 / γ < s := lt_of_le_of_lt (le_max_left _ _) hs1
    have hs4 : Q γ + η + γ / 2 - ε < s := lt_of_le_of_lt (le_max_right _ _) hs1
    have hx : 0 < (s + (Q γ - η) + ε - γ / 2 - 2 * Q γ) / γ := div_pos (by linarith) hγ
    rw [hL s hs3 hs2, hR s hs3 hs2, hu₂,
      ← gammaHalfUnitCrossingMultiplier_eq_three hγ one_pos (by linarith) hε₂ hx,
      ← Complex.ofReal_mul,
      hCross 1 (Q γ - η) ε s one_pos (by linarith) hε₂ hs2 (by linarith) (by linarith)]
  have h := eq_of_real_interval hDo hg₁ hg₂ hJD (le_max_left _ _) hc₀Q le_rfl heq ht₁ ht₂
  rw [hL t ht₁ ht₂, hR t ht₁ ht₂, hu₂, crossingMultiplier3_ofReal hγ] at h
  exact_mod_cast h

/-- **Step B**: the crossing on the two-pole slice, `C̄(Q - η - γ/2, x, 2/γ + η) =
T(Q - η, x, 2/γ + η) C̄(Q - η, x + γ/2, 2/γ + η)` for `2η < x < 2/γ`. -/
theorem unitVolume_crossing_slice {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (M : Ω → MeasureTheory.Measure ℂ) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2)
    (hCross : ∀ μ α' ε α : ℝ, 0 < μ → γ / 2 < ε → ε < 2 / γ → α < Q γ → α' < Q γ →
      2 * Q γ < α + α' + ε - γ / 2 →
      unitVolumeStructureConstant P M γ (α' - γ / 2) ε α =
        gammaHalfUnitCrossingMultiplier γ μ α' ε α *
          unitVolumeStructureConstant P M γ α' (ε + γ / 2) α)
    {V₃ : Set (Fin 3 → ℂ)} (hV₃ : IsOpen V₃)
    (hV₃mem : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) →
      complexifyNCharges α ∈ V₃)
    {f₃ : (Fin 3 → ℂ) → ℂ} (hf₃ : DifferentiableOn ℂ f₃ V₃)
    (hf₃eq : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) →
      f₃ (complexifyNCharges α) = (unitVolumeStructureConstant P M γ (α 0) (α 1) (α 2) : ℂ))
    {η : ℝ} (hη : 0 < η) (hη4 : η < γ / 4) (hηγ : η < 2 / γ - γ / 2)
    {x : ℝ} (hx₁ : 2 * η < x) (hx₂ : x < 2 / γ) :
    unitVolumeStructureConstant P M γ (Q γ - η - γ / 2) x (2 / γ + η) =
      crossingMultiplier3Real γ (Q γ - η) x (2 / γ + η) *
        unitVolumeStructureConstant P M γ (Q γ - η) (x + γ / 2) (2 / γ + η) := by
  obtain ⟨hQ, hQ2, hγh, h42, h2⟩ := slice_facts hγ hγ2
  have hη2 : η < γ / 2 := by linarith
  set u₁ : ℂ := ((Q γ - η - γ / 2 : ℝ) : ℂ) with hu₁
  set u₂ : ℂ := ((Q γ - η : ℝ) : ℂ) with hu₂
  set w : ℂ := ((2 / γ + η : ℝ) : ℂ) with hw
  set D : Set ℂ := {z | 2 * η < z.re ∧ z.re < 2 / γ} ∩ tripleSecond u₁ 0 w ⁻¹' V₃ ∩
    tripleSecond u₂ ((γ / 2 : ℝ) : ℂ) w ⁻¹' V₃ with hD
  have hDo : IsOpen D :=
    (((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).inter
      (hV₃.preimage (differentiable_tripleSecond _ _ _).continuous)).inter
      (hV₃.preimage (differentiable_tripleSecond _ _ _).continuous)
  have hL : ∀ s : ℝ, 2 * η < s → s < 2 / γ → f₃ (tripleSecond u₁ 0 w (s : ℂ)) =
      (unitVolumeStructureConstant P M γ (Q γ - η - γ / 2) s (2 / γ + η) : ℂ) :=
    fun s h1 h2 => by
      rw [hu₁, hw, ← Complex.ofReal_zero, tripleSecond_ofReal, add_zero]
      exact hf₃eq ![Q γ - η - γ / 2, s, 2 / γ + η]
        (extendedSeiberg3_sliceB_left hγ hγ2 hη hη2 h1 h2)
  have hR : ∀ s : ℝ, 2 * η < s → s < 2 / γ → f₃ (tripleSecond u₂ ((γ / 2 : ℝ) : ℂ) w (s : ℂ)) =
      (unitVolumeStructureConstant P M γ (Q γ - η) (s + γ / 2) (2 / γ + η) : ℂ) :=
    fun s h1 h2 => by
      rw [hu₂, hw, tripleSecond_ofReal]
      exact hf₃eq ![Q γ - η, s + γ / 2, 2 / γ + η]
        (extendedSeiberg3_sliceB_right hγ hγ2 hη hη4 (by linarith) h2)
  have hJD : ∀ s : ℝ, 2 * η < s → s < 2 / γ → (s : ℂ) ∈ D := fun s h1 h2 => by
    refine ⟨⟨⟨by rw [Complex.ofReal_re]; exact h1, by rw [Complex.ofReal_re]; exact h2⟩, ?_⟩, ?_⟩
    · change tripleSecond u₁ 0 w (s : ℂ) ∈ V₃
      rw [hu₁, hw, ← Complex.ofReal_zero, tripleSecond_ofReal, add_zero]
      exact hV₃mem ![Q γ - η - γ / 2, s, 2 / γ + η]
        (extendedSeiberg3_sliceB_left hγ hγ2 hη hη2 h1 h2)
    · change tripleSecond u₂ ((γ / 2 : ℝ) : ℂ) w (s : ℂ) ∈ V₃
      rw [hu₂, hw, tripleSecond_ofReal]
      exact hV₃mem ![Q γ - η, s + γ / 2, 2 / γ + η]
        (extendedSeiberg3_sliceB_right hγ hγ2 hη hη4 (by linarith) h2)
  have hT : DifferentiableOn ℂ (fun z => crossingMultiplier3 γ u₂ z w) D := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    obtain ⟨⟨⟨hz1, hz2⟩, -⟩, -⟩ := hz
    refine differentiableAt_crossingMultiplier3 (φ₁ := fun _ => u₂) (φ₂ := id)
      (φ₃ := fun _ => w) (differentiableAt_const _) differentiableAt_id (differentiableAt_const _)
      ?_ ?_ ?_ ?_
    · rw [crossA3_add_one_re, hu₂, hw, Complex.ofReal_re, Complex.ofReal_re]
      have : 0 < γ / 4 * (Q γ - η + (id z).re + (2 / γ + η) - Q γ - γ) + 1 / 2 := by
        have h1 := quarter_mul_lt (u := -(2 / γ)) (v := Q γ - η + (id z).re + (2 / γ + η) - Q γ - γ)
          hγ (by simp only [id]; linarith)
        have h2' : γ / 4 * -(2 / γ) = -(1 / 2) := by field_simp; ring
        linarith
      exact this
    · rw [crossB3_re, hu₂, hw, Complex.ofReal_re, Complex.ofReal_re]
      have : 0 < γ / 4 * (Q γ - η + (id z).re - (2 / γ + η) - Q γ + 2 / γ) := mul_pos
        (by positivity) (by simp only [id]; linarith)
      have h2' : γ / 4 * (Q γ - η + (id z).re - (2 / γ + η) - Q γ) + 1 / 2 =
          γ / 4 * (Q γ - η + (id z).re - (2 / γ + η) - Q γ + 2 / γ) := by field_simp; ring
      rw [h2']
      exact this
    · rw [one_sub_crossC3_re, hu₂, Complex.ofReal_re]
      exact mul_pos (by positivity) (by linarith)
    · rw [one_sub_mul_half_re]
      have : γ * (id z).re < γ * (2 / γ) := mul_lt_mul_of_pos_left hz2 hγ
      rw [mul_div_cancel₀ _ hγ.ne'] at this
      linarith
  have hg₁ : DifferentiableOn ℂ (fun z => f₃ (tripleSecond u₁ 0 w z)) D :=
    hf₃.comp (differentiable_tripleSecond _ _ _).differentiableOn fun _ hz => hz.1.2
  have hg₂ : DifferentiableOn ℂ (fun z => crossingMultiplier3 γ u₂ z w *
      f₃ (tripleSecond u₂ ((γ / 2 : ℝ) : ℂ) w z)) D :=
    hT.mul (hf₃.comp (differentiable_tripleSecond _ _ _).differentiableOn fun _ hz => hz.2)
  -- agreement from step A on `(γ/2 + η, 2/γ)`
  have heq : ∀ s : ℝ, γ / 2 + η < s → s < 2 / γ → f₃ (tripleSecond u₁ 0 w (s : ℂ)) =
      crossingMultiplier3 γ u₂ s w * f₃ (tripleSecond u₂ ((γ / 2 : ℝ) : ℂ) w (s : ℂ)) := by
    intro s hs1 hs2
    have hs3 : 2 * η < s := by linarith
    rw [hL s hs3 hs2, hR s hs3 hs2, hu₂, hw, crossingMultiplier3_ofReal hγ, ← Complex.ofReal_mul,
      unitVolume_crossing_sliceA P M hγ hγ2 hCross hV₃ hV₃mem hf₃ hf₃eq hη hs1 hs2
        (t := 2 / γ + η) (by linarith) (by rw [hQ]; linarith)]
  have h := eq_of_real_interval hDo hg₁ hg₂ hJD (by linarith) (show γ / 2 + η < 2 / γ by linarith)
    le_rfl heq hx₁ hx₂
  rw [hL x hx₁ hx₂, hR x hx₁ hx₂, hu₂, hw, crossingMultiplier3_ofReal hγ] at h
  exact_mod_cast h

end DOZZ.Proofs

end
