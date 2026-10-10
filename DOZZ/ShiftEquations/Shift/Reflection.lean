/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Shift.Continuation3
public import DOZZ.Statements.Correlations.BridgeMultiplicity
public import DOZZ.Statements.Brownian.ReflectionBarR
public import DOZZ.Statements.Brownian.IsSourceLateralProjection
public import DOZZ.Statements.Brownian.IsReflectionData
public import DOZZ.Statements.Defs.IsEquatorGFF
public import DOZZ.Statements.Defs.IsGMCOf
import DOZZ.Correlations.Symmetry.ReflectionMomentSwap
import DOZZ.Correlations.Symmetry.InversionSwap
import DOZZ.Brownian.Reflection.WitnessIndependence
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The unit-volume reflection relation near `Q`

Let `α' = Q - η`, `α = 2/γ + η` with an admissible two-pole window. The two-pole expansion
`F = R₁/(z - 2η) + R₂/(z + 2η) + r` of `x ↦ C̄(α' - γ/2, x, α)` and the continued crossing
`C̄(α' - γ/2, x, α) = T(x) C̄(α', x + γ/2, α)` on `(2η, 1/γ)` give, after multiplying by `z - 2η`,
the identity `R₁ + (z - 2η) R₂/(z + 2η) + (z - 2η) r = T̃(z) C̄ₕ(α', z + γ/2, α)` on `(-2η, 1/γ)`,
with `T̃ = (z - 2η) T` the regularized multiplier. Multiplying by `x + 2η` and letting `x ↓ -2η`,
the residue bridge (`α₂ = 2/γ + η < α₃ = Q - η`) gives `-4η R₂ = T̃(-2η) (4η/γ) R̄(Q - η)`, i.e.
`(η + γ/2) R̄(Q - η - γ/2) = η T(Q - η, -2η, 2/γ + η) R̄(Q - η)` ([KRV, §10.2]).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace DOZZ.Proofs

/-- **The identity theorem along a real interval, from frequent agreement.** -/
theorem eq_of_real_interval_of_frequently {D : Set ℂ} (hD : IsOpen D) {g₁ g₂ : ℂ → ℂ}
    (hg₁ : DifferentiableOn ℂ g₁ D) (hg₂ : DifferentiableOn ℂ g₂ D) {a b x₀ : ℝ}
    (hJD : ∀ t : ℝ, a < t → t < b → (t : ℂ) ∈ D) (hx₀a : a < x₀) (hx₀b : x₀ < b)
    (hfreq : ∃ᶠ z in 𝓝[≠] (x₀ : ℂ), g₁ z = g₂ z) {t : ℝ} (ht₁ : a < t) (ht₂ : t < b) :
    g₁ t = g₂ t := by
  have hx₀D : (x₀ : ℂ) ∈ D := hJD x₀ hx₀a hx₀b
  set U := connectedComponentIn D (x₀ : ℂ) with hU
  have hUo : IsOpen U := hD.connectedComponentIn
  have hUD : U ⊆ D := connectedComponentIn_subset D _
  have hEq : EqOn g₁ g₂ U :=
    ((hg₁.mono hUD).analyticOnNhd hUo).eqOn_of_preconnected_of_frequently_eq
      ((hg₂.mono hUD).analyticOnNhd hUo) isPreconnected_connectedComponentIn
      (mem_connectedComponentIn hx₀D) hfreq
  have hJU : (fun s : ℝ => (s : ℂ)) '' Ioo a b ⊆ U :=
    (isPreconnected_Ioo.image _ Complex.continuous_ofReal.continuousOn).subset_connectedComponentIn
      ⟨x₀, ⟨hx₀a, hx₀b⟩, rfl⟩ (image_subset_iff.mpr fun s hs => hJD s hs.1 hs.2)
  exact hEq (hJU ⟨t, ⟨ht₁, ht₂⟩, rfl⟩)

/-- Real points approach a real point from the punctured complex neighborhood. -/
theorem tendsto_ofReal_nhdsNE_slice (x₀ : ℝ) :
    Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[≠] x₀) (𝓝[≠] (x₀ : ℂ)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun s hs => by simpa [Complex.ofReal_inj] using hs)

/-- On the slice, the Gauss parameter `B` is `(γ/4)(z - 2η)`. -/
theorem crossB3_slice {γ η : ℝ} (hγ : 0 < γ) (z : ℂ) :
    crossB3 γ ((Q γ - η : ℝ) : ℂ) z ((2 / γ + η : ℝ) : ℂ) = (γ / 4 : ℂ) * (z - 2 * η) := by
  unfold crossB3
  have hγ0 : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ.ne'
  push_cast
  field_simp
  ring

/-- On the slice, off `z = 2η`, the regularized multiplier is `(z - 2η) T`. -/
theorem crossingMultiplier3Reg_slice {γ η : ℝ} (hγ : 0 < γ) {z : ℂ} (hz : z ≠ 2 * η) :
    crossingMultiplier3Reg γ ((Q γ - η : ℝ) : ℂ) z ((2 / γ + η : ℝ) : ℂ) =
      (z - 2 * η) * crossingMultiplier3 γ ((Q γ - η : ℝ) : ℂ) z ((2 / γ + η : ℝ) : ℂ) := by
  have hγ0 : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ.ne'
  have hB : crossB3 γ ((Q γ - η : ℝ) : ℂ) z ((2 / γ + η : ℝ) : ℂ) ≠ 0 := by
    rw [crossB3_slice hγ]
    exact mul_ne_zero (div_ne_zero hγ0 (by norm_num)) (sub_ne_zero.mpr hz)
  rw [crossingMultiplier3Reg_eq_mul hB, crossB3_slice hγ]
  field_simp

/-- **The regularized multiplier on the slice is holomorphic on `-2η - δ < Re z < 2/γ`.** -/
theorem differentiableAt_crossingMultiplier3Reg_slice {γ η δ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hη : 0 < η) (hδ1 : 2 * η + δ < 4 / γ - γ) (hδ2 : 4 * η + δ < γ) {z : ℂ}
    (hz1 : -(2 * η) - δ < z.re) (hz2 : z.re < 2 / γ) :
    DifferentiableAt ℂ (fun w => crossingMultiplier3Reg γ ((Q γ - η : ℝ) : ℂ) w
      ((2 / γ + η : ℝ) : ℂ)) z := by
  obtain ⟨hQ, hQ2, hγh, h42, h2⟩ := slice_facts hγ hγ2
  refine differentiableAt_crossingMultiplier3Reg (φ₁ := fun _ => ((Q γ - η : ℝ) : ℂ))
    (φ₂ := id) (φ₃ := fun _ => ((2 / γ + η : ℝ) : ℂ)) (differentiableAt_const _)
    differentiableAt_id (differentiableAt_const _) ?_ ?_ ?_ ?_
  · rw [crossA3_add_one_re, Complex.ofReal_re, Complex.ofReal_re]
    have h1 := quarter_mul_lt (u := -(2 / γ)) (v := Q γ - η + (id z).re + (2 / γ + η) - Q γ - γ)
      hγ (by simp only [id]; linarith)
    have h2' : γ / 4 * -(2 / γ) = -(1 / 2) := by field_simp; ring
    linarith
  · have hB := crossB3_slice (η := η) hγ (id z)
    have hre : (crossB3 γ ((Q γ - η : ℝ) : ℂ) (id z) ((2 / γ + η : ℝ) : ℂ) + 1).re =
        γ / 4 * (z.re - 2 * η) + 1 := by
      rw [hB]
      simp [Complex.mul_re]
    rw [hre]
    have h1 := quarter_mul_lt (u := -(4 / γ)) (v := z.re - 2 * η) hγ (by linarith)
    have h2' : γ / 4 * -(4 / γ) = -1 := by field_simp
    linarith
  · rw [one_sub_crossC3_re, Complex.ofReal_re]
    exact mul_pos (by positivity) (by linarith)
  · rw [one_sub_mul_half_re]
    have : γ * (id z).re < γ * (2 / γ) := mul_lt_mul_of_pos_left hz2 hγ
    rw [mul_div_cancel₀ _ hγ.ne'] at this
    linarith

/-- **Agreement of the two regularized sides on `(-2η, 1/γ)`.** -/
theorem slice_regularized_agreement {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
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
    {η δ : ℝ} (hη : 0 < η) (hη4 : η < γ / 4) (hηγ : η < 2 / γ - γ / 2)
    (hη2γ : η < 1 / (2 * γ)) (hδ : 0 < δ) (hδ1 : 2 * η + δ < 4 / γ - γ)
    (hδ2 : 4 * η + δ < γ)
    {V : Set ℂ} (hV : IsOpen V) (hVx : ∀ x : ℝ, -2 * η - δ < x ∧ x < 1 / γ → (x : ℂ) ∈ V)
    {F r : ℂ → ℂ} (hr : DifferentiableOn ℂ r V)
    (hFx : ∀ x : ℝ, 2 * η < x ∧ x < 1 / γ →
      F (x : ℂ) = (unitVolumeStructureConstant P M γ (Q γ - η - γ / 2) x (2 / γ + η) : ℂ))
    {R₁ R₂ : ℂ}
    (hFexp : ∀ᶠ z in codiscrete ℂ, z ∈ V → F z = R₁ / (z - 2 * η) + R₂ / (z + 2 * η) + r z)
    {x : ℝ} (hx₁ : -(2 * η) < x) (hx₂ : x < 1 / γ) :
    R₁ + ((x : ℂ) - 2 * η) * R₂ / ((x : ℂ) + 2 * η) + ((x : ℂ) - 2 * η) * r x =
      crossingMultiplier3Reg γ ((Q γ - η : ℝ) : ℂ) x ((2 / γ + η : ℝ) : ℂ) *
        f₃ (tripleSecond ((Q γ - η : ℝ) : ℂ) ((γ / 2 : ℝ) : ℂ) ((2 / γ + η : ℝ) : ℂ) x) := by
  obtain ⟨hQ, hQ2, hγh, h42, h2⟩ := slice_facts hγ hγ2
  have h1γ : 1 / γ < 2 / γ := by gcongr; norm_num
  have h12 : 2 * η < 1 / γ := by
    have : 1 / γ = 2 * (1 / (2 * γ)) := by field_simp
    linarith
  set u₂ : ℂ := ((Q γ - η : ℝ) : ℂ) with hu₂
  set w : ℂ := ((2 / γ + η : ℝ) : ℂ) with hw
  set D : Set ℂ := (V ∩ {z | z + 2 * η ≠ 0}) ∩
    ({z | -(2 * η) - δ < z.re ∧ z.re < 2 / γ} ∩ tripleSecond u₂ ((γ / 2 : ℝ) : ℂ) w ⁻¹' V₃)
    with hD
  have hDo : IsOpen D :=
    (hV.inter (isOpen_ne_fun (by fun_prop) continuous_const)).inter
      (((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).inter
        (hV₃.preimage (differentiable_tripleSecond _ _ _).continuous))
  have hJD : ∀ t : ℝ, -(2 * η) < t → t < 1 / γ → (t : ℂ) ∈ D := fun t h1 h2' => by
    refine ⟨⟨hVx t ⟨by linarith, h2'⟩, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · change (t : ℂ) + 2 * η ≠ 0
      exact_mod_cast (show t + 2 * η ≠ 0 by intro h; linarith)
    · rw [Complex.ofReal_re]
      linarith
    · rw [Complex.ofReal_re]
      linarith
    · change tripleSecond u₂ ((γ / 2 : ℝ) : ℂ) w (t : ℂ) ∈ V₃
      rw [hu₂, hw, tripleSecond_ofReal]
      exact hV₃mem ![Q γ - η, t + γ / 2, 2 / γ + η]
        (extendedSeiberg3_sliceB_right hγ hγ2 hη hη4 h1 (by linarith))
  have hg₁ : DifferentiableOn ℂ (fun z => R₁ + (z - 2 * η) * R₂ / (z + 2 * η) +
      (z - 2 * η) * r z) D := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have hrz : DifferentiableAt ℂ r z := hr.differentiableAt (hV.mem_nhds hz.1.1)
    have hz0 : z + 2 * η ≠ 0 := hz.1.2
    have h1 : DifferentiableAt ℂ (fun z : ℂ => z - 2 * (η : ℂ)) z := by fun_prop
    have h2 : DifferentiableAt ℂ (fun z : ℂ => z + 2 * (η : ℂ)) z := by fun_prop
    exact ((differentiableAt_const R₁).add ((h1.mul_const R₂).div h2 hz0)).add (h1.mul hrz)
  have hg₂ : DifferentiableOn ℂ (fun z => crossingMultiplier3Reg γ u₂ z w *
      f₃ (tripleSecond u₂ ((γ / 2 : ℝ) : ℂ) w z)) D := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    obtain ⟨-, ⟨⟨hz1, hz2⟩, hz3⟩⟩ := hz
    exact (differentiableAt_crossingMultiplier3Reg_slice hγ hγ2 hη hδ1 hδ2 hz1 hz2).mul
      ((hf₃.differentiableAt (hV₃.mem_nhds hz3)).comp z
        ((differentiable_tripleSecond _ _ _) z))
  -- frequent agreement near a point of `(2η, 1/γ)`
  set x₀ : ℝ := (2 * η + 1 / γ) / 2 with hx₀
  have hx₀1 : 2 * η < x₀ := by rw [hx₀]; linarith
  have hx₀2 : x₀ < 1 / γ := by rw [hx₀]; linarith
  have hE : ∀ᶠ t : ℝ in 𝓝[≠] x₀, ((t : ℂ) ∈ V → F t = R₁ / ((t : ℂ) - 2 * η) +
      R₂ / ((t : ℂ) + 2 * η) + r t) :=
    (tendsto_ofReal_nhdsNE_slice x₀).eventually
      ((eventually_codiscrete_iff_forall_eventually_nhdsNE.mp hFexp) (x₀ : ℂ))
  have hI : ∀ᶠ t : ℝ in 𝓝[≠] x₀, 2 * η < t ∧ t < 1 / γ :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_of_mem (Ioo_mem_nhds hx₀1 hx₀2)
      fun t ht => ht)
  have hev : ∀ᶠ t : ℝ in 𝓝[≠] x₀, R₁ + ((t : ℂ) - 2 * η) * R₂ / ((t : ℂ) + 2 * η) +
      ((t : ℂ) - 2 * η) * r t = crossingMultiplier3Reg γ u₂ t w *
        f₃ (tripleSecond u₂ ((γ / 2 : ℝ) : ℂ) w t) := by
    filter_upwards [hE, hI] with t hEt hIt
    have ht2 : t < 2 / γ := by linarith [hIt.2]
    have htV : (t : ℂ) ∈ V := hVx t ⟨by linarith [hIt.1], hIt.2⟩
    have hne : (t : ℂ) - 2 * η ≠ 0 := by
      exact_mod_cast (show t - 2 * η ≠ 0 by intro h; linarith [hIt.1])
    have hne' : (t : ℂ) + 2 * η ≠ 0 := by
      exact_mod_cast (show t + 2 * η ≠ 0 by intro h; linarith [hIt.1])
    have hne'' : (t : ℂ) ≠ 2 * η := fun h => hne (by rw [h]; ring)
    have hcr := unitVolume_crossing_slice P M hγ hγ2 hCross hV₃ hV₃mem hf₃ hf₃eq hη hη4 hηγ
      hIt.1 ht2
    have hR : f₃ (tripleSecond u₂ ((γ / 2 : ℝ) : ℂ) w t) =
        (unitVolumeStructureConstant P M γ (Q γ - η) (t + γ / 2) (2 / γ + η) : ℂ) := by
      rw [hu₂, hw, tripleSecond_ofReal]
      exact hf₃eq ![Q γ - η, t + γ / 2, 2 / γ + η]
        (extendedSeiberg3_sliceB_right hγ hγ2 hη hη4 (by linarith [hIt.1]) ht2)
    calc R₁ + ((t : ℂ) - 2 * η) * R₂ / ((t : ℂ) + 2 * η) + ((t : ℂ) - 2 * η) * r t
        = ((t : ℂ) - 2 * η) * (R₁ / ((t : ℂ) - 2 * η) + R₂ / ((t : ℂ) + 2 * η) + r t) := by
          field_simp
      _ = ((t : ℂ) - 2 * η) * F t := by rw [hEt htV]
      _ = ((t : ℂ) - 2 * η) * (crossingMultiplier3 γ u₂ t w *
            (unitVolumeStructureConstant P M γ (Q γ - η) (t + γ / 2) (2 / γ + η) : ℂ)) := by
          rw [hFx t hIt, hcr, Complex.ofReal_mul, hu₂, hw, crossingMultiplier3_ofReal hγ]
      _ = _ := by
          rw [hR, crossingMultiplier3Reg_slice hγ hne'']
          ring
  exact eq_of_real_interval_of_frequently hDo hg₁ hg₂ hJD (by linarith) (by linarith)
    ((tendsto_ofReal_nhdsNE_slice x₀).frequently hev.frequently) hx₁ hx₂

/-- **The second residue of the two-pole expansion from the residue bridge**:
`R₂ = (4η/γ) T(Q - η, -2η, 2/γ + η) R̄(Q - η)`. -/
theorem secondResidue_eq_of_bridge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (M : Ω → Measure ℂ) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hCross : ∀ μ α' ε α : ℝ, 0 < μ → γ / 2 < ε → ε < 2 / γ → α < Q γ → α' < Q γ →
      2 * Q γ < α + α' + ε - γ / 2 →
      unitVolumeStructureConstant P M γ (α' - γ / 2) ε α =
        gammaHalfUnitCrossingMultiplier γ μ α' ε α *
          unitVolumeStructureConstant P M γ α' (ε + γ / 2) α)
    (hBridge : ∀ α2 α3 : ℝ, 0 < α2 ∧ α2 ≤ α3 ∧ γ / 2 < α3 ∧ α3 < Q γ →
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧ IsReflectionData P γ α3 (B α3) Z ∧
        Tendsto (fun ε : ℝ => ε * unitVolumeStructureConstant P M γ
            (α3 - α2 + ε) α2 α3) (𝓝[>] 0)
          (𝓝 (bridgeMultiplicity α2 α3 * reflectionExponent γ α3 *
            reflectionBarR P γ α3 (B α3) Z)))
    {V₃ : Set (Fin 3 → ℂ)} (hV₃ : IsOpen V₃)
    (hV₃mem : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) →
      complexifyNCharges α ∈ V₃)
    {f₃ : (Fin 3 → ℂ) → ℂ} (hf₃ : DifferentiableOn ℂ f₃ V₃)
    (hf₃eq : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) →
      f₃ (complexifyNCharges α) = (unitVolumeStructureConstant P M γ (α 0) (α 1) (α 2) : ℂ))
    {η δ : ℝ} (hη : 0 < η) (hη4 : η < γ / 4) (hηγ : η < 2 / γ - γ / 2)
    (hη2γ : η < 1 / (2 * γ)) (hδ : 0 < δ) (hδ1 : 2 * η + δ < 4 / γ - γ)
    (hδ2 : 4 * η + δ < γ)
    {V : Set ℂ} (hV : IsOpen V) (hVx : ∀ x : ℝ, -2 * η - δ < x ∧ x < 1 / γ → (x : ℂ) ∈ V)
    {F r : ℂ → ℂ} (hr : DifferentiableOn ℂ r V)
    (hFx : ∀ x : ℝ, 2 * η < x ∧ x < 1 / γ →
      F (x : ℂ) = (unitVolumeStructureConstant P M γ (Q γ - η - γ / 2) x (2 / γ + η) : ℂ))
    {R₁ R₂ : ℂ}
    (hFexp : ∀ᶠ z in codiscrete ℂ, z ∈ V → F z = R₁ / (z - 2 * η) + R₂ / (z + 2 * η) + r z)
    (B₂ : Ω → BrownianPath × BrownianPath) (Z₂ : Ω → Measure ℝ)
    (h₂ : IsReflectionData P γ (Q γ - η) B₂ Z₂) :
    R₂ = ((4 * η / γ * crossingMultiplier3Real γ (Q γ - η) (-(2 * η)) (2 / γ + η) *
      reflectionBarR P γ (Q γ - η) B₂ Z₂ : ℝ) : ℂ) := by
  obtain ⟨hQ, hQ2, hγh, h42, h2⟩ := slice_facts hγ hγ2
  have h1γ : 1 / γ < 2 / γ := by gcongr; norm_num
  have h12 : 2 * η < 1 / γ := by
    have : 1 / γ = 2 * (1 / (2 * γ)) := by field_simp
    linarith
  set u₂ : ℂ := ((Q γ - η : ℝ) : ℂ) with hu₂
  set w : ℂ := ((2 / γ + η : ℝ) : ℂ) with hw
  -- the residue bridge at `(2/γ + η, Q - η)`
  obtain ⟨B', Z', -, hRD', hLim⟩ := hBridge (2 / γ + η) (Q γ - η)
    ⟨by positivity, by rw [hQ]; linarith, by rw [hQ]; linarith, by linarith⟩
  have hmult : bridgeMultiplicity (2 / γ + η) (Q γ - η) = 2 := by
    have hne : 2 / γ + η ≠ Q γ - η := by rw [hQ]; intro h; linarith
    simp only [bridgeMultiplicity, hne, ↓reduceIte]
  have hp : reflectionExponent γ (Q γ - η) = 2 * η / γ := by
    unfold reflectionExponent
    ring
  set Rb := reflectionBarR P γ (Q γ - η) (B' (Q γ - η)) Z' with hRb
  have hshift : Tendsto (fun x : ℝ => x + 2 * η) (𝓝[>] (-(2 * η))) (𝓝[>] 0) := by
    have h := (by fun_prop : Continuous fun x : ℝ => x + 2 * η).tendsto (-(2 * η))
    rw [neg_add_cancel] at h
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (h.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun x hx => by
        change 0 < x + 2 * η
        have : -(2 * η) < x := hx
        linarith)
  have hCb : Tendsto (fun x : ℝ => (x + 2 * η) *
      unitVolumeStructureConstant P M γ (Q γ - η) (x + γ / 2) (2 / γ + η))
      (𝓝[>] (-(2 * η))) (𝓝 (4 * η / γ * Rb)) := by
    have h := hLim.comp hshift
    have hval : (2 : ℝ) * (2 * η / γ) * Rb = 4 * η / γ * Rb := by ring
    rw [hmult, hp, hval] at h
    refine h.congr fun x => ?_
    simp only [Function.comp_apply]
    rw [show Q γ - η - (2 / γ + η) + (x + 2 * η) = x + γ / 2 by rw [hQ]; ring,
      unitVolumeStructureConstant_swap13 P X M γ (Q γ - η) (x + γ / 2) (2 / γ + η) hγ hγ2 hX hM,
      unitVolumeStructureConstant_swap12 P X M γ (2 / γ + η) (x + γ / 2) (Q γ - η) hγ hγ2 hX hM]
  -- the multiplier side
  have hRegc : ContinuousAt (fun z => crossingMultiplier3Reg γ u₂ z w)
      ((-(2 * η) : ℝ) : ℂ) :=
    (differentiableAt_crossingMultiplier3Reg_slice hγ hγ2 hη hδ1 hδ2
      (by rw [Complex.ofReal_re]; linarith) (by rw [Complex.ofReal_re]; linarith)).continuousAt
  have hRside : Tendsto (fun x : ℝ => ((x : ℂ) + 2 * η) * (crossingMultiplier3Reg γ u₂ x w *
      f₃ (tripleSecond u₂ ((γ / 2 : ℝ) : ℂ) w x))) (𝓝[>] (-(2 * η)))
      (𝓝 (crossingMultiplier3Reg γ u₂ ((-(2 * η) : ℝ) : ℂ) w * ((4 * η / γ * Rb : ℝ) : ℂ))) := by
    have hReg : Tendsto (fun x : ℝ => crossingMultiplier3Reg γ u₂ (x : ℂ) w) (𝓝[>] (-(2 * η)))
        (𝓝 (crossingMultiplier3Reg γ u₂ ((-(2 * η) : ℝ) : ℂ) w)) :=
      (hRegc.tendsto.comp (Complex.continuous_ofReal.tendsto _)).mono_left nhdsWithin_le_nhds
    refine (hReg.mul ((Complex.continuous_ofReal.tendsto _).comp hCb)).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show -(2 * η) < 2 / γ by linarith)] with x hx
    have hR : f₃ (tripleSecond u₂ ((γ / 2 : ℝ) : ℂ) w x) =
        (unitVolumeStructureConstant P M γ (Q γ - η) (x + γ / 2) (2 / γ + η) : ℂ) := by
      rw [hu₂, hw, tripleSecond_ofReal]
      exact hf₃eq ![Q γ - η, x + γ / 2, 2 / γ + η]
        (extendedSeiberg3_sliceB_right hγ hγ2 hη hη4 hx.1 hx.2)
    simp only [Function.comp_apply]
    rw [hR]
    push_cast
    ring
  -- the expansion side
  have hrc : ContinuousAt r ((-(2 * η) : ℝ) : ℂ) :=
    (hr.differentiableAt (hV.mem_nhds (hVx _ ⟨by linarith, by linarith⟩))).continuousAt
  have hLside : Tendsto (fun x : ℝ => ((x : ℂ) + 2 * η) * (R₁ + ((x : ℂ) - 2 * η) * R₂ /
      ((x : ℂ) + 2 * η) + ((x : ℂ) - 2 * η) * r x)) (𝓝[>] (-(2 * η))) (𝓝 (-(4 * η) * R₂)) := by
    have hG : ContinuousAt (fun x : ℝ => ((x : ℂ) + 2 * η) * R₁ + ((x : ℂ) - 2 * η) * R₂ +
        ((x : ℂ) + 2 * η) * ((x : ℂ) - 2 * η) * r x) (-(2 * η)) := by
      have hrx : ContinuousAt (fun x : ℝ => r x) (-(2 * η)) :=
        hrc.comp Complex.continuous_ofReal.continuousAt
      have hx : ContinuousAt (fun x : ℝ => (x : ℂ)) (-(2 * η)) :=
        Complex.continuous_ofReal.continuousAt
      exact (((hx.add continuousAt_const).mul continuousAt_const).add
        ((hx.sub continuousAt_const).mul continuousAt_const)).add
        (((hx.add continuousAt_const).mul (hx.sub continuousAt_const)).mul hrx)
    have hval : ((((-(2 * η) : ℝ) : ℂ) + 2 * η) * R₁ + (((-(2 * η) : ℝ) : ℂ) - 2 * η) * R₂ +
        (((-(2 * η) : ℝ) : ℂ) + 2 * η) * (((-(2 * η) : ℝ) : ℂ) - 2 * η) *
          r ((-(2 * η) : ℝ) : ℂ)) = -(4 * η) * R₂ := by
      push_cast
      ring
    have h := hG.tendsto
    rw [hval] at h
    refine (h.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : -(2 * η) < x := hx
    have hne : (x : ℂ) + 2 * η ≠ 0 := by
      exact_mod_cast (show x + 2 * η ≠ 0 by intro h; linarith)
    field_simp
  -- the two sides agree near `-2η`
  have hagree : ∀ᶠ x : ℝ in 𝓝[>] (-(2 * η)),
      ((x : ℂ) + 2 * η) * (R₁ + ((x : ℂ) - 2 * η) * R₂ / ((x : ℂ) + 2 * η) +
        ((x : ℂ) - 2 * η) * r x) =
      ((x : ℂ) + 2 * η) * (crossingMultiplier3Reg γ u₂ x w *
        f₃ (tripleSecond u₂ ((γ / 2 : ℝ) : ℂ) w x)) := by
    filter_upwards [Ioo_mem_nhdsGT (show -(2 * η) < 1 / γ by linarith)] with x hx
    rw [slice_regularized_agreement P M hγ hγ2 hCross hV₃ hV₃mem hf₃ hf₃eq hη hη4 hηγ hη2γ hδ
      hδ1 hδ2 hV hVx hr hFx hFexp hx.1 hx.2]
  have huniq := tendsto_nhds_unique (hLside.congr' hagree) hRside
  -- solve for `R₂`
  have hz : ((-(2 * η) : ℝ) : ℂ) ≠ 2 * η := by
    push_cast
    intro h
    have : (4 * η : ℂ) = 0 := by linear_combination -h
    exact (show (4 * η : ℝ) ≠ 0 by positivity) (by exact_mod_cast this)
  rw [crossingMultiplier3Reg_slice hγ hz, crossingMultiplier3_ofReal hγ] at huniq
  have h4η : (-(4 * η) : ℂ) ≠ 0 := by
    have : (4 * η : ℝ) ≠ 0 := by positivity
    exact neg_ne_zero.mpr (by exact_mod_cast this)
  have hR2 : R₂ = (crossingMultiplier3Real γ (Q γ - η) (-(2 * η)) (2 / γ + η) : ℂ) *
      ((4 * η / γ * Rb : ℝ) : ℂ) := by
    apply mul_left_cancel₀ h4η
    rw [huniq]
    push_cast
    ring
  rw [hR2, reflectionBarR_eq_of_isReflectionData P P γ (Q γ - η) B₂ Z₂ (B' (Q γ - η)) Z' h₂ hRD',
    ← hRb]
  push_cast
  ring

end DOZZ.Proofs

end
