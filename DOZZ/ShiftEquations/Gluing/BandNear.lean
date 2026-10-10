/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Gluing.BandLine
public import DOZZ.ShiftEquations.Gluing.Meromorphy
public import DOZZ.Statements.Defs.ExtendedSeiberg3
import DOZZ.ShiftEquations.Shift.ShiftGluing
import DOZZ.ShiftEquations.Shift.Reflection
public import DOZZ.ShiftEquations.Residual.Calibration
import DOZZ.Complex.Basic

/-!
# The γ/2 shifts at exact real points, for spectators near `Q`

For spectators `b, c` near `Q`, the first structure shift
(`DOZZ.structureConstant_first_shift_strip`) and the reflected shift
(`DOZZ.structureConstant_reflected_shift_and_gluing`) are identities between meromorphic germs on a
strip. Their functions agree with the physical structure constant `C(·, b, c)` on `(2η, Q)`, hence
(identity theorem) with its continuation `C_f(·, b, c)` through the holomorphic unit-volume
extension `f` (`DOZZ.unitVolumeStructureConstant_holomorphic_near_extended_domain`). Where the shift
coefficient is analytic, continuity turns the germ identities into exact identities at real points:
`C(α) = -𝒜(α - γ/2) C(α - γ)/(πμ)` for `α < Q` and `R(α) C(2Q - α) = -𝒜(α - γ/2) C(α - γ)/(πμ)` for
`α > Q` near `Q`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- Punctured germs are transported by the reflection `w ↦ c - w`. -/
theorem eventually_comp_reflect {p : ℂ → Prop} {z : ℂ} (c : ℂ)
    (h : ∀ᶠ w in 𝓝[≠] (c - z), p w) : ∀ᶠ w in 𝓝[≠] z, p (c - w) := by
  have htend : Tendsto (fun w : ℂ => c - w) (𝓝[≠] z) (𝓝[≠] (c - z)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((continuous_const.sub continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun w hw => by
        change c - w ≠ c - z
        intro h'
        exact hw (sub_right_injective h'))
  exact htend.eventually h

/-- Two germs that agree on a punctured neighbourhood and are continuous at the point agree at
the point. -/
theorem eq_of_eventuallyEq_nhdsNE_of_continuousAt {f g : ℂ → ℂ} {z : ℂ}
    (h : f =ᶠ[𝓝[≠] z] g) (hf : ContinuousAt f z) (hg : ContinuousAt g z) : f z = g z :=
  tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)

/-- **A meromorphic function on a strip that equals the physical slice on `(2η, Q)` has the germs
of the continued slice there.** -/
theorem eventuallyEq_structureConstantH_of_physical {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) {γ μ η b c : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hμ : 0 < μ) (hη : 0 < η ∧ Q γ - 2 * η > γ) (hb : Q γ - η < b ∧ b < Q γ)
    (hc : Q γ - η < c ∧ c < Q γ)
    {V₃ : Set (Fin 3 → ℂ)} (hV₃ : IsOpen V₃)
    (hV₃mem : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) → complexifyNCharges α ∈ V₃)
    {f₃ : (Fin 3 → ℂ) → ℂ} (hf₃ : DifferentiableOn ℂ f₃ V₃)
    (hf₃eq : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) →
      f₃ (complexifyNCharges α) = (unitVolumeStructureConstant P M γ (α 0) (α 1) (α 2) : ℂ))
    {h : ℝ} (hh : 0 < h) {C : ℂ → ℂ} (hCm : MeromorphicOn C (horizontalStrip h))
    (hCv : ∀ α : ℝ, 2 * η < α → α < Q γ → C (α : ℂ) = (structureConstant P M γ μ α b c : ℂ))
    {x : ℝ} (hx₁ : 2 * η < x) (hx₂ : x < Q γ) :
    C =ᶠ[𝓝[≠] (x : ℂ)] fun z => structureConstantH f₃ γ μ (tripleFirst (b : ℂ) (c : ℂ) z) := by
  obtain ⟨hη0, hηγ⟩ := hη
  set g : ℂ → ℂ := fun z => structureConstantH f₃ γ μ (tripleFirst (b : ℂ) (c : ℂ) z) with hg
  set D : Set ℂ := horizontalStrip h ∩ tripleFirst (b : ℂ) (c : ℂ) ⁻¹' V₃ with hD
  have hDo : IsOpen D := (isOpen_horizontalStrip h).inter
    (hV₃.preimage (differentiable_tripleFirst _ _).continuous)
  have hES : ∀ t : ℝ, 2 * η < t → t < Q γ → ExtendedSeiberg3 γ t b c := fun t h1 h2 =>
    extendedSeiberg3_slice hγ hγ2 ⟨hη0, hηγ⟩ hb hc
      (lt_of_lt_of_le' h1 (by
        have : max (b - c) (c - b) < η := max_lt (by linarith [hb.2, hc.1])
          (by linarith [hb.1, hc.2])
        linarith)) h2
  have hDmem : ∀ t : ℝ, 2 * η < t → t < Q γ → (t : ℂ) ∈ D := fun t h1 h2 => by
    refine ⟨?_, ?_⟩
    · change |((t : ℝ) : ℂ).im| < h
      simpa using hh
    · change tripleFirst (b : ℂ) (c : ℂ) (t : ℂ) ∈ V₃
      rw [tripleFirst_ofReal]
      exact hV₃mem ![t, b, c] (hES t h1 h2)
  have hgval : ∀ t : ℝ, 2 * η < t → t < Q γ → g t = (structureConstant P M γ μ t b c : ℂ) :=
    fun t h1 h2 => by
      change structureConstantH f₃ γ μ (tripleFirst (b : ℂ) (c : ℂ) (t : ℂ)) = _
      rw [tripleFirst_ofReal]
      exact structureConstantH_complexify P M hμ ![t, b, c] (hf₃eq ![t, b, c] (hES t h1 h2))
  have hgm : MeromorphicOn g D := fun z hz =>
    meromorphicOn_structureConstantH_comp hV₃ hf₃ hμ (differentiable_tripleFirst _ _) z hz.2
  have hCm' : MeromorphicOn C D := fun z hz => hCm z hz.1
  set W := connectedComponentIn D (x : ℂ) with hW
  have hWo : IsOpen W := hDo.connectedComponentIn
  have hWsub : W ⊆ D := connectedComponentIn_subset D _
  have hxW : (x : ℂ) ∈ W := mem_connectedComponentIn (hDmem x hx₁ hx₂)
  have hev : ∀ᶠ t : ℝ in 𝓝[≠] x, C t = g t :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_of_mem (Ioo_mem_nhds hx₁ hx₂)
      fun t ht => (hCv t ht.1 ht.2).trans (hgval t ht.1 ht.2).symm)
  exact ShiftGluing.meromorphicOn_eventuallyEq_of_frequently
    (fun z hz => hCm' z (hWsub hz)) (fun z hz => hgm z (hWsub hz))
    isPreconnected_connectedComponentIn hxW hxW
    ((tendsto_ofReal_nhdsNE_slice x).frequently hev.frequently)

/-- The continued slice is analytic at real points of `(2η, Q)` (there `s > 0`). -/
theorem analyticAt_structureConstantH_slice {γ μ η b c : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hμ : 0 < μ) (hη : 0 < η ∧ Q γ - 2 * η > γ) (hb : Q γ - η < b ∧ b < Q γ)
    (hc : Q γ - η < c ∧ c < Q γ)
    {V₃ : Set (Fin 3 → ℂ)} (hV₃ : IsOpen V₃)
    (hV₃mem : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) → complexifyNCharges α ∈ V₃)
    {f₃ : (Fin 3 → ℂ) → ℂ} (hf₃ : DifferentiableOn ℂ f₃ V₃)
    {x : ℝ} (hx₁ : 2 * η < x) (hx₂ : x < Q γ) :
    AnalyticAt ℂ (fun z => structureConstantH f₃ γ μ (tripleFirst (b : ℂ) (c : ℂ) z)) (x : ℂ) := by
  have hES : ExtendedSeiberg3 γ x b c :=
    extendedSeiberg3_slice hγ hγ2 hη hb hc
      (lt_of_lt_of_le' hx₁ (by
        have : max (b - c) (c - b) < η := max_lt (by linarith [hb.2, hc.1])
          (by linarith [hb.1, hc.2])
        linarith [hη.1])) hx₂
  refine analyticAt_structureConstantH_comp hV₃ hf₃ hμ (differentiable_tripleFirst _ _) ?_ ?_
  · rw [tripleFirst_ofReal]
    exact hV₃mem ![x, b, c] hES
  · intro n hn
    rw [tripleFirst_ofReal, sExpC_complexify] at hn
    have hs : 0 < sExp γ x b c := by
      unfold sExp
      exact div_pos (by linarith [hb.1, hc.1]) hγ
    have hn' : sExp γ x b c = -(n : ℝ) := by exact_mod_cast hn
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

/-- **The first structure shift at an exact real point** near `Q`, from a strip function of
`DOZZ.structureConstant_first_shift_strip`. -/
theorem firstShift_exact_of_strip {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) {γ μ η b c : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hη : 0 < η ∧ Q γ - 2 * η > γ) (hb : Q γ - η < b ∧ b < Q γ)
    (hc : Q γ - η < c ∧ c < Q γ)
    {V₃ : Set (Fin 3 → ℂ)} (hV₃ : IsOpen V₃)
    (hV₃mem : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) → complexifyNCharges α ∈ V₃)
    {f₃ : (Fin 3 → ℂ) → ℂ} (hf₃ : DifferentiableOn ℂ f₃ V₃)
    (hf₃eq : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) →
      f₃ (complexifyNCharges α) = (unitVolumeStructureConstant P M γ (α 0) (α 1) (α 2) : ℂ))
    {h : ℝ} (hh : 0 < h) {C : ℂ → ℂ} (hCm : MeromorphicOn C (horizontalStrip h))
    (hCv : ∀ α : ℝ, 2 * η < α → α < Q γ → C (α : ℂ) = (structureConstant P M γ μ α b c : ℂ))
    (hCs : ∀ᶠ z in codiscrete ℂ, C (z + γ / 2) =
      -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (b : ℂ) (c : ℂ) * C (z - γ / 2))
    {α : ℝ} (hα₁ : 2 * η + γ < α) (hα₂ : α < Q γ)
    (hA : AnalyticAt ℂ (fun z => shiftCoeffA γ (γ / 2) z (b : ℂ) (c : ℂ)) ((α : ℂ) - γ / 2)) :
    (structureConstant P M γ μ α b c : ℂ) =
      -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) ((α : ℂ) - γ / 2) (b : ℂ) (c : ℂ) *
        (structureConstant P M γ μ (α - γ) b c : ℂ) := by
  set g : ℂ → ℂ := fun z => structureConstantH f₃ γ μ (tripleFirst (b : ℂ) (c : ℂ) z) with hg
  set z₀ : ℂ := (α : ℂ) - γ / 2 with hz₀
  have hg₁ := eventuallyEq_structureConstantH_of_physical P M hγ hγ2 hμ hη hb hc hV₃ hV₃mem hf₃
    hf₃eq hh hCm hCv (x := α) (by linarith) hα₂
  have hg₂ := eventuallyEq_structureConstantH_of_physical P M hγ hγ2 hμ hη hb hc hV₃ hV₃mem hf₃
    hf₃eq hh hCm hCv (x := α - γ) (by linarith) (by linarith)
  have hga₁ := analyticAt_structureConstantH_slice hγ hγ2 hμ hη hb hc hV₃ hV₃mem hf₃
    (x := α) (by linarith) hα₂
  have hga₂ := analyticAt_structureConstantH_slice hγ hγ2 hμ hη hb hc hV₃ hV₃mem hf₃
    (x := α - γ) (by linarith) (by linarith)
  have hval : ∀ t : ℝ, 2 * η < t → t < Q γ → g t = (structureConstant P M γ μ t b c : ℂ) :=
    fun t h1 h2 => by
      have hES : ExtendedSeiberg3 γ t b c :=
        extendedSeiberg3_slice hγ hγ2 hη hb hc
          (lt_of_lt_of_le' h1 (by
            have : max (b - c) (c - b) < η := max_lt (by linarith [hb.2, hc.1])
              (by linarith [hb.1, hc.2])
            linarith [hη.1])) h2
      change structureConstantH f₃ γ μ (tripleFirst (b : ℂ) (c : ℂ) (t : ℂ)) = _
      rw [tripleFirst_ofReal]
      exact structureConstantH_complexify P M hμ ![t, b, c] (hf₃eq ![t, b, c] hES)
  -- the relation for the continued slice near `z₀`
  have hrel : ∀ᶠ z in 𝓝[≠] z₀, g (z + γ / 2) =
      -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (b : ℂ) (c : ℂ) * g (z - γ / 2) := by
    have e₁ : ∀ᶠ z in 𝓝[≠] z₀, C (z + γ / 2) = g (z + γ / 2) :=
      ShiftGluing.eventually_comp_add (z := z₀) ((γ : ℂ) / 2)
        (by rw [hz₀, sub_add_cancel]; exact hg₁)
    have e₂ : ∀ᶠ z in 𝓝[≠] z₀, C (z - γ / 2) = g (z - γ / 2) :=
      ShiftGluing.eventually_comp_sub (z := z₀) ((γ : ℂ) / 2)
        (by rw [show z₀ - (γ : ℂ) / 2 = ((α - γ : ℝ) : ℂ) by rw [hz₀]; push_cast; ring]
            exact hg₂)
    filter_upwards [(eventually_codiscrete_iff_forall_eventually_nhdsNE.mp hCs) z₀, e₁, e₂]
      with z h0 h1 h2
    rw [← h1, ← h2]
    exact h0
  have hpt := eq_of_eventuallyEq_nhdsNE_of_continuousAt hrel
    (by
      have : ContinuousAt g (z₀ + γ / 2) := by
        rw [hz₀, sub_add_cancel]
        exact hga₁.continuousAt
      exact ContinuousAt.comp (f := fun w : ℂ => w + (γ : ℂ) / 2) this (by fun_prop))
    (by
      have hg' : ContinuousAt g (z₀ - γ / 2) := by
        rw [show z₀ - (γ : ℂ) / 2 = ((α - γ : ℝ) : ℂ) by rw [hz₀]; push_cast; ring]
        exact hga₂.continuousAt
      exact (continuousAt_const.mul hA.continuousAt).mul
        (ContinuousAt.comp (f := fun w : ℂ => w - (γ : ℂ) / 2) hg' (by fun_prop)))
  rw [hz₀, sub_add_cancel, show (α : ℂ) - γ / 2 - γ / 2 = ((α - γ : ℝ) : ℂ) by push_cast; ring,
    hval α (by linarith) hα₂, hval (α - γ) (by linarith) (by linarith)] at hpt
  exact hpt

/-- **The reflected γ/2 shift at an exact real point** to the right of `Q`, from strip functions of
`DOZZ.structureConstant_reflected_shift_and_gluing` and a reference reflection germ `R`. -/
theorem reflectedShift_exact_of_strip {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) {γ μ η b c : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hη : 0 < η ∧ Q γ - 2 * η > γ) (hb : Q γ - η < b ∧ b < Q γ)
    (hc : Q γ - η < c ∧ c < Q γ)
    {V₃ : Set (Fin 3 → ℂ)} (hV₃ : IsOpen V₃)
    (hV₃mem : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) → complexifyNCharges α ∈ V₃)
    {f₃ : (Fin 3 → ℂ) → ℂ} (hf₃ : DifferentiableOn ℂ f₃ V₃)
    (hf₃eq : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) →
      f₃ (complexifyNCharges α) = (unitVolumeStructureConstant P M γ (α 0) (α 1) (α 2) : ℂ))
    {h : ℝ} (hh : 0 < h) {C Rs R : ℂ → ℂ} (hCm : MeromorphicOn C (horizontalStrip h))
    (hRsm : MeromorphicOn Rs (horizontalStrip h)) (hRm : MeromorphicOn R (horizontalStrip h))
    (hCv : ∀ α : ℝ, 2 * η < α → α < Q γ → C (α : ℂ) = (structureConstant P M γ μ α b c : ℂ))
    (hRsR : ∀ α : ℝ, γ / 2 < α → α < Q γ → Rs (α : ℂ) = R (α : ℂ))
    (hrefl : ∀ᶠ z in codiscrete ℂ, Rs (z + γ / 2) * C (2 * Q γ - z - γ / 2) =
      -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (b : ℂ) (c : ℂ) * C (z - γ / 2))
    {α : ℝ} (hα₁ : Q γ < α) (hα₂ : α < Q γ + γ)
    (hR : AnalyticAt ℂ R (α : ℂ))
    (hA : AnalyticAt ℂ (fun z => shiftCoeffA γ (γ / 2) z (b : ℂ) (c : ℂ)) ((α : ℂ) - γ / 2)) :
    R α * (structureConstant P M γ μ (2 * Q γ - α) b c : ℂ) =
      -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) ((α : ℂ) - γ / 2) (b : ℂ) (c : ℂ) *
        (structureConstant P M γ μ (α - γ) b c : ℂ) := by
  obtain ⟨hη0, hηγ⟩ := hη
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hγh : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ (by norm_num) hγ]
    nlinarith
  set g : ℂ → ℂ := fun z => structureConstantH f₃ γ μ (tripleFirst (b : ℂ) (c : ℂ) z) with hg
  set z₀ : ℂ := (α : ℂ) - γ / 2 with hz₀
  have hg₁ := eventuallyEq_structureConstantH_of_physical P M hγ hγ2 hμ ⟨hη0, hηγ⟩ hb hc hV₃
    hV₃mem hf₃ hf₃eq hh hCm hCv (x := 2 * Q γ - α) (by linarith) (by linarith)
  have hg₂ := eventuallyEq_structureConstantH_of_physical P M hγ hγ2 hμ ⟨hη0, hηγ⟩ hb hc hV₃
    hV₃mem hf₃ hf₃eq hh hCm hCv (x := α - γ) (by linarith) (by linarith)
  have hga₁ := analyticAt_structureConstantH_slice hγ hγ2 hμ ⟨hη0, hηγ⟩ hb hc hV₃ hV₃mem hf₃
    (x := 2 * Q γ - α) (by linarith) (by linarith)
  have hga₂ := analyticAt_structureConstantH_slice hγ hγ2 hμ ⟨hη0, hηγ⟩ hb hc hV₃ hV₃mem hf₃
    (x := α - γ) (by linarith) (by linarith)
  have hval : ∀ t : ℝ, 2 * η < t → t < Q γ → g t = (structureConstant P M γ μ t b c : ℂ) :=
    fun t h1 h2 => by
      have hES : ExtendedSeiberg3 γ t b c :=
        extendedSeiberg3_slice hγ hγ2 ⟨hη0, hηγ⟩ hb hc
          (lt_of_lt_of_le' h1 (by
            have : max (b - c) (c - b) < η := max_lt (by linarith [hb.2, hc.1])
              (by linarith [hb.1, hc.2])
            linarith)) h2
      change structureConstantH f₃ γ μ (tripleFirst (b : ℂ) (c : ℂ) (t : ℂ)) = _
      rw [tripleFirst_ofReal]
      exact structureConstantH_complexify P M hμ ![t, b, c] (hf₃eq ![t, b, c] hES)
  -- the two reflection germs agree on the strip
  have hRR : Rs =ᶠ[𝓝[≠] (α : ℂ)] R := by
    set x₀ : ℝ := (γ / 2 + Q γ) / 2 with hx₀
    have hx₀1 : γ / 2 < x₀ := by rw [hx₀]; linarith
    have hx₀2 : x₀ < Q γ := by rw [hx₀]; linarith
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] x₀, Rs t = R t :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_of_mem (Ioo_mem_nhds hx₀1 hx₀2)
        fun t ht => hRsR t ht.1 ht.2)
    exact ShiftGluing.meromorphicOn_eventuallyEq_of_frequently hRsm hRm
      (isPreconnected_horizontalStrip h)
      (by change |((x₀ : ℝ) : ℂ).im| < h; simpa using hh)
      (by change |((α : ℝ) : ℂ).im| < h; simpa using hh)
      ((tendsto_ofReal_nhdsNE_slice x₀).frequently hev.frequently)
  have hrel : ∀ᶠ z in 𝓝[≠] z₀, R (z + γ / 2) * g (2 * Q γ - z - γ / 2) =
      -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (b : ℂ) (c : ℂ) * g (z - γ / 2) := by
    have e₀ : ∀ᶠ z in 𝓝[≠] z₀, Rs (z + γ / 2) = R (z + γ / 2) :=
      ShiftGluing.eventually_comp_add (z := z₀) ((γ : ℂ) / 2)
        (by rw [hz₀, sub_add_cancel]; exact hRR)
    have e₁ : ∀ᶠ z in 𝓝[≠] z₀, C (2 * Q γ - γ / 2 - z) = g (2 * Q γ - γ / 2 - z) :=
      eventually_comp_reflect (z := z₀) (2 * (Q γ : ℂ) - γ / 2)
        (by rw [show 2 * (Q γ : ℂ) - γ / 2 - z₀ = ((2 * Q γ - α : ℝ) : ℂ) by
              rw [hz₀]; push_cast; ring]
            exact hg₁)
    have e₂ : ∀ᶠ z in 𝓝[≠] z₀, C (z - γ / 2) = g (z - γ / 2) :=
      ShiftGluing.eventually_comp_sub (z := z₀) ((γ : ℂ) / 2)
        (by rw [show z₀ - (γ : ℂ) / 2 = ((α - γ : ℝ) : ℂ) by rw [hz₀]; push_cast; ring]
            exact hg₂)
    filter_upwards [(eventually_codiscrete_iff_forall_eventually_nhdsNE.mp hrefl) z₀, e₀, e₁, e₂]
      with z h0 h1 h2 h3
    rw [← h1, show 2 * (Q γ : ℂ) - z - γ / 2 = 2 * Q γ - γ / 2 - z by ring, ← h2, ← h3,
      show 2 * (Q γ : ℂ) - γ / 2 - z = 2 * Q γ - z - γ / 2 by ring]
    exact h0
  have hpt := eq_of_eventuallyEq_nhdsNE_of_continuousAt hrel
    (by
      have hRc : ContinuousAt R (z₀ + γ / 2) := by
        rw [hz₀, sub_add_cancel]
        exact hR.continuousAt
      have hgc : ContinuousAt g (2 * Q γ - z₀ - γ / 2) := by
        rw [show 2 * (Q γ : ℂ) - z₀ - γ / 2 = ((2 * Q γ - α : ℝ) : ℂ) by
          rw [hz₀]; push_cast; ring]
        exact hga₁.continuousAt
      exact (ContinuousAt.comp (f := fun w : ℂ => w + (γ : ℂ) / 2) hRc (by fun_prop)).mul
        (ContinuousAt.comp (f := fun w : ℂ => 2 * (Q γ : ℂ) - w - γ / 2) hgc (by fun_prop)))
    (by
      have hg' : ContinuousAt g (z₀ - γ / 2) := by
        rw [show z₀ - (γ : ℂ) / 2 = ((α - γ : ℝ) : ℂ) by rw [hz₀]; push_cast; ring]
        exact hga₂.continuousAt
      exact (continuousAt_const.mul hA.continuousAt).mul
        (ContinuousAt.comp (f := fun w : ℂ => w - (γ : ℂ) / 2) hg' (by fun_prop)))
  rw [hz₀, sub_add_cancel,
    show 2 * (Q γ : ℂ) - ((α : ℂ) - γ / 2) - γ / 2 = ((2 * Q γ - α : ℝ) : ℂ) by push_cast; ring,
    show (α : ℂ) - γ / 2 - γ / 2 = ((α - γ : ℝ) : ℂ) by push_cast; ring,
    hval (2 * Q γ - α) (by linarith) (by linarith), hval (α - γ) (by linarith) (by linarith)]
    at hpt
  exact hpt

end DOZZ.Proofs

end
