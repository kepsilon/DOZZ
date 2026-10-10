/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.MomentLimitC

/-! # Limits of the moments of the softened four-point mass

Along `(εₙ, zₙ) → (0, z₀)` with `z₀ ∉ {0, 1}` and `0 ≤ εₙ ≤ 1`, the expectations of
`I^{-s}` and of the moment fields `−s I^{−s−1} DI` and `s(s+1) I^{−s−2} DI ⊗ DI − s I^{−s−1} D²I`
of the softened four-point mass `I` converge to their values at `(0, z₀)`. The near-root parts
are small in expectation uniformly along the sequence (rooted bound), and the far parts converge
by dominated convergence. The same estimates give bounds on the expectations of the moment fields
that are uniform near `z₀` and in the softening. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

attribute [local instance low] bpzNormedAddCommGroupBilin bpzNormedSpaceBilin

variable {γ χ α₁ α₂ α₃ : ℝ}

/-- The almost sure data at a regular root `z₀`, with an integrable lower bound `Y` of the mass
at all roots within distance `1` of `z₀`. -/
theorem bpz_moment_setup {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (ha1 : γ * χ / 2 ≤ 1)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 ≤ s) {z₀ : ℂ}
    (hz0 : z₀ ≠ 0) (hz1 : z₀ ≠ 1) :
    ∃ Y : Ω → ℝ, Integrable (fun ω => Y ω ^ (-s)) P ∧
      ∀ᵐ ω ∂P, (∀ x, M ω {x} = 0) ∧ 0 < Y ω ∧ Integrable (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) ∧
        Integrable (fun x => Complex.normSq (x - z₀) ^ (γ * χ / 2) *
          bpzBaseWeight γ χ α₁ α₂ α₃ x) (M ω) ∧
        ∀ z : ℂ, ‖z - z₀‖ ≤ 1 → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
          Integrable (fun x => (Complex.normSq (x - z) + ε ^ 2) ^ (γ * χ / 2) *
            bpzBaseWeight γ χ α₁ α₂ α₃ x) (M ω) ∧
          Y ω ≤ bpzSoftMassReal (γ * χ / 2) ε (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z := by
  have ha : 0 < γ * χ / 2 := by positivity
  obtain ⟨Y, -, hYpos, hYint, hYle⟩ := bpz_farBall_lower (χ := χ) (α₁ := α₁) (α₂ := α₂)
    (α₃ := α₃) P X hX hγ hγ2 M hM hMm (R := ‖z₀‖ + 1) (by positivity) hs
  refine ⟨Y, hYint, ?_⟩
  filter_upwards [bpz_moment_good_ae P X hX hγ hγ2 M hM hMm hχ hα₁ hα₂ hα₃ hz0 hz1, hYpos]
    with ω hω hY
  obtain ⟨h0, hintw, hint⟩ := hω
  refine ⟨h0, hY, hintw, hint, fun z hz ε hε0 hε1 => ?_⟩
  have hintz := bpzSoft_integrable_near ha ha1 hε0 hε1 measurable_bpzBaseWeight
    bpzBaseWeight_nonneg hint hintw hz
  refine ⟨hintz, hYle ω z ?_ ε hε0 hε1 hintz⟩
  have := norm_le_norm_add_norm_sub' z z₀
  linarith

/-- Bounds at a fixed softening and root for the first moment field and its far part. -/
theorem bpz_momField1_bounds {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (ha1 : γ * χ / 2 ≤ 1)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 ≤ s) {z₀ : ℂ}
    (hz0 : z₀ ≠ 0) (hz1 : z₀ ≠ 1) {Y : Ω → ℝ} (hYint : Integrable (fun ω => Y ω ^ (-s)) P)
    (hG : ∀ᵐ ω ∂P, (∀ x, M ω {x} = 0) ∧ 0 < Y ω ∧
        ∀ z : ℂ, ‖z - z₀‖ ≤ 1 → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
          Integrable (fun x => (Complex.normSq (x - z) + ε ^ 2) ^ (γ * χ / 2) *
            bpzBaseWeight γ χ α₁ α₂ α₃ x) (M ω) ∧
          Y ω ≤ bpzSoftMassReal (γ * χ / 2) ε (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ z : ℂ, ‖z - z₀‖ ≤ min 1 (r / 2) →
        Integrable (fun ω => bpzMomField1 (γ * χ / 2) s ε (bpzBaseWeight γ χ α₁ α₂ α₃)
          (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z) P ∧
        Integrable (fun ω => bpzMomField1 (γ * χ / 2) s ε (bpzBaseWeight γ χ α₁ α₂ α₃)
          (fun x => if r ≤ ‖x - z₀‖ then bpzBaseWeight γ χ α₁ α₂ α₃ x else 0) (M ω) z) P ∧
        ∫ ω, ‖bpzMomField1 (γ * χ / 2) s ε (bpzBaseWeight γ χ α₁ α₂ α₃)
            (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z -
          bpzMomField1 (γ * χ / 2) s ε (bpzBaseWeight γ χ α₁ α₂ α₃)
            (fun x => if r ≤ ‖x - z₀‖ then bpzBaseWeight γ χ α₁ α₂ α₃ x else 0) (M ω) z‖ ∂P ≤
          s * (2 * (γ * χ / 2)) * (C * (2 * Real.pi * (2 * r) ^ (2 * (γ * χ / 2) - 1 + 2) /
            (2 * (γ * χ / 2) - 1 + 2))) ∧
        ∀ᵐ ω ∂P, ‖bpzMomField1 (γ * χ / 2) s ε (bpzBaseWeight γ χ α₁ α₂ α₃)
            (fun x => if r ≤ ‖x - z₀‖ then bpzBaseWeight γ χ α₁ α₂ α₃ x else 0) (M ω) z‖ ≤
          s * (4 * (γ * χ / 2) / r) * Y ω ^ (-s) := by
  have ha : 0 < γ * χ / 2 := by positivity
  obtain ⟨r₀, hr₀, C, hC0, hC⟩ := bpz_near_real_bound P X hX hγ hγ2 M hM hMm hχ hα₁ hα₂ hα₃
    hs hz0 hz1
  refine ⟨r₀, hr₀, C, hC0, fun r hr hrr ε hε0 hε1 z hz => ?_⟩
  have hz1' : ‖z - z₀‖ ≤ 1 := hz.trans (min_le_left _ _)
  have hz2' : ‖z - z₀‖ ≤ r / 2 := hz.trans (min_le_right _ _)
  obtain ⟨hBint, hB, hnear⟩ := hC r hr hrr z hz2' ε hε0 hε1 (2 * (γ * χ / 2) - 1)
    (by linarith)
  refine bpz_momField1_near hMm ha ha1 hs measurable_bpzBaseWeight bpzBaseWeight_nonneg hr hz2'
    hYint ?_ hnear hBint hB
  filter_upwards [hG] with ω h
  exact ⟨h.1 z, h.2.1, (h.2.2 z hz1' ε hε0 hε1).2, (h.2.2 z hz1' ε hε0 hε1).1⟩

/-- Bounds at a fixed softening and root for the second moment field and its far part. -/
theorem bpz_momField2_bounds {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (ha1 : γ * χ / 2 ≤ 1)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 ≤ s) {z₀ : ℂ}
    (hz0 : z₀ ≠ 0) (hz1 : z₀ ≠ 1) {Y : Ω → ℝ} (hYint : Integrable (fun ω => Y ω ^ (-s)) P)
    (hG : ∀ᵐ ω ∂P, (∀ x, M ω {x} = 0) ∧ 0 < Y ω ∧
        ∀ z : ℂ, ‖z - z₀‖ ≤ 1 → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
          Integrable (fun x => (Complex.normSq (x - z) + ε ^ 2) ^ (γ * χ / 2) *
            bpzBaseWeight γ χ α₁ α₂ α₃ x) (M ω) ∧
          Y ω ≤ bpzSoftMassReal (γ * χ / 2) ε (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ z : ℂ, ‖z - z₀‖ ≤ min 1 (r / 2) →
        Integrable (fun ω => bpzMomField2 (γ * χ / 2) s ε (bpzBaseWeight γ χ α₁ α₂ α₃)
          (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z) P ∧
        Integrable (fun ω => bpzMomField2 (γ * χ / 2) s ε (bpzBaseWeight γ χ α₁ α₂ α₃)
          (fun x => if r ≤ ‖x - z₀‖ then bpzBaseWeight γ χ α₁ α₂ α₃ x else 0) (M ω) z) P ∧
        ∫ ω, ‖bpzMomField2 (γ * χ / 2) s ε (bpzBaseWeight γ χ α₁ α₂ α₃)
            (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z -
          bpzMomField2 (γ * χ / 2) s ε (bpzBaseWeight γ χ α₁ α₂ α₃)
            (fun x => if r ≤ ‖x - z₀‖ then bpzBaseWeight γ χ α₁ α₂ α₃ x else 0) (M ω) z‖ ∂P ≤
          (4 * (γ * χ / 2) ^ 2 * s * (s + 1) +
              s * (4 * (γ * χ / 2) * (1 - γ * χ / 2) + 2 * (γ * χ / 2))) *
            (C * (2 * Real.pi * (2 * r) ^ (2 * (γ * χ / 2) - 2 + 2) /
              (2 * (γ * χ / 2) - 2 + 2))) +
          16 * (γ * χ / 2) ^ 2 * s * (s + 1) / r *
            (C * (2 * Real.pi * (2 * r) ^ (2 * (γ * χ / 2) - 1 + 2) /
              (2 * (γ * χ / 2) - 1 + 2))) ∧
        ∀ᵐ ω ∂P, ‖bpzMomField2 (γ * χ / 2) s ε (bpzBaseWeight γ χ α₁ α₂ α₃)
            (fun x => if r ≤ ‖x - z₀‖ then bpzBaseWeight γ χ α₁ α₂ α₃ x else 0) (M ω) z‖ ≤
          (s * (s + 1) * (4 * (γ * χ / 2) / r) ^ 2 +
            s * (4 * (4 * (γ * χ / 2) * (1 - γ * χ / 2) + 2 * (γ * χ / 2)) / r ^ 2)) *
            Y ω ^ (-s) := by
  have ha : 0 < γ * χ / 2 := by positivity
  obtain ⟨r₀, hr₀, C, hC0, hC⟩ := bpz_near_real_bound P X hX hγ hγ2 M hM hMm hχ hα₁ hα₂ hα₃
    hs hz0 hz1
  refine ⟨r₀, hr₀, C, hC0, fun r hr hrr ε hε0 hε1 z hz => ?_⟩
  have hz1' : ‖z - z₀‖ ≤ 1 := hz.trans (min_le_left _ _)
  have hz2' : ‖z - z₀‖ ≤ r / 2 := hz.trans (min_le_right _ _)
  obtain ⟨hB1int, hB1, hnear1⟩ := hC r hr hrr z hz2' ε hε0 hε1 (2 * (γ * χ / 2) - 1)
    (by linarith)
  obtain ⟨hB2int, hB2, hnear2⟩ := hC r hr hrr z hz2' ε hε0 hε1 (2 * (γ * χ / 2) - 2)
    (by linarith)
  refine bpz_momField2_near hMm ha ha1 hs measurable_bpzBaseWeight bpzBaseWeight_nonneg hr hz2'
    hYint ?_ hnear1 hnear2 hB1int hB1 hB2int hB2
  filter_upwards [hG] with ω h
  exact ⟨h.1 z, h.2.1, (h.2.2 z hz1' ε hε0 hε1).2, (h.2.2 z hz1' ε hε0 hε1).1⟩

/-- Rewriting the second-field bound as a multiple of `(2r)^{2a}`. -/
theorem bpz_mom2_bound_eq {a s C r K₂ : ℝ} (hr : 0 < r) :
    (4 * a ^ 2 * s * (s + 1) + s * K₂) * (C * (2 * Real.pi * (2 * r) ^ (2 * a - 2 + 2) /
        (2 * a - 2 + 2))) +
      16 * a ^ 2 * s * (s + 1) / r * (C * (2 * Real.pi * (2 * r) ^ (2 * a - 1 + 2) /
        (2 * a - 1 + 2))) =
    ((4 * a ^ 2 * s * (s + 1) + s * K₂) * (C * (2 * Real.pi) / (2 * a - 2 + 2)) +
      32 * a ^ 2 * s * (s + 1) * (C * (2 * Real.pi) / (2 * a - 1 + 2))) *
        (2 * r) ^ (2 * a - 2 + 2) := by
  have h2r : 0 < 2 * r := by positivity
  have e : (2 * r) ^ (2 * a - 1 + 2) = (2 * r) ^ (2 * a - 2 + 2) * (2 * r) := by
    rw [show 2 * a - 1 + 2 = (2 * a - 2 + 2) + 1 by ring, Real.rpow_add h2r, Real.rpow_one]
  rw [e]
  field_simp
  ring

/-- Convergence of the zeroth moment along `(εₙ, zₙ) → (0, z₀)`. -/
theorem bpz_tendsto_mom0_gmc {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (ha1 : γ * χ / 2 ≤ 1)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 ≤ s) {z₀ : ℂ}
    (hz0 : z₀ ≠ 0) (hz1 : z₀ ≠ 1) {εs : ℕ → ℝ} (hε0 : ∀ n, 0 ≤ εs n) (hε1 : ∀ n, εs n ≤ 1)
    (hε : Tendsto εs atTop (𝓝 0)) {zs : ℕ → ℂ} (hz : Tendsto zs atTop (𝓝 z₀)) :
    Tendsto (fun n => ∫ ω, bpzSoftMassReal (γ * χ / 2) (εs n) (bpzBaseWeight γ χ α₁ α₂ α₃)
        (M ω) (zs n) ^ (-s) ∂P) atTop
      (𝓝 (∫ ω, bpzSoftMassReal (γ * χ / 2) 0 (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z₀ ^ (-s) ∂P)) := by
  have ha : 0 < γ * χ / 2 := by positivity
  obtain ⟨Y, hYint, hG⟩ := bpz_moment_setup P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs hz0 hz1
  refine bpz_tendsto_mom0 hMm ha ha1 hs measurable_bpzBaseWeight bpzBaseWeight_nonneg hYint ?_
    hε0 hε1 hε hz
  filter_upwards [hG] with ω h
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, fun z hz ε h0 h1 => (h.2.2.2.2 z hz ε h0 h1).2⟩

/-- Convergence of the first moment field along `(εₙ, zₙ) → (0, z₀)`. -/
theorem bpz_tendsto_momField1_gmc {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (ha1 : γ * χ / 2 ≤ 1)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 ≤ s) {z₀ : ℂ}
    (hz0 : z₀ ≠ 0) (hz1 : z₀ ≠ 1) {εs : ℕ → ℝ} (hε0 : ∀ n, 0 ≤ εs n) (hε1 : ∀ n, εs n ≤ 1)
    (hε : Tendsto εs atTop (𝓝 0)) {zs : ℕ → ℂ} (hz : Tendsto zs atTop (𝓝 z₀)) :
    Tendsto (fun n => ∫ ω, bpzMomField1 (γ * χ / 2) s (εs n) (bpzBaseWeight γ χ α₁ α₂ α₃)
        (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) (zs n) ∂P) atTop
      (𝓝 (∫ ω, bpzMomField1 (γ * χ / 2) s 0 (bpzBaseWeight γ χ α₁ α₂ α₃)
        (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z₀ ∂P)) := by
  have ha : 0 < γ * χ / 2 := by positivity
  obtain ⟨Y, hYint, hG⟩ := bpz_moment_setup P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs hz0 hz1
  have hG' : ∀ᵐ ω ∂P, (∀ x, M ω {x} = 0) ∧ 0 < Y ω ∧
      ∀ z : ℂ, ‖z - z₀‖ ≤ 1 → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
        Integrable (fun x => (Complex.normSq (x - z) + ε ^ 2) ^ (γ * χ / 2) *
          bpzBaseWeight γ χ α₁ α₂ α₃ x) (M ω) ∧
        Y ω ≤ bpzSoftMassReal (γ * χ / 2) ε (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z :=
    hG.mono fun ω h => ⟨h.1, h.2.1, h.2.2.2.2⟩
  have hgood : ∀ᵐ ω ∂P, 0 < Y ω ∧ Integrable (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) ∧
      Integrable (fun x => Complex.normSq (x - z₀) ^ (γ * χ / 2) *
        bpzBaseWeight γ χ α₁ α₂ α₃ x) (M ω) ∧
      ∀ z : ℂ, ‖z - z₀‖ ≤ 1 → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
        Y ω ≤ bpzSoftMassReal (γ * χ / 2) ε (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z :=
    hG.mono fun ω h => ⟨h.2.1, h.2.2.1, h.2.2.2.1, fun z hz ε h0 h1 => (h.2.2.2.2 z hz ε h0 h1).2⟩
  obtain ⟨r₀, hr₀, C, hC0, hQ⟩ := bpz_momField1_bounds P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂
    hα₃ hs hz0 hz1 hYint hG'
  refine bpz_tendsto_integral_of_approx fun η hη => ?_
  obtain ⟨r, hr, hrr, hrη⟩ := bpz_exists_small_radius
    (K := s * (2 * (γ * χ / 2)) * (C * (2 * Real.pi) / (2 * (γ * χ / 2) - 1 + 2)))
    (p := 2 * (γ * χ / 2) - 1 + 2) (by linarith) hr₀ hη
  have hbound : s * (2 * (γ * χ / 2)) * (C * (2 * Real.pi * (2 * r) ^ (2 * (γ * χ / 2) - 1 + 2) /
      (2 * (γ * χ / 2) - 1 + 2))) ≤ η := by
    refine le_of_eq_of_le ?_ hrη
    ring
  have hev : ∀ᶠ n in atTop, ‖zs n - z₀‖ ≤ min 1 (r / 2) :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hz).eventually
      (ge_mem_nhds (lt_min one_pos (half_pos hr)))
  refine ⟨fun n ω => bpzMomField1 (γ * χ / 2) s (εs n) (bpzBaseWeight γ χ α₁ α₂ α₃)
      (fun x => if r ≤ ‖x - z₀‖ then bpzBaseWeight γ χ α₁ α₂ α₃ x else 0) (M ω) (zs n),
    fun ω => bpzMomField1 (γ * χ / 2) s 0 (bpzBaseWeight γ χ α₁ α₂ α₃)
      (fun x => if r ≤ ‖x - z₀‖ then bpzBaseWeight γ χ α₁ α₂ α₃ x else 0) (M ω) z₀,
    bpz_tendsto_momField1_far hMm ha ha1 hs measurable_bpzBaseWeight bpzBaseWeight_nonneg hr
      hYint hgood hε0 hε1 hε hz, ?_, ?_⟩
  · filter_upwards [hev] with n hn
    obtain ⟨h1, h2, h3, -⟩ := hQ r hr hrr (εs n) (hε0 n) (hε1 n) (zs n) hn
    exact ⟨h1, h2, h3.trans hbound⟩
  · have h0 : ‖z₀ - z₀‖ ≤ min 1 (r / 2) := by
      rw [sub_self, norm_zero]
      exact le_min zero_le_one (by positivity)
    obtain ⟨h1, h2, h3, -⟩ := hQ r hr hrr 0 le_rfl zero_le_one z₀ h0
    exact ⟨h1, h2, h3.trans hbound⟩

/-- Convergence of the second moment field along `(εₙ, zₙ) → (0, z₀)`. -/
theorem bpz_tendsto_momField2_gmc {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (ha1 : γ * χ / 2 ≤ 1)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 ≤ s) {z₀ : ℂ}
    (hz0 : z₀ ≠ 0) (hz1 : z₀ ≠ 1) {εs : ℕ → ℝ} (hε0 : ∀ n, 0 ≤ εs n) (hε1 : ∀ n, εs n ≤ 1)
    (hε : Tendsto εs atTop (𝓝 0)) {zs : ℕ → ℂ} (hz : Tendsto zs atTop (𝓝 z₀)) :
    Tendsto (fun n => ∫ ω, bpzMomField2 (γ * χ / 2) s (εs n) (bpzBaseWeight γ χ α₁ α₂ α₃)
        (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) (zs n) ∂P) atTop
      (𝓝 (∫ ω, bpzMomField2 (γ * χ / 2) s 0 (bpzBaseWeight γ χ α₁ α₂ α₃)
        (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z₀ ∂P)) := by
  have ha : 0 < γ * χ / 2 := by positivity
  obtain ⟨Y, hYint, hG⟩ := bpz_moment_setup P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs hz0 hz1
  have hG' : ∀ᵐ ω ∂P, (∀ x, M ω {x} = 0) ∧ 0 < Y ω ∧
      ∀ z : ℂ, ‖z - z₀‖ ≤ 1 → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
        Integrable (fun x => (Complex.normSq (x - z) + ε ^ 2) ^ (γ * χ / 2) *
          bpzBaseWeight γ χ α₁ α₂ α₃ x) (M ω) ∧
        Y ω ≤ bpzSoftMassReal (γ * χ / 2) ε (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z :=
    hG.mono fun ω h => ⟨h.1, h.2.1, h.2.2.2.2⟩
  have hgood : ∀ᵐ ω ∂P, 0 < Y ω ∧ Integrable (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) ∧
      Integrable (fun x => Complex.normSq (x - z₀) ^ (γ * χ / 2) *
        bpzBaseWeight γ χ α₁ α₂ α₃ x) (M ω) ∧
      ∀ z : ℂ, ‖z - z₀‖ ≤ 1 → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
        Y ω ≤ bpzSoftMassReal (γ * χ / 2) ε (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z :=
    hG.mono fun ω h => ⟨h.2.1, h.2.2.1, h.2.2.2.1, fun z hz ε h0 h1 => (h.2.2.2.2 z hz ε h0 h1).2⟩
  obtain ⟨r₀, hr₀, C, hC0, hQ⟩ := bpz_momField2_bounds P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂
    hα₃ hs hz0 hz1 hYint hG'
  refine bpz_tendsto_integral_of_approx fun η hη => ?_
  obtain ⟨r, hr, hrr, hrη⟩ := bpz_exists_small_radius
    (K := (4 * (γ * χ / 2) ^ 2 * s * (s + 1) +
        s * (4 * (γ * χ / 2) * (1 - γ * χ / 2) + 2 * (γ * χ / 2))) *
          (C * (2 * Real.pi) / (2 * (γ * χ / 2) - 2 + 2)) +
      32 * (γ * χ / 2) ^ 2 * s * (s + 1) * (C * (2 * Real.pi) / (2 * (γ * χ / 2) - 1 + 2)))
    (p := 2 * (γ * χ / 2) - 2 + 2) (by linarith) hr₀ hη
  have hbound := (bpz_mom2_bound_eq (a := γ * χ / 2) (s := s) (C := C)
    (K₂ := 4 * (γ * χ / 2) * (1 - γ * χ / 2) + 2 * (γ * χ / 2)) hr).le.trans hrη
  have hev : ∀ᶠ n in atTop, ‖zs n - z₀‖ ≤ min 1 (r / 2) :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hz).eventually
      (ge_mem_nhds (lt_min one_pos (half_pos hr)))
  refine ⟨fun n ω => bpzMomField2 (γ * χ / 2) s (εs n) (bpzBaseWeight γ χ α₁ α₂ α₃)
      (fun x => if r ≤ ‖x - z₀‖ then bpzBaseWeight γ χ α₁ α₂ α₃ x else 0) (M ω) (zs n),
    fun ω => bpzMomField2 (γ * χ / 2) s 0 (bpzBaseWeight γ χ α₁ α₂ α₃)
      (fun x => if r ≤ ‖x - z₀‖ then bpzBaseWeight γ χ α₁ α₂ α₃ x else 0) (M ω) z₀,
    bpz_tendsto_momField2_far hMm ha ha1 hs measurable_bpzBaseWeight bpzBaseWeight_nonneg hr
      hYint hgood hε0 hε1 hε hz, ?_, ?_⟩
  · filter_upwards [hev] with n hn
    obtain ⟨h1, h2, h3, -⟩ := hQ r hr hrr (εs n) (hε0 n) (hε1 n) (zs n) hn
    exact ⟨h1, h2, h3.trans hbound⟩
  · have h0 : ‖z₀ - z₀‖ ≤ min 1 (r / 2) := by
      rw [sub_self, norm_zero]
      exact le_min zero_le_one (by positivity)
    obtain ⟨h1, h2, h3, -⟩ := hQ r hr hrr 0 le_rfl zero_le_one z₀ h0
    exact ⟨h1, h2, h3.trans hbound⟩

end DOZZ.Proofs
