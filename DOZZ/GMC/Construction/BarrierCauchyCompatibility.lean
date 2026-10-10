/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.BarrierCauchyLocalEstimates

/-! Uniform finite-scale covariance and rectangle limits for mixed admissible cutoffs. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- For any choices of the two admissible regularization families, the finite coarse Gaussian
rectangle sees the same limiting two-root tilt shift. The first family supplies the coarse
barrier coordinates; compatibility transfers the fixed-coarse limit for every `Z` root to the
same kernel as for `Y`. -/
theorem compatible_finite_coarse_two_root_shift_tendsto_uniformly
    {Ω α ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (_hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    (hYZ : IsCompatibleAdmissibleRegularizations P U ε₀ ε₁ Y Z)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (S : Set α) (rootX rootY : α → ℂ)
    (hrootX : ∀ a ∈ S, rootX a ∈ K) (hrootY : ∀ a ∈ S, rootY a ∈ K)
    (scale : ι → ℕ) (center : α → ι → ℂ)
    (hcenter : ∀ a ∈ S, ∀ i, center a i ∈ K)
    (hscale : ∀ i, Real.exp (-(scale i : ℝ)) ≤ min ε₀ ε₁)
    (b₁ b₂ : Bool) (Γ : Set ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hΓ : ∀ γ ∈ Γ, |γ| ≤ B) :
    ∃ coarseKernel : ℕ → ℂ → ℂ → ℝ, ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε ε' : ℝ,
        0 < ε → ε ≤ min δ (min ε₀ ε₁) →
        0 < ε' → ε' ≤ min δ (min ε₀ ε₁) →
        ∀ γ ∈ Γ, ∀ a ∈ S, ∀ i,
          |γ * gaussianCovariance P
                (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
                (fun ω => if b₁ then Y ω ε (rootX a) else Z ω ε (rootX a)) +
            γ * gaussianCovariance P
                (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
                (fun ω => if b₂ then Y ω ε' (rootY a) else Z ω ε' (rootY a)) -
            (γ * coarseKernel (scale i) (rootX a) (center a i) +
              γ * coarseKernel (scale i) (rootY a) (center a i))| < η := by
  rcases hYZ with ⟨_hJoint, _hCov, _hCoarse, _hOffDiagonal, hFixedCoarse⟩
  obtain ⟨coarseKernel, hfixedY⟩ := hY.fixedCoarseLimit
  refine ⟨coarseKernel, ?_⟩
  intro η hη
  let η' : ℝ := η / (8 * (B + 1))
  have hη' : 0 < η' := by dsimp [η']; positivity
  have hcovComm : ∀ (f g : Ω → ℝ),
      gaussianCovariance P f g = gaussianCovariance P g f := by
    intro f g
    unfold gaussianCovariance
    apply integral_congr_ae
    exact ae_of_all P (fun ω => by ring)
  have hrootCov (i : ι) (root coarse : α → ℂ)
      (hroot : ∀ a ∈ S, root a ∈ K) (hcoarse : ∀ a ∈ S, coarse a ∈ K) :
      ∃ δi : ℝ, 0 < δi ∧ ∀ ε : ℝ, 0 < ε →
        ε ≤ min δi (min ε₀ ε₁) → ∀ b : Bool, ∀ a ∈ S,
        |gaussianCovariance P
            (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (coarse a))
            (fun ω => if b then Y ω ε (root a) else Z ω ε (root a)) -
          coarseKernel (scale i) (root a) (coarse a)| < 2 * η' := by
    obtain ⟨δY, hδY, hYlimit⟩ := hfixedY K hK hKU (scale i)
      (le_trans (hscale i) (min_le_left _ _)) η' hη'
    obtain ⟨δZ, hδZ, hZlimit⟩ := hFixedCoarse K hK hKU (scale i)
      (hscale i) η' hη'
    let δi : ℝ := min δY δZ
    have hδi : 0 < δi := lt_min hδY hδZ
    refine ⟨δi, hδi, ?_⟩
    intro ε hε hεcut b a ha
    have hεY : ε ≤ min δY ε₀ := by
      apply le_min
      · exact (hεcut.trans (min_le_left _ _)).trans (min_le_left _ _)
      · exact le_trans (hεcut.trans (min_le_right _ _)) (min_le_left _ _)
    have hεZ : ε ≤ min δZ (min ε₀ ε₁) := by
      apply le_min
      · exact (hεcut.trans (min_le_left _ _)).trans (min_le_right _ _)
      · exact hεcut.trans (min_le_right _ _)
    have hYlim := hYlimit ε hε hεY (root a) (hroot a ha) (coarse a) (hcoarse a ha)
    have hYlim' : |gaussianCovariance P
          (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (coarse a))
          (fun ω => Y ω ε (root a)) - coarseKernel (scale i) (root a) (coarse a)| < η' := by
      simpa only [hcovComm] using hYlim
    cases b
    · have hZlim := hZlimit ε hε hεZ (root a) (hroot a ha) (coarse a) (hcoarse a ha)
      have hZlim' : |gaussianCovariance P
            (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (coarse a))
            (fun ω => Z ω ε (root a)) - gaussianCovariance P
              (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (coarse a))
              (fun ω => Y ω ε (root a))| < η' := by
        simpa only [hcovComm] using hZlim
      calc
        |gaussianCovariance P (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (coarse a))
              (fun ω => Z ω ε (root a)) - coarseKernel (scale i) (root a) (coarse a)|
            = |(gaussianCovariance P
                  (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (coarse a))
                  (fun ω => Z ω ε (root a)) - gaussianCovariance P
                    (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (coarse a))
                    (fun ω => Y ω ε (root a))) +
                (gaussianCovariance P
                  (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (coarse a))
                  (fun ω => Y ω ε (root a)) - coarseKernel (scale i) (root a) (coarse a))| := by
                    congr 1
                    ring
        _ ≤ |gaussianCovariance P
                (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (coarse a))
                (fun ω => Z ω ε (root a)) - gaussianCovariance P
                  (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (coarse a))
                  (fun ω => Y ω ε (root a))| +
              |gaussianCovariance P
                  (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (coarse a))
                  (fun ω => Y ω ε (root a)) - coarseKernel (scale i) (root a) (coarse a)| :=
                    abs_add_le _ _
        _ < 2 * η' := by linarith
    · exact lt_trans hYlim' (by linarith [hη'])
  have hlocal (i : ι) : ∃ δi : ℝ, 0 < δi ∧
      ∀ ε ε' : ℝ, 0 < ε → ε ≤ min δi (min ε₀ ε₁) →
        0 < ε' → ε' ≤ min δi (min ε₀ ε₁) →
        ∀ γ ∈ Γ, ∀ a ∈ S,
          |γ * gaussianCovariance P
                (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
                (fun ω => if b₁ then Y ω ε (rootX a) else Z ω ε (rootX a)) +
            γ * gaussianCovariance P
                (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
                (fun ω => if b₂ then Y ω ε' (rootY a) else Z ω ε' (rootY a)) -
            (γ * coarseKernel (scale i) (rootX a) (center a i) +
              γ * coarseKernel (scale i) (rootY a) (center a i))| < η := by
    obtain ⟨δ₁, hδ₁, hfirst⟩ := hrootCov i rootX (fun a => center a i)
      hrootX (fun a ha => hcenter a ha i)
    obtain ⟨δ₂, hδ₂, hsecond⟩ := hrootCov i rootY (fun a => center a i)
      hrootY (fun a ha => hcenter a ha i)
    let δi : ℝ := min δ₁ δ₂
    have hδi : 0 < δi := lt_min hδ₁ hδ₂
    refine ⟨δi, hδi, ?_⟩
    intro ε ε' hε hεcut hε' hε'cut γ hγ a ha
    have hεfirst : ε ≤ min δ₁ (min ε₀ ε₁) := by
      apply le_min
      · exact (hεcut.trans (min_le_left _ _)).trans (min_le_left _ _)
      · exact hεcut.trans (min_le_right _ _)
    have hε'second : ε' ≤ min δ₂ (min ε₀ ε₁) := by
      apply le_min
      · exact (hε'cut.trans (min_le_left _ _)).trans (min_le_right _ _)
      · exact hε'cut.trans (min_le_right _ _)
    have hcov₁ := hfirst ε hε hεfirst b₁ a ha
    have hcov₂ := hsecond ε' hε' hε'second b₂ a ha
    have hγbound : |γ| ≤ B := hΓ γ hγ
    let c₁ : ℝ := gaussianCovariance P
      (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
      (fun ω => if b₁ then Y ω ε (rootX a) else Z ω ε (rootX a))
    let c₂ : ℝ := gaussianCovariance P
      (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
      (fun ω => if b₂ then Y ω ε' (rootY a) else Z ω ε' (rootY a))
    let k₁ : ℝ := coarseKernel (scale i) (rootX a) (center a i)
    let k₂ : ℝ := coarseKernel (scale i) (rootY a) (center a i)
    have hc₁ : |c₁ - k₁| < 2 * η' := by simpa [c₁, k₁] using hcov₁
    have hc₂ : |c₂ - k₂| < 2 * η' := by simpa [c₂, k₂] using hcov₂
    have hsumBound :
        |γ * (c₁ - k₁)| + |γ * (c₂ - k₂)| ≤
          4 * B * η' := by
      calc
        _ = |γ| * |c₁ - k₁| + |γ| * |c₂ - k₂| := by rw [abs_mul, abs_mul]
        _ ≤ |γ| * (2 * η') + |γ| * (2 * η') := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left hc₁.le (abs_nonneg γ))
                (mul_le_mul_of_nonneg_left hc₂.le (abs_nonneg γ))
        _ ≤ B * (2 * η') + B * (2 * η') := by
              gcongr
        _ = 4 * B * η' := by ring
    have hηeq : η' * (8 * (B + 1)) = η := by
      dsimp [η']
      field_simp
    have hsmall : 4 * B * η' < η := by
      rw [← hηeq]
      nlinarith [mul_pos hη' (show 0 < B + 2 by linarith)]
    have hsum : |γ * (c₁ - k₁) + γ * (c₂ - k₂)| ≤
        |γ * (c₁ - k₁)| + |γ * (c₂ - k₂)| := abs_add_le _ _
    calc
      |γ * c₁ + γ * c₂ - (γ * k₁ + γ * k₂)|
          = |γ * (c₁ - k₁) + γ * (c₂ - k₂)| := by congr 1; ring
      _ ≤ |γ * (c₁ - k₁)| + |γ * (c₂ - k₂)| := hsum
      _ ≤ 4 * B * η' := hsumBound
      _ < η := hsmall

  choose δi hδi hshift using hlocal
  obtain ⟨i₀, hmin⟩ := Finite.exists_min (fun i : ι => δi i)
  let δ : ℝ := δi i₀
  have hδ : 0 < δ := hδi i₀
  refine ⟨δ, hδ, ?_⟩
  intro ε ε' hε hεcut hε' hε'cut γ hγ a ha i
  have hδle : δ ≤ δi i := hmin i
  have hεcut' : ε ≤ min (δi i) (min ε₀ ε₁) := by
    apply le_min
    · exact (hεcut.trans (min_le_left _ _)).trans hδle
    · exact hεcut.trans (min_le_right _ _)
  have hε'cut' : ε' ≤ min (δi i) (min ε₀ ε₁) := by
    apply le_min
    · exact (hε'cut.trans (min_le_left _ _)).trans hδle
    · exact hε'cut.trans (min_le_right _ _)
  have h := hshift i ε ε' hε hεcut' hε' hε'cut' γ hγ a ha
  exact h

/-- The finite-barrier rectangle probabilities for any mixed pair of regularization families
converge uniformly to one common coarse limit. This is the off-diagonal finite-scale convergence
input to the growing-barrier mixed-cutoff Cauchy argument. -/
theorem compatible_finite_coarse_double_root_barrier_probability_tendsto_uniformly
    {Ω α : Type*} {n : ℕ} [MeasurableSpace Ω] [Nonempty (Fin n)]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    (hYZ : IsCompatibleAdmissibleRegularizations P U ε₀ ε₁ Y Z)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (S : Set α) (rootX rootY : α → ℂ)
    (hrootX : ∀ a ∈ S, rootX a ∈ K) (hrootY : ∀ a ∈ S, rootY a ∈ K)
    (scale : Fin n → ℕ) (center : α → Fin n → ℂ)
    (hcenter : ∀ a ∈ S, ∀ i, center a i ∈ K)
    (hscale : ∀ i, Real.exp (-(scale i : ℝ)) ≤ min ε₀ ε₁)
    (hv : ∀ a ∈ S, ∀ i, 1 ≤ gaussianVariance P
      (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i)))
    (b₁ b₂ : Bool) (barrier : Fin n → ℝ) (Γ : Set ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hΓ : ∀ γ ∈ Γ, |γ| ≤ B) :
    ∃ coarseKernel : ℕ → ℂ → ℂ → ℝ, ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε ε' : ℝ,
        0 < ε → ε ≤ min δ (min ε₀ ε₁) →
        0 < ε' → ε' ≤ min δ (min ε₀ ε₁) →
        ∀ γ ∈ Γ, ∀ a ∈ S,
          |(∫ ω, gaussianRectangleIndicator
                (fun ω i => Y ω (Real.exp (-(scale i : ℝ))) (center a i)) barrier
                (fun i => γ * gaussianCovariance P
                    (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
                    (fun ω => if b₁ then Y ω ε (rootX a) else Z ω ε (rootX a)) +
                  γ * gaussianCovariance P
                    (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
                    (fun ω => if b₂ then Y ω ε' (rootY a) else Z ω ε' (rootY a))) ω ∂P) -
            (∫ ω, gaussianRectangleIndicator
                (fun ω i => Y ω (Real.exp (-(scale i : ℝ))) (center a i)) barrier
                (fun i => γ * coarseKernel (scale i) (rootX a) (center a i) +
                  γ * coarseKernel (scale i) (rootY a) (center a i)) ω ∂P)| < η := by
  let q : α → Fin n → ℝ × ℂ := fun a i =>
    (Real.exp (-(scale i : ℝ)), center a i)
  let W : α → Ω → Fin n → ℝ := fun a ω i => Y ω (q a i).1 (q a i).2
  have hW : ∀ a ∈ S, IsCenteredJointlyGaussian P (W a) := by
    intro a ha
    change IsCenteredJointlyGaussian P
      (fun ω i => Y ω (q a i).1 (q a i).2)
    apply hY.gaussian n (q a)
    intro i
    exact ⟨Real.exp_pos _, le_trans (hscale i) (min_le_left _ _)⟩
  have hshift := compatible_finite_coarse_two_root_shift_tendsto_uniformly
    P U dens ε₀ ε₁ Y Z hY hZ hYZ K hK hKU S rootX rootY hrootX hrootY
    scale center hcenter hscale b₁ b₂ Γ B hB hΓ
  obtain ⟨coarseKernel, hshift⟩ := hshift
  let c : ℝ → ℝ → ℝ → α → Fin n → ℝ := fun ε ε' γ a i =>
    γ * gaussianCovariance P (fun ω => W a ω i)
        (fun ω => if b₁ then Y ω ε (rootX a) else Z ω ε (rootX a)) +
      γ * gaussianCovariance P (fun ω => W a ω i)
        (fun ω => if b₂ then Y ω ε' (rootY a) else Z ω ε' (rootY a))
  let d : ℝ → α → Fin n → ℝ := fun γ a i =>
    γ * coarseKernel (scale i) (rootX a) (center a i) +
      γ * coarseKernel (scale i) (rootY a) (center a i)
  have hcoord : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ ε ε' : ℝ, 0 < ε → ε ≤ δ → 0 < ε' → ε' ≤ δ →
        ∀ γ ∈ Γ, ∀ a ∈ S, ∀ i, |c ε ε' γ a i - d γ a i| < η := by
    intro η hη
    obtain ⟨δ₀, hδ₀, hshift'⟩ := hshift η hη
    let δ : ℝ := min δ₀ (min ε₀ ε₁)
    have hδ : 0 < δ := lt_min hδ₀ (lt_min hY.cutoffPositive hZ.cutoffPositive)
    refine ⟨δ, hδ, ?_⟩
    intro ε ε' hε hεcut hε' hε'cut γ hγ a ha i
    have hε'cut' : ε ≤ min δ₀ (min ε₀ ε₁) := by
      apply le_min
      · exact hεcut.trans (min_le_left _ _)
      · exact hεcut.trans (min_le_right _ _)
    have hε''cut' : ε' ≤ min δ₀ (min ε₀ ε₁) := by
      apply le_min
      · exact hε'cut.trans (min_le_left _ _)
      · exact hε'cut.trans (min_le_right _ _)
    have h := hshift' ε ε' hε hε'cut' hε' hε''cut' γ hγ a ha i
    simpa [c, d, W, q] using h
  have hprob := finite_gaussian_rectangle_probability_two_shift_tendsto_uniformly
    P Γ S W hW barrier hv c d hcoord
  refine ⟨coarseKernel, ?_⟩
  intro η hη
  obtain ⟨δ₀, hδ₀, hprob'⟩ := hprob η hη
  let δ : ℝ := min δ₀ (min ε₀ ε₁)
  have hδ : 0 < δ := lt_min hδ₀ (lt_min hY.cutoffPositive hZ.cutoffPositive)
  refine ⟨δ, hδ, ?_⟩
  intro ε ε' hε hεcut hε' hε'cut γ hγ a ha
  have hεδ : ε ≤ δ₀ := by
    have hε' : ε ≤ δ := hεcut.trans (min_le_left δ (min ε₀ ε₁))
    exact hε'.trans (min_le_left δ₀ (min ε₀ ε₁))
  have hε'δ : ε' ≤ δ₀ := by
    have hε'' : ε' ≤ δ := hε'cut.trans (min_le_left δ (min ε₀ ε₁))
    exact hε''.trans (min_le_left δ₀ (min ε₀ ε₁))
  have h := hprob' ε ε' hε hεδ hε' hε'δ γ hγ a ha
  simpa [W, q, c, d] using h

/-- On a compact separated chart, every mixed Y/Z off-diagonal covariance has the same limit as
the Y/Y covariance. The two compatibility convergence clauses cover YZ and ZZ directly; the ZY
case follows by covariance symmetry. -/
theorem compatible_mixed_off_diagonal_covariance_tendsto_uniformly
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (_hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    (hYZ : IsCompatibleAdmissibleRegularizations P U ε₀ ε₁ Y Z)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (s : ℝ) (hs : 0 < s)
    (b₁ b₂ : Bool) :
    ∃ H : ℂ → ℂ → ℝ, ContinuousOn (Function.uncurry H) (U ×ˢ U) ∧
      ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
        ∀ ε ε' : ℝ, 0 < ε → ε ≤ min δ (min ε₀ ε₁) →
          0 < ε' → ε' ≤ min δ (min ε₀ ε₁) →
          ∀ x ∈ K, ∀ y ∈ K, s ≤ ‖x - y‖ →
            |gaussianCovariance P
                (fun ω => if b₁ then Y ω ε x else Z ω ε x)
                (fun ω => if b₂ then Y ω ε' y else Z ω ε' y) -
              (Real.log (1 / ‖x - y‖) + H x y)| < η := by
  rcases hYZ with ⟨_hJoint, _hCov, _hCoarse, hOffDiagonal, _hFixedCoarse⟩
  obtain ⟨H, hH, hYoff⟩ := hY.offDiagonalLimit
  refine ⟨H, hH, ?_⟩
  intro η hη
  let η' : ℝ := η / 3
  have hη' : 0 < η' := by dsimp [η']; positivity
  obtain ⟨δY, hδY, hYclose⟩ := hYoff K hK hKU s hs η' hη'
  obtain ⟨δC, hδC, hCclose⟩ := hOffDiagonal K hK hKU s hs η' hη'
  let δ : ℝ := min δY δC
  have hδ : 0 < δ := lt_min hδY hδC
  have hcovComm (f g : Ω → ℝ) :
      gaussianCovariance P f g = gaussianCovariance P g f := by
    unfold gaussianCovariance
    apply integral_congr_ae
    exact ae_of_all P (fun ω => by ring)
  refine ⟨δ, hδ, ?_⟩
  intro ε ε' hε hεcut hε' hε'cut x hx y hy hxy
  have hεY : ε ≤ min δY ε₀ := by
    apply le_min
    · exact (hεcut.trans (min_le_left _ _)).trans (min_le_left _ _)
    · exact le_trans (hεcut.trans (min_le_right _ _)) (min_le_left _ _)
  have hε'Y : ε' ≤ min δY ε₀ := by
    apply le_min
    · exact (hε'cut.trans (min_le_left _ _)).trans (min_le_left _ _)
    · exact le_trans (hε'cut.trans (min_le_right _ _)) (min_le_left _ _)
  have hεC : ε ≤ min δC (min ε₀ ε₁) := by
    apply le_min
    · exact (hεcut.trans (min_le_left _ _)).trans (min_le_right _ _)
    · exact hεcut.trans (min_le_right _ _)
  have hε'C : ε' ≤ min δC (min ε₀ ε₁) := by
    apply le_min
    · exact (hε'cut.trans (min_le_left _ _)).trans (min_le_right _ _)
    · exact hε'cut.trans (min_le_right _ _)
  have hbase : |gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Y ω ε' y) -
      (Real.log (1 / ‖x - y‖) + H x y)| < η' :=
    hYclose ε ε' hε hεY hε' hε'Y x hx y hy hxy
  have hcombine {A B L : ℝ} (hAB : |A - B| < η') (hBL : |B - L| < η') :
      |A - L| < η := by
    calc
      |A - L| = |(A - B) + (B - L)| := by congr 1; ring
      _ ≤ |A - B| + |B - L| := abs_add_le _ _
      _ < η' + η' := add_lt_add hAB hBL
      _ < η := by dsimp [η']; linarith
  cases b₁ <;> cases b₂
  · have hcomp := hCclose ε ε' hε hεC hε' hε'C x hx y hy hxy
    have hcomp' : |gaussianCovariance P (fun ω => Z ω ε x) (fun ω => Z ω ε' y) -
        gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Y ω ε' y)| < η' := hcomp.2
    exact hcombine hcomp' hbase
  · have hcomp := hCclose ε' ε hε' hε'C hε hεC y hy x hx
      (by simpa [norm_sub_rev] using hxy)
    have hcomp' : |gaussianCovariance P (fun ω => Z ω ε x) (fun ω => Y ω ε' y) -
        gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Y ω ε' y)| < η' := by
      simpa only [hcovComm] using hcomp.1
    exact hcombine hcomp' hbase
  · have hcomp := hCclose ε ε' hε hεC hε' hε'C x hx y hy hxy
    have hcomp' : |gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Z ω ε' y) -
        gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Y ω ε' y)| < η' := hcomp.1
    exact hcombine hcomp' hbase
  · exact lt_trans hbase (by dsimp [η']; linarith)

/-- The mixed two-root Wick prefactor converges uniformly to the common GMC kernel on compact
separated spatial sets, for all four choices of Y/Z families and bounded charges. -/
theorem compatible_mixed_off_diagonal_wick_factor_tendsto_uniformly
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    (hYZ : IsCompatibleAdmissibleRegularizations P U ε₀ ε₁ Y Z)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (s : ℝ) (hs : 0 < s)
    (S : Set (ℂ × ℂ)) (hS : IsCompact S)
    (hSxy : ∀ p ∈ S, p.1 ∈ K ∧ p.2 ∈ K ∧ s ≤ ‖p.1 - p.2‖)
    (b₁ b₂ : Bool) (Γ : Set ℝ) (B : ℝ)
    (hΓ : ∀ γ ∈ Γ, |γ| ≤ B) :
    ∃ H : ℂ → ℂ → ℝ, ContinuousOn (Function.uncurry H) (U ×ˢ U) ∧
      ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
        ∀ ε ε' : ℝ, 0 < ε → ε ≤ min δ (min ε₀ ε₁) →
          0 < ε' → ε' ≤ min δ (min ε₀ ε₁) →
          ∀ γ ∈ Γ, ∀ p ∈ S,
            |Real.exp (γ ^ 2 * gaussianCovariance P
                (fun ω => if b₁ then Y ω ε p.1 else Z ω ε p.1)
                (fun ω => if b₂ then Y ω ε' p.2 else Z ω ε' p.2)) -
              Real.exp (γ ^ 2 * (Real.log (1 / ‖p.1 - p.2‖) + H p.1 p.2))| < η := by
  obtain ⟨H, hH, hcovlim⟩ := compatible_mixed_off_diagonal_covariance_tendsto_uniformly
    P U dens ε₀ ε₁ Y Z hY hZ hYZ K hK hKU s hs b₁ b₂
  refine ⟨H, hH, ?_⟩
  intro η hη
  let lim : ℂ × ℂ → ℝ := fun p => Real.log (1 / ‖p.1 - p.2‖) + H p.1 p.2
  have hsep (p : ℂ × ℂ) (hp : p ∈ S) : 0 < ‖p.1 - p.2‖ :=
    lt_of_lt_of_le hs (hSxy p hp).2.2
  have hdist : Continuous fun p : ℂ × ℂ => ‖p.1 - p.2‖ := by fun_prop
  have hinv : ContinuousOn (fun p : ℂ × ℂ => (‖p.1 - p.2‖)⁻¹) S :=
    hdist.continuousOn.inv₀ (fun p hp => ne_of_gt (hsep p hp))
  have harg : ContinuousOn (fun p : ℂ × ℂ => 1 / ‖p.1 - p.2‖) S := by
    simpa [one_div] using hinv
  have hargNe : ∀ p ∈ S, 1 / ‖p.1 - p.2‖ ∈ ({0} : Set ℝ)ᶜ := by
    intro p hp
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt (one_div_pos.mpr (hsep p hp))
  have hlog : ContinuousOn (fun p : ℂ × ℂ => Real.log (1 / ‖p.1 - p.2‖)) S :=
    ContinuousOn.comp' Real.continuousOn_log harg hargNe
  have hHsub : S ⊆ U ×ˢ U := by
    intro p hp
    exact Set.mem_prod.mpr ⟨hKU (hSxy p hp).1, hKU (hSxy p hp).2.1⟩
  have hH' : ContinuousOn (fun p : ℂ × ℂ => H p.1 p.2) S := hH.mono hHsub
  have hlim : ContinuousOn lim S := by exact hlog.add hH'
  have habs : ContinuousOn (fun p => |lim p|) S := hlim.abs
  obtain ⟨R₀, hR₀⟩ := hS.bddAbove_image habs
  let R : ℝ := max 0 R₀
  have hR : 0 ≤ R := le_max_left _ _
  have hlimBound (p : ℂ × ℂ) (hp : p ∈ S) : |lim p| ≤ R := by
    have hmem : |lim p| ∈ (fun p : ℂ × ℂ => |lim p|) '' S := ⟨p, hp, rfl⟩
    exact (hR₀ hmem).trans (le_max_right _ _)
  let D : Set ℝ := Set.Icc (-B) B
  let T : Set ℝ := Set.Icc (-(R + 1)) (R + 1)
  have hD : IsCompact D := isCompact_Icc
  have hT : IsCompact T := isCompact_Icc
  let E : ℝ × ℝ → ℝ := fun z => Real.exp (z.1 ^ 2 * z.2)
  have hE : Continuous E := by fun_prop
  have hET : IsCompact (D ×ˢ T) := hD.prod hT
  have hUC : UniformContinuousOn E (D ×ˢ T) := hET.uniformContinuousOn_of_continuous hE.continuousOn
  obtain ⟨δE, hδE, hmod⟩ := Metric.uniformContinuousOn_iff.mp hUC η hη
  let ηcov : ℝ := min δE 1
  have hηcov : 0 < ηcov := lt_min hδE one_pos
  have hηcovE : ηcov ≤ δE := min_le_left _ _
  have hηcovOne : ηcov ≤ 1 := min_le_right _ _
  obtain ⟨δ, hδ, hcov⟩ := hcovlim ηcov hηcov
  refine ⟨δ, hδ, ?_⟩
  intro ε ε' hε hεcut hε' hε'cut γ hγ p hp
  have hpK := hSxy p hp
  have hcovErr : |gaussianCovariance P
        (fun ω => if b₁ then Y ω ε p.1 else Z ω ε p.1)
        (fun ω => if b₂ then Y ω ε' p.2 else Z ω ε' p.2) - lim p| < ηcov :=
    hcov ε ε' hε hεcut hε' hε'cut p.1 hpK.1 p.2 hpK.2.1 hpK.2.2
  have hgammaD : γ ∈ D := by
    change -B ≤ γ ∧ γ ≤ B
    exact abs_le.mp (hΓ γ hγ)
  have hlimD : lim p ∈ T := by
    change -(R + 1) ≤ lim p ∧ lim p ≤ R + 1
    have hb := abs_le.mp (hlimBound p hp)
    constructor <;> linarith [hR]
  have hcovD : gaussianCovariance P
      (fun ω => if b₁ then Y ω ε p.1 else Z ω ε p.1)
      (fun ω => if b₂ then Y ω ε' p.2 else Z ω ε' p.2) ∈ T := by
    change -(R + 1) ≤ gaussianCovariance P
        (fun ω => if b₁ then Y ω ε p.1 else Z ω ε p.1)
        (fun ω => if b₂ then Y ω ε' p.2 else Z ω ε' p.2) ∧
      gaussianCovariance P (fun ω => if b₁ then Y ω ε p.1 else Z ω ε p.1)
        (fun ω => if b₂ then Y ω ε' p.2 else Z ω ε' p.2) ≤ R + 1
    have hcovAbs : |gaussianCovariance P
        (fun ω => if b₁ then Y ω ε p.1 else Z ω ε p.1)
        (fun ω => if b₂ then Y ω ε' p.2 else Z ω ε' p.2)| ≤ R + 1 := by
      calc
        _ = |(gaussianCovariance P
              (fun ω => if b₁ then Y ω ε p.1 else Z ω ε p.1)
              (fun ω => if b₂ then Y ω ε' p.2 else Z ω ε' p.2) - lim p) + lim p| := by
                congr 1
                ring
        _ ≤ |gaussianCovariance P
              (fun ω => if b₁ then Y ω ε p.1 else Z ω ε p.1)
              (fun ω => if b₂ then Y ω ε' p.2 else Z ω ε' p.2) - lim p| + |lim p| :=
                abs_add_le _ _
        _ ≤ R + 1 := by linarith [hlimBound p hp, hcovErr.le, hηcovOne]
    exact abs_le.mp hcovAbs
  have hpairDist : dist (γ, lim p) (γ, gaussianCovariance P
      (fun ω => if b₁ then Y ω ε p.1 else Z ω ε p.1)
      (fun ω => if b₂ then Y ω ε' p.2 else Z ω ε' p.2)) < δE := by
    have hsecond : dist (lim p) (gaussianCovariance P
        (fun ω => if b₁ then Y ω ε p.1 else Z ω ε p.1)
        (fun ω => if b₂ then Y ω ε' p.2 else Z ω ε' p.2)) < δE := by
      have h' := lt_of_lt_of_le hcovErr hηcovE
      simpa [Real.dist_eq, abs_sub_comm] using h'
    simpa [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)] using hsecond
  have hEclose := hmod (γ, lim p) (Set.mem_prod.mpr ⟨hgammaD, hlimD⟩)
    (γ, gaussianCovariance P
      (fun ω => if b₁ then Y ω ε p.1 else Z ω ε p.1)
      (fun ω => if b₂ then Y ω ε' p.2 else Z ω ε' p.2))
    (Set.mem_prod.mpr ⟨hgammaD, hcovD⟩) hpairDist
  simpa [E, lim, Real.dist_eq, abs_sub_comm] using hEclose


end DOZZ.Proofs
