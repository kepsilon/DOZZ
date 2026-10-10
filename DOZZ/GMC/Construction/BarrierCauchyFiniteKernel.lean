/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.BarrierCauchyKernel

/-! Uniform convergence of finite-barrier mixed pair kernels off the spatial diagonal. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs


/-- For two arbitrary compatible admissible regularizations, a finite coarse-barrier mixed
two-root kernel converges uniformly off the spatial diagonal to the same kernel for every choice
of fine-cutoff family. This is the finite-barrier comparison used before removing the growing
barrier tail. -/
theorem compatible_finite_mixed_pair_kernel_tendsto_uniformly
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} [Nonempty (Fin n)]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    (hYZ : IsCompatibleAdmissibleRegularizations P U ε₀ ε₁ Y Z)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (S : Set (ℂ × ℂ)) (hS : IsCompact S) (hSK : S ⊆ K ×ˢ K)
    (s : ℝ) (hs : 0 < s)
    (hsep : ∀ p ∈ S, s ≤ ‖p.1 - p.2‖)
    (scale : Fin n → ℕ)
    (hscale : ∀ i, Real.exp (-(scale i : ℝ)) ≤ min ε₀ ε₁)
    (center : (ℂ × ℂ) → Fin n → ℂ)
    (hcenter : ∀ p ∈ S, ∀ i, center p i ∈ K)
    (hv : ∀ p ∈ S, ∀ i, 1 ≤ gaussianVariance P
      (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center p i)))
    (barrier : Fin n → ℝ) (b₁ b₂ : Bool)
    (Γ : Set ℝ) (B : ℝ) (hB : 0 ≤ B) (hΓ : ∀ γ ∈ Γ, |γ| ≤ B) :
    ∃ H : ℂ → ℂ → ℝ, ContinuousOn (Function.uncurry H) (U ×ˢ U) ∧
    ∃ coarseKernel : ℕ → ℂ → ℂ → ℝ, ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε ε' : ℝ,
        0 < ε → ε ≤ min δ (min ε₀ ε₁) →
        0 < ε' → ε' ≤ min δ (min ε₀ ε₁) →
        ∀ γ ∈ Γ, ∀ p ∈ S,
          |Real.exp (γ ^ 2 * gaussianCovariance P
              (fun ω => if b₁ then Y ω ε p.1 else Z ω ε p.1)
              (fun ω => if b₂ then Y ω ε' p.2 else Z ω ε' p.2)) *
              (∫ ω, gaussianRectangleIndicator
                (fun ω i => Y ω (Real.exp (-(scale i : ℝ))) (center p i)) barrier
                (fun i => γ * gaussianCovariance P
                    (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center p i))
                    (fun ω => if b₁ then Y ω ε p.1 else Z ω ε p.1) +
                  γ * gaussianCovariance P
                    (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center p i))
                    (fun ω => if b₂ then Y ω ε' p.2 else Z ω ε' p.2)) ω ∂P) -
            Real.exp (γ ^ 2 * (Real.log (1 / ‖p.1 - p.2‖) + H p.1 p.2)) *
              (∫ ω, gaussianRectangleIndicator
                (fun ω i => Y ω (Real.exp (-(scale i : ℝ))) (center p i)) barrier
                (fun i => γ * coarseKernel (scale i) p.1 (center p i) +
                  γ * coarseKernel (scale i) p.2 (center p i)) ω ∂P)| < η := by
  obtain ⟨H, hH, hwick⟩ := compatible_mixed_off_diagonal_wick_factor_tendsto_uniformly
    P U dens ε₀ ε₁ Y Z hY hZ hYZ K hK hKU s hs S hS
    (fun p hp => ⟨(hSK hp).1, (hSK hp).2, hsep p hp⟩) b₁ b₂ Γ B hΓ
  have hrootX : ∀ p ∈ S, p.1 ∈ K := fun p hp => (hSK hp).1
  have hrootY : ∀ p ∈ S, p.2 ∈ K := fun p hp => (hSK hp).2
  obtain ⟨coarseKernel, hprob⟩ :=
    compatible_finite_coarse_double_root_barrier_probability_tendsto_uniformly
      P U dens ε₀ ε₁ Y Z hY hZ hYZ K hK hKU S (fun p => p.1) (fun p => p.2)
      hrootX hrootY scale center hcenter hscale hv b₁ b₂ barrier Γ B hB hΓ
  let S' : Set (ℝ × (ℂ × ℂ)) := Γ ×ˢ S
  let limCov : ℂ × ℂ → ℝ := fun p =>
    Real.log (1 / ‖p.1 - p.2‖) + H p.1 p.2
  let F : ℝ → ℝ → ℝ × (ℂ × ℂ) → ℝ := fun ε ε' q =>
    Real.exp (q.1 ^ 2 * gaussianCovariance P
      (fun ω => if b₁ then Y ω ε q.2.1 else Z ω ε q.2.1)
      (fun ω => if b₂ then Y ω ε' q.2.2 else Z ω ε' q.2.2))
  let F₀ : ℝ → ℝ → ℝ × (ℂ × ℂ) → ℝ := fun _ _ q =>
    Real.exp (q.1 ^ 2 * limCov q.2)
  let G : ℝ → ℝ → ℝ × (ℂ × ℂ) → ℝ := fun ε ε' q =>
    ∫ ω, gaussianRectangleIndicator
      (fun ω i => Y ω (Real.exp (-(scale i : ℝ))) (center q.2 i)) barrier
      (fun i => q.1 * gaussianCovariance P
          (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center q.2 i))
          (fun ω => if b₁ then Y ω ε q.2.1 else Z ω ε q.2.1) +
        q.1 * gaussianCovariance P
          (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center q.2 i))
          (fun ω => if b₂ then Y ω ε' q.2.2 else Z ω ε' q.2.2)) ω ∂P
  let G₀ : ℝ → ℝ → ℝ × (ℂ × ℂ) → ℝ := fun _ _ q =>
    ∫ ω, gaussianRectangleIndicator
      (fun ω i => Y ω (Real.exp (-(scale i : ℝ))) (center q.2 i)) barrier
      (fun i => q.1 * coarseKernel (scale i) q.2.1 (center q.2 i) +
        q.1 * coarseKernel (scale i) q.2.2 (center q.2 i)) ω ∂P
  have hSsub : S ⊆ U ×ˢ U := by
    intro p hp
    exact ⟨hKU (hrootX p hp), hKU (hrootY p hp)⟩
  have hdist : Continuous fun p : ℂ × ℂ => ‖p.1 - p.2‖ := by fun_prop
  have hdistpos : ∀ p ∈ S, 0 < ‖p.1 - p.2‖ := by
    intro p hp
    exact lt_of_lt_of_le hs (hsep p hp)
  have hinv : ContinuousOn (fun p : ℂ × ℂ => (‖p.1 - p.2‖)⁻¹) S :=
    hdist.continuousOn.inv₀ (fun p hp => ne_of_gt (hdistpos p hp))
  have harg : ContinuousOn (fun p : ℂ × ℂ => 1 / ‖p.1 - p.2‖) S := by
    simpa [one_div] using hinv
  have hargNe : ∀ p ∈ S, 1 / ‖p.1 - p.2‖ ∈ ({0} : Set ℝ)ᶜ := by
    intro p hp
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt (one_div_pos.mpr (hdistpos p hp))
  have hlog : ContinuousOn (fun p : ℂ × ℂ => Real.log (1 / ‖p.1 - p.2‖)) S :=
    ContinuousOn.comp' Real.continuousOn_log harg hargNe
  have hlimCov : ContinuousOn limCov S := by
    dsimp [limCov]
    have hHcont : ContinuousOn (fun p : ℂ × ℂ => H p.1 p.2) S := by
      change ContinuousOn (Function.uncurry H) S
      exact hH.mono hSsub
    exact hlog.add hHcont
  have hlimAbs : ContinuousOn (fun p : ℂ × ℂ => |limCov p|) S := hlimCov.abs
  obtain ⟨R, hR⟩ := hS.bddAbove_image hlimAbs
  let C : ℝ := max 0 R
  have hC : 0 ≤ C := by dsimp [C]; exact le_max_left _ _
  have hlimCovAbs : ∀ p ∈ S, |limCov p| ≤ C := by
    intro p hp
    have himg : |limCov p| ∈ (fun q : ℂ × ℂ => |limCov q|) '' S := ⟨p, hp, rfl⟩
    exact (hR himg).trans (le_max_right _ _)
  let M : ℝ := Real.exp (B ^ 2 * C)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hF : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ ε ε' : ℝ,
      0 < ε → ε ≤ δ → 0 < ε' → ε' ≤ δ → ∀ q ∈ S',
        |F ε ε' q - F₀ 0 0 q| < η := by
    intro η hη
    obtain ⟨δ, hδ, hclose⟩ := hwick η hη
    refine ⟨min δ (min ε₀ ε₁), lt_min hδ (lt_min hY.cutoffPositive hZ.cutoffPositive), ?_⟩
    intro ε ε' hε hεcut hε' hε'cut q hq
    rcases q with ⟨γ, p⟩
    rcases hq with ⟨hγ, hp⟩
    have h := hclose ε ε' hε (by simpa using hεcut) hε' (by simpa using hε'cut) γ hγ p hp
    simpa [F, F₀, limCov] using h
  have hG : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ ε ε' : ℝ,
      0 < ε → ε ≤ δ → 0 < ε' → ε' ≤ δ → ∀ q ∈ S',
        |G ε ε' q - G₀ 0 0 q| < η := by
    intro η hη
    obtain ⟨δ, hδ, hclose⟩ := hprob η hη
    refine ⟨min δ (min ε₀ ε₁), lt_min hδ (lt_min hY.cutoffPositive hZ.cutoffPositive), ?_⟩
    intro ε ε' hε hεcut hε' hε'cut q hq
    rcases q with ⟨γ, p⟩
    rcases hq with ⟨hγ, hp⟩
    have h := hclose ε ε' hε (by simpa using hεcut) hε' (by simpa using hε'cut) γ hγ p hp
    simpa [G, G₀] using h
  have hF₀ : ∀ q ∈ S', |F₀ 0 0 q| ≤ M := by
    intro q hq
    rcases q with ⟨γ, p⟩
    rcases hq with ⟨hγ, hp⟩
    have hγsq : γ ^ 2 ≤ B ^ 2 := by
      apply sq_le_sq.2
      simpa [abs_of_nonneg hB] using hΓ γ hγ
    have hlimle : limCov p ≤ C := (le_abs_self _).trans (hlimCovAbs p hp)
    have hexp : γ ^ 2 * limCov p ≤ B ^ 2 * C := by
      calc
        γ ^ 2 * limCov p ≤ γ ^ 2 * C :=
          mul_le_mul_of_nonneg_left hlimle (sq_nonneg γ)
        _ ≤ B ^ 2 * C := mul_le_mul_of_nonneg_right hγsq hC
    dsimp [F₀]
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr hexp
  have hG₀ : ∀ q ∈ S', |G₀ 0 0 q| ≤ 1 := by
    intro q hq
    rcases q with ⟨γ, p⟩
    rcases hq with ⟨_hγ, hp⟩
    let W : Ω → Fin n → ℝ := fun ω i => Y ω (Real.exp (-(scale i : ℝ))) (center p i)
    have hW : IsCenteredJointlyGaussian P W := by
      apply hY.gaussian n (fun i => (Real.exp (-(scale i : ℝ)), center p i))
      intro i
      exact ⟨Real.exp_pos _, le_trans (hscale i) (min_le_left _ _)⟩
    simpa [G₀, W] using integral_gaussianRectangleIndicator_abs_le_one P W hW barrier
      (fun i => γ * coarseKernel (scale i) p.1 (center p i) +
        γ * coarseKernel (scale i) p.2 (center p i))
  refine ⟨H, hH, coarseKernel, ?_⟩
  intro η hη
  obtain ⟨δ', hδ', hprod'⟩ := tendsto_uniformlyOn_product_of_tendsto_uniformlyOn
    S' M hM F F₀ G G₀ hF hG hF₀ hG₀ η hη
  refine ⟨δ', hδ', ?_⟩
  intro ε ε' hε hεcut hε' hε'cut γ hγ p hp
  have hεδ : ε ≤ δ' := le_trans hεcut (min_le_left _ _)
  have hε'δ : ε' ≤ δ' := le_trans hε'cut (min_le_left _ _)
  have h := hprod' ε ε' hε hεδ hε' hε'δ (γ, p) ⟨hγ, hp⟩
  simpa [F, F₀, G, G₀, limCov] using h

end DOZZ.Proofs
