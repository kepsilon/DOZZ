/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsCompatibleAdmissibleRegularizations
public import DOZZ.GMC.AdmissibleCoarseBarrier
public import DOZZ.GMC.AdmissibleCoarseScaleBarrier
public import DOZZ.GMC.Construction.GMCBarrierCompactTestL1
public import DOZZ.GMC.Construction.FiniteGaussianWickPairTilt
public import DOZZ.GMC.GoodBarrierL2Cauchy
public import DOZZ.GMC.PowerKernelIntegrability

/-! Mixed-cutoff barrier estimates for compatible admissible logarithmic regularizations. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- A mixed pair of fine Wick roots from two compatible admissible regularizations is controlled
by the first regularization's coarse barrier. The cutoff scales and roots may vary independently.
This is the pointwise mixed-kernel estimate used before integrating over the spatial variables. -/
theorem compatible_two_root_wick_pair_good_barrier_power_bound_BarrierCauchyLocalEstimates
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    (hYZ : IsCompatibleAdmissibleRegularizations P U ε₀ ε₁ Y Z)
    (b₁ b₂ : Bool)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ), Real.exp (-(k : ℝ)) ≤ min ε₀ ε₁ →
      ∀ ε δ : ℝ, 0 < ε → ε ≤ min ε₀ ε₁ → ε ≤ Real.exp (-(k : ℝ)) →
        0 < δ → δ ≤ min ε₀ ε₁ → δ ≤ Real.exp (-(k : ℝ)) → ∀ κ : ℝ,
    ∀ x y : ℂ, x ∈ K → y ∈ K →
      ‖x - y‖ ≤ Real.exp (-(k : ℝ)) → 0 < ‖x - y‖ →
      ∀ ρ : ℝ, ρ = max ‖x - y‖ (max ε δ) →
      Real.log (1 / ρ) - 1 < (k : ℝ) →
      ∀ η g a : ℝ, 0 < η → η < 1 → 0 < g → a < 2 * g →
      C < (k : ℝ) → C ≤ η * (k : ℝ) →
      2 * g * C + 1 ≤ η * (2 * g - a) * (k : ℝ) →
      0 ≤ κ →
      g ^ 2 - ((1 - η) ^ 2 * (2 * g - a) ^ 2 / (2 * (1 + η))) ≤ κ →
      ∫⁻ ω, ENNReal.ofReal (Real.exp
          (g * (if b₁ then Y else Z) ω ε x - g ^ 2 / 2 * gaussianVariance P
            (fun ω => (if b₁ then Y else Z) ω ε x))) *
        ENNReal.ofReal (Real.exp
          (g * (if b₂ then Y else Z) ω δ y - g ^ 2 / 2 * gaussianVariance P
            (fun ω => (if b₂ then Y else Z) ω δ y))) *
        Set.indicator {ω | Y ω (Real.exp (-(k : ℝ))) x ≤ a * (k : ℝ)}
          (fun _ => (1 : ℝ≥0∞)) ω ∂P ≤
        ENNReal.ofReal ((Real.exp (g ^ 2 * C +
          ((1 - η) ^ 2 * (2 * g - a) ^ 2 / (2 * (1 + η)))) * ‖x - y‖ ^ (-κ))) := by
  rcases hYZ with ⟨hJoint, hCov, hCoarse, hOffDiagonal, hFixedCoarse⟩
  obtain ⟨Cv, hCv, hvar⟩ := hY.coarseVarianceBound K hK hKU
  obtain ⟨CmY, hCmY, hmixY⟩ := hY.coarseMixedBound K hK hKU
  obtain ⟨CmZ, hCmZ, hmixZ⟩ := hCoarse K hK hKU
  obtain ⟨Cyy, hCyy, hcovYY⟩ := hY.covarianceBound K hK hKU
  obtain ⟨Czz, hCzz, hcovZZ⟩ := hZ.covarianceBound K hK hKU
  obtain ⟨Cyz, hCyz, hcovYZ⟩ := hCov K hK hKU
  let C₀ : ℝ := Cv + CmY + CmZ + Cyy + Czz + Cyz
  have hC₀nonneg : 0 ≤ C₀ := by
    dsimp [C₀]
    positivity
  have hCvC : Cv ≤ C₀ := by dsimp [C₀]; linarith [hCmY, hCmZ, hCyy, hCzz, hCyz]
  have hCmYC : CmY ≤ C₀ := by dsimp [C₀]; linarith [hCv, hCmZ, hCyy, hCzz, hCyz]
  have hCmZC : CmZ ≤ C₀ := by dsimp [C₀]; linarith [hCv, hCmY, hCyy, hCzz, hCyz]
  have hCyyC : Cyy ≤ C₀ := by dsimp [C₀]; linarith [hCv, hCmY, hCmZ, hCzz, hCyz]
  have hCzzC : Czz ≤ C₀ := by dsimp [C₀]; linarith [hCv, hCmY, hCmZ, hCyy, hCyz]
  have hCyzC : Cyz ≤ C₀ := by dsimp [C₀]; linarith [hCv, hCmY, hCmZ, hCyy, hCzz]
  refine ⟨C₀, hC₀nonneg, ?_⟩
  intro k hkcut ε δ hε hεcut₀ hεcut hδ hδcut₁ hδcut κ
    x y hx hy hxy hxypos ρ hρdef hfloor
  have hrhoCut : ρ ≤ Real.exp (-(k : ℝ)) := by
    rw [hρdef]
    exact max_le hxy (max_le hεcut hδcut)
  have hrhoPos : 0 < ρ := by
    rw [hρdef]
    have hεδ : 0 < max ε δ := lt_of_lt_of_le hε (le_max_left _ _)
    exact lt_of_lt_of_le hεδ (le_max_right _ _)
  have hrhoLeOne : ρ ≤ 1 :=
    hrhoCut.trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg k)))
  have hdistLeRho : ‖x - y‖ ≤ ρ := by
    rw [hρdef]
    exact le_max_left _ _
  let r : ℝ := Real.exp (-(k : ℝ))
  let q : Fin 3 → Bool × ℝ × ℂ := fun i =>
    if i = 0 then (true, r, x) else if i = 1 then (b₁, ε, x) else (b₂, δ, y)
  let V : Ω → Fin 3 → ℝ := fun ω i =>
    if (q i).1 then Y ω (q i).2.1 (q i).2.2 else Z ω (q i).2.1 (q i).2.2
  have hV : IsCenteredJointlyGaussian P V := by
    apply hJoint 3 q
    intro i
    fin_cases i
    · exact ⟨Real.exp_pos _, hkcut⟩
    · exact ⟨hε, hεcut₀⟩
    · exact ⟨hδ, hδcut₁⟩
  have hvarV : |gaussianVariance P (fun ω => V ω 0) - (k : ℝ)| ≤ C₀ := by
    have h := hvar k (le_trans hkcut (min_le_left _ _)) x hx
    have h' : |gaussianVariance P (fun ω => V ω 0) - (k : ℝ)| ≤ Cv := by
      simpa [V, q, r] using h
    exact h'.trans hCvC
  have hcovV₁ : |gaussianCovariance P (fun ω => V ω 0)
      (fun ω => V ω 1) - (k : ℝ)| ≤ C₀ := by
    cases b₁ with
    | false =>
        have hεcutZ : ε ≤ min ε₁ r := le_min
          (le_trans hεcut₀ (min_le_right _ _)) hεcut
        have h := hmixZ k (le_trans hkcut (min_le_left _ _)) ε hε hεcutZ x hx
        have h' : |gaussianCovariance P (fun ω => V ω 0)
            (fun ω => V ω 1) - (k : ℝ)| ≤ CmZ := by
          simpa [V, q, r] using h
        exact h'.trans hCmZC
    | true =>
        have h := hmixY k (le_trans hkcut (min_le_left _ _)) ε hε hεcut x hx
        have h' : |gaussianCovariance P (fun ω => V ω 0)
            (fun ω => V ω 1) - (k : ℝ)| ≤ CmY := by
          simpa [V, q, r] using h
        exact h'.trans hCmYC
  have hgeom : max ‖x - y‖ (max r δ) = r := by
    rw [max_eq_left hδcut, max_eq_right hxy]
  have hlog : Real.log (1 / max ‖x - y‖ (max r δ)) = (k : ℝ) := by
    rw [hgeom]
    simp [r]
  have hcovV₂ : |gaussianCovariance P (fun ω => V ω 0)
      (fun ω => V ω 2) - (k : ℝ)| ≤ C₀ := by
    cases b₂ with
    | false =>
        have h := hcovYZ r δ (Real.exp_pos _) (le_trans hkcut (min_le_left _ _))
          hδ (le_trans hδcut₁ (min_le_right _ _)) x hx y hy
        have h' : |gaussianCovariance P (fun ω => V ω 0)
            (fun ω => V ω 2) - (k : ℝ)| ≤ Cyz := by
          have hbound : |gaussianCovariance P (fun ω => V ω 0)
              (fun ω => V ω 2) - Real.log (1 / max ‖x - y‖ (max r δ))| ≤ Cyz := by
            simpa [V, q, r] using h
          rw [hlog] at hbound
          exact hbound
        exact h'.trans hCyzC
    | true =>
        have h := hcovYY r δ (Real.exp_pos _) (le_trans hkcut (min_le_left _ _))
          hδ (le_trans hδcut₁ (min_le_left _ _)) x hx y hy
        have h' : |gaussianCovariance P (fun ω => V ω 0)
            (fun ω => V ω 2) - (k : ℝ)| ≤ Cyy := by
          have hbound : |gaussianCovariance P (fun ω => V ω 0)
              (fun ω => V ω 2) - Real.log (1 / max ‖x - y‖ (max r δ))| ≤ Cyy := by
            simpa [V, q, r] using h
          rw [hlog] at hbound
          exact hbound
        exact h'.trans hCyyC
  have hcovComm (f g : Ω → ℝ) :
      gaussianCovariance P f g = gaussianCovariance P g f := by
    unfold gaussianCovariance
    apply integral_congr_ae
    exact ae_of_all P (fun ω => by ring)
  have hcovRoot : gaussianCovariance P (fun ω => V ω 1)
      (fun ω => V ω 2) ≤ Real.log (1 / ρ) + C₀ := by
    have h' : |gaussianCovariance P (fun ω => V ω 1)
        (fun ω => V ω 2) - Real.log (1 / ρ)| ≤ C₀ := by
      cases b₁ with
      | true =>
        cases b₂ with
        | true =>
          have h := hcovYY ε δ hε (le_trans hεcut₀ (min_le_left _ _))
            hδ (le_trans hδcut₁ (min_le_left _ _)) x hx y hy
          have h' : |gaussianCovariance P (fun ω => V ω 1)
              (fun ω => V ω 2) - Real.log (1 / ρ)| ≤ Cyy := by
            simpa [V, q, hρdef] using h
          exact h'.trans hCyyC
        | false =>
          have h := hcovYZ ε δ hε (le_trans hεcut₀ (min_le_left _ _))
            hδ (le_trans hδcut₁ (min_le_right _ _)) x hx y hy
          have h' : |gaussianCovariance P (fun ω => V ω 1)
              (fun ω => V ω 2) - Real.log (1 / ρ)| ≤ Cyz := by
            simpa [V, q, hρdef] using h
          exact h'.trans hCyzC
      | false =>
        cases b₂ with
        | true =>
          have h := hcovYZ δ ε hδ (le_trans hδcut₁ (min_le_left _ _))
            hε (le_trans hεcut₀ (min_le_right _ _)) y hy x hx
          have h' : |gaussianCovariance P (fun ω => V ω 1)
              (fun ω => V ω 2) - Real.log (1 / ρ)| ≤ Cyz := by
            simpa [V, q, hρdef, hcovComm, norm_sub_rev, max_comm] using h
          exact h'.trans hCyzC
        | false =>
          have h := hcovZZ ε δ hε (le_trans hεcut₀ (min_le_right _ _))
            hδ (le_trans hδcut₁ (min_le_right _ _)) x hx y hy
          have h' : |gaussianCovariance P (fun ω => V ω 1)
              (fun ω => V ω 2) - Real.log (1 / ρ)| ≤ Czz := by
            simpa [V, q, hρdef] using h
          exact h'.trans hCzzC
    have hupper := (abs_le.mp h').2
    linarith
  intro η g a hη hη1 hg hag hCk hCeta hgap hκ hκexp
  have hkpos : 0 < (k : ℝ) := lt_of_le_of_lt hC₀nonneg hCk
  have hpair := finite_gaussian_wick_pair_good_barrier_power_bound P V hV
    1 2 0 (by decide) g a C₀ η (k : ℝ) ‖x - y‖ ρ κ hg hag hkpos hη hη1
    hCeta hgap hvarV hcovV₁ hcovV₂ hrhoPos hrhoLeOne hxypos hdistLeRho hcovRoot hfloor
    hκ hκexp
  cases b₁ <;> cases b₂ <;> simpa [V, q, r] using hpair


/-- A bounded nonnegative continuous spatial test preserves local integrability of the barrier
kernel. This is the spatial majorant used to integrate the mixed pair estimate over a compact
chart; the singularity exponent must remain strictly below the planar dimension. -/
theorem admissible_barrier_spatial_power_integrable
    (K : Set ℂ) (hK : IsCompact K) (f : ℂ → ℝ)
    (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (B κ : ℝ) (hB : 0 ≤ B) (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∫⁻ p in K ×ˢ K,
        ENNReal.ofReal (B * f p.1 * f p.2 * ‖p.1 - p.2‖ ^ (-κ))
          ∂(volume.prod volume) ≤ C := by
  have hkernel := complex_norm_pair_neg_rpow_lintegral_isCompact K hK κ hκ hκ2
  obtain ⟨C₀, hC₀, hpair⟩ := hkernel
  let F : ℂ × ℂ → ℝ := fun p => B * f p.1 * f p.2
  have hFcont : Continuous F := by
    dsimp [F]
    exact continuous_const.mul (hf.comp continuous_fst) |>.mul (hf.comp continuous_snd)
  have hprod : IsCompact (K ×ˢ K) := hK.prod hK
  have habs : ContinuousOn (fun p : ℂ × ℂ => |F p|) (K ×ˢ K) :=
    hFcont.abs.continuousOn
  obtain ⟨R, hbound⟩ := hprod.bddAbove_image habs
  let R' : ℝ := max 0 R
  have hR' : 0 ≤ R' := le_max_left _ _
  have hFbound (p : ℂ × ℂ) (hp : p ∈ K ×ˢ K) : |F p| ≤ R' := by
    have hp' : |F p| ∈ (fun q : ℂ × ℂ => |F q|) '' (K ×ˢ K) := ⟨p, hp, rfl⟩
    exact (hbound hp').trans (le_max_right _ _)
  have hFnonneg (p : ℂ × ℂ) : 0 ≤ F p := by
    dsimp [F]
    exact mul_nonneg (mul_nonneg hB (hf0 p.1)) (hf0 p.2)
  have hpoint (p : ℂ × ℂ) (hp : p ∈ K ×ˢ K) :
      ENNReal.ofReal (F p * ‖p.1 - p.2‖ ^ (-κ)) ≤
        ENNReal.ofReal R' * ENNReal.ofReal (‖p.1 - p.2‖ ^ (-κ)) := by
    rw [← ENNReal.ofReal_mul hR']
    apply ENNReal.ofReal_le_ofReal
    calc
      F p * ‖p.1 - p.2‖ ^ (-κ) ≤ R' * ‖p.1 - p.2‖ ^ (-κ) :=
        mul_le_mul_of_nonneg_right (by
          have h := hFbound p hp
          rw [abs_of_nonneg (hFnonneg p)] at h
          exact h) (Real.rpow_nonneg (norm_nonneg _) _)
      _ = R' * ‖p.1 - p.2‖ ^ (-κ) := rfl
  let J : ℂ × ℂ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (F p * ‖p.1 - p.2‖ ^ (-κ))
  let G : ℂ × ℂ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal R' * ENNReal.ofReal (‖p.1 - p.2‖ ^ (-κ))
  have hJle : ∀ᵐ p : ℂ × ℂ ∂(volume.prod volume), p ∈ K ×ˢ K → J p ≤ G p := by
    filter_upwards [] with p
    intro hp
    exact hpoint p hp
  have hsing := setLIntegral_mono_ae' (hK.measurableSet.prod hK.measurableSet) hJle
  have hscale :
      (∫⁻ p in K ×ˢ K, G p ∂(volume.prod volume)) ≤ ENNReal.ofReal R' * C₀ := by
    calc
      _ = ENNReal.ofReal R' *
          (∫⁻ p in K ×ˢ K,
            ENNReal.ofReal (‖p.1 - p.2‖ ^ (-κ)) ∂(volume.prod volume)) := by
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal R' * C₀ := by
        simpa [mul_comm] using mul_le_mul_left hpair (ENNReal.ofReal R')
  refine ⟨ENNReal.ofReal R' * C₀, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC₀, ?_⟩
  calc
    _ = ∫⁻ p in K ×ˢ K, J p ∂(volume.prod volume) := by
      apply setLIntegral_congr_fun (hK.measurableSet.prod hK.measurableSet)
      intro p hp
      rfl
    _ ≤ ∫⁻ p in K ×ˢ K, G p ∂(volume.prod volume) := hsing
    _ ≤ ENNReal.ofReal R' * C₀ := hscale

/-- Integrate a pointwise mixed-cutoff power bound against a nonnegative compact-chart test.
The set `S` may be one annulus in a scale decomposition; its contribution is controlled by the
integrable planar Riesz kernel on the entire compact chart. -/
theorem admissible_barrier_spatial_integral_bound_of_pointwise
    (K : Set ℂ) (hK : IsCompact K) (f : ℂ → ℝ)
    (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (S : Set (ℂ × ℂ)) (hS : MeasurableSet S) (hSK : S ⊆ K ×ˢ K)
    (W : ℂ × ℂ → ℝ≥0∞) (B κ : ℝ) (hB : 0 ≤ B)
    (hκ : 0 < κ) (hκ2 : κ < 2)
    (hW : ∀ p ∈ S, W p ≤ ENNReal.ofReal (B * ‖p.1 - p.2‖ ^ (-κ))) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∫⁻ p in S, ENNReal.ofReal (f p.1 * f p.2) * W p
        ∂(volume.prod volume) ≤ C := by
  obtain ⟨C, hC, hkernel⟩ :=
    admissible_barrier_spatial_power_integrable K hK f hf hf0 B κ hB hκ hκ2
  let target : ℂ × ℂ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (B * f p.1 * f p.2 * ‖p.1 - p.2‖ ^ (-κ))
  have hpoint (p : ℂ × ℂ) (hp : p ∈ S) :
      ENNReal.ofReal (f p.1 * f p.2) * W p ≤ target p := by
    have hfprod : 0 ≤ f p.1 * f p.2 := mul_nonneg (hf0 p.1) (hf0 p.2)
    calc
      ENNReal.ofReal (f p.1 * f p.2) * W p ≤
          ENNReal.ofReal (f p.1 * f p.2) *
            ENNReal.ofReal (B * ‖p.1 - p.2‖ ^ (-κ)) :=
        by simpa [mul_comm] using
          mul_le_mul_left (hW p hp) (ENNReal.ofReal (f p.1 * f p.2))
      _ = ENNReal.ofReal
          ((f p.1 * f p.2) * (B * ‖p.1 - p.2‖ ^ (-κ))) :=
        (ENNReal.ofReal_mul hfprod).symm
      _ = target p := by
        congr 1
        ring
  have hSle :
      ∫⁻ p in S, ENNReal.ofReal (f p.1 * f p.2) * W p
        ∂(volume.prod volume) ≤
      ∫⁻ p in S, target p ∂(volume.prod volume) :=
    setLIntegral_mono' hS hpoint
  have hKK : IsCompact (K ×ˢ K) := hK.prod hK
  have hKKmeas : MeasurableSet (K ×ˢ K) := hKK.measurableSet
  have htargetRestrict :
      ∫⁻ p in S, target p ∂(volume.prod volume) ≤
      ∫⁻ p in K ×ˢ K, target p ∂(volume.prod volume) := by
    rw [← lintegral_indicator hS, ← lintegral_indicator hKKmeas]
    apply lintegral_mono
    intro p
    by_cases hp : p ∈ S
    · have hpKK : p ∈ K ×ˢ K := hSK hp
      simp [hp, hpKK]
    · by_cases hpKK : p ∈ K ×ˢ K
      · simp [hp, hpKK]
      · simp [hp, hpKK]
  exact ⟨C, hC, hSle.trans (htargetRestrict.trans hkernel)⟩

/-- Spatially integrate the near-diagonal mixed Wick-pair estimate for two compatible
admissible regularizations. The covariance constant is uniform over all roots in `K`; the
barrier-good contribution on any measurable scale slice `S` is therefore bounded by one compact
planar Riesz-kernel integral. -/
theorem compatible_two_root_wick_pair_good_barrier_spatial_integral_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    (hYZ : IsCompatibleAdmissibleRegularizations P U ε₀ ε₁ Y Z)
    (b₁ b₂ : Bool)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (k : ℕ) (hkcut : Real.exp (-(k : ℝ)) ≤ min ε₀ ε₁)
    (ε δ : ℝ) (hε : 0 < ε) (hεcut₀ : ε ≤ min ε₀ ε₁)
    (hεcut : ε ≤ Real.exp (-(k : ℝ)))
    (hδ : 0 < δ) (hδcut₁ : δ ≤ min ε₀ ε₁)
    (hδcut : δ ≤ Real.exp (-(k : ℝ)))
    (κ : ℝ) (hκ : 0 < κ) (hκ2 : κ < 2)
    (f : ℂ → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (S : Set (ℂ × ℂ)) (hS : MeasurableSet S) (hSK : S ⊆ K ×ˢ K)
    (hnear : ∀ p ∈ S, ‖p.1 - p.2‖ ≤ Real.exp (-(k : ℝ)))
    (hsep : ∀ p ∈ S, 0 < ‖p.1 - p.2‖)
    (hfloor : ∀ p ∈ S,
      Real.log (1 / max ‖p.1 - p.2‖ (max ε δ)) - 1 < (k : ℝ))
    (η g a : ℝ) (hη : 0 < η) (hη1 : η < 1) (hg : 0 < g)
    (_hga : g < a) (hag : a < 2 * g) :
    ∃ C : ℝ, 0 ≤ C ∧
      (C < (k : ℝ) → C ≤ η * (k : ℝ) →
        2 * g * C + 1 ≤ η * (2 * g - a) * (k : ℝ) →
        g ^ 2 - ((1 - η) ^ 2 * (2 * g - a) ^ 2 / (2 * (1 + η))) ≤ κ →
        ∃ I : ℝ≥0∞, I ≠ ∞ ∧
          ∫⁻ p in S, ENNReal.ofReal (f p.1 * f p.2) *
            (∫⁻ ω, ENNReal.ofReal (Real.exp
                (g * (if b₁ then Y else Z) ω ε p.1 - g ^ 2 / 2 * gaussianVariance P
                  (fun ω => (if b₁ then Y else Z) ω ε p.1))) *
              ENNReal.ofReal (Real.exp
                (g * (if b₂ then Y else Z) ω δ p.2 - g ^ 2 / 2 * gaussianVariance P
                  (fun ω => (if b₂ then Y else Z) ω δ p.2))) *
              Set.indicator {ω | Y ω (Real.exp (-(k : ℝ))) p.1 ≤ a * (k : ℝ)}
                (fun _ => (1 : ℝ≥0∞)) ω ∂P)
              ∂(volume.prod volume) ≤ I) := by
  obtain ⟨C, hC, hpointAll⟩ := compatible_two_root_wick_pair_good_barrier_power_bound_BarrierCauchyLocalEstimates
    P U dens ε₀ ε₁ Y Z hY hZ hYZ b₁ b₂ K hK hKU
  have hpoint := hpointAll k hkcut ε δ hε hεcut₀ hεcut hδ hδcut₁ hδcut κ
  refine ⟨C, hC, ?_⟩
  intro hCk hCη hgap hκexp
  let W : ℂ × ℂ → ℝ≥0∞ := fun p =>
    ∫⁻ ω, ENNReal.ofReal (Real.exp
        (g * (if b₁ then Y else Z) ω ε p.1 - g ^ 2 / 2 * gaussianVariance P
          (fun ω => (if b₁ then Y else Z) ω ε p.1))) *
      ENNReal.ofReal (Real.exp
        (g * (if b₂ then Y else Z) ω δ p.2 - g ^ 2 / 2 * gaussianVariance P
          (fun ω => (if b₂ then Y else Z) ω δ p.2))) *
      Set.indicator {ω | Y ω (Real.exp (-(k : ℝ))) p.1 ≤ a * (k : ℝ)}
        (fun _ => (1 : ℝ≥0∞)) ω ∂P
  let B : ℝ := Real.exp (g ^ 2 * C +
    ((1 - η) ^ 2 * (2 * g - a) ^ 2 / (2 * (1 + η))))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hW : ∀ p ∈ S, W p ≤ ENNReal.ofReal (B * ‖p.1 - p.2‖ ^ (-κ)) := by
    intro p hp
    have hpK := hSK hp
    have hb := hpoint p.1 p.2 hpK.1 hpK.2 (hnear p hp) (hsep p hp)
      (max ‖p.1 - p.2‖ (max ε δ)) rfl (hfloor p hp)
      η g a hη hη1 hg hag hCk hCη hgap (le_of_lt hκ) hκexp
    simpa [W, B] using hb
  obtain ⟨I, hIfin, hI⟩ := admissible_barrier_spatial_integral_bound_of_pointwise
    K hK f hf hf0 S hS hSK W B κ hB hκ hκ2 hW
  exact ⟨I, hIfin, by simpa [W] using hI⟩



end DOZZ.Proofs
