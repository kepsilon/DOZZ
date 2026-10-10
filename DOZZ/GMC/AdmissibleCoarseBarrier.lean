/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsAdmissibleLogRegularization
public import DOZZ.GMC.GaussianTailBound

/-! Coarse-scale barrier tails for admissible logarithmic Gaussian regularizations. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- The same-center coarse variance and mixed covariance bounds in an admissible logarithmic
regularization give a uniform one-root barrier tail under a fine-scale Wick tilt. -/
theorem admissible_coarse_barrier_tail_rate
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, Real.exp (-(k : ℝ)) ≤ ε₀ → C < (k : ℝ) →
      ∀ x ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ Real.exp (-(k : ℝ)) →
      ∀ g a : ℝ, 0 < g → g < a → g * C ≤ (a - g) * (k : ℝ) / 2 →
      ∫⁻ ω, ENNReal.ofReal (Real.exp
          (g * Y ω ε x - g ^ 2 / 2 * gaussianVariance P (fun ω => Y ω ε x))) *
        (Set.indicator {ω | a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) x}
          (fun _ => (1 : ℝ≥0∞)) ω) ∂P ≤
        ENNReal.ofReal (Real.exp (-((a - g) ^ 2 * (k : ℝ) / 16))) := by
  obtain ⟨Cv, hCv, hvar⟩ := hY.coarseVarianceBound K hK hKU
  obtain ⟨Cm, hCm, hmix⟩ := hY.coarseMixedBound K hK hKU
  let C : ℝ := max Cv Cm
  have hCnonneg : 0 ≤ C := by dsimp [C]; exact le_trans hCv (le_max_left Cv Cm)
  refine ⟨C, hCnonneg, ?_⟩
  intro k hkcut hCk x hx ε hε hεk g a hg hga hgap
  let p : Fin 2 → ℝ × ℂ := fun i =>
    if i = 0 then (Real.exp (-(k : ℝ)), x) else (ε, x)
  let Z : Ω → Fin 2 → ℝ := fun ω i => Y ω (p i).1 (p i).2
  have hZ : IsCenteredJointlyGaussian P Z := by
    apply hY.gaussian 2 p
    intro i
    fin_cases i
    · simp [p, Real.exp_pos, hkcut]
    · simp [p, hε, le_trans hεk hkcut]
  have hvarZ : |gaussianVariance P (fun ω => Z ω 0) - (k : ℝ)| ≤ C := by
    have h := hvar k hkcut x hx
    have h' : |gaussianVariance P (fun ω => Z ω 0) - (k : ℝ)| ≤ max Cv Cm := by
      simpa [Z, p] using h.trans (le_max_left Cv Cm)
    simpa [C] using h'
  have hcovZ : |gaussianCovariance P (fun ω => Z ω 0)
      (fun ω => Z ω 1) - (k : ℝ)| ≤ C := by
    have h := hmix k hkcut ε hε hεk x hx
    have h' : |gaussianCovariance P (fun ω => Z ω 0)
        (fun ω => Z ω 1) - (k : ℝ)| ≤ max Cv Cm := by
      simpa [Z, p] using h.trans (le_max_right Cv Cm)
    simpa [C] using h'
  have hk : 0 < (k : ℝ) := lt_of_le_of_lt hCnonneg hCk
  have hbound := finite_gaussian_tilt_coarse_barrier_tail_rate P Z hZ
    1 0 (k : ℝ) g a C hg hga hk
    hCk hvarZ hcovZ hgap
  simpa [Z, p] using hbound


/-- The admissibility covariance estimates give a direct spatial power bound for a pair of fine
Wick roots on the good coarse barrier. This is the finite-cutoff mixed-pair estimate used in the
circle-average GMC Cauchy argument. -/
theorem admissible_two_root_wick_pair_good_barrier_power_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (x y : ℂ) (hx : x ∈ K) (hy : y ∈ K)
    (k : ℕ) (hkcut : Real.exp (-(k : ℝ)) ≤ ε₀)
    (hxy : ‖x - y‖ ≤ Real.exp (-(k : ℝ)))
    (ε δ : ℝ) (hε : 0 < ε) (hεcut : ε ≤ Real.exp (-(k : ℝ)))
    (hδ : 0 < δ) (hδcut : δ ≤ Real.exp (-(k : ℝ)))
    (ρ : ℝ) (hρdef : ρ = max ‖x - y‖ (max ε δ))
    (hfloor : Real.log (1 / ρ) - 1 < (k : ℝ))
    (hxypos : 0 < ‖x - y‖) (κ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η g a : ℝ, 0 < η → η < 1 → 0 < g → a < 2 * g →
      C < (k : ℝ) → C ≤ η * (k : ℝ) →
      2 * g * C + 1 ≤ η * (2 * g - a) * (k : ℝ) →
      0 ≤ κ →
      g ^ 2 - ((1 - η) ^ 2 * (2 * g - a) ^ 2 / (2 * (1 + η))) ≤ κ →
      ∫⁻ ω, ENNReal.ofReal (Real.exp
          (g * Y ω ε x - g ^ 2 / 2 * gaussianVariance P (fun ω => Y ω ε x))) *
        ENNReal.ofReal (Real.exp
          (g * Y ω δ y - g ^ 2 / 2 * gaussianVariance P (fun ω => Y ω δ y))) *
        Set.indicator {ω | Y ω (Real.exp (-(k : ℝ))) x ≤ a * (k : ℝ)}
          (fun _ => (1 : ℝ≥0∞)) ω ∂P ≤
        ENNReal.ofReal ((Real.exp (g ^ 2 * C +
          ((1 - η) ^ 2 * (2 * g - a) ^ 2 / (2 * (1 + η)))) * ‖x - y‖ ^ (-κ))) := by
  obtain ⟨Cv, hCv, hvar⟩ := hY.coarseVarianceBound K hK hKU
  obtain ⟨Cm, hCm, hmix⟩ := hY.coarseMixedBound K hK hKU
  obtain ⟨Cc, hCc, hcovBound⟩ := hY.covarianceBound K hK hKU
  let C₀ : ℝ := max Cv (max Cm Cc)
  have hC₀nonneg : 0 ≤ C₀ := by
    dsimp [C₀]
    exact le_trans hCv (le_max_left _ _)
  have hrhoCut : ρ ≤ Real.exp (-(k : ℝ)) := by
    rw [hρdef]
    exact max_le hxy (max_le hεcut hδcut)
  have hrhoPos : 0 < ρ := by
    rw [hρdef]
    have hεδ : 0 < max ε δ := lt_of_lt_of_le hε (le_max_left _ _)
    exact lt_of_lt_of_le hεδ (le_max_right _ _)
  have hrhoLeOne : ρ ≤ 1 := by
    exact hrhoCut.trans (Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (Nat.cast_nonneg k)))
  have hdistLeRho : ‖x - y‖ ≤ ρ := by
    rw [hρdef]
    exact le_max_left _ _
  refine ⟨C₀, hC₀nonneg, ?_⟩
  intro η g a hη hη1 hg hga hC₀strict hC₀small hoffset hκ hκrate
  let r : ℝ := Real.exp (-(k : ℝ))
  let q : Fin 3 → ℝ × ℂ := fun i =>
    if i = 0 then (r, x) else if i = 1 then (ε, x) else (δ, y)
  let Z : Ω → Fin 3 → ℝ := fun ω i => Y ω (q i).1 (q i).2
  have hZ : IsCenteredJointlyGaussian P Z := by
    apply hY.gaussian 3 q
    intro i
    fin_cases i
    · simpa [q, r] using ⟨Real.exp_pos (-(k : ℝ)), hkcut⟩
    · simpa [q, r] using ⟨hε, le_trans hεcut hkcut⟩
    · simpa [q, r] using ⟨hδ, le_trans hδcut hkcut⟩
  have hvarZ : |gaussianVariance P (fun ω => Z ω 0) - (k : ℝ)| ≤ C₀ := by
    have h := hvar k hkcut x hx
    have h' : |gaussianVariance P (fun ω => Z ω 0) - (k : ℝ)| ≤ Cv := by
      simpa [Z, q, r] using h
    exact h'.trans (le_max_left Cv (max Cm Cc))
  have hcovZ₁ : |gaussianCovariance P (fun ω => Z ω 0)
      (fun ω => Z ω 1) - (k : ℝ)| ≤ C₀ := by
    have h := hmix k hkcut ε hε hεcut x hx
    have h' : |gaussianCovariance P (fun ω => Z ω 0)
        (fun ω => Z ω 1) - (k : ℝ)| ≤ Cm := by
      simpa [Z, q, r] using h
    exact h'.trans (le_trans (le_max_left Cm Cc) (le_max_right Cv (max Cm Cc)))
  have hgeom : max ‖x - y‖ (max r δ) = r := by
    rw [max_eq_left hδcut, max_eq_right hxy]
  have hlog : Real.log (1 / max ‖x - y‖ (max r δ)) = (k : ℝ) := by
    rw [hgeom]
    simp [r]
  have hcovZ₂ : |gaussianCovariance P (fun ω => Z ω 0)
      (fun ω => Z ω 2) - (k : ℝ)| ≤ C₀ := by
    have h := hcovBound r δ (by positivity) hkcut hδ
      (le_trans hδcut hkcut) x hx y hy
    have h' : |gaussianCovariance P (fun ω => Z ω 0)
        (fun ω => Z ω 2) - (k : ℝ)| ≤ Cc := by
      have hbound : |gaussianCovariance P (fun ω => Z ω 0)
          (fun ω => Z ω 2) - Real.log (1 / max ‖x - y‖ (max r δ))| ≤ Cc := by
        simpa [Z, q, r] using h
      rw [hlog] at hbound
      exact hbound
    exact h'.trans (le_trans (le_max_right Cm Cc) (le_max_right Cv (max Cm Cc)))
  have hcovRoot : gaussianCovariance P (fun ω => Z ω 1) (fun ω => Z ω 2) ≤
      Real.log (1 / ρ) + C₀ := by
    have h := hcovBound ε δ hε (le_trans hεcut hkcut) hδ
      (le_trans hδcut hkcut) x hx y hy
    have h' : |gaussianCovariance P (fun ω => Z ω 1)
        (fun ω => Z ω 2) - Real.log (1 / ρ)| ≤ Cc := by
      simpa [Z, q, hρdef] using h
    have hCcC : Cc ≤ C₀ := by
      dsimp [C₀]
      exact le_trans (le_max_right Cm Cc) (le_max_right Cv (max Cm Cc))
    calc
      gaussianCovariance P (fun ω => Z ω 1) (fun ω => Z ω 2) ≤
          Real.log (1 / ρ) + Cc := by linarith [(abs_le.mp h').2]
      _ ≤ Real.log (1 / ρ) + C₀ := by
        simpa [add_comm] using add_le_add_left hCcC (Real.log (1 / ρ))
  have hkpos : 0 < (k : ℝ) := lt_of_le_of_lt hC₀nonneg hC₀strict
  have hdpos : 0 < ‖x - y‖ := hxypos
  have hpair := finite_gaussian_wick_pair_good_barrier_power_bound P Z hZ
    1 2 0 (by decide) g a C₀ η (k : ℝ) ‖x - y‖ ρ κ hg hga hkpos hη hη1
    hC₀small hoffset hvarZ hcovZ₁ hcovZ₂ hrhoPos hrhoLeOne hdpos hdistLeRho
    hcovRoot hfloor hκ hκrate
  simpa [Z, q, r] using hpair

end DOZZ.Proofs
