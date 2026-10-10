/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.BarrierCauchyCompatibility
public import DOZZ.GMC.GoodBarrierL2Cauchy

/-! Growing-barrier tail bounds, their spatial integration, and the L² algebra criterion. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs


/-- Countable version of the weighted union bound. It lets one sum all omitted integer
barriers even though the final cutoff only activates a finite initial segment. -/
theorem lintegral_mul_indicator_exists_le_tsum
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) (w : Ω → ℝ≥0∞) (bad : ι → Ω → Prop)
    (hbadMeas : ∀ i, AEMeasurable (fun ω => w ω *
      Set.indicator {ω | bad i ω} (fun _ => (1 : ℝ≥0∞)) ω) P) :
    ∫⁻ ω, w ω * Set.indicator {ω | ∃ i, bad i ω}
        (fun _ => (1 : ℝ≥0∞)) ω ∂P ≤
      ∑' i, ∫⁻ ω, w ω * Set.indicator {ω | bad i ω}
        (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
  calc
    ∫⁻ ω, w ω * Set.indicator {ω | ∃ i, bad i ω}
        (fun _ => (1 : ℝ≥0∞)) ω ∂P ≤
      ∫⁻ ω, ∑' i, w ω * Set.indicator {ω | bad i ω}
          (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
            apply lintegral_mono
            intro ω
            by_cases hbad : ∃ i, bad i ω
            · obtain ⟨i, hi⟩ := hbad
              have hterm : w ω * Set.indicator {ω | bad i ω}
                  (fun _ => (1 : ℝ≥0∞)) ω = w ω := by simp [hi]
              have hexists : ∃ j, bad j ω := ⟨i, hi⟩
              calc
                w ω * Set.indicator {ω | ∃ i, bad i ω}
                    (fun _ => (1 : ℝ≥0∞)) ω = w ω := by simp [hexists]
                _ = w ω * Set.indicator {ω | bad i ω}
                    (fun _ => (1 : ℝ≥0∞)) ω := hterm.symm
                _ ≤ ∑' j, w ω * Set.indicator {ω | bad j ω}
                    (fun _ => (1 : ℝ≥0∞)) ω :=
                      ENNReal.le_tsum
                        (f := fun j => w ω * Set.indicator {ω | bad j ω}
                          (fun _ => (1 : ℝ≥0∞)) ω) i
            · simp [hbad]
    _ = ∑' i, ∫⁻ ω, w ω * Set.indicator {ω | bad i ω}
          (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
            rw [lintegral_tsum hbadMeas]

/-- Beyond the spatial separation scale, the discarded coarse barriers have a summable tail
under a mixed two-root tilt. The first fine root is controlled by the same-center coarse bound;
the separated second root contributes only a bounded mean shift. -/
def compatibleMixedPairBarrierVector
    {Ω : Type*} (Y Z : Ω → ℝ → ℂ → ℝ) (r ε δ : ℝ) (x y : ℂ)
    (b₁ b₂ : Bool) : Ω → Fin 3 → ℝ := fun ω i =>
  if i = 0 then Y ω r x else if i = 1 then
    (if b₁ then Y ω ε x else Z ω ε x) else
      (if b₂ then Y ω δ y else Z ω δ y)

theorem compatible_mixed_double_root_barrier_tail_rate
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (_hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    (hYZ : IsCompatibleAdmissibleRegularizations P U ε₀ ε₁ Y Z)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (s L : ℝ) (hs : 0 < s)
    (hL : ∀ x ∈ K, ∀ y ∈ K, s ≤ ‖x - y‖ →
      Real.log (1 / ‖x - y‖) ≤ L)
    (b₁ b₂ : Bool) (g a : ℝ) (hg : 0 < g) (hga : g < a) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      Real.exp (-(k : ℝ)) ≤ min ε₀ ε₁ → Real.exp (-(k : ℝ)) ≤ s →
      ∀ x ∈ K, ∀ y ∈ K, s ≤ ‖x - y‖ →
      ∀ ε δ : ℝ, 0 < ε → ε ≤ min ε₀ ε₁ → ε ≤ Real.exp (-(k : ℝ)) →
        0 < δ → δ ≤ min ε₀ ε₁ →
        let V : Ω → Fin 3 → ℝ := compatibleMixedPairBarrierVector Y Z
          (Real.exp (-(k : ℝ))) ε δ x y b₁ b₂
        let tilt : Fin 3 → ℝ := twoRootTilt 1 2 g
        ∫⁻ ω, ENNReal.ofReal (Real.exp
            ((∑ i : Fin 3, tilt i * V ω i) -
              (∑ i : Fin 3, ∑ j : Fin 3, tilt i *
                gaussianCovariance P (fun ω => V ω i) (fun ω => V ω j) * tilt j) / 2)) *
          Set.indicator {ω | a * (k : ℝ) < V ω 0}
            (fun _ => (1 : ℝ≥0∞)) ω ∂P ≤
          ENNReal.ofReal (Real.exp (-((a - g) ^ 2 * (k : ℝ) / 16))) := by
  rcases hYZ with ⟨hJoint, hCov, hCoarse, _hOffDiagonal, _hFixedCoarse⟩
  obtain ⟨Cv, hCv, hvar⟩ := hY.coarseVarianceBound K hK hKU
  obtain ⟨CmY, hCmY, hmixY⟩ := hY.coarseMixedBound K hK hKU
  obtain ⟨CmZ, hCmZ, hmixZ⟩ := hCoarse K hK hKU
  obtain ⟨Cyy, hCyy, hcovYY⟩ := hY.covarianceBound K hK hKU
  obtain ⟨Cyz, hCyz, hcovYZ⟩ := hCov K hK hKU
  let C : ℝ := max Cv (max (max CmY CmZ) (max Cyy Cyz))
  have hC : 0 ≤ C := by
    dsimp [C]
    exact le_trans hCv (le_max_left _ _)
  have hCvar : Cv ≤ C := by dsimp [C]; exact le_max_left _ _
  have hCmY' : CmY ≤ C := by
    dsimp [C]
    exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
  have hCmZ' : CmZ ≤ C := by
    dsimp [C]
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
  have hCyy' : Cyy ≤ C := by
    dsimp [C]
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hCyz' : Cyz ≤ C := by
    dsimp [C]
    exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  let D : ℝ := g * (|L| + 2 * C + 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hrateScale : 0 < a - g := sub_pos.mpr hga
  obtain ⟨N, hN⟩ := exists_nat_gt (max C (2 * D / (a - g)))
  refine ⟨N, ?_⟩
  intro k hk hkscale hks x hx y hy hxy ε δ hε hεcut hεr hδ hδcut
  have hkreal : (max C (2 * D / (a - g))) < (N : ℝ) := by exact hN
  have hkC : C < (k : ℝ) := lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hkreal) (Nat.cast_le.mpr hk)
  have hkD : D ≤ (a - g) * (k : ℝ) / 2 := by
    have hbound : 2 * D / (a - g) < (k : ℝ) :=
      lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hkreal) (Nat.cast_le.mpr hk)
    have := (div_lt_iff₀ hrateScale).mp hbound
    linarith only [this]
  let r : ℝ := Real.exp (-(k : ℝ))
  let q : Fin 3 → Bool × ℝ × ℂ := fun i =>
    if i = 0 then (true, r, x) else if i = 1 then (b₁, ε, x) else (b₂, δ, y)
  let V : Ω → Fin 3 → ℝ := compatibleMixedPairBarrierVector Y Z r ε δ x y b₁ b₂
  have hVq : IsCenteredJointlyGaussian P (fun ω i =>
      if (q i).1 then Y ω (q i).2.1 (q i).2.2 else Z ω (q i).2.1 (q i).2.2) := by
    apply hJoint 3 q
    intro i
    fin_cases i
    · exact ⟨Real.exp_pos _, hkscale⟩
    · exact ⟨hε, hεcut⟩
    · exact ⟨hδ, hδcut⟩
  have hV : IsCenteredJointlyGaussian P V := by
    have hVeq : V = (fun ω i =>
        if (q i).1 then Y ω (q i).2.1 (q i).2.2 else Z ω (q i).2.1 (q i).2.2) := by
      funext ω i
      fin_cases i <;> simp [V, compatibleMixedPairBarrierVector, q, r]
    rw [hVeq]
    exact hVq
  have hvarV : |gaussianVariance P (fun ω => V ω 0) - (k : ℝ)| ≤ C := by
    have h := hvar k (le_trans hkscale (min_le_left _ _)) x hx
    have h' : |gaussianVariance P (fun ω => V ω 0) - (k : ℝ)| ≤ Cv := by
      simpa [V, compatibleMixedPairBarrierVector, q, r] using h
    exact h'.trans hCvar
  have hcovV1 : |gaussianCovariance P (fun ω => V ω 0)
      (fun ω => V ω 1) - (k : ℝ)| ≤ C := by
    have h' : |gaussianCovariance P (fun ω => V ω 0)
        (fun ω => V ω 1) - (k : ℝ)| ≤ max CmY CmZ := by
      cases b₁
      · have hcutZ : ε ≤ min ε₁ r := le_min (hεcut.trans (min_le_right _ _)) hεr
        have hz := hmixZ k (le_trans hkscale (min_le_left _ _)) ε hε hcutZ x hx
        have hz' : |gaussianCovariance P (fun ω => V ω 0)
            (fun ω => V ω 1) - (k : ℝ)| ≤ CmZ := by
          simpa [V, compatibleMixedPairBarrierVector, q, r] using hz
        exact hz'.trans (le_max_right _ _)
      · have hy := hmixY k (le_trans hkscale (min_le_left _ _)) ε hε hεr x hx
        have hy' : |gaussianCovariance P (fun ω => V ω 0)
            (fun ω => V ω 1) - (k : ℝ)| ≤ CmY := by
          simpa [V, compatibleMixedPairBarrierVector, q, r] using hy
        exact hy'.trans (le_max_left _ _)
    exact h'.trans (le_trans (le_max_left _ _) (le_max_right _ _))
  have hdistpos : 0 < ‖x - y‖ := lt_of_lt_of_le hs hxy
  have hρpos : 0 < max ‖x - y‖ (max r δ) :=
    lt_of_lt_of_le hdistpos (le_max_left _ _)
  have hlogle : Real.log (1 / max ‖x - y‖ (max r δ)) ≤ L := by
    have harg : 1 / max ‖x - y‖ (max r δ) ≤ 1 / ‖x - y‖ :=
      one_div_le_one_div_of_le hdistpos (le_max_left _ _)
    exact (Real.log_le_log (one_div_pos.mpr hρpos) harg).trans (hL x hx y hy hxy)
  have hcovV2 : gaussianCovariance P (fun ω => V ω 0)
      (fun ω => V ω 2) ≤ L + C := by
    have h' : |gaussianCovariance P (fun ω => V ω 0)
        (fun ω => V ω 2) - Real.log (1 / max ‖x - y‖ (max r δ))| ≤
          max Cyy Cyz := by
      cases b₂
      · have hz := hcovYZ r δ (Real.exp_pos _) (le_trans hkscale (min_le_left _ _))
          hδ (le_trans hδcut (min_le_right _ _)) x hx y hy
        have hz' : |gaussianCovariance P (fun ω => V ω 0)
            (fun ω => V ω 2) - Real.log (1 / max ‖x - y‖ (max r δ))| ≤ Cyz := by
          simpa [V, compatibleMixedPairBarrierVector, q, r] using hz
        exact hz'.trans (le_max_right _ _)
      · have hy := hcovYY r δ (Real.exp_pos _)
          (le_trans hkscale (min_le_left _ _)) hδ
          (le_trans hδcut (min_le_left _ _)) x hx y hy
        have hy' : |gaussianCovariance P (fun ω => V ω 0)
            (fun ω => V ω 2) - Real.log (1 / max ‖x - y‖ (max r δ))| ≤ Cyy := by
          simpa [V, compatibleMixedPairBarrierVector, q, r] using hy
        exact hy'.trans (le_max_left _ _)
    have hupper := (abs_le.mp h').2
    have hCbound : max Cyy Cyz ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
    linarith only [hupper, hCbound, hlogle]
  let tilt : Fin 3 → ℝ := twoRootTilt 1 2 g
  have hmean : (∑ i : Fin 3, gaussianCovariance P (fun ω => V ω 0)
      (fun ω => V ω i) * tilt i) =
      g * gaussianCovariance P (fun ω => V ω 0) (fun ω => V ω 1) +
        g * gaussianCovariance P (fun ω => V ω 0) (fun ω => V ω 2) := by
    have hterm (i : Fin 3) : gaussianCovariance P (fun ω => V ω 0)
        (fun ω => V ω i) * tilt i =
        (if i = 1 then gaussianCovariance P (fun ω => V ω 0)
          (fun ω => V ω i) * g else 0) +
        (if i = 2 then gaussianCovariance P (fun ω => V ω 0)
          (fun ω => V ω i) * g else 0) := by
      fin_cases i <;> simp [tilt, twoRootTilt]
    rw [show (∑ i : Fin 3, gaussianCovariance P (fun ω => V ω 0)
        (fun ω => V ω i) * tilt i) =
        ∑ i : Fin 3, ((if i = 1 then gaussianCovariance P
          (fun ω => V ω 0) (fun ω => V ω i) * g else 0) +
          (if i = 2 then gaussianCovariance P (fun ω => V ω 0)
            (fun ω => V ω i) * g else 0)) by
          apply Finset.sum_congr rfl
          intro i hi
          exact hterm i]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp
    ring
  let m : ℝ := ∑ i : Fin 3, gaussianCovariance P (fun ω => V ω 0)
    (fun ω => V ω i) * tilt i
  have hmUpper : m ≤ g * (k : ℝ) + D := by
    have hcov1upper : gaussianCovariance P (fun ω => V ω 0)
        (fun ω => V ω 1) ≤ (k : ℝ) + C := by
      have h := (abs_le.mp hcovV1).2
      linarith only [h]
    have hcov2upper : gaussianCovariance P (fun ω => V ω 0)
        (fun ω => V ω 2) ≤ L + C := hcovV2
    have hsum := add_le_add
      (mul_le_mul_of_nonneg_left hcov1upper hg.le)
      (mul_le_mul_of_nonneg_left hcov2upper hg.le)
    rw [← hmean] at hsum
    dsimp [m] at hsum ⊢
    have hL : L ≤ |L| := le_abs_self L
    have hgL : g * L ≤ g * |L| := mul_le_mul_of_nonneg_left hL hg.le
    dsimp [D]
    linarith only [hsum, hgL, hg]
  have hgapLower : (a - g) * (k : ℝ) / 2 ≤ a * (k : ℝ) - m := by
    have h := hmUpper
    linarith only [h, hkD]
  have hgap : m < a * (k : ℝ) := by
    have hkpos : 0 < (k : ℝ) := lt_of_le_of_lt hC hkC
    have hstrict : (a - g) * (k : ℝ) / 2 > 0 := by positivity
    linarith only [hgapLower, hstrict]
  have hvarPos : 0 < gaussianVariance P (fun ω => V ω 0) := by
    have h := (abs_le.mp hvarV).1
    linarith only [h, hkC, hC]
  have hvarUpper : gaussianVariance P (fun ω => V ω 0) ≤ 2 * (k : ℝ) := by
    have h := (abs_le.mp hvarV).2
    linarith only [h, hkC]
  have hrate : (a - g) ^ 2 * (k : ℝ) / 16 ≤
      (a * (k : ℝ) - m) ^ 2 /
        (2 * gaussianVariance P (fun ω => V ω 0)) := by
    have hkpos : 0 < (k : ℝ) := lt_of_le_of_lt hC hkC
    have hgapSq : ((a - g) * (k : ℝ) / 2) ^ 2 ≤ (a * (k : ℝ) - m) ^ 2 :=
      sq_le_sq' (by linarith only [hgapLower, mul_pos hrateScale hkpos]) hgapLower
    have hinv : (4 * (k : ℝ))⁻¹ ≤
        (2 * gaussianVariance P (fun ω => V ω 0))⁻¹ := by
      have hden₁ : 0 < 4 * (k : ℝ) := by positivity
      have hden₂ : 0 < 2 * gaussianVariance P (fun ω => V ω 0) :=
        mul_pos (by norm_num) hvarPos
      exact (inv_le_inv₀ hden₁ hden₂).2 (by linarith only [hvarUpper])
    calc
      (a - g) ^ 2 * (k : ℝ) / 16 =
          ((a - g) * (k : ℝ) / 2) ^ 2 * (4 * (k : ℝ))⁻¹ := by field_simp; ring
      _ ≤ (a * (k : ℝ) - m) ^ 2 *
            (2 * gaussianVariance P (fun ω => V ω 0))⁻¹ := by
              exact mul_le_mul hgapSq hinv (by positivity) (by positivity)
      _ = _ := by rw [div_eq_mul_inv]
  have htail := finite_gaussian_tilt_barrier_tail_bound P V hV tilt 0
    (a * (k : ℝ)) hgap hvarPos
  have htail' : ∫⁻ ω, ENNReal.ofReal (Real.exp
      ((∑ i : Fin 3, tilt i * V ω i) -
        (∑ i : Fin 3, ∑ j : Fin 3, tilt i * gaussianCovariance P
          (fun ω => V ω i) (fun ω => V ω j) * tilt j) / 2)) *
      Set.indicator {ω | a * (k : ℝ) < V ω 0} (fun _ => (1 : ℝ≥0∞)) ω ∂P ≤
        ENNReal.ofReal (Real.exp (-((a - g) ^ 2 * (k : ℝ) / 16))) := by
    calc
      _ ≤ ENNReal.ofReal (Real.exp
          (-(a * (k : ℝ) - m) ^ 2 /
            (2 * gaussianVariance P (fun ω => V ω 0)))) := by
              simpa only [m] using htail
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        calc
          -(a * (k : ℝ) - m) ^ 2 /
              (2 * gaussianVariance P (fun ω => V ω 0)) =
              -((a * (k : ℝ) - m) ^ 2 /
                (2 * gaussianVariance P (fun ω => V ω 0))) := by rw [neg_div]
          _ ≤ -((a - g) ^ 2 * (k : ℝ) / 16) := neg_le_neg hrate
  exact htail'

/-- The mixed double-root barrier rate is summable over the coarse scales whenever the barrier
slope is strictly above the charge. -/
theorem summable_compatible_mixed_double_root_barrier_rate
    (g a : ℝ) (hga : g < a) :
    Summable (fun k : ℕ => Real.exp (-((a - g) ^ 2 * (k : ℝ) / 16))) := by
  let c : ℝ := (a - g) ^ 2 / 16
  have hc : 0 < c := by dsimp [c]; positivity
  have hfun : (fun k : ℕ => Real.exp (-c * (k : ℝ))) =
      fun k : ℕ => Real.exp (-((a - g) ^ 2 * (k : ℝ) / 16)) := by
    funext k
    congr 1
    dsimp [c]
    ring
  rw [← hfun]
  exact summable_gaussian_barrier_tail c hc

/-- The integrated cost of all omitted integer barriers tends to zero as the finite truncation
level grows. -/
theorem tendsto_compatible_mixed_double_root_barrier_tail_sum
    (g a : ℝ) (hga : g < a) :
    Tendsto
      (fun N : ℕ => ∑' k : ℕ,
        ENNReal.ofReal (Real.exp (-((a - g) ^ 2 * ((k + N : ℕ) : ℝ) / 16))))
      atTop (𝓝 0) := by
  let c : ℝ := (a - g) ^ 2 / 16
  have hc : 0 < c := by dsimp [c]; positivity
  have hsummable : Summable (fun k : ℕ => Real.exp (-c * (k : ℝ))) := by
    have h := summable_compatible_mixed_double_root_barrier_rate g a hga
    apply h.congr
    intro k
    congr 1
    dsimp [c]
    ring
  let f : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (Real.exp (-c * (k : ℝ)))
  have hfinite : ∑' k, f k ≠ ∞ := by
    exact hsummable.tsum_ofReal_ne_top
  have htail := ENNReal.tendsto_sum_nat_add f hfinite
  have hfun :
      (fun N : ℕ => ∑' k : ℕ,
        ENNReal.ofReal (Real.exp (-((a - g) ^ 2 * ((k + N : ℕ) : ℝ) / 16)))) =
      fun N => ∑' k : ℕ, f (k + N) := by
    funext N
    apply tsum_congr
    intro k
    simp only [f]
    congr 1
    rw [Nat.cast_add]
    dsimp [c]
    ring_nf
  rw [hfun]
  exact htail


/-- Integrate a spatially uniform probability-tail estimate over a compact planar root chart.
This turns the uniform two-root barrier tail into a spatially integrated tail estimate. -/
theorem compact_spatial_integral_uniform_bound
    (K : Set ℂ) (hK : IsCompact K) (F : ℂ × ℂ → ℝ≥0∞)
    (c : ℝ≥0∞) (hc : c ≠ ∞)
    (hF : ∀ p ∈ K ×ˢ K, F p ≤ c) :
    ∫⁻ p in K ×ˢ K, F p ∂(volume.prod volume) ≤ c * (volume K * volume K) ∧
      c * (volume K * volume K) ≠ ∞ := by
  have hKK : IsCompact (K ×ˢ K) := hK.prod hK
  have hKKmeas : MeasurableSet (K ×ˢ K) := hKK.measurableSet
  have hvol : volume K ≠ ∞ := hK.measure_lt_top.ne
  refine ⟨?_, ENNReal.mul_ne_top hc (ENNReal.mul_ne_top hvol hvol)⟩
  calc
    ∫⁻ p in K ×ˢ K, F p ∂(volume.prod volume) ≤
        ∫⁻ p in K ×ˢ K, c ∂(volume.prod volume) :=
      setLIntegral_mono' hKKmeas hF
    _ = c * (volume K * volume K) := by simp [lintegral_const]

/-- The two-root omitted-barrier tail remains exponentially small after spatial integration on
any measurable compact-chart slice whose roots stay a fixed positive distance apart. This is the
far-field companion to `compatible_two_root_wick_pair_good_barrier_spatial_integral_bound`. -/
theorem compatible_mixed_double_root_barrier_tail_spatial_integral_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    (hYZ : IsCompatibleAdmissibleRegularizations P U ε₀ ε₁ Y Z)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (s L : ℝ) (hs : 0 < s)
    (hL : ∀ x ∈ K, ∀ y ∈ K, s ≤ ‖x - y‖ →
      Real.log (1 / ‖x - y‖) ≤ L)
    (S : Set (ℂ × ℂ)) (hS : MeasurableSet S) (hSK : S ⊆ K ×ˢ K)
    (hSep : ∀ p ∈ S, s ≤ ‖p.1 - p.2‖)
    (b₁ b₂ : Bool) (g a : ℝ) (hg : 0 < g) (hga : g < a) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      Real.exp (-(k : ℝ)) ≤ min ε₀ ε₁ → Real.exp (-(k : ℝ)) ≤ s →
      ∀ ε δ : ℝ, 0 < ε → ε ≤ min ε₀ ε₁ → ε ≤ Real.exp (-(k : ℝ)) →
        0 < δ → δ ≤ min ε₀ ε₁ →
        ∃ I : ℝ≥0∞, I ≠ ∞ ∧
          ∫⁻ p in S,
            (∫⁻ ω, ENNReal.ofReal (Real.exp
                ((∑ i : Fin 3, (twoRootTilt 1 2 g) i *
                    compatibleMixedPairBarrierVector Y Z
                      (Real.exp (-(k : ℝ))) ε δ p.1 p.2 b₁ b₂ ω i) -
                  (∑ i : Fin 3, ∑ j : Fin 3, (twoRootTilt 1 2 g) i *
                    gaussianCovariance P
                      (fun ω => compatibleMixedPairBarrierVector Y Z
                        (Real.exp (-(k : ℝ))) ε δ p.1 p.2 b₁ b₂ ω i)
                      (fun ω => compatibleMixedPairBarrierVector Y Z
                        (Real.exp (-(k : ℝ))) ε δ p.1 p.2 b₁ b₂ ω j) *
                    (twoRootTilt 1 2 g) j) / 2)) *
              Set.indicator {ω | a * (k : ℝ) <
                compatibleMixedPairBarrierVector Y Z
                  (Real.exp (-(k : ℝ))) ε δ p.1 p.2 b₁ b₂ ω 0}
                (fun _ => (1 : ℝ≥0∞)) ω ∂P)
            ∂(volume.prod volume) ≤
          ENNReal.ofReal (Real.exp (-((a - g) ^ 2 * (k : ℝ) / 16))) *
            (volume K * volume K) := by
  obtain ⟨N, hN⟩ := compatible_mixed_double_root_barrier_tail_rate
    P U dens ε₀ ε₁ Y Z hY hZ hYZ K hK hKU s L hs hL b₁ b₂ g a hg hga
  refine ⟨N, ?_⟩
  intro k hk hkscale hks ε δ hε hεcut hεr hδ hδcut
  let W : ℂ × ℂ → ℝ≥0∞ := fun p =>
    ∫⁻ ω, ENNReal.ofReal (Real.exp
        ((∑ i : Fin 3, (twoRootTilt 1 2 g) i *
            compatibleMixedPairBarrierVector Y Z (Real.exp (-(k : ℝ)))
              ε δ p.1 p.2 b₁ b₂ ω i) -
          (∑ i : Fin 3, ∑ j : Fin 3, (twoRootTilt 1 2 g) i *
            gaussianCovariance P
              (fun ω => compatibleMixedPairBarrierVector Y Z (Real.exp (-(k : ℝ)))
                ε δ p.1 p.2 b₁ b₂ ω i)
              (fun ω => compatibleMixedPairBarrierVector Y Z (Real.exp (-(k : ℝ)))
                ε δ p.1 p.2 b₁ b₂ ω j) * (twoRootTilt 1 2 g) j) / 2)) *
      Set.indicator {ω | a * (k : ℝ) <
        compatibleMixedPairBarrierVector Y Z (Real.exp (-(k : ℝ)))
          ε δ p.1 p.2 b₁ b₂ ω 0} (fun _ => (1 : ℝ≥0∞)) ω ∂P
  let tail : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-((a - g) ^ 2 * (k : ℝ) / 16)))
  let F : ℂ × ℂ → ℝ≥0∞ := S.indicator W
  have htail : ∀ p ∈ S, W p ≤ tail := by
    intro p hp
    have hpK := hSK hp
    exact hN k hk hkscale hks p.1 hpK.1 p.2 hpK.2 (hSep p hp)
      ε δ hε hεcut hεr hδ hδcut
  have hF : ∀ p ∈ K ×ˢ K, F p ≤ tail := by
    intro p hp
    by_cases hpS : p ∈ S
    · simpa [F, hpS] using htail p hpS
    · simp [F, hpS]
  have hcompact := compact_spatial_integral_uniform_bound K hK F tail
    (by simp [tail]) hF
  have hEq :
      ∫⁻ p in S, W p ∂(volume.prod volume) =
        ∫⁻ p in K ×ˢ K, F p ∂(volume.prod volume) := by
    rw [← lintegral_indicator hS, ← lintegral_indicator (hK.prod hK).measurableSet]
    apply lintegral_congr_ae
    filter_upwards [] with p
    by_cases hpS : p ∈ S
    · have hpK : p ∈ K ×ˢ K := hSK hpS
      simp [F, hpS, hpK]
    · simp [F, hpS, Set.indicator]
  rcases hcompact with ⟨hbound, hfinite⟩
  refine ⟨tail * (volume K * volume K), hfinite, ?_⟩
  rw [hEq]
  simpa [tail] using hbound

/-- The spatial integral of the omitted coarse-barrier event for the first root under the
normalized double Wick tilt. -/
noncomputable def compatibleMixedPairBarrierTailKernel
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y Z : Ω → ℝ → ℂ → ℝ)
    (b₁ b₂ : Bool) (g a : ℝ) (k : ℕ) (ε δ : ℝ) (x y : ℂ) : ℝ≥0∞ := by
  classical
  let V : Ω → Fin 3 → ℝ := compatibleMixedPairBarrierVector Y Z
    (Real.exp (-(k : ℝ))) ε δ x y b₁ b₂
  let tilt : Fin 3 → ℝ := twoRootTilt 1 2 g
  exact ∫⁻ ω, ENNReal.ofReal (Real.exp
      ((∑ i : Fin 3, tilt i * V ω i) -
        (∑ i : Fin 3, ∑ j : Fin 3, tilt i *
          gaussianCovariance P (fun ω => V ω i) (fun ω => V ω j) * tilt j) / 2)) *
      Set.indicator {ω | a * (k : ℝ) < V ω 0}
        (fun _ => (1 : ℝ≥0∞)) ω ∂P

/-- Spatial integration of the first-root barrier estimate after reversing the two spatial
roots and their fine cutoffs. This controls a violation at the second root of the original
mixed pair, without requiring the spatial slice itself to be symmetric. -/
theorem compatible_mixed_double_root_barrier_tail_spatial_integral_bound_swapped
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    (hYZ : IsCompatibleAdmissibleRegularizations P U ε₀ ε₁ Y Z)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (s L : ℝ) (hs : 0 < s)
    (hL : ∀ x ∈ K, ∀ y ∈ K, s ≤ ‖x - y‖ →
      Real.log (1 / ‖x - y‖) ≤ L)
    (S : Set (ℂ × ℂ)) (hS : MeasurableSet S) (hSK : S ⊆ K ×ˢ K)
    (hSep : ∀ p ∈ S, s ≤ ‖p.1 - p.2‖)
    (b₁ b₂ : Bool) (g a : ℝ) (hg : 0 < g) (hga : g < a) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      Real.exp (-(k : ℝ)) ≤ min ε₀ ε₁ → Real.exp (-(k : ℝ)) ≤ s →
      ∀ ε δ : ℝ, 0 < ε → ε ≤ min ε₀ ε₁ →
        0 < δ → δ ≤ min ε₀ ε₁ → δ ≤ Real.exp (-(k : ℝ)) →
          ∃ I : ℝ≥0∞, I ≠ ∞ ∧
            ∫⁻ p in S, compatibleMixedPairBarrierTailKernel P Y Z b₂ b₁ g a k
              δ ε p.2 p.1 ∂(volume.prod volume) ≤
              ENNReal.ofReal (Real.exp (-((a - g) ^ 2 * (k : ℝ) / 16))) *
                (volume K * volume K) := by
  obtain ⟨N, hN⟩ := compatible_mixed_double_root_barrier_tail_rate
    P U dens ε₀ ε₁ Y Z hY hZ hYZ K hK hKU s L hs hL b₂ b₁ g a hg hga
  refine ⟨N, ?_⟩
  intro k hk hkscale hks ε δ hε hεcut hδ hδcut hδr
  let tail : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-((a - g) ^ 2 * (k : ℝ) / 16)))
  let W : ℂ × ℂ → ℝ≥0∞ := fun p =>
    compatibleMixedPairBarrierTailKernel P Y Z b₂ b₁ g a k δ ε p.2 p.1
  have htail : ∀ p ∈ S, W p ≤ tail := by
    intro p hp
    have hpK := hSK hp
    have hsep' : s ≤ ‖p.2 - p.1‖ := by simpa [norm_sub_rev] using hSep p hp
    have h := hN k hk hkscale hks p.2 hpK.2 p.1 hpK.1 hsep'
      δ ε hδ hδcut hδr hε hεcut
    exact h
  let F : ℂ × ℂ → ℝ≥0∞ := S.indicator W
  have hF : ∀ p ∈ K ×ˢ K, F p ≤ tail := by
    intro p hp
    by_cases hpS : p ∈ S
    · simpa [F, hpS] using htail p hpS
    · simp [F, hpS]
  have hcompact := compact_spatial_integral_uniform_bound K hK F tail
    (by simp [tail]) hF
  have hEq :
      ∫⁻ p in S, W p ∂(volume.prod volume) =
        ∫⁻ p in K ×ˢ K, F p ∂(volume.prod volume) := by
    rw [← lintegral_indicator hS, ← lintegral_indicator (hK.prod hK).measurableSet]
    apply lintegral_congr_ae
    filter_upwards [] with p
    by_cases hpS : p ∈ S
    · have hpK : p ∈ K ×ˢ K := hSK hpS
      simp [F, hpS, hpK]
    · simp [F, hpS, Set.indicator]
  rcases hcompact with ⟨hbound, hfinite⟩
  refine ⟨tail * (volume K * volume K), hfinite, ?_⟩
  rw [hEq]
  simpa [tail] using hbound



end DOZZ.Proofs
