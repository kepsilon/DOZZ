/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteGaussianProduct
public import DOZZ.GMC.FiniteChaosMean
public import Mathlib.Probability.Moments.Covariance

/-! Adding one independent centered Gaussian scalar to every coordinate of a finite Gaussian
family. This is the common-scalar step in Kahane's constant trick. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

private theorem gaussianReal_standard_scale_map (c : ℝ) :
    (gaussianReal 0 (1 : ℝ≥0)).map (fun x : ℝ => c * x) =
      gaussianReal 0 ⟨c ^ 2, sq_nonneg c⟩ := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · ring
  · apply Subtype.ext
    simp

private theorem ennreal_rpow_ofReal_mul_pos_left {x y p : ℝ}
    (hx : 0 ≤ x) (hy : 0 < y) :
    ENNReal.rpow (ENNReal.ofReal (y * x)) p =
      ENNReal.ofReal (y ^ p) * ENNReal.rpow (ENNReal.ofReal x) p := by
  change ENNReal.ofReal (y * x) ^ p =
    ENNReal.ofReal (y ^ p) * ENNReal.ofReal x ^ p
  by_cases hx0 : x = 0
  · subst x
    by_cases hp0 : p = 0
    · simp [hp0]
    by_cases hpneg : p < 0
    · simp [ENNReal.zero_rpow_of_neg hpneg, Real.rpow_pos_of_pos hy]
    · have hpnonneg : 0 ≤ p := le_of_not_gt hpneg
      have hppos : 0 < p := lt_of_le_of_ne hpnonneg (Ne.symm hp0)
      simp [ENNReal.zero_rpow_of_pos hppos]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    rw [ENNReal.ofReal_rpow_of_pos (mul_pos hy hxpos),
      ENNReal.ofReal_rpow_of_pos hxpos,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hy.le p), Real.mul_rpow hy.le hxpos.le]

private theorem centeredJointlyGaussian_singleton_scaled_standard (c : ℝ) :
    DOZZ.IsCenteredJointlyGaussian (gaussianReal 0 1)
      (fun x (_ : Unit) => c * x) := by
  classical
  have hprob : IsProbabilityMeasure (gaussianReal 0 1) := inferInstance
  refine ⟨hprob, ?_, ?_⟩
  · intro _
    exact (measurable_const_mul c).aemeasurable
  · intro a
    let d : ℝ := a () * c
    have hmem : MemLp (fun x : ℝ => d * x) 2 (gaussianReal 0 1) :=
      (memLp_id_gaussianReal (2 : ℝ≥0)).const_mul d
    have hmap : (gaussianReal 0 1).map (fun x : ℝ => d * x) =
        gaussianReal 0 ⟨d ^ 2, sq_nonneg d⟩ := by
      exact gaussianReal_standard_scale_map d
    refine ⟨?_, ⟨⟨d ^ 2, sq_nonneg d⟩, ?_⟩⟩
    · convert hmem using 1
      ext x
      simp [d]
      ring
    · convert hmap using 1
      have hfun : (fun x : ℝ => ∑ i : Unit,
          a i * (fun y : ℝ => fun _ : Unit => c * y) x i) = fun x => d * x := by
        funext x
        simp [d]
        ring
      rw [hfun]

/-- The sum of an arbitrary centered jointly Gaussian finite family and an independent common
centered Gaussian coordinate is again centered jointly Gaussian. -/
theorem independent_common_scalar_add_isCenteredJointlyGaussian
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : DOZZ.IsCenteredJointlyGaussian P Z) (c : ℝ) :
    DOZZ.IsCenteredJointlyGaussian (P.prod (gaussianReal 0 1))
      (fun ω i => Z ω.1 i + c * ω.2) := by
  classical
  let Q : Measure ℝ := gaussianReal 0 1
  have hQ : IsProbabilityMeasure Q := inferInstance
  have hP : IsProbabilityMeasure P := hZ.1
  let : IsProbabilityMeasure P := hP
  let : IsProbabilityMeasure Q := hQ
  refine ⟨inferInstance, ?_, ?_⟩
  · intro i
    have hZi : AEMeasurable (fun ω : Ω × ℝ => Z ω.1 i) (P.prod Q) :=
      (hZ.2.1 i).comp_fst
    have hN : Measurable (fun ω : Ω × ℝ => c * ω.2) := by fun_prop
    exact hZi.add hN.aemeasurable
  · intro a
    let U : Ω → ℝ := fun ω => ∑ i, a i * Z ω i
    let V : ℝ → ℝ := fun x => (∑ i, a i) * c * x
    let S : Ω × ℝ → ℝ := fun ω => U ω.1 + V ω.2
    obtain ⟨hUmem, ⟨vU, hUmap⟩⟩ := hZ.2.2 a
    have hUmeas : AEMeasurable U P := hUmem.aemeasurable
    have hUlaw : HasLaw U (gaussianReal 0 vU) P := ⟨hUmeas, hUmap⟩
    let d : ℝ := (∑ i, a i) * c
    have hVmem : MemLp V 2 Q := by
      dsimp [V, Q, d]
      exact (memLp_id_gaussianReal (2 : ℝ≥0)).const_mul ((∑ i, a i) * c)
    have hVlaw : HasLaw V (gaussianReal 0 ⟨d ^ 2, sq_nonneg d⟩) Q := by
      refine ⟨?_, ?_⟩
      · exact (measurable_const_mul d).aemeasurable
      · exact gaussianReal_standard_scale_map d
    have hUprod : HasLaw (fun ω : Ω × ℝ => U ω.1) (gaussianReal 0 vU) (P.prod Q) :=
      hUlaw.comp measurePreserving_fst.hasLaw
    have hVprod : HasLaw (fun ω : Ω × ℝ => V ω.2)
        (gaussianReal 0 ⟨d ^ 2, sq_nonneg d⟩) (P.prod Q) :=
      hVlaw.comp measurePreserving_snd.hasLaw
    have hIndep : (fun ω : Ω × ℝ => U ω.1) ⟂ᵢ[P.prod Q]
        (fun ω => V ω.2) := indepFun_prod₀ hUmeas
          ((measurable_const_mul d).aemeasurable)
    have hSumLaw : HasLaw S (gaussianReal 0 (vU + ⟨d ^ 2, sq_nonneg d⟩)) (P.prod Q) := by
      refine ⟨hUprod.aemeasurable.add hVprod.aemeasurable, ?_⟩
      convert gaussianReal_add_gaussianReal_of_indepFun hIndep hUprod hVprod using 1; simp
    have hSsum (ω : Ω × ℝ) :
        (∑ i, a i * (Z ω.1 i + c * ω.2)) = S ω := by
      dsimp [S, U, V]
      calc
        (∑ i, a i * (Z ω.1 i + c * ω.2)) =
            ∑ i, (a i * Z ω.1 i + a i * (c * ω.2)) := by
              congr 1
              funext i
              ring
        _ = (∑ i, a i * Z ω.1 i) + ∑ i, a i * (c * ω.2) := Finset.sum_add_distrib
        _ = U ω.1 + V ω.2 := by
              simp only [U, V]
              rw [← Finset.sum_mul]
              ring
    refine ⟨?_, ⟨vU + ⟨d ^ 2, sq_nonneg d⟩, ?_⟩⟩
    · have hmemS : MemLp S 2 (P.prod Q) := by
        exact hSumLaw.memLp (memLp_id_gaussianReal (2 : ℝ≥0))
      simpa only [hSsum] using hmemS
    · simpa only [hSsum] using hSumLaw.map_eq

/-- The common scalar increases every covariance entry by its variance. -/
theorem gaussianCovariance_independent_common_scalar_add
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : DOZZ.IsCenteredJointlyGaussian P Z) (c : ℝ) (i j : ι) :
    DOZZ.gaussianCovariance (P.prod (gaussianReal 0 1))
      (fun ω => Z ω.1 i + c * ω.2) (fun ω => Z ω.1 j + c * ω.2) =
        DOZZ.gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) + c ^ 2 := by
  classical
  let Q : Measure ℝ := gaussianReal 0 1
  let μ : Measure (Ω × ℝ) := P.prod Q
  let Xi : Ω × ℝ → ℝ := fun ω => Z ω.1 i
  let Xj : Ω × ℝ → ℝ := fun ω => Z ω.1 j
  let N : Ω × ℝ → ℝ := fun ω => c * ω.2
  let Zi : Ω → ℝ := fun ω => Z ω i
  let Zj : Ω → ℝ := fun ω => Z ω j
  let v : ℝ≥0 := ⟨c ^ 2, sq_nonneg c⟩
  have : IsProbabilityMeasure P := hZ.1
  have : IsProbabilityMeasure Q := inferInstance
  have : IsProbabilityMeasure μ := inferInstance
  let hfst : MeasurePreserving Prod.fst μ P := measurePreserving_fst
  let hsnd : MeasurePreserving Prod.snd μ Q := measurePreserving_snd
  have hiMem : MemLp Zi 2 P := by
    obtain ⟨hm, _⟩ := hZ.2.2 (Pi.single i 1)
    simpa [Zi, Pi.single_apply] using hm
  have hjMem : MemLp Zj 2 P := by
    obtain ⟨hm, _⟩ := hZ.2.2 (Pi.single j 1)
    simpa [Zj, Pi.single_apply] using hm
  have hXi2 : MemLp Xi 2 μ := by
    change MemLp (Zi ∘ Prod.fst) 2 μ
    exact hiMem.comp_measurePreserving hfst
  have hXj2 : MemLp Xj 2 μ := by
    change MemLp (Zj ∘ Prod.fst) 2 μ
    exact hjMem.comp_measurePreserving hfst
  have hN2 : MemLp N 2 μ := by
    have hcoord : MemLp (fun x : ℝ => c * x) 2 Q := by
      simpa [Q] using (memLp_id_gaussianReal (2 : ℝ≥0)).const_mul c
    change MemLp ((fun x : ℝ => c * x) ∘ Prod.snd) 2 μ
    exact hcoord.comp_measurePreserving hsnd
  obtain ⟨_, _, hmeanZi, _⟩ := coordinate_mean_variance P Z hZ i
  obtain ⟨_, _, hmeanZj, _⟩ := coordinate_mean_variance P Z hZ j
  have hmeanXi : (∫ ω, Xi ω ∂μ) = 0 := by
    have hmap := integral_map hfst.aemeasurable
      (by
        rw [hfst.map_eq]
        exact (hiMem.integrable (by norm_num : 1 ≤ (2 : ENNReal))).aestronglyMeasurable)
    rw [hfst.map_eq] at hmap
    simpa [Xi, Zi, Function.comp_def] using hmap.symm.trans hmeanZi
  have hmeanXj : (∫ ω, Xj ω ∂μ) = 0 := by
    have hmap := integral_map hfst.aemeasurable
      (by
        rw [hfst.map_eq]
        exact (hjMem.integrable (by norm_num : 1 ≤ (2 : ENNReal))).aestronglyMeasurable)
    rw [hfst.map_eq] at hmap
    simpa [Xj, Zj, Function.comp_def] using hmap.symm.trans hmeanZj
  have hNlaw : HasLaw N (gaussianReal 0 v) μ := by
    have hscaled : HasLaw (fun x : ℝ => c * x)
        (gaussianReal 0 v) Q := by
      refine ⟨(measurable_const_mul c).aemeasurable, ?_⟩
      simpa [v, Q] using gaussianReal_standard_scale_map c
    simpa [N, Q, Function.comp_def] using hscaled.comp hsnd.hasLaw
  have hmeanN : (∫ ω, N ω ∂μ) = 0 := by
    calc
      ∫ ω, N ω ∂μ = ∫ x, x ∂gaussianReal 0 v := hNlaw.integral_eq
      _ = 0 := by simp [integral_id_gaussianReal]
  have hvarN : ProbabilityTheory.covariance N N μ = c ^ 2 := by
    calc
      ProbabilityTheory.covariance N N μ = variance N μ :=
        ProbabilityTheory.covariance_self hN2.aemeasurable
      _ = variance id (gaussianReal 0 v) := hNlaw.variance_eq
      _ = c ^ 2 := by rw [variance_id_gaussianReal]; rfl
  have hXi : MemLp Xi 2 μ := hXi2
  have hXj : MemLp Xj 2 μ := hXj2
  have hN : MemLp N 2 μ := hN2
  have hXiN : Xi ⟂ᵢ[μ] N := by
    exact indepFun_prod₀ (hZ.2.1 i)
      (measurable_const_mul c).aemeasurable
  have hXjN : Xj ⟂ᵢ[μ] N := by
    exact indepFun_prod₀ (hZ.2.1 j)
      (measurable_const_mul c).aemeasurable
  have hNj : N ⟂ᵢ[μ] Xj := hXjN.symm
  have hsumCov : ProbabilityTheory.covariance (Xi + N) (Xj + N) μ =
      ProbabilityTheory.covariance Xi Xj μ + ProbabilityTheory.covariance N N μ := by
    rw [ProbabilityTheory.covariance_add_left hXi hN (hXj.add hN),
      ProbabilityTheory.covariance_add_right (X := Xi) (Y := Xj) (Z := N) hXi hXj hN,
      ProbabilityTheory.covariance_add_right (X := N) (Y := Xj) (Z := N) hN hXj hN]
    simp [ProbabilityTheory.IndepFun.covariance_eq_zero hXiN hXi hN,
      ProbabilityTheory.IndepFun.covariance_eq_zero hNj hN hXj]
  have hcovXiXj : ProbabilityTheory.covariance Xi Xj μ =
      DOZZ.gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) := by
    have hiMeasMap : AEStronglyMeasurable Zi (μ.map Prod.fst) := by
      rw [hfst.map_eq]
      exact (hZ.2.1 i).aestronglyMeasurable
    have hjMeasMap : AEStronglyMeasurable Zj (μ.map Prod.fst) := by
      rw [hfst.map_eq]
      exact (hZ.2.1 j).aestronglyMeasurable
    have hcovMap : ProbabilityTheory.covariance Zi Zj (μ.map Prod.fst) =
        ProbabilityTheory.covariance (fun ω => Zi (Prod.fst ω))
          (fun ω => Zj (Prod.fst ω)) μ :=
      ProbabilityTheory.covariance_map hiMeasMap hjMeasMap hfst.aemeasurable
    have hcovOrig : ProbabilityTheory.covariance Zi Zj P =
        DOZZ.gaussianCovariance P Zi Zj := by
      rw [ProbabilityTheory.covariance_eq_sub hiMem hjMem, hmeanZi, hmeanZj]
      simp [DOZZ.gaussianCovariance, Zi, Zj]
    calc
      ProbabilityTheory.covariance Xi Xj μ =
          ProbabilityTheory.covariance Zi Zj (μ.map Prod.fst) := by
            symm
            simpa [Xi, Xj, Zi, Zj] using hcovMap
      _ = ProbabilityTheory.covariance Zi Zj P := by rw [hfst.map_eq]
      _ = DOZZ.gaussianCovariance P Zi Zj := hcovOrig
  rw [show (fun ω : Ω × ℝ => Z ω.1 i + c * ω.2) = Xi + N by rfl,
    show (fun ω : Ω × ℝ => Z ω.1 j + c * ω.2) = Xj + N by rfl]
  rw [show DOZZ.gaussianCovariance μ (Xi + N) (Xj + N) =
      ProbabilityTheory.covariance (Xi + N) (Xj + N) μ by
        rw [ProbabilityTheory.covariance_eq_sub (hXi.add hN) (hXj.add hN)]
        have hmeanSumX : (∫ ω, (Xi + N) ω ∂μ) = 0 := by
          calc
            ∫ ω, (Xi + N) ω ∂μ = ∫ ω, Xi ω + N ω ∂μ := rfl
            _ = ∫ ω, Xi ω ∂μ + ∫ ω, N ω ∂μ :=
              integral_add (hXi.integrable (by norm_num)) (hN.integrable (by norm_num))
            _ = 0 := by rw [hmeanXi, hmeanN]; simp
        have hmeanSumY : (∫ ω, (Xj + N) ω ∂μ) = 0 := by
          calc
            ∫ ω, (Xj + N) ω ∂μ = ∫ ω, Xj ω + N ω ∂μ := rfl
            _ = ∫ ω, Xj ω ∂μ + ∫ ω, N ω ∂μ :=
              integral_add (hXj.integrable (by norm_num)) (hN.integrable (by norm_num))
            _ = 0 := by rw [hmeanXj, hmeanN]; simp
        rw [hmeanSumX, hmeanSumY]
        simp [DOZZ.gaussianCovariance]]
  rw [hsumCov, hcovXiXj, hvarN]

/-- A common independent Gaussian scalar factors out of the finite Wick chaos mass. The covariance
shift cancels from the coordinatewise Wick normalization, leaving one shared exponential factor. -/
theorem finiteChaosMass_independent_common_scalar_factor
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : DOZZ.IsCenteredJointlyGaussian P Z) (a : ι → ℝ) (γ c : ℝ)
    (ω : Ω) (z : ℝ) :
    DOZZ.finiteChaosMass (P.prod (gaussianReal 0 1))
        (fun ω i => Z ω.1 i + c * ω.2) a γ (ω, z) =
      Real.exp (γ * c * z - γ ^ 2 / 2 * c ^ 2) *
        DOZZ.finiteChaosMass P Z a γ ω := by
  classical
  have hvariance (i : ι) :
      DOZZ.gaussianVariance (P.prod (gaussianReal 0 1))
        (fun ω => Z ω.1 i + c * ω.2) =
      DOZZ.gaussianVariance P (fun ω => Z ω i) + c ^ 2 := by
    rw [DOZZ.gaussianVariance, DOZZ.gaussianVariance]
    exact gaussianCovariance_independent_common_scalar_add P Z hZ c i i
  let B : ℝ := Real.exp (γ * c * z - γ ^ 2 / 2 * c ^ 2)
  rw [DOZZ.finiteChaosMass, DOZZ.finiteChaosMass]
  calc
    (∑ i, a i * Real.exp
        (γ * (Z ω i + c * z) - γ ^ 2 / 2 *
          DOZZ.gaussianVariance (P.prod (gaussianReal 0 1))
            (fun ω => Z ω.1 i + c * ω.2))) =
      ∑ i, B * (a i * Real.exp
        (γ * Z ω i - γ ^ 2 / 2 * DOZZ.gaussianVariance P (fun ω => Z ω i))) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hvariance i]
          dsimp [B]
          rw [show γ * (Z ω i + c * z) - γ ^ 2 / 2 *
              (DOZZ.gaussianVariance P (fun ω => Z ω i) + c ^ 2) =
              (γ * c * z - γ ^ 2 / 2 * c ^ 2) +
                (γ * Z ω i - γ ^ 2 / 2 * DOZZ.gaussianVariance P (fun ω => Z ω i)) by ring,
            Real.exp_add]
          ring
    _ = B * ∑ i, a i * Real.exp
        (γ * Z ω i - γ ^ 2 / 2 * DOZZ.gaussianVariance P (fun ω => Z ω i)) := by
          rw [Finset.mul_sum]
    _ = _ := rfl

/-- The common scalar multiplies every extended finite-chaos moment by the Gaussian moment of its
shared Wick exponential. The identity is valid in `[0,∞]`, including zero weights and negative
powers. -/
theorem finiteChaosMoment_independent_common_scalar_factor
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : DOZZ.IsCenteredJointlyGaussian P Z) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (γ c p : ℝ) :
    DOZZ.finiteChaosMoment (P.prod (gaussianReal 0 1))
        (fun ω i => Z ω.1 i + c * ω.2) a γ p =
      ENNReal.ofReal (Real.exp (γ ^ 2 * c ^ 2 / 2 * (p ^ 2 - p))) *
        DOZZ.finiteChaosMoment P Z a γ p := by
  classical
  let Q : Measure ℝ := gaussianReal 0 1
  let M : Ω → ℝ := DOZZ.finiteChaosMass P Z a γ
  let G : ℝ → ℝ := fun z => Real.exp (γ * c * z - γ ^ 2 / 2 * c ^ 2)
  let F : Ω → ℝ≥0∞ := fun ω => ENNReal.rpow (ENNReal.ofReal (M ω)) p
  let H : ℝ → ℝ≥0∞ := fun z => ENNReal.rpow (ENNReal.ofReal (G z)) p
  have hmass_nonneg (ω : Ω) : 0 ≤ M ω := by
    dsimp [M, DOZZ.finiteChaosMass]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (Real.exp_nonneg _)
  have hmass_meas : AEMeasurable M P := by
    have hterm (i : ι) : AEMeasurable
        (fun ω => a i * Real.exp (γ * Z ω i - γ ^ 2 / 2 *
          DOZZ.gaussianVariance P (fun ω => Z ω i))) P := by
      have harg : AEMeasurable (fun ω => γ * Z ω i - γ ^ 2 / 2 *
          DOZZ.gaussianVariance P (fun ω => Z ω i)) P :=
        (hZ.2.1 i).const_mul γ |>.sub_const _
      exact (Real.measurable_exp.comp_aemeasurable harg).const_mul (a i)
    change AEMeasurable (fun ω => ∑ i, a i * Real.exp (γ * Z ω i - γ ^ 2 / 2 *
      DOZZ.gaussianVariance P (fun ω => Z ω i))) P
    exact Finset.aemeasurable_fun_sum Finset.univ fun i _ => hterm i
  have hFmeas : AEMeasurable F P := by
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      hmass_meas.ennreal_ofReal
  have hGmeas : Measurable G := by
    dsimp [G]
    fun_prop
  have hHmeas : AEMeasurable H Q := by
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (hGmeas.comp_aemeasurable measurable_id.aemeasurable).ennreal_ofReal
  have hGpositive (z : ℝ) : 0 < G z := Real.exp_pos _
  have hGpow (z : ℝ) : G z ^ p =
      Real.exp ((p * γ * c) * z - p * (γ ^ 2 / 2 * c ^ 2)) := by
    dsimp [G]
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  have hGintegrable : Integrable (fun z => G z ^ p) Q := by
    have hbase : Integrable (fun z : ℝ => Real.exp ((p * γ * c) * z)) Q :=
      integrable_exp_mul_gaussianReal _
    have hrepr : (fun z : ℝ => G z ^ p) = fun z =>
        Real.exp (-(p * (γ ^ 2 / 2 * c ^ 2))) * Real.exp ((p * γ * c) * z) := by
      funext z
      rw [hGpow z, ← Real.exp_add]
      congr 1
      ring
    rw [hrepr]
    exact hbase.const_mul _
  have hGmean : (∫ z, G z ^ p ∂Q) =
      Real.exp (γ ^ 2 * c ^ 2 / 2 * (p ^ 2 - p)) := by
    have hmgf : (∫ z : ℝ, Real.exp ((p * γ * c) * z) ∂Q) =
        Real.exp ((p * γ * c) ^ 2 / 2) := by
      calc
        (∫ z : ℝ, Real.exp ((p * γ * c) * z) ∂Q) = mgf id Q (p * γ * c) := rfl
        _ = Real.exp ((p * γ * c) ^ 2 / 2) := by
          rw [mgf_id_gaussianReal]
          simp
    calc
      (∫ z, G z ^ p ∂Q) =
          Real.exp (-(p * (γ ^ 2 / 2 * c ^ 2))) *
            ∫ z, Real.exp ((p * γ * c) * z) ∂Q := by
              calc
                _ = ∫ z, Real.exp (-(p * (γ ^ 2 / 2 * c ^ 2))) *
                      Real.exp ((p * γ * c) * z) ∂Q := by
                        congr 1
                        funext z
                        rw [hGpow z, ← Real.exp_add]
                        congr 1
                        ring
                _ = _ := integral_const_mul _ _
      _ = Real.exp (-(p * (γ ^ 2 / 2 * c ^ 2))) *
            Real.exp ((p * γ * c) ^ 2 / 2) := by rw [hmgf]
      _ = Real.exp (γ ^ 2 * c ^ 2 / 2 * (p ^ 2 - p)) := by
            rw [← Real.exp_add]
            congr 1
            ring
  have hHintegral : (∫⁻ z, H z ∂Q) =
      ENNReal.ofReal (Real.exp (γ ^ 2 * c ^ 2 / 2 * (p ^ 2 - p))) := by
    have hnonneg : 0 ≤ᵐ[Q] fun z => G z ^ p :=
      Filter.Eventually.of_forall fun z => Real.rpow_nonneg (le_of_lt (hGpositive z)) p
    rw [show (fun z => H z) = fun z => ENNReal.ofReal (G z ^ p) by
      funext z
      dsimp [H]
      exact ENNReal.ofReal_rpow_of_pos (hGpositive z)]
    rw [← ofReal_integral_eq_lintegral_ofReal hGintegrable hnonneg, hGmean]
  have hfactor (ω : Ω) (z : ℝ) :
      ENNReal.rpow (ENNReal.ofReal
        (DOZZ.finiteChaosMass (P.prod Q) (fun ω i => Z ω.1 i + c * ω.2)
          a γ (ω, z))) p = F ω * H z := by
    rw [show DOZZ.finiteChaosMass (P.prod Q) (fun ω i => Z ω.1 i + c * ω.2)
        a γ (ω, z) = G z * M ω by
          simpa [G, M, Q] using
            finiteChaosMass_independent_common_scalar_factor P Z hZ a γ c ω z]
    have hHp : H z = ENNReal.ofReal (G z ^ p) := by
      dsimp [H]
      exact ENNReal.ofReal_rpow_of_pos (hGpositive z)
    rw [hHp]
    simpa [F, mul_comm] using
      (ennreal_rpow_ofReal_mul_pos_left (x := M ω) (y := G z) (p := p)
        (hmass_nonneg ω) (hGpositive z))
  calc
    DOZZ.finiteChaosMoment (P.prod Q) (fun ω i => Z ω.1 i + c * ω.2) a γ p =
        ∫⁻ u, F u.1 * H u.2 ∂(P.prod Q) := by
          rw [DOZZ.finiteChaosMoment]
          apply lintegral_congr_ae
          exact ae_of_all (P.prod Q) fun u => hfactor u.1 u.2
    _ = (∫⁻ ω, F ω ∂P) * ∫⁻ z, H z ∂Q :=
          lintegral_prod_mul hFmeas hHmeas
    _ = ENNReal.ofReal (Real.exp (γ ^ 2 * c ^ 2 / 2 * (p ^ 2 - p))) *
          DOZZ.finiteChaosMoment P Z a γ p := by
          rw [hHintegral]
          rw [DOZZ.finiteChaosMoment]
          exact mul_comm _ _


end DOZZ.Proofs
