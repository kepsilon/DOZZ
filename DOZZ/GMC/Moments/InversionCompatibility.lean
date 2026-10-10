/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionCircleMixedLimit
public import DOZZ.GMC.Moments.InversionSeparatedCompatibility
public import DOZZ.GMC.Assembly.AdmissibleGMC

/-! Compatibility of the coupled inversion circle regularizations on bounded annular charts. -/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Real
open scoped Topology Distributions ENNReal
open DOZZ.Proofs.CirclePotential

namespace DOZZ.Proofs

/-- The actual inverted-test circle limits are compatible with the pulled source circles on
any bounded annular chart. Every clause is uniform on compact subsets of that chart. -/
theorem inversionCircle_compatible_of_coupled_limits
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (f : (ℂ × ℝ) → ℕ → TestFn)
    (hf : ∀ p n, tsupport (f p n : ℂ → ℝ) ⊆ inversionChart)
    (Z : Ω → ℂ → ℝ → ℝ)
    (hgap : ∀ p, Tendsto (fun n => circleEnergyGap p.1 p.2 (f p n)) atTop (𝓝 0))
    (hmem : ∀ x r, MemLp (fun ω => Z ω x r) 2 P)
    (hlim : ∀ p, Tendsto (fun n => eLpNorm (fun ω =>
      X ω (inversionTest (f p n) (hf p n)) - Z ω p.1 p.2) 2 P) atTop (𝓝 0))
    (hcov : ∀ x y r s, gaussianCovariance P (fun ω => Z ω x r) (fun ω => Z ω y s) =
      circleKernel x r y s)
    (U : Set ℂ) {m R : ℝ} (hm : 0 < m) (hR : 0 ≤ R)
    (hU : ∀ x ∈ U, 2 * m ≤ ‖x‖ ∧ ‖x‖ ≤ R) :
    IsCompatibleAdmissibleRegularizations P U 1 (min (m / 2) 1)
      (fun ω ε x => Xc ω x⁻¹ (Real.log (1 / ε)))
      (fun ω ε x => Z ω x (Real.log (1 / ε))) := by
  let : IsProbabilityMeasure P := hX.1
  let e := min (m / 2) 1
  have he1 : e ≤ 1 := min_le_right _ _
  have hem : e ≤ m / 2 := min_le_left _ _
  have hexp {ε : ℝ} (hε : 0 < ε) : Real.exp (-Real.log (1 / ε)) = ε :=
    exp_neg_log_one_div hε
  have hlog {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : 0 ≤ Real.log (1 / ε) :=
    log_one_div_nonneg_of_le_one hε hε1
  have hsrc x y r s : gaussianCovariance P (fun ω => Xc ω x⁻¹ r)
      (fun ω => Xc ω y⁻¹ s) = circleKernel x⁻¹ r y⁻¹ s :=
    isCircleAverage_covariance P X hX Xc hXc x⁻¹ y⁻¹ r s
  have hsym x y r s : circleKernel x r y s = circleKernel y s x r := by
    unfold circleKernel
    rw [← isCircleAverage_covariance P X hX Xc hXc x y r s,
      ← isCircleAverage_covariance P X hX Xc hXc y x s r]
    exact DOZZ.Assembly.gaussianCovariance_comm P _ _
  have hmix {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδe : δ ≤ e)
      (x y : ℂ) (hy : y ∈ U) :
      gaussianCovariance P (fun ω => Xc ω x⁻¹ (Real.log (1 / ε)))
        (fun ω => Z ω y (Real.log (1 / δ))) =
      circleAverage (fun u => innerPot x⁻¹ (Real.log (1 / ε)) u⁻¹) y δ := by
    have hsmall : 2 * Real.exp (-Real.log (1 / δ)) < ‖y‖ := by
      rw [hexp hδ]
      have hd := hδe.trans hem
      linarith only [hd, (hU y hy).1, hm]
    have ht := inversionCircle_source_gaussianCovariance X hX Xc hXc y
      (Real.log (1 / δ)) hsmall (fun ω => Z ω y (Real.log (1 / δ)))
      (hmem _ _) (f (y, Real.log (1 / δ))) (hf _)
      (hgap _) (hlim _) x⁻¹ (Real.log (1 / ε))
    simpa only [hexp hδ] using ht
  let C := (2 * (|Real.log m| + Real.log (R + 1)) + 2) +
    (Real.log 3 + 2 * Real.log (1 + R))
  have hC : 0 ≤ C := by
    have h1 := Real.log_nonneg (show 1 ≤ R + 1 by linarith only [hR])
    have h2 := Real.log_nonneg (show 1 ≤ 1 + R by linarith only [hR])
    have h3 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
    dsimp [C]
    linarith only [h1, h2, h3, abs_nonneg (Real.log m)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n q _hq
    exact inversionCircle_source_jointly_gaussian X hX Xc hXc
      (fun i => ((q i).1, ((q i).2.2)⁻¹, Real.log (1 / (q i).2.1)))
      (fun i ω => Z ω (q i).2.2 (Real.log (1 / (q i).2.1)))
      (fun i => hmem _ _) (fun i => f ((q i).2.2, Real.log (1 / (q i).2.1)))
      (fun i => hf _) (fun i => hlim _)
  · intro K _hK hKU
    refine ⟨C, hC, ?_⟩
    intro ε δ hε hε1 hδ hδe x hx y hy
    rw [hmix hε hδ hδe x y (hKU hy)]
    have ht := inversion_mixed_log_bound_on_annulus hm hR
      (hU y (hKU hy)).1 (hU x (hKU hx)).1
      (hU y (hKU hy)).2 (hU x (hKU hx)).2
      (hlog hδ (hδe.trans he1)) (hlog hε hε1)
      (show Real.exp (-Real.log (1 / δ)) ≤ min m 1 by
        rw [hexp hδ]; exact le_min (by linarith only [hδe, hem, hm]) (hδe.trans he1))
    simpa only [hexp hδ, hexp hε, norm_sub_rev y x, max_comm δ ε] using ht
  · intro K _hK hKU
    refine ⟨C, hC, ?_⟩
    intro k _hk ε hε hεb x hx
    have hεe := hεb.trans (min_le_left _ _)
    rw [hmix (Real.exp_pos _) hε hεe x x (hKU hx)]
    have hlogk : Real.log (1 / Real.exp (-(k : ℝ))) = k := log_one_div_exp_neg_eq _
    rw [hlogk]
    have ht := inversion_mixed_coarse_center_bound_on_annulus hm hR
      (hU x (hKU hx)).1 (hU x (hKU hx)).2 (Nat.cast_nonneg k)
      (hlog hε (hεe.trans he1))
      (show Real.exp (-Real.log (1 / ε)) ≤ min m 1 by
        rw [hexp hε]; exact le_min (by linarith only [hεe, hem, hm]) (hεe.trans he1))
      (by rw [hexp hε]; exact hεb.trans (min_le_right _ _))
    simpa only [hexp hε] using ht
  · intro K _hK hKU d hd η hη
    obtain ⟨δ, hδ, hb⟩ := inversion_separated_kernel_uniform hm hR hd hη
    refine ⟨δ, hδ, ?_⟩
    intro ε δ' hε hεb hδ' hδ'b x hx y hy hdist
    have hδ'e : δ' ≤ e := hδ'b.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [hmix hε hδ' hδ'e x y (hKU hy), hsrc, hcov]
    have ht := hb (Real.log (1 / δ')) (Real.log (1 / ε))
      (by rw [hexp hδ']; exact hδ'b.trans (min_le_left _ _))
      (by rw [hexp hε]; exact hεb.trans (min_le_left _ _))
      y x (hU y (hKU hy)).1 (hU x (hKU hx)).1
      (hU y (hKU hy)).2 (hU x (hKU hx)).2 (by simpa only [norm_sub_rev] using hdist)
    rw [hexp hδ'] at ht
    rw [hsym y⁻¹ x⁻¹ (Real.log (1 / δ')) (Real.log (1 / ε)),
      hsym y x (Real.log (1 / δ')) (Real.log (1 / ε))] at ht
    exact ht
  · intro K _hK hKU k _hk η hη
    obtain ⟨δ, hδ, hb⟩ := inversion_mixed_fixed_coarse_uniform (k : ℝ) hm hη
    refine ⟨δ, hδ, ?_⟩
    intro ε hε hεb x hx y hy
    have hεe : ε ≤ e := hεb.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [DOZZ.Assembly.gaussianCovariance_comm P (fun ω => Z ω x (Real.log (1 / ε)))]
    rw [hmix (Real.exp_pos _) hε hεe y x (hKU hx), hsrc]
    have hlogk : Real.log (1 / Real.exp (-(k : ℝ))) = k := log_one_div_exp_neg_eq _
    rw [hlogk]
    exact hb ε hε (hεb.trans (min_le_left _ _)) x (hU x (hKU hx)).1 y⁻¹

end DOZZ.Proofs
