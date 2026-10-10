/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Malmsten representation and Gamma identification
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace DOZZ.Proofs


private noncomputable def malmstenRealNumerator (x u : ℝ) : ℝ :=
  (x - 1) * Real.exp (-u) * (1 - Real.exp (-u)) +
    Real.exp (-x * u) - Real.exp (-u)

noncomputable def malmstenRealIntegrand (x u : ℝ) : ℝ :=
  ((x - 1) * Real.exp (-u) +
    (Real.exp (-x * u) - Real.exp (-u)) / (1 - Real.exp (-u))) / u

private lemma malmstenRealIntegrand_eq_num {x u : ℝ} (hu : 0 < u) :
    malmstenRealIntegrand x u =
      malmstenRealNumerator x u / (u * (1 - Real.exp (-u))) := by
  rw [malmstenRealIntegrand, malmstenRealNumerator]
  have hden : 1 - Real.exp (-u) ≠ 0 :=
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))).ne'
  field_simp [ne_of_gt hu, hden]
  ring_nf

private lemma malmstenRealNumerator_contDiff (x : ℝ) :
    ContDiff ℝ 2 (malmstenRealNumerator x) := by
  unfold malmstenRealNumerator
  fun_prop

private lemma malmstenRealNumerator_zero (x : ℝ) : malmstenRealNumerator x 0 = 0 := by
  simp [malmstenRealNumerator]

private lemma malmstenRealNumerator_deriv_zero (x : ℝ) :
    deriv (malmstenRealNumerator x) 0 = 0 := by
  unfold malmstenRealNumerator
  simp (disch := fun_prop)
  ring

private lemma malmstenRealNumerator_iteratedDerivWithin_one_zero (x : ℝ) :
    iteratedDerivWithin 1 (malmstenRealNumerator x) (Icc 0 1) 0 = 0 := by
  have hf : ContDiffAt ℝ 1 (malmstenRealNumerator x) 0 :=
    (malmstenRealNumerator_contDiff x).contDiffAt.of_le (by norm_num)
  have hEq := iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) hf (by simp)
  rw [hEq]
  simpa [iteratedDeriv_succ] using malmstenRealNumerator_deriv_zero x

private lemma malmstenRealNumerator_taylorWithinEval_zero (x u : ℝ) :
    taylorWithinEval (malmstenRealNumerator x) 1 (Icc 0 1) 0 u = 0 := by
  rw [taylor_within_apply]
  have h0 : iteratedDerivWithin 0 (malmstenRealNumerator x) (Icc 0 1) 0 = 0 := by
    simpa using malmstenRealNumerator_zero x
  have h1 := malmstenRealNumerator_iteratedDerivWithin_one_zero x
  simp [Finset.sum_range_succ, h0, h1]

private lemma exists_malmstenRealNumerator_taylor_bound (x : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Icc 0 1,
      |malmstenRealNumerator x u| ≤ C * u ^ 2 := by
  have hcont : ContDiffOn ℝ (1 + 1) (malmstenRealNumerator x) (Icc 0 1) := by
    exact (malmstenRealNumerator_contDiff x).contDiffOn.mono (Set.subset_univ _)
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound
    (f := malmstenRealNumerator x) (a := 0) (b := 1) (n := 1) (by norm_num) hcont
  refine ⟨C, ?_, ?_⟩
  · have h := hC 1 (by norm_num)
    rw [malmstenRealNumerator_taylorWithinEval_zero x 1] at h
    have h' : |malmstenRealNumerator x 1| ≤ C := by simpa using h
    exact (abs_nonneg _).trans h'
  · intro u hu
    have h := hC u hu
    rw [malmstenRealNumerator_taylorWithinEval_zero x u] at h
    simpa using h

private lemma one_sub_exp_neg_ge_linear {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (1 - Real.exp (-1)) * u ≤ 1 - Real.exp (-u) := by
  have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-1 : ℝ))
    (by positivity : 0 ≤ 1 - u) hu0 (by ring : (1 - u) + u = 1)
  have hchord : Real.exp (-u) ≤ (1 - u) * Real.exp 0 + u * Real.exp (-1) := by
    simpa [smul_eq_mul] using hconv
  have h := sub_le_sub_left hchord 1
  calc
    (1 - Real.exp (-1)) * u =
        1 - ((1 - u) * Real.exp 0 + u * Real.exp (-1)) := by
          simp [Real.exp_zero]
          ring
    _ ≤ 1 - Real.exp (-u) := h

private lemma malmstenRealIntegrand_norm_le_local {x u C : ℝ}
    (hC : 0 ≤ C)
    (hTaylor : ∀ u ∈ Icc 0 1, |malmstenRealNumerator x u| ≤ C * u ^ 2)
    (hu : 0 < u) (hu1 : u ≤ 1) :
    |malmstenRealIntegrand x u| ≤ C / (1 - Real.exp (-1)) := by
  have hc : 0 < 1 - Real.exp (-1) := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hden : 0 < u * (1 - Real.exp (-u)) := by
    apply mul_pos hu
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hdenLower : (1 - Real.exp (-1)) * u ^ 2 ≤ u * (1 - Real.exp (-u)) := by
    have hlinear := one_sub_exp_neg_ge_linear hu.le hu1
    calc
      (1 - Real.exp (-1)) * u ^ 2 = u * ((1 - Real.exp (-1)) * u) := by ring
      _ ≤ u * (1 - Real.exp (-u)) := mul_le_mul_of_nonneg_left hlinear hu.le
  rw [malmstenRealIntegrand_eq_num hu]
  rw [abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).2
  have hnum := hTaylor u ⟨hu.le, hu1⟩
  calc
    |malmstenRealNumerator x u| ≤ C * u ^ 2 := hnum
    _ = (C / (1 - Real.exp (-1))) * ((1 - Real.exp (-1)) * u ^ 2) := by
      field_simp [hc.ne']
    _ ≤ (C / (1 - Real.exp (-1))) * (u * (1 - Real.exp (-u))) :=
      mul_le_mul_of_nonneg_left hdenLower (by positivity)

private lemma malmstenRealIntegrand_measurable (x : ℝ) :
    Measurable (malmstenRealIntegrand x) := by
  unfold malmstenRealIntegrand
  fun_prop

private lemma malmstenRealIntegrand_aestronglyMeasurable (x : ℝ) :
    AEStronglyMeasurable (malmstenRealIntegrand x) volume :=
  (malmstenRealIntegrand_measurable x).aestronglyMeasurable

private lemma malmstenRealIntegrand_integrableOn_Ioc {x : ℝ} (_hx : 0 < x) :
    IntegrableOn (malmstenRealIntegrand x) (Ioc 0 1) := by
  obtain ⟨C, hC, hTaylor⟩ := exists_malmstenRealNumerator_taylor_bound x
  have hc : 0 < 1 - Real.exp (-1) := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hmeas := malmstenRealIntegrand_aestronglyMeasurable x
  apply Measure.integrableOn_of_bounded (s := Ioc 0 1) (μ := volume) (by simp) hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hbound := malmstenRealIntegrand_norm_le_local hC hTaylor hu.1 hu.2
  simpa [Real.norm_eq_abs] using hbound

private lemma malmstenRealIntegrand_norm_le_tail {x u : ℝ} (_hx : 0 < x)
    (hu : 1 ≤ u) :
    |malmstenRealIntegrand x u| ≤
      ((|x - 1| + 1) / (1 - Real.exp (-1))) * Real.exp (-u) +
        (1 / (1 - Real.exp (-1))) * Real.exp (-x * u) := by
  have hc : 0 < 1 - Real.exp (-1) := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have huPos : 0 < u := by linarith
  have hexp : Real.exp (-u) ≤ Real.exp (-1) :=
    Real.exp_le_exp.mpr (by linarith)
  have hden : 1 - Real.exp (-1) ≤ 1 - Real.exp (-u) := by linarith
  have hden' : 0 < u * (1 - Real.exp (-u)) := by
    apply mul_pos huPos
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hfac : 0 ≤ 1 - Real.exp (-u) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hdenLower : 1 - Real.exp (-1) ≤ u * (1 - Real.exp (-u)) := by
    calc
      1 - Real.exp (-1) ≤ 1 - Real.exp (-u) := hden
      _ ≤ u * (1 - Real.exp (-u)) := by
        exact le_mul_of_one_le_left hfac hu
  have hfac' : 1 - Real.exp (-u) ≤ 1 := by
    linarith [Real.exp_pos (-u)]
  have hnum :
      |malmstenRealNumerator x u| ≤
        (|x - 1| + 1) * Real.exp (-u) + Real.exp (-x * u) := by
    unfold malmstenRealNumerator
    have ha :
        |(x - 1) * Real.exp (-u) * (1 - Real.exp (-u))| =
          |x - 1| * Real.exp (-u) * (1 - Real.exp (-u)) := by
      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hfac]
    have hb :
        |Real.exp (-x * u) - Real.exp (-u)| ≤ Real.exp (-x * u) + Real.exp (-u) := by
      simpa [abs_of_pos (Real.exp_pos _)] using
        (abs_sub_le (Real.exp (-x * u)) 0 (Real.exp (-u)))
    calc
      |(x - 1) * Real.exp (-u) * (1 - Real.exp (-u)) +
          Real.exp (-x * u) - Real.exp (-u)| =
          |(x - 1) * Real.exp (-u) * (1 - Real.exp (-u)) +
            (Real.exp (-x * u) - Real.exp (-u))| := by congr 1; ring_nf
      _ ≤ |(x - 1) * Real.exp (-u) * (1 - Real.exp (-u))| +
            |Real.exp (-x * u) - Real.exp (-u)| := abs_add_le _ _
      _ ≤ |x - 1| * Real.exp (-u) * (1 - Real.exp (-u)) +
            Real.exp (-x * u) + Real.exp (-u) := by rw [ha]; linarith [hb]
      _ ≤ (|x - 1| + 1) * Real.exp (-u) + Real.exp (-x * u) := by
        have hp : 0 ≤ |x - 1| * Real.exp (-u) :=
          mul_nonneg (abs_nonneg _) (le_of_lt (Real.exp_pos _))
        have hq : 0 ≤ 1 - (1 - Real.exp (-u)) := by linarith
        nlinarith [mul_nonneg hp hq]
  rw [malmstenRealIntegrand_eq_num huPos, abs_div, abs_of_pos hden']
  have huInv : (u * (1 - Real.exp (-u)))⁻¹ ≤ (1 - Real.exp (-1))⁻¹ :=
    (inv_le_inv₀ hden' hc).2 hdenLower
  have hMnonneg : 0 ≤ (|x - 1| + 1) * Real.exp (-u) + Real.exp (-x * u) := by positivity
  calc
    |malmstenRealNumerator x u| / (u * (1 - Real.exp (-u))) ≤
        ((|x - 1| + 1) * Real.exp (-u) + Real.exp (-x * u)) /
          (u * (1 - Real.exp (-u))) := div_le_div_of_nonneg_right hnum (le_of_lt hden')
    _ = ((|x - 1| + 1) * Real.exp (-u) + Real.exp (-x * u)) *
          (u * (1 - Real.exp (-u)))⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ ((|x - 1| + 1) * Real.exp (-u) + Real.exp (-x * u)) *
          (1 - Real.exp (-1))⁻¹ := mul_le_mul_of_nonneg_left huInv hMnonneg
    _ = ((|x - 1| + 1) / (1 - Real.exp (-1))) * Real.exp (-u) +
      (1 / (1 - Real.exp (-1))) * Real.exp (-x * u) := by
      field_simp [hc.ne']

private lemma malmstenRealIntegrand_integrableOn_Ioi_one {x : ℝ} (hx : 0 < x) :
    IntegrableOn (malmstenRealIntegrand x) (Ioi 1) := by
  have hc : 0 < 1 - Real.exp (-1) := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  let A : ℝ := (|x - 1| + 1) / (1 - Real.exp (-1))
  let B : ℝ := 1 / (1 - Real.exp (-1))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmajor1 : IntegrableOn (fun u : ℝ => A * Real.exp (-u)) (Ioi 1) := by
    change Integrable (fun u : ℝ => A * Real.exp (-u)) (volume.restrict (Ioi 1))
    simpa [mul_comm] using (exp_neg_integrableOn_Ioi 1 (b := 1) (by norm_num)).const_mul A
  have hmajor2 : IntegrableOn (fun u : ℝ => B * Real.exp (-x * u)) (Ioi 1) := by
    change Integrable (fun u : ℝ => B * Real.exp (-x * u)) (volume.restrict (Ioi 1))
    simpa [mul_comm] using (exp_neg_integrableOn_Ioi 1 (b := x) hx).const_mul B
  have hmajor : IntegrableOn (fun u : ℝ => A * Real.exp (-u) + B * Real.exp (-x * u))
      (Ioi 1) := hmajor1.add hmajor2
  apply Integrable.mono' hmajor (malmstenRealIntegrand_aestronglyMeasurable x).restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hbound := malmstenRealIntegrand_norm_le_tail hx hu.le
  simpa [A, B] using hbound

theorem malmstenRealIntegrand_integrableOn {x : ℝ} (hx : 0 < x) :
    IntegrableOn (malmstenRealIntegrand x) (Ioi 0) := by
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    ext u
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro hu
      by_cases hle : u ≤ 1
      · exact Or.inl ⟨hu, hle⟩
      · exact Or.inr (lt_of_not_ge hle)
    · rintro (⟨hu, _⟩ | hu)
      · exact hu
      · linarith
  rw [hsplit, integrableOn_union]
  exact ⟨malmstenRealIntegrand_integrableOn_Ioc hx,
    malmstenRealIntegrand_integrableOn_Ioi_one hx⟩

noncomputable def malmstenRealH (x : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), malmstenRealIntegrand x u

private lemma malmstenRealIntegrand_convex_inequality {x y a b u : ℝ}
    (hu : 0 < u) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    malmstenRealIntegrand (a * x + b * y) u ≤
      a * malmstenRealIntegrand x u + b * malmstenRealIntegrand y u := by
  have hden : 0 < u * (1 - Real.exp (-u)) := by
    apply mul_pos hu
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hconv := convexOn_exp.2 (Set.mem_univ (-x * u)) (Set.mem_univ (-y * u)) ha hb hab
  have hexp : Real.exp (-(a * x + b * y) * u) ≤
      a * Real.exp (-x * u) + b * Real.exp (-y * u) := by
    convert hconv using 1; ring_nf
  have hnum :
    malmstenRealNumerator (a * x + b * y) u ≤
        a * malmstenRealNumerator x u + b * malmstenRealNumerator y u := by
    unfold malmstenRealNumerator
    have hcoeff : a * x + b * y - 1 = a * (x - 1) + b * (y - 1) := by
      calc
        a * x + b * y - 1 = a * x + b * y - (a + b) := by rw [hab]
        _ = a * (x - 1) + b * (y - 1) := by ring
    have hlinear :
        (a * x + b * y - 1) * Real.exp (-u) * (1 - Real.exp (-u)) -
            Real.exp (-u) =
          a * ((x - 1) * Real.exp (-u) * (1 - Real.exp (-u)) - Real.exp (-u)) +
            b * ((y - 1) * Real.exp (-u) * (1 - Real.exp (-u)) - Real.exp (-u)) := by
      linear_combination
        (Real.exp (-u) * (1 - Real.exp (-u))) * hcoeff +
          Real.exp (-u) * hab
    calc
      _ = ((a * x + b * y) - 1) * Real.exp (-u) * (1 - Real.exp (-u)) -
          Real.exp (-u) + Real.exp (-(a * x + b * y) * u) := by ring
      _ = Real.exp (-(a * x + b * y) * u) +
          ((a * x + b * y - 1) * Real.exp (-u) * (1 - Real.exp (-u)) - Real.exp (-u)) := by ring
      _ ≤ (a * Real.exp (-x * u) + b * Real.exp (-y * u)) +
          ((a * x + b * y - 1) * Real.exp (-u) * (1 - Real.exp (-u)) - Real.exp (-u)) := by
            let A := (a * x + b * y - 1) * Real.exp (-u) * (1 - Real.exp (-u)) -
              Real.exp (-u)
            have h := add_le_add_right hexp A
            calc
              _ = A + Real.exp (-(a * x + b * y) * u) := by dsimp [A]; ring
              _ ≤ A + (a * Real.exp (-x * u) + b * Real.exp (-y * u)) := h
              _ = _ := by dsimp [A]; ring
      _ = a * malmstenRealNumerator x u + b * malmstenRealNumerator y u := by
            unfold malmstenRealNumerator
            linear_combination hlinear
  rw [malmstenRealIntegrand_eq_num hu, malmstenRealIntegrand_eq_num hu,
    malmstenRealIntegrand_eq_num hu]
  calc
    malmstenRealNumerator (a * x + b * y) u / (u * (1 - Real.exp (-u))) ≤
        (a * malmstenRealNumerator x u + b * malmstenRealNumerator y u) /
          (u * (1 - Real.exp (-u))) := div_le_div_of_nonneg_right hnum (le_of_lt hden)
    _ = a * (malmstenRealNumerator x u / (u * (1 - Real.exp (-u)))) +
          b * (malmstenRealNumerator y u / (u * (1 - Real.exp (-u)))) := by
      field_simp [hden.ne']

private lemma malmstenRealH_convexOn : ConvexOn ℝ (Ioi 0) malmstenRealH := by
  refine ⟨convex_Ioi _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz : 0 < a * x + b * y := by
    rcases le_total x y with hxy | hyx
    · have hmul := mul_le_mul_of_nonneg_left hxy hb
      have hle : x ≤ a * x + b * y := by
        calc
          x = (a + b) * x := by rw [hab]; ring
          _ = a * x + b * x := by ring
          _ ≤ a * x + b * y := by nlinarith [hmul]
      exact lt_of_lt_of_le hx hle
    · have hmul : a * y ≤ a * x := mul_le_mul_of_nonneg_left hyx ha
      have hle : y ≤ a * x + b * y := by
        calc
          y = (a + b) * y := by rw [hab]; ring
          _ = a * y + b * y := by ring
          _ ≤ a * x + b * y := by nlinarith [hmul]
      exact lt_of_lt_of_le hy hle
  have hix := malmstenRealIntegrand_integrableOn hx
  have hiy := malmstenRealIntegrand_integrableOn hy
  have hiz := malmstenRealIntegrand_integrableOn hz
  have hiR : IntegrableOn
      (fun u : ℝ => a * malmstenRealIntegrand x u + b * malmstenRealIntegrand y u)
      (Ioi 0) := by
    have hx' : IntegrableOn (fun u : ℝ => a * malmstenRealIntegrand x u) (Ioi 0) := by
      change Integrable (fun u : ℝ => a * malmstenRealIntegrand x u)
        (volume.restrict (Ioi 0))
      exact hix.const_mul a
    have hy' : IntegrableOn (fun u : ℝ => b * malmstenRealIntegrand y u) (Ioi 0) := by
      change Integrable (fun u : ℝ => b * malmstenRealIntegrand y u)
        (volume.restrict (Ioi 0))
      exact hiy.const_mul b
    exact hx'.add hy'
  have hpoint : malmstenRealIntegrand (a * x + b * y) ≤ᵐ[volume.restrict (Ioi 0)]
      (fun u : ℝ => a * malmstenRealIntegrand x u + b * malmstenRealIntegrand y u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact malmstenRealIntegrand_convex_inequality hu ha hb hab
  have hle := integral_mono_ae (μ := volume.restrict (Ioi 0)) hiz hiR hpoint
  change (∫ u in Ioi (0 : ℝ), malmstenRealIntegrand (a * x + b * y) u) ≤ _ at hle
  rw [integral_add (hix.const_mul a) (hiy.const_mul b), integral_const_mul,
    integral_const_mul] at hle
  simpa [malmstenRealH, smul_eq_mul] using hle

theorem malmstenRealIntegrand_add_one_sub {x u : ℝ} (hu : 0 < u) :
    malmstenRealIntegrand (x + 1) u - malmstenRealIntegrand x u =
      u⁻¹ * (Real.exp (-u) - Real.exp (-x * u)) := by
  rw [malmstenRealIntegrand_eq_num hu, malmstenRealIntegrand_eq_num hu]
  unfold malmstenRealNumerator
  have hden : 1 - Real.exp (-u) ≠ 0 :=
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))).ne'
  rw [show -(x + 1) * u = -u + -(x * u) by ring, Real.exp_add]
  field_simp [hden, ne_of_gt hu]
  ring_nf

private lemma malmstenRealH_add_one {x : ℝ} (hx : 0 < x) :
    malmstenRealH (x + 1) = malmstenRealH x + Real.log x := by
  have hix1 := malmstenRealIntegrand_integrableOn (add_pos hx one_pos)
  have hix := malmstenRealIntegrand_integrableOn hx
  have hsub := hix1.sub hix
  have hpoint : ∀ u ∈ Ioi (0 : ℝ),
      malmstenRealIntegrand (x + 1) u - malmstenRealIntegrand x u =
        u⁻¹ * (Real.exp (-u) - Real.exp (-x * u)) := by
    intro u hu
    exact malmstenRealIntegrand_add_one_sub hu
  have hint : IntegrableOn
      (fun u : ℝ => u⁻¹ * (Real.exp (-u) - Real.exp (-x * u))) (Ioi 0) := by
    apply hsub.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact hpoint u hu
  have hloc : LocallyIntegrableOn (fun u : ℝ => Real.exp (-u)) (Ioi 0) := by
    have hcont : Continuous (fun u : ℝ => Real.exp (-u)) := by fun_prop
    exact hcont.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have hzero : Tendsto (fun u : ℝ => Real.exp (-u)) (𝓝[>] 0) (𝓝 1) := by
    have hcont : ContinuousAt (fun u : ℝ => Real.exp (-u)) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hinf : Tendsto (fun u : ℝ => Real.exp (-u)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hintF : IntegrableOn
      (fun u : ℝ => u⁻¹ • (Real.exp (-(1 * u)) - Real.exp (-(x * u)))) (Ioi 0) := by
    simpa [smul_eq_mul] using hint
  have hfr := Frullani.integral_Ioi_eq hloc one_pos hx hzero hinf hintF
  have hfr' :
      ∫ u in Ioi (0 : ℝ), u⁻¹ * (Real.exp (-u) - Real.exp (-x * u)) = Real.log x := by
    simpa [smul_eq_mul, one_mul] using hfr
  have hInt :
      ∫ u in Ioi (0 : ℝ),
          (malmstenRealIntegrand (x + 1) u - malmstenRealIntegrand x u) =
        ∫ u in Ioi (0 : ℝ), u⁻¹ * (Real.exp (-u) - Real.exp (-x * u)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    exact hpoint
  have hsubEval :
      ∫ u in Ioi (0 : ℝ),
          (malmstenRealIntegrand (x + 1) u - malmstenRealIntegrand x u) = Real.log x := by
    rw [hInt, hfr']
  have hsubEq :
      (∫ u in Ioi (0 : ℝ), malmstenRealIntegrand (x + 1) u) -
        ∫ u in Ioi (0 : ℝ), malmstenRealIntegrand x u =
      ∫ u in Ioi (0 : ℝ),
        (malmstenRealIntegrand (x + 1) u - malmstenRealIntegrand x u) := by
    rw [integral_sub hix1 hix]
  unfold malmstenRealH
  linarith [hsubEval, hsubEq]

private lemma malmstenRealH_one : malmstenRealH 1 = 0 := by
  unfold malmstenRealH malmstenRealIntegrand
  simp

private noncomputable def malmstenRealExp (x : ℝ) : ℝ := Real.exp (malmstenRealH x)

theorem malmstenRealH_exp_eq_Gamma {x : ℝ} (hx : 0 < x) :
    Real.exp (malmstenRealH x) = Real.Gamma x := by
  change malmstenRealExp x = Real.Gamma x
  have hconv : ConvexOn ℝ (Ioi 0) (Real.log ∘ malmstenRealExp) := by
    have heq : (Real.log ∘ malmstenRealExp) = malmstenRealH := by
      funext y
      simp [Function.comp_apply, malmstenRealExp, Real.log_exp]
    rw [heq]
    exact malmstenRealH_convexOn
  have hfeq : ∀ {y : ℝ}, 0 < y →
      malmstenRealExp (y + 1) = y * malmstenRealExp y := by
    intro y hy
    rw [malmstenRealExp, malmstenRealExp, malmstenRealH_add_one hy,
      Real.exp_add, Real.exp_log hy]
    ring
  have hpos : ∀ {y : ℝ}, 0 < y → 0 < malmstenRealExp y := by
    intro y hy
    exact Real.exp_pos _
  have hone : malmstenRealExp 1 = 1 := by
    rw [malmstenRealExp, malmstenRealH_one, Real.exp_zero]
  exact (Real.eq_Gamma_of_log_convex hconv hfeq hpos hone) hx

end DOZZ.Proofs

end
