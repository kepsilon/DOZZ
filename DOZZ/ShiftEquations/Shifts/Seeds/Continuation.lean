/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Shifts.Seeds.Reflection
public import DOZZ.ShiftEquations.DualR.Segment
public import DOZZ.ShiftEquations.Shift.FullShift
import DOZZ.ShiftEquations.DualR.SegFactors
import DOZZ.ShiftEquations.Shift.Wrappers
import DOZZ.FourPoint.Crossing.GammaHalfCrossing
import DOZZ.Correlations.Analytic.StructureConstantHolomorphic
import DOZZ.Brownian.Reflection.RtheorAnalytic
import DOZZ.Hypergeom.PhysicalRange

/-!
# Continuation of the dual reflection identity in the first charge

For fixed spectators `α₂, α₃ < Q`, the dual reflection identity
`C(α₁ - 2/γ, α₂, α₃) r(α₁) = R(α₁) C(2Q - α₁ - 2/γ, α₂, α₃)` (`r` the ratio of [KRV, (Fundrelation)]
at the dual Gauss parameters) holds on the whole interval `2Q + 2/γ - α₂ - α₃ < α₁ < Q` once it
holds near `Q`. Every factor continues meromorphically in the first charge: the two structure
constants through the holomorphic extension (`structureConstantH`, from
`unitVolumeStructureConstant_holomorphic_near_extended_domain`), the ratio through complex Gamma,
and the reflection coefficient through the representation of `R̄`, available from the γ/2 crossing
(`reflectionBarR_holomorphic_representation_of_crossing`). The shifted and reflected triples are
ordinary Seiberg on the interval, the Gauss parameters satisfy `0 < a < b < c < 1` (physical range),
and `p_α ∈ (0, 1)`, so both sides are analytic at every real point; the segment identity theorem
(`eq_at_one_of_segment`) concludes. This is the continuation step in the derivation of the dual
crossing seeds.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-! ### The Gauss coefficient ratio with complex Gamma -/

/-- The ratio `gaussCoefficientRatio` of [KRV, (Fundrelation)] with complex arguments and complex
Gamma. -/
noncomputable def gaussCoefficientRatioC (a b c : ℂ) : ℂ :=
  -(Complex.Gamma c ^ 2 * Complex.Gamma (1 - a) * Complex.Gamma (1 - b) *
      Complex.Gamma (a - c + 1) * Complex.Gamma (b - c + 1)) /
    (Complex.Gamma (2 - c) ^ 2 * Complex.Gamma (c - a) * Complex.Gamma (c - b) *
      Complex.Gamma a * Complex.Gamma b)

theorem gaussCoefficientRatioC_ofReal (a b c : ℝ) :
    gaussCoefficientRatioC (a : ℂ) (b : ℂ) (c : ℂ) = (gaussCoefficientRatio a b c : ℂ) := by
  have h : ∀ x : ℝ, (Real.Gamma x : ℂ) = Complex.Gamma (x : ℂ) := fun x =>
    (Complex.Gamma_ofReal x).symm
  unfold gaussCoefficientRatioC gaussCoefficientRatio
  push_cast [h]
  ring

/-- The complex ratio `gaussCoefficientRatioC` is meromorphic along analytic parameter curves. -/
theorem meromorphicAt_gaussCoefficientRatioC_comp {fa fb fc : ℂ → ℂ} {t : ℂ}
    (ha : AnalyticAt ℂ fa t) (hb : AnalyticAt ℂ fb t) (hc : AnalyticAt ℂ fc t) :
    MeromorphicAt (fun t => gaussCoefficientRatioC (fa t) (fb t) (fc t)) t := by
  have hG : ∀ g : ℂ → ℂ, AnalyticAt ℂ g t → MeromorphicAt (fun t => Complex.Gamma (g t)) t :=
    fun g hg => (meromorphicAt_complexGamma (g t)).comp_analyticAt hg
  have hone : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) t := analyticAt_const
  have htwo : AnalyticAt ℂ (fun _ : ℂ => (2 : ℂ)) t := analyticAt_const
  have h1 := hG fc hc
  have h2 := hG (fun t => 1 - fa t) (hone.sub ha)
  have h3 := hG (fun t => 1 - fb t) (hone.sub hb)
  have h4 := hG (fun t => fa t - fc t + 1) ((ha.sub hc).add hone)
  have h5 := hG (fun t => fb t - fc t + 1) ((hb.sub hc).add hone)
  have h6 := hG (fun t => 2 - fc t) (htwo.sub hc)
  have h7 := hG (fun t => fc t - fa t) (hc.sub ha)
  have h8 := hG (fun t => fc t - fb t) (hc.sub hb)
  have h9 := hG fa ha
  have h10 := hG fb hb
  unfold gaussCoefficientRatioC
  exact (((((h1.fun_pow 2).fun_mul h2).fun_mul h3).fun_mul h4).fun_mul h5).fun_neg.fun_div
    (((((h6.fun_pow 2).fun_mul h7).fun_mul h8).fun_mul h9).fun_mul h10)

/-- The complex ratio `gaussCoefficientRatioC` is analytic at a parameter point
`0 < a < b < c < 1`. -/
theorem analyticAt_gaussCoefficientRatioC_comp {fa fb fc : ℂ → ℂ} {t : ℂ}
    (hfa : AnalyticAt ℂ fa t) (hfb : AnalyticAt ℂ fb t) (hfc : AnalyticAt ℂ fc t)
    {a b c : ℝ} (ha : fa t = a) (hb : fb t = b) (hc : fc t = c)
    (ha0 : 0 < a) (hab : a < b) (hbc : b < c) (hc1 : c < 1) :
    AnalyticAt ℂ (fun t => gaussCoefficientRatioC (fa t) (fb t) (fc t)) t := by
  have hΓ : ∀ (g : ℂ → ℂ) (r : ℝ), AnalyticAt ℂ g t → g t = (r : ℂ) → 0 < r →
      AnalyticAt ℂ (fun t => Complex.Gamma (g t)) t := fun g r hg hgr hr =>
    AnalyticAt.comp_of_eq (analyticAt_Gamma_ofReal_pos hr) hg hgr
  have hΓne : ∀ (g : ℂ → ℂ) (r : ℝ), g t = (r : ℂ) → 0 < r → Complex.Gamma (g t) ≠ 0 :=
    fun g r hgr hr => by
      rw [hgr]
      exact Complex.Gamma_ne_zero_of_re_pos (by rw [Complex.ofReal_re]; exact hr)
  have e2 : (fun t => 1 - fa t) t = ((1 - a : ℝ) : ℂ) := by simp [ha]
  have e3 : (fun t => 1 - fb t) t = ((1 - b : ℝ) : ℂ) := by simp [hb]
  have e4 : (fun t => fa t - fc t + 1) t = ((a - c + 1 : ℝ) : ℂ) := by simp [ha, hc]
  have e5 : (fun t => fb t - fc t + 1) t = ((b - c + 1 : ℝ) : ℂ) := by simp [hb, hc]
  have e6 : (fun t => 2 - fc t) t = ((2 - c : ℝ) : ℂ) := by simp [hc]
  have e7 : (fun t => fc t - fa t) t = ((c - a : ℝ) : ℂ) := by simp [ha, hc]
  have e8 : (fun t => fc t - fb t) t = ((c - b : ℝ) : ℂ) := by simp [hb, hc]
  have p2 : (0 : ℝ) < 1 - a := by linarith
  have p3 : (0 : ℝ) < 1 - b := by linarith
  have p4 : (0 : ℝ) < a - c + 1 := by linarith
  have p5 : (0 : ℝ) < b - c + 1 := by linarith
  have p6 : (0 : ℝ) < 2 - c := by linarith
  have p7 : (0 : ℝ) < c - a := by linarith
  have p8 : (0 : ℝ) < c - b := by linarith
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  have hone : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) t := analyticAt_const
  have htwo : AnalyticAt ℂ (fun _ : ℂ => (2 : ℂ)) t := analyticAt_const
  have a1 := hΓ fc c hfc hc hc0
  have a2 := hΓ (fun t => 1 - fa t) _ (hone.sub hfa) e2 p2
  have a3 := hΓ (fun t => 1 - fb t) _ (hone.sub hfb) e3 p3
  have a4 := hΓ (fun t => fa t - fc t + 1) _ ((hfa.sub hfc).add hone) e4 p4
  have a5 := hΓ (fun t => fb t - fc t + 1) _ ((hfb.sub hfc).add hone) e5 p5
  have a6 := hΓ (fun t => 2 - fc t) _ (htwo.sub hfc) e6 p6
  have a7 := hΓ (fun t => fc t - fa t) _ (hfc.sub hfa) e7 p7
  have a8 := hΓ (fun t => fc t - fb t) _ (hfc.sub hfb) e8 p8
  have a9 := hΓ fa a hfa ha ha0
  have a10 := hΓ fb b hfb hb hb0
  have hden : Complex.Gamma (2 - fc t) ^ 2 * Complex.Gamma (fc t - fa t) *
      Complex.Gamma (fc t - fb t) * Complex.Gamma (fa t) * Complex.Gamma (fb t) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (pow_ne_zero 2 (hΓne (fun t => 2 - fc t) _ e6 p6))
      (hΓne (fun t => fc t - fa t) _ e7 p7)) (hΓne (fun t => fc t - fb t) _ e8 p8))
      (hΓne fa a ha ha0)) (hΓne fb b hb hb0)
  unfold gaussCoefficientRatioC
  exact (((((a1.fun_pow 2).fun_mul a2).fun_mul a3).fun_mul a4).fun_mul a5).fun_neg.fun_div
    (((((a6.fun_pow 2).fun_mul a7).fun_mul a8).fun_mul a9).fun_mul a10) hden

/-! ### The dual Gauss parameters and the two charge lines -/

/-- The dual Gauss parameter `a` as an affine function of the complexified first charge. -/
noncomputable def dualParamA (γ α₂ α₃ : ℝ) (z : ℂ) : ℂ :=
  (gaussParameterA γ (2 / γ) 0 α₂ α₃ : ℂ) + z / γ

/-- The dual Gauss parameter `b` as an affine function of the complexified first charge. -/
noncomputable def dualParamB (γ α₂ α₃ : ℝ) (z : ℂ) : ℂ :=
  (gaussParameterB γ (2 / γ) 0 α₂ α₃ : ℂ) + z / γ

/-- The dual Gauss parameter `c` as an affine function of the complexified first charge. -/
noncomputable def dualParamC (γ : ℝ) (z : ℂ) : ℂ :=
  (gaussParameterC γ (2 / γ) 0 : ℂ) + 2 * z / γ

theorem dualParamA_ofReal {γ : ℝ} (hγ : γ ≠ 0) (α₁ α₂ α₃ : ℝ) :
    dualParamA γ α₂ α₃ (α₁ : ℂ) = (gaussParameterA γ (2 / γ) α₁ α₂ α₃ : ℂ) := by
  have hγc : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ
  unfold dualParamA gaussParameterA
  push_cast
  field_simp
  ring

theorem dualParamB_ofReal {γ : ℝ} (hγ : γ ≠ 0) (α₁ α₂ α₃ : ℝ) :
    dualParamB γ α₂ α₃ (α₁ : ℂ) = (gaussParameterB γ (2 / γ) α₁ α₂ α₃ : ℂ) := by
  have hγc : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ
  unfold dualParamB gaussParameterB
  push_cast
  field_simp
  ring

theorem dualParamC_ofReal {γ : ℝ} (hγ : γ ≠ 0) (α₁ : ℝ) :
    dualParamC γ (α₁ : ℂ) = (gaussParameterC γ (2 / γ) α₁ : ℂ) := by
  have hγc : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ
  unfold dualParamC gaussParameterC
  push_cast
  field_simp
  ring

theorem differentiable_dualParamA (γ α₂ α₃ : ℝ) : Differentiable ℂ (dualParamA γ α₂ α₃) := by
  unfold dualParamA
  fun_prop

theorem differentiable_dualParamB (γ α₂ α₃ : ℝ) : Differentiable ℂ (dualParamB γ α₂ α₃) := by
  unfold dualParamB
  fun_prop

theorem differentiable_dualParamC (γ : ℝ) : Differentiable ℂ (dualParamC γ) := by
  unfold dualParamC
  fun_prop

/-- The shifted triple `(z - 2/γ, α₂, α₃)` as a complex charge line. -/
noncomputable def dualShiftedLine (γ α₂ α₃ : ℝ) (z : ℂ) : Fin 3 → ℂ :=
  ![z - 2 / γ, (α₂ : ℂ), (α₃ : ℂ)]

/-- The reflected triple `(2Q - z - 2/γ, α₂, α₃)` as a complex charge line. -/
noncomputable def dualReflectedLine (γ α₂ α₃ : ℝ) (z : ℂ) : Fin 3 → ℂ :=
  ![2 * (Q γ : ℂ) - z - 2 / γ, (α₂ : ℂ), (α₃ : ℂ)]

theorem dualShiftedLine_ofReal (γ α₁ α₂ α₃ : ℝ) :
    dualShiftedLine γ α₂ α₃ (α₁ : ℂ) = complexifyNCharges ![α₁ - 2 / γ, α₂, α₃] := by
  rw [← vec3_ofReal]
  unfold dualShiftedLine
  push_cast
  rfl

theorem dualReflectedLine_ofReal (γ α₁ α₂ α₃ : ℝ) :
    dualReflectedLine γ α₂ α₃ (α₁ : ℂ) =
      complexifyNCharges ![2 * Q γ - α₁ - 2 / γ, α₂, α₃] := by
  rw [← vec3_ofReal]
  unfold dualReflectedLine
  push_cast
  rfl

theorem differentiable_dualShiftedLine (γ α₂ α₃ : ℝ) :
    Differentiable ℂ (dualShiftedLine γ α₂ α₃) := by
  rw [differentiable_pi]
  intro i
  fin_cases i
  · change Differentiable ℂ fun z : ℂ => z - 2 / (γ : ℂ)
    fun_prop
  · exact differentiable_const _
  · exact differentiable_const _

theorem differentiable_dualReflectedLine (γ α₂ α₃ : ℝ) :
    Differentiable ℂ (dualReflectedLine γ α₂ α₃) := by
  rw [differentiable_pi]
  intro i
  fin_cases i
  · change Differentiable ℂ fun z : ℂ => 2 * (Q γ : ℂ) - z - 2 / (γ : ℂ)
    fun_prop
  · exact differentiable_const _
  · exact differentiable_const _

/-! ### The two sides of the dual reflection identity, continued in the first charge -/

/-- The left side `C(z - 2/γ, α₂, α₃) r(z)`, from an extension `f` of the unit-volume structure
constant. -/
noncomputable def dualReflLeft (f : (Fin 3 → ℂ) → ℂ) (γ μ α₂ α₃ : ℝ) (z : ℂ) : ℂ :=
  structureConstantH f γ μ (dualShiftedLine γ α₂ α₃ z) *
    gaussCoefficientRatioC (dualParamA γ α₂ α₃ z) (dualParamB γ α₂ α₃ z) (dualParamC γ z)

/-- The right side `R(z) C(2Q - z - 2/γ, α₂, α₃)`, from an extension `G` of `R̄`. -/
noncomputable def dualReflRight (f : (Fin 3 → ℂ) → ℂ) (G : ℂ → ℂ) (γ μ α₂ α₃ : ℝ)
    (z : ℂ) : ℂ :=
  reflectionRFromBar γ μ G z * structureConstantH f γ μ (dualReflectedLine γ α₂ α₃ z)

/-- Charges below `Q` with positive zero mode satisfy the extended Seiberg bounds. -/
theorem seeds_extendedSeiberg3_of_sExp_pos {γ α₁ α₂ α₃ : ℝ} (hγ : 0 < γ)
    (h₁ : α₁ < Q γ) (h₂ : α₂ < Q γ) (h₃ : α₃ < Q γ) (hs : 0 < sExp γ α₁ α₂ α₃) :
    ExtendedSeiberg3 γ α₁ α₂ α₃ := by
  refine ⟨h₁, h₂, h₃, ?_⟩
  have h2γ : 0 < 2 / γ := div_pos two_pos hγ
  have hmin := lt_min (show (0 : ℝ) < 4 / γ ^ 2 by positivity)
    (lt_min (mul_pos h2γ (sub_pos.mpr h₁)) (lt_min (mul_pos h2γ (sub_pos.mpr h₂))
      (mul_pos h2γ (sub_pos.mpr h₃))))
  linarith

/-- On the interval `2Q + 2/γ - α₂ - α₃ < α < Q`, the shifted triple is ordinary Seiberg. -/
theorem seeds_shifted_triple {γ α α₂ α₃ : ℝ} (hγ : 0 < γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hα : α < Q γ) (hs : 2 * Q γ + 2 / γ < α + α₂ + α₃) :
    0 < sExp γ (α - 2 / γ) α₂ α₃ ∧ ExtendedSeiberg3 γ (α - 2 / γ) α₂ α₃ := by
  have hpos : 0 < sExp γ (α - 2 / γ) α₂ α₃ := by
    unfold sExp
    exact div_pos (by linarith) hγ
  have h2γ : 0 < 2 / γ := div_pos two_pos hγ
  exact ⟨hpos, seeds_extendedSeiberg3_of_sExp_pos hγ (by linarith) hα₂ hα₃ hpos⟩

/-- On the same interval, the reflected triple is ordinary Seiberg. -/
theorem seeds_reflected_triple {γ α α₂ α₃ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hα : α < Q γ) (hs : 2 * Q γ + 2 / γ < α + α₂ + α₃) :
    0 < sExp γ (2 * Q γ - α - 2 / γ) α₂ α₃ ∧ ExtendedSeiberg3 γ (2 * Q γ - α - 2 / γ) α₂ α₃ := by
  have hlow := (dual_seed_charge_lower γ α α₂ α₃ hα hα₂ hα₃ hs).1
  have hhalf : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ two_pos hγ]
    nlinarith
  have hQ : Q γ = γ / 2 + 2 / γ := by unfold Q; ring
  have hpos : 0 < sExp γ (2 * Q γ - α - 2 / γ) α₂ α₃ := by
    unfold sExp
    exact div_pos (by linarith) hγ
  exact ⟨hpos, seeds_extendedSeiberg3_of_sExp_pos hγ (by linarith) hα₂ hα₃ hpos⟩

/-- The left side at a real charge of the interval. -/
theorem dualReflLeft_ofReal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ)
    {f : (Fin 3 → ℂ) → ℂ} {γ μ α₂ α₃ : ℝ} (hγ : 0 < γ) (hμ : 0 < μ)
    (hfeq : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) →
      f (complexifyNCharges α) = (unitVolumeStructureConstant P M γ (α 0) (α 1) (α 2) : ℂ))
    {α : ℝ} (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hα : α < Q γ)
    (hs : 2 * Q γ + 2 / γ < α + α₂ + α₃) :
    dualReflLeft f γ μ α₂ α₃ (α : ℂ) =
      ((structureConstant P M γ μ (α - 2 / γ) α₂ α₃ *
        gaussCoefficientRatio (gaussParameterA γ (2 / γ) α α₂ α₃)
          (gaussParameterB γ (2 / γ) α α₂ α₃) (gaussParameterC γ (2 / γ) α) : ℝ) : ℂ) := by
  unfold dualReflLeft
  rw [dualShiftedLine_ofReal, structureConstantH_complexify P M hμ _
      (hfeq _ (seeds_shifted_triple hγ hα₂ hα₃ hα hs).2),
    dualParamA_ofReal hγ.ne', dualParamB_ofReal hγ.ne', dualParamC_ofReal hγ.ne',
    gaussCoefficientRatioC_ofReal, Complex.ofReal_mul]
  rfl

/-- The right side at a real charge of the interval, for the witness of `G`. -/
theorem dualReflRight_ofReal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) {f : (Fin 3 → ℂ) → ℂ} {G : ℂ → ℂ} {γ μ α₂ α₃ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hfeq : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) →
      f (complexifyNCharges α) = (unitVolumeStructureConstant P M γ (α 0) (α 1) (α 2) : ℂ))
    {α : ℝ} (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hα : α < Q γ)
    (hs : 2 * Q γ + 2 / γ < α + α₂ + α₃)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hG : G α = (reflectionBarR P γ α B Z : ℂ)) :
    dualReflRight f G γ μ α₂ α₃ (α : ℂ) =
      ((reflectionR P γ μ α B Z * structureConstant P M γ μ (2 * Q γ - α - 2 / γ) α₂ α₃ :
        ℝ) : ℂ) := by
  unfold dualReflRight
  rw [reflectionRFromBar_ofReal P hμ α B Z hG, dualReflectedLine_ofReal,
    structureConstantH_complexify P M hμ _
      (hfeq _ (seeds_reflected_triple hγ hγ2 hα₂ hα₃ hα hs).2), Complex.ofReal_mul]
  rfl

/-! ### Analyticity at real charges and meromorphy along the lines -/

/-- The continued reflection coefficient is analytic where `G` is and `Γ` is analytic at
`-p(z)`. -/
theorem analyticAt_reflectionRFromBar {γ μ : ℝ} (hμ : 0 < μ) {G : ℂ → ℂ} {z : ℂ}
    (hG : AnalyticAt ℂ G z) (hΓ : AnalyticAt ℂ Complex.Gamma (-reflectionExponentC γ z)) :
    AnalyticAt ℂ (reflectionRFromBar γ μ G) z := by
  have hp : AnalyticAt ℂ (reflectionExponentC γ) z := by
    unfold reflectionExponentC
    fun_prop
  have hμs : (μ : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr hμ
  have hpow : AnalyticAt ℂ (fun w => (μ : ℂ) ^ reflectionExponentC γ w) z :=
    analyticAt_const.cpow hp hμs
  have hΓc : AnalyticAt ℂ (fun w => Complex.Gamma (-reflectionExponentC γ w)) z :=
    AnalyticAt.comp_of_eq hΓ hp.neg rfl
  show AnalyticAt ℂ (fun w => (μ : ℂ) ^ reflectionExponentC γ w *
    Complex.Gamma (-reflectionExponentC γ w) * reflectionExponentC γ w * G w) z
  exact ((hpow.mul hΓc).mul hp).mul hG

/-- A positive zero mode is not a pole of `Γ`. -/
theorem seeds_sExpC_ne_neg_nat {γ a b c : ℝ} (hs : 0 < sExp γ a b c) (n : ℕ) :
    sExpC γ (complexifyNCharges ![a, b, c]) ≠ -(n : ℂ) := by
  intro hn
  rw [sExpC_complexify] at hn
  have hn' : sExp γ a b c = -(n : ℝ) := by
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] using (by exact_mod_cast hn : _ = -(n : ℝ))
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- The left side is analytic at every real charge of the interval. -/
theorem analyticAt_dualReflLeft {f : (Fin 3 → ℂ) → ℂ} {V : Set (Fin 3 → ℂ)} (hVo : IsOpen V)
    (hf : DifferentiableOn ℂ f V) {γ μ α₂ α₃ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hVmem : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) → complexifyNCharges α ∈ V)
    {α : ℝ} (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hα : α < Q γ)
    (hs : 2 * Q γ + 2 / γ < α + α₂ + α₃) :
    AnalyticAt ℂ (dualReflLeft f γ μ α₂ α₃) (α : ℂ) := by
  obtain ⟨hspos, hES⟩ := seeds_shifted_triple hγ hα₂ hα₃ hα hs
  have h1 : AnalyticAt ℂ (fun z => structureConstantH f γ μ (dualShiftedLine γ α₂ α₃ z))
      (α : ℂ) :=
    analyticAt_structureConstantH_comp hVo hf hμ (differentiable_dualShiftedLine γ α₂ α₃)
      (by rw [dualShiftedLine_ofReal]; exact hVmem _ hES)
      (by rw [dualShiftedLine_ofReal]; exact seeds_sExpC_ne_neg_nat hspos)
  obtain ⟨ha0, hab, hbc, hc1, -⟩ :=
    gauss_physical_parameter_range γ (2 / γ) α α₂ α₃ hγ hγ2 (Or.inr rfl) hs hα hα₂ hα₃
  have h2 := analyticAt_gaussCoefficientRatioC_comp
    ((differentiable_dualParamA γ α₂ α₃).analyticAt (α : ℂ))
    ((differentiable_dualParamB γ α₂ α₃).analyticAt (α : ℂ))
    ((differentiable_dualParamC γ).analyticAt (α : ℂ))
    (dualParamA_ofReal hγ.ne' α α₂ α₃) (dualParamB_ofReal hγ.ne' α α₂ α₃)
    (dualParamC_ofReal hγ.ne' α) ha0 hab hbc hc1
  show AnalyticAt ℂ (fun z => structureConstantH f γ μ (dualShiftedLine γ α₂ α₃ z) *
    gaussCoefficientRatioC (dualParamA γ α₂ α₃ z) (dualParamB γ α₂ α₃ z) (dualParamC γ z)) _
  exact h1.mul h2

/-- The right side is analytic at every real charge of the interval where `G` is analytic. -/
theorem analyticAt_dualReflRight {f : (Fin 3 → ℂ) → ℂ} {V : Set (Fin 3 → ℂ)} (hVo : IsOpen V)
    (hf : DifferentiableOn ℂ f V) {G : ℂ → ℂ} {γ μ α₂ α₃ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hμ : 0 < μ)
    (hVmem : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) → complexifyNCharges α ∈ V)
    {α : ℝ} (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hα : α < Q γ)
    (hs : 2 * Q γ + 2 / γ < α + α₂ + α₃) (hG : AnalyticAt ℂ G (α : ℂ)) :
    AnalyticAt ℂ (dualReflRight f G γ μ α₂ α₃) (α : ℂ) := by
  obtain ⟨hspos, hES⟩ := seeds_reflected_triple hγ hγ2 hα₂ hα₃ hα hs
  have hlow := (dual_seed_charge_lower γ α α₂ α₃ hα hα₂ hα₃ hs).1
  have hp0 : 0 < reflectionExponent γ α := by
    unfold reflectionExponent
    exact div_pos (by linarith) hγ
  have hp1 : reflectionExponent γ α < 1 := by
    unfold reflectionExponent
    rw [div_lt_one hγ]
    have hQ : Q γ = 2 / γ + γ / 2 := by unfold Q; ring
    linarith
  have hΓ : AnalyticAt ℂ Complex.Gamma (-reflectionExponentC γ (α : ℂ)) := by
    rw [reflectionExponentC_ofReal, ← Complex.ofReal_neg]
    exact analyticAt_Gamma_ofReal_neg_one_lt (by linarith) (by linarith)
  have h1 := analyticAt_reflectionRFromBar hμ hG hΓ
  have h2 : AnalyticAt ℂ (fun z => structureConstantH f γ μ (dualReflectedLine γ α₂ α₃ z))
      (α : ℂ) :=
    analyticAt_structureConstantH_comp hVo hf hμ (differentiable_dualReflectedLine γ α₂ α₃)
      (by rw [dualReflectedLine_ofReal]; exact hVmem _ hES)
      (by rw [dualReflectedLine_ofReal]; exact seeds_sExpC_ne_neg_nat hspos)
  show AnalyticAt ℂ (fun z => reflectionRFromBar γ μ G z *
    structureConstantH f γ μ (dualReflectedLine γ α₂ α₃ z)) _
  exact h1.mul h2

/-- The left side is meromorphic on the preimage of the holomorphy domain of `f`. -/
theorem meromorphicOn_dualReflLeft {f : (Fin 3 → ℂ) → ℂ} {V : Set (Fin 3 → ℂ)}
    (hVo : IsOpen V) (hf : DifferentiableOn ℂ f V) {γ μ α₂ α₃ : ℝ} (hμ : 0 < μ) :
    MeromorphicOn (dualReflLeft f γ μ α₂ α₃) (dualShiftedLine γ α₂ α₃ ⁻¹' V) := by
  intro z hz
  have h1 := meromorphicOn_structureConstantH_comp (γ := γ) hVo hf hμ
    (differentiable_dualShiftedLine γ α₂ α₃) z hz
  have h2 := meromorphicAt_gaussCoefficientRatioC_comp
    ((differentiable_dualParamA γ α₂ α₃).analyticAt z)
    ((differentiable_dualParamB γ α₂ α₃).analyticAt z)
    ((differentiable_dualParamC γ).analyticAt z)
  show MeromorphicAt (fun z => structureConstantH f γ μ (dualShiftedLine γ α₂ α₃ z) *
    gaussCoefficientRatioC (dualParamA γ α₂ α₃ z) (dualParamB γ α₂ α₃ z) (dualParamC γ z)) z
  exact h1.fun_mul h2

/-- The right side is meromorphic where `G` is and on the preimage of the holomorphy domain. -/
theorem meromorphicOn_dualReflRight {f : (Fin 3 → ℂ) → ℂ} {V : Set (Fin 3 → ℂ)}
    (hVo : IsOpen V) (hf : DifferentiableOn ℂ f V) {G : ℂ → ℂ} {W : Set ℂ}
    (hG : MeromorphicOn G W) {γ μ α₂ α₃ : ℝ} (hμ : 0 < μ) :
    MeromorphicOn (dualReflRight f G γ μ α₂ α₃) (dualReflectedLine γ α₂ α₃ ⁻¹' V ∩ W) := by
  intro z hz
  have h1 := meromorphicOn_reflectionRFromBar (γ := γ) hμ hG z hz.2
  have h2 := meromorphicOn_structureConstantH_comp (γ := γ) hVo hf hμ
    (differentiable_dualReflectedLine γ α₂ α₃) z hz.1
  show MeromorphicAt (fun z => reflectionRFromBar γ μ G z *
    structureConstantH f γ μ (dualReflectedLine γ α₂ α₃ z)) z
  exact h1.fun_mul h2

/-! ### The continuation -/

/-- **Continuation of the dual reflection identity in the first charge.** For fixed spectators below
`Q`, the identity `C(α₁ - 2/γ, α₂, α₃) r(α₁) = R(α₁) C(2Q - α₁ - 2/γ, α₂, α₃)` near `Q` (`hnear`)
extends to every `α₁ < Q` with `α₁ + α₂ + α₃ > 2Q + 2/γ`, for every witness of `R(α₁)`. -/
theorem dual_reflection_identity_continuation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ)
    (γ μ α₂ α₃ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hnear : ∀ α₁ : ℝ, α₁ < Q γ → Q γ - α₁ < dualSeedWindow γ →
      2 * Q γ + 2 / γ < α₁ + α₂ + α₃ →
      ∀ (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ),
        IsReflectionData P γ α₁ B Z →
        structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃ *
            gaussCoefficientRatio (gaussParameterA γ (2 / γ) α₁ α₂ α₃)
              (gaussParameterB γ (2 / γ) α₁ α₂ α₃) (gaussParameterC γ (2 / γ) α₁) =
          reflectionR P γ μ α₁ B Z *
            structureConstant P M γ μ (2 * Q γ - α₁ - 2 / γ) α₂ α₃)
    (α₁ : ℝ) (hα₁ : α₁ < Q γ) (hs : 2 * Q γ + 2 / γ < α₁ + α₂ + α₃)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : IsReflectionData P γ α₁ B Z) :
    structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃ *
        gaussCoefficientRatio (gaussParameterA γ (2 / γ) α₁ α₂ α₃)
          (gaussParameterB γ (2 / γ) α₁ α₂ α₃) (gaussParameterC γ (2 / γ) α₁) =
      reflectionR P γ μ α₁ B Z * structureConstant P M γ μ (2 * Q γ - α₁ - 2 / γ) α₂ α₃ := by
  set a₀ : ℝ := 2 * Q γ + 2 / γ - α₂ - α₃ with ha₀_def
  have ha₀ : a₀ < α₁ := by rw [ha₀_def]; linarith
  have hint : ∀ y : ℝ, a₀ < y → 2 * Q γ + 2 / γ < y + α₂ + α₃ := fun y hy => by
    rw [ha₀_def] at hy
    linarith
  have hhalf : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ two_pos hγ]
    nlinarith
  have hlowI : ∀ y ∈ Ioo a₀ (Q γ), γ / 2 < y ∧ y < Q γ := fun y hy =>
    ⟨by linarith [(dual_seed_charge_lower γ y α₂ α₃ hy.2 hα₂ hα₃ (hint y hy.1)).1], hy.2⟩
  -- the holomorphic data: the extension of `C̄` and the `R̄` representation from the γ/2 crossing
  obtain ⟨V, hVo, hVmem, f, hf, hfeq⟩ :=
    unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM
  obtain ⟨B', Z', -, hB', VR, hVRo, hVRmem, fR, -, -, hGd, hGval⟩ :=
    reflectionBarR_holomorphic_representation_of_crossing P X M γ hγ hγ2 hX hM
      (fun μ' α' ε α hμ' h1 h2 h3 h4 h5 =>
        (gammaHalf_crossing P X M γ μ' α' ε α hγ hγ2 hμ' h1 h2 h3 h4 h5 hX hM).2)
      (Ioo a₀ (Q γ)) hlowI
  have hGm : MeromorphicOn (fun z => rbarCoefficient γ z * fR z) VR := fun z hz =>
    (hGd.analyticAt (hVRo.mem_nhds hz)).meromorphicAt
  -- the base point in the window
  have hw := dualSeedWindow_pos hγ hγ2
  set m : ℝ := max a₀ (Q γ - dualSeedWindow γ) with hm
  have hmQ : m < Q γ := max_lt (by linarith) (by linarith)
  set x₀ : ℝ := (m + Q γ) / 2 with hx₀
  have hx₀m : m < x₀ := by rw [hx₀]; linarith
  have hx₀Q : x₀ < Q γ := by rw [hx₀]; linarith
  have hx₀a : a₀ < x₀ := lt_of_le_of_lt (le_max_left _ _) hx₀m
  have hsegpt : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      a₀ < x₀ + t * (α₁ - x₀) ∧ x₀ + t * (α₁ - x₀) < Q γ := by
    intro t ht0 ht1
    refine ⟨?_, add_mul_sub_lt_of_lt hx₀Q hα₁ ht0 ht1⟩
    have h := add_mul_sub_lt_of_lt (c := -a₀) (x := -x₀) (y := -α₁) (by linarith)
      (by linarith) ht0 ht1
    linarith
  -- the two sides along the segment from `x₀` to `α₁`
  set U : Set ℂ := segC x₀ α₁ ⁻¹' (dualShiftedLine γ α₂ α₃ ⁻¹' V ∩
    (dualReflectedLine γ α₂ α₃ ⁻¹' V ∩ VR)) with hU
  have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (t : ℂ) ∈ U := by
    intro t ht0 ht1
    obtain ⟨h1, h2⟩ := hsegpt t ht0 ht1
    show segC x₀ α₁ (t : ℂ) ∈ dualShiftedLine γ α₂ α₃ ⁻¹' V ∩
      (dualReflectedLine γ α₂ α₃ ⁻¹' V ∩ VR)
    rw [segC_ofReal]
    refine ⟨?_, ?_, hVRmem _ ⟨h1, h2⟩⟩
    · show dualShiftedLine γ α₂ α₃ _ ∈ V
      rw [dualShiftedLine_ofReal]
      exact hVmem _ (seeds_shifted_triple hγ hα₂ hα₃ h2 (hint _ h1)).2
    · show dualReflectedLine γ α₂ α₃ _ ∈ V
      rw [dualReflectedLine_ofReal]
      exact hVmem _ (seeds_reflected_triple hγ hγ2 hα₂ hα₃ h2 (hint _ h1)).2
  have hLm := meromorphicOn_dualReflLeft (α₂ := α₂) (α₃ := α₃) hVo hf (γ := γ) hμ
  have hRm := meromorphicOn_dualReflRight (α₂ := α₂) (α₃ := α₃) hVo hf hGm (γ := γ) hμ
  have hF₁ : MeromorphicOn (fun t => dualReflLeft f γ μ α₂ α₃ (segC x₀ α₁ t)) U :=
    fun t ht => (hLm _ ht.1).comp_analyticAt (g := segC x₀ α₁) (analyticAt_segC x₀ α₁ t)
  have hF₂ : MeromorphicOn (fun t => dualReflRight f (fun z => rbarCoefficient γ z * fR z)
      γ μ α₂ α₃ (segC x₀ α₁ t)) U :=
    fun t ht => (hRm _ ht.2).comp_analyticAt (g := segC x₀ α₁) (analyticAt_segC x₀ α₁ t)
  -- agreement near the start, inside the window
  have hstart : ∀ᶠ t : ℝ in 𝓝[>] 0, dualReflLeft f γ μ α₂ α₃ (segC x₀ α₁ t) =
      dualReflRight f (fun z => rbarCoefficient γ z * fR z) γ μ α₂ α₃
        (segC x₀ α₁ t) := by
    filter_upwards [eventually_segC_mem (b := α₁) isOpen_Ioo
      (show x₀ ∈ Ioo m (Q γ) from ⟨hx₀m, hx₀Q⟩)] with t ht
    obtain ⟨hym, hyQ⟩ := ht
    have hya : a₀ < x₀ + t * (α₁ - x₀) := lt_of_le_of_lt (le_max_left _ _) hym
    have hyw : Q γ - (x₀ + t * (α₁ - x₀)) < dualSeedWindow γ := by
      have := lt_of_le_of_lt (le_max_right _ _) hym
      linarith
    rw [segC_ofReal, dualReflLeft_ofReal P M hγ hμ hfeq hα₂ hα₃ hyQ (hint _ hya),
      dualReflRight_ofReal P M hγ hγ2 hμ hfeq hα₂ hα₃ hyQ (hint _ hya) (B' _) Z'
        (hGval _ ⟨hya, hyQ⟩),
      hnear _ hyQ hyw (hint _ hya) (B' _) Z' (hB' _ ⟨hya, hyQ⟩)]
  -- analyticity at the target
  have hF₁1 : AnalyticAt ℂ (fun t => dualReflLeft f γ μ α₂ α₃ (segC x₀ α₁ t)) 1 :=
    AnalyticAt.comp_of_eq (analyticAt_dualReflLeft hVo hf hγ hγ2 hμ hVmem hα₂ hα₃ hα₁ hs)
      (analyticAt_segC x₀ α₁ 1) (segC_one x₀ α₁)
  have hF₂1 : AnalyticAt ℂ (fun t => dualReflRight f (fun z => rbarCoefficient γ z * fR z)
      γ μ α₂ α₃ (segC x₀ α₁ t)) 1 :=
    AnalyticAt.comp_of_eq (analyticAt_dualReflRight hVo hf hγ hγ2 hμ hVmem hα₂ hα₃ hα₁ hs
      (hGd.analyticAt (hVRo.mem_nhds (hVRmem _ ⟨ha₀, hα₁⟩))))
      (analyticAt_segC x₀ α₁ 1) (segC_one x₀ α₁)
  have hmain := eq_at_one_of_segment hseg hF₁ hF₂ hstart hF₁1 hF₂1
  simp only [segC_one] at hmain
  rw [dualReflLeft_ofReal P M hγ hμ hfeq hα₂ hα₃ hα₁ hs,
    dualReflRight_ofReal P M hγ hγ2 hμ hfeq hα₂ hα₃ hα₁ hs (B' α₁) Z'
      (hGval _ ⟨ha₀, hα₁⟩)] at hmain
  rw [Complex.ofReal_injective hmain, reflectionR_eq_of_isReflectionData P P γ μ α₁ (B' α₁) Z'
    B Z (hB' _ ⟨ha₀, hα₁⟩) hB]

end DOZZ.Proofs

end
