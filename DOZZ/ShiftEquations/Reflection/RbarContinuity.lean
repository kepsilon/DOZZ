/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Reflection.StructureContinuity
public import DOZZ.Statements.ShiftEquations.RbarCoefficient
public import DOZZ.Statements.Brownian.ReflectionR
public import DOZZ.Statements.Brownian.ReflectionPoleFree
public import DOZZ.Statements.Brownian.IsSourceLateralProjection
public import DOZZ.Statements.Brownian.IsReflectionData
import DOZZ.Brownian.Reflection.WitnessIndependence
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Continuity in `γ` of the reflection coefficients from the `R̄` representation

On the physical domain `0 < γ < 2`, `γ/2 < α < Q`, the four `l`-function arguments of the
coefficient of [KRV, (formulaforbarR)] (erratum K29, see docs/ERRATA-AND-DEVIATIONS.md) lie in
`(-1, 0)` or `(0, 1)`, away from all poles and zeros of `l(x) = Γ(x)/Γ(1-x)`, so the coefficient is
jointly continuous and nonvanishing. Given the representation `R̄(α) = coefficient · C̄(α, γ, α)`
for every `γ`, the witness independence of `R̄` and the joint continuity of `C̄` give the joint
continuity of `R̄`, and of `R` off its Gamma poles.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The physical reflection domain. -/
def reflectionDomain : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ q.1 < 2 ∧ q.1 / 2 < q.2 ∧ q.2 < Q q.1}

/-- `l` is continuous and nonzero at points `x` with `x` and `1 - x` off the Gamma poles. -/
theorem continuousAt_lFun {x : ℂ} (h1 : ∀ m : ℕ, x ≠ -m) (h2 : ∀ m : ℕ, 1 - x ≠ -m) :
    ContinuousAt lFun x := by
  have hc : ContinuousAt (fun y : ℂ => Complex.Gamma (1 - y)) x :=
    (Complex.differentiableAt_Gamma (1 - x) h2).continuousAt.comp
      (continuous_const.sub continuous_id).continuousAt
  exact (Complex.differentiableAt_Gamma x h1).continuousAt.div hc (Complex.Gamma_ne_zero h2)

theorem lFun_ne_zero {x : ℂ} (h1 : ∀ m : ℕ, x ≠ -m) (h2 : ∀ m : ℕ, 1 - x ≠ -m) :
    lFun x ≠ 0 :=
  div_ne_zero (Complex.Gamma_ne_zero h1) (Complex.Gamma_ne_zero h2)

/-- A real point strictly between two consecutive integers is off every pole. -/
theorem ofReal_ne_neg_nat_of_mem {r : ℝ} (h : (-1 < r ∧ r < 0) ∨ (0 < r ∧ r < 1) ∨
    (1 < r ∧ r < 2)) : ∀ m : ℕ, (r : ℂ) ≠ -m := by
  intro m hm
  have hr : r = -m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hr] at h1 h2
    rcases Nat.lt_or_ge m 1 with hm1 | hm1
    · interval_cases m
      norm_num at h2
    · have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      linarith
  · rw [hr] at h1
    linarith
  · rw [hr] at h1
    linarith

/-- The `l`-arguments of the coefficient at real points of the domain. -/
theorem lFun_arguments_mem {γ α : ℝ} (hq : (γ, α) ∈ reflectionDomain) :
    (-1 < γ / 2 * α - γ ^ 2 / 4 - 1 ∧ γ / 2 * α - γ ^ 2 / 4 - 1 < 0) ∧
      (0 < 1 + γ / 2 * (α - Q γ) ∧ 1 + γ / 2 * (α - Q γ) < 1) ∧
      (-1 < -(γ ^ 2) / 4 ∧ -(γ ^ 2) / 4 < 0) ∧ (0 < γ ^ 2 / 4 ∧ γ ^ 2 / 4 < 1) := by
  obtain ⟨hγ, hγ2, hα1, hα2⟩ := hq
  have hQ : γ / 2 * Q γ = 1 + γ ^ 2 / 4 := by
    rw [Q]
    field_simp
    ring
  have hγsq : γ ^ 2 < 4 := by
    have := pow_lt_pow_left₀ hγ2 hγ.le two_ne_zero
    linarith only [this]
  have h1 : γ / 2 * (γ / 2) < γ / 2 * α := mul_lt_mul_of_pos_left hα1 (by positivity)
  have h2 : γ / 2 * α < γ / 2 * Q γ := mul_lt_mul_of_pos_left hα2 (by positivity)
  have hγsq0 : 0 < γ ^ 2 := pow_pos hγ 2
  refine ⟨⟨by linarith only [h1], by linarith only [h2, hQ]⟩,
    ⟨by linarith only [h1, hQ], by linarith only [h2]⟩,
    ⟨by linarith only [hγsq], by linarith only [hγsq0]⟩, ⟨by positivity, by linarith only [hγsq]⟩⟩

/-- Composition of `l` with a continuous map through an admissible real value. -/
theorem continuousAt_lFun_comp {f : ℝ × ℝ → ℂ} {q : ℝ × ℝ} (hf : ContinuousAt f q) {r : ℝ}
    (hr : f q = r) (hr1 : (-1 < r ∧ r < 0) ∨ (0 < r ∧ r < 1)) :
    ContinuousAt (fun p => lFun (f p)) q ∧ lFun (f q) ≠ 0 := by
  have h1 : ∀ m : ℕ, f q ≠ -m := by
    rw [hr]
    exact ofReal_ne_neg_nat_of_mem (by tauto)
  have h2 : ∀ m : ℕ, 1 - f q ≠ -m := by
    rw [hr, show (1 : ℂ) - r = ((1 - r : ℝ) : ℂ) by push_cast; ring]
    refine ofReal_ne_neg_nat_of_mem ?_
    rcases hr1 with ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)
    · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
  exact ⟨(continuousAt_lFun h1 h2).comp hf, lFun_ne_zero h1 h2⟩

/-- **The `formulaforbarR` coefficient is continuous on the physical domain.** -/
theorem continuousOn_rbarCoefficient :
    ContinuousOn (fun q : ℝ × ℝ => rbarCoefficient q.1 (q.2 : ℂ)) reflectionDomain := by
  intro q hq
  apply ContinuousAt.continuousWithinAt
  obtain ⟨ha, hb, hc, hd⟩ := lFun_arguments_mem hq
  have hγ0 : q.1 ≠ 0 := hq.1.ne'
  have hc1 : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) := Complex.continuous_ofReal.comp continuous_fst
  have hc2 : Continuous fun p : ℝ × ℝ => (p.2 : ℂ) := Complex.continuous_ofReal.comp continuous_snd
  have cA := continuousAt_lFun_comp (f := fun p : ℝ × ℝ =>
      (p.1 : ℂ) / 2 * (p.2 : ℂ) - (p.1 : ℂ) ^ 2 / 4 - 1)
    (show Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) / 2 * (p.2 : ℂ) - (p.1 : ℂ) ^ 2 / 4 - 1) from
      (((hc1.div_const 2).mul hc2).sub ((hc1.pow 2).div_const 4)).sub continuous_const).continuousAt
    (r := q.1 / 2 * q.2 - q.1 ^ 2 / 4 - 1) (by push_cast; ring) (Or.inl ha)
  have cB := continuousAt_lFun_comp (f := fun p : ℝ × ℝ =>
      1 + (p.1 : ℂ) / 2 * ((p.2 : ℂ) - (Q p.1 : ℂ))) (by
        have : ContinuousAt (fun p : ℝ × ℝ => Q p.1) q := by
          unfold Q
          exact (continuousAt_const.div continuous_fst.continuousAt hγ0).add
            (continuous_fst.continuousAt.div_const _)
        exact continuousAt_const.add ((Complex.continuous_ofReal.comp continuous_fst).continuousAt
          |>.div_const _ |>.mul ((Complex.continuous_ofReal.comp continuous_snd).continuousAt.sub
          (Complex.continuous_ofReal.continuousAt.comp this))))
    (r := 1 + q.1 / 2 * (q.2 - Q q.1)) (by push_cast; ring) (Or.inr hb)
  have cC := continuousAt_lFun_comp (f := fun p : ℝ × ℝ => -((p.1 : ℂ) ^ 2) / 4)
    (show Continuous (fun p : ℝ × ℝ => -((p.1 : ℂ) ^ 2) / 4) from
      (hc1.pow 2).neg.div_const 4).continuousAt
    (r := -(q.1 ^ 2) / 4) (by push_cast; ring) (Or.inl hc)
  have cD := continuousAt_lFun_comp (f := fun p : ℝ × ℝ => (p.1 : ℂ) ^ 2 / 4)
    (show Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) ^ 2 / 4) from (hc1.pow 2).div_const 4).continuousAt
    (r := q.1 ^ 2 / 4) (by push_cast; ring) (Or.inr hd)
  have cpre : ContinuousAt (fun p : ℝ × ℝ => 2 * (Real.pi : ℂ) / (p.1 : ℂ)) q :=
    continuousAt_const.div (Complex.continuous_ofReal.comp continuous_fst).continuousAt
      (Complex.ofReal_ne_zero.mpr hγ0)
  unfold rbarCoefficient
  exact (cpre.mul cA.1).div ((cB.1.mul cC.1).mul cD.1) (mul_ne_zero (mul_ne_zero cB.2 cC.2) cD.2)

/-- The charges `(α, γ, α)` of the `R̄` representation lie in the extended domain. -/
theorem extendedSeiberg3_reflection {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα1 : γ / 2 < α)
    (hα2 : α < Q γ) : ExtendedSeiberg3 γ α γ α := by
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hγQ : γ < Q γ := by
    rw [hQ]
    have : γ / 2 < 2 / γ := by
      rw [div_lt_div_iff₀ (by norm_num) hγ]
      exact mul_self_lt_mul_self hγ.le hγ2
    linarith
  have hs : -sExp γ α γ α = (2 * Q γ - 2 * α - γ) / γ := by
    unfold sExp
    ring
  refine ⟨hα2, hγQ, hα2, ?_⟩
  rw [hs]
  refine lt_min ?_ (lt_min ?_ (lt_min ?_ ?_))
  · rw [div_lt_div_iff₀ hγ (by positivity), hQ]
    field_simp
    linarith only [mul_pos hγ (by linarith only [hα1, hγ] : (0 : ℝ) < α)]
  · rw [div_lt_iff₀ hγ, show 2 / γ * (Q γ - α) * γ = 2 * (Q γ - α) by field_simp]
    linarith
  · rw [div_lt_iff₀ hγ, show 2 / γ * (Q γ - γ) * γ = 2 * (Q γ - γ) by field_simp]
    linarith
  · rw [div_lt_iff₀ hγ, show 2 / γ * (Q γ - α) * γ = 2 * (Q γ - α) by field_simp]
    linarith

/-- **The `R̄` representation gives `R̄ = Re(coefficient) · C̄(α, γ, α)`** for any reflection
data. -/
theorem reflectionBarR_eq_coefficient_mul {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (M : ℝ → Ω → Measure ℂ)
    (hM : ∀ γ, 0 < γ → γ < 2 → IsGMCOf P X γ (M γ))
    (hBarRRepresentation : ∀ (γ : ℝ) (Mγ : Ω → Measure ℂ) (_ : 0 < γ) (_ : γ < 2) (_ : IsGMCOf P X γ Mγ)
      (I : Set ℝ) (_ : IsCompact I) (_ : ∀ α ∈ I, γ / 2 < α ∧ α < Q γ),
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ Mγ Z ∧ (∀ α ∈ I, IsReflectionData P γ α (B α) Z) ∧
          ∃ V : Set ℂ, IsOpen V ∧ (∀ α ∈ I, (α : ℂ) ∈ V) ∧
            ∃ f : ℂ → ℂ, DifferentiableOn ℂ f V ∧
              (∀ α ∈ I, f (α : ℂ) = (unitVolumeStructureConstant P Mγ γ α γ α : ℂ)) ∧
              DifferentiableOn ℂ (fun z => rbarCoefficient γ z * f z) V ∧
              ∀ α ∈ I, rbarCoefficient γ (α : ℂ) * f (α : ℂ) =
                (reflectionBarR P γ α (B α) Z : ℂ))
    {γ α : ℝ} (hq : (γ, α) ∈ reflectionDomain) (B : Ω → BrownianPath × BrownianPath)
    (Z : Ω → Measure ℝ) (hData : IsReflectionData P γ α B Z) :
    reflectionBarR P γ α B Z =
      (rbarCoefficient γ (α : ℂ) * (unitVolumeStructureConstant P (M γ) γ α γ α : ℂ)).re := by
  obtain ⟨hγ, hγ2, hα1, hα2⟩ := hq
  obtain ⟨B', Z', -, hRD', V, -, -, f, -, hf, -, hcoef⟩ := hBarRRepresentation γ (M γ) hγ hγ2 (hM γ hγ hγ2)
    {α} isCompact_singleton (by
      intro a ha
      rw [ha]
      exact ⟨hα1, hα2⟩)
  have hc := hcoef α rfl
  rw [hf α rfl] at hc
  rw [hc, Complex.ofReal_re]
  exact reflectionBarR_eq_of_isReflectionData P P γ α B Z (B' α) Z' hData (hRD' α rfl)

/-- **Joint continuity of `R̄`, and of `R` off its Gamma poles** (third conjunct of
`DOZZ.reflection_endpoint_and_gamma_continuity`), from the `R̄` representation. -/
theorem continuousOn_reflection_of_representation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : ℝ → Ω → Measure ℂ) (hX : IsEquatorGFF P X)
    (hM : ∀ γ, 0 < γ → γ < 2 → IsGMCOf P X γ (M γ))
    (hBarRRepresentation : ∀ (γ : ℝ) (Mγ : Ω → Measure ℂ) (_ : 0 < γ) (_ : γ < 2) (_ : IsGMCOf P X γ Mγ)
      (I : Set ℝ) (_ : IsCompact I) (_ : ∀ α ∈ I, γ / 2 < α ∧ α < Q γ),
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ Mγ Z ∧ (∀ α ∈ I, IsReflectionData P γ α (B α) Z) ∧
          ∃ V : Set ℂ, IsOpen V ∧ (∀ α ∈ I, (α : ℂ) ∈ V) ∧
            ∃ f : ℂ → ℂ, DifferentiableOn ℂ f V ∧
              (∀ α ∈ I, f (α : ℂ) = (unitVolumeStructureConstant P Mγ γ α γ α : ℂ)) ∧
              DifferentiableOn ℂ (fun z => rbarCoefficient γ z * f z) V ∧
              ∀ α ∈ I, rbarCoefficient γ (α : ℂ) * f (α : ℂ) =
                (reflectionBarR P γ α (B α) Z : ℂ))
    (μ : ℝ) (hμ : 0 < μ) (B : ℝ → ℝ → Ω → BrownianPath × BrownianPath)
    (Z : ℝ → Ω → Measure ℝ)
    (hData : ∀ γ, 0 < γ → γ < 2 → ∀ α, γ / 2 < α → α < Q γ →
      IsReflectionData P γ α (B γ α) (Z γ))
    (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (hKdom : ∀ q ∈ K, 0 < q.1 ∧ q.1 < 2 ∧ q.1 / 2 < q.2 ∧ q.2 < Q q.1) :
    ContinuousOn (fun q => reflectionBarR P q.1 q.2 (B q.1 q.2) (Z q.1)) K ∧
      ((∀ q ∈ K, ReflectionPoleFree q.1 q.2) →
        ContinuousOn (fun q => reflectionR P q.1 μ q.2 (B q.1 q.2) (Z q.1)) K) := by
  have hKD : K ⊆ reflectionDomain := fun q hq => hKdom q hq
  -- continuity of `C̄(α, γ, α)`
  set ι : ℝ × ℝ → ℝ × (Fin 3 → ℝ) := fun q => (q.1, ![q.2, q.1, q.2]) with hι
  have hιc : Continuous ι := by
    refine continuous_fst.prodMk (continuous_pi fun i => ?_)
    fin_cases i
    · exact continuous_snd
    · exact continuous_fst
    · exact continuous_snd
  have hCbar : ContinuousOn (fun q : ℝ × ℝ => unitVolumeStructureConstant P (M q.1) q.1 q.2 q.1
      q.2) K := by
    have h := continuousOn_unitVolumeStructureConstant P X M hX hM (ι '' K) (hK.image hιc)
      (by
        rintro _ ⟨q, hq, rfl⟩
        obtain ⟨hγ, hγ2, hα1, hα2⟩ := hKdom q hq
        refine ⟨hγ, hγ2, ?_⟩
        simp only [hι, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
        exact extendedSeiberg3_reflection hγ hγ2 hα1 hα2)
    exact h.comp hιc.continuousOn (mapsTo_image ι K)
  have hR : ContinuousOn (fun q => reflectionBarR P q.1 q.2 (B q.1 q.2) (Z q.1)) K := by
    have hcont : ContinuousOn (fun q : ℝ × ℝ => (rbarCoefficient q.1 (q.2 : ℂ) *
        (unitVolumeStructureConstant P (M q.1) q.1 q.2 q.1 q.2 : ℂ)).re) K :=
      Complex.continuous_re.comp_continuousOn ((continuousOn_rbarCoefficient.mono hKD).mul
        (Complex.continuous_ofReal.comp_continuousOn hCbar))
    refine hcont.congr fun q hq => ?_
    obtain ⟨hγ, hγ2, hα1, hα2⟩ := hKdom q hq
    exact reflectionBarR_eq_coefficient_mul P X M hM hBarRRepresentation (hKdom q hq) _ _
      (hData q.1 hγ hγ2 q.2 hα1 hα2)
  refine ⟨hR, fun hpole => ?_⟩
  have hp : ContinuousOn (fun q : ℝ × ℝ => reflectionExponent q.1 q.2) K := by
    unfold reflectionExponent Q
    have hγne : ∀ q ∈ K, q.1 ≠ 0 := fun q hq => (hKdom q hq).1.ne'
    exact ((continuousOn_const.mul ((((continuousOn_const.div continuous_fst.continuousOn hγne).add
      (continuous_fst.continuousOn.div_const _)).sub continuous_snd.continuousOn))).div
      continuous_fst.continuousOn hγne)
  have hΓc : ContinuousOn Real.Gamma {x : ℝ | ∀ m : ℕ, x ≠ -m} := fun x hx =>
    (Real.differentiableAt_Gamma hx).continuousAt.continuousWithinAt
  have hnp : ∀ q ∈ K, ∀ m : ℕ, -reflectionExponent q.1 q.2 ≠ -m := by
    intro q hq m hm
    obtain ⟨hγ, hγ2, hα1, hα2⟩ := hKdom q hq
    have hp0 : 0 < reflectionExponent q.1 q.2 := by
      unfold reflectionExponent
      exact div_pos (by linarith) hγ
    have hm' : reflectionExponent q.1 q.2 = m := by linarith
    rcases m with _ | n
    · simp only [Nat.cast_zero] at hm'
      linarith
    · exact hpole q hq n (by rw [hm'])
  have hΓ : ContinuousOn (fun q : ℝ × ℝ => Real.Gamma (-reflectionExponent q.1 q.2)) K :=
    hΓc.comp hp.neg fun q hq => hnp q hq
  have hμp : ContinuousOn (fun q : ℝ × ℝ => μ ^ reflectionExponent q.1 q.2) K :=
    continuousOn_const.rpow hp fun _ _ => Or.inl hμ.ne'
  unfold reflectionR
  exact ((hμp.mul hΓ).mul hp).mul hR

end DOZZ.Proofs

end
