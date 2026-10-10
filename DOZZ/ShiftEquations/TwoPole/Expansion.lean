/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.TwoPole.MellinLocal
public import DOZZ.ShiftEquations.TwoPole.Coefficients
public import DOZZ.ShiftEquations.TwoPole.RealFrame
public import DOZZ.Statements.Brownian.IsSourceLateralProjection
public import DOZZ.Statements.Correlations.UniformPositiveC1Family
import DOZZ.ShiftEquations.PoleSubtracted.Holomorphy
import DOZZ.Brownian.Reflection.PositiveFinite
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The two-pole expansion from the two-insertion tail estimate

This is the proof of [KRV, Proposition 10.1], with the coefficients of erratum K26
(see docs/ERRATA-AND-DEVIATIONS.md). In the pole frame `(0, 2, -2)`,
`C̄(α₃, x, α₂) = (2/γ) 2^{4(1-x/γ)} (E[Z_ℂ(x)^{w} - R₁^{w}] + E[R₁^{w}])`, `w = 1 - x/γ`. The first
expectation is the function shown to be holomorphic by `poleSubtractedObservable_holomorphic`; the
second is the Mellin transform of the local mass, meromorphic below the double-tail ceiling with
simple poles at the reflection exponents `w = 1 ∓ 2η/γ`, i.e. `x = ±2η`. Its residues, multiplied by
the frame factor, are `(4/γ)(Q - α) R̄(α)`; the remainder is analytic across both poles (it differs
from the meromorphic part by difference quotients of an entire function).

The two-insertion tail estimate `twoInsertion_tail_sum_uniform` enters as the hypothesis `hTail`,
its conclusion at the given field and chaos.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- **The two-pole expansion from the two-insertion tail estimate.** -/
theorem structureConstant_two_pole_expansion_of_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ η δ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hX : IsEquatorGFF P X)
    (hM : IsGMCOf P X γ M)
    (hWindow : TwoPoleWindow γ η δ)
    (hTail : ∀ (K2 K3 : Set ℂ) (_ : IsCompact K2) (_ : IsCompact K3)
      (_ : ∀ z ∈ K2, 2 ≤ ‖z‖) (_ : ∀ z ∈ K3, 2 ≤ ‖z‖)
      (_ : ∀ z2 ∈ K2, ∀ z3 ∈ K3, 3 ≤ ‖z2 - z3‖)
      (A2 A3 : Set ℝ) (_ : IsCompact A2) (_ : IsCompact A3)
      (_ : ∀ α ∈ A2, γ / 2 < α ∧ α < Q γ)
      (_ : ∀ α ∈ A3, γ / 2 < α ∧ α < Q γ)
      (F2s F3s : ℂ → Set (ℂ → ℝ)) (radius supBound derivBound lowerBound : ℝ)
      (_ : UniformPositiveC1Family K2 F2s radius supBound derivBound lowerBound)
      (_ : UniformPositiveC1Family K3 F3s radius supBound derivBound lowerBound),
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α, (α ∈ A2 ∨ α ∈ A3) → IsReflectionData P γ α (B α) Z) ∧
          ∀ θ : ℝ, 0 < θ → ∃ C : ℝ, 0 ≤ C ∧
            ∀ z2 ∈ K2, ∀ z3 ∈ K3, ∀ α2 ∈ A2, ∀ α3 ∈ A3,
              ∀ F2 ∈ F2s z2, ∀ F3 ∈ F3s z3, ∀ x : ℝ, 1 ≤ x →
                |(P {ω | ENNReal.ofReal x <
                    localSingularMass M F2 z2 γ α2 ω + localSingularMass M F3 z3 γ α3 ω}).toReal -
                  (oneInsertionTailCoefficient γ α2 z2 (F2 z2) (reflectionBarR P γ α2 (B α2) Z) *
                      Real.rpow x (-reflectionExponent γ α2) +
                    oneInsertionTailCoefficient γ α3 z3 (F3 z3) (reflectionBarR P γ α3 (B α3) Z) *
                      Real.rpow x (-reflectionExponent γ α3))| ≤
                  C * Real.rpow x (-(twoInsertionTailCeiling γ α2 α3 - θ))) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          IsReflectionData P γ (2 / γ + η)
            (B (2 / γ + η)) Z ∧
          IsReflectionData P γ (Q γ - η - γ / 2)
            (B (Q γ - η - γ / 2)) Z ∧
            ∃ V : Set ℂ, IsOpen V ∧
              (∀ x : ℝ, -2 * η - δ < x ∧ x < 1 / γ → (x : ℂ) ∈ V) ∧
              ∃ F r : ℂ → ℂ,
                MeromorphicOn F V ∧ DifferentiableOn ℂ r V ∧
                (∀ x : ℝ, 2 * η < x ∧ x < 1 / γ →
                  F (x : ℂ) =
                    (unitVolumeStructureConstant P M γ (Q γ - η - γ / 2) x
                      (2 / γ + η) : ℂ)) ∧
                ∀ᶠ z in codiscrete ℂ, z ∈ V →
                  F z =
                    (twoPoleFirstResidue P γ B Z η : ℂ) / (z - 2 * η) +
                    (twoPoleSecondResidue P γ B Z η : ℂ) / (z + 2 * η) + r z := by
  have hη := window_eta_pos hWindow
  have hηγ := window_eta_le_two_div hγ hγ2 hWindow
  have hη4 := window_eta_lt_quarter hWindow
  have hδ := window_delta_pos hWindow
  have hηlt : η < 2 / γ - γ / 2 := lt_of_lt_of_le hWindow.2.1 (min_le_left _ _)
  have hceil := hWindow.2.2.2.2.2
  have hQ : Q γ - η - γ / 2 = 2 / γ - η := by
    rw [Q]
    ring
  have hα₂ : γ / 2 < 2 / γ + η ∧ 2 / γ + η < Q γ := by
    refine ⟨by linarith, ?_⟩
    rw [Q]
    linarith
  have hα₃ : γ / 2 < Q γ - η - γ / 2 ∧ Q γ - η - γ / 2 < Q γ := by
    rw [hQ]
    refine ⟨by linarith, ?_⟩
    rw [Q]
    linarith
  -- the tail estimate at the two poles
  obtain ⟨rad, sup, der, low, hF2, hF3⟩ :=
    exists_uniformPositiveC1Family_poleFactors hγ hη.le hηγ
  obtain ⟨B, Z, hSLP, hRD, htailθ⟩ := hTail {2} {-2} isCompact_singleton isCompact_singleton
    (by intro z hz; rw [hz]; norm_num) (by intro z hz; rw [hz]; norm_num)
    (by intro z2 hz2 z3 hz3; rw [hz2, hz3]; norm_num)
    {2 / γ + η} {Q γ - η - γ / 2} isCompact_singleton isCompact_singleton
    (by intro α hα; rw [hα]; exact hα₂) (by intro α hα; rw [hα]; exact hα₃)
    (fun _ => {poleFactorTwo γ η}) (fun _ => {poleFactorNegTwo γ η}) rad sup der low hF2 hF3
  have hRD₂ := hRD (2 / γ + η) (Or.inl rfl)
  have hRD₃ := hRD (Q γ - η - γ / 2) (Or.inr rfl)
  refine ⟨B, Z, hSLP, hRD₂, hRD₃, ?_⟩
  have hR₂ := (reflectionBarR_positive_finite P γ (2 / γ + η) hγ hγ2 hα₂ _ Z hRD₂).1
  have hR₃ := (reflectionBarR_positive_finite P γ (Q γ - η - γ / 2) hγ hγ2 hα₃ _ Z hRD₃).1
  generalize hR₂def : reflectionBarR P γ (2 / γ + η) (B (2 / γ + η)) Z = R₂ at hR₂
  generalize hR₃def : reflectionBarR P γ (Q γ - η - γ / 2) (B (Q γ - η - γ / 2)) Z = R₃ at hR₃
  -- the cut below the double-tail ceiling
  rw [hQ] at hceil
  obtain ⟨θ, hθ, hθβ⟩ : ∃ θ : ℝ, 0 < θ ∧
      1 + (2 * η + δ) / γ < twoInsertionTailCeiling γ (2 / γ + η) (2 / γ - η) - θ :=
    ⟨(twoInsertionTailCeiling γ (2 / γ + η) (2 / γ - η) - (1 + (2 * η + δ) / γ)) / 2,
      by linarith, by linarith⟩
  obtain ⟨C, -, hC⟩ := htailθ θ hθ
  have htail : ∀ x : ℝ, 1 ≤ x →
      |(P {ω | ENNReal.ofReal x <
          localSingularMass M (poleFactorTwo γ η) 2 γ (2 / γ + η) ω +
            localSingularMass M (poleFactorNegTwo γ η) (-2) γ (2 / γ - η) ω}).toReal -
        (oneInsertionTailCoefficient γ (2 / γ + η) 2 (poleFactorTwo γ η 2) R₂ *
            Real.rpow x (-reflectionExponent γ (2 / γ + η)) +
          oneInsertionTailCoefficient γ (2 / γ - η) (-2) (poleFactorNegTwo γ η (-2)) R₃ *
            Real.rpow x (-reflectionExponent γ (2 / γ - η)))| ≤
        C * Real.rpow x (-(twoInsertionTailCeiling γ (2 / γ + η) (2 / γ - η) - θ)) := by
    intro x hx
    have h := hC 2 rfl (-2) rfl (2 / γ + η) rfl (Q γ - η - γ / 2) rfl (poleFactorTwo γ η) rfl
      (poleFactorNegTwo γ η) rfl x hx
    rw [hR₂def, hR₃def, hQ] at h
    exact h
  have hβ : reflectionExponent γ (2 / γ - η) <
      twoInsertionTailCeiling γ (2 / γ + η) (2 / γ - η) - θ := by
    rw [reflectionExponent_pole_neg hγ η]
    have : 2 * η / γ < (2 * η + δ) / γ := by
      rw [div_lt_div_iff_of_pos_right hγ]
      linarith
    linarith
  obtain ⟨rL, hrL, hmellin⟩ :=
    exists_localMass_mellin P X hX γ hγ hγ2 M hM hWindow hR₂ hR₃ htail hβ
  -- the holomorphic pole-subtracted part
  obtain ⟨-, Xc, hXc, -⟩ := id hM
  obtain ⟨V₁, hV₁o, hV₁int, F₁, hF₁d, hF₁real, -⟩ :=
    poleSubtractedObservable_holomorphic P X M γ η δ hγ hγ2 hX Xc hXc hM hWindow
  -- notation
  have hβ₁v : reflectionExponent γ (2 / γ + η) = 1 - 2 * η / γ := reflectionExponent_pole hγ η
  have hβ₂v : reflectionExponent γ (2 / γ - η) = 1 + 2 * η / γ := reflectionExponent_pole_neg hγ η
  have hc₁v := tailCoefficient_two hγ η R₂
  have hc₂v := tailCoefficient_negTwo hγ η R₃
  generalize hc₁def : oneInsertionTailCoefficient γ (2 / γ + η) 2 (poleFactorTwo γ η 2) R₂ = c₁
    at hmellin hc₁v
  generalize hc₂def : oneInsertionTailCoefficient γ (2 / γ - η) (-2) (poleFactorNegTwo γ η (-2))
    R₃ = c₂ at hmellin hc₂v
  rw [hβ₁v, hβ₂v] at hmellin
  set β₃ : ℝ := twoInsertionTailCeiling γ (2 / γ + η) (2 / γ - η) - θ with hβ₃def
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ,
      G = fun z : ℂ => (2 / (γ : ℂ)) * (2 : ℂ) ^ (4 * (1 - z / (γ : ℂ))) := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : ℂ → ℂ, h = fun z : ℂ => G z * (1 - z / (γ : ℂ)) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℂ → ℂ, T = fun z : ℂ =>
      twoTailRational c₁ c₂ (1 - 2 * η / γ) (1 + 2 * η / γ) (1 - z / (γ : ℂ)) := ⟨_, rfl⟩
  obtain ⟨Rl, hRl⟩ : ∃ Rl : ℂ → ℂ, Rl = fun z : ℂ => rL (1 - z / (γ : ℂ)) := ⟨_, rfl⟩
  set V : Set ℂ := V₁ ∩ {z : ℂ | (1 - z / (γ : ℂ)).re < β₃} with hVdef
  -- regularity
  have hwd : Differentiable ℂ fun z : ℂ => 1 - z / (γ : ℂ) := by fun_prop
  have hGd : Differentiable ℂ G := by
    rw [hG]
    intro z
    exact (differentiableAt_const _).mul (((hwd z).const_mul 4).const_cpow (Or.inl two_ne_zero))
  have hhd : Differentiable ℂ h := by
    rw [hh]
    exact hGd.mul hwd
  have hVopen : IsOpen V :=
    hV₁o.inter (isOpen_lt (Complex.continuous_re.comp hwd.continuous) continuous_const)
  have hRld : DifferentiableOn ℂ Rl V := by
    rw [hRl]
    exact hrL.comp hwd.differentiableOn fun z hz => hz.2
  have hF₁V : DifferentiableOn ℂ F₁ V := hF₁d.mono inter_subset_left
  have hdslope : ∀ a : ℂ, DifferentiableOn ℂ (dslope h a) V := fun a =>
    ((Complex.differentiableOn_dslope Filter.univ_mem).2 hhd.differentiableOn).mono
      (subset_univ V)
  have hTform : ∀ z : ℂ, z ≠ 2 * η → z ≠ -(2 * η) →
      T z = ((γ * c₁ : ℝ) : ℂ) * (1 - z / (γ : ℂ)) / (z - 2 * η) +
        ((γ * c₂ : ℝ) : ℂ) * (1 - z / (γ : ℂ)) / (z + 2 * η) := by
    intro z hz1 hz2
    have h1 : z - 2 * η ≠ 0 := sub_ne_zero.mpr hz1
    have h2 : z + 2 * η ≠ 0 := by
      intro h
      exact hz2 (eq_neg_of_add_eq_zero_left h)
    have hγ0 : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ.ne'
    simp only [hT, twoTailRational]
    push_cast
    have e1 : ((1 : ℂ) - 2 * η / γ - (1 - z / γ)) = (z - 2 * η) / γ := by
      field_simp
      ring
    have e2 : ((1 : ℂ) + 2 * η / γ - (1 - z / γ)) = (z + 2 * η) / γ := by
      field_simp
      ring
    rw [e1, e2]
    field_simp
  -- the residues
  have hres₁ : ((γ * c₁ : ℝ) : ℂ) * h (2 * η) = (twoPoleFirstResidue P γ B Z η : ℂ) := by
    have hpw : (2 : ℂ) ^ (4 * (1 - 2 * (η : ℂ) / (γ : ℂ))) =
        (((2 : ℝ) ^ (4 * (1 - 2 * η / γ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2)]
      push_cast
      rfl
    rw [twoPoleFirstResidue, hR₂def, ← firstResidue_eq hγ η R₂, ← hc₁v]
    simp only [hh, hG]
    rw [hpw]
    push_cast
    ring
  have hres₂ : ((γ * c₂ : ℝ) : ℂ) * h (-(2 * η)) =
      (twoPoleSecondResidue P γ B Z η : ℂ) := by
    have hpw : (2 : ℂ) ^ (4 * (1 - -(2 * (η : ℂ)) / (γ : ℂ))) =
        (((2 : ℝ) ^ (4 * (1 + 2 * η / γ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2)]
      push_cast
      ring_nf
    rw [twoPoleSecondResidue, hR₃def, ← secondResidue_eq hγ η R₃, ← hc₂v]
    simp only [hh, hG]
    rw [hpw]
    push_cast
    ring
  refine ⟨V, hVopen, ?_, fun z => G z * (F₁ z + (T z + Rl z)),
    fun z => G z * (F₁ z + Rl z) + ((γ * c₁ : ℝ) : ℂ) * dslope h (2 * η) z +
      ((γ * c₂ : ℝ) : ℂ) * dslope h (-(2 * η)) z, ?_, ?_, ?_, ?_⟩
  · -- the interval lies in `V`
    intro x hx
    refine ⟨hV₁int x hx, ?_⟩
    show (1 - (x : ℂ) / (γ : ℂ)).re < β₃
    rw [re_one_sub_div, Complex.ofReal_re]
    have : -(x / γ) < (2 * η + δ) / γ := by
      rw [← neg_div, div_lt_div_iff_of_pos_right hγ]
      linarith [hx.1]
    linarith
  · -- meromorphy
    intro z hz
    have hGm := (hGd.analyticAt z).meromorphicAt
    have hF₁m := (hF₁d.analyticAt (hV₁o.mem_nhds hz.1)).meromorphicAt
    have hRlm := (hRld.analyticAt (hVopen.mem_nhds hz)).meromorphicAt
    have hTm : MeromorphicAt T z := by
      rw [hT]
      simp only [twoTailRational]
      apply MeromorphicAt.add <;> apply MeromorphicAt.div <;>
        exact (Differentiable.analyticAt (by fun_prop) z).meromorphicAt
    exact hGm.mul (hF₁m.add (hTm.add hRlm))
  · -- the remainder is holomorphic
    exact ((hGd.differentiableOn.mul (hF₁V.add hRld)).add
      ((differentiableOn_const _).mul (hdslope _))).add ((differentiableOn_const _).mul (hdslope _))
  · -- the real identity
    rintro x ⟨hx₁, hx₂⟩
    have hxI : -2 * η - δ < x := by linarith
    have hLnn : ∀ ω, 0 ≤ localMassReal M γ η ω := fun ω => ENNReal.toReal_nonneg
    have hws : (1 - (x : ℂ) / (γ : ℂ)) = ((1 - x / γ : ℝ) : ℂ) := by push_cast; ring
    have hwre : ((1 - x / γ : ℝ) : ℂ).re < 1 - 2 * η / γ := by
      rw [Complex.ofReal_re]
      have : 2 * η / γ < x / γ := by
        rw [div_lt_div_iff_of_pos_right hγ]
        exact hx₁
      linarith
    obtain ⟨hLint_c, hLeq⟩ := hmellin _ hwre
    have hfun : (fun ω => ((localMassReal M γ η ω : ℝ) : ℂ) ^ (((1 - x / γ : ℝ)) : ℂ)) =
        fun ω => ((localMassReal M γ η ω ^ (1 - x / γ) : ℝ) : ℂ) :=
      funext fun ω => (Complex.ofReal_cpow (hLnn ω) _).symm
    have hLint : Integrable (fun ω => localMassReal M γ η ω ^ (1 - x / γ)) P := by
      rw [hfun] at hLint_c
      exact hLint_c.re
    have hLreal : ∫ ω, ((localMassReal M γ η ω : ℝ) : ℂ) ^ (((1 - x / γ : ℝ)) : ℂ) ∂P =
        ((∫ ω, localMassReal M γ η ω ^ (1 - x / γ) ∂P : ℝ) : ℂ) := by
      rw [hfun, integral_complex_ofReal]
    have hobs := observable_add_localMoment P X hX γ hγ hγ2 M hM hWindow hx₁ hx₂ hLint
    have hF₁x := hF₁real x ⟨hxI, hx₂⟩
    have hTR : T x + Rl x = ((∫ ω, localMassReal M γ η ω ^ (1 - x / γ) ∂P : ℝ) : ℂ) := by
      simp only [hT, hRl]
      rw [hws, ← hLreal, hLeq]
    have hGx : G x = (((2 / γ) * (2 : ℝ) ^ (4 * (1 - x / γ)) : ℝ) : ℂ) := by
      simp only [hG]
      rw [Complex.ofReal_mul, Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2)]
      push_cast
      ring
    rw [unitVolumeStructureConstant_pole_order P X hX γ hγ hγ2 M hM
      (extendedSeiberg3_pole hγ hγ2 hWindow hx₁ hx₂),
      unitVolumeStructureConstant_eq_frame P X hX γ hγ hγ2 M hM η x]
    show G x * (F₁ x + (T x + Rl x)) = _
    rw [hGx, hF₁x, hTR, ← Complex.ofReal_add, ← Complex.ofReal_mul, hobs]
    congr 1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    ring
  · -- the pole decomposition off the poles
    have hfin : ({2 * (η : ℂ), -(2 * (η : ℂ))} : Set ℂ).Finite := Set.toFinite _
    filter_upwards [(compl_finite_mem_codiscreteWithin (s := Set.univ) hfin :
      _ ∈ codiscrete ℂ)] with z hz _
    have hz1 : z ≠ 2 * η := fun h => hz (by simp [h])
    have hz2 : z ≠ -(2 * η) := fun h => hz (by simp [h])
    have h1 : z - 2 * η ≠ 0 := sub_ne_zero.mpr hz1
    have h2 : z + 2 * η ≠ 0 := fun h => hz2 (eq_neg_of_add_eq_zero_left h)
    have hγ0 : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ.ne'
    have hhz : h z = G z * (1 - z / (γ : ℂ)) := by rw [hh]
    rw [← hres₁, ← hres₂]
    show G z * (F₁ z + (T z + Rl z)) = _
    rw [hTform z hz1 hz2, dslope_of_ne _ hz1, dslope_of_ne _ hz2, slope_def_field,
      slope_def_field, hhz]
    field_simp
    ring

end DOZZ.Proofs

end
