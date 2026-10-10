/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.SeparatedTail.LocalWeights
public import DOZZ.Correlations.SeparatedTail.JointMarkov

/-! The separated joint-tail inequality `DOZZ.separatedSingularMass_joint_tail` for the
two-insertion tail [KRV, Lemma 7.3] (erratum K9, see docs/ERRATA-AND-DEVIATIONS.md), proved here
with its literal statement. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology
namespace DOZZ.Proofs

/-- The proof transfers the exterior-pinned decomposition to the actual equator GMC and applies
Markov to its uniform mixed singular moment. -/
theorem separatedSingularMass_joint_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (K2 K3 : Set ℂ) (hK2 : IsCompact K2) (hK3 : IsCompact K3)
    (hpos2 : ∀ z ∈ K2, 2 ≤ ‖z‖) (hpos3 : ∀ z ∈ K3, 2 ≤ ‖z‖)
    (hsep : ∀ z2 ∈ K2, ∀ z3 ∈ K3, 3 ≤ ‖z2 - z3‖)
    (A2 A3 : Set ℝ) (hA2 : IsCompact A2) (hA3 : IsCompact A3)
    (hα2 : ∀ α ∈ A2, γ / 2 < α ∧ α < Q γ)
    (hα3 : ∀ α ∈ A3, γ / 2 < α ∧ α < Q γ)
    (F2s F3s : ℂ → Set (ℂ → ℝ)) (radius supBound derivBound lowerBound : ℝ)
    (hF2 : UniformPositiveC1Family K2 F2s radius supBound derivBound lowerBound)
    (hF3 : UniformPositiveC1Family K3 F3s radius supBound derivBound lowerBound)
    (ε : ℝ) (hε : 0 < ε)
    (hε2 : ∀ α ∈ A2, ε < reflectionExponent γ α)
    (hε3 : ∀ α ∈ A3, ε < reflectionExponent γ α) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z2 ∈ K2, ∀ z3 ∈ K3, ∀ α2 ∈ A2, ∀ α3 ∈ A3,
        ∀ F2 ∈ F2s z2, ∀ F3 ∈ F3s z3, ∀ u v : ℝ, 1 ≤ u → 1 ≤ v →
          (P {ω | ENNReal.ofReal u < localSingularMass M F2 z2 γ α2 ω ∧
            ENNReal.ofReal v < localSingularMass M F3 z3 γ α3 ω}).toReal ≤
            C * Real.rpow u (-reflectionExponent γ α2 + ε) *
              Real.rpow v (-reflectionExponent γ α3 + ε) := by
  let _ : IsProbabilityMeasure P := hX.1
  have _ := hpos2
  have _ := hpos3
  obtain ⟨B,hB,hbound⟩ := separatedTail_singular_mixed_moment_uniform P X hX γ hγ hγ2 M hM
    K2 K3 hK2 hK3 hsep A2 A3 hA2 hA3 hα2 hα3 ε hε hε2 hε3
  let T : ℝ := 4/γ^2
  have hT : 0 < T := by dsimp [T]; positivity
  let S : ℝ≥0∞ := ENNReal.ofReal (max supBound 1)
  have hS : S ≠ ⊤ := ENNReal.ofReal_ne_top
  have hS1 : 1 ≤ S := by
    simpa only [S, ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (le_max_right supBound 1)
  let Bfinal := S^(2*T)*B
  have hBfinal : Bfinal ≠ ⊤ := (ENNReal.mul_lt_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) hS).lt_top hB).ne
  refine ⟨Bfinal.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro z2 hz2 z3 hz3 α2 hα2mem α3 hα3mem F2 hF2mem F3 hF3mem u v hu hv
  have hf2 := hF2.2.2.2.2 z2 hz2 F2 hF2mem
  have hf3 := hF3.2.2.2.2 z3 hz3 F3 hF3mem
  have hFs2 (x : ℂ) : ENNReal.ofReal (F2 x) ≤ S := ENNReal.ofReal_le_ofReal
    ((le_abs_self _).trans ((hf2.2.1 x).2.trans (le_max_left _ _)))
  have hFs3 (x : ℂ) : ENNReal.ofReal (F3 x) ≤ S := ENNReal.ofReal_le_ofReal
    ((le_abs_self _).trans ((hf3.2.1 x).2.trans (le_max_left _ _)))
  have ha2 : 0 ≤ reflectionExponent γ α2-ε := (sub_pos.mpr (hε2 α2 hα2mem)).le
  have ha3 : 0 ≤ reflectionExponent γ α3-ε := (sub_pos.mpr (hε3 α3 hα3mem)).le
  have ha2T : reflectionExponent γ α2-ε ≤ T := by
    have hh := separatedTail_reflectionExponent_lt_bulk hγ (hα2 α2 hα2mem).1
    dsimp [T]
    linarith
  have ha3T : reflectionExponent γ α3-ε ≤ T := by
    have hh := separatedTail_reflectionExponent_lt_bulk hγ (hα3 α3 hα3mem).1
    dsimp [T]
    linarith
  have hm := separatedTail_local_mixed_moment_le P M F2 F3 z2 z3 γ α2 α3
    (reflectionExponent γ α2-ε) (reflectionExponent γ α3-ε) T ha2 ha3 ha2T ha3T
    S B hS1 hS hFs2 hFs3 (hbound z2 hz2 z3 hz3 α2 hα2mem α3 hα3mem)
  have ht := separatedTail_joint_tail_le_of_mixed_moment P
    (localSingularMass M F2 z2 γ α2) (localSingularMass M F3 z3 γ α3)
    (localSingularMass_aemeasurable P X hX γ hγ hγ2 M hM F2 hf2.1 z2 α2)
    (localSingularMass_aemeasurable P X hX γ hγ hγ2 M hM F3 hf3.1 z3 α3)
    _ _ ha2 ha3 Bfinal hBfinal hm u v (by linarith) (by linarith)
  have he2 : -(reflectionExponent γ α2-ε) = -reflectionExponent γ α2+ε := by ring
  have he3 : -(reflectionExponent γ α3-ε) = -reflectionExponent γ α3+ε := by ring
  rw [he2,he3] at ht
  simpa only [Real.rpow_eq_pow] using ht

end DOZZ.Proofs
