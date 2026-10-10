/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.WilliamsPolarSplit
public import DOZZ.Brownian.Reflection.LastCut

/-! A measurable code for the lifetime-marked reflection integral against locally finite chaos. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

noncomputable def stoppedReflectionIntegrand (γ : ℝ)
    (z : (ℝ≥0 × (BrownianPath × BrownianPath)) × ℝ) : ℝ≥0∞ :=
  if -(z.1.1 : ℝ) ≤ z.2 then
    ENNReal.ofReal (Real.exp (γ * reflectionPairValue z.1.2 z.2)) else 0

theorem measurable_stoppedReflectionIntegrand (γ : ℝ) :
    Measurable (stoppedReflectionIntegrand γ) := by
  have hval := measurable_uncurry_reflectionPairValue.comp
    (measurable_fst.snd.prodMk measurable_snd : Measurable
      (fun z : (ℝ≥0 × (BrownianPath × BrownianPath)) × ℝ => (z.1.2,z.2)))
  exact Measurable.ite (measurableSet_le measurable_fst.fst.coe_nnreal_real.neg measurable_snd)
    ((hval.const_mul γ).exp.ennreal_ofReal) measurable_const

/-- Sum finite restrictions to disjoint shells, so the code is measurable on all input measures. -/
noncomputable def stoppedReflectionMassCode (γ : ℝ)
    (z : (ℝ≥0 × (BrownianPath × BrownianPath)) × Measure ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, ∫⁻ s, stoppedReflectionIntegrand γ (z.1,s)
    ∂(finiteRestrictionOnSet (translationShell n) z.2 : Measure ℝ)

theorem measurable_stoppedReflectionMassCode (γ : ℝ) :
    Measurable (stoppedReflectionMassCode γ) := by
  apply Measurable.tsum
  intro n
  have hi := measurable_lintegral_finiteMeasure_parameter
    (measurable_stoppedReflectionIntegrand γ)
  exact hi.comp (measurable_fst.prodMk
    ((measurable_finiteRestrictionOnSet _ (measurableSet_translationShell n)).comp measurable_snd))

/-- On locally finite measures the measurable code is the literal stopped reflection integral. -/
theorem stoppedReflectionMassCode_eq (γ : ℝ) (τ : ℝ≥0)
    (B : BrownianPath × BrownianPath) (Z : Measure ℝ)
    (hfin : ∀ a b : ℝ, Z (Icc a b) < ⊤) :
    stoppedReflectionMassCode γ ((τ,B),Z) = stoppedReflectionMass γ τ B Z := by
  have hshell (n : ℕ) : Z (translationShell n) < ⊤ :=
    lt_of_le_of_lt (measure_mono (translationShell_subset_window n)) (hfin _ _)
  exact (lintegral_eq_tsum_finiteRestrictionOnSet_translationShell
    (fun s => stoppedReflectionIntegrand γ ((τ,B),s)) Z hshell).symm


end DOZZ.Proofs
