/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.WilliamsPolarMassLaw

/-! Williams' mass as a jointly measurable function of the level and reflection input. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

noncomputable def williamsCutMassCode (γ : ℝ)
    (p : ℝ × ((BrownianPath × BrownianPath) × Measure ℝ)) : ℝ≥0∞ :=
  stoppedReflectionMassCode γ
    ((negativeLastExitTime p.2.1.2 p.1,p.2.1),p.2.2)

theorem measurable_williamsCutMassCode (γ : ℝ) :
    Measurable (williamsCutMassCode γ) := by
  exact (measurable_stoppedReflectionMassCode γ).comp
    (((measurable_negativeLastExitTime_joint.comp
      (measurable_fst.prodMk measurable_snd.fst.snd)).prodMk measurable_snd.fst).prodMk
      measurable_snd.snd)

theorem williamsCutMassCode_eq (γ m : ℝ)
    (B : BrownianPath × BrownianPath) (Z : Measure ℝ)
    (hfin : ∀ a b : ℝ, Z (Icc a b) < ⊤) :
    williamsCutMassCode γ (m,(B,Z)) =
      twoSidedReflectionCutMass γ m (fun _ : Unit => B) (fun _ : Unit => Z) () := by
  exact stoppedReflectionMassCode_eq γ (negativeLastExitTime B.2 m) B Z hfin

noncomputable def williamsInputMassCode (γ : ℝ)
    (p : ℝ × ((BrownianPath × BrownianPath) × Measure ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (γ*p.1))*williamsCutMassCode γ p

theorem measurable_williamsInputMassCode (γ : ℝ) :
    Measurable (williamsInputMassCode γ) :=
  ((measurable_fst.const_mul γ).exp.ennreal_ofReal).mul
    (measurable_williamsCutMassCode γ)


end DOZZ.Proofs
