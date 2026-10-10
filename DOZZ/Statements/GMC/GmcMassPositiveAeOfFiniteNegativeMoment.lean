/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GmcMassMoment
import DOZZ.GMC.MomentPositivity

/-! The statement `DOZZ.gmcMass_positive_ae_of_finite_negative_moment`,
proved by `DOZZ.Proofs.gmcMass_positive_ae_of_finite_negative_moment`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- A finite negative moment and an a.e.-measurable mass imply almost-sure positivity. -/
theorem gmcMass_positive_ae_of_finite_negative_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (A : Set ℂ)
    (hM : AEMeasurable (fun ω => M ω A) P) (q : ℝ) (hq : 0 < q)
    (hfinite : gmcMassMoment P M A (-q) < ⊤) :
    ∀ᵐ ω ∂P, 0 < M ω A := by exact DOZZ.Proofs.gmcMass_positive_ae_of_finite_negative_moment P M A hM q hq hfinite

end DOZZ
