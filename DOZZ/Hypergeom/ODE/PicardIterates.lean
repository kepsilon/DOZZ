/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.DiskPrimitive
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Holomorphic Picard iterates for a linear system on a disk (local step). -/

@[expose] public section

namespace DOZZ.Proofs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The Picard summands for `Y' = H(z)Y`, represented together with the holomorphicity proof
needed to take the next primitive. The zeroth term is the initial vector and every later term is
the normalized primitive of `H` applied to the preceding term. -/
noncomputable def holomorphicPicardIterates (c : ℂ) (r : ℝ)
    (H : ℂ → E →L[ℂ] E) (hH : DifferentiableOn ℂ H (Metric.ball c r)) (y : E) :
    ℕ → {f : ℂ → E // DifferentiableOn ℂ f (Metric.ball c r)}
  | 0 => ⟨fun _ => y, differentiableOn_const (c := y)⟩
  | n + 1 => by
      let prev := holomorphicPicardIterates c r H hH y n
      let integrand : ℂ → E := fun z => H z (prev.1 z)
      have hintegrand : DifferentiableOn ℂ integrand (Metric.ball c r) :=
        hH.clm_apply prev.2
      exact ⟨normalizedDiskPrimitive c r integrand 0 hintegrand,
        differentiableOn_normalizedDiskPrimitive c r integrand 0 hintegrand⟩


theorem holomorphicPicardIterates_apply_center (c : ℂ) (r : ℝ)
    (H : ℂ → E →L[ℂ] E) (hH : DifferentiableOn ℂ H (Metric.ball c r)) (y : E) :
    ∀ n : ℕ, (holomorphicPicardIterates c r H hH y n).1 c = if n = 0 then y else 0 := by
  intro n
  cases n with
  | zero => simp only [holomorphicPicardIterates, ↓reduceIte]
  | succ _ =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, holomorphicPicardIterates]
      exact normalizedDiskPrimitive_apply_center c r _ 0 _

theorem holomorphicPicardIterates_hasDerivAt_succ (c : ℂ) (r : ℝ)
    (H : ℂ → E →L[ℂ] E) (hH : DifferentiableOn ℂ H (Metric.ball c r)) (y : E)
    (n : ℕ) {z : ℂ} (hz : z ∈ Metric.ball c r) :
    HasDerivAt (holomorphicPicardIterates c r H hH y (n + 1)).1
      (H z ((holomorphicPicardIterates c r H hH y n).1 z)) z := by
  simp only [holomorphicPicardIterates]
  exact hasDerivAt_normalizedDiskPrimitive
    (hH.clm_apply (holomorphicPicardIterates c r H hH y n).2) hz

end DOZZ.Proofs
