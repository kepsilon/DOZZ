/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GFFStructure.PoissonCollarValue
import DOZZ.GFFStructure.MarkovAssembly

/-! The statement `DOZZ.exists_exteriorPinned_markov_uniform`,
proved by `DOZZ.Proofs.exists_exteriorPinned_markov_uniform`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

universe u

namespace DOZZ

/-- Exterior-pin Markov decomposition with all-order uniform harmonic moments, for the separated
two-insertion joint tail [KRV, Lemma 7.3] (erratum K9, see docs/ERRATA-AND-DEVIATIONS.md). For this
application take `n = 2`, `ρ = 5/4`, `a = 1` and a fixed positive separation margin. The bound
precedes every realization and center choice. Neither the pin scalar nor the exterior field of `X`
is asserted independent. The circle-cutoff conjuncts (with a `σ(Dᵢ) ⊗ Borel`-measurable version
`Dc`) are the form needed for that tail estimate; the test-level conjuncts alone do not reach it. -/
theorem exists_exteriorPinned_markov_uniform
    (n : ℕ) (R ρ a δ : ℝ) (hR : 1 < R) (hρ : 0 < ρ)
    (haρ : a < ρ) (hδ : 0 < δ) :
    ∃ C : ℝ → ℝ, (∀ l, 0 < l → 0 < C l) ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω]
      (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ),
      IsEquatorGFF P X → IsCircleAverage P X Xc →
    ∀ c : Fin n → ℂ,
      (∀ i, ‖c i‖ + ρ + δ ≤ R) →
      (∀ i j, i ≠ j → 2 * ρ + δ ≤ dist (c i) (c j)) →
    ∃ (D : Fin n → Ω → Distr) (H : Ω → Distr)
      (Hi : Fin n → Ω → ℂ → ℝ) (Dc : Fin n → Ω → ℂ → ℝ → ℝ) (ε : ℝ) (q : ℕ → ℝ → ℝ)
      (p : Fin n → ℂ → ℕ → TestFn),
      0 < ε ∧ ε < δ / 2 ∧
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (q k) ∧ HasCompactSupport (q k) ∧
        tsupport (q k) ⊆ Ioo 0 (ε / (k + 1)) ∧
        (∀ t, 0 ≤ q k t) ∧ (∫ t : ℝ, q k t) = 1) ∧
      (∀ i z (hz : z ∈ ball (c i) ρ), ∀ k,
        (∀ w, p i z k w = poissonCollarValue (c i) z ρ hρ hz (q k) w) ∧
        tsupport (p i z k) ⊆ (⋃ j, ball (c j) ρ)ᶜ) ∧
      (∀ i z, z ∈ ball (c i) ρ →
        Tendsto (fun k => eLpNorm
          (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω (p i z k) - Hi i ω z) 2 P)
          atTop (𝓝 0)) ∧
      (∀ i, IsGaussianProcess (fun f : TestFn => fun ω => D i ω f) P ∧
        (∀ f : TestFn, Measurable (fun ω => D i ω f) ∧
          MemLp (fun ω => D i ω f) 2 P ∧ (∫ ω, D i ω f ∂P) = 0) ∧
        (∀ f g : TestFn, covariance (fun ω => D i ω f) (fun ω => D i ω g) P =
          diskGreenCovariance (c i) ρ hρ f g)) ∧
      IsGaussianProcess (fun f : TestFn => fun ω => H ω f) P ∧
      (∀ f : TestFn, Measurable (fun ω => H ω f) ∧
        MemLp (fun ω => H ω f) 2 P ∧ (∫ ω, H ω f ∂P) = 0) ∧
      (∀ i, Measurable (fun w : Ω × ℂ => Hi i w.1 w.2)) ∧
      (∀ i z, z ∈ ball (c i) ρ →
        MemLp (fun ω => Hi i ω z) 2 P ∧ (∫ ω, Hi i ω z ∂P) = 0) ∧
      (∀ i z w, z ∈ ball (c i) ρ → w ∈ ball (c i) ρ →
        covariance (fun ω => Hi i ω z) (fun ω => Hi i ω w) P =
          Real.log R + Real.log ρ -
            Real.log ‖(ρ : ℂ) ^ 2 - (z - c i) * star (w - c i)‖) ∧
      (∀ᵐ ω ∂P,
        (∀ f : TestFn, exteriorPinnedEvaluation X Xc R (by linarith) ω f =
          (∑ i, D i ω f) + H ω f) ∧
          (∀ f : TestFn, X ω f = (∑ i, D i ω f) + H ω f -
          equatorRestorationScalar Xc R (by linarith) ω * (∫ z : ℂ, f z)) ∧
        (∀ i, InnerProductSpace.HarmonicOnNhd (Hi i ω) (ball (c i) ρ) ∧
          ContDiffOn ℝ (⊤ : ℕ∞) (Hi i ω) (ball (c i) ρ)) ∧
        (∀ i (f : TestFn), tsupport f ⊆ ball (c i) ρ →
          H ω f = (∫ z : ℂ, f z * Hi i ω z)) ∧
        (∀ i (f : TestFn), tsupport f ⊆ (closedBall (c i) ρ)ᶜ → D i ω f = 0)) ∧
      iIndepFun (fun j : Option (Fin n) => fun ω => fun f : TestFn =>
        match j with | none => H ω f | some i => D i ω f) P ∧
      IndepFun (fun ω => fun i => fun f : TestFn => D i ω f)
        (fun ω => fun f : {f : TestFn // tsupport f ⊆ (⋃ i, ball (c i) ρ)ᶜ} =>
          exteriorPinnedEvaluation X Xc R (by linarith) ω f.val) P ∧
      (∀ i l, 0 < l →
        ∫⁻ ω, ENNReal.ofReal (Real.exp (l *
            |equatorRestorationScalar Xc R (by linarith) ω|)) *
          ⨆ z ∈ closedBall (c i) a, ENNReal.ofReal (Real.exp (l * |Hi i ω z|)) ∂P
          ≤ ENNReal.ofReal (C l)) ∧
      -- Circle cutoffs of each Dirichlet field, radius `e^{-r}` as in `IsCircleAverage`.
      (∀ i, Measurable[(MeasurableSpace.comap (fun ω => fun f : TestFn => D i ω f)
          MeasurableSpace.pi).prod inferInstance]
        (fun w : Ω × (ℂ × ℝ) => Dc i w.1 w.2.1 w.2.2)) ∧
      (∀ i, IsGaussianProcess (fun p : {p : ℂ × ℝ // ‖p.1 - c i‖ + Real.exp (-p.2) < ρ} =>
        fun ω => Dc i ω p.1.1 p.1.2) P) ∧
      (∀ i (x : ℂ) (r : ℝ), ‖x - c i‖ + Real.exp (-r) < ρ →
        MemLp (fun ω => Dc i ω x r) 2 P ∧ (∫ ω, Dc i ω x r ∂P) = 0 ∧
        (fun ω => Xc ω x r) =ᵐ[P] fun ω =>
          Dc i ω x r + Hi i ω x - equatorRestorationScalar Xc R (by linarith) ω) ∧
      (∀ i (x y : ℂ) (r s : ℝ), ‖x - c i‖ + Real.exp (-r) < ρ →
        ‖y - c i‖ + Real.exp (-s) < ρ →
        covariance (fun ω => Dc i ω x r) (fun ω => Dc i ω y s) P =
          ∫ v, ∫ w, diskGreenKernel (c i) ρ hρ v w ∂circleMeasure y s ∂circleMeasure x r) := by exact DOZZ.Proofs.exists_exteriorPinned_markov_uniform n R ρ a δ hR hρ haρ hδ

end DOZZ
