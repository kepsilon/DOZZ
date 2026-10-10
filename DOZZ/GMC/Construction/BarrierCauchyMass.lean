/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.BarrierCauchyEstimates
public import DOZZ.Statements.GMC.RegularizedLogChaosTestMass

/-! Growing-barrier good masses for arbitrary compatible admissible regularizations. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The thick-point event through log scale `r`: every integer coarse field scale between `k₀`
and the current cutoff scale stays below the linear barrier. -/
def admissibleGrowingBarrierSet {Ω : Type*}
    (Y : Ω → ℝ → ℂ → ℝ) (a : ℝ) (k₀ : ℕ) (r : ℝ) : Set (Ω × ℂ) :=
  {q | ∀ k : ℕ, k₀ ≤ k → (k : ℝ) ≤ r →
    Y q.1 (Real.exp (-(k : ℝ))) q.2 ≤ a * (k : ℝ)}

/-- The growing-barrier event is jointly measurable in the sample and spatial point. -/
theorem admissibleGrowingBarrierSet_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (a : ℝ) (k₀ : ℕ) (r : ℝ) :
    MeasurableSet (admissibleGrowingBarrierSet Y a k₀ r) := by
  classical
  let B : ℕ → Set (Ω × ℂ) := fun k =>
    if hk : k₀ ≤ k ∧ (k : ℝ) ≤ r then
      {q | Y q.1 (Real.exp (-(k : ℝ))) q.2 ≤ a * (k : ℝ)}
    else Set.univ
  have hEq : admissibleGrowingBarrierSet Y a k₀ r = ⋂ k, B k := by
    ext q
    simp only [admissibleGrowingBarrierSet, Set.mem_iInter]
    constructor
    · intro h k
      by_cases hk : k₀ ≤ k ∧ (k : ℝ) ≤ r
      · simpa [B, hk] using h k hk.1 hk.2
      · simp [B, hk]
    · intro h k hk₀ hkr
      have hk : k₀ ≤ k ∧ (k : ℝ) ≤ r := ⟨hk₀, hkr⟩
      simpa [B, hk] using h k
  rw [hEq]
  apply MeasurableSet.iInter
  intro k
  by_cases hk : k₀ ≤ k ∧ (k : ℝ) ≤ r
  · have hset : MeasurableSet
        {q : Ω × ℂ | Y q.1 (Real.exp (-(k : ℝ))) q.2 ≤ a * (k : ℝ)} :=
      measurableSet_le (hY.measurableAtScale (Real.exp (-(k : ℝ)))) measurable_const
    simpa [B, hk] using hset
  · simp [B, hk]

/-- Choose one of two compatible admissible regularization families at a fine cutoff. -/
def compatibleAdmissibleFineField {Ω : Type*}
    (Y Z : Ω → ℝ → ℂ → ℝ) (b : Bool) (ω : Ω) (ε : ℝ) (x : ℂ) : ℝ :=
  if b then Y ω ε x else Z ω ε x

/-- Every admissible Gaussian regularization is defined over a probability measure. -/
theorem admissibleLogRegularization_isProbabilityMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) :
    IsProbabilityMeasure P := by
  let q : Fin 1 → ℝ × ℂ := fun _ => (ε₀ / 2, 0)
  have hq : ∀ i, 0 < (q i).1 ∧ (q i).1 ≤ ε₀ := by
    intro i
    simp only [q]
    constructor <;> linarith [hY.cutoffPositive]
  exact (hY.gaussian 1 q hq).1

/-- At each regularization scale, the variance is measurable in the spatial coordinate. -/
theorem admissibleLogRegularization_variance_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (ε : ℝ) :
    Measurable (fun x => gaussianVariance P (fun ω => Y ω ε x)) := by
  have hfield : Measurable (fun q : Ω × ℂ => Y q.1 ε q.2) := hY.measurableAtScale ε
  have hswap : Measurable (fun q : ℂ × Ω => Y q.2 ε q.1) :=
    hfield.comp measurable_swap
  have hsquare : Measurable (fun q : ℂ × Ω => Y q.2 ε q.1 ^ 2) := hswap.pow_const 2
  have hvar : Measurable (fun x : ℂ => ∫ ω, Y ω ε x ^ 2 ∂P) :=
    hsquare.stronglyMeasurable.integral_prod_right.measurable
  have heq : (fun x : ℂ => gaussianVariance P (fun ω => Y ω ε x)) =
      fun x => ∫ ω, Y ω ε x ^ 2 ∂P := by
    funext x
    simp [gaussianVariance, gaussianCovariance, pow_two]
  rw [heq]
  exact hvar

/-- Variance measurability is preserved when either of two compatible fine fields is selected. -/
theorem compatibleAdmissibleFineField_variance_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    (b : Bool) (ε : ℝ) :
    Measurable (fun x => gaussianVariance P
      (fun ω => compatibleAdmissibleFineField Y Z b ω ε x)) := by
  cases b
  · simpa [compatibleAdmissibleFineField] using
      admissibleLogRegularization_variance_measurable P U dens ε₁ Z hZ ε
  · simpa [compatibleAdmissibleFineField] using
      admissibleLogRegularization_variance_measurable P U dens ε₀ Y hY ε

/-- The good part of a compact-test Wick integral, with the barrier taken from the first
regularization at every integer scale up to the fine cutoff. The Boolean selects either fine
regularization, so this definition supports both diagonal and mixed second moments. -/
noncomputable def compatibleGrowingBarrierTestMass
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ) (γ a : ℝ) (k₀ : ℕ)
    (r : ℝ) (b : Bool) (ω : Ω) (f : BoundedContinuousFunction ℂ ℝ) : ℝ := by
  classical
  exact ∫ x, f x * Real.exp
      (γ * compatibleAdmissibleFineField Y Z b ω (Real.exp (-r)) x -
        γ ^ 2 / 2 * gaussianVariance P
          (fun ω' => compatibleAdmissibleFineField Y Z b ω' (Real.exp (-r)) x)) *
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)
        (fun _ => (1 : ℝ)) (ω, x) ∂logRegularizationReference U dens



end DOZZ.Proofs
