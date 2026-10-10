module

public import DOZZ.GMC.CircleAverageCutoffIntensity
public import DOZZ.GMC.FiniteFirstMomentSubunit

/-! Uniform subunit moments of finite-cutoff GMC masses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- A finite circle-cutoff GMC mass is measurable as a random variable on every Borel set. -/
theorem regularizedGMC_mass_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ r : ℝ) (A : Set ℂ) (hA : MeasurableSet A) :
    AEMeasurable (fun ω => regularizedGMC P Xc γ r ω A) P := by
  classical
  have : IsProbabilityMeasure P := hX.1
  let V : ℂ → ℝ := fun x => ∫ ω, Xc ω x r ^ 2 ∂P
  let density : Ω × ℂ → ℝ≥0∞ := fun p => ENNReal.ofReal
    (Real.exp (γ * Xc p.1 p.2 r - γ ^ 2 / 2 * V p.2) * normPlus p.2 ^ (-4 : ℝ))
  let q : ℂ → Ω → ℝ := fun x ω => Xc ω x r ^ 2
  have hq : Measurable (Function.uncurry q) := by
    have hbase : Measurable (fun p : ℂ × Ω => Xc p.2 p.1 r) :=
      (hXc.1 r).comp measurable_swap
    change Measurable (fun p : ℂ × Ω => Xc p.2 p.1 r ^ 2)
    have hEq : (fun p : ℂ × Ω => Xc p.2 p.1 r ^ 2) =
        fun p => Xc p.2 p.1 r * Xc p.2 p.1 r := by
      funext p
      ring
    rw [hEq]
    exact hbase.mul hbase
  have hVmeas : Measurable V := by
    change Measurable (fun x => ∫ ω, q x ω ∂P)
    exact hq.stronglyMeasurable.integral_prod_right.measurable
  have hfield : Measurable (fun p : Ω × ℂ => Xc p.1 p.2 r) := hXc.1 r
  have hnormPlus : Measurable (fun x : ℂ => normPlus x) := by
    unfold normPlus
    exact measurable_const.max measurable_norm
  have hVprod : Measurable (fun p : Ω × ℂ => V p.2) := hVmeas.comp measurable_snd
  have hnormprod : Measurable (fun p : Ω × ℂ => normPlus p.2) :=
    hnormPlus.comp measurable_snd
  have hdensity : Measurable density := by
    dsimp [density]
    fun_prop
  let G : Ω × ℂ → ℝ≥0∞ := fun p => if p.2 ∈ A then density p else 0
  have hG : Measurable G := by
    exact Measurable.ite (hA.preimage measurable_snd) hdensity measurable_const
  have hsection (ω : Ω) : regularizedGMC P Xc γ r ω A =
      ∫⁻ x, G (ω, x) ∂volume := by
    rw [regularizedGMC, withDensity_apply _ hA]
    rw [← lintegral_indicator hA]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ A
    · simp [G, hx, density, V]
    · simp [G, hx]
  have hmass : Measurable (fun ω => ∫⁻ x, G (ω, x) ∂volume) :=
    hG.lintegral_prod_right'
  have heq : (fun ω => regularizedGMC P Xc γ r ω A) =
      fun ω => ∫⁻ x, G (ω, x) ∂volume := by
    funext ω
    exact hsection ω
  rw [heq]
  exact hmass.aemeasurable

/-- On a probability space, a finite-cutoff GMC mass has every subunit positive moment bounded
by one plus its deterministic first moment. The bound is uniform in the cutoff. -/
theorem regularizedGMC_subunit_moment_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ r : ℝ) (A : Set ℂ) (hA : MeasurableSet A)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫⁻ ω, ENNReal.rpow (regularizedGMC P Xc γ r ω A) p ∂P ≤
      1 + gmcReferenceMeasure A := by
  have : IsProbabilityMeasure P := hX.1
  have hsub := lintegral_rpow_le_one_add_of_probability P
    (fun ω => regularizedGMC P Xc γ r ω A) hp0 hp1
  rw [regularizedGMC_lintegral_eq_reference P X hX Xc hXc γ r A hA] at hsub
  exact hsub

end DOZZ.Proofs
