/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.FiniteVertexHolomorphy
public import DOZZ.Correlations.Analytic.RetainedRegions
public import DOZZ.Correlations.Analytic.EquatorCorrectionBounds

/-! Joint Wick normalization and the exact equator pin correction for mixed frames. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The final coordinate is the outward vertex at the origin. -/
def mixedVertexCenters {N : ℕ} (z : Fin N → ℂ) : Fin (N + 1) → ℂ := Fin.snoc z 0

/-- Finite vertices shrink inward while the last circle expands outward. -/
def mixedVertexTimes (N : ℕ) (r : ℝ) : Fin (N + 1) → ℝ :=
  Fin.snoc (fun _ => r) (-r)

/-- The complex continuation of the negative zero-mode exponent. -/
noncomputable def complexMomentPower {N : ℕ} (γ : ℝ) (β : Fin N → ℂ) : ℂ :=
  - (((-2 * Q γ / γ : ℝ) : ℂ) + (γ : ℂ)⁻¹ * ∑ i, β i)

/-- Joint Wick normalization uses the full covariance matrix of the actual vertex coordinates. -/
noncomputable def jointVertexPolynomial
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    (Xc : Ω → ℂ → ℝ → ℝ) (z : Fin N → ℂ) (r : Fin N → ℝ) (β : Fin N → ℂ) : ℂ :=
  -(∑ i, ∑ j, β i * β j *
    (gaussianCovariance P (fun ω => Xc ω (z i) (r i))
      (fun ω => Xc ω (z j) (r j)) : ℂ)) / 2

/-- The pin factor cancels the constant equator contribution to the tilted retained mass.
Joint rather than coordinatewise Wick normalization removes the deterministic pair factor;
the finite-position Coulomb prefactor can then be multiplied after taking the limit. -/
noncomputable def normalizedVertexPolynomial
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    (Xc : Ω → ℂ → ℝ → ℝ) (γ : ℝ) (z : Fin N → ℂ) (r : ℝ)
    (β : Fin (N + 1) → ℂ) : ℂ :=
  jointVertexPolynomial P Xc (mixedVertexCenters z) (mixedVertexTimes N r) β -
    complexMomentPower γ β * (γ : ℂ) *
      ∑ i, β i.castSucc * (equatorCircleMean (z i) r : ℂ)

/-- The normalized cutoff observable retains a charge-independent unweighted mass. -/
noncomputable def normalizedVertexMoment
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    (Xc : Ω → ℂ → ℝ → ℝ) (M : Ω → Measure ℂ) (O : Set ℂ)
    (γ : ℝ) (z : Fin N → ℂ) (r : ℝ) (β : Fin (N + 1) → ℂ) : ℂ :=
  ∫ ω, Complex.exp (normalizedVertexPolynomial P Xc γ z r β +
    ∑ i, β i * (Xc ω (mixedVertexCenters z i) (mixedVertexTimes N r i) : ℂ)) *
    ((M ω O).toReal : ℂ) ^ complexMomentPower γ β ∂P

/-- The exact joint Wick and equator-normalized cutoff family is integrable and holomorphic
throughout the finite-radius bulk moment half-space. -/
theorem normalized_vertex_moment_holomorphic
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (O : Set ℂ) (ho : IsOpen O) (hb : Bornology.IsBounded O) (hn : O.Nonempty)
    (z : Fin N → ℂ) (r : ℝ) :
    (∀ β : Fin (N + 1) → ℂ, (complexMomentPower γ β).re < 4 / γ ^ 2 →
      Integrable (fun ω => Complex.exp (normalizedVertexPolynomial P Xc γ z r β +
        ∑ i, β i * (Xc ω (mixedVertexCenters z i) (mixedVertexTimes N r i) : ℂ)) *
        ((M ω O).toReal : ℂ) ^ complexMomentPower γ β) P) ∧
    DifferentiableOn ℂ (normalizedVertexMoment P Xc M O γ z r)
      {β | (complexMomentPower γ β).re < 4 / γ ^ 2} := by
  let := hX.1
  let A : Ω → ℝ := fun ω => (M ω O).toReal
  have hm := gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM O ho.measurableSet
  have hA : AEMeasurable A P := ENNReal.measurable_toReal.comp_aemeasurable hm
  have hpos : ∀ᵐ ω ∂P, 0 < A ω := by
    filter_upwards [open_mass_pos_finite_ae P X hX γ hγ hγ2 M hM O ho hb hn] with ω hω
    exact ENNReal.toReal_pos hω.1 hω.2
  have hinv (q : ℝ) (hq : 0 < q) : Integrable (fun ω => A ω ^ (-q)) P := by
    apply open_mass_real_power_integrable P X hX γ hγ hγ2 M hM O ho hb hn
    linarith [show (0 : ℝ) < 4 / γ ^ 2 by positivity]
  have hmoment (p : ℝ) (_ : 0 ≤ p) (hp : p < 4 / γ ^ 2) :
      Integrable (fun ω => A ω ^ p) P :=
    open_mass_real_power_integrable P X hX γ hγ hγ2 M hM O ho hb hn p hp
  have hc : DifferentiableOn ℂ (normalizedVertexPolynomial P Xc γ z r) univ := by
    unfold normalizedVertexPolynomial jointVertexPolynomial complexMomentPower
    fun_prop
  have hd := differentiableOn_gaussian_charge_moment P univ isOpen_univ
    (fun ω i => Xc ω (mixedVertexCenters z i) (mixedVertexTimes N r i))
    (circle_vertex_hasGaussianLaw P X hX Xc hXc
      (mixedVertexCenters z) (mixedVertexTimes N r)) A hA hpos
    (4 / γ ^ 2) (by positivity) hinv hmoment
    (normalizedVertexPolynomial P Xc γ z r) hc
    ((-2 * Q γ / γ : ℝ) : ℂ) ((γ : ℂ)⁻¹ • chargeSumCLM (N + 1))
  constructor
  · intro β hβ
    have hb' : -(↑(-2 * Q γ / γ) + ((γ : ℂ)⁻¹ • chargeSumCLM (N + 1)) β).re <
        4 / γ ^ 2 := by
      simpa only [complexMomentPower, smul_apply, smul_eq_mul,
        chargeSumCLM_apply, Complex.neg_re] using hβ
    simpa only [complexMomentPower, A, smul_apply, smul_eq_mul,
      chargeSumCLM_apply] using hd.1 β ⟨mem_univ β, hb'⟩
  · change DifferentiableOn ℂ (fun β => normalizedVertexMoment P Xc M O γ z r β) _
    simpa only [normalizedVertexMoment, complexMomentPower, A,
      smul_apply, smul_eq_mul, chargeSumCLM_apply, mem_univ, true_and,
      Complex.neg_re] using hd.2

end DOZZ.Proofs
