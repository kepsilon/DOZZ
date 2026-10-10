module

public import DOZZ.GMC.SharpMoments.InverseGamma
public import DOZZ.GMC.Annulus.HigherScales

/-! # Coupling comparison for convex cutoff moments -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Convex cutoff moments increase with the coupling on sets with nonnegative covariance. -/
theorem regularizedGMC_convex_moment_le_of_gamma_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ g r : ℝ) (hγ : 0 < γ)
    (hγg : γ ≤ g) (A : Set ℂ) (hA : MeasurableSet A) (hAtop : gmcReferenceMeasure A ≠ ⊤)
    (hnn : ∀ x ∈ A, ∀ y ∈ A, 0 ≤ ∫ ω, Xc ω x r * Xc ω y r ∂P) (p : ℝ) (hp : p ≤ 0 ∨ 1 ≤ p) :
    ∫⁻ ω, (regularizedGMC P Xc γ r ω A) ^ p ∂P ≤
      ∫⁻ ω, (regularizedGMC P Xc g r ω A) ^ p ∂P := by
  have hg : 0 < g := lt_of_lt_of_le hγ hγg
  set c : ℝ := γ / g with hc
  have hc0 : 0 ≤ c := div_nonneg hγ.le hg.le
  have hc1 : c ≤ 1 := (div_le_one hg).mpr hγg
  have hc2 : c ^ 2 ≤ 1 := by nlinarith
  set ν : Measure ℂ := gmcReferenceMeasure.restrict A with hν
  have hνfin : IsFiniteMeasure ν := by
    rw [hν]
    exact isFiniteMeasure_restrict.mpr hAtop
  have hΦ := circleAverage_smul_isCenteredGaussianField P X hX Xc hXc r c
  have hΨ := circleAverage_isCenteredGaussianField P X hX Xc hXc r
  have hmemA : ∀ᵐ x ∂ν, x ∈ A := by
    rw [hν]
    exact ae_restrict_mem hA
  have hcov : ∀ᵐ q ∂ν.prod ν,
      ∫ ω, c * Xc ω q.1 r * (c * Xc ω q.2 r) ∂P ≤ ∫ ω, Xc ω q.1 r * Xc ω q.2 r ∂P := by
    have hprod : ν.prod ν = (gmcReferenceMeasure.prod gmcReferenceMeasure).restrict (A ×ˢ A) := by
      have : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
      rw [hν, Measure.prod_restrict]
    rw [hprod]
    filter_upwards [ae_restrict_mem (hA.prod hA)] with q hq
    have hfun : (fun ω => c * Xc ω q.1 r * (c * Xc ω q.2 r)) =
        fun ω => c ^ 2 * (Xc ω q.1 r * Xc ω q.2 r) := by
      funext ω
      ring
    rw [hfun, integral_const_mul]
    have h0 := hnn q.1 hq.1 q.2 hq.2
    nlinarith
  have hdiag : ∀ᵐ x ∂ν, ∫ ω, (c * Xc ω x r) ^ 2 ∂P ≤ ∫ ω, Xc ω x r ^ 2 ∂P := by
    filter_upwards [] with x
    have hfun : (fun ω => (c * Xc ω x r) ^ 2) = fun ω => c ^ 2 * Xc ω x r ^ 2 := by
      funext ω
      ring
    rw [hfun, integral_const_mul]
    have h0 : 0 ≤ ∫ ω, Xc ω x r ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
    nlinarith
  have hk := kahane_field_power_convex P P (fun ω x => c * Xc ω x r) (fun ω x => Xc ω x r)
    hΦ hΨ ν (fun _ => 1) measurable_const ⟨1, fun _ => le_rfl⟩ g p hp
    hcov hdiag
  have hleft : ∀ ω, regularizedGMC P Xc γ r ω A =
      fieldChaosMass P (fun ω x => c * Xc ω x r) ν (fun _ => 1) g ω :=
    fun ω => regularizedGMC_apply_eq_fieldChaosMass_scaled P X hX Xc hXc γ g r hg.ne' A hA ω
  have hright : ∀ ω, regularizedGMC P Xc g r ω A =
      fieldChaosMass P (fun ω x => Xc ω x r) ν (fun _ => 1) g ω :=
    fun ω => regularizedGMC_apply_eq_fieldChaosMass P X hX Xc hXc g r A hA ω
  simp only [hleft, hright]
  exact hk

/-- At fine cutoffs, a single reference-disk positive moment bound works for every coupling
in a compact family below its critical moment threshold. -/
theorem regularizedGMC_reference_positive_moment_compact_gamma
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (Γ : Set ℝ) (hΓ : IsCompact Γ) (hΓpos : ∀ γ ∈ Γ, 0 < γ)
    (p : ℝ) (hp : 1 < p) (hcrit : ∀ γ ∈ Γ, p < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ γ ∈ Γ, ∀ r : ℝ, 1 ≤ r →
      (∫⁻ ω, (regularizedGMC P Xc γ r ω (Metric.ball 0 (1 / 8))) ^ p ∂P) ≤ C := by
  classical
  rcases Set.eq_empty_or_nonempty Γ with hEmpty | hNonempty
  · refine ⟨0, by simp, ?_⟩
    simp [hEmpty]
  obtain ⟨g, hg, hmax⟩ := hΓ.exists_isMaxOn hNonempty continuousOn_id
  obtain ⟨C, hC, hbound⟩ := regularizedGMC_reference_positive_moment_uniform
    P X hX Xc hXc g p (hΓpos g hg) hp (hcrit g hg)
    (R := (1 / 8 : ℝ)) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro γ hγ r hr
  have htop : gmcReferenceMeasure (Metric.ball (0 : ℂ) (1 / 8)) ≠ ⊤ :=
    ne_top_of_le_ne_top gmcReferenceMeasure_univ_ne_top (measure_mono (Set.subset_univ _))
  have hcmp := regularizedGMC_convex_moment_le_of_gamma_le P X hX Xc hXc γ g r
    (hΓpos γ hγ) (hmax hγ) (Metric.ball 0 (1 / 8)) Metric.isOpen_ball.measurableSet htop
    (fun x hx y hy => circleField_covariance_nonneg_reference P X hX Xc hXc r hr x hx y hy)
    p (Or.inr hp.le)
  exact hcmp.trans (hbound r (by linarith))

end DOZZ.Proofs
