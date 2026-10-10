/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FieldChaosAffineMax
public import DOZZ.GMC.KahaneLpLimit
public import DOZZ.GMC.KahaneNonnegativeConvexOrder
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Positive-power Kahane comparison at chaos limits. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Limit Kahane comparison for positive powers above one. Each finite-cutoff pair satisfies the
continuum covariance order; convergence against the test mass in probability and in `L¹` passes
the comparison to the chaos limits. -/
theorem kahane_limit_field_positive_power
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [MeasurableSpace S]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (Φ : ℝ → ΩX → S → ℝ) (Ψ : ℝ → ΩY → S → ℝ)
    (hΦ : ∀ r, IsCenteredGaussianField PX (Φ r))
    (hΨ : ∀ r, IsCenteredGaussianField PY (Ψ r))
    (ν : Measure S) [IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ p : ℝ) (hp : 1 < p)
    (hcov : ∀ r, ∀ᵐ q ∂ν.prod ν,
      ∫ ω, Φ r ω q.1 * Φ r ω q.2 ∂PX ≤ ∫ ω, Ψ r ω q.1 * Ψ r ω q.2 ∂PY)
    (hdiag : ∀ r, ∀ᵐ x ∂ν,
      ∫ ω, Φ r ω x ^ 2 ∂PX ≤ ∫ ω, Ψ r ω x ^ 2 ∂PY)
    (ZX : ΩX → ℝ) (ZY : ΩY → ℝ)
    (hXconv : TendstoInMeasure PX
      (fun r ω => (fieldChaosMass PX (Φ r) ν h γ ω).toReal) atTop ZX)
    (hYconv : TendstoInMeasure PY
      (fun r ω => (fieldChaosMass PY (Ψ r) ν h γ ω).toReal) atTop ZY)
    (hXL1 : Tendsto (fun r : ℝ =>
      eLpNorm (fun ω => (fieldChaosMass PX (Φ r) ν h γ ω).toReal - ZX ω) 1 PX)
      atTop (𝓝 0))
    (hYL1 : Tendsto (fun r : ℝ =>
      eLpNorm (fun ω => (fieldChaosMass PY (Ψ r) ν h γ ω).toReal - ZY ω) 1 PY)
      atTop (𝓝 0)) :
    ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (ZX ω)) p ∂PX ≤
      ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (ZY ω)) p ∂PY := by
  let : IsProbabilityMeasure PX := (hΦ 0 |>.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
  let : IsProbabilityMeasure PY := (hΨ 0 |>.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
  let fX : ℝ → ΩX → ℝ := fun r ω => (fieldChaosMass PX (Φ r) ν h γ ω).toReal
  let fY : ℝ → ΩY → ℝ := fun r ω => (fieldChaosMass PY (Ψ r) ν h γ ω).toReal
  have hfX (r : ℝ) : Integrable (fX r) PX :=
    (fieldChaosMass_toReal_integrable_mean PX (Φ r) (hΦ r) ν h hh hhb γ).1
  have hfY (r : ℝ) : Integrable (fY r) PY :=
    (fieldChaosMass_toReal_integrable_mean PY (Ψ r) (hΨ r) ν h hh hhb γ).1
  have hZXmeas : AEMeasurable ZX PX := hXconv.aemeasurable (fun r => (hfX r).aemeasurable)
  have hZYmeas : AEMeasurable ZY PY := hYconv.aemeasurable (fun r => (hfY r).aemeasurable)
  have hZX := integrable_of_eLpNorm_sub_tendsto PX fX ZX atTop hfX hZXmeas hXL1
  have hZY := integrable_of_eLpNorm_sub_tendsto PY fY ZY atTop hfY hZYmeas hYL1
  have hXnat : TendstoInMeasure PX (fun n : ℕ => fX n) atTop ZX :=
    hXconv.comp tendsto_natCast_atTop_atTop
  have hYnat : TendstoInMeasure PY (fun n : ℕ => fY n) atTop ZY :=
    hYconv.comp tendsto_natCast_atTop_atTop
  obtain ⟨ns, _, hXae⟩ := hXnat.exists_seq_tendsto_ae
  obtain ⟨ms, _, hYae⟩ := hYnat.exists_seq_tendsto_ae
  have hZX0 : ∀ᵐ ω ∂PX, 0 ≤ ZX ω := by
    filter_upwards [hXae] with ω hω
    exact isClosed_Ici.mem_of_tendsto hω (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
  have hZY0 : ∀ᵐ ω ∂PY, 0 ≤ ZY ω := by
    filter_upwards [hYae] with ω hω
    exact isClosed_Ici.mem_of_tendsto hω (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
  have htX : Tendsto (fun r => ∫ ω, fX r ω ∂PX) atTop (𝓝 (∫ ω, ZX ω ∂PX)) :=
    tendsto_integral_of_L1' ZX (Eventually.of_forall hfX) hXL1
  have htY : Tendsto (fun r => ∫ ω, fY r ω ∂PY) atTop (𝓝 (∫ ω, ZY ω ∂PY)) :=
    tendsto_integral_of_L1' ZY (Eventually.of_forall hfY) hYL1
  have htXconst : Tendsto (fun r => ∫ ω, fX r ω ∂PX) atTop (𝓝 (∫ x, (h x : ℝ) ∂ν)) := by
    have heq (r : ℝ) := (fieldChaosMass_toReal_integrable_mean PX (Φ r) (hΦ r) ν h hh hhb γ).2
    simp_rw [show ∀ r, (∫ ω, fX r ω ∂PX) = ∫ x, (h x : ℝ) ∂ν from heq]
    exact tendsto_const_nhds
  have htYconst : Tendsto (fun r => ∫ ω, fY r ω ∂PY) atTop (𝓝 (∫ x, (h x : ℝ) ∂ν)) := by
    have heq (r : ℝ) := (fieldChaosMass_toReal_integrable_mean PY (Ψ r) (hΨ r) ν h hh hhb γ).2
    simp_rw [show ∀ r, (∫ ω, fY r ω ∂PY) = ∫ x, (h x : ℝ) ∂ν from heq]
    exact tendsto_const_nhds
  have hmean : (∫ ω, ZX ω ∂PX) = ∫ ω, ZY ω ∂PY :=
    (tendsto_nhds_unique htX htXconst).trans (tendsto_nhds_unique htY htYconst).symm
  apply nonneg_power_comparison_of_affine_max_order PX PY ZX ZY hZX hZY hZX0 hZY0 hmean
    (fun n a b => ?_) p hp.le
  have hta := affineMax_integral_tendsto_of_eLpNorm PX fX ZX atTop hfX hZXmeas hXL1 a b
  have htb := affineMax_integral_tendsto_of_eLpNorm PY fY ZY atTop hfY hZYmeas hYL1 a b
  exact le_of_tendsto_of_tendsto hta htb (Eventually.of_forall fun r =>
    kahane_field_affine_max PX PY (Φ r) (Ψ r) (hΦ r) (hΨ r) ν h hh hhb γ a b
      (hcov r) (hdiag r))



end DOZZ.Proofs
