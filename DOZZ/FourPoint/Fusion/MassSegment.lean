/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.ConvexMass
public import DOZZ.FourPoint.Fusion.RootedMomentIdentity
public import DOZZ.GMC.Moments.RhoCoulomb
public import DOZZ.FourPoint.Fusion.MassPositiveFinite
public import DOZZ.FourPoint.FourPointTZeroEqStructureConstant
public import DOZZ.FourPoint.TaylorFixedDisk
/-! # The unrooted positive KRV mass segment -/
@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace DOZZ.Proofs
noncomputable def fusionUnrootedSegment (γ α₁ α₂ α₃ t : ℝ) (z : ℂ) (μ : Measure ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal t * coulombMass γ μ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ +
    ENNReal.ofReal (1 - t) * coulombMass γ μ ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃
/-- The segment inverse power is a measurable functional of its measure. -/
theorem fusionUnrootedSegment_measurable (γ α₁ α₂ α₃ t s : ℝ) (z : ℂ) :
    Measurable (fun μ : Measure ℂ => fusionUnrootedSegment γ α₁ α₂ α₃ t z μ ^ s) :=
  (((fusion_measurable_coulombMass γ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃).const_mul _).add
    ((fusion_measurable_coulombMass γ ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃).const_mul _)).pow_const s
/-- The coincident zero-insertion mass is positive and finite almost surely. -/
theorem fusion_zeroMass_pos_finite_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hα₁ : α₁ < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) :
    ∀ᵐ ω ∂P, coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃ ≠ 0 ∧
      coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃ ≠ ⊤ := by
  have hi : Function.Injective (![0, 1] : Fin 2 → ℂ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have ha : ∀ j : Fin 2, (![α₁ - γ / 2, α₂] : Fin 2 → ℝ) j < Q γ := by
    intro j
    fin_cases j
    · change α₁ - γ / 2 < Q γ
      unfold Q
      linarith
    · exact hα₂
  filter_upwards [coulomb_mass_pos_finite_ae P X hX γ hγ hγ2 M hM ![0, 1] hi ![α₁ - γ / 2, α₂] α₃ ha hα₃,
    gmc_rho_eq_coulombMass_ae P X hX γ hγ hγ2 M hM (α₁ - γ / 2) α₂ α₃,
    gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 0,
    gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 1] with ω hω he h0 h1
  have hmass := coulombMass_at_zero_eq_rho γ (γ / 2) α₁ α₂ α₃ (M ω) h0 h1
  simp only [← neg_div] at hmass
  rw [hmass, he]
  exact hω
/-- All nonpositive segment moments are uniformly bounded over the time interval and unit roots. -/
theorem fusionUnrootedSegment_inverse_uniform {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p : ℝ) (hp : 0 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℂ, ‖z‖ ≤ 1 →
      (∫⁻ ω, fusionUnrootedSegment γ α₁ α₂ α₃ t z (M ω) ^ (-p) ∂P) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hb⟩ := coulomb_inverse_moment_uniform_roots P X hX γ hγ hγ2 M hM
    ![-γ / 2, α₁, α₂] α₃ p hp
  refine ⟨C + C, by linarith, ?_⟩
  intro t ht z hz
  have hzv : ∀ j : Fin 3, ‖(![z, 0, 1] : Fin 3 → ℂ) j‖ ≤ 1 := by
    intro j; fin_cases j
    · exact hz
    · simp
    · simp
  have h0v : ∀ j : Fin 3, ‖(![0, 0, 1] : Fin 3 → ℂ) j‖ ≤ 1 := by intro j; fin_cases j <;> simp
  calc
    _ ≤ ∫⁻ ω, coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ (-p) +
        coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃ ^ (-p) ∂P :=
      lintegral_mono fun ω => fusion_convexMass_inverse_bound _ _ t (-p) ht (by linarith)
    _ = _ := lintegral_add_left' ((gmc_coulombMass_aemeasurable P X hX γ hγ hγ2 M hM _ _ _).pow_const _) _
    _ ≤ ENNReal.ofReal C + ENNReal.ofReal C := add_le_add (hb _ hzv) (hb _ h0v)
    _ = _ := (ENNReal.ofReal_add hC.le hC.le).symm
end DOZZ.Proofs
