/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.Grid
public import DOZZ.FourPoint.BPZ.WardTilt
public import DOZZ.FourPoint.BPZ.Rooting
public import DOZZ.GMC.Construction.RootedAllRootFinite

/-! # The chaos measure has no atoms

The mass of the dyadic square of generation `k` containing `u` is a jointly measurable function
of the root `u` and the measure, and it decreases to the atom at `u` for a finite measure. Rooting
at `u` keeps the atom at `u` zero, because the chaos has no atom at a fixed point and the rooted
measure is finite. The rooted identity then shows that `∫ M{u} dM(u) = 0` almost surely, so the
chaos measure has almost surely no atoms at all. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The mass of the dyadic grid square of generation `k` containing `x`. -/
noncomputable def bpzDyadicMass (k : ℕ) (m : Measure ℂ) (x : ℂ) : ℝ≥0∞ :=
  m (bpzGridIdx ((2 ^ k)⁻¹) ⁻¹' {bpzGridIdx ((2 ^ k)⁻¹) x})

theorem measurable_bpzDyadicMass (k : ℕ) :
    Measurable (fun p : Measure ℂ × ℂ => bpzDyadicMass k p.1 p.2) := by
  set h : ℝ := (2 ^ k)⁻¹
  have hF : Measurable (fun q : (ℤ × ℤ) × Measure ℂ => q.2 (bpzGridIdx h ⁻¹' {q.1})) :=
    measurable_from_prod_countable_right fun i =>
      Measure.measurable_coe (measurableSet_bpzGridCell h i)
  exact hF.comp (((measurable_bpzGridIdx h).comp measurable_snd).prodMk measurable_fst)

theorem bpzDyadic_cell_subset_ball (k : ℕ) (x : ℂ) :
    bpzGridIdx ((2 ^ k)⁻¹) ⁻¹' {bpzGridIdx ((2 ^ k)⁻¹) x} ⊆
      Metric.closedBall x (4 * (2 ^ k)⁻¹) := by
  intro y hy
  set h : ℝ := (2 ^ k)⁻¹ with hhdef
  have hh : (0 : ℝ) < h := by positivity
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy
  rw [Metric.mem_closedBall, dist_eq_norm]
  set c := bpzGridCorner h (bpzGridIdx h x)
  have h1 := norm_sub_bpzGridCorner_le hh y
  have h2 : ‖x - c‖ ≤ 2 * h := norm_sub_bpzGridCorner_le hh x
  rw [hy] at h1
  calc ‖y - x‖ = ‖(y - c) - (x - c)‖ := by ring_nf
    _ ≤ ‖y - c‖ + ‖x - c‖ := norm_sub_le _ _
    _ ≤ 2 * h + 2 * h := add_le_add h1 h2
    _ = 4 * h := by ring

theorem le_bpzDyadicMass (k : ℕ) (m : Measure ℂ) (x : ℂ) : m {x} ≤ bpzDyadicMass k m x :=
  measure_mono (Set.singleton_subset_iff.mpr (by simp))

theorem iInter_closedBall_four_mul_inv_pow (x : ℂ) :
    ⋂ k : ℕ, Metric.closedBall x (4 * (2 ^ k)⁻¹ : ℝ) = {x} := by
  ext y
  simp only [Set.mem_iInter, Metric.mem_closedBall, Set.mem_singleton_iff]
  constructor
  · intro hy
    by_contra hne
    have hpos : 0 < dist y x := dist_pos.mpr hne
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < dist y x / 4 by positivity)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    have := hy k
    rw [one_div, inv_pow] at hk
    linarith
  · rintro rfl k
    rw [dist_self]
    positivity

/-- For a finite measure, the dyadic masses at a point decrease to the atom at the point. -/
theorem iInf_bpzDyadicMass_le (m : Measure ℂ) [IsFiniteMeasure m] (x : ℂ) :
    ⨅ k, bpzDyadicMass k m x ≤ m {x} := by
  have hanti : Antitone fun k : ℕ => Metric.closedBall x (4 * (2 ^ k)⁻¹ : ℝ) := by
    intro i j hij
    apply Metric.closedBall_subset_closedBall
    have : ((2 : ℝ) ^ j)⁻¹ ≤ ((2 : ℝ) ^ i)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hij)
    linarith
  calc ⨅ k, bpzDyadicMass k m x ≤ ⨅ k : ℕ, m (Metric.closedBall x (4 * (2 ^ k)⁻¹)) :=
        iInf_mono fun k => measure_mono (bpzDyadic_cell_subset_ball k x)
    _ = m (⋂ k : ℕ, Metric.closedBall x (4 * (2 ^ k)⁻¹)) :=
        (hanti.measure_iInter (fun _ => measurableSet_closedBall.nullMeasurableSet)
          ⟨0, measure_ne_top _ _⟩).symm
    _ = m {x} := by rw [iInter_closedBall_four_mul_inv_pow]

/-- A measure for which almost every point is not an atom has no atoms. -/
theorem measure_singleton_eq_zero_of_ae {μ : Measure ℂ} (h : ∀ᵐ u ∂μ, μ {u} = 0) (x : ℂ) :
    μ {x} = 0 := by
  rw [ae_iff] at h
  by_contra hx
  exact hx (le_antisymm ((measure_mono (Set.singleton_subset_iff.mpr hx)).trans h.le)
    zero_le)

/-- The chaos measure almost surely has no atoms. -/
theorem gmc_noAtoms_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) :
    ∀ᵐ ω ∂P, ∀ x, M ω {x} = 0 := by
  set g : Measure ℂ → ℂ → ℝ≥0∞ := fun m u => ⨅ k, bpzDyadicMass k m u with hg
  have hgm : Measurable (Function.uncurry g) :=
    Measurable.iInf fun k => measurable_bpzDyadicMass k
  set H : ℂ → (TestFn → ℝ) → Measure ℂ → ℝ≥0∞ := fun u _ m => g m u with hH
  have hHm : Measurable (fun q : ℂ × ((TestFn → ℝ) × Measure ℂ) => H q.1 q.2.1 q.2.2) :=
    hgm.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst)
  have hid := equatorGFF_rooted_GMC_identity P X hX γ hγ hγ2 M hM H hHm
  have hzero : ∀ u, ∫⁻ ω, H u (fun f => X ω f + γ * gffRootCovariance u f)
      (gmcRootedMeasure γ u (M ω)) ∂P = 0 := by
    intro u
    rw [lintegral_eq_zero_iff' ?_]
    · filter_upwards [equatorGFF_rooted_measure_finite P X hX γ hγ hγ2 M hM u,
        gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM u] with ω hfin h0
      have hroot0 : gmcRootedMeasure γ u (M ω) {u} = 0 :=
        withDensity_absolutelyContinuous _ _ h0
      exact le_antisymm ((iInf_bpzDyadicMass_le _ u).trans hroot0.le) zero_le
    · have hroot : Measurable fun ω => gmcRootedMeasure γ u (M ω) := by
        refine Measure.measurable_of_measurable_coe _ fun t ht => ?_
        have heq : (fun ω => gmcRootedMeasure γ u (M ω) t) = (fun m : Measure ℂ =>
            ∫⁻ y, t.indicator (fun x => ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel u x))) y
              ∂m) ∘ M := by
          funext ω
          simp [gmcRootedMeasure, withDensity_apply _ ht, lintegral_indicator ht]
        rw [heq]
        exact (Measure.measurable_lintegral ((measurable_gmcRootedDensity u).indicator ht)).comp
          hMm
      exact (hgm.comp (hroot.prodMk measurable_const)).aemeasurable
  have hlhs : ∫⁻ ω, ∫⁻ u, g (M ω) u ∂M ω ∂P = 0 := by
    have h := hid
    simp only [hH] at h hzero
    rw [h]
    simp [hzero]
  have hmeas : Measurable fun ω => ∫⁻ u, g (M ω) u ∂M ω :=
    (bpz_measurable_lintegral_finite_family M hMm hM.1 g hgm).comp
      (measurable_id.prodMk hMm)
  filter_upwards [(lintegral_eq_zero_iff hmeas).mp hlhs] with ω hω
  have hgω : g (M ω) =ᵐ[M ω] 0 :=
    (lintegral_eq_zero_iff (hgm.comp (measurable_const.prodMk measurable_id))).mp hω
  refine measure_singleton_eq_zero_of_ae ?_
  filter_upwards [hgω] with u hu
  exact le_antisymm ((le_iInf fun k => le_bpzDyadicMass k (M ω) u).trans hu.le) zero_le

end DOZZ.Proofs
