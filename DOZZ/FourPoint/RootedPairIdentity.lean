/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.RootedIdentity
public import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-! Iterating the rooted identity `equatorGFF_rooted_GMC_identity` for a nonnegative two-mark
observable. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Finite-measure extension used only to make observables measurable on the entire Giry space. -/
noncomputable def finite_measure_part (μ : Measure ℂ) : Measure ℂ := by
  classical
  exact if IsFiniteMeasure μ then μ else 0

theorem finite_measure_part_measurable : Measurable finite_measure_part := by
  classical
  exact Measurable.ite FiniteMeasure.measurableSet_isFiniteMeasure measurable_id measurable_const

theorem finite_measure_part_finite (μ : Measure ℂ) :
    IsFiniteMeasure (finite_measure_part μ) := by
  classical
  by_cases hμ : IsFiniteMeasure μ
  · simpa only [finite_measure_part, ite_eq_left hμ] using hμ
  · simp only [finite_measure_part, ite_eq_right hμ]
    infer_instance

theorem finite_measure_part_eq (μ : Measure ℂ) (hμ : IsFiniteMeasure μ) :
    finite_measure_part μ = μ := by
  classical
  simp only [finite_measure_part, ite_eq_left hμ]

/-- Integrating the second mark is measurable on the finite-measure extension. -/
theorem finite_pair_integral_measurable
    (H : ℂ → ℂ → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : ℂ × (ℂ × Measure ℂ) => H q.1 q.2.1 q.2.2)) :
    Measurable (fun q : ℂ × Measure ℂ => ∫⁻ v,
      H q.1 v (finite_measure_part q.2) ∂finite_measure_part q.2) := by
  refine measurable_lintegral_finite_family
    (fun q : ℂ × Measure ℂ => finite_measure_part q.2)
    (finite_measure_part_measurable.comp measurable_snd)
    (fun q => finite_measure_part_finite q.2)
    (fun q : (ℂ × Measure ℂ) × ℂ => H q.1.1 q.2 (finite_measure_part q.1.2)) ?_
  exact hH.comp ((measurable_fst.comp measurable_fst).prodMk
    (measurable_snd.prodMk (finite_measure_part_measurable.comp
      (measurable_snd.comp measurable_fst))))

/-- The rooted finite-measure extension is measurable. -/
theorem finite_root_measurable (γ : ℝ) (u : ℂ) :
    Measurable (fun μ : Measure ℂ => gmcRootedMeasure γ u (finite_measure_part μ)) := by
  apply measurable_withDensity_finite_family finite_measure_part
    finite_measure_part_measurable finite_measure_part_finite
    (fun q : Measure ℂ × ℂ => ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel u q.2)))
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul (measurable_pointRootPotential.comp
      (measurable_const.prodMk measurable_snd))))

/-- The second rooted observable keeps the measurable Wick cross factor. -/
theorem rooted_pair_slice_measurable (γ : ℝ) (u : ℂ)
    (H : ℂ → ℂ → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : ℂ × (ℂ × Measure ℂ) => H q.1 q.2.1 q.2.2)) :
    Measurable (fun q : ℂ × Measure ℂ => ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel u q.1)) *
      H u q.1 (gmcRootedMeasure γ u (finite_measure_part q.2))) := by
  have hw : Measurable (fun v : ℂ => ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel u v))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (measurable_pointRootPotential.comp
        (measurable_const.prodMk measurable_id))))
  exact (hw.comp measurable_fst).mul
    (hH.comp (measurable_const.prodMk (measurable_fst.prodMk
      ((finite_root_measurable γ u).comp measurable_snd))))

/-- The two-root identity keeps the exact Wick cross factor and both insertions on the same
supplied GMC. No independence of the two rooted restrictions is asserted. -/
theorem rooted_pair_identity
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (H : ℂ → ℂ → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : ℂ × (ℂ × Measure ℂ) => H q.1 q.2.1 q.2.2)) :
    (∫⁻ ω, ∫⁻ u, ∫⁻ v, H u v (M ω) ∂M ω ∂M ω ∂P) =
      ∫⁻ u, ∫⁻ v, ∫⁻ ω, ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel u v)) *
        H u v (gmcRootedMeasure γ u (gmcRootedMeasure γ v (M ω))) ∂P
          ∂gmcReferenceMeasure ∂gmcReferenceMeasure := by
  let N : Measure ℂ → Measure ℂ := finite_measure_part
  have hN : Measurable N := finite_measure_part_measurable
  have hNfinite : ∀ μ, IsFiniteMeasure (N μ) := finite_measure_part_finite
  let F : ℂ × Measure ℂ → ℝ≥0∞ := fun q => ∫⁻ v, H q.1 v (N q.2) ∂N q.2
  have hF : Measurable F := finite_pair_integral_measurable H hH
  have hfirst := equatorGFF_rooted_GMC_identity P X hX γ hγ hγ2 M hM
    (fun u _ μ => F (u, μ)) (hF.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hMpart (ω : Ω) : N (M ω) = M ω := finite_measure_part_eq _ (hM.1 ω)
  have hleft : (∫⁻ ω, ∫⁻ u, ∫⁻ v, H u v (M ω) ∂M ω ∂M ω ∂P) =
      ∫⁻ ω, ∫⁻ u, F (u, M ω) ∂M ω ∂P := by
    apply lintegral_congr
    intro ω
    apply lintegral_congr
    intro u
    dsimp only [F]
    rw [hMpart]
  rw [hleft, hfirst]
  apply lintegral_congr
  intro u
  let w : ℂ → ℝ≥0∞ := fun v => ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel u v))
  have hw : Measurable w := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul (measurable_pointRootPotential.comp
      (measurable_const.prodMk measurable_id))))
  let J : ℂ × Measure ℂ → ℝ≥0∞ := fun q => w q.1 * H u q.1 (gmcRootedMeasure γ u (N q.2))
  have hJ : Measurable J := rooted_pair_slice_measurable γ u H hH
  have hsecond := equatorGFF_rooted_GMC_identity P X hX γ hγ hγ2 M hM
    (fun v _ μ => J (v, μ)) (hJ.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hexpand : (∫⁻ ω, F (u, gmcRootedMeasure γ u (M ω)) ∂P) =
      ∫⁻ ω, ∫⁻ v, J (v, M ω) ∂M ω ∂P := by
    apply lintegral_congr_ae
    filter_upwards [equatorGFF_rooted_measure_finite P X hX γ hγ hγ2 M hM u] with ω hfinite
    have hpart : N (gmcRootedMeasure γ u (M ω)) = gmcRootedMeasure γ u (M ω) :=
      finite_measure_part_eq _ hfinite
    dsimp only [F, J]
    rw [hpart, hMpart]
    have hh : Measurable (fun v => H u v (gmcRootedMeasure γ u (M ω))) :=
      hH.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
    exact lintegral_withDensity_eq_lintegral_mul (M ω) hw hh
  rw [hexpand, hsecond]
  apply lintegral_congr
  intro v
  apply lintegral_congr_ae
  filter_upwards [equatorGFF_rooted_measure_finite P X hX γ hγ hγ2 M hM v] with ω hfinite
  dsimp only [J, N]
  rw [finite_measure_part_eq _ hfinite]

end DOZZ.Proofs
