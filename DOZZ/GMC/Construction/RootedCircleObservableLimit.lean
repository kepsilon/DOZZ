/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.GMC.Construction.RootedCircleCoordinateLimit
public import DOZZ.GMC.Construction.RootedMeasureKernel
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Convergence of bounded continuous marked observables under circle-root insertion. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped Distributions ENNReal BoundedContinuousFunction

namespace DOZZ.Proofs


/-- The circle-rooted marked expectation converges after integration against any finite root
measure for which the point insertion is almost surely finite. -/
theorem circleRooted_bounded_coordinate_lintegral_tendsto
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (hMmeas : Measurable M)
    (ν : Measure ℂ) [IsFiniteMeasure ν]
    (hRoot : ∀ᵐ u ∂ν, ∀ᵐ ω ∂P, IsFiniteMeasure (gmcRootedMeasure γ u (M ω)))
    (s : Finset gmcTiltCoordinateIndex)
    (φ : BoundedContinuousFunction (∀ _i : {i // i ∈ s}, ℝ) ℝ) :
    Tendsto (fun n : ℕ => ∫⁻ u, ∫⁻ ω, ENNReal.ofReal (φ (gmcTiltFiniteCoordinatePath s
      (fun f => X ω f + γ * circleCross u (n : ℝ) f)
      ((M ω).withDensity (fun x => ENNReal.ofReal
        (Real.exp (γ ^ 2 * ∫ v, gffKernel x v ∂circleMeasure u (n : ℝ))))))) ∂P ∂ν)
      atTop (𝓝 (∫⁻ u, ∫⁻ ω, ENNReal.ofReal (φ (gmcTiltFiniteCoordinatePath s
        (fun f => X ω f + γ * gffRootCovariance u f)
        (gmcRootedMeasure γ u (M ω)))) ∂P ∂ν)) := by
  let _ := hX.1
  let F : ℕ → ℂ × Ω → ℝ≥0∞ := fun n q => ENNReal.ofReal (φ (gmcTiltFiniteCoordinatePath s
    (fun f => X q.2 f + γ * circleCross q.1 (n : ℝ) f)
    ((M q.2).withDensity (fun x => ENNReal.ofReal
      (Real.exp (γ ^ 2 * ∫ v, gffKernel x v ∂circleMeasure q.1 (n : ℝ)))))))
  let G : ℂ × Ω → ℝ≥0∞ := fun q => ENNReal.ofReal (φ (gmcTiltFiniteCoordinatePath s
    (fun f => X q.2 f + γ * gffRootCovariance q.1 f)
    (gmcRootedMeasure γ q.1 (M q.2))))
  have hF (n : ℕ) : Measurable (F n) := by
    have hfield : Measurable (fun q : ℂ × Ω =>
        fun f => X q.2 f + γ * circleCross q.1 (n : ℝ) f) := by
      rw [measurable_pi_iff]
      intro f
      exact ((hX.2 f).1.comp measurable_snd).add
        (measurable_const.mul ((measurable_circleCross_center (n : ℝ) f).comp measurable_fst))
    exact ENNReal.measurable_ofReal.comp (φ.continuous.measurable.comp ((measurable_gmcTiltFiniteCoordinatePath s).comp
      (hfield.prodMk (measurable_circleRootedMeasure_family M hMmeas hM.1 γ (n : ℝ)))))
  have hbound (n : ℕ) (q : ℂ × Ω) : F n q ≤ ENNReal.ofReal ‖φ‖ := by
    apply ENNReal.ofReal_le_ofReal
    exact (le_abs_self _).trans (φ.norm_coe_le_norm _)
  have hlim : ∀ᵐ u ∂ν, Tendsto (fun n => ∫⁻ ω, F n (u, ω) ∂P) atTop
      (𝓝 (∫⁻ ω, G (u, ω) ∂P)) := by
    filter_upwards [hRoot] with u hu
    apply tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal ‖φ‖)
    · intro n
      exact (hF n).comp (measurable_const.prodMk measurable_id)
    · intro n
      exact ae_of_all _ fun ω => hbound n (u, ω)
    · simp
    · filter_upwards [ae_circleRootedCoordinatePath_tendsto P X hX γ hγ hγ2 M hM u hu]
        with ω hω
      apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      apply φ.continuous.continuousAt.tendsto.comp
      apply tendsto_pi_nhds.mpr
      intro i
      exact (tendsto_pi_nhds.mp hω) i.1
  apply tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal ‖φ‖)
  · intro n
    exact (hF n).lintegral_prod_right'
  · intro n
    exact ae_of_all _ fun u => by
      calc
        (∫⁻ ω, F n (u, ω) ∂P) ≤ ∫⁻ _ω, ENNReal.ofReal ‖φ‖ ∂P :=
          lintegral_mono fun ω => hbound n (u, ω)
        _ = _ := by simp
  · simp only [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν Set.univ)
  · exact hlim

end DOZZ.Proofs
