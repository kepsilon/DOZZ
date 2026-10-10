/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FieldChaosNegativePower
public import DOZZ.GMC.KahaneScheffe

/-! Spatial sampling of nonnegative integrable random fields converges in mean. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace DOZZ.Proofs

/-- Sampling one spatial coordinate preserves joint integrability. -/
theorem spatial_sample_integrable
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure S) [IsProbabilityMeasure ν] (f : Ω → S → ℝ)
    (hf : Integrable (fun p : Ω × S => f p.1 p.2) (P.prod ν)) (i : ℕ) :
    Integrable (fun p : Ω × (ℕ → S) => f p.1 (p.2 i))
      (P.prod (Measure.infinitePi (fun _ : ℕ => ν))) := by
  have heval : MeasurePreserving (fun q : ℕ → S => q i)
      (Measure.infinitePi (fun _ : ℕ => ν)) ν :=
    ⟨measurable_pi_apply i, Measure.infinitePi_map_eval (fun _ : ℕ => ν) i⟩
  exact ((MeasurePreserving.id P).prod heval).integrable_comp_of_integrable hf

/-- Every finite spatial sample average is integrable. -/
theorem spatial_empirical_average_integrable
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure S) [IsProbabilityMeasure ν] (f : Ω → S → ℝ)
    (hf : Integrable (fun p : Ω × S => f p.1 p.2) (P.prod ν)) (n : ℕ) :
    Integrable (fun p : Ω × (ℕ → S) =>
      (n : ℝ)⁻¹ * ∑ i : Fin n, f p.1 (p.2 i.val))
      (P.prod (Measure.infinitePi (fun _ : ℕ => ν))) :=
  (integrable_finsetSum Finset.univ (fun i _ =>
    spatial_sample_integrable P ν f hf i.val)).const_mul _

/-- Joint integrability upgrades the spatial strong law to convergence in mean on the product
of the field probability space and the independent spatial sampling space. -/
theorem spatial_empirical_average_L1
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure S) [IsProbabilityMeasure ν] (f : Ω → S → ℝ)
    (hjoint : Measurable (fun p : Ω × S => f p.1 p.2))
    (hf : Integrable (fun p : Ω × S => f p.1 p.2) (P.prod ν))
    (hnonneg : ∀ ω x, 0 ≤ f ω x) :
    let Q := Measure.infinitePi (fun _ : ℕ => ν)
    Tendsto (fun n : ℕ => ∫ p : Ω × (ℕ → S),
      |(n : ℝ)⁻¹ * ∑ i : Fin n, f p.1 (p.2 i.val) - ∫ x, f p.1 x ∂ν|
      ∂(P.prod Q)) atTop (𝓝 0) := by
  classical
  let Q := Measure.infinitePi (fun _ : ℕ => ν)
  let μ := P.prod Q
  let avg : ℕ → Ω × (ℕ → S) → ℝ :=
    fun n p => (n : ℝ)⁻¹ * ∑ i : Fin n, f p.1 (p.2 i.val)
  let g : Ω × (ℕ → S) → ℝ := fun p => ∫ x, f p.1 x ∂ν
  have heval (i : ℕ) : MeasurePreserving (fun q : ℕ → S => q i) Q ν :=
    ⟨measurable_pi_apply i, Measure.infinitePi_map_eval (fun _ : ℕ => ν) i⟩
  have hmap (i : ℕ) : MeasurePreserving
      (fun p : Ω × (ℕ → S) => (p.1, p.2 i)) μ (P.prod ν) :=
    (MeasurePreserving.id P).prod (heval i)
  have hterm (i : ℕ) : Integrable (fun p : Ω × (ℕ → S) => f p.1 (p.2 i)) μ :=
    (hmap i).integrable_comp_of_integrable hf
  have htermMean (i : ℕ) : (∫ p : Ω × (ℕ → S), f p.1 (p.2 i) ∂μ) =
      ∫ p : Ω × S, f p.1 p.2 ∂(P.prod ν) := by
    rw [← (hmap i).map_eq] at hf ⊢
    exact (integral_map (hmap i).measurable.aemeasurable hf.aestronglyMeasurable).symm
  have havg (n : ℕ) : Integrable (avg n) μ :=
    (integrable_finsetSum Finset.univ (fun i _ => hterm i.val)).const_mul _
  have hg : Integrable g μ := by
    change Integrable (fun p : Ω × (ℕ → S) => (∫ x, f p.1 x ∂ν)) (P.prod Q)
    exact hf.integral_prod_left.comp_fst Q
  have hgmean : (∫ p, g p ∂μ) = ∫ p : Ω × S, f p.1 p.2 ∂(P.prod ν) := by
    change (∫ p, g p ∂(P.prod Q)) = _
    rw [integral_prod g hg]
    simp only [g, integral_const, probReal_univ, one_smul]
    exact (integral_prod _ hf).symm
  have hmean : Tendsto (fun n => ∫ p, avg n p ∂μ) atTop (𝓝 (∫ p, g p ∂μ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    dsimp [avg]
    rw [integral_const_mul, integral_finsetSum _ (fun i _ => hterm i.val)]
    simp_rw [htermMean]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hn.ne'), one_mul, hgmean]
  have hlim : ∀ᵐ p ∂μ, Tendsto (fun n => avg n p) atTop (𝓝 (g p)) := by
    apply (Measure.ae_prod_iff_ae_ae ?_).2
    · exact ae_empirical_average_tendsto P ν f hjoint hf.prod_right_ae
    · apply measurableSet_tendsto_fun (l := atTop)
      · intro n
        exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
          hjoint.comp (measurable_fst.prodMk
            ((measurable_pi_apply i.val).comp measurable_snd)))
      · exact hjoint.stronglyMeasurable.integral_prod_right'.measurable.comp measurable_fst
  exact nonneg_integral_abs_sub_tendsto_zero μ avg g havg hg
    (fun n => ae_of_all _ fun p => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
      (Finset.sum_nonneg fun i _ => hnonneg _ _))
    (ae_of_all _ fun p => integral_nonneg fun x => hnonneg _ _) hlim hmean

end DOZZ.Proofs
