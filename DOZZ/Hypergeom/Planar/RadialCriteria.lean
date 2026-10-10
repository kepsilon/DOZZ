module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology

namespace DOZZ.Proofs

private theorem measurable_norm_rpow (s : ℝ) :
    Measurable (fun w : ℂ => ‖w‖ ^ s) := by
  have hrepr : (fun w : ℂ => ‖w‖ ^ s) =
    fun w => if ‖w‖ = 0 then 0 ^ s else Real.exp (s * Real.log ‖w‖) := by
    funext w
    by_cases hw : ‖w‖ = 0
    · simp [hw]
    · rw [ite_eq_right hw,
        Real.rpow_def_of_pos (lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw))]
      congr 1
      ring
  rw [hrepr]
  apply Measurable.ite
  · exact MeasurableSet.preimage (measurableSet_singleton (0 : ℝ)) (by fun_prop)
  · exact measurable_const
  · fun_prop

private theorem integrableOn_nonneg_iff_lintegral_lt_top {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} {f : α → ℝ}
    (hf : Measurable f) (hnonneg : 0 ≤ᵐ[μ.restrict s] f) :
    IntegrableOn f s μ ↔ (∫⁻ x in s, ENNReal.ofReal (f x) ∂μ) < ∞ := by
  change Integrable f (μ.restrict s) ↔ _
  rw [Integrable, hasFiniteIntegral_iff_ofReal (μ := μ.restrict s)
    hnonneg]
  simp only [hf.aestronglyMeasurable, true_and]

private theorem ofReal_mul_rpow (r s : ℝ) (hr : 0 < r) :
    ENNReal.ofReal r * ENNReal.ofReal (r ^ s) = ENNReal.ofReal (r ^ (s + 1)) := by
  calc
    ENNReal.ofReal r * ENNReal.ofReal (r ^ s) = ENNReal.ofReal (r * r ^ s) := by
      rw [← ENNReal.ofReal_mul (le_of_lt hr)]
    _ = ENNReal.ofReal (r ^ (1 + s)) := by
      congr 1
      calc
        r * r ^ s = r ^ 1 * r ^ s := by simp
        _ = r ^ (1 + s) := (Real.rpow_add hr 1 s).symm
    _ = ENNReal.ofReal (r ^ (s + 1)) := by
      congr 1
      congr 1
      ring

private def angularInterval : Set ℝ := Ioo (-Real.pi) Real.pi

private theorem angular_volume_pos : 0 < volume angularInterval := by
  rw [angularInterval, Real.volume_Ioo]
  apply ENNReal.ofReal_pos.mpr
  nlinarith [Real.pi_pos]

private theorem angular_volume_ne_top : volume angularInterval ≠ ∞ := by
  rw [angularInterval, Real.volume_Ioo]
  exact ENNReal.ofReal_ne_top

private def radialLocal (s R r : ℝ) : ℝ≥0∞ :=
  (Ioo (0 : ℝ) R).indicator (fun t : ℝ => ENNReal.ofReal (t ^ (s + 1))) r

private def radialTail (s R r : ℝ) : ℝ≥0∞ :=
  (Ici R).indicator (fun t : ℝ => ENNReal.ofReal (t ^ (s + 1))) r

private theorem lintegral_norm_rpow_ball_eq (s R : ℝ) :
    (∫⁻ w : ℂ in Metric.ball 0 R, ENNReal.ofReal (‖w‖ ^ s)) =
      (∫⁻ r : ℝ in Ioo 0 R, ENNReal.ofReal (r ^ (s + 1))) * volume angularInterval := by
  let F : ℂ → ℝ≥0∞ := fun w =>
    (Metric.ball 0 R).indicator (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ s)) w
  have hchange := Complex.lintegral_comp_polarCoord_symm F
  have hpolar :
      (∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal p.1 • F (Complex.polarCoord.symm p)) =
        ∫⁻ p : ℝ × ℝ in Set.Ioi 0 ×ˢ angularInterval, radialLocal s R p.1 := by
    rw [Complex.polarCoord_target, angularInterval]
    apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    change p.1 ∈ Ioi (0 : ℝ) ∧ p.2 ∈ Ioo (-Real.pi) Real.pi at hp
    have hr : 0 < p.1 := hp.1
    have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hr]
    have hball : Complex.polarCoord.symm p ∈ Metric.ball (0 : ℂ) R ↔ p.1 < R := by
      simp [Metric.mem_ball, dist_zero_right, abs_of_pos hr]
    by_cases hlt : p.1 < R
    · have hpow := ofReal_mul_rpow p.1 s hr
      dsimp [F, radialLocal]
      rw [Set.indicator_of_mem (s := Ioo (0 : ℝ) R) (show p.1 ∈ Ioo 0 R from ⟨hr, hlt⟩)]
      rw [Set.indicator_of_mem (hball.mpr hlt), hnorm]
      exact hpow
    · have hnotball : Complex.polarCoord.symm p ∉ Metric.ball (0 : ℂ) R :=
        fun hm => hlt (hball.mp hm)
      have hnotradial : p.1 ∉ Ioo (0 : ℝ) R := fun hm => hlt hm.2
      dsimp [F, radialLocal]
      rw [Set.indicator_of_notMem hnotball, Set.indicator_of_notMem hnotradial]
      simp

  have hconst (c : ℝ≥0∞) :
      (∫⁻ θ : ℝ in angularInterval, c) = c * volume angularInterval := by
    simp [lintegral_const, angularInterval, Measure.restrict_apply]
  have hradial :
      (∫⁻ r : ℝ in Ioi 0, radialLocal s R r) =
        ∫⁻ r : ℝ in Ioo 0 R, ENNReal.ofReal (r ^ (s + 1)) := by
    change (∫⁻ r : ℝ in Ioi 0,
      (Ioo (0 : ℝ) R).indicator (fun t : ℝ => ENNReal.ofReal (t ^ (s + 1))) r) = _
    rw [setLIntegral_indicator measurableSet_Ioo]
    have hset : Ioo (0 : ℝ) R ∩ Ioi 0 = Ioo 0 R := by
      ext r
      simp only [mem_inter_iff, mem_Ioo, mem_Ioi]
      constructor
      · rintro ⟨hr, _⟩
        exact hr
      · intro hr
        exact ⟨hr, hr.1⟩
    rw [hset]
  have hradialMeas : Measurable (radialLocal s R) := by
    change Measurable ((Ioo (0 : ℝ) R).indicator
      (fun t : ℝ => ENNReal.ofReal (t ^ (s + 1))))
    have hf : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ (s + 1))) := by fun_prop
    exact hf.indicator measurableSet_Ioo
  have hprodMeas : Measurable (fun p : ℝ × ℝ => radialLocal s R p.1) :=
    hradialMeas.comp measurable_fst
  have hprod :
      (∫⁻ p : ℝ × ℝ in Set.Ioi 0 ×ˢ angularInterval, radialLocal s R p.1) =
        (∫⁻ r : ℝ in Ioo 0 R, ENNReal.ofReal (r ^ (s + 1))) * volume angularInterval := by
    calc
      (∫⁻ p : ℝ × ℝ in Set.Ioi 0 ×ˢ angularInterval, radialLocal s R p.1) =
          ∫⁻ r : ℝ in Ioi 0, ∫⁻ θ : ℝ in angularInterval, radialLocal s R r := by
        rw [Measure.volume_eq_prod, setLIntegral_prod _ hprodMeas.aemeasurable]
      _ = ∫⁻ r : ℝ in Ioi 0, radialLocal s R r * volume angularInterval := by
        congr 1
        funext r
        exact hconst (radialLocal s R r)
      _ = (∫⁻ r : ℝ in Ioi 0, radialLocal s R r) * volume angularInterval := by
        rw [lintegral_mul_const' (volume angularInterval) _ angular_volume_ne_top]
      _ = (∫⁻ r : ℝ in Ioo 0 R, ENNReal.ofReal (r ^ (s + 1))) * volume angularInterval := by
        rw [hradial]
  calc
    _ = ∫⁻ w : ℂ, F w := by
      rw [← lintegral_indicator (Metric.isOpen_ball.measurableSet)]
    _ = ∫⁻ p in Complex.polarCoord.target,
          ENNReal.ofReal p.1 • F (Complex.polarCoord.symm p) := hchange.symm
    _ = ∫⁻ p : ℝ × ℝ in Set.Ioi 0 ×ˢ angularInterval, radialLocal s R p.1 := hpolar
    _ = _ := hprod

private theorem lintegral_norm_rpow_tail_eq (s R : ℝ) (hR : 0 < R) :
    (∫⁻ w : ℂ in (Metric.ball 0 R)ᶜ, ENNReal.ofReal (‖w‖ ^ s)) =
      (∫⁻ r : ℝ in Ici R, ENNReal.ofReal (r ^ (s + 1))) * volume angularInterval := by
  let F : ℂ → ℝ≥0∞ := fun w =>
    ((Metric.ball 0 R)ᶜ).indicator (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ s)) w
  have hchange := Complex.lintegral_comp_polarCoord_symm F
  have hpolar :
      (∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal p.1 • F (Complex.polarCoord.symm p)) =
        ∫⁻ p : ℝ × ℝ in Set.Ioi 0 ×ˢ angularInterval, radialTail s R p.1 := by
    rw [Complex.polarCoord_target, angularInterval]
    apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    change p.1 ∈ Ioi (0 : ℝ) ∧ p.2 ∈ Ioo (-Real.pi) Real.pi at hp
    have hr : 0 < p.1 := hp.1
    have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hr]
    have hball : Complex.polarCoord.symm p ∈ Metric.ball (0 : ℂ) R ↔ p.1 < R := by
      simp [Metric.mem_ball, dist_zero_right, abs_of_pos hr]
    by_cases hle : R ≤ p.1
    · have hpow := ofReal_mul_rpow p.1 s hr
      have hnotball : Complex.polarCoord.symm p ∉ Metric.ball (0 : ℂ) R :=
        fun hm => (not_lt_of_ge hle) (hball.mp hm)
      have hmemcomp : Complex.polarCoord.symm p ∈ (Metric.ball (0 : ℂ) R)ᶜ := by
        simpa using hnotball
      dsimp [F, radialTail]
      rw [Set.indicator_of_mem (s := Ici R) (show p.1 ∈ Ici R from hle)]
      rw [Set.indicator_of_mem hmemcomp, hnorm]
      exact hpow
    · have hlt : p.1 < R := lt_of_not_ge hle
      have hballMem : Complex.polarCoord.symm p ∈ Metric.ball (0 : ℂ) R := hball.mpr hlt
      have hnotradial : p.1 ∉ Ici R := hle
      have hnotcomp : Complex.polarCoord.symm p ∉ (Metric.ball (0 : ℂ) R)ᶜ := by
        simpa using hballMem
      dsimp [F, radialTail]
      rw [Set.indicator_of_notMem hnotcomp,
        Set.indicator_of_notMem hnotradial]
      simp
  have hconst (c : ℝ≥0∞) :
      (∫⁻ θ : ℝ in angularInterval, c) = c * volume angularInterval := by
    simp [lintegral_const, angularInterval, Measure.restrict_apply]
  have hradial :
      (∫⁻ r : ℝ in Ioi 0, radialTail s R r) =
        ∫⁻ r : ℝ in Ici R, ENNReal.ofReal (r ^ (s + 1)) := by
    change (∫⁻ r : ℝ in Ioi 0,
      (Ici R).indicator (fun t : ℝ => ENNReal.ofReal (t ^ (s + 1))) r) = _
    rw [setLIntegral_indicator measurableSet_Ici]
    have hset : Ici R ∩ Ioi (0 : ℝ) = Ici R := by
      ext r
      simp only [mem_inter_iff, mem_Ici, mem_Ioi]
      constructor
      · rintro ⟨hrR, _⟩
        exact hrR
      · intro hrR
        exact ⟨hrR, lt_of_lt_of_le hR hrR⟩
    rw [hset]
  have hradialMeas : Measurable (radialTail s R) := by
    change Measurable ((Ici R).indicator
      (fun t : ℝ => ENNReal.ofReal (t ^ (s + 1))))
    have hf : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ (s + 1))) := by fun_prop
    exact hf.indicator measurableSet_Ici
  have hprodMeas : Measurable (fun p : ℝ × ℝ => radialTail s R p.1) :=
    hradialMeas.comp measurable_fst
  have hprod :
      (∫⁻ p : ℝ × ℝ in Set.Ioi 0 ×ˢ angularInterval, radialTail s R p.1) =
        (∫⁻ r : ℝ in Ici R, ENNReal.ofReal (r ^ (s + 1))) * volume angularInterval := by
    calc
      (∫⁻ p : ℝ × ℝ in Set.Ioi 0 ×ˢ angularInterval, radialTail s R p.1) =
          ∫⁻ r : ℝ in Ioi 0, ∫⁻ θ : ℝ in angularInterval, radialTail s R r := by
        rw [Measure.volume_eq_prod, setLIntegral_prod _ hprodMeas.aemeasurable]
      _ = ∫⁻ r : ℝ in Ioi 0, radialTail s R r * volume angularInterval := by
        congr 1
        funext r
        exact hconst (radialTail s R r)
      _ = (∫⁻ r : ℝ in Ioi 0, radialTail s R r) * volume angularInterval := by
        rw [lintegral_mul_const' (volume angularInterval) _ angular_volume_ne_top]
      _ = (∫⁻ r : ℝ in Ici R, ENNReal.ofReal (r ^ (s + 1))) * volume angularInterval := by
        rw [hradial]
  calc
    _ = ∫⁻ w : ℂ, F w := by
      rw [← lintegral_indicator (MeasurableSet.compl Metric.isOpen_ball.measurableSet)]
    _ = ∫⁻ p in Complex.polarCoord.target,
          ENNReal.ofReal p.1 • F (Complex.polarCoord.symm p) := hchange.symm
    _ = ∫⁻ p : ℝ × ℝ in Set.Ioi 0 ×ˢ angularInterval, radialTail s R p.1 := hpolar
    _ = _ := hprod

private theorem radialLocal_finite_iff (s R : ℝ) (hR : 0 < R) :
    (∫⁻ r : ℝ in Ioo 0 R, ENNReal.ofReal (r ^ (s + 1))) < ∞ ↔ -2 < s := by
  have hmeas : Measurable (fun r : ℝ => r ^ (s + 1)) := by fun_prop
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) R)] (fun r : ℝ => r ^ (s + 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact Real.rpow_nonneg hr.1.le _
  rw [← integrableOn_nonneg_iff_lintegral_lt_top hmeas hnonneg,
    intervalIntegral.integrableOn_Ioo_rpow_iff hR]
  constructor <;> intro h <;> linarith

private theorem radialTail_finite_iff (s R : ℝ) (hR : 0 < R) :
    (∫⁻ r : ℝ in Ici R, ENNReal.ofReal (r ^ (s + 1))) < ∞ ↔ s < -2 := by
  have hmeas : Measurable (fun r : ℝ => r ^ (s + 1)) := by fun_prop
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ici R)] (fun r : ℝ => r ^ (s + 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with r hr
    exact Real.rpow_nonneg (le_trans hR.le hr) _
  rw [← integrableOn_nonneg_iff_lintegral_lt_top hmeas hnonneg,
    ← integrableOn_congr_set_ae (μ := volume) (Ioi_ae_eq_Ici (a := R)),
    integrableOn_Ioi_rpow_iff hR]
  constructor <;> intro h <;> linarith

theorem integrableOn_norm_rpow_ball_iff (s R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun w : ℂ => ‖w‖ ^ s) (Metric.ball 0 R) volume ↔ -2 < s := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Metric.ball (0 : ℂ) R)] (fun w : ℂ => ‖w‖ ^ s) := by
    filter_upwards with w
    exact Real.rpow_nonneg (norm_nonneg w) _
  rw [integrableOn_nonneg_iff_lintegral_lt_top (measurable_norm_rpow s) hnonneg,
    lintegral_norm_rpow_ball_eq s R]
  have hfactor (a : ℝ≥0∞) :
      a * volume angularInterval < ∞ ↔ a < ∞ := by
    rw [ENNReal.mul_lt_top_iff]
    constructor
    · rintro (⟨ha, _⟩ | ha0 | hC0)
      · exact ha
      · simp [ha0]
      · exact (angular_volume_pos.ne' hC0).elim
    · intro ha
      exact Or.inl ⟨ha, lt_top_iff_ne_top.mpr angular_volume_ne_top⟩
  exact (hfactor _).trans (radialLocal_finite_iff s R hR)

theorem integrableOn_norm_rpow_ball_compl_iff (s R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun w : ℂ => ‖w‖ ^ s) (Metric.ball 0 R)ᶜ volume ↔ s < -2 := by
  have hnonneg : 0 ≤ᵐ[volume.restrict ((Metric.ball (0 : ℂ) R)ᶜ)]
      (fun w : ℂ => ‖w‖ ^ s) := by
    filter_upwards with w
    exact Real.rpow_nonneg (norm_nonneg w) _
  rw [integrableOn_nonneg_iff_lintegral_lt_top (measurable_norm_rpow s) hnonneg,
    lintegral_norm_rpow_tail_eq s R hR]
  have hfactor (a : ℝ≥0∞) :
      a * volume angularInterval < ∞ ↔ a < ∞ := by
    rw [ENNReal.mul_lt_top_iff]
    constructor
    · rintro (⟨ha, _⟩ | ha0 | hC0)
      · exact ha
      · simp [ha0]
      · exact (angular_volume_pos.ne' hC0).elim
    · intro ha
      exact Or.inl ⟨ha, lt_top_iff_ne_top.mpr angular_volume_ne_top⟩
  exact (hfactor _).trans (radialTail_finite_iff s R hR)

end DOZZ.Proofs
