/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Local integrability of the planar power kernel below its dimension threshold. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal Pointwise

namespace DOZZ.Proofs

/-- The planar Riesz kernel `‖z‖⁻ᵅ` is locally integrable when its exponent is strictly below
the real dimension two. -/
theorem complex_norm_neg_rpow_locallyIntegrable (α : ℝ) (hαpos : 0 < α) (hα : α < 2) :
    LocallyIntegrable (fun z : ℂ => ‖z‖ ^ (-α)) volume := by
  refine MeasureTheory.locallyIntegrable_of_norm_le_rpow (E := ℂ) (F := ℝ)
    (μ := volume) (C := 1) (α := α) ?_ ?_ ?_ ?_
  · rw [Complex.finrank_real_complex]
    norm_num
  · exact hα.trans_eq (by norm_num [Complex.finrank_real_complex])
  · filter_upwards [] with z
    calc
      ‖‖z‖ ^ (-α)‖ = ‖z‖ ^ (-α) :=
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)
      _ ≤ 1 * ‖z‖ ^ (-α) := by simp
  · have hα0 : 0 ≤ α := hαpos.le
    have hpow : Measurable (fun z : ℂ => ‖z‖ ^ α) :=
      (Real.continuous_rpow_const hα0).comp continuous_norm |>.measurable
    have hfun : (fun z : ℂ => ‖z‖ ^ (-α)) =
        fun z => (‖z‖ ^ α)⁻¹ := by
      funext z
      rw [Real.rpow_neg (norm_nonneg z)]
    rw [hfun]
    exact (measurable_inv.comp hpow).aestronglyMeasurable

/-- Translating the singularity to any fixed root preserves local integrability. -/
theorem complex_norm_sub_neg_rpow_locallyIntegrable (u : ℂ) (α : ℝ)
    (hαpos : 0 < α) (hα : α < 2) :
    LocallyIntegrable (fun z : ℂ => ‖z - u‖ ^ (-α)) volume := by
  let e : ℂ ≃ₜ ℂ :=
    { toFun := fun z => z - u
      invFun := fun z => z + u
      left_inv := fun z => by simp
      right_inv := fun z => by simp
      continuous_toFun := continuous_id.sub continuous_const
      continuous_invFun := continuous_id.add continuous_const }
  have hmap : volume.map e = volume := by
    change volume.map (fun z : ℂ => z + -u) = volume
    exact (MeasureTheory.measurePreserving_add_right volume (-u)).map_eq
  let f : ℂ → ℝ := fun z => ‖z‖ ^ (-α)
  have hbase := complex_norm_neg_rpow_locallyIntegrable α hαpos hα
  have hcomp : LocallyIntegrable (f ∘ e) volume := by
    have hbase' : LocallyIntegrable f (volume.map e) := by
      rw [hmap]
      simpa [f] using hbase
    exact (MeasureTheory.locallyIntegrable_map_homeomorph e).mp hbase'
  have hEq : (fun z : ℂ => ‖z - u‖ ^ (-α)) =
      f ∘ e := by
    funext z
    change ‖z - u‖ ^ (-α) = f (e z)
    rfl
  rw [hEq]
  exact hcomp

/-- The translated planar power kernel is integrable on every compact set. -/
theorem complex_norm_sub_neg_rpow_integrableOn_isCompact (K : Set ℂ) (hK : IsCompact K)
    (u : ℂ) (α : ℝ) (hαpos : 0 < α) (hα : α < 2) :
    IntegrableOn (fun z : ℂ => ‖z - u‖ ^ (-α)) K volume :=
  (complex_norm_sub_neg_rpow_locallyIntegrable u α hαpos hα).integrableOn_isCompact hK

/-- The local singularity has a uniform finite integral when its center ranges over a compact
set and the integration domain is compact. The bound comes from translating both compact sets
into one fixed ball around the origin. -/
theorem complex_norm_sub_neg_rpow_lintegral_uniform_compacts
    (K L : Set ℂ) (hK : IsCompact K) (hL : IsCompact L)
    (α : ℝ) (hαpos : 0 < α) (hα : α < 2) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ u ∈ K,
      ∫⁻ z in L, ENNReal.ofReal (‖z - u‖ ^ (-α)) ∂volume ≤ C := by
  obtain ⟨R₁, hR₁, hLnorm⟩ := hL.isBounded.exists_pos_norm_lt
  obtain ⟨R₂, hR₂, hKnorm⟩ := hK.isBounded.exists_pos_norm_lt
  let R : ℝ := R₁ + R₂
  have hR : 0 < R := by dsimp [R]; linarith
  let B : Set ℂ := Metric.closedBall 0 R
  let f : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z‖ ^ (-α))
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hbase := complex_norm_neg_rpow_locallyIntegrable α hαpos hα
  have hballReal : IntegrableOn (fun z : ℂ => ‖z‖ ^ (-α)) B volume :=
    hbase.integrableOn_isCompact (isCompact_closedBall 0 R)
  have hballNonneg : 0 ≤ᵐ[volume.restrict B] (fun z : ℂ => ‖z‖ ^ (-α)) :=
    ae_of_all _ (fun z => Real.rpow_nonneg (norm_nonneg _) _)
  let C : ℝ≥0∞ := ∫⁻ z in B, f z ∂volume
  have hC : C ≠ ∞ := by
    dsimp [C, f]
    rw [← ofReal_integral_eq_lintegral_ofReal hballReal hballNonneg]
    exact ENNReal.ofReal_ne_top
  refine ⟨C, hC, ?_⟩
  intro u hu
  let e : ℂ → ℂ := fun z => z + u
  have he : MeasurePreserving e volume volume :=
    MeasureTheory.measurePreserving_add_right volume u
  have hchange :
      ∫⁻ z in L, ENNReal.ofReal (‖z - u‖ ^ (-α)) ∂volume =
        ∫⁻ z in e ⁻¹' L, f z ∂volume := by
    calc
      _ = ∫⁻ z in L, ENNReal.ofReal (‖z - u‖ ^ (-α)) ∂volume.map e := by
            rw [he.map_eq]
      _ = ∫⁻ z in e ⁻¹' L,
            ENNReal.ofReal (‖(z + u) - u‖ ^ (-α)) ∂volume := by
              rw [setLIntegral_map hL.measurableSet (by fun_prop) he.measurable]
      _ = ∫⁻ z in e ⁻¹' L, f z ∂volume := by
            rw [setLIntegral_congr_fun (hL.measurableSet.preimage he.measurable)]
            intro z hz
            simp [f]
  have hsubset (z : ℂ) (hz : z ∈ e ⁻¹' L) : z ∈ B := by
    have hzu : z + u ∈ L := hz
    have hnorm : ‖z‖ = ‖(z + u) - u‖ := by rw [add_sub_cancel_right]
    have h1 := hLnorm (z + u) hzu
    have h2 := hKnorm u hu
    have hbound : ‖z‖ ≤ R₁ + R₂ := by
      rw [hnorm]
      apply le_of_lt
      calc
        ‖(z + u) - u‖ ≤ ‖z + u‖ + ‖u‖ := norm_sub_le _ _
        _ < R₁ + R₂ := add_lt_add h1 h2
    simpa [B, R, Metric.mem_closedBall, dist_zero_right] using hbound
  calc
    ∫⁻ z in L, ENNReal.ofReal (‖z - u‖ ^ (-α)) ∂volume =
        ∫⁻ z in e ⁻¹' L, f z ∂volume := hchange
    _ ≤ ∫⁻ z in B, f z ∂volume := lintegral_mono_set hsubset
    _ = C := rfl

/-- The planar pair kernel is integrable over a compact root set when its singularity exponent
is below the dimension. The uniform translated-kernel estimate reduces the product integral to
one finite local integral times the volume of the root set. -/
theorem complex_norm_pair_neg_rpow_lintegral_isCompact
    (K : Set ℂ) (hK : IsCompact K) (α : ℝ) (hαpos : 0 < α) (hα : α < 2) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∫⁻ p in K ×ˢ K,
        ENNReal.ofReal (‖p.1 - p.2‖ ^ (-α)) ∂(volume.prod volume) ≤ C := by
  obtain ⟨C, hC, huniform⟩ :=
    complex_norm_sub_neg_rpow_lintegral_uniform_compacts K K hK hK α hαpos hα
  let f : ℂ × ℂ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((‖p.1 - p.2‖ ^ α)⁻¹)
  have hnorm : Measurable (fun p : ℂ × ℂ => ‖p.1 - p.2‖) := by fun_prop
  have hpow : Measurable (fun p : ℂ × ℂ => ‖p.1 - p.2‖ ^ α) :=
    (Real.continuous_rpow_const hαpos.le).measurable.comp hnorm
  have hf : Measurable f := by
    dsimp [f]
    exact ENNReal.measurable_ofReal.comp (measurable_inv.comp hpow)
  have hpair :
      ∫⁻ p in K ×ˢ K, f p ∂(volume.prod volume) =
        ∫⁻ x in K, ∫⁻ y in K, f (x, y) ∂volume ∂volume :=
    setLIntegral_prod f hf.aemeasurable
  have hinner (x : ℂ) (hx : x ∈ K) :
      ∫⁻ y in K, f (x, y) ∂volume ≤ C := by
    have hfun : (fun y : ℂ => f (x, y)) =
        fun y => ENNReal.ofReal (‖y - x‖ ^ (-α)) := by
      funext y
      dsimp [f]
      rw [Real.rpow_neg (norm_nonneg (y - x)), norm_sub_rev]
    rw [hfun]
    exact huniform x hx
  have houter :
      ∫⁻ x in K, ∫⁻ y in K, f (x, y) ∂volume ∂volume ≤ C * volume K := by
    calc
      ∫⁻ x in K, ∫⁻ y in K, f (x, y) ∂volume ∂volume
          ≤ ∫⁻ x in K, C ∂volume :=
            setLIntegral_mono measurable_const (fun x hx => hinner x hx)
      _ = C * volume K := by simp [lintegral_const]
  have hkernel : (fun p : ℂ × ℂ => ENNReal.ofReal (‖p.1 - p.2‖ ^ (-α))) = f := by
    funext p
    dsimp [f]
    rw [Real.rpow_neg (norm_nonneg (p.1 - p.2))]
  refine ⟨C * volume K, ENNReal.mul_ne_top hC hK.measure_ne_top, ?_⟩
  rw [hkernel, hpair]
  exact houter

/-- Any pair kernel with an almost-everywhere power majorant has a finite root-space integral on
a compact planar chart. This packages the Tonelli-side deterministic step used after a good-barrier
estimate supplies the pointwise covariance-kernel bound. -/
theorem complex_norm_pair_power_majorant_lintegrableOn_isCompact
    (K : Set ℂ) (hK : IsCompact K) (α : ℝ) (hαpos : 0 < α) (hα : α < 2)
    (c : ℝ≥0∞) (hc : c ≠ ∞) (F : ℂ × ℂ → ℝ≥0∞)
    (hF : ∀ᵐ p : ℂ × ℂ ∂(volume.prod volume), p ∈ K ×ˢ K →
      F p ≤ c * ENNReal.ofReal (‖p.1 - p.2‖ ^ (-α))) :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧
      ∫⁻ p in K ×ˢ K, F p ∂(volume.prod volume) ≤ c * B := by
  obtain ⟨B, hB, hpair⟩ :=
    complex_norm_pair_neg_rpow_lintegral_isCompact K hK α hαpos hα
  have hset : MeasurableSet (K ×ˢ K) := hK.measurableSet.prod hK.measurableSet
  have hmono := setLIntegral_mono_ae' hset hF
  have hscale : c *
      (∫⁻ p in K ×ˢ K, ENNReal.ofReal (‖p.1 - p.2‖ ^ (-α))
        ∂(volume.prod volume)) ≤ c * B := by
    calc
      _ = (∫⁻ p in K ×ˢ K,
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-α)) ∂(volume.prod volume)) * c := by
            rw [mul_comm]
      _ ≤ B * c := mul_le_mul_left hpair c
      _ = c * B := mul_comm _ _
  refine ⟨B, hB, ?_⟩
  calc
    ∫⁻ p in K ×ˢ K, F p ∂(volume.prod volume) ≤
        ∫⁻ p in K ×ˢ K,
          c * ENNReal.ofReal (‖p.1 - p.2‖ ^ (-α)) ∂(volume.prod volume) := hmono
    _ = c * (∫⁻ p in K ×ˢ K,
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-α)) ∂(volume.prod volume)) := by
          rw [lintegral_const_mul' c _ hc]
    _ ≤ c * B := hscale


/-- The Riesz-kernel integral on a planar ball has its exact homogeneity exponent `2 - α`. -/
theorem complex_norm_neg_rpow_integral_ball_scaling
    (α r : ℝ) (hr : 0 < r) :
    ∫ z in Metric.ball (0 : ℂ) r, ‖z‖ ^ (-α) ∂volume =
      r ^ (2 - α) * ∫ z in Metric.ball (0 : ℂ) 1, ‖z‖ ^ (-α) ∂volume := by
  let f : ℂ → ℝ := fun z => ‖z‖ ^ (-α)
  have hscale := MeasureTheory.Measure.setIntegral_comp_smul_of_pos volume f
    (Metric.ball (0 : ℂ) 1) hr
  have hball : r • Metric.ball (0 : ℂ) 1 = Metric.ball (0 : ℂ) r := by
    rw [smul_ball hr.ne' (0 : ℂ) 1]
    simp [abs_of_pos hr]
  have hfun (z : ℂ) : f (r • z) = r ^ (-α) * f z := by
    dsimp [f]
    have hnorm : ‖(r : ℂ) * z‖ = r * ‖z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
    rw [hnorm, Real.mul_rpow hr.le (norm_nonneg z)]
  rw [hball] at hscale
  have hleft : (∫ z in Metric.ball (0 : ℂ) 1, f (r • z) ∂volume) =
      r ^ (-α) * ∫ z in Metric.ball (0 : ℂ) 1, f z ∂volume := by
    rw [setIntegral_congr_fun Metric.isOpen_ball.measurableSet (fun z hz => hfun z)]
    rw [integral_const_mul]
  rw [hleft] at hscale
  simp only [Complex.finrank_real_complex] at hscale
  dsimp [f] at hscale ⊢
  have hrpow : r ^ ((2 : ℝ) - α) = r ^ (2 : ℝ) * r ^ (-α) := by
    rw [show (2 : ℝ) - α = 2 + (-α) by ring, Real.rpow_add hr]
  have hscale' : r ^ (-α) * (∫ z in Metric.ball (0 : ℂ) 1, ‖z‖ ^ (-α) ∂volume) =
      (r ^ (2 : ℕ))⁻¹ * ∫ z in Metric.ball (0 : ℂ) r, ‖z‖ ^ (-α) ∂volume := by
    simpa [f, smul_eq_mul] using hscale
  have hscaled : ∫ z in Metric.ball (0 : ℂ) r, ‖z‖ ^ (-α) ∂volume =
      r ^ (2 : ℕ) * (r ^ (-α) *
        ∫ z in Metric.ball (0 : ℂ) 1, ‖z‖ ^ (-α) ∂volume) := by
    calc
      ∫ z in Metric.ball (0 : ℂ) r, ‖z‖ ^ (-α) ∂volume =
          r ^ (2 : ℕ) * ((r ^ (2 : ℕ))⁻¹ * ∫ z in Metric.ball (0 : ℂ) r,
            ‖z‖ ^ (-α) ∂volume) := by
              rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hr.ne'), one_mul]
      _ = r ^ (2 : ℕ) * (r ^ (-α) *
          ∫ z in Metric.ball (0 : ℂ) 1, ‖z‖ ^ (-α) ∂volume) := by rw [← hscale']
  have hpow2 : (r ^ (2 : ℕ) : ℝ) = r ^ (2 : ℝ) :=
    (Real.rpow_natCast r 2).symm
  calc
    ∫ z in Metric.ball (0 : ℂ) r, ‖z‖ ^ (-α) ∂volume =
        r ^ (2 : ℕ) * (r ^ (-α) *
          ∫ z in Metric.ball (0 : ℂ) 1, ‖z‖ ^ (-α) ∂volume) := hscaled
    _ = r ^ (2 : ℝ) * (r ^ (-α) *
        ∫ z in Metric.ball (0 : ℂ) 1, ‖z‖ ^ (-α) ∂volume) := by rw [hpow2]
    _ = r ^ (2 - α) * ∫ z in Metric.ball (0 : ℂ) 1, ‖z‖ ^ (-α) ∂volume := by
      rw [hrpow]
      ring

/-- Translation invariance transports the exact ball scaling formula to a ball about any root. -/
theorem complex_norm_sub_neg_rpow_integral_ball_scaling
    (u : ℂ) (α r : ℝ) (hr : 0 < r) :
    ∫ z in Metric.ball u r, ‖z - u‖ ^ (-α) ∂volume =
      r ^ (2 - α) * ∫ z in Metric.ball (0 : ℂ) 1, ‖z‖ ^ (-α) ∂volume := by
  let e : ℂ ≃ₜ ℂ :=
    { toFun := fun z => z + u
      invFun := fun z => z - u
      left_inv := fun z => by simp
      right_inv := fun z => by simp
      continuous_toFun := continuous_id.add continuous_const
      continuous_invFun := continuous_id.sub continuous_const }
  let f : ℂ → ℝ := fun z => ‖z - u‖ ^ (-α)
  have he : MeasurePreserving e volume volume := by
    change MeasurePreserving (fun z : ℂ => z + u) volume volume
    exact MeasureTheory.measurePreserving_add_right volume u
  have hpre : e ⁻¹' Metric.ball u r = Metric.ball (0 : ℂ) r := by
    ext z
    simp [e, Metric.mem_ball, dist_eq_norm]
  have hchange := he.setIntegral_preimage_emb e.measurableEmbedding f (Metric.ball u r)
  rw [hpre] at hchange
  have hfun : (fun z : ℂ => f (e z)) = fun z => ‖z‖ ^ (-α) := by
    funext z
    simp [f, e]
  rw [hfun] at hchange
  calc
    ∫ z in Metric.ball u r, ‖z - u‖ ^ (-α) ∂volume =
        ∫ z in Metric.ball (0 : ℂ) r, ‖z‖ ^ (-α) ∂volume := hchange.symm
    _ = r ^ (2 - α) * ∫ z in Metric.ball (0 : ℂ) 1, ‖z‖ ^ (-α) ∂volume :=
      complex_norm_neg_rpow_integral_ball_scaling α r hr

/-- Below dimension two, a translated Riesz kernel is integrable on every finite-radius ball. -/
theorem complex_norm_sub_neg_rpow_integrableOn_ball
    (u : ℂ) (α r : ℝ) (hα : 0 < α) (hα2 : α < 2) :
    IntegrableOn (fun z : ℂ => ‖z - u‖ ^ (-α)) (Metric.ball u r) volume := by
  have hclosed : IntegrableOn (fun z : ℂ => ‖z - u‖ ^ (-α))
      (Metric.closedBall u r) volume :=
    complex_norm_sub_neg_rpow_integrableOn_isCompact
      (Metric.closedBall u r) (isCompact_closedBall u r) u α hα hα2
  exact hclosed.mono_set Metric.ball_subset_closedBall


/-- Below the planar dimension threshold, the translated Riesz kernel is integrable on every
finite-radius ball. -/
theorem complex_norm_neg_rpow_integrableOn_ball
    (α r : ℝ) (hα : 0 < α) (hα2 : α < 2) :
    IntegrableOn (fun z : ℂ => ‖z‖ ^ (-α)) (Metric.ball 0 r) volume := by
  have hclosed : IntegrableOn (fun z : ℂ => ‖z - (0 : ℂ)‖ ^ (-α))
      (Metric.closedBall 0 r) volume :=
    complex_norm_sub_neg_rpow_integrableOn_isCompact
      (Metric.closedBall 0 r) (isCompact_closedBall 0 r) 0 α hα hα2
  simpa using hclosed.mono_set Metric.ball_subset_closedBall


end DOZZ.Proofs
