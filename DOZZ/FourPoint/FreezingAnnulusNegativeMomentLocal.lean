/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.RetainedAnnuliGeometry
public import DOZZ.GMC.BallAnnulus.Ball

/-! Local freezing from the separated retained-mass comparison and sharp ball moments. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- Localized freezing, with the constant uniform over centers in a compact set (used in
[KRV, §9.2]). It implies the unbounded form [KRV, (freezingannulus)]. -/
theorem freezing_annulus_negative_moment_local {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ α p R : ℝ) (K : Set ℂ) (hK : IsCompact K)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hX : IsEquatorGFF P X)
    (hGMC : IsGMCOf P X γ M) (hR : 0 < R)
    (hα : Q γ < α) (hp : 0 < p) (hthreshold : α - Q γ < γ * p) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ z ∈ K, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        (∫⁻ ω, ENNReal.rpow (freezingAnnulusMassLocal γ α (M ω) z ε R) (-p) ∂P) ≤
          ENNReal.ofReal (C * ε ^ ((α - Q γ) ^ 2 / 2)) := by
  have _hPositiveOrder := hp
  let a : ℝ := (α - Q γ) / γ
  let b : ℝ := p - a
  have ha : 0 < a := div_pos (sub_pos.mpr hα) hγ
  have hap : a < p := (div_lt_iff₀ hγ).mpr (by simpa only [mul_comm] using hthreshold)
  have hb : 0 < b := sub_pos.mpr hap
  have hab : a + b = p := by dsimp only [b]; ring
  have hQ : 0 < Q γ := by
    unfold Q
    exact add_pos (div_pos (by norm_num) hγ) (div_pos hγ (by norm_num))
  have hγα : 0 < γ * α := mul_pos hγ (hQ.trans hα)
  let t : ℝ := min (R / 2) (1 / 8)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have htR : t ≤ R / 2 := min_le_left _ _
  have ht8 : t ≤ 1 / 8 := min_le_right _ _
  obtain ⟨B, hB, hnorm⟩ := hK.isBounded.exists_pos_norm_le
  let L : ℝ := B + 1
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  let K' : Set ℂ := Metric.closedBall 0 L
  have hK' : IsCompact K' := isCompact_closedBall _ _
  have hbulk : 0 < 4 / γ ^ 2 := div_pos (by norm_num) (sq_pos_of_pos hγ)
  obtain ⟨Ca, hCa, hMa⟩ := equatorGFF_GMC_ball_moment_bound P X hX γ hγ hγ₂ M hGMC
    (-a) ((neg_nonpos.mpr ha.le).trans_lt hbulk) K' hK'
  obtain ⟨Cb, hCb, hMb⟩ := equatorGFF_GMC_ball_moment_bound P X hX γ hγ hγ₂ M hGMC
    (-b) ((neg_nonpos.mpr hb.le).trans_lt hbulk) K' hK'
  let ξa : ℝ := γ * Q γ * (-a) - γ ^ 2 * (-a) ^ 2 / 2
  let ξb : ℝ := γ * Q γ * (-b) - γ ^ 2 * (-b) ^ 2 / 2
  let k : ℝ := Real.exp (γ ^ 2 *
    max 0 (Real.log (1 / (t / 2)) + gmcCircleChartRemainder L) / 2 *
      ((a + b) ^ 2 + a + b))
  let C : ℝ := 4 ^ (γ * α * a) * (2 * t) ^ (γ * α * b) * k *
    Ca * (1 / 2 : ℝ) ^ ξa * Cb * (t / 8) ^ ξb
  have hk : 0 < k := Real.exp_pos _
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, t / 32, hC, by positivity, ?_⟩
  intro z hz ε hε hεt
  let u : ℂ := z + ((3 * ε : ℝ) : ℂ)
  let v : ℂ := z + (t : ℂ)
  have hε8 : ε / 2 ≤ 1 / 8 := by linarith only [hεt, ht8]
  have ht8' : t / 8 ≤ 1 / 8 := by linarith only [ht8]
  have hun : ‖u‖ ≤ B + 3 * ε := by
    have hh := norm_add_le z ((3 * ε : ℝ) : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hh
    exact hh.trans (add_le_add (hnorm z hz) le_rfl)
  have hvn : ‖v‖ ≤ B + t := by
    have hh := norm_add_le z (t : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.le] at hh
    exact hh.trans (add_le_add (hnorm z hz) le_rfl)
  have huL : ‖u‖ + ε / 2 ≤ L := by dsimp only [L]; linarith only [hun, hεt, ht8]
  have hvL : ‖v‖ + t / 8 ≤ L := by dsimp only [L]; linarith only [hvn, ht8]
  have huK : u ∈ K' := by
    change dist u 0 ≤ L
    rw [dist_zero_right]
    linarith only [huL, hε]
  have hvK : v ∈ K' := by
    change dist v 0 ≤ L
    rw [dist_zero_right]
    linarith only [hvL, ht]
  have hma := (hMa u huK (ε / 2) (by positivity) (by linarith only [hε8])).2
  have hmb := (hMb v hvK (t / 8) (by positivity) (by linarith only [ht8'])).2
  have hjoint := joint_retained_annuli_inverse_bound P X hX γ hγ hγ₂ M hGMC
    u v (ε / 2) (t / 8) L (t / 2) a b (by positivity) (by positivity) hε8 ht8'
    hL (by positivity) huL hvL (freezing_disk_separation z ε t hε hεt) ha.le hb.le
  have hlowerA (ω : Ω) : ENNReal.ofReal ((4 * ε) ^ (-(γ * α))) *
      M ω (Metric.ball u (ε / 2)) ≤ freezingAnnulusMassLocal γ α (M ω) z ε R := by
    apply freezing_retained_lower_bound
      γ α ε R ((4 * ε) ^ (-(γ * α))) (M ω) z u (ε / 2)
      (freezing_inner_disk z ε t R hε hεt htR)
    intro x hx
    obtain ⟨hl, hu⟩ := retained_disk_radial_bounds z (3 * ε) (ε / 2)
      (by positivity) x hx
    exact Real.rpow_le_rpow_of_nonpos (by linarith only [hl, hε])
      (by linarith only [hu, hε]) (neg_nonpos.mpr hγα.le)
  have hlowerB (ω : Ω) : ENNReal.ofReal ((2 * t) ^ (-(γ * α))) *
      M ω (Metric.ball v (t / 8)) ≤ freezingAnnulusMassLocal γ α (M ω) z ε R := by
    apply freezing_retained_lower_bound
      γ α ε R ((2 * t) ^ (-(γ * α))) (M ω) z v (t / 8)
      (freezing_outer_disk z ε t R hε hεt htR)
    intro x hx
    obtain ⟨hl, hu⟩ := retained_disk_radial_bounds z t (t / 8) ht.le x hx
    exact Real.rpow_le_rpow_of_nonpos (by linarith only [hl, ht])
      (by linarith only [hu, ht]) (neg_nonpos.mpr hγα.le)
  have hfinite (ω : Ω) (D : Set ℂ) : M ω D ≠ ⊤ := by
    let _ := hGMC.1 ω
    exact measure_ne_top _ _
  have halloc := retained_moment_allocation P
    (fun ω => freezingAnnulusMassLocal γ α (M ω) z ε R)
    (fun ω => M ω (Metric.ball u (ε / 2))) (fun ω => M ω (Metric.ball v (t / 8)))
    (fun ω => hfinite ω _) (fun ω => hfinite ω _)
    ((4 * ε) ^ (-(γ * α))) ((2 * t) ^ (-(γ * α))) a b
    (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos (by positivity) _)
    ha.le hb.le hlowerA hlowerB
  rw [hab] at halloc
  have horders : (-(γ * α)) * (-a) = γ * α * a := by ring
  have horders' : (-(γ * α)) * (-b) = γ * α * b := by ring
  rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity), horders, horders']
    at halloc
  have htotal := halloc.trans (mul_le_mul' le_rfl hjoint)
  have htotal' := htotal.trans (mul_le_mul' le_rfl
    (mul_le_mul' (mul_le_mul' le_rfl hma) hmb))
  have he : γ * α * a + ξa = (α - Q γ) ^ 2 / 2 := by
    dsimp only [ξa, a]
    field_simp
    ring
  have hscale :
      ((4 * ε) ^ (γ * α * a) * (2 * t) ^ (γ * α * b)) * k *
        (Ca * (ε / 2) ^ ξa) * (Cb * (t / 8) ^ ξb) =
      C * ε ^ ((α - Q γ) ^ 2 / 2) := by
    rw [show ε / 2 = ε * (1 / 2 : ℝ) by ring,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hε.le,
      Real.mul_rpow hε.le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [← he, Real.rpow_add hε]
    dsimp only [C]
    ring
  convert htotal' using 1
  change ENNReal.ofReal (C * ε ^ ((α - Q γ) ^ 2 / 2)) =
    ENNReal.ofReal ((4 * ε) ^ (γ * α * a) * (2 * t) ^ (γ * α * b)) *
      (ENNReal.ofReal k * ENNReal.ofReal (Ca * (ε / 2) ^ ξa) *
        ENNReal.ofReal (Cb * (t / 8) ^ ξb))
  simp only [← mul_assoc]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (4 * ε) ^ (γ * α * a) *
      (2 * t) ^ (γ * α * b)), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), hscale]

end DOZZ.Proofs
