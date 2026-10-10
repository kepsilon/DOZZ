/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.TaylorSingular
public import DOZZ.FourPoint.Fusion.FullTimeSplit
public import DOZZ.FourPoint.TaylorOneRootIdentity
public import DOZZ.FourPoint.TaylorRegionCover
public import DOZZ.FourPoint.TwoRootedDomination

/-! # The one- and two-rooted Taylor terms as a Taylor remainder

For `0 < t ≤ 1/4`, the sum `r₁ + r₂ + r₃ + p₁ + p₂ + p₃` of the one-rooted and two-rooted
Taylor terms at `z = t` is the Taylor remainder `∫ u in 0..t, (t - u) * g2 u` of any function
`g2` that on `(0, t]` is the corresponding six-term expression (`bpz_rootedTerms_eq_integral`).

The proof substitutes `u = s t` in the Taylor remainder (`bpz_taylor_remainder_subst_complex`) and
integrates the six-term expression term by term in `s ∈ [0, 1]`. This needs the integrability of
the four weighted time integrands `s ↦ (1 - s) F (s t)`:

* The one-rooted integrands are handled by the local and exterior bounds of the fusion
  estimates (`bpzRR_oneRooted_pure_time_integrable`, `bpzRR_oneRooted_mixed_time_integrable`).
* The two-rooted integrands are dominated by the positive majorant
  `gammaHalfTwoRootedMajorant`. The Taylor fundamental estimate controls the majorant only
  below a small radius `r₀ ≤ 1/4`, which may be smaller than `t`; here the power bound
  `‖w‖ ^ (γ² / 2 - γ α₁)` is proved on the whole punctured quarter disk, from the exterior
  bound, the one-root rooting bound on the half-unit disk, and the explicit planar integral of
  the local kernel (`bpzRR_majorant_bound`). The exponent exceeds `-1`, which is all that
  integrability needs. The measurability of the two-rooted integrands in the moving root is
  proved as in the one-rooted case (`bpzRR_pair_measurable`). -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ComplexConjugate

namespace DOZZ.Proofs

/-! ### Conjugation and the integral -/

/-- Complex conjugation preserves integrability. -/
theorem bpzRR_integrable_star {μ : Measure ℝ} {f : ℝ → ℂ} (hf : Integrable f μ) :
    Integrable (fun x => star (f x)) μ :=
  hf.norm.mono' (continuous_star.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (ae_of_all _ fun x => by simp only [norm_star, le_refl])

/-- The integral commutes with complex conjugation. -/
theorem bpzRR_integral_star {μ : Measure ℝ} (f : ℝ → ℂ) :
    ∫ x, star (f x) ∂μ = star (∫ x, f x ∂μ) := integral_conj

/-- Conjugating a product with two real factors pulls the factors out. -/
theorem bpzRR_star_cast_mul (c T : ℝ) (I : ℂ) :
    star ((c : ℂ) * (T : ℂ) * I) = (T : ℂ) * star ((c : ℂ) * I) := by
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
  ring

/-! ### Measurability in the moving root -/

/-- The Coulomb expectation of a product of two spatial integrals is measurable in the moving
insertion point. -/
theorem bpzRR_pair_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ s : ℝ) (H₁ H₂ : ℂ × ℂ → ℂ) (hH₁ : Measurable H₁) (hH₂ : Measurable H₂) :
    Measurable (fun z : ℂ => ∫ ω,
      ((coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ s).toReal : ℂ) *
        (∫ x, H₁ (z, x) ∂M ω) * (∫ x, H₂ (z, x) ∂M ω) ∂P) := by
  let _ : IsProbabilityMeasure P := hX.1
  obtain ⟨N, hN, hfN, he⟩ := equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  let I := fun q : ℂ × Ω => ∫⁻ x, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ q.1 x) ∂N q.2
  have hp : Measurable (fun q : (ℂ × Ω) × ℂ => (q.1.1, q.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hIm : Measurable I := by
    apply measurable_lintegral_finite_family (fun q : ℂ × Ω => N q.2)
      (hN.comp measurable_snd) (fun q => hfN q.2)
      (fun q : (ℂ × Ω) × ℂ => ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ q.1.1 q.2))
    simpa only [Function.comp_def] using ENNReal.measurable_ofReal.comp
      ((fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃).comp hp)
  have hHm₁ : Measurable (fun q : ℂ × Ω => ∫ x, H₁ (q.1, x) ∂N q.2) := by
    apply fusion_measurable_integral_finite_family (fun q : ℂ × Ω => N q.2)
      (hN.comp measurable_snd) (fun q => hfN q.2) (fun q : (ℂ × Ω) × ℂ => H₁ (q.1.1, q.2))
    simpa only [Function.comp_def] using hH₁.comp hp
  have hHm₂ : Measurable (fun q : ℂ × Ω => ∫ x, H₂ (q.1, x) ∂N q.2) := by
    apply fusion_measurable_integral_finite_family (fun q : ℂ × Ω => N q.2)
      (hN.comp measurable_snd) (fun q => hfN q.2) (fun q : (ℂ × Ω) × ℂ => H₂ (q.1.1, q.2))
    simpa only [Function.comp_def] using hH₂.comp hp
  have hFn : Measurable (fun z : ℂ => ∫ ω, ((I (z, ω) ^ s).toReal : ℂ) *
      (∫ x, H₁ (z, x) ∂N ω) * (∫ x, H₂ (z, x) ∂N ω) ∂P) :=
    ((((Complex.measurable_ofReal.comp (hIm.pow_const s).ennreal_toReal).mul hHm₁).mul
      hHm₂).stronglyMeasurable.integral_prod_right').measurable
  have heq : (fun z : ℂ => ∫ ω,
      ((coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ s).toReal : ℂ) *
        (∫ x, H₁ (z, x) ∂M ω) * (∫ x, H₂ (z, x) ∂M ω) ∂P) =
      (fun z : ℂ => ∫ ω, ((I (z, ω) ^ s).toReal : ℂ) *
        (∫ x, H₁ (z, x) ∂N ω) * (∫ x, H₂ (z, x) ∂N ω) ∂P) := by
    funext z
    apply integral_congr_ae
    filter_upwards [he, gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM z,
      gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 0,
      gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 1] with ω hω hωz hω0 hω1
    dsimp only [I]
    rw [fusion_gammaHalfMass_kernel γ α₁ α₂ α₃ z (M ω) hωz hω0 hω1, hω]
  rw [heq]
  exact hFn

/-- The pure two-rooted expectation (the integrand of `p₁`) is measurable in the moving root. -/
theorem bpzRR_twoRooted_square_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p : ℝ) :
    Measurable (fun w : ℂ => ∫ ω, ((ENNReal.rpow
      (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![w, 0, 1] α₃) (-p - 2)).toReal : ℂ) *
        gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω w ^ 2 ∂P) := by
  have hH : Measurable (fun q : ℂ × ℂ =>
      (gammaHalfKernel γ α₁ α₂ α₃ q.1 q.2 : ℂ) / (q.2 - q.1)) :=
    (Complex.measurable_ofReal.comp (fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃)).div
      (measurable_snd.sub measurable_fst)
  have h := bpzRR_pair_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ (-p - 2) _ _ hH hH
  simpa only [gammaHalfRootKernelZ, pow_two, mul_assoc, ENNReal.rpow_eq_pow] using h

/-- The mixed two-rooted expectation (the integrand of `p₂`) is measurable in the moving root. -/
theorem bpzRR_twoRooted_mixed_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p : ℝ) :
    Measurable (fun w : ℂ => ∫ ω, ((ENNReal.rpow
      (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![w, 0, 1] α₃) (-p - 2)).toReal : ℂ) *
        gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω w * gammaHalfRootKernelBar M γ α₁ α₂ α₃ ω w ∂P) := by
  have hK : Measurable (fun q : ℂ × ℂ => (gammaHalfKernel γ α₁ α₂ α₃ q.1 q.2 : ℂ)) :=
    Complex.measurable_ofReal.comp (fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃)
  have hH₁ : Measurable (fun q : ℂ × ℂ =>
      (gammaHalfKernel γ α₁ α₂ α₃ q.1 q.2 : ℂ) / (q.2 - q.1)) :=
    hK.div (measurable_snd.sub measurable_fst)
  have hH₂ : Measurable (fun q : ℂ × ℂ =>
      (gammaHalfKernel γ α₁ α₂ α₃ q.1 q.2 : ℂ) / star (q.2 - q.1)) :=
    hK.div (continuous_star.measurable.comp (measurable_snd.sub measurable_fst))
  have h := bpzRR_pair_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ (-p - 2) _ _ hH₁ hH₂
  simpa only [gammaHalfRootKernelZ, gammaHalfRootKernelBar, ENNReal.rpow_eq_pow] using h

/-! ### The power bound for the two-rooted majorant on the quarter disk -/

/-- The local second-derivative kernel has Lebesgue integral on the half-unit disk bounded by the
scaling power `‖w‖ ^ (γ² / 2 - γ α₁)`, by the explicit planar (Riesz) integral. -/
theorem bpzRR_planar_ball_bound (γ α₁ α₂ α₃ : ℝ) (hγ : 0 < γ) (hlo : γ / 2 < α₁)
    (hα₁ : α₁ < 2 / γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, w ≠ 0 →
      ∫⁻ x in Metric.ball (0 : ℂ) (1 / 2),
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ w x / ‖x - w‖ ^ 2) ≤
        ENNReal.ofReal (C * ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁)) := by
  have hk : 0 < γ ^ 2 / 2 := by positivity
  have hβ : γ ^ 2 / 2 < γ * α₁ := by
    have h := mul_lt_mul_of_pos_left hlo hγ
    linarith only [h]
  have hβ2 : γ * α₁ < 2 := by
    have h := (lt_div_iff₀ hγ).mp hα₁
    linarith only [h]
  have heq : ∀ w : ℂ, (fun u : ℂ => planarMixedKernel (γ ^ 2 / 2) (γ * α₁) w u) =ᵐ[volume]
      (fun u => ‖u‖ ^ (-(γ * α₁)) * ‖u - w‖ ^ (γ ^ 2 / 2 - 2)) := by
    intro w
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with u hu
    change ‖u - w‖ ^ (γ ^ 2 / 2 - 2) / ‖u‖ ^ (γ * α₁) = _
    rw [div_eq_mul_inv, Real.rpow_neg (norm_nonneg u)]
    ring
  obtain ⟨Cr, hCr⟩ : ∃ Cr : ℝ, ∀ w : ℂ, w ≠ 0 →
      ∫ u : ℂ, planarMixedKernel (γ ^ 2 / 2) (γ * α₁) w u =
        Cr * ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁) :=
    ⟨_, fun w hw => (integral_congr_ae (heq w)).trans
      (positive_riesz_convolution_integral _ _ hk hβ hβ2 w hw)⟩
  refine ⟨2 ^ |γ * α₂| * |Cr| + 1, by positivity, ?_⟩
  intro w hw
  have hint := (planar_mixed_integral _ _ hk hβ hβ2 w hw).1
  have hnn : ∀ x, 0 ≤ planarMixedKernel (γ ^ 2 / 2) (γ * α₁) w x := fun x => by
    unfold planarMixedKernel
    positivity
  have hc0 : (0 : ℝ) ≤ 2 ^ |γ * α₂| := by positivity
  have hN : 0 ≤ ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁) := Real.rpow_nonneg (norm_nonneg _) _
  calc
    _ ≤ ∫⁻ x in Metric.ball (0 : ℂ) (1 / 2),
        ENNReal.ofReal (2 ^ |γ * α₂| * planarMixedKernel (γ ^ 2 / 2) (γ * α₁) w x) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_ball,
        ae_restrict_of_ae (Measure.ae_ne volume (0 : ℂ)),
        ae_restrict_of_ae (Measure.ae_ne volume w)] with x hx hx0 hxw
      exact ENNReal.ofReal_le_ofReal (fusion_localSecondKernel_bound γ α₁ α₂ α₃ w x
        (by simpa only [Metric.mem_ball, dist_zero_right] using hx) hx0 hxw)
    _ ≤ ∫⁻ x, ENNReal.ofReal (2 ^ |γ * α₂| * planarMixedKernel (γ ^ 2 / 2) (γ * α₁) w x) :=
      setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (∫ x, 2 ^ |γ * α₂| * planarMixedKernel (γ ^ 2 / 2) (γ * α₁) w x) :=
      (ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
        (ae_of_all _ fun x => mul_nonneg hc0 (hnn x))).symm
    _ = ENNReal.ofReal (2 ^ |γ * α₂| * (Cr * ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁))) := by
      rw [integral_const_mul, hCr w hw]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ = (2 ^ |γ * α₂| * Cr) * ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁) := by ring
        _ ≤ (2 ^ |γ * α₂| * |Cr|) * ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self Cr) hc0) hN
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only) hN

/-- The positive two-rooted majorant obeys the scaling power `‖w‖ ^ (γ² / 2 - γ α₁)` on the whole
punctured quarter disk, with a constant independent of `w`. The exterior region is bounded, and
the half-unit disk is bounded by the one-root rooting bound and the planar integral. -/
theorem bpzRR_majorant_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p : ℝ) (hlo : γ / 2 < α₁) (hα₁ : α₁ < 2 / γ) (hp : 0 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, w ≠ 0 → ‖w‖ ≤ 1 / 4 →
      gammaHalfTwoRootedMajorant P M γ α₁ α₂ α₃ p w ≤
        ENNReal.ofReal (C * ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁)) := by
  obtain ⟨Ce, hCe, hext⟩ := twoRooted_exterior_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p hp
  obtain ⟨C₀, hC₀, hsp⟩ := twoRooted_annular_spatial_bound P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ p hp
  obtain ⟨C₁, hC₁, hball⟩ := bpzRR_planar_ball_bound γ α₁ α₂ α₃ hγ hlo hα₁
  refine ⟨64 * (Ce + C₀ * C₁), by positivity, ?_⟩
  intro w hw hw4
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hexp : γ ^ 2 / 2 - γ * α₁ ≤ 0 := by
    have h := mul_lt_mul_of_pos_left hlo hγ
    linarith only [h]
  have hpow : 1 ≤ ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_ge hn (hw4.trans (by norm_num)) hexp
  let Y : ℝ := (Ce + C₀ * C₁) * ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁)
  have hY : 0 ≤ Y := by positivity
  have h0 : gammaHalfTwoRootedMajorantOn P M γ α₁ α₂ α₃ p w
      (Metric.ball (0 : ℂ) (1 / 2))ᶜ ≤ ENNReal.ofReal Y := by
    refine (hext w hw4).trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      Ce ≤ Ce * ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁) := le_mul_of_one_le_right hCe.le hpow
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [mul_pos hC₀ hC₁]) (by positivity)
  have h1 : gammaHalfTwoRootedMajorantOn P M γ α₁ α₂ α₃ p w
      (Metric.ball (0 : ℂ) (1 / 2)) ≤ ENNReal.ofReal Y := by
    refine (hsp w hw4 _ measurableSet_ball (fun x hx => ?_)).trans ?_
    · exact (show ‖x‖ < 1 / 2 by simpa only [Metric.mem_ball, dist_zero_right] using hx).le
    · calc
        _ ≤ ENNReal.ofReal C₀ * ENNReal.ofReal (C₁ * ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁)) :=
          mul_le_mul' le_rfl (hball w hw)
        _ = ENNReal.ofReal (C₀ * (C₁ * ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁))) :=
          (ENNReal.ofReal_mul hC₀.le).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal (by
          have hN : 0 ≤ ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁) := by positivity
          calc
            _ = (C₀ * C₁) * ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hCe]) hN)
  let B : Fin 4 → Set ℂ := ![(Metric.ball (0 : ℂ) (1 / 2))ᶜ, Metric.ball 0 (1 / 2),
    Metric.ball 0 (1 / 2), Metric.ball 0 (1 / 2)]
  have hB : ∀ i, MeasurableSet (B i) := by
    intro i
    fin_cases i
    · exact measurableSet_ball.compl
    · exact measurableSet_ball
    · exact measurableSet_ball
    · exact measurableSet_ball
  have hcover : ⋃ i, B i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    rw [Set.mem_iUnion]
    by_cases hx : x ∈ Metric.ball (0 : ℂ) (1 / 2)
    · exact ⟨1, hx⟩
    · exact ⟨0, hx⟩
  have hreg : ∀ i, gammaHalfTwoRootedMajorantOn P M γ α₁ α₂ α₃ p w (B i) ≤
      ENNReal.ofReal Y := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h1
    · exact h1
  calc
    _ ≤ 16 * ∑ i : Fin 4, gammaHalfTwoRootedMajorantOn P M γ α₁ α₂ α₃ p w (B i) :=
      twoRooted_region_cover P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p w B hB hcover
    _ ≤ 16 * ∑ i : Fin 4, ENNReal.ofReal Y :=
      mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => hreg i)
    _ = ENNReal.ofReal (64 * Y) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64), ← mul_assoc]
      norm_num
    _ = _ := by
      congr 1
      ring

/-! ### Integrability of the weighted time integrands -/

/-- The weighted time integrand of `p₁` is integrable on `[0, 1]` for a root `z` in the punctured
quarter disk. -/
theorem bpzRR_twoRooted_square_time_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p : ℝ) (hlo : γ / 2 < α₁) (hsq : 2 < γ ^ 2) (hα₁ : α₁ < 2 / γ) (hp : 0 ≤ p)
    (z : ℂ) (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4) :
    IntegrableOn (fun s : ℝ => ((1 - s : ℝ) : ℂ) * ∫ ω, ((ENNReal.rpow
      (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![(s : ℂ) * z, 0, 1] α₃) (-p - 2)).toReal : ℂ) *
        gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω ((s : ℂ) * z) ^ 2 ∂P) (Icc 0 1) volume := by
  obtain ⟨C, hC, hI⟩ := bpzRR_majorant_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p hlo hα₁ hp
  have he : -1 < γ ^ 2 / 2 - γ * α₁ := by
    have hd := fusion_taylor_parameters γ α₁ hγ hlo hsq hα₁
    linarith only [hd.2.2.2.1]
  refine fusion_time_integrable_of_power_bound _
    (bpzRR_twoRooted_square_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p) C
    (γ ^ 2 / 2 - γ * α₁) (1 / 4) he ?_ z hz hz4
  intro w hw hwr
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC.le (Real.rpow_nonneg (norm_nonneg _) _))).mp
  rw [ofReal_norm]
  exact (twoRooted_square_expectation_enorm_le P M γ α₁ α₂ α₃ p w).trans (hI w hw hwr)

/-- The weighted time integrand of `p₂` is integrable on `[0, 1]` for a root `z` in the punctured
quarter disk. -/
theorem bpzRR_twoRooted_mixed_time_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p : ℝ) (hlo : γ / 2 < α₁) (hsq : 2 < γ ^ 2) (hα₁ : α₁ < 2 / γ) (hp : 0 ≤ p)
    (z : ℂ) (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4) :
    IntegrableOn (fun s : ℝ => ((1 - s : ℝ) : ℂ) * ∫ ω, ((ENNReal.rpow
      (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![(s : ℂ) * z, 0, 1] α₃) (-p - 2)).toReal : ℂ) *
        gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω ((s : ℂ) * z) *
          gammaHalfRootKernelBar M γ α₁ α₂ α₃ ω ((s : ℂ) * z) ∂P) (Icc 0 1) volume := by
  obtain ⟨C, hC, hI⟩ := bpzRR_majorant_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p hlo hα₁ hp
  have he : -1 < γ ^ 2 / 2 - γ * α₁ := by
    have hd := fusion_taylor_parameters γ α₁ hγ hlo hsq hα₁
    linarith only [hd.2.2.2.1]
  refine fusion_time_integrable_of_power_bound _
    (bpzRR_twoRooted_mixed_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p) C
    (γ ^ 2 / 2 - γ * α₁) (1 / 4) he ?_ z hz hz4
  intro w hw hwr
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC.le (Real.rpow_nonneg (norm_nonneg _) _))).mp
  rw [ofReal_norm]
  exact (twoRooted_mixed_expectation_enorm_le P M γ α₁ α₂ α₃ p w).trans (hI w hw hwr)

/-- The weighted time integrand of `r₁` is integrable on `[0, 1]`: the local part has the power
bound `‖w‖ ^ (γ² / 2 - γ α₁)` and the exterior part is bounded. -/
theorem bpzRR_oneRooted_pure_time_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hlo : γ / 2 < α₁) (hsq : 2 < γ ^ 2) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (p : ℝ) (hp : 0 ≤ p)
    (z : ℂ) (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4) :
    IntegrableOn (fun s : ℝ => ((1 - s : ℝ) : ℂ) *
      fusionPureSpatial P M γ α₁ α₂ α₃ p univ ((s : ℂ) * z)) (Icc 0 1) volume := by
  let B := Metric.ball (0 : ℂ) (1 / 2)
  let F := fusionPureSpatial P M γ α₁ α₂ α₃ p univ
  let L := fusionPureSpatial P M γ α₁ α₂ α₃ p B
  let E := fusionPureSpatial P M γ α₁ α₂ α₃ p Bᶜ
  obtain ⟨CL, _, hbL⟩ := fusion_localR1_expectation_bound P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ hlo hα₁ hα₂ hα₃ p hp
  obtain ⟨CE, _, hbE⟩ := fusion_exteriorR1_expectation_bound P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ hα₁ hα₂ hα₃ p hp
  obtain ⟨-, hβ, -, hβe, -, -⟩ := fusion_taylor_parameters γ α₁ hγ hlo hsq hα₁
  have he : -1 < γ ^ 2 / 2 - γ * α₁ := by linarith only [hβe]
  have hLm := fusionPureSpatial_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p B
    Metric.isOpen_ball.measurableSet
  have hEm := fusionPureSpatial_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p Bᶜ
    Metric.isOpen_ball.measurableSet.compl
  have hL := fusion_time_integrable_of_power_bound L hLm CL (γ ^ 2 / 2 - γ * α₁) (1 / 4)
    he hbL z hz hz4
  have hE := fusion_time_integrable_of_power_bound E hEm CE 0 (1 / 4) (by norm_num)
    (fun w hw hw4 => by
      simpa only [E, B, fusionPureSpatial, Real.rpow_zero, mul_one] using (hbE w hw hw4).2)
    z hz hz4
  have hsplit : ∀ᵐ t : ℝ ∂volume.restrict (Icc 0 1),
      F ((t : ℂ) * z) = L ((t : ℂ) * z) + E ((t : ℂ) * z) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))] with t ht ht0
    have htz : (t : ℂ) * z ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr ht0) hz
    have htz4 : ‖(t : ℂ) * z‖ ≤ 1 / 4 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans hz4
    simpa only [F, L, E, fusionPureSpatial, Measure.restrict_univ] using
      fusion_pureSpatial_expectation_split P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hβ hα₁ hα₂ hα₃ p hp
        ((t : ℂ) * z) htz htz4
  refine (hL.add hE).congr ?_
  filter_upwards [hsplit] with t ht
  show ((1 - t : ℝ) : ℂ) * L ((t : ℂ) * z) + ((1 - t : ℝ) : ℂ) * E ((t : ℂ) * z) =
    ((1 - t : ℝ) : ℂ) * F ((t : ℂ) * z)
  rw [ht, mul_add]

/-- The weighted time integrand of `r₂` is integrable on `[0, 1]`: the local part has the power
bound `‖w‖ ^ (γ² / 2 - γ α₁)` and the exterior part is bounded. -/
theorem bpzRR_oneRooted_mixed_time_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hlo : γ / 2 < α₁) (hsq : 2 < γ ^ 2) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (p : ℝ) (hp : 0 ≤ p)
    (z : ℂ) (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4) :
    IntegrableOn (fun s : ℝ => ((1 - s : ℝ) : ℂ) *
      fusionMixedSpatial P M γ α₁ α₂ α₃ p univ ((s : ℂ) * z)) (Icc 0 1) volume := by
  let B := Metric.ball (0 : ℂ) (1 / 2)
  let F := fusionMixedSpatial P M γ α₁ α₂ α₃ p univ
  let L := fusionMixedSpatial P M γ α₁ α₂ α₃ p B
  let E := fusionMixedSpatial P M γ α₁ α₂ α₃ p Bᶜ
  obtain ⟨CL, _, hbL⟩ := fusion_localR2_expectation_bound P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ hlo hα₁ hα₂ hα₃ p hp
  obtain ⟨CE, _, hbE⟩ := fusion_exteriorR2_expectation_bound P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ hα₁ hα₂ hα₃ p hp
  obtain ⟨-, hβ, -, hβe, -, -⟩ := fusion_taylor_parameters γ α₁ hγ hlo hsq hα₁
  have he : -1 < γ ^ 2 / 2 - γ * α₁ := by linarith only [hβe]
  have hLm := fusionMixedSpatial_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p B
    Metric.isOpen_ball.measurableSet
  have hEm := fusionMixedSpatial_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p Bᶜ
    Metric.isOpen_ball.measurableSet.compl
  have hL := fusion_time_integrable_of_power_bound L hLm CL (γ ^ 2 / 2 - γ * α₁) (1 / 4)
    he hbL z hz hz4
  have hE := fusion_time_integrable_of_power_bound E hEm CE 0 (1 / 4) (by norm_num)
    (fun w hw hw4 => by
      simpa only [E, B, fusionMixedSpatial, Real.rpow_zero, mul_one] using (hbE w hw hw4).2)
    z hz hz4
  have hsplit : ∀ᵐ t : ℝ ∂volume.restrict (Icc 0 1),
      F ((t : ℂ) * z) = L ((t : ℂ) * z) + E ((t : ℂ) * z) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))] with t ht ht0
    have htz : (t : ℂ) * z ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr ht0) hz
    have htz4 : ‖(t : ℂ) * z‖ ≤ 1 / 4 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans hz4
    simpa only [F, L, E, fusionMixedSpatial, Measure.restrict_univ] using
      fusion_mixedSpatial_expectation_split P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hβ hα₁ hα₂ hα₃ p hp
        ((t : ℂ) * z) htz htz4
  refine (hL.add hE).congr ?_
  filter_upwards [hsplit] with t ht
  show ((1 - t : ℝ) : ℂ) * L ((t : ℂ) * z) + ((1 - t : ℝ) : ℂ) * E ((t : ℂ) * z) =
    ((1 - t : ℝ) : ℂ) * F ((t : ℂ) * z)
  rw [ht, mul_add]

/-! ### Assembling the remainder -/

/-- The term `r₁` as a weighted time integral of the unrestricted pure spatial expectation. -/
theorem bpzRR_R1_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ)
    (γ α₁ α₂ α₃ p : ℝ) (z : ℂ) :
    gammaHalfRootedR1 P M γ α₁ α₂ α₃ p z =
      ((-p * (γ ^ 2 / 4) * (γ ^ 2 / 4 - 1) : ℝ) : ℂ) * z ^ 2 *
        ∫ s in Icc (0 : ℝ) 1, ((1 - s : ℝ) : ℂ) *
          fusionPureSpatial P M γ α₁ α₂ α₃ p univ ((s : ℂ) * z) := by
  simp only [gammaHalfRootedR1, fusionPureSpatial, Measure.restrict_univ,
    ENNReal.rpow_eq_pow]

/-- The term `r₂` as a weighted time integral of the unrestricted mixed spatial expectation. -/
theorem bpzRR_R2_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ)
    (γ α₁ α₂ α₃ p : ℝ) (z : ℂ) :
    gammaHalfRootedR2 P M γ α₁ α₂ α₃ p z =
      ((-2 * p * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) * z * star z *
        ∫ s in Icc (0 : ℝ) 1, ((1 - s : ℝ) : ℂ) *
          fusionMixedSpatial P M γ α₁ α₂ α₃ p univ ((s : ℂ) * z) := by
  simp only [gammaHalfRootedR2, fusionMixedSpatial, Measure.restrict_univ,
    ENNReal.rpow_eq_pow, Complex.ofReal_pow]

/-- The four weighted time integrals combine linearly, including the conjugate terms. -/
theorem bpzRR_six_term_integral (a b c d : ℝ → ℂ) (c₁ c₂ d₁ d₂ : ℝ)
    (ha : IntegrableOn (fun s : ℝ => ((1 - s : ℝ) : ℂ) * a s) (Icc 0 1))
    (hb : IntegrableOn (fun s : ℝ => ((1 - s : ℝ) : ℂ) * b s) (Icc 0 1))
    (hc : IntegrableOn (fun s : ℝ => ((1 - s : ℝ) : ℂ) * c s) (Icc 0 1))
    (hd : IntegrableOn (fun s : ℝ => ((1 - s : ℝ) : ℂ) * d s) (Icc 0 1)) :
    (∫ s in Icc (0 : ℝ) 1, ((1 - s : ℝ) : ℂ) *
      ((c₁ : ℂ) * a s + (c₂ : ℂ) * b s + star ((c₁ : ℂ) * a s) +
        (d₁ : ℂ) * c s + (d₂ : ℂ) * d s + star ((d₁ : ℂ) * c s))) =
    (c₁ : ℂ) * (∫ s in Icc (0 : ℝ) 1, ((1 - s : ℝ) : ℂ) * a s) +
      (c₂ : ℂ) * (∫ s in Icc (0 : ℝ) 1, ((1 - s : ℝ) : ℂ) * b s) +
      star ((c₁ : ℂ) * ∫ s in Icc (0 : ℝ) 1, ((1 - s : ℝ) : ℂ) * a s) +
      (d₁ : ℂ) * (∫ s in Icc (0 : ℝ) 1, ((1 - s : ℝ) : ℂ) * c s) +
      (d₂ : ℂ) * (∫ s in Icc (0 : ℝ) 1, ((1 - s : ℝ) : ℂ) * d s) +
      star ((d₁ : ℂ) * ∫ s in Icc (0 : ℝ) 1, ((1 - s : ℝ) : ℂ) * c s) := by
  have hpt : ∀ s : ℝ, ((1 - s : ℝ) : ℂ) * ((c₁ : ℂ) * a s + (c₂ : ℂ) * b s +
      star ((c₁ : ℂ) * a s) + (d₁ : ℂ) * c s + (d₂ : ℂ) * d s + star ((d₁ : ℂ) * c s)) =
      (c₁ : ℂ) * (((1 - s : ℝ) : ℂ) * a s) + (c₂ : ℂ) * (((1 - s : ℝ) : ℂ) * b s) +
        star ((c₁ : ℂ) * (((1 - s : ℝ) : ℂ) * a s)) +
        (d₁ : ℂ) * (((1 - s : ℝ) : ℂ) * c s) + (d₂ : ℂ) * (((1 - s : ℝ) : ℂ) * d s) +
        star ((d₁ : ℂ) * (((1 - s : ℝ) : ℂ) * c s)) := by
    intro s
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
    ring
  simp_rw [hpt]
  have hA : Integrable (fun s : ℝ => (c₁ : ℂ) * (((1 - s : ℝ) : ℂ) * a s))
      (volume.restrict (Icc 0 1)) := ha.const_mul _
  have hB : Integrable (fun s : ℝ => (c₂ : ℂ) * (((1 - s : ℝ) : ℂ) * b s))
      (volume.restrict (Icc 0 1)) := hb.const_mul _
  have hC : Integrable (fun s : ℝ => (d₁ : ℂ) * (((1 - s : ℝ) : ℂ) * c s))
      (volume.restrict (Icc 0 1)) := hc.const_mul _
  have hD : Integrable (fun s : ℝ => (d₂ : ℂ) * (((1 - s : ℝ) : ℂ) * d s))
      (volume.restrict (Icc 0 1)) := hd.const_mul _
  have hAs := bpzRR_integrable_star hA
  have hCs := bpzRR_integrable_star hC
  have h2 : Integrable (fun s : ℝ => (c₁ : ℂ) * (((1 - s : ℝ) : ℂ) * a s) +
      (c₂ : ℂ) * (((1 - s : ℝ) : ℂ) * b s)) (volume.restrict (Icc 0 1)) := hA.add hB
  have h3 : Integrable (fun s : ℝ => (c₁ : ℂ) * (((1 - s : ℝ) : ℂ) * a s) +
      (c₂ : ℂ) * (((1 - s : ℝ) : ℂ) * b s) +
      star ((c₁ : ℂ) * (((1 - s : ℝ) : ℂ) * a s))) (volume.restrict (Icc 0 1)) := h2.add hAs
  have h4 : Integrable (fun s : ℝ => (c₁ : ℂ) * (((1 - s : ℝ) : ℂ) * a s) +
      (c₂ : ℂ) * (((1 - s : ℝ) : ℂ) * b s) +
      star ((c₁ : ℂ) * (((1 - s : ℝ) : ℂ) * a s)) +
      (d₁ : ℂ) * (((1 - s : ℝ) : ℂ) * c s)) (volume.restrict (Icc 0 1)) := h3.add hC
  have h5 : Integrable (fun s : ℝ => (c₁ : ℂ) * (((1 - s : ℝ) : ℂ) * a s) +
      (c₂ : ℂ) * (((1 - s : ℝ) : ℂ) * b s) +
      star ((c₁ : ℂ) * (((1 - s : ℝ) : ℂ) * a s)) +
      (d₁ : ℂ) * (((1 - s : ℝ) : ℂ) * c s) + (d₂ : ℂ) * (((1 - s : ℝ) : ℂ) * d s))
      (volume.restrict (Icc 0 1)) := h4.add hD
  rw [integral_add h5 hCs, integral_add h4 hD, integral_add h3 hC, integral_add h2 hAs,
    integral_add hA hB, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, bpzRR_integral_star (fun s => (c₁ : ℂ) * (((1 - s : ℝ) : ℂ) * a s)),
    bpzRR_integral_star (fun s => (d₁ : ℂ) * (((1 - s : ℝ) : ℂ) * c s)),
    integral_const_mul, integral_const_mul]

/-- The Taylor remainder at a real point `t > 0` is `t ^ 2` times the weighted time integral. -/
theorem bpzRR_remainder_eq {t : ℝ} (ht0 : 0 < t) (g2 : ℝ → ℝ) :
    ((∫ u in (0 : ℝ)..t, (t - u) * g2 u : ℝ) : ℂ) =
      ((t ^ 2 : ℝ) : ℂ) * ∫ s in Icc (0 : ℝ) 1, ((1 - s : ℝ) : ℂ) * (g2 (s * t) : ℂ) := by
  have h := bpz_taylor_remainder_subst_complex (f := fun u => (g2 u : ℂ)) ht0
  rw [← h, ← intervalIntegral.integral_ofReal]
  simp only [Complex.ofReal_mul]

/-- The one-rooted and two-rooted Taylor terms at a real point `t ∈ (0, 1/4]` add up to the
Taylor remainder `∫ u in 0..t, (t - u) * g2 u` of any function `g2` that on `(0, t]` equals the
six-term expression built from the four rooted expectations and their conjugates. -/
theorem bpz_rootedTerms_eq_integral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (α₁ α₂ α₃ : ℝ) (hlo : γ / 2 < α₁)
    (hsq : 2 < γ ^ 2) (hα₁ : α₁ < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {p : ℝ}
    (hp : 0 ≤ p) {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 4) {g2 : ℝ → ℝ}
    (hpt : ∀ u : ℝ, 0 < u → u ≤ t →
      (g2 u : ℂ) =
        ((-p * (γ ^ 2 / 4) * (γ ^ 2 / 4 - 1) : ℝ) : ℂ) *
            fusionPureSpatial P M γ α₁ α₂ α₃ p Set.univ (u : ℂ) +
          ((-2 * p * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) *
            fusionMixedSpatial P M γ α₁ α₂ α₃ p Set.univ (u : ℂ) +
          star (((-p * (γ ^ 2 / 4) * (γ ^ 2 / 4 - 1) : ℝ) : ℂ) *
            fusionPureSpatial P M γ α₁ α₂ α₃ p Set.univ (u : ℂ)) +
          ((p * (p + 1) * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) *
            (∫ ω, ((ENNReal.rpow (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![(u : ℂ), 0, 1] α₃)
              (-p - 2)).toReal : ℂ) * gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω (u : ℂ) ^ 2 ∂P) +
          ((2 * p * (p + 1) * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) *
            (∫ ω, ((ENNReal.rpow (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![(u : ℂ), 0, 1] α₃)
              (-p - 2)).toReal : ℂ) * gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω (u : ℂ) *
                gammaHalfRootKernelBar M γ α₁ α₂ α₃ ω (u : ℂ) ∂P) +
          star (((p * (p + 1) * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) *
            (∫ ω, ((ENNReal.rpow (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![(u : ℂ), 0, 1] α₃)
              (-p - 2)).toReal : ℂ) * gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω (u : ℂ) ^ 2 ∂P))) :
    gammaHalfOneRootedTerm P M γ α₁ α₂ α₃ p (t : ℂ) +
        gammaHalfTwoRootedTerm P M γ α₁ α₂ α₃ p (t : ℂ) =
      ((∫ u in (0 : ℝ)..t, (t - u) * g2 u : ℝ) : ℂ) := by
  have hz0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
  have hz4 : ‖(t : ℂ)‖ ≤ 1 / 4 := by
    rw [Complex.norm_real, Real.norm_of_nonneg ht0.le]
    exact ht
  have i1 := bpzRR_oneRooted_pure_time_integrable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hlo hsq hα₁
    hα₂ hα₃ p hp (t : ℂ) hz0 hz4
  have i2 := bpzRR_oneRooted_mixed_time_integrable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hlo hsq hα₁
    hα₂ hα₃ p hp (t : ℂ) hz0 hz4
  have i3 := bpzRR_twoRooted_square_time_integrable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p hlo hsq
    hα₁ hp (t : ℂ) hz0 hz4
  have i4 := bpzRR_twoRooted_mixed_time_integrable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p hlo hsq
    hα₁ hp (t : ℂ) hz0 hz4
  have hsix := bpzRR_six_term_integral
    (fun s => fusionPureSpatial P M γ α₁ α₂ α₃ p univ ((s : ℂ) * (t : ℂ)))
    (fun s => fusionMixedSpatial P M γ α₁ α₂ α₃ p univ ((s : ℂ) * (t : ℂ)))
    (fun s => ∫ ω, ((ENNReal.rpow
      (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![(s : ℂ) * (t : ℂ), 0, 1] α₃) (-p - 2)).toReal :
        ℂ) * gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω ((s : ℂ) * (t : ℂ)) ^ 2 ∂P)
    (fun s => ∫ ω, ((ENNReal.rpow
      (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![(s : ℂ) * (t : ℂ), 0, 1] α₃) (-p - 2)).toReal :
        ℂ) * gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω ((s : ℂ) * (t : ℂ)) *
          gammaHalfRootKernelBar M γ α₁ α₂ α₃ ω ((s : ℂ) * (t : ℂ)) ∂P)
    (-p * (γ ^ 2 / 4) * (γ ^ 2 / 4 - 1)) (-2 * p * (γ ^ 2 / 4) ^ 2)
    (p * (p + 1) * (γ ^ 2 / 4) ^ 2) (2 * p * (p + 1) * (γ ^ 2 / 4) ^ 2) i1 i2 i3 i4
  have hae : (∫ s in Icc (0 : ℝ) 1, ((1 - s : ℝ) : ℂ) * (g2 (s * t) : ℂ)) =
      ∫ s in Icc (0 : ℝ) 1, ((1 - s : ℝ) : ℂ) *
        (((-p * (γ ^ 2 / 4) * (γ ^ 2 / 4 - 1) : ℝ) : ℂ) *
            fusionPureSpatial P M γ α₁ α₂ α₃ p univ ((s : ℂ) * (t : ℂ)) +
          ((-2 * p * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) *
            fusionMixedSpatial P M γ α₁ α₂ α₃ p univ ((s : ℂ) * (t : ℂ)) +
          star (((-p * (γ ^ 2 / 4) * (γ ^ 2 / 4 - 1) : ℝ) : ℂ) *
            fusionPureSpatial P M γ α₁ α₂ α₃ p univ ((s : ℂ) * (t : ℂ))) +
          ((p * (p + 1) * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) *
            (∫ ω, ((ENNReal.rpow
              (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![(s : ℂ) * (t : ℂ), 0, 1] α₃)
              (-p - 2)).toReal : ℂ) *
                gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω ((s : ℂ) * (t : ℂ)) ^ 2 ∂P) +
          ((2 * p * (p + 1) * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) *
            (∫ ω, ((ENNReal.rpow
              (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![(s : ℂ) * (t : ℂ), 0, 1] α₃)
              (-p - 2)).toReal : ℂ) *
                gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω ((s : ℂ) * (t : ℂ)) *
                  gammaHalfRootKernelBar M γ α₁ α₂ α₃ ω ((s : ℂ) * (t : ℂ)) ∂P) +
          star (((p * (p + 1) * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) *
            (∫ ω, ((ENNReal.rpow
              (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![(s : ℂ) * (t : ℂ), 0, 1] α₃)
              (-p - 2)).toReal : ℂ) *
                gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω ((s : ℂ) * (t : ℂ)) ^ 2 ∂P))) := by
    apply setIntegral_congr_ae measurableSet_Icc
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with s hs0 hs
    have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have h := hpt (s * t) (mul_pos hspos ht0) (mul_le_of_le_one_left ht0.le hs.2)
    rw [show ((s * t : ℝ) : ℂ) = (s : ℂ) * (t : ℂ) from Complex.ofReal_mul s t] at h
    rw [h]
  have hT1 : (t : ℂ) ^ 2 = ((t ^ 2 : ℝ) : ℂ) := (Complex.ofReal_pow t 2).symm
  have hT2 : (t : ℂ) * star (t : ℂ) = ((t ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, sq]
  rw [bpzRR_remainder_eq ht0 g2, hae, hsix]
  simp only [gammaHalfOneRootedTerm, gammaHalfTwoRootedTerm, gammaHalfRootedR3,
    gammaHalfTwoRootedP3]
  rw [bpzRR_R1_eq, bpzRR_R2_eq]
  simp only [gammaHalfTwoRootedP1, gammaHalfTwoRootedP2]
  have hm : ∀ c I : ℂ, c * (t : ℂ) * star (t : ℂ) * I = c * ((t ^ 2 : ℝ) : ℂ) * I := by
    intro c I
    rw [mul_assoc c, hT2]
  rw [hm, hm, hT1, bpzRR_star_cast_mul, bpzRR_star_cast_mul]
  ring

end DOZZ.Proofs
