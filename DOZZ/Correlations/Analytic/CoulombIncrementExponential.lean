/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.CoulombNestedThreshold
public import DOZZ.Correlations.Analytic.NormalizedVertexHolomorphy
public import DOZZ.Correlations.Analytic.CoulombEnvelopeUniform
public import DOZZ.Correlations.Analytic.ThresholdFiniteConstants

/-! Uniform exponential decay of the actual complex Coulomb mass-power increment. -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- The spatial increment of the complex mass power decays exponentially, uniformly on a
bounded charge box satisfying strict positive-moment and root slack. Both signs of `Re p`
are allowed. -/
theorem coulomb_power_increment_exponential
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : Fin N → ℂ) (hz : Function.Injective z)
    (δ R Zs A a gap m g lo hi q b : ℝ)
    (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8) (hR : 1 ≤ R) (hZs : 0 ≤ Zs)
    (hsep : ∀ j k, j ≠ k → 2 * δ ≤ ‖z j - z k‖)
    (hzn : ∑ j, ‖z j‖ ≤ Zs) (hzR : ∀ i, 2 * ‖z i‖ ≤ R)
    (hgap : 0 < gap) (ha : a + gap < Q γ) (hm : 0 < m) (hm1 : m ≤ 1)
    (hms : m < min (4 / γ ^ 2) (2 / γ * (Q γ - (a + gap))))
    (hg : 0 < g) (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (hq : 1 < q)
    (hbulk : hi * q + g ≤ 4 / γ ^ 2)
    (hroot : hi * q + g ≤ 2 / γ * (Q γ - a)) :
    ∃ K κ : ℝ, 0 ≤ K ∧ 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (β : Fin (N + 1) → ℂ), (∀ i, |(β i).re| ≤ A) → (∀ i, (β i).re ≤ a) →
        lo ≤ (complexMomentPower γ β).re - 1 →
        (complexMomentPower γ β).re ≤ hi → ‖complexMomentPower γ β‖ ≤ b →
        (∫⁻ ω, ENNReal.ofReal
          ‖((∫⁻ x in retainedRegion z ((n + 1 : ℕ) : ℝ),
              coulombWeight γ (fun i => (β i.castSucc).re) z ((β (Fin.last N)).re) x ∂M ω).toReal : ℂ) ^
                complexMomentPower γ β -
            ((∫⁻ x in retainedRegion z (n : ℝ),
              coulombWeight γ (fun i => (β i.castSucc).re) z ((β (Fin.last N)).re) x ∂M ω).toReal : ℂ) ^
                complexMomentPower γ β‖ ∂P) ≤ ENNReal.ofReal (K * Real.exp (-κ * n)) := by
  classical
  let c := ENNReal.ofReal ((2 : ℝ) ^ (-(N * (γ * A)))) *
    ENNReal.ofReal ((R + 2) ^ (-(γ * A)))
  have hc : c ≠ 0 := mul_ne_zero
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)).ne'
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)).ne'
  have hc' : c ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hhiq : hi ≤ hi * q := by nlinarith
  obtain ⟨H₁, hH₁, henv₁⟩ := coulomb_envelope_uniform_moment
    P X hX γ hγ hγ2 M hM z hz δ R Zs A g hδ hδ8 hR hZs hg hsep hzn hzR
    (((R + 1 : ℝ)) : ℂ) c hc hc' lo hi 1 hlo hhi le_rfl
  obtain ⟨Hq, hHq, henvq⟩ := coulomb_envelope_uniform_moment
    P X hX γ hγ hγ2 M hM z hz δ R Zs A g hδ hδ8 hR hZs hg hsep hzn hzR
    (((R + 1 : ℝ)) : ℂ) c hc hc' lo hi q hlo hhi hq.le
  obtain ⟨C, hC, htail⟩ := complement_exponential_moment
    P X hX γ hγ hγ2 M hM z δ hδ (hδ8.trans (by norm_num))
      (fun k j h => hsep j k h) A a gap m hgap ha hm hm1 hms
  let D := ENNReal.ofReal (2 * b) * H₁
  let B := ((ENNReal.ofReal 2) ^ q * Hq) ^ (1 / q)
  have hD : D ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hH₁.ne
  have hB : B ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg
    (by positivity : 0 ≤ 1 / q)
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top) hHq.ne)
  obtain ⟨K, κ, hK, hκ, hdec⟩ := threshold_finite_constants
    D B C hD hB hC.ne (γ * gap * m) m q (by positivity) hm hq
  refine ⟨K, κ, hK, hκ, ?_⟩
  filter_upwards [htail, retained_cutoff_geometry_eventually z δ R hδ] with n hn hgeo
  intro β hβA hβa hβlo hβhi hβnorm
  let α := fun i : Fin N => (β i.castSucc).re
  let αinf := (β (Fin.last N)).re
  let p := complexMomentPower γ β
  let O₀ := retainedRegion z (n : ℝ)
  let O₁ := retainedRegion z ((n + 1 : ℕ) : ℝ)
  let H (ω : Ω) := ENNReal.ofReal
    ((c * M ω (Metric.ball (((R + 1 : ℝ)) : ℂ) (1 / 8))).toReal ^ lo +
      (coulombMass γ (M ω) α z αinf).toReal ^ hi)
  have hα : ∀ i, |α i| ≤ A := fun i => hβA i.castSucc
  have hinf : |αinf| ≤ A := hβA (Fin.last N)
  have haq : ∀ i, α i < Q γ := fun i => (hβa i.castSucc).trans_lt (by linarith)
  have hiq : αinf < Q γ := (hβa (Fin.last N)).trans_lt (by linarith)
  have hroots : ∀ i, hi * q + g ≤ 2 / γ * (Q γ - α i) := fun i =>
    hroot.trans (mul_le_mul_of_nonneg_left (by dsimp only [α]; linarith [hβa i.castSucc]) (by positivity))
  have hinfty : hi * q + g ≤ 2 / γ * (Q γ - αinf) :=
    hroot.trans (mul_le_mul_of_nonneg_left (by dsimp only [αinf]; linarith [hβa (Fin.last N)]) (by positivity))
  have henv1 : (∫⁻ ω, H ω ∂P) ≤ H₁ := by
    have he := henv₁ α αinf hα hinf haq hiq
      (by simpa only [mul_one] using (show hi + g ≤ 4 / γ ^ 2 from (by linarith)))
      (fun i => by simpa only [mul_one] using (show hi + g ≤ 2 / γ * (Q γ - α i) from (by linarith [hroots i])))
      (by simpa only [mul_one] using (show hi + g ≤ 2 / γ * (Q γ - αinf) from (by linarith [hinfty])))
    simpa only [ENNReal.rpow_one] using he
  have henvQ : (∫⁻ ω, H ω ^ q ∂P) ≤ Hq :=
    henvq α αinf hα hinf haq hiq hbulk hroots hinfty
  have hO : Metric.ball (((R + 1 : ℝ)) : ℂ) (1 / 8) ⊆ O₀ :=
    exterior_ball_subset_retainedRegion z R hR hzR (n : ℝ) (Nat.cast_nonneg _) hgeo.2.2.2
  have hsub : O₀ ⊆ O₁ := retainedRegion_mono z
    (by exact_mod_cast Nat.le_succ n)
  let u := Real.exp (-((γ * gap * m) / (2 * m)) * n)
  have hest := coulomb_nested_increment_threshold
    P X hX γ hγ hγ2 M hM α z hz αinf A hα hinf haq hiq O₀ O₁
    (retainedRegion_isOpen z _).measurableSet
    (retainedRegion_isOpen z _).measurableSet hsub R hR hzR hO lo hi p
    hlo hhi hβlo hβhi u m q (Real.exp_pos _) hm hq
  have hsmall : (∫⁻ ω, (ENNReal.ofReal
      (∫⁻ x in O₁ \ O₀, coulombWeight γ α z αinf x ∂M ω).toReal) ^ m ∂P) ≤
      ENNReal.ofReal (Real.exp (-(γ * gap * m) * n)) * C := by
    apply (lintegral_mono (fun ω => ENNReal.rpow_le_rpow
      ((ENNReal.ofReal_toReal_le).trans (lintegral_mono_set
        (show O₁ \ O₀ ⊆ O₀ᶜ from fun _ h => h.2))) hm.le)).trans
    exact hn α αinf hα hinf (fun i => hβa i.castSucc) (hβa (Fin.last N))
  calc
    _ ≤ ENNReal.ofReal u * ENNReal.ofReal (2 * ‖p‖) * (∫⁻ ω, H ω ∂P) +
        ((ENNReal.ofReal 2) ^ q * (∫⁻ ω, H ω ^ q ∂P)) ^ (1 / q) *
          ((∫⁻ ω, (ENNReal.ofReal
            (∫⁻ x in O₁ \ O₀, coulombWeight γ α z αinf x ∂M ω).toReal) ^ m ∂P) /
              (ENNReal.ofReal u) ^ m) ^ (1 / (q / (q - 1))) := hest
    _ ≤ ENNReal.ofReal u * D + B *
        ((ENNReal.ofReal (Real.exp (-(γ * gap * m) * n)) * C) /
          (ENNReal.ofReal u) ^ m) ^ (1 / (q / (q - 1))) := by
      apply add_le_add
      · have hc₁ := ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left hβnorm (by norm_num : (0 : ℝ) ≤ 2))
        exact (mul_le_mul' (mul_le_mul' le_rfl hc₁) henv1).trans_eq (mul_assoc _ _ _)
      · apply mul_le_mul'
        · exact ENNReal.rpow_le_rpow (mul_le_mul' le_rfl henvQ) (by positivity)
        · apply ENNReal.rpow_le_rpow _ (by positivity)
          exact ENNReal.div_le_div_right hsmall _
    _ ≤ _ := hdec (n : ℝ) (Nat.cast_nonneg _)

end DOZZ.Proofs
