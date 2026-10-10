/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.CoulombIncrementExponential
public import DOZZ.Correlations.Analytic.NormalizedObservableIncrement
public import DOZZ.Correlations.Analytic.ImaginaryGrowth

/-! Summable actual analytic cutoff increments on thin complex polydiscs. -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- Uniform spatial moment slack gives exponentially decaying increments of the actual
holomorphic cutoff observables. The allowed imaginary width is positive and depends only on
the stated real charge box and moment margins. -/
theorem normalized_cutoff_exponential_polydisc
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (z : Fin N → ℂ) (hz : Function.Injective z)
    (δ R Zs A a gap m g lo hi q b : ℝ)
    (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8) (hR : 1 ≤ R) (hZs : 0 ≤ Zs)
    (hsep : ∀ j k, j ≠ k → 2 * δ ≤ ‖z j - z k‖)
    (hzn : ∑ j, ‖z j‖ ≤ Zs) (hzR : ∀ i, 2 * ‖z i‖ ≤ R)
    (hgap : 0 < gap) (ha : a + gap < Q γ) (hm : 0 < m) (hm1 : m ≤ 1)
    (hms : m < min (4 / γ ^ 2) (2 / γ * (Q γ - (a + gap))))
    (hg : 0 < g) (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (hq : 1 < q)
    (hbulk : hi * q + g ≤ 4 / γ ^ 2)
    (hroot : hi * q + g ≤ 2 / γ * (Q γ - a))
    (center radius : Fin (N + 1) → ℝ) (hradius : ∀ i, 0 < radius i)
    (hbox : ∀ β ∈ complexPolydisc (fun i => (center i : ℂ)) radius,
      (∀ i, |(β i).re| ≤ A) ∧ (∀ i, (β i).re ≤ a) ∧
        lo ≤ (complexMomentPower γ β).re - 1 ∧
        (complexMomentPower γ β).re ≤ hi ∧ ‖complexMomentPower γ β‖ ≤ b) :
    ∃ K κ d : ℝ, 0 ≤ K ∧ 0 < κ ∧ 0 < d ∧ ∀ᶠ n : ℕ in atTop,
      ∀ β ∈ complexPolydisc (fun i => (center i : ℂ)) radius,
        (∑ i, (β i).im ^ 2) ≤ d →
        ‖normalizedVertexMoment P Xc M (retainedRegion z ((n + 1 : ℕ) : ℝ))
            γ z ((n + 1 : ℕ) : ℝ) β -
          normalizedVertexMoment P Xc M (retainedRegion z (n : ℝ))
            γ z (n : ℝ) β‖ ≤ K * Real.exp (-κ * n) := by
  classical
  obtain ⟨K, κ, hK, hκ, hdec⟩ := coulomb_power_increment_exponential
    P X hX γ hγ hγ2 M hM z hz δ R Zs A a gap m g lo hi q b hδ hδ8 hR hZs hsep hzn hzR
      hgap ha hm hm1 hms hg hlo hhi hq hbulk hroot
  obtain ⟨E, hE, hgrowth⟩ := normalized_imaginary_growth P X Xc hX hc γ hγ.ne' z
  let d := κ / (2 * E)
  have hd : 0 < d := div_pos hκ (mul_pos (by norm_num) hE)
  have hEd : E * d = κ / 2 := by dsimp only [d]; field_simp
  have hbulkβ : ∀ β ∈ complexPolydisc (fun i => (center i : ℂ)) radius,
      (complexMomentPower γ β).re < 4 / γ ^ 2 := by
    intro β hβ
    have hb := (hbox β hβ).2.2.2.1
    have hhiq : hi ≤ hi * q := by nlinarith
    linarith
  refine ⟨K * Real.exp κ, κ / 2, d, by positivity, half_pos hκ, hd, ?_⟩
  filter_upwards [hdec, retained_cutoff_geometry_eventually z δ R hδ] with n hn hgeo
  intro β hβ him
  have hpars := hbox β hβ
  have hmass := hn β hpars.1 hpars.2.1 hpars.2.2.1 hpars.2.2.2.1 hpars.2.2.2.2
  have hr : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hrs : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  have hball := exterior_ball_subset_retainedRegion z R hR hzR (n : ℝ) hr hgeo.2.2.2
  have hne : (retainedRegion z (n : ℝ)).Nonempty :=
    (Metric.nonempty_ball.mpr (by norm_num : (0 : ℝ) < 1 / 8)).mono hball
  have hne' : (retainedRegion z ((n + 1 : ℕ) : ℝ)).Nonempty :=
    hne.mono (retainedRegion_mono z hrs)
  have hobs := normalized_cutoff_increment_norm_le
    P X hX γ hγ hγ2 M hM Xc hc z (n : ℝ) ((n + 1 : ℕ) : ℝ) hr hrs
    (retainedRegion z (n : ℝ)) (retainedRegion z ((n + 1 : ℕ) : ℝ))
    (retainedRegion_isOpen z _) (retainedRegion_isBounded z _) hne
    (retainedRegion_isOpen z _) (retainedRegion_isBounded z _) hne'
    Set.Subset.rfl Set.Subset.rfl center radius hradius hbulkβ β hβ
  have hdet := hgrowth ((n + 1 : ℕ) : ℝ) (Nat.cast_nonneg _) β
  have hdet' : (normalizedVertexPolynomial P Xc γ z ((n + 1 : ℕ) : ℝ) β).re +
        gaussianVariance P (fun ω => ∑ i, (β i).re * Xc ω (mixedVertexCenters z i)
          (mixedVertexTimes N ((n + 1 : ℕ) : ℝ) i)) / 2 +
        (γ * ∑ i, (β i.castSucc).re * equatorCircleMean (z i) ((n + 1 : ℕ) : ℝ)) *
          (complexMomentPower γ β).re ≤ E * ((n : ℝ) + 2) * ∑ i, (β i).im ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hdet
  have hthin : E * (∑ i, (β i).im ^ 2) ≤ κ / 2 := by
    exact (mul_le_mul_of_nonneg_left him hE.le).trans_eq hEd
  have he := imaginary_decay_absorption K E (∑ i, (β i).im ^ 2) κ (n : ℝ) hK hthin hr
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
  calc
    _ ≤ ENNReal.ofReal (Real.exp (E * ((n : ℝ) + 2) * ∑ i, (β i).im ^ 2)) *
        ENNReal.ofReal (K * Real.exp (-κ * n)) :=
      hobs.trans (mul_le_mul'
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hdet')) hmass)
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      exact ENNReal.ofReal_le_ofReal he

end DOZZ.Proofs
