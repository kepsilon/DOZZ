/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsAdmissibleLogRegularization
public import DOZZ.GMC.Moments.InversionReference
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! Covariance comparison and admissibility for the pulled-back inversion cutoff. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

def inversionChart : Set ℂ := {0}ᶜ

/-- The usual inversion map as an open partial homeomorphism of the punctured plane. -/
noncomputable def complexInvOpenPartialHomeomorph : OpenPartialHomeomorph ℂ ℂ where
  toFun := fun z => z⁻¹
  invFun := fun z => z⁻¹
  source := inversionChart
  target := inversionChart
  map_source' := by
    intro z hz
    exact inv_ne_zero hz
  map_target' := by
    intro z hz
    exact inv_ne_zero hz
  left_inv' := by
    intro z hz
    exact inv_inv z
  right_inv' := by
    intro z hz
    exact inv_inv z
  continuousOn_toFun := by
    simpa [inversionChart] using (continuousOn_inv₀ : ContinuousOn (fun z : ℂ => z⁻¹) {0}ᶜ)
  continuousOn_invFun := by
    simpa [inversionChart] using (continuousOn_inv₀ : ContinuousOn (fun z : ℂ => z⁻¹) {0}ᶜ)
  open_source := by exact isOpen_compl_singleton
  open_target := by exact isOpen_compl_singleton

@[simp] theorem complexInvOpenPartialHomeomorph_source :
    complexInvOpenPartialHomeomorph.source = inversionChart := rfl

@[simp] theorem complexInvOpenPartialHomeomorph_target :
    complexInvOpenPartialHomeomorph.target = inversionChart := rfl

/-- Dividing the distance scale by a positive factor changes its clipped logarithm by at most
the absolute logarithm of that factor. -/
theorem inversion_logmax_div_scale_bound {q t c : ℝ} (hq : 0 ≤ q) (ht : 0 < t) (hc : 0 < c) :
    |Real.log (max (q / c) t) - Real.log (max q t)| ≤ |Real.log c| := by
  let A := max (q / c) t
  let B := max q t
  let C := max q (t * c)
  have hB : 0 < B := lt_of_lt_of_le ht (le_max_right q t)
  have hC : 0 < C := lt_of_lt_of_le (mul_pos ht hc) (le_max_right q (t * c))
  have hAeq : A = C / c := by
    dsimp [A, B, C]
    by_cases h : q / c ≤ t
    · rw [max_eq_right h, max_eq_right ((div_le_iff₀ hc).mp h)]
      field_simp [hc.ne']
    · have h' : t ≤ q / c := le_of_not_ge h
      rw [max_eq_left h', max_eq_left ((le_div_iff₀ hc).mp h')]
  by_cases h1 : 1 ≤ c
  · have htc : t ≤ t * c := by nlinarith [mul_le_mul_of_nonneg_left h1 ht.le]
    have hBC : B ≤ C := max_le_max le_rfl htc
    have hBscale : B ≤ c * B := by nlinarith [mul_le_mul_of_nonneg_right h1 hB.le]
    have hCB : C ≤ c * B := by
      apply max_le
      · exact le_trans (le_max_left q t) hBscale
      · calc
          t * c = c * t := by ring
          _ ≤ c * B := mul_le_mul_of_nonneg_left (le_max_right q t) hc.le
    have hlogc : 0 ≤ Real.log c := by
      rw [← Real.log_one]
      exact Real.log_le_log (by norm_num) h1
    have hlogB_C : Real.log B ≤ Real.log C := Real.log_le_log hB hBC
    have hlogC_cB : Real.log C ≤ Real.log c + Real.log B := by
      rw [← Real.log_mul hc.ne' hB.ne']
      exact Real.log_le_log hC hCB
    have hdiff : 0 ≤ Real.log C - Real.log B ∧ Real.log C - Real.log B ≤ Real.log c := by
      constructor
      · linarith
      · linarith
    change |Real.log A - Real.log B| ≤ |Real.log c|
    rw [hAeq, Real.log_div hC.ne' hc.ne']
    have hfinal : |(Real.log C - Real.log B) - Real.log c| ≤ |Real.log c| := by
      rw [abs_of_nonneg hlogc, abs_le]
      constructor
      · linarith
      · linarith
    have harg : Real.log C - Real.log c - Real.log B =
        (Real.log C - Real.log B) - Real.log c := by ring
    rw [harg]
    exact hfinal
  · have hc1 : c ≤ 1 := le_of_not_ge h1
    have hCB : C ≤ B := max_le (le_max_left q t)
      (le_trans (mul_le_of_le_one_right ht.le hc1) (le_max_right q t))
    have hcB_C : c * B ≤ C := by
      change c * max q t ≤ max q (t * c)
      by_cases hqt : q ≤ t
      · rw [max_eq_right hqt]
        calc
          c * t = t * c := by ring
          _ ≤ max q (t * c) := le_max_right _ _
      · have htq : t ≤ q := le_of_not_ge hqt
        rw [max_eq_left htq]
        calc
          c * q ≤ q := by nlinarith [mul_le_mul_of_nonneg_right hc1 hq]
          _ ≤ max q (t * c) := le_max_left _ _
    have hlogc : Real.log c ≤ 0 := by
      rw [← Real.log_one]
      exact Real.log_le_log hc hc1
    have hlogC_B : Real.log C ≤ Real.log B := Real.log_le_log hC hCB
    have hlogcB_C : Real.log c + Real.log B ≤ Real.log C := by
      rw [← Real.log_mul hc.ne' hB.ne']
      exact Real.log_le_log (mul_pos hc hB) hcB_C
    have hdiff : Real.log c ≤ Real.log C - Real.log B ∧ Real.log C - Real.log B ≤ 0 := by
      constructor
      · linarith
      · linarith
    change |Real.log A - Real.log B| ≤ |Real.log c|
    rw [hAeq, Real.log_div hC.ne' hc.ne']
    have hfinal : |(Real.log C - Real.log B) - Real.log c| ≤ |Real.log c| := by
      rw [abs_of_nonpos hlogc, abs_le]
      constructor
      · linarith
      · linarith
    have harg : Real.log C - Real.log c - Real.log B =
        (Real.log C - Real.log B) - Real.log c := by ring
    rw [harg]
    exact hfinal

/-- The distance between inverted points has the exact product denominator, including the
coincident-point case. -/
theorem complexInv_distance_of_ne_zero {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖x⁻¹ - y⁻¹‖ = ‖x - y‖ / (‖x‖ * ‖y‖) := by
  have h : x⁻¹ - y⁻¹ = (y - x) / (x * y) := by field_simp [hx, hy]
  rw [h, norm_div, norm_mul, norm_sub_rev]

private theorem exists_abs_log_norm_bound {K : Set ℂ} (hK : IsCompact K)
    (hKsub : K ⊆ inversionChart) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, |Real.log ‖x‖| ≤ B := by
  by_cases hne : K.Nonempty
  · let f : ℂ → ℝ := fun x => |Real.log ‖x‖|
    have hf : ContinuousOn f K := by
      dsimp [f]
      apply ContinuousOn.abs
      apply Real.continuousOn_log.comp continuous_norm.continuousOn
      intro x hx
      exact norm_ne_zero_iff.mpr (hKsub hx)
    obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne hf
    refine ⟨f x, abs_nonneg _, ?_⟩
    intro y hy
    exact hmax hy
  · refine ⟨0, le_rfl, ?_⟩
    intro x hx
    exact (hne ⟨x, hx⟩).elim

/-- Pulling an admissible logarithmic cutoff family through inversion preserves admissibility on
the punctured chart. The regular part changes by the two logarithms of the chart coordinates. -/
theorem isAdmissibleLogRegularization_complexInv
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (dens : ℂ → ℝ) (ε₀ : ℝ) (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P inversionChart dens ε₀ Y) :
    IsAdmissibleLogRegularization P inversionChart dens ε₀
      (fun ω ε x => Y ω ε x⁻¹) := by
  classical
  let U := inversionChart
  let Z : Ω → ℝ → ℂ → ℝ := fun ω ε x => Y ω ε x⁻¹
  refine ⟨?_, hY.openChart, hY.densityContinuous, hY.densityPositive, hY.cutoffPositive,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ε
    exact (hY.measurableAtScale ε).comp (by
      exact measurable_fst.prodMk (measurable_snd.inv))
  · intro n q hq
    let q' : Fin n → ℝ × ℂ := fun i => ((q i).1, ((q i).2)⁻¹)
    have hq' : ∀ i, 0 < (q' i).1 ∧ (q' i).1 ≤ ε₀ := by simpa [q'] using hq
    have h := hY.gaussian n q' hq'
    simpa [Z, q'] using h
  · intro K hK hKU
    obtain ⟨B, hB, hBbound⟩ := exists_abs_log_norm_bound hK hKU
    let K' := (fun x : ℂ => x⁻¹) '' K
    have hK' : IsCompact K' := by
      apply hK.image_of_continuousOn
      exact continuousOn_inv₀.mono hKU
    have hK'sub : K' ⊆ U := by
      rintro z ⟨x, hx, rfl⟩
      exact inv_ne_zero (hKU hx)
    obtain ⟨C, hC, hCov⟩ := hY.covarianceBound K' hK' hK'sub
    refine ⟨C + 4 * B, by positivity, ?_⟩
    intro ε δ hε hε₀ hδ hδ₀ x hx y hy
    have hx0 : x ≠ 0 := hKU hx
    have hy0 : y ≠ 0 := hKU hy
    have hnormx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
    have hnormy : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy0
    have hc : 0 < ‖x‖ * ‖y‖ := mul_pos (norm_pos_iff.mpr hx0) (norm_pos_iff.mpr hy0)
    have hdist := complexInv_distance_of_ne_zero hx0 hy0
    have hsrc := hCov ε δ hε hε₀ hδ hδ₀ (x⁻¹) ⟨x, hx, rfl⟩ (y⁻¹) ⟨y, hy, rfl⟩
    let t := max ε δ
    have ht : 0 < t := lt_of_lt_of_le hε (le_max_left _ _)
    have hlog := inversion_logmax_div_scale_bound (q := ‖x - y‖) (t := t)
      (c := ‖x‖ * ‖y‖) (norm_nonneg _) ht hc
    have hlogc : |Real.log (‖x‖ * ‖y‖)| ≤ 2 * B := by
      rw [Real.log_mul hnormx hnormy]
      have hxB := hBbound x hx
      have hyB := hBbound y hy
      calc
        |Real.log ‖x‖ + Real.log ‖y‖| ≤
            |Real.log ‖x‖| + |Real.log ‖y‖| := abs_add_le _ _
        _ ≤ B + B := add_le_add hxB hyB
        _ = 2 * B := by ring
    have hkernel : |Real.log (1 / max ‖x⁻¹ - y⁻¹‖ t) -
        Real.log (1 / max ‖x - y‖ t)| ≤ 4 * B := by
      rw [hdist, one_div, one_div, Real.log_inv, Real.log_inv]
      have hcomp := inversion_logmax_div_scale_bound (q := ‖x - y‖) (t := t)
        (c := ‖x‖ * ‖y‖) (norm_nonneg _) ht hc
      have harg :
          -Real.log (max (‖x - y‖ / (‖x‖ * ‖y‖)) t) -
            -Real.log (max ‖x - y‖ t) =
          -(Real.log (max (‖x - y‖ / (‖x‖ * ‖y‖)) t) -
            Real.log (max ‖x - y‖ t)) := by ring
      rw [harg, abs_neg]
      exact le_trans hcomp (by nlinarith [hlogc])
    have hdecomp :
        (gaussianCovariance P (fun ω => Z ω ε x) (fun ω => Z ω δ y) -
          Real.log (1 / max ‖x - y‖ t)) =
        (gaussianCovariance P (fun ω => Y ω ε x⁻¹) (fun ω => Y ω δ y⁻¹) -
          Real.log (1 / max ‖x⁻¹ - y⁻¹‖ t)) +
          (Real.log (1 / max ‖x⁻¹ - y⁻¹‖ t) - Real.log (1 / max ‖x - y‖ t)) := by
      ring
    rw [show (fun ω => Z ω ε x) = (fun ω => Y ω ε x⁻¹) by rfl,
      show (fun ω => Z ω δ y) = (fun ω => Y ω δ y⁻¹) by rfl]
    rw [hdecomp]
    calc
      |(gaussianCovariance P (fun ω => Y ω ε x⁻¹) (fun ω => Y ω δ y⁻¹) -
          Real.log (1 / max ‖x⁻¹ - y⁻¹‖ t)) +
          (Real.log (1 / max ‖x⁻¹ - y⁻¹‖ t) - Real.log (1 / max ‖x - y‖ t))|
          ≤ |gaussianCovariance P (fun ω => Y ω ε x⁻¹) (fun ω => Y ω δ y⁻¹) -
              Real.log (1 / max ‖x⁻¹ - y⁻¹‖ t)| +
            |Real.log (1 / max ‖x⁻¹ - y⁻¹‖ t) - Real.log (1 / max ‖x - y‖ t)| :=
            abs_add_le _ _
      _ ≤ C + 4 * B := add_le_add hsrc hkernel
  · intro K hK hKU
    let K' := (fun x : ℂ => x⁻¹) '' K
    have hK' : IsCompact K' := hK.image_of_continuousOn (continuousOn_inv₀.mono hKU)
    have hK'sub : K' ⊆ U := by
      rintro z ⟨x, hx, rfl⟩
      exact inv_ne_zero (hKU hx)
    obtain ⟨C, hC, hvar⟩ := hY.coarseVarianceBound K' hK' hK'sub
    refine ⟨C, hC, ?_⟩
    intro k hk x hx
    exact hvar k hk x⁻¹ ⟨x, hx, rfl⟩
  · intro K hK hKU
    let K' := (fun x : ℂ => x⁻¹) '' K
    have hK' : IsCompact K' := hK.image_of_continuousOn (continuousOn_inv₀.mono hKU)
    have hK'sub : K' ⊆ U := by
      rintro z ⟨x, hx, rfl⟩
      exact inv_ne_zero (hKU hx)
    obtain ⟨C, hC, hvar⟩ := hY.coarseMixedBound K' hK' hK'sub
    refine ⟨C, hC, ?_⟩
    intro k hk ε hε hεk x hx
    exact hvar k hk ε hε hεk x⁻¹ ⟨x, hx, rfl⟩
  · obtain ⟨H, hHcont, hHlim⟩ := hY.offDiagonalLimit
    let H' : ℂ → ℂ → ℝ := fun x y => H x⁻¹ y⁻¹ + Real.log ‖x‖ + Real.log ‖y‖
    refine ⟨H', ?_, ?_⟩
    · have hlog : ContinuousOn (fun x : ℂ => Real.log ‖x‖) U := by
        apply Real.continuousOn_log.comp continuous_norm.continuousOn
        intro x hx
        exact norm_ne_zero_iff.mpr hx
      have hinvCont : ContinuousOn (fun x : ℂ => x⁻¹) U := continuousOn_inv₀
      have hpair : ContinuousOn (fun p : ℂ × ℂ => (p.1⁻¹, p.2⁻¹)) (U ×ˢ U) := by
        apply ContinuousOn.prodMk
        · exact hinvCont.comp continuous_fst.continuousOn (by intro p hp; exact hp.1)
        · exact hinvCont.comp continuous_snd.continuousOn (by intro p hp; exact hp.2)
      have hcomp : ContinuousOn (fun p : ℂ × ℂ => H p.1⁻¹ p.2⁻¹) (U ×ˢ U) := by
        apply hHcont.comp hpair
        intro p hp
        exact ⟨inv_ne_zero hp.1, inv_ne_zero hp.2⟩
      have hlog₁ : ContinuousOn (fun p : ℂ × ℂ => Real.log ‖p.1‖) (U ×ˢ U) :=
        hlog.comp continuous_fst.continuousOn (by intro p hp; exact hp.1)
      have hlog₂ : ContinuousOn (fun p : ℂ × ℂ => Real.log ‖p.2‖) (U ×ˢ U) :=
        hlog.comp continuous_snd.continuousOn (by intro p hp; exact hp.2)
      change ContinuousOn
        (fun p : ℂ × ℂ => H p.1⁻¹ p.2⁻¹ + Real.log ‖p.1‖ + Real.log ‖p.2‖)
        (U ×ˢ U)
      have hassoc :
          (fun p : ℂ × ℂ => H p.1⁻¹ p.2⁻¹ + Real.log ‖p.1‖ + Real.log ‖p.2‖) =
            (fun p => H p.1⁻¹ p.2⁻¹ + (Real.log ‖p.1‖ + Real.log ‖p.2‖)) := by
        funext p
        ring
      rw [hassoc]
      exact hcomp.add (hlog₁.add hlog₂)
    · intro K hK hKU s hs η hη
      have hMexists : ∃ M : ℝ, 0 < M ∧ ∀ x ∈ K, ‖x‖ ≤ M := by
        by_cases hne : Set.Nonempty K
        · obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
          refine ⟨max 1 ‖x‖, by positivity, ?_⟩
          intro y hy
          exact (hmax hy).trans (le_max_right _ _)
        · exact ⟨1, by norm_num, by intro y hy; exact (hne ⟨y, hy⟩).elim⟩
      obtain ⟨M, hMpos, hMbound⟩ := hMexists
      have hK' : IsCompact ((fun x : ℂ => x⁻¹) '' K) := by
        apply hK.image_of_continuousOn
        exact continuousOn_inv₀.mono hKU
      have hK'sub : ((fun x : ℂ => x⁻¹) '' K) ⊆ U := by
        rintro z ⟨x, hx, rfl⟩
        exact inv_ne_zero (hKU hx)
      obtain ⟨δ, hδ, hlim⟩ := hHlim ((fun x : ℂ => x⁻¹) '' K) hK' hK'sub (s / M ^ 2)
        (div_pos hs (by positivity)) η hη
      refine ⟨δ, hδ, ?_⟩
      intro ε ε' hε hεlim hε' hε'lim x hx y hy hsep
      have hx0 : x ≠ 0 := hKU hx
      have hy0 : y ≠ 0 := hKU hy
      have hdist := complexInv_distance_of_ne_zero hx0 hy0
      have hsep' : s / M ^ 2 ≤ ‖x⁻¹ - y⁻¹‖ := by
        rw [hdist]
        have hxy : s ≤ ‖x - y‖ := hsep
        have hxM := hMbound x hx
        have hyM := hMbound y hy
        have hden : ‖x‖ * ‖y‖ ≤ M ^ 2 := by
          calc
            ‖x‖ * ‖y‖ ≤ M * ‖y‖ := mul_le_mul_of_nonneg_right hxM (norm_nonneg y)
            _ ≤ M * M := mul_le_mul_of_nonneg_left hyM hMpos.le
            _ = M ^ 2 := by ring
        have hprod : 0 < ‖x‖ * ‖y‖ := by positivity
        have h1 : s / M ^ 2 ≤ s / (‖x‖ * ‖y‖) :=
          div_le_div_of_nonneg_left hs.le hprod hden
        have h2 : s / (‖x‖ * ‖y‖) ≤ ‖x - y‖ / (‖x‖ * ‖y‖) :=
          (div_le_div_iff₀ hprod hprod).2
            (mul_le_mul_of_nonneg_right hxy (le_of_lt hprod))
        exact h1.trans h2
      have hsrc := hlim ε ε' hε hεlim hε' hε'lim
        (x⁻¹) ⟨x, hx, rfl⟩ (y⁻¹) ⟨y, hy, rfl⟩ hsep'
      have hlogEq : Real.log (1 / ‖x⁻¹ - y⁻¹‖) + H (x⁻¹) (y⁻¹) =
          Real.log (1 / ‖x - y‖) + H' x y := by
        dsimp [H']
        have hxy : x ≠ y := by
          intro heq
          subst y
          have hs0 : s ≤ 0 := by simpa using hsep
          exact (not_le_of_gt hs) hs0
        have hdiffpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
        have hnormx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
        have hnormy : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy0
        rw [hdist, one_div, one_div, Real.log_inv, Real.log_inv]
        rw [Real.log_div (ne_of_gt hdiffpos) (ne_of_gt
          (mul_pos (norm_pos_iff.mpr hx0) (norm_pos_iff.mpr hy0))),
          Real.log_mul hnormx hnormy]
        ring
      rw [← hlogEq]
      exact hsrc
  · obtain ⟨coarseKernel, hcoarse⟩ := hY.fixedCoarseLimit
    refine ⟨fun k x y => coarseKernel k x⁻¹ y⁻¹, ?_⟩
    intro K hK hKU k hk η hη
    have hK' : IsCompact ((fun x : ℂ => x⁻¹) '' K) := by
      apply hK.image_of_continuousOn
      exact continuousOn_inv₀.mono hKU
    have hK'sub : ((fun x : ℂ => x⁻¹) '' K) ⊆ U := by
      rintro z ⟨x, hx, rfl⟩
      exact inv_ne_zero (hKU hx)
    obtain ⟨δ, hδ, hlim⟩ := hcoarse ((fun x : ℂ => x⁻¹) '' K) hK' hK'sub k hk η hη
    refine ⟨δ, hδ, ?_⟩
    intro ε hε hεlim x hx y hy
    exact hlim ε hε hεlim x⁻¹ ⟨x, hx, rfl⟩ y⁻¹ ⟨y, hy, rfl⟩

end DOZZ.Proofs
