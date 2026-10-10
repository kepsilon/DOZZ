/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionEulerPlusCoefficient
public import DOZZ.Hypergeom.ODE.ConnectionEulerSecondCoefficientBox

/-! Holomorphic continuation of both powered connection coefficients from real Euler boxes. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter Set
open scoped Topology

private theorem intCast_abs_sub_lower_bound (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (n : ℤ) :
    min q (1 - q) ≤ |(n : ℝ) - q| := by
  have hn : n ≤ 0 ∨ 1 ≤ n := by omega
  rcases hn with hn | hn
  · have hnR : (n : ℝ) ≤ 0 := by exact_mod_cast hn
    rw [abs_of_nonpos (by linarith)]
    exact (min_le_left q (1 - q)).trans (by linarith)
  · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [abs_of_nonneg (by linarith)]
    exact (min_le_right q (1 - q)).trans (by linarith)

private theorem realInterval_accumulates_in_complex (lo x hi : ℝ)
    (hlo : lo < x) (hhi : x < hi) :
    (x : ℂ) ∈ closure
      ((fun y : ℝ => (y : ℂ)) '' (Ioo lo hi \ {x})) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let d : ℝ := min (ε / 2) ((hi - x) / 2)
  have hd : 0 < d := by dsimp [d]; positivity
  have hdε : d < ε := by
    dsimp [d]
    have hleft : ε / 2 < ε := by linarith
    exact (min_le_left _ _).trans_lt hleft
  have hdhi : d < hi - x := by
    dsimp [d]
    have hright : (hi - x) / 2 < hi - x := by linarith
    exact (min_le_right _ _).trans_lt hright
  have hy : x + d ∈ Ioo lo hi \ {x} := by
    constructor
    · constructor <;> linarith
    · simp [ne_of_gt hd]
  refine ⟨(x + d : ℝ), ?_, ?_⟩
  · exact ⟨x + d, hy, rfl⟩
  · have hdiff : (x : ℂ) - ((x + d : ℝ) : ℂ) = -(d : ℂ) := by push_cast; ring
    rw [dist_eq_norm, hdiff, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
    exact hdε

private theorem ofReal_interval_subset_ball {lo q hi r : ℝ}
    (hleft : q - r ≤ lo) (hright : hi ≤ q + r)
    {x : ℝ} (hx : x ∈ Ioo lo hi) :
    (x : ℂ) ∈ Metric.ball (q : ℂ) r := by
  rcases hx with ⟨hxlo, hxhi⟩
  have hbound : |x - q| < r := by
    apply abs_lt.mpr
    constructor <;> linarith
  rw [Metric.mem_ball, dist_eq_norm]
  have hnorm : ‖(x : ℂ) - (q : ℂ)‖ = |x - q| := by
    rw [show (x : ℂ) - (q : ℂ) = ((x - q : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  exact hbound

private theorem ofReal_ball_subset_integerRange_compl (q r : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hr : r < min q (1 - q)) :
    Metric.ball (q : ℂ) r ⊆ gaussConnectionIntegerRangeᶜ := by
  intro z hz hzInt
  rcases hzInt with ⟨n, hn⟩
  subst z
  have hdist : ‖(n : ℂ) - (q : ℂ)‖ < r := by
    have hball := Metric.mem_ball.mp hz
    simpa [dist_eq_norm] using hball
  have hdistLower : min q (1 - q) ≤ ‖(n : ℂ) - (q : ℂ)‖ := by
    have hnormEq : ‖(n : ℂ) - (q : ℂ)‖ = |(n : ℝ) - q| := by
      calc
        ‖(n : ℂ) - (q : ℂ)‖ = ‖(((n : ℝ) - q : ℝ) : ℂ)‖ := by
          congr 1
          push_cast
          ring
        _ = |(n : ℝ) - q| := by rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnormEq]
    exact intCast_abs_sub_lower_bound q hq0 hq1 n
  linarith

private theorem ofReal_mem_integerRange_compl_of_between_zero_one {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    (x : ℂ) ∈ gaussConnectionIntegerRangeᶜ := by
  rw [gaussConnectionIntegerRange, Set.mem_compl_iff]
  rintro ⟨n, hn⟩
  have hnC : ((n : ℝ) : ℂ) = (x : ℂ) := by
    simpa only [Complex.ofReal_intCast] using hn
  have hnR : (n : ℝ) = x := Complex.ofReal_injective hnC
  have hnCases : n ≤ 0 ∨ 1 ≤ n := by omega
  rcases hnCases with hn | hn
  · have hn' : (n : ℝ) ≤ 0 := by exact_mod_cast hn
    linarith
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith

/-- On the real Euler region, the first midpoint Cramer coefficient is the first Gamma
coefficient. Nonintegrality is retained only for the ODE connection-basis hypotheses. -/

private theorem secondCoefficient_realInterval_accumulates (lo x hi : ℝ)
    (hlo : lo < x) (hhi : x < hi) :
    (x : ℂ) ∈ closure
      ((fun y : ℝ => (y : ℂ)) '' (Ioo lo hi \ {x})) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let d : ℝ := min (ε / 2) ((hi - x) / 2)
  have hd : 0 < d := by dsimp [d]; positivity
  have hdε : d < ε := by
    dsimp [d]
    have hleft : ε / 2 < ε := by linarith
    exact (min_le_left _ _).trans_lt hleft
  have hdhi : d < hi - x := by
    dsimp [d]
    have hright : (hi - x) / 2 < hi - x := by linarith
    exact (min_le_right _ _).trans_lt hright
  have hy : x + d ∈ Ioo lo hi \ {x} := by
    constructor
    · constructor <;> linarith
    · simp [ne_of_gt hd]
  refine ⟨(x + d : ℝ), ?_, ?_⟩
  · exact ⟨x + d, hy, rfl⟩
  · have hdiff : (x : ℂ) - ((x + d : ℝ) : ℂ) = -(d : ℂ) := by push_cast; ring
    rw [dist_eq_norm, hdiff, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hd]
    exact hdε

private theorem secondCoefficient_ofReal_interval_subset_ball {lo q hi r : ℝ}
    (hleft : q - r ≤ lo) (hright : hi ≤ q + r)
    {x : ℝ} (hx : x ∈ Ioo lo hi) :
    (x : ℂ) ∈ Metric.ball (q : ℂ) r := by
  rcases hx with ⟨hxlo, hxhi⟩
  have hbound : |x - q| < r := by
    apply abs_lt.mpr
    constructor <;> linarith
  rw [Metric.mem_ball, dist_eq_norm]
  have hnorm : ‖(x : ℂ) - (q : ℂ)‖ = |x - q| := by
    rw [show (x : ℂ) - (q : ℂ) = ((x - q : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  exact hbound

/-- A sufficiently small real-centered parameter ball avoids every integer. -/
theorem plusSecondCoefficient_ofReal_ball_subset_integerRange_compl
    (q r : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hr : r < min q (1 - q)) :
    Metric.ball (q : ℂ) r ⊆ gaussConnectionIntegerRangeᶜ := by
  intro z hz hzInt
  rcases hzInt with ⟨n, hn⟩
  subst z
  have hdist : ‖(n : ℂ) - (q : ℂ)‖ < r := by
    have hball := Metric.mem_ball.mp hz
    simpa [dist_eq_norm] using hball
  have hdistLower : min q (1 - q) ≤ ‖(n : ℂ) - (q : ℂ)‖ := by
    have hnormEq : ‖(n : ℂ) - (q : ℂ)‖ = |(n : ℝ) - q| := by
      calc
        ‖(n : ℂ) - (q : ℂ)‖ = ‖(((n : ℝ) - q : ℝ) : ℂ)‖ := by
          congr 1
          push_cast
          ring
        _ = |(n : ℝ) - q| := by rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnormEq]
    have hn' : n ≤ 0 ∨ 1 ≤ n := by omega
    rcases hn' with hn' | hn'
    · have hnR : (n : ℝ) ≤ 0 := by exact_mod_cast hn'
      rw [abs_of_nonpos (by linarith)]
      exact (min_le_left q (1 - q)).trans (by linarith)
    · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn'
      rw [abs_of_nonneg (by linarith)]
      exact (min_le_right q (1 - q)).trans (by linarith)
  linarith

/-- The radius-`1/16` ball centered at `-1/4` avoids the integer lattice. -/
theorem plusSecondCoefficient_negativeQuarter_ball_avoids_integers :
    Metric.ball (-(1 / 4 : ℂ)) (1 / 16 : ℝ) ⊆ gaussConnectionIntegerRangeᶜ := by
  intro z hz hzInt
  rcases hzInt with ⟨n, hn⟩
  subst z
  have hball := Metric.mem_ball.mp hz
  have hnorm : ‖(n : ℂ) - (-(1 / 4 : ℂ))‖ = |(n : ℝ) + 1 / 4| := by
    rw [show (n : ℂ) - (-(1 / 4 : ℂ)) = (((n : ℝ) + 1 / 4 : ℝ) : ℂ) by
      push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  have hdist : |(n : ℝ) + 1 / 4| < 1 / 16 := by
    rw [dist_eq_norm, hnorm] at hball
    exact hball
  have hncase : n ≤ -1 ∨ 0 ≤ n := by omega
  rcases hncase with hnneg | hnnonneg
  · have hnR : (n : ℝ) ≤ -1 := by exact_mod_cast hnneg
    have hpos : (n : ℝ) + 1 / 4 ≤ 0 := by linarith
    rw [abs_of_nonpos hpos] at hdist
    norm_num at hdist
    linarith
  · have hnR : (0 : ℝ) ≤ n := by exact_mod_cast hnnonneg
    rw [abs_of_nonneg (by linarith : 0 ≤ (n : ℝ) + 1 / 4)] at hdist
    norm_num at hdist
    linarith

/-- The real first-coefficient identity extends to an open complex parameter box by applying the
one-variable identity theorem successively in `c`, `δ`, and `a`. -/
theorem connectionPlusFirstCramer_eq_gamma_on_open_box
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H) :
    ∀ c ∈ Metric.ball (3 / 4 : ℂ) (1 / 8 : ℝ),
      ∀ δ ∈ Metric.ball (1 / 4 : ℂ) (1 / 8 : ℝ),
        ∀ a ∈ Metric.ball (1 / 4 : ℂ) (1 / 8 : ℝ),
          connectionPlusFirstCramerCoefficient H
              (gaussConnectionCoordinates c δ a) =
            gaussConnectionPlusGammaCoefficient₁ (gaussConnectionCoordinates c δ a) := by
  let SC : Set ℂ := Metric.ball (3 / 4 : ℂ) (1 / 8 : ℝ)
  let TC : Set ℂ := Metric.ball (1 / 4 : ℂ) (1 / 8 : ℝ)
  let VC : Set ℂ := Metric.ball (1 / 4 : ℂ) (1 / 8 : ℝ)
  let SR : Set ℝ := Ioo (11 / 16 : ℝ) (13 / 16 : ℝ)
  let TR : Set ℝ := Ioo (3 / 16 : ℝ) (5 / 16 : ℝ)
  let VR : Set ℝ := Ioo (3 / 16 : ℝ) (5 / 16 : ℝ)
  let f : ℂ × ℂ × ℂ → ℂ := connectionPlusFirstCramerCoefficient H
  let g : ℂ × ℂ × ℂ → ℂ := gaussConnectionPlusGammaCoefficient₁
  have hSCInt : SC ⊆ gaussConnectionIntegerRangeᶜ := by
    simpa [SC, Complex.ofReal_div] using
      (ofReal_ball_subset_integerRange_compl (3 / 4) (1 / 8) (by norm_num)
        (by norm_num) (by norm_num))
  have hTCInt : TC ⊆ gaussConnectionIntegerRangeᶜ := by
    simpa [TC, Complex.ofReal_div] using
      (ofReal_ball_subset_integerRange_compl (1 / 4) (1 / 8) (by norm_num)
        (by norm_num) (by norm_num))
  have hSCReal {x : ℝ} (hx : x ∈ SR) : (x : ℂ) ∈ SC := by
    simpa [SC, Complex.ofReal_div] using
      (ofReal_interval_subset_ball (lo := 11 / 16) (q := 3 / 4)
        (hi := 13 / 16) (r := 1 / 8) (by norm_num) (by norm_num) hx)
  have hTCReal {x : ℝ} (hx : x ∈ TR) : (x : ℂ) ∈ TC := by
    simpa [TC, Complex.ofReal_div] using
      (ofReal_interval_subset_ball (lo := 3 / 16) (q := 1 / 4)
        (hi := 5 / 16) (r := 1 / 8) (by norm_num) (by norm_num) hx)
  have hVCReal {x : ℝ} (hx : x ∈ VR) : (x : ℂ) ∈ VC := by
    simpa [VC, Complex.ofReal_div] using
      (ofReal_interval_subset_ball (lo := 3 / 16) (q := 1 / 4)
        (hi := 5 / 16) (r := 1 / 8) (by norm_num) (by norm_num) hx)
  have hrealEq : ∀ c ∈ SR, ∀ δ ∈ TR, ∀ a ∈ VR,
      f (gaussConnectionCoordinates (c : ℂ) (δ : ℂ) (a : ℂ)) =
        g (gaussConnectionCoordinates (c : ℂ) (δ : ℂ) (a : ℂ)) := by
    intro c hc δ hδ a ha
    have hcpos : 0 < c := by rcases hc with ⟨h₁, h₂⟩; norm_num at h₁ h₂ ⊢; linarith
    have hcLt : c < 1 := by rcases hc with ⟨h₁, h₂⟩; norm_num at h₁ h₂ ⊢; linarith
    have hδpos : 0 < δ := by rcases hδ with ⟨h₁, h₂⟩; norm_num at h₁ h₂ ⊢; linarith
    have hδLt : δ < 1 := by rcases hδ with ⟨h₁, h₂⟩; norm_num at h₁ h₂ ⊢; linarith
    have hap : 0 < a := by rcases ha with ⟨h₁, h₂⟩; norm_num at h₁ h₂ ⊢; linarith
    have hb : 0 < c - δ - a := by
      rcases hc with ⟨hcLo, hcHi⟩
      rcases hδ with ⟨hδLo, hδHi⟩
      rcases ha with ⟨haLo, haHi⟩
      norm_num at hcLo hcHi hδLo hδHi haLo haHi
      linarith
    have hA : 0 < a - c + 1 := by
      rcases hc with ⟨hcLo, hcHi⟩
      rcases ha with ⟨haLo, haHi⟩
      norm_num at hcLo hcHi haLo haHi
      linarith
    have hB : 0 < (c - δ - a) - c + 1 := by
      rcases hδ with ⟨hδLo, hδHi⟩
      rcases ha with ⟨haLo, haHi⟩
      norm_num at hδLo hδHi haLo haHi
      linarith
    have hcInt := ofReal_mem_integerRange_compl_of_between_zero_one hcpos hcLt
    have hδInt := ofReal_mem_integerRange_compl_of_between_zero_one hδpos hδLt
    have hdelta : 0 < c - a - (c - δ - a) := by simpa only [show c - a - (c - δ - a) = δ by ring] using hδpos
    have hreal := connectionPlusFirstCramer_eq_gamma_of_real hH a (c - δ - a) c
      hA hB hdelta hcInt (by
        rw [show c - a - (c - δ - a) = δ by ring]
        exact hδInt)
    simpa [f, g, gaussConnectionCoordinates] using hreal
  have hf : ∀ p ∈ gaussConnectionParameterDomain, DifferentiableAt ℂ f p := by
    intro p hp
    exact connectionPlusFirstCramerCoefficient_differentiableAt hH hp
  have hg : ∀ p ∈ gaussConnectionParameterDomain, DifferentiableAt ℂ g p := by
    intro p hp
    exact gaussConnectionPlusGammaCoefficient₁_differentiableAt hp
  have hcoord (c δ a : ℂ) (hc : c ∈ SC) (hδ : δ ∈ TC) :
      gaussConnectionCoordinates c δ a ∈ gaussConnectionParameterDomain := by
    have hparams : c ∈ gaussConnectionIntegerRangeᶜ ∧
        δ ∈ gaussConnectionIntegerRangeᶜ := ⟨hSCInt hc, hTCInt hδ⟩
    simpa [gaussConnectionCoordinates, gaussConnectionParameterDomain,
      gaussConnectionIntegerRange, eq_comm] using hparams
  have hfC (δ a : ℂ) (hδ : δ ∈ TC) (ha : a ∈ VC) :
      AnalyticOnNhd ℂ (fun c => f (gaussConnectionCoordinates c δ a)) SC := by
    apply DifferentiableOn.analyticOnNhd
    · intro c hc
      have hmap : DifferentiableAt ℂ (fun x => gaussConnectionCoordinates x δ a) c := by
        dsimp [gaussConnectionCoordinates]
        fun_prop
      exact ((hf _ (hcoord c δ a hc hδ)).comp c hmap).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hgC (δ a : ℂ) (hδ : δ ∈ TC) (ha : a ∈ VC) :
      AnalyticOnNhd ℂ (fun c => g (gaussConnectionCoordinates c δ a)) SC := by
    apply DifferentiableOn.analyticOnNhd
    · intro c hc
      have hmap : DifferentiableAt ℂ (fun x => gaussConnectionCoordinates x δ a) c := by
        dsimp [gaussConnectionCoordinates]
        fun_prop
      exact ((hg _ (hcoord c δ a hc hδ)).comp c hmap).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hfD (c a : ℂ) (hc : c ∈ SC) (ha : a ∈ VC) :
      AnalyticOnNhd ℂ (fun δ => f (gaussConnectionCoordinates c δ a)) TC := by
    apply DifferentiableOn.analyticOnNhd
    · intro δ hδ
      have hmap : DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c x a) δ := by
        dsimp [gaussConnectionCoordinates]
        fun_prop
      exact ((hf _ (hcoord c δ a hc hδ)).comp δ hmap).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hgD (c a : ℂ) (hc : c ∈ SC) (ha : a ∈ VC) :
      AnalyticOnNhd ℂ (fun δ => g (gaussConnectionCoordinates c δ a)) TC := by
    apply DifferentiableOn.analyticOnNhd
    · intro δ hδ
      have hmap : DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c x a) δ := by
        dsimp [gaussConnectionCoordinates]
        fun_prop
      exact ((hg _ (hcoord c δ a hc hδ)).comp δ hmap).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hfA (c δ : ℂ) (hc : c ∈ SC) (hδ : δ ∈ TC) :
      AnalyticOnNhd ℂ (fun a => f (gaussConnectionCoordinates c δ a)) VC := by
    apply DifferentiableOn.analyticOnNhd
    · intro a ha
      have hmap : DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c δ x) a := by
        dsimp [gaussConnectionCoordinates]
        fun_prop
      exact ((hf _ (hcoord c δ a hc hδ)).comp a hmap).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hgA (c δ : ℂ) (hc : c ∈ SC) (hδ : δ ∈ TC) :
      AnalyticOnNhd ℂ (fun a => g (gaussConnectionCoordinates c δ a)) VC := by
    apply DifferentiableOn.analyticOnNhd
    · intro a ha
      have hmap : DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c δ x) a := by
        dsimp [gaussConnectionCoordinates]
        fun_prop
      exact ((hg _ (hcoord c δ a hc hδ)).comp a hmap).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hcCenter : (3 / 4 : ℂ) ∈ SC := by norm_num [SC, Metric.mem_ball, dist_eq_norm]
  have hδCenter : (1 / 4 : ℂ) ∈ TC := by norm_num [TC, Metric.mem_ball, dist_eq_norm]
  have haCenter : (1 / 4 : ℂ) ∈ VC := by norm_num [VC, Metric.mem_ball, dist_eq_norm]
  have hC (δ : ℝ) (hδ : δ ∈ TR) (a : ℝ) (ha : a ∈ VR) :
      ∀ c ∈ SC, f (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ)) =
        g (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ)) := by
    have hδC := hTCReal hδ
    have haC := hVCReal ha
    have hclosure : (3 / 4 : ℂ) ∈ closure
        ({c | f (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ)) =
            g (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ))} \ {(3 / 4 : ℂ)}) := by
      have hacc := realInterval_accumulates_in_complex
        (11 / 16) (3 / 4) (13 / 16) (by norm_num) (by norm_num)
      have hsub : ((fun x : ℝ => (x : ℂ)) '' (SR \ {(3 / 4 : ℝ)})) ⊆
          {c | f (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ)) =
            g (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ))} \ {(3 / 4 : ℂ)} := by
        rintro z ⟨c, ⟨hc, hcn⟩, rfl⟩
        constructor
        · exact hrealEq c hc δ hδ a ha
        · intro heq
          apply hcn
          have heqC : (c : ℂ) = (3 / 4 : ℂ) := by
            simpa only [Set.mem_singleton_iff] using heq
          have heq' : c = (3 / 4 : ℝ) :=
            Complex.ofReal_injective (heqC.trans (by norm_num))
          exact Set.mem_singleton_iff.mpr heq'
      exact closure_mono hsub (by simpa [SR] using hacc)
    have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure
      (hfC (δ : ℂ) (a : ℂ) hδC haC) (hgC (δ : ℂ) (a : ℂ) hδC haC)
      (convex_ball (3 / 4 : ℂ) (1 / 8 : ℝ)).isPreconnected hcCenter hclosure
    intro c hc
    exact hEq hc
  have hD (c : ℂ) (hc : c ∈ SC) (a : ℝ) (ha : a ∈ VR) :
      ∀ δ ∈ TC, f (gaussConnectionCoordinates c δ (a : ℂ)) =
        g (gaussConnectionCoordinates c δ (a : ℂ)) := by
    have haC := hVCReal ha
    have hclosure : (1 / 4 : ℂ) ∈ closure
        ({δ | f (gaussConnectionCoordinates c δ (a : ℂ)) =
            g (gaussConnectionCoordinates c δ (a : ℂ))} \ {(1 / 4 : ℂ)}) := by
      have hacc := realInterval_accumulates_in_complex
        (3 / 16) (1 / 4) (5 / 16) (by norm_num) (by norm_num)
      have hsub : ((fun x : ℝ => (x : ℂ)) '' (TR \ {(1 / 4 : ℝ)})) ⊆
          {δ | f (gaussConnectionCoordinates c δ (a : ℂ)) =
            g (gaussConnectionCoordinates c δ (a : ℂ))} \ {(1 / 4 : ℂ)} := by
        rintro z ⟨δ, ⟨hδ, hδn⟩, rfl⟩
        constructor
        · exact hC δ hδ a ha c hc
        · intro heq
          apply hδn
          have heqC : (δ : ℂ) = (1 / 4 : ℂ) := by
            simpa only [Set.mem_singleton_iff] using heq
          have heq' : δ = (1 / 4 : ℝ) :=
            Complex.ofReal_injective (heqC.trans (by norm_num))
          exact Set.mem_singleton_iff.mpr heq'
      exact closure_mono hsub (by simpa [TR] using hacc)
    have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure
      (hfD c (a : ℂ) hc haC) (hgD c (a : ℂ) hc haC)
      (convex_ball (1 / 4 : ℂ) (1 / 8 : ℝ)).isPreconnected hδCenter hclosure
    intro δ hδ
    exact hEq hδ
  have hA (c δ : ℂ) (hc : c ∈ SC) (hδ : δ ∈ TC) :
      ∀ a ∈ VC, f (gaussConnectionCoordinates c δ a) =
        g (gaussConnectionCoordinates c δ a) := by
    have hclosure : (1 / 4 : ℂ) ∈ closure
        ({a | f (gaussConnectionCoordinates c δ a) =
            g (gaussConnectionCoordinates c δ a)} \ {(1 / 4 : ℂ)}) := by
      have hacc := realInterval_accumulates_in_complex
        (3 / 16) (1 / 4) (5 / 16) (by norm_num) (by norm_num)
      have hsub : ((fun x : ℝ => (x : ℂ)) '' (VR \ {(1 / 4 : ℝ)})) ⊆
          {a | f (gaussConnectionCoordinates c δ a) =
            g (gaussConnectionCoordinates c δ a)} \ {(1 / 4 : ℂ)} := by
        rintro z ⟨a, ⟨ha, han⟩, rfl⟩
        constructor
        · exact hD c hc a ha δ hδ
        · intro heq
          apply han
          have heqC : (a : ℂ) = (1 / 4 : ℂ) := by
            simpa only [Set.mem_singleton_iff] using heq
          have heq' : a = (1 / 4 : ℝ) :=
            Complex.ofReal_injective (heqC.trans (by norm_num))
          exact Set.mem_singleton_iff.mpr heq'
      exact closure_mono hsub (by simpa [VR] using hacc)
    have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure
      (hfA c δ hc hδ) (hgA c δ hc hδ)
      (convex_ball (1 / 4 : ℂ) (1 / 8 : ℝ)).isPreconnected haCenter hclosure
    intro a ha
    exact hEq ha
  intro c hc δ hδ a ha
  exact hA c δ hc hδ a ha

/-- The second midpoint Cramer coefficient agrees with its Gamma value on a nonempty complex
open box. The box is centered in the negative-excess Euler region, then three one-variable
identity theorems continue the real identity in `c`, `δ`, and `a`. -/
theorem connectionPlusSecondCramer_eq_gamma_on_open_box
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H) :
    ∀ c ∈ Metric.ball (3 / 4 : ℂ) (1 / 8 : ℝ),
      ∀ δ ∈ Metric.ball (-(1 / 4 : ℂ)) (1 / 16 : ℝ),
        ∀ a ∈ Metric.ball (1 / 2 : ℂ) (1 / 16 : ℝ),
          connectionPlusSecondCramerCoefficient H
              (gaussConnectionCoordinates c δ a) =
            gaussConnectionPlusGammaCoefficient₂ (gaussConnectionCoordinates c δ a) := by
  let SC : Set ℂ := Metric.ball (3 / 4 : ℂ) (1 / 8 : ℝ)
  let TC : Set ℂ := Metric.ball (-(1 / 4 : ℂ)) (1 / 16 : ℝ)
  let VC : Set ℂ := Metric.ball (1 / 2 : ℂ) (1 / 16 : ℝ)
  let SR : Set ℝ := Ioo (11 / 16 : ℝ) (13 / 16 : ℝ)
  let TR : Set ℝ := Ioo (-(5 / 16 : ℝ)) (-(3 / 16 : ℝ))
  let VR : Set ℝ := Ioo (7 / 16 : ℝ) (9 / 16 : ℝ)
  let f : ℂ × ℂ × ℂ → ℂ := connectionPlusSecondCramerCoefficient H
  let g : ℂ × ℂ × ℂ → ℂ := gaussConnectionPlusGammaCoefficient₂
  have hSCInt : SC ⊆ gaussConnectionIntegerRangeᶜ := by
    simpa [SC, Complex.ofReal_div] using
      (plusSecondCoefficient_ofReal_ball_subset_integerRange_compl (3 / 4) (1 / 8)
        (by norm_num) (by norm_num) (by norm_num))
  have hTCInt : TC ⊆ gaussConnectionIntegerRangeᶜ := by
    simpa [TC] using plusSecondCoefficient_negativeQuarter_ball_avoids_integers
  have hSCReal {x : ℝ} (hx : x ∈ SR) : (x : ℂ) ∈ SC := by
    simpa [SC, Complex.ofReal_div] using
      (secondCoefficient_ofReal_interval_subset_ball (lo := 11 / 16) (q := 3 / 4)
        (hi := 13 / 16) (r := 1 / 8) (by norm_num) (by norm_num) hx)
  have hTCReal {x : ℝ} (hx : x ∈ TR) : (x : ℂ) ∈ TC := by
    simpa [TC] using
      (secondCoefficient_ofReal_interval_subset_ball (lo := -(5 / 16)) (q := -(1 / 4))
        (hi := -(3 / 16)) (r := 1 / 16) (by norm_num) (by norm_num) hx)
  have hVCReal {x : ℝ} (hx : x ∈ VR) : (x : ℂ) ∈ VC := by
    simpa [VC, Complex.ofReal_div] using
      (secondCoefficient_ofReal_interval_subset_ball (lo := 7 / 16) (q := 1 / 2)
        (hi := 9 / 16) (r := 1 / 16) (by norm_num) (by norm_num) hx)
  have hrealEq : ∀ c ∈ SR, ∀ δ ∈ TR, ∀ a ∈ VR,
      f (gaussConnectionCoordinates (c : ℂ) (δ : ℂ) (a : ℂ)) =
        g (gaussConnectionCoordinates (c : ℂ) (δ : ℂ) (a : ℂ)) := by
    intro c hc δ hδ a ha
    have hcpos : 0 < c := by rcases hc with ⟨h₁, h₂⟩; norm_num at h₁ h₂ ⊢; linarith
    have hcLt : c < 1 := by rcases hc with ⟨h₁, h₂⟩; norm_num at h₁ h₂ ⊢; linarith
    have hδneg : δ < 0 := by rcases hδ with ⟨h₁, h₂⟩; norm_num at h₁ h₂ ⊢; linarith
    have hap : 0 < a := by rcases ha with ⟨h₁, h₂⟩; norm_num at h₁ h₂ ⊢; linarith
    have hca : 0 < c - a := by
      rcases hc with ⟨hcLo, hcHi⟩
      rcases ha with ⟨haLo, haHi⟩
      norm_num at hcLo hcHi haLo haHi
      linarith
    have hcb : 0 < c - (c - δ - a) := by
      have hδa : 0 < δ + a := by
        rcases hδ with ⟨hδLo, hδHi⟩
        rcases ha with ⟨haLo, haHi⟩
        norm_num at hδLo hδHi haLo haHi
        linarith
      convert hδa using 1
      ring
    have hb : 0 < c - δ - a := by
      rcases hc with ⟨hcLo, hcHi⟩
      rcases hδ with ⟨hδLo, hδHi⟩
      rcases ha with ⟨haLo, haHi⟩
      norm_num at hcLo hcHi hδLo hδHi haLo haHi
      linarith
    have h1a : 0 < 1 - a := by
      rcases ha with ⟨haLo, haHi⟩
      norm_num at haLo haHi ⊢
      linarith
    have h1b : 0 < 1 - (c - δ - a) := by
      rcases hc with ⟨hcLo, hcHi⟩
      rcases hδ with ⟨hδLo, hδHi⟩
      rcases ha with ⟨haLo, haHi⟩
      norm_num at hcLo hcHi hδLo hδHi haLo haHi ⊢
      linarith
    have hA : 0 < a - c + 1 := by
      rcases hc with ⟨hcLo, hcHi⟩
      rcases ha with ⟨haLo, haHi⟩
      norm_num at hcLo hcHi haLo haHi
      linarith
    have hB : 0 < (c - δ - a) - c + 1 := by
      rw [show (c - δ - a) - c + 1 = 1 - δ - a by ring]
      linarith
    have hcInt := hSCInt (hSCReal hc)
    have hδInt : ((c - a - (c - δ - a) : ℝ) : ℂ) ∈
        gaussConnectionIntegerRangeᶜ := by
      rw [show c - a - (c - δ - a) = δ by ring]
      exact hTCInt (hTCReal hδ)
    have hdelta : c - a - (c - δ - a) < 0 := by
      rw [show c - a - (c - δ - a) = δ by ring]
      exact hδneg
    have hreal := connectionPlusSecondCramer_eq_gamma_of_real hH a (c - δ - a) c
      hA hB h1a h1b hdelta hcInt hδInt
    simpa [f, g, gaussConnectionCoordinates] using hreal
  have hf : ∀ p ∈ gaussConnectionParameterDomain, DifferentiableAt ℂ f p := by
    intro p hp
    exact connectionPlusSecondCramerCoefficient_differentiableAt hH hp
  have hg : ∀ p ∈ gaussConnectionParameterDomain, DifferentiableAt ℂ g p := by
    intro p hp
    exact gaussConnectionPlusGammaCoefficient₂_differentiableAt hp
  have hcoord (c δ a : ℂ) (hc : c ∈ SC) (hδ : δ ∈ TC) :
      gaussConnectionCoordinates c δ a ∈ gaussConnectionParameterDomain := by
    have hparams : c ∈ gaussConnectionIntegerRangeᶜ ∧
        δ ∈ gaussConnectionIntegerRangeᶜ := ⟨hSCInt hc, hTCInt hδ⟩
    simpa [gaussConnectionCoordinates, gaussConnectionParameterDomain,
      gaussConnectionIntegerRange, eq_comm] using hparams
  have hfC (δ a : ℂ) (hδ : δ ∈ TC) (ha : a ∈ VC) :
      AnalyticOnNhd ℂ (fun c => f (gaussConnectionCoordinates c δ a)) SC := by
    apply DifferentiableOn.analyticOnNhd
    · intro c hc
      have hmap : DifferentiableAt ℂ (fun x => gaussConnectionCoordinates x δ a) c := by
        dsimp [gaussConnectionCoordinates]
        fun_prop
      exact ((hf _ (hcoord c δ a hc hδ)).comp c hmap).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hgC (δ a : ℂ) (hδ : δ ∈ TC) (ha : a ∈ VC) :
      AnalyticOnNhd ℂ (fun c => g (gaussConnectionCoordinates c δ a)) SC := by
    apply DifferentiableOn.analyticOnNhd
    · intro c hc
      have hmap : DifferentiableAt ℂ (fun x => gaussConnectionCoordinates x δ a) c := by
        dsimp [gaussConnectionCoordinates]
        fun_prop
      exact ((hg _ (hcoord c δ a hc hδ)).comp c hmap).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hfD (c a : ℂ) (hc : c ∈ SC) (ha : a ∈ VC) :
      AnalyticOnNhd ℂ (fun δ => f (gaussConnectionCoordinates c δ a)) TC := by
    apply DifferentiableOn.analyticOnNhd
    · intro δ hδ
      have hmap : DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c x a) δ := by
        dsimp [gaussConnectionCoordinates]
        fun_prop
      exact ((hf _ (hcoord c δ a hc hδ)).comp δ hmap).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hgD (c a : ℂ) (hc : c ∈ SC) (ha : a ∈ VC) :
      AnalyticOnNhd ℂ (fun δ => g (gaussConnectionCoordinates c δ a)) TC := by
    apply DifferentiableOn.analyticOnNhd
    · intro δ hδ
      have hmap : DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c x a) δ := by
        dsimp [gaussConnectionCoordinates]
        fun_prop
      exact ((hg _ (hcoord c δ a hc hδ)).comp δ hmap).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hfA (c δ : ℂ) (hc : c ∈ SC) (hδ : δ ∈ TC) :
      AnalyticOnNhd ℂ (fun a => f (gaussConnectionCoordinates c δ a)) VC := by
    apply DifferentiableOn.analyticOnNhd
    · intro a ha
      have hmap : DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c δ x) a := by
        dsimp [gaussConnectionCoordinates]
        fun_prop
      exact ((hf _ (hcoord c δ a hc hδ)).comp a hmap).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hgA (c δ : ℂ) (hc : c ∈ SC) (hδ : δ ∈ TC) :
      AnalyticOnNhd ℂ (fun a => g (gaussConnectionCoordinates c δ a)) VC := by
    apply DifferentiableOn.analyticOnNhd
    · intro a ha
      have hmap : DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c δ x) a := by
        dsimp [gaussConnectionCoordinates]
        fun_prop
      exact ((hg _ (hcoord c δ a hc hδ)).comp a hmap).differentiableWithinAt
    · exact Metric.isOpen_ball
  have hcCenter : (3 / 4 : ℂ) ∈ SC := by
    norm_num [SC, Metric.mem_ball, dist_eq_norm]
  have hδCenter : -(1 / 4 : ℂ) ∈ TC := by
    norm_num [TC, Metric.mem_ball, dist_eq_norm]
  have haCenter : (1 / 2 : ℂ) ∈ VC := by
    norm_num [VC, Metric.mem_ball, dist_eq_norm]
  have hC (δ : ℝ) (hδ : δ ∈ TR) (a : ℝ) (ha : a ∈ VR) :
      ∀ c ∈ SC, f (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ)) =
        g (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ)) := by
    have hδC := hTCReal hδ
    have haC := hVCReal ha
    have hclosure : (3 / 4 : ℂ) ∈ closure
        ({c | f (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ)) =
            g (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ))} \ {(3 / 4 : ℂ)}) := by
      have hacc := secondCoefficient_realInterval_accumulates
        (11 / 16) (3 / 4) (13 / 16) (by norm_num) (by norm_num)
      have hsub : ((fun x : ℝ => (x : ℂ)) '' (SR \ {(3 / 4 : ℝ)})) ⊆
          {c | f (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ)) =
            g (gaussConnectionCoordinates c (δ : ℂ) (a : ℂ))} \ {(3 / 4 : ℂ)} := by
        rintro z ⟨c, ⟨hc, hcn⟩, rfl⟩
        constructor
        · exact hrealEq c hc δ hδ a ha
        · intro heq
          apply hcn
          have heqC : (c : ℂ) = (3 / 4 : ℂ) := by
            simpa only [Set.mem_singleton_iff] using heq
          exact Set.mem_singleton_iff.mpr (Complex.ofReal_injective (heqC.trans (by norm_num)))
      exact closure_mono hsub (by simpa [SR] using hacc)
    have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure
      (hfC (δ : ℂ) (a : ℂ) hδC haC) (hgC (δ : ℂ) (a : ℂ) hδC haC)
      (convex_ball (3 / 4 : ℂ) (1 / 8 : ℝ)).isPreconnected hcCenter hclosure
    intro c hc
    exact hEq hc
  have hD (c : ℂ) (hc : c ∈ SC) (a : ℝ) (ha : a ∈ VR) :
      ∀ δ ∈ TC, f (gaussConnectionCoordinates c δ (a : ℂ)) =
        g (gaussConnectionCoordinates c δ (a : ℂ)) := by
    have haC := hVCReal ha
    have hclosure : (-(1 / 4 : ℂ)) ∈ closure
        ({δ | f (gaussConnectionCoordinates c δ (a : ℂ)) =
            g (gaussConnectionCoordinates c δ (a : ℂ))} \ {-(1 / 4 : ℂ)}) := by
      have hacc := secondCoefficient_realInterval_accumulates
        (-(5 / 16)) (-(1 / 4)) (-(3 / 16)) (by norm_num) (by norm_num)
      have hsub : ((fun x : ℝ => (x : ℂ)) '' (TR \ {-(1 / 4 : ℝ)})) ⊆
          {δ | f (gaussConnectionCoordinates c δ (a : ℂ)) =
            g (gaussConnectionCoordinates c δ (a : ℂ))} \ {-(1 / 4 : ℂ)} := by
        rintro z ⟨δ, ⟨hδ, hδn⟩, rfl⟩
        constructor
        · exact hC δ hδ a ha c hc
        · intro heq
          apply hδn
          have heqC : (δ : ℂ) = -(1 / 4 : ℂ) := by
            simpa only [Set.mem_singleton_iff] using heq
          exact Set.mem_singleton_iff.mpr
            (Complex.ofReal_injective (heqC.trans (by norm_num)))
      exact closure_mono hsub (by simpa [TR] using hacc)
    have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure
      (hfD c (a : ℂ) hc haC) (hgD c (a : ℂ) hc haC)
      (convex_ball (-(1 / 4 : ℂ)) (1 / 16 : ℝ)).isPreconnected hδCenter hclosure
    intro δ hδ
    exact hEq hδ
  have hA (c δ : ℂ) (hc : c ∈ SC) (hδ : δ ∈ TC) :
      ∀ a ∈ VC, f (gaussConnectionCoordinates c δ a) =
        g (gaussConnectionCoordinates c δ a) := by
    have hclosure : (1 / 2 : ℂ) ∈ closure
        ({a | f (gaussConnectionCoordinates c δ a) =
            g (gaussConnectionCoordinates c δ a)} \ {(1 / 2 : ℂ)}) := by
      have hacc := secondCoefficient_realInterval_accumulates
        (7 / 16) (1 / 2) (9 / 16) (by norm_num) (by norm_num)
      have hsub : ((fun x : ℝ => (x : ℂ)) '' (VR \ {(1 / 2 : ℝ)})) ⊆
          {a | f (gaussConnectionCoordinates c δ a) =
            g (gaussConnectionCoordinates c δ a)} \ {(1 / 2 : ℂ)} := by
        rintro z ⟨a, ⟨ha, han⟩, rfl⟩
        constructor
        · exact hD c hc a ha δ hδ
        · intro heq
          apply han
          have heqC : (a : ℂ) = (1 / 2 : ℂ) := by
            simpa only [Set.mem_singleton_iff] using heq
          exact Set.mem_singleton_iff.mpr (Complex.ofReal_injective (heqC.trans (by norm_num)))
      exact closure_mono hsub (by simpa [VR] using hacc)
    have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure
      (hfA c δ hc hδ) (hgA c δ hc hδ)
      (convex_ball (1 / 2 : ℂ) (1 / 16 : ℝ)).isPreconnected haCenter hclosure
    intro a ha
    exact hEq ha
  intro c hc δ hδ a ha
  exact hA c δ hc hδ a ha

end DOZZ.Proofs
