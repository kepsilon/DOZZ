/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFFStructure.CircleVersion
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Complex.Harmonic.Poisson

/-!
# Literal smooth exterior Poisson collars

Normalized positive radial bumps give the exact collar densities required by
`DOZZ.exists_exteriorPinned_markov_uniform`. Their Cartesian formula is smooth across the apparent
center pole, because the radial support has a positive gap. The actual TestFn values, compact
support, separated-disk exterior support, pin-circle containment, shrinking support and polar
formula are proved. Boundary weights have deterministic bounds on every compact inner disk.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped Topology ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- A normalized smooth radial density strictly inside the positive collar interval. -/
noncomputable def poissonCollarDensity (ε : ℝ) (hε : 0 < ε) (k : ℕ) : ℝ → ℝ :=
  (⟨ε/(8*((k : ℝ)+1)), ε/(4*((k : ℝ)+1)), by positivity, by
    have hp : 0 < ε/(8*((k : ℝ)+1)) := by positivity
    calc
      _ < 2*(ε/(8*((k : ℝ)+1))) := by linarith
      _ = ε/(4*((k : ℝ)+1)) := by
        field_simp [show (k : ℝ)+1 ≠ 0 by positivity]
        ring⟩ :
    ContDiffBump (ε/(2*((k : ℝ)+1)))).normed volume

/-- The radial collar density is smooth. -/
theorem poissonCollarDensity_contDiff (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (poissonCollarDensity ε hε k) := by
  exact ContDiffBump.contDiff_normed _

/-- The normalized density is nonnegative. -/
theorem poissonCollarDensity_nonneg (ε : ℝ) (hε : 0 < ε) (k : ℕ) (t : ℝ) :
    0 ≤ poissonCollarDensity ε hε k t := by
  exact ContDiffBump.nonneg_normed _ _

/-- Normalization gives total radial mass one. -/
theorem integral_poissonCollarDensity (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    (∫ t : ℝ, poissonCollarDensity ε hε k t) = 1 := by
  exact ContDiffBump.integral_normed _

/-- The normalized collar density has compact support. -/
theorem poissonCollarDensity_hasCompactSupport (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    HasCompactSupport (poissonCollarDensity ε hε k) := by
  exact ContDiffBump.hasCompactSupport_normed _

/-- The collar support stays strictly between zero and its prescribed width. -/
theorem tsupport_poissonCollarDensity_subset (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    tsupport (poissonCollarDensity ε hε k) ⊆ Ioo 0 (ε/((k : ℝ)+1)) := by
  rw [poissonCollarDensity, ContDiffBump.tsupport_normed_eq]
  intro t ht
  have hk : 0 < (k : ℝ)+1 := by positivity
  have hdist : |t - ε/(2*((k : ℝ)+1))| ≤ ε/(4*((k : ℝ)+1)) := by
    simpa only [mem_closedBall, Real.dist_eq] using ht
  have htlo := (abs_le.mp hdist).1
  have hthi := (abs_le.mp hdist).2
  have he : 0 < ε/((k : ℝ)+1) := div_pos hε hk
  have h2 : ε/(2*((k : ℝ)+1)) = (ε/((k : ℝ)+1))/2 := by field_simp [hk.ne']
  have h4 : ε/(4*((k : ℝ)+1)) = (ε/((k : ℝ)+1))/4 := by field_simp [hk.ne']
  rw [h2, h4] at htlo hthi
  constructor <;> linarith

/-- A positive separation margin supplies a strictly smaller collar width. -/
theorem exists_poissonCollarDensity (δ : ℝ) (hδ : 0 < δ) :
    ∃ (ε : ℝ) (q : ℕ → ℝ → ℝ), 0 < ε ∧ ε < δ/2 ∧
      ∀ k, ContDiff ℝ (⊤ : ℕ∞) (q k) ∧ HasCompactSupport (q k) ∧
        tsupport (q k) ⊆ Ioo 0 (ε/(k+1)) ∧ (∀ t, 0 ≤ q k t) ∧ (∫ t : ℝ, q k t) = 1 := by
  have he : 0 < δ/4 := by positivity
  refine ⟨δ/4, poissonCollarDensity (δ/4) he, he, by linarith, fun k => ?_⟩
  exact ⟨poissonCollarDensity_contDiff _ _ _, poissonCollarDensity_hasCompactSupport _ _ _,
    tsupport_poissonCollarDensity_subset _ _ _, poissonCollarDensity_nonneg _ _ _,
    integral_poissonCollarDensity _ _ _⟩

/-- Radial normalization maps every nonzero displacement to the boundary circle. -/
theorem norm_poissonBoundaryDirection (c w : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hw : w ≠ c) :
    ‖(ρ : ℂ)*(w-c)/(‖w-c‖ : ℂ)‖ = ρ := by
  have hn : ‖w-c‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw)
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), mul_div_cancel_right₀ _ hn]

/-- An interior point is separated from every radially normalized boundary point. -/
theorem poissonBoundary_ne (c z w : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (hw : w ≠ c) :
    c+(ρ : ℂ)*(w-c)/(‖w-c‖ : ℂ)-z ≠ 0 := by
  intro h
  have he : (ρ : ℂ)*(w-c)/(‖w-c‖ : ℂ) = z-c := by linear_combination h
  have hn := norm_poissonBoundaryDirection c w ρ hρ hw
  rw [he] at hn
  have hz' : ‖z-c‖ < ρ := by simpa only [mem_ball, dist_eq_norm] using hz
  exact hz'.ne hn

/-- The support of a Poisson collar lies over the support of its radial density. -/
theorem tsupport_poissonCollarValue_subset (c z : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (q : ℝ → ℝ) :
    tsupport (poissonCollarValue c z ρ hρ hz q) ⊆
      (fun w : ℂ => ‖w-c‖-ρ) ⁻¹' tsupport q := by
  apply closure_minimal
  · intro w hw
    apply subset_closure
    contrapose! hw
    simp only [Function.mem_support, not_ne_iff] at hw ⊢
    simp only [poissonCollarValue, hw, zero_mul, zero_div]
  · exact (isClosed_tsupport q).preimage (by fun_prop)

/-- The Cartesian collar is separated from the center and lies in its outer annulus. -/
theorem tsupport_poissonCollarValue_annulus (c z : ℂ) (ρ ε : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (q : ℝ → ℝ) (hq : tsupport q ⊆ Ioo 0 ε) :
    tsupport (poissonCollarValue c z ρ hρ hz q) ⊆
      {w | ρ < ‖w-c‖ ∧ ‖w-c‖ < ρ+ε} := by
  intro w hw
  have h := hq (tsupport_poissonCollarValue_subset c z ρ hρ hz q hw)
  constructor <;> linarith [h.1, h.2]

/-- The Cartesian Poisson collar has compact support whenever the radial support is bounded. -/
theorem poissonCollarValue_hasCompactSupport (c z : ℂ) (ρ ε : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (q : ℝ → ℝ) (hq : tsupport q ⊆ Ioo 0 ε) :
    HasCompactSupport (poissonCollarValue c z ρ hρ hz q) := by
  apply (isCompact_closedBall c (ρ+ε)).of_isClosed_subset (isClosed_tsupport _)
  intro w hw
  have h := tsupport_poissonCollarValue_annulus c z ρ ε hρ hz q hq hw
  exact (mem_closedBall.mpr (by simpa only [dist_eq_norm] using h.2.le))


/-- The collar vanishes on the whole inner disk, including its apparent Cartesian pole. -/
theorem poissonCollarValue_eq_zero_inside (c z : ℂ) (ρ ε : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (q : ℝ → ℝ) (hq : tsupport q ⊆ Ioo 0 ε)
    {w : ℂ} (hw : w ∈ ball c ρ) : poissonCollarValue c z ρ hρ hz q w = 0 := by
  have hn : ‖w-c‖ < ρ := by simpa only [mem_ball, dist_eq_norm] using hw
  have hqzero : q (‖w-c‖-ρ) = 0 := image_eq_zero_of_notMem_tsupport (fun h => by
    have hp := (hq h).1
    linarith)
  simp only [poissonCollarValue, hqzero, zero_mul, zero_div]

/-- Away from the center, every denominator in the Cartesian collar is nonzero. -/
theorem contDiffAt_poissonCollarValue_of_ne (c z : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (q : ℝ → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    {w : ℂ} (hw : w ≠ c) :
    ContDiffAt ℝ (⊤ : ℕ∞) (poissonCollarValue c z ρ hρ hz q) w := by
  have hsub : ContDiffAt ℝ (⊤ : ℕ∞) (fun v : ℂ => v-c) w :=
    contDiffAt_id.sub contDiffAt_const
  have hn := hsub.norm ℝ (sub_ne_zero.mpr hw)
  have hscalar : ContDiffAt ℝ (⊤ : ℕ∞) (fun v : ℂ => ρ/‖v-c‖) w :=
    contDiffAt_const.div hn (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw))
  have hbound : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun v : ℂ => c+(ρ : ℂ)*(v-c)/(‖v-c‖ : ℂ)-z) w := by
    have h : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun v : ℂ => c + (ρ/‖v-c‖) • (v-c) - z) w :=
      (contDiffAt_const.add (hscalar.smul hsub)).sub contDiffAt_const
    convert h using 1
    funext v
    simp only [Complex.real_smul, div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv]
    ring
  have hden : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun v : ℂ => 2*Real.pi*‖v-c‖*‖c+(ρ : ℂ)*(v-c)/(‖v-c‖ : ℂ)-z‖^2) w :=
    (contDiffAt_const.mul hn).mul (hbound.norm_sq ℝ)
  have hdenzero : 2*Real.pi*‖w-c‖*‖c+(ρ : ℂ)*(w-c)/(‖w-c‖ : ℂ)-z‖^2 ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw))
    · exact pow_ne_zero _ (norm_ne_zero_iff.mpr (poissonBoundary_ne c z w ρ hρ hz hw))
  exact ((hq.contDiffAt.comp w (hn.sub contDiffAt_const)).mul contDiffAt_const).div hden hdenzero

/-- The apparent center singularity is removed by the positive radial support gap. -/
theorem contDiff_poissonCollarValue (c z : ℂ) (ρ ε : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (q : ℝ → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hqs : tsupport q ⊆ Ioo 0 ε) :
    ContDiff ℝ (⊤ : ℕ∞) (poissonCollarValue c z ρ hρ hz q) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : w = c
  · subst w
    have heq : poissonCollarValue c z ρ hρ hz q =ᶠ[𝓝 c] (fun _ => (0 : ℝ)) :=
      eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self hρ))
        (fun v hv => poissonCollarValue_eq_zero_inside c z ρ ε hρ hz q hqs hv)
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · exact contDiffAt_poissonCollarValue_of_ne c z ρ hρ hz q hq hw

/-- The literal Cartesian density `DOZZ.poissonCollarValue` is an actual compactly supported smooth
test. -/
noncomputable def poissonCollarTest (c z : ℂ) (ρ ε : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (q : ℝ → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hqs : tsupport q ⊆ Ioo 0 ε) : TestFn :=
  ⟨poissonCollarValue c z ρ hρ hz q,
    contDiff_poissonCollarValue c z ρ ε hρ hz q hq hqs,
    poissonCollarValue_hasCompactSupport c z ρ ε hρ hz q hqs, subset_univ _⟩

/-- The test has exactly the pointwise value `DOZZ.poissonCollarValue`. -/
theorem poissonCollarTest_apply (c z : ℂ) (ρ ε : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (q : ℝ → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hqs : tsupport q ⊆ Ioo 0 ε) (w : ℂ) :
    poissonCollarTest c z ρ ε hρ hz q hq hqs w = poissonCollarValue c z ρ hρ hz q w := rfl

/-- A collar of one disk stays outside every separated disk. -/
theorem tsupport_poissonCollarTest_exterior {n : ℕ} (c : Fin n → ℂ) (ρ ε δ : ℝ)
    (hρ : 0 < ρ) (hεδ : ε < δ/2)
    (hsep : ∀ i j, i ≠ j → 2*ρ+δ ≤ dist (c i) (c j))
    (i : Fin n) (z : ℂ) (hz : z ∈ ball (c i) ρ) (q : ℝ → ℝ)
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hqs : tsupport q ⊆ Ioo 0 ε) :
    tsupport (poissonCollarTest (c i) z ρ ε hρ hz q hq hqs) ⊆ (⋃ j, ball (c j) ρ)ᶜ := by
  intro w hw
  have hann := tsupport_poissonCollarValue_annulus (c i) z ρ ε hρ hz q hqs hw
  simp only [mem_compl_iff, mem_iUnion]
  rintro ⟨j, hj⟩
  have hjdist : dist w (c j) < ρ := hj
  have hidist : dist w (c i) < ρ+ε := by simpa only [dist_eq_norm] using hann.2
  by_cases hij : i = j
  · subst j
    have hwρ : ρ < dist w (c i) := by simpa only [dist_eq_norm] using hann.1
    exact (hwρ.trans hjdist).false
  · have hs := hsep i j hij
    have ht := dist_triangle (c i) w (c j)
    rw [dist_comm (c i) w] at ht
    have hlo : ρ < dist w (c i) := by simpa only [dist_eq_norm] using hann.1
    linarith


/-- The width of every radial approximation is at most the original collar width. -/
theorem poissonCollarWidth_le (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ε/((k : ℝ)+1) ≤ ε := by
  exact div_le_self hε.le (by linarith [Nat.cast_nonneg (α := ℝ) k])

/-- All collars stay strictly inside the prescribed exterior pin circle. -/
theorem tsupport_poissonCollarTest_inside_pin (c z : ℂ) (ρ ε δ R : ℝ)
    (hρ : 0 < ρ) (hεδ : ε < δ) (hc : ‖c‖+ρ+δ ≤ R)
    (hz : z ∈ ball c ρ) (q : ℝ → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hqs : tsupport q ⊆ Ioo 0 ε) :
    tsupport (poissonCollarTest c z ρ ε hρ hz q hq hqs) ⊆ ball (0 : ℂ) R := by
  intro w hw
  have hann := tsupport_poissonCollarValue_annulus c z ρ ε hρ hz q hqs hw
  have hn : ‖w‖ ≤ ‖w-c‖+‖c‖ := by
    simpa only [sub_add_cancel] using norm_add_le (w-c) c
  have hwr : ‖w‖ < R := by linarith [hann.2]
  simpa only [mem_ball, dist_zero_right] using hwr

/-- Inside the pin circle the literal exterior kernel is the uncurved logarithmic kernel. -/
theorem exteriorPinnedKernel_eq_log_sub {R : ℝ} (hR : 0 < R) {v w : ℂ}
    (hv : ‖v‖ ≤ R) (hw : ‖w‖ ≤ R) :
    exteriorPinnedKernel R hR v w = Real.log R - Real.log ‖v-w‖ := by
  simp only [exteriorPinnedKernel, max_eq_right hv, max_eq_right hw]
  ring


/-- The Poisson numerator is positive at every point of the open disk. -/
theorem poissonNumerator_pos (c z : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hz : z ∈ ball c ρ) :
    0 < ρ^2-‖z-c‖^2 := by
  have hzn : ‖z-c‖ < ρ := by simpa only [mem_ball, dist_eq_norm] using hz
  have hn := norm_nonneg (z-c)
  nlinarith

/-- A nonnegative radial density gives a nonnegative Cartesian Poisson collar. -/
theorem poissonCollarValue_nonneg (c z : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (q : ℝ → ℝ) (hq : ∀ t, 0 ≤ q t) (w : ℂ) :
    0 ≤ poissonCollarValue c z ρ hρ hz q w := by
  apply div_nonneg
  · exact mul_nonneg (hq _) (poissonNumerator_pos c z ρ hρ hz).le
  · positivity



/-- A radially parametrized boundary displacement has the expected norm. -/
theorem norm_poissonPolarPoint_sub (c : ℂ) (u θ : ℝ) (hu : 0 ≤ u) :
    ‖c+(u : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)-c‖ = u := by
  rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hu, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- Radial projection of a positive polar radius removes that radius exactly. -/
theorem poissonBoundaryDirection_polar (c : ℂ) (ρ u θ : ℝ) (hu : 0 < u) :
    (ρ : ℂ)*((c+(u : ℂ)*Complex.exp ((θ : ℂ)*Complex.I))-c) /
      (‖(c+(u : ℂ)*Complex.exp ((θ : ℂ)*Complex.I))-c‖ : ℂ) =
      (ρ : ℂ)*Complex.exp ((θ : ℂ)*Complex.I) := by
  rw [norm_poissonPolarPoint_sub c u θ hu.le, add_sub_cancel_left]
  field_simp [Complex.ofReal_ne_zero.mpr hu.ne']


/-- Boundary distance has a uniform positive lower bound on each compact inner disk. -/
theorem poissonBoundary_norm_lower (c z w : ℂ) (ρ a : ℝ) (hρ : 0 < ρ)
    (hz : ‖z-c‖ ≤ a) (hw : w ≠ c) :
    ρ-a ≤ ‖c+(ρ : ℂ)*(w-c)/(‖w-c‖ : ℂ)-z‖ := by
  let b := (ρ : ℂ)*(w-c)/(‖w-c‖ : ℂ)
  have hb : ‖b‖ = ρ := norm_poissonBoundaryDirection c w ρ hρ hw
  have htri : ‖b‖ ≤ ‖c+b-z‖+‖z-c‖ := by
    have h := norm_add_le (c+b-z) (z-c)
    have he : c+b-z+(z-c) = b := by ring
    rwa [he] at h
  change ρ-a ≤ ‖c+b-z‖
  linarith


/-- The radial collar widths tend to zero. -/
theorem tendsto_poissonCollarWidth (ε : ℝ) :
    Tendsto (fun k : ℕ => ε/((k : ℝ)+1)) atTop (𝓝 0) := by
  have h := (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) ε).comp
    (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h



/-- The squared Poisson denominator is uniformly positive on compact inner disks. -/
theorem poissonBoundary_norm_sq_lower (c z w : ℂ) (ρ a : ℝ) (hρ : 0 < ρ)
    (haρ : a < ρ) (hz : ‖z-c‖ ≤ a) (hw : w ≠ c) :
    0 < (ρ-a)^2 ∧ (ρ-a)^2 ≤ ‖c+(ρ : ℂ)*(w-c)/(‖w-c‖ : ℂ)-z‖^2 := by
  have hgap : 0 < ρ-a := sub_pos.mpr haρ
  have hlow := poissonBoundary_norm_lower c z w ρ a hρ hz hw
  exact ⟨sq_pos_of_pos hgap, pow_le_pow_left₀ hgap.le hlow 2⟩

/-- The boundary Poisson weight has a deterministic compact-set bound. -/
theorem poissonBoundaryWeight_le (c z w : ℂ) (ρ a : ℝ) (hρ : 0 < ρ)
    (haρ : a < ρ) (hz : ‖z-c‖ ≤ a) (hw : w ≠ c) :
    (ρ^2-‖z-c‖^2) / ‖c+(ρ : ℂ)*(w-c)/(‖w-c‖ : ℂ)-z‖^2 ≤
      ρ^2/(ρ-a)^2 := by
  have hden := poissonBoundary_norm_sq_lower c z w ρ a hρ haρ hz hw
  have hn : ρ^2-‖z-c‖^2 ≤ ρ^2 := sub_le_self _ (sq_nonneg _)
  calc
    _ ≤ ρ^2/‖c+(ρ : ℂ)*(w-c)/(‖w-c‖ : ℂ)-z‖^2 :=
      div_le_div_of_nonneg_right hn (sq_nonneg _)
    _ ≤ ρ^2/(ρ-a)^2 :=
      div_le_div_of_nonneg_left (sq_nonneg _) hden.1 hden.2





/-- The boundary Poisson weight has normalized circle average one. -/
theorem circleAverage_poissonKernel_eq_one (c z : ℂ) (ρ : ℝ)
    (hz : z ∈ ball c ρ) : Real.circleAverage (poissonKernel c z) c ρ = 1 := by
  have h := (InnerProductSpace.harmonicOnNhd_const (1 : ℝ)
    (s := closedBall c ρ)).circleAverage_poissonKernel_smul hz
  simpa only [Pi.smul_def, smul_eq_mul, Pi.mul_def, mul_one] using h

end DOZZ.Proofs
