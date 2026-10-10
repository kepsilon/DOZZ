/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitKernel
public import DOZZ.Brownian.Williams.ConditionedBandFinite

/-!
# Full-future avoidance shift for the Brownian reference law

Under the exact negative-drift Brownian law conditioned below an upper level, avoiding a lower
level is the same event as conditioning below the reduced upper level. This proves the all-path
shift identity directly from the actual infinite-survival measures, without restarting at a
random last-exit time.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- A path lies strictly below a fixed upper level at every nonnegative time. -/
def brownianPathStrictlyBelow (x : ℝ) : Set BrownianPath :=
  {q | ∀ t : ℝ≥0, q t < x}

/-- Reflect an upper-conditioned negative-drift path to a positive path started at `x`. -/
def brownianUpperConditionedPositivePath (x : ℝ) (q : BrownianPath) : BrownianPath :=
  ⟨fun t => x - q t, continuous_const.sub q.continuous⟩

theorem measurable_brownianUpperConditionedPositivePath (x : ℝ) :
    Measurable (brownianUpperConditionedPositivePath x) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact measurable_const.sub (ContinuousMap.measurable_eval t)

private theorem conditionedH_pos_of_pos {ν x : ℝ} (hν : 0 < ν) (hx : 0 < x) :
    0 < conditionedH ν x := by
  rw [conditionedH, ite_eq_right hν.ne']
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  nlinarith

/-- For the actual Brownian reference law, strict avoidance of `c` by the positive path started
at `x` has mass `a_c(x)`, and after shifting down by `c` its entire future path law is the same
upper-conditioned reference law started at `x-c`. The identity is for every measurable
nonnegative full-path test. -/
theorem brownianBelowConditionedLaw_avoidance_shift_integral
    (B : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) B)
    (ν c x : ℝ) (hν : 0 < ν) (hc : 0 < c) (hcx : c < x)
    (F : BrownianPath → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ q in brownianPathStrictlyBelow (x - c),
        F (brownianUpperConditionedPositivePath (x - c) q) ∂
          brownianBelowConditionedLaw B ν x) =
      ENNReal.ofReal (lastExitAvoidanceFactor ν c x) *
        ∫⁻ q, F (brownianUpperConditionedPositivePath (x - c) q) ∂
          brownianBelowConditionedLaw B ν (x - c) := by
  have _ := hB
  let hx : ℝ := conditionedH ν x
  let hxc : ℝ := conditionedH ν (x - c)
  have hxpos : 0 < hx := conditionedH_pos_of_pos hν (lt_trans hc hcx)
  have hxcpos : 0 < hxc := conditionedH_pos_of_pos hν (sub_pos.mpr hcx)
  have hset : MeasurableSet (brownianPathStrictlyBelow (x - c)) :=
    measurableSet_brownianPath_below (x - c)
  have hD : Measurable (driftedBrownianPath (-ν)) :=
    continuous_driftedBrownianPath.measurable.comp
      (measurable_const.prodMk measurable_id)
  have hF' : Measurable (fun q : BrownianPath =>
      F (brownianUpperConditionedPositivePath (x - c) q)) :=
    hF.comp (measurable_brownianUpperConditionedPositivePath (x - c))
  have hF'' : Measurable (fun p : BrownianPath =>
      F (brownianUpperConditionedPositivePath (x - c) (driftedBrownianPath (-ν) p))) :=
    hF'.comp hD
  have htest : Measurable ((brownianPathStrictlyBelow (x - c)).indicator
      (fun q => F (brownianUpperConditionedPositivePath (x - c) q))) :=
    hF'.indicator hset
  have hraw (a : ℝ) : MeasurableSet
      {p : BrownianPath | ∀ t : ℝ≥0, driftedBrownianPath (-ν) p t < a} :=
    (measurableSet_brownianPath_below a).preimage hD
  have hsub : {p : BrownianPath | ∀ t : ℝ≥0,
      driftedBrownianPath (-ν) p t < x - c} ⊆
      {p : BrownianPath | ∀ t : ℝ≥0,
        driftedBrownianPath (-ν) p t < x} := by
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp ⊢
    intro t
    exact (hp t).trans (by linarith)
  have hrawIntegrand :
      ({p : BrownianPath | ∀ t : ℝ≥0,
          driftedBrownianPath (-ν) p t < x}).indicator
        (fun p => (brownianPathStrictlyBelow (x - c)).indicator
          (fun q => F (brownianUpperConditionedPositivePath (x - c) q))
          (driftedBrownianPath (-ν) p)) =
      ({p : BrownianPath | ∀ t : ℝ≥0,
          driftedBrownianPath (-ν) p t < x - c}).indicator
        (fun p => F (brownianUpperConditionedPositivePath (x - c)
          (driftedBrownianPath (-ν) p))) := by
    funext p
    by_cases hp : p ∈ {p : BrownianPath | ∀ t : ℝ≥0,
        driftedBrownianPath (-ν) p t < x - c}
    · have hp' : p ∈ {p : BrownianPath | ∀ t : ℝ≥0,
          driftedBrownianPath (-ν) p t < x} := hsub hp
      have hq : driftedBrownianPath (-ν) p ∈ brownianPathStrictlyBelow (x - c) := by
        simpa [brownianPathStrictlyBelow] using hp
      simp [hp, hp', hq]
    · have hq : driftedBrownianPath (-ν) p ∉ brownianPathStrictlyBelow (x - c) := by
        simpa [brownianPathStrictlyBelow] using hp
      simp [hp, hq]
  have hcoeff : ENNReal.ofReal (hxc / hx) * (ENNReal.ofReal hxc)⁻¹ =
      (ENNReal.ofReal hx)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos hxpos, div_eq_mul_inv]
    have ha0 : ENNReal.ofReal hxc ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr hxcpos)
    have hatop : ENNReal.ofReal hxc ≠ ∞ := ENNReal.ofReal_ne_top
    calc
      (ENNReal.ofReal hxc * (ENNReal.ofReal hx)⁻¹) *
          (ENNReal.ofReal hxc)⁻¹ =
        (ENNReal.ofReal hx)⁻¹ *
          (ENNReal.ofReal hxc * (ENNReal.ofReal hxc)⁻¹) := by ac_rfl
      _ = (ENNReal.ofReal hx)⁻¹ := by
        rw [ENNReal.mul_inv_cancel ha0 hatop, mul_one]
  have hfactor : lastExitAvoidanceFactor ν c x = hxc / hx := by
    simp [lastExitAvoidanceFactor, hx, hxc, hcx]
  calc
    (∫⁻ q in brownianPathStrictlyBelow (x - c),
        F (brownianUpperConditionedPositivePath (x - c) q) ∂
          brownianBelowConditionedLaw B ν x) =
        ∫⁻ q, (brownianPathStrictlyBelow (x - c)).indicator
        (fun q => F (brownianUpperConditionedPositivePath (x - c) q)) q ∂
          brownianBelowConditionedLaw B ν x := by
        rw [lintegral_indicator hset]
    _ = (ENNReal.ofReal hx)⁻¹ *
        ∫⁻ p in {p : BrownianPath | ∀ t : ℝ≥0,
          driftedBrownianPath (-ν) p t < x - c},
            F (brownianUpperConditionedPositivePath (x - c)
              (driftedBrownianPath (-ν) p)) ∂B := by
        rw [lintegral_brownianBelowConditionedLaw B ν x _ htest]
        rw [← lintegral_indicator (hraw x)]
        congr 1
        rw [hrawIntegrand]
        rw [lintegral_indicator (hraw (x - c))]
    _ = (ENNReal.ofReal hx)⁻¹ *
        ((ENNReal.ofReal hxc) *
          ∫⁻ q, F (brownianUpperConditionedPositivePath (x - c) q) ∂
            brownianBelowConditionedLaw B ν (x - c)) := by
        rw [brownianPath_below_lintegral_eq_conditioned B ν (x - c)
          hν (sub_pos.mpr hcx)
          (fun q => F (brownianUpperConditionedPositivePath (x - c) q)) hF']
    _ = ENNReal.ofReal (lastExitAvoidanceFactor ν c x) *
        ∫⁻ q, F (brownianUpperConditionedPositivePath (x - c) q) ∂
          brownianBelowConditionedLaw B ν (x - c) := by
        have hA0 : ENNReal.ofReal hxc ≠ 0 :=
          ne_of_gt (ENNReal.ofReal_pos.mpr hxcpos)
        have hAtop : ENNReal.ofReal hxc ≠ ∞ := ENNReal.ofReal_ne_top
        rw [hfactor]
        calc
          (ENNReal.ofReal hx)⁻¹ *
              (ENNReal.ofReal hxc *
                ∫⁻ q, F (brownianUpperConditionedPositivePath (x - c) q) ∂
                  brownianBelowConditionedLaw B ν (x - c)) =
            ((ENNReal.ofReal hx)⁻¹ * ENNReal.ofReal hxc) *
                ∫⁻ q, F (brownianUpperConditionedPositivePath (x - c) q) ∂
                  brownianBelowConditionedLaw B ν (x - c) := by ac_rfl
          _ = ENNReal.ofReal (hxc / hx) *
                ∫⁻ q, F (brownianUpperConditionedPositivePath (x - c) q) ∂
                  brownianBelowConditionedLaw B ν (x - c) := by
            calc
              ((ENNReal.ofReal hx)⁻¹ * ENNReal.ofReal hxc) *
                  ∫⁻ q, F (brownianUpperConditionedPositivePath (x - c) q) ∂
                    brownianBelowConditionedLaw B ν (x - c) =
                ((ENNReal.ofReal (hxc / hx) * (ENNReal.ofReal hxc)⁻¹) *
                    ENNReal.ofReal hxc) *
                  ∫⁻ q, F (brownianUpperConditionedPositivePath (x - c) q) ∂
                    brownianBelowConditionedLaw B ν (x - c) := by rw [hcoeff]
              _ = ENNReal.ofReal (hxc / hx) *
                  ∫⁻ q, F (brownianUpperConditionedPositivePath (x - c) q) ∂
                    brownianBelowConditionedLaw B ν (x - c) := by
                congr 1
                calc
                  (ENNReal.ofReal (hxc / hx) * (ENNReal.ofReal hxc)⁻¹) *
                      ENNReal.ofReal hxc =
                    ENNReal.ofReal (hxc / hx) *
                      ((ENNReal.ofReal hxc)⁻¹ * ENNReal.ofReal hxc) := by ac_rfl
                  _ = ENNReal.ofReal (hxc / hx) := by
                    rw [ENNReal.inv_mul_cancel hA0 hAtop, mul_one]

end DOZZ.Proofs

end
