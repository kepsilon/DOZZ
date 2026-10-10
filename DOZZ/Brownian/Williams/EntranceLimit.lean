/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Williams.ConditionedBandFinite
public import DOZZ.Brownian.LastExitFDDMarkov
public import DOZZ.Statements.Brownian.ConditionedPositiveEntranceDensity
public import Mathlib.Analysis.Calculus.Deriv.Slope
/-!
# The actual Williams band future converges to the entrance law

The scalar Doob transition converges at a zero initial state by the ratio
of the derivatives of its killed numerator and its harmonic denominator.
Only the first factor of a finite Doob chain varies with the initial state.
Reflection and the characterization `DOZZ.IsNegativeConditionedBrownianLaw`
identify its limit with every version of the negative conditioned entrance
law.

The overlap of two probability densities controls all bounded tests,
including tests translated with the initial state. This gives convergence
of the actual normalized upper-conditioned Brownian future on every finite
continuous cylinder. No last-exit identity is used in this identification.
-/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace DOZZ.Proofs

private theorem heat_start_derivative (t y : ℝ) (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => brownianHeatDensity t (y-x)-brownianHeatDensity t (y+x))
      (2*y/t*brownianHeatDensity t y) 0 := by
  have hargL : HasDerivAt (fun x : ℝ => y-x) (-1) 0 := by
    convert (hasDerivAt_const (0 : ℝ) y).sub (hasDerivAt_id 0) using 1 <;> first | rfl | norm_num
  have hargR : HasDerivAt (fun x : ℝ => y+x) 1 0 := by
    convert (hasDerivAt_const (0 : ℝ) y).add (hasDerivAt_id 0) using 1 <;> first | rfl | norm_num
  have hleft : HasDerivAt (fun x : ℝ => Real.exp (-((y-x)^2)/(2*t)))
      (Real.exp (-y^2/(2*t))*(y/t)) 0 := by
    convert ((hargL.pow 2).neg.div_const (2*t)).exp using 1
    simp only [Pi.neg_apply,Pi.pow_apply,sub_zero,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_neg_one,neg_neg]
    field_simp
  have hright : HasDerivAt (fun x : ℝ => Real.exp (-((y+x)^2)/(2*t)))
      (Real.exp (-y^2/(2*t))*(-y/t)) 0 := by
    convert ((hargR.pow 2).neg.div_const (2*t)).exp using 1
    simp only [Pi.neg_apply,Pi.pow_apply,add_zero,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]
    field_simp
  have hh := (hleft.div_const (Real.sqrt (2*Real.pi*t))).sub (hright.div_const (Real.sqrt (2*Real.pi*t)))
  convert hh using 1
  · funext x
    simp only [brownianHeatDensity,ht,ite_eq_left,Pi.sub_apply]
  · simp only [brownianHeatDensity,ht,ite_eq_left]
    field_simp
    ring

private theorem harmonic_start_derivative (ν : ℝ) (hν : 0 < ν) :
    HasDerivAt (conditionedH ν) (2*ν) 0 := by
  have harg : HasDerivAt (fun x : ℝ => Real.exp (-2*ν*x)) (-2*ν) 0 := by
    simpa only [id_eq,mul_zero,Real.exp_zero,mul_one,one_mul] using
      ((hasDerivAt_id (0 : ℝ)).const_mul (-2*ν)).exp
  have hh := (hasDerivAt_const (0 : ℝ) 1).sub harg
  convert hh using 1
  · funext x
    simp only [conditionedH,ite_eq_right hν.ne',Pi.sub_apply]
  · ring

/-- The positive-start Doob transition density tends to the entrance density. -/
theorem conditionedPositiveTransitionDensity_tendsto_entrance (ν t y : ℝ)
    (hν : 0 < ν) (ht : 0 < t) :
    Tendsto (fun x => conditionedPositiveTransitionDensity ν t x y)
      (𝓝[>] (0 : ℝ)) (𝓝 (conditionedPositiveEntranceDensity ν t y)) := by
  by_cases hy : 0 < y
  · have hnum := (heat_start_derivative t y ht).tendsto_slope_zero_right
    have hden := (harmonic_start_derivative ν hν).tendsto_slope_zero_right
    simp only [zero_add,brownianHeatDensity,ht,ite_eq_left,sub_zero,add_zero,sub_self] at hnum
    simp only [zero_add,conditionedH,ite_eq_right hν.ne',mul_zero,Real.exp_zero,sub_self,sub_zero] at hden
    have hquot := hnum.div hden (by positivity : (2*ν : ℝ) ≠ 0)
    have hexp : Tendsto (fun x : ℝ => Real.exp (ν*(y-x)-ν^2*t/2)) (𝓝[>] 0)
        (𝓝 (Real.exp (ν*y-ν^2*t/2))) := by
      have hc : Continuous (fun x : ℝ => Real.exp (ν*(y-x)-ν^2*t/2)) := by fun_prop
      simpa only [sub_zero] using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    have hprod := (hexp.mul hquot).mul_const (conditionedH ν y)
    have he : (fun x : ℝ => conditionedPositiveTransitionDensity ν t x y) =ᶠ[𝓝[>] 0]
        (fun x => Real.exp (ν*(y-x)-ν^2*t/2)*
          (((brownianHeatDensity t (y-x)-brownianHeatDensity t (y+x))/x)/(conditionedH ν x/x))*conditionedH ν y) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : 0 < x := hx
      simp only [conditionedPositiveTransitionDensity,hν.le,ht,hx',hy,and_self,ite_eq_left]
      field_simp [hx'.ne']
    apply (tendsto_congr' he).mpr
    convert hprod using 1
    · funext x
      simp only [brownianHeatDensity,ht,ite_eq_left,Pi.div_apply,smul_eq_mul,div_eq_mul_inv,
        conditionedH,ite_eq_right hν.ne']
      ring
    · apply congrArg nhds
      rw [conditionedPositiveEntranceDensity_eq_firstHit ν t y hν ht hy,
        brownianFirstHitDensity_heat ν y t ht,brownianHeatDensity,ite_eq_left ht]
      field_simp
  · have he : (fun x : ℝ => conditionedPositiveTransitionDensity ν t x y) = fun _ => 0 := by
      funext x
      simp [conditionedPositiveTransitionDensity,hy]
    rw [he]
    simpa only [conditionedPositiveEntranceDensity,hy,and_false,ite_false] using
      (tendsto_const_nhds (x := (0 : ℝ)))


/-- Probability densities converging pointwise transport uniformly bounded moving tests. -/
private theorem density_test_limit {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (f : ℕ → E → ℝ≥0∞) (g : E → ℝ≥0∞) (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hfm : ∀ n, (∫⁻ x, f n x ∂μ) = 1) (hgm : (∫⁻ x, g x ∂μ) = 1)
    (hfg : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (φ : ℕ → E → ℝ≥0∞) (ψ : E → ℝ≥0∞) (hφ : ∀ n, Measurable (φ n))
    (K : ℝ≥0∞) (hK : K ≠ ∞) (hbound : ∀ n x, φ n x ≤ K)
    (hlim : ∀ x, Tendsto (fun n => φ n x) atTop (𝓝 (ψ x))) :
    Tendsto (fun n => ∫⁻ x, f n x*φ n x ∂μ) atTop (𝓝 (∫⁻ x, g x*ψ x ∂μ)) := by
  let A : ℕ → E → ℝ≥0∞ := fun n x => min (f n x) (g x)
  have hA (n : ℕ) : Measurable (A n) := (hf n).min hg
  have hAm (n : ℕ) : (∫⁻ x, A n x ∂μ) ≠ ∞ := ne_top_of_le_ne_top
    (hgm ▸ ENNReal.one_ne_top) (lintegral_mono (fun x => min_le_right _ _))
  have hAlim (x : E) : Tendsto (fun n => A n x) atTop (𝓝 (g x)) := by
    simpa only [min_self] using (hfg x).min (tendsto_const_nhds (x := g x))
  have hJ : Tendsto (fun n => ∫⁻ x, A n x ∂μ) atTop (𝓝 1) := by
    rw [← hgm]
    exact tendsto_lintegral_of_dominated_convergence g hA
      (fun n => ae_of_all _ (fun x => min_le_right _ _)) (hgm ▸ ENNReal.one_ne_top)
        (ae_of_all _ hAlim)
  have hψbound (x : E) : ψ x ≤ K := le_of_tendsto (hlim x)
    (Filter.Eventually.of_forall (fun n => hbound n x))
  have hKg : Measurable (fun x => K*g x) := measurable_const.mul hg
  have hKgfin : (∫⁻ x, K*g x ∂μ) ≠ ∞ := by rw [lintegral_const_mul K hg,hgm,mul_one]; exact hK
  have hAP (n : ℕ) : Measurable (fun x => A n x*φ n x) := (hA n).mul (hφ n)
  have hT : Tendsto (fun n => ∫⁻ x, A n x*φ n x ∂μ) atTop (𝓝 (∫⁻ x, g x*ψ x ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun x => K*g x) hAP ?_ hKgfin ?_
    · intro n
      exact ae_of_all _ (fun x => (mul_le_mul' (min_le_right _ _) (hbound n x)).trans_eq (mul_comm _ _))
    · filter_upwards [ae_lt_top hg (hgm ▸ ENNReal.one_ne_top)] with x hx
      exact ENNReal.Tendsto.mul (hAlim x) (Or.inr (ne_top_of_le_ne_top hK (hψbound x)))
        (hlim x) (Or.inr hx.ne)
  have hres : Tendsto (fun n => K*(1-∫⁻ x, A n x ∂μ)) atTop (𝓝 0) := by
    have hh := ENNReal.Tendsto.const_mul
      (ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞))) hJ (Or.inl ENNReal.one_ne_top))
      (Or.inr hK)
    simpa only [tsub_self,mul_zero] using hh
  have hupper (n : ℕ) : (∫⁻ x, f n x*φ n x ∂μ) ≤
      (∫⁻ x, A n x*φ n x ∂μ)+K*(1-∫⁻ x, A n x ∂μ) := by
    have hdecomp : (fun x => f n x*φ n x) =
        (fun x => A n x*φ n x+(f n x-A n x)*φ n x) := by
      funext x
      rw [← add_mul,add_tsub_cancel_of_le (min_le_left _ _)]
    rw [hdecomp,lintegral_add_left (hAP n)]
    apply add_le_add le_rfl
    calc
      _ ≤ ∫⁻ x, K*(f n x-A n x) ∂μ := lintegral_mono (fun x =>
        (mul_le_mul' le_rfl (hbound n x)).trans_eq (mul_comm _ _))
      _ = K*(1-∫⁻ x, A n x ∂μ) := by
        have hm : Measurable (fun x => f n x-A n x) := (hf n).sub (hA n)
        rw [lintegral_const_mul K hm,lintegral_sub (hA n) (hAm n)
          (ae_of_all _ (fun x => min_le_left _ _)),hfm n]
  have hI : (∫⁻ x, g x*ψ x ∂μ) ≤ K := by
    calc
      _ ≤ ∫⁻ x, K*g x ∂μ := lintegral_mono (fun x => (mul_le_mul' le_rfl (hψbound x)).trans_eq (mul_comm _ _))
      _ = K := by rw [lintegral_const_mul K hg,hgm,mul_one]
  have hTop : Tendsto (fun n => (∫⁻ x, A n x*φ n x ∂μ)+K*(1-∫⁻ x, A n x ∂μ)) atTop
      (𝓝 (∫⁻ x, g x*ψ x ∂μ)) := by
    simpa only [add_zero] using hT.add hres
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hT hTop
    (fun n => lintegral_mono (fun x => mul_le_mul' (min_le_left _ _) le_rfl)) hupper

private theorem transition_nonneg (ν : ℝ) (t : ℝ≥0) (x y : ℝ) (hν : 0 < ν) (ht : 0 < t) :
    0 ≤ conditionedPositiveTransitionDensity ν t x y := by
  by_cases hx : 0 < x
  · rw [conditionedPositiveTransitionDensity_eq_killed ν hν t ht x y hx]
    by_cases hy : 0 < y
    · have hh : 0 < conditionedH ν y := by
        rw [conditionedH,ite_eq_right hν.ne']
        exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
      have hhx : 0 < conditionedH ν x := by
        rw [conditionedH,ite_eq_right hν.ne']
        exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
      exact div_nonneg (mul_nonneg (brownianKilledTransitionPDF_nonneg ν t ht.ne' x y) hh.le) hhx.le
    · simp only [brownianKilledTransitionPDF,hy,and_false,ite_false,zero_mul,zero_div,le_refl]
  · simp only [conditionedPositiveTransitionDensity,hx,false_and,and_false,ite_false,le_refl]

private theorem entrance_nonneg (ν t y : ℝ) (hν : 0 < ν) (ht : 0 < t) :
    0 ≤ conditionedPositiveEntranceDensity ν t y := by
  by_cases hy : 0 < y
  · rw [conditionedPositiveEntranceDensity_eq_firstHit ν t y hν ht hy]
    have hh : 0 < conditionedH ν y := by
      rw [conditionedH,ite_eq_right hν.ne']
      exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
    exact div_nonneg (mul_nonneg hh.le (brownianFirstHitDensity_nonneg ν y t hy.le)) hν.le
  · simp only [conditionedPositiveEntranceDensity,hy,and_false,ite_false,le_refl]

/-- The entrance factor followed by the elapsed-schedule Doob transition product. -/
noncomputable def brownianEntranceFinitePDF (ν : ℝ) :
    (n : ℕ) → (Fin n → ℝ≥0) → (Fin n → ℝ) → ℝ≥0∞
  | 0, _, _ => 1
  | n+1, ds, ys => ENNReal.ofReal (conditionedPositiveEntranceDensity ν (ds 0) (ys 0))*
      brownianDoobFinitePDF ν n (Fin.tail ds) (ys 0) (Fin.tail ys)

private theorem doob_chain_eq (ν : ℝ) (hν : 0 < ν) (n : ℕ) (ds : Fin n → ℝ≥0)
    (hds : ∀ i, 0 < ds i) (t x : ℝ) (ys : Fin n → ℝ) :
    ENNReal.ofReal (conditionedPositiveTimeChainDensity ν t x
      (List.ofFn fun i => t+(brownianFirstHitTimes n ds i : ℝ)) (List.ofFn ys)) =
        brownianDoobFinitePDF ν n ds x ys := by
  induction n generalizing t x with
  | zero => simp [conditionedPositiveTimeChainDensity,brownianDoobFinitePDF]
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ]
    simp only [brownianFirstHitTimes,Fin.cons_zero,Fin.cons_succ,NNReal.coe_add,
      conditionedPositiveTimeChainDensity,add_sub_cancel_left]
    rw [ENNReal.ofReal_mul (transition_nonneg ν (ds 0) x (ys 0) hν (hds 0))]
    change _ * ENNReal.ofReal (conditionedPositiveTimeChainDensity ν (t+(ds 0 : ℝ)) (ys 0)
      (List.ofFn fun i => t+((ds 0 : ℝ)+(brownianFirstHitTimes n (Fin.tail ds) i : ℝ)))
      (List.ofFn (Fin.tail ys))) = _
    simp_rw [← add_assoc]
    rw [ih (Fin.tail ds) (fun i => hds i.succ) (t+(ds 0 : ℝ)) (ys 0) (Fin.tail ys)]
    rfl

/-- The entrance factor followed by the elapsed-schedule Doob transition product. -/
theorem brownianEntranceFinitePDF_eq_conditionedPositiveFDDDensity (ν : ℝ) (hν : 0 < ν) (n : ℕ)
    (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i) (ys : Fin n → ℝ) :
    brownianEntranceFinitePDF ν n ds ys = ENNReal.ofReal (conditionedPositiveFDDDensity ν
      (List.ofFn fun i => (brownianFirstHitTimes n ds i : ℝ)) (List.ofFn ys)) := by
  cases n with
  | zero => simp [brownianEntranceFinitePDF,conditionedPositiveFDDDensity]
  | succ n =>
    rw [List.ofFn_succ,List.ofFn_succ]
    simp only [brownianFirstHitTimes,Fin.cons_zero,Fin.cons_succ,NNReal.coe_add,
      conditionedPositiveFDDDensity]
    change ENNReal.ofReal (conditionedPositiveEntranceDensity ν (ds 0) (ys 0)) *
      brownianDoobFinitePDF ν n (Fin.tail ds) (ys 0) (Fin.tail ys) =
      ENNReal.ofReal (conditionedPositiveEntranceDensity ν (ds 0) (ys 0)*
        conditionedPositiveTimeChainDensity ν (ds 0) (ys 0)
          (List.ofFn fun i => (ds 0 : ℝ)+(brownianFirstHitTimes n (Fin.tail ds) i : ℝ))
          (List.ofFn (Fin.tail ys)))
    rw [ENNReal.ofReal_mul (entrance_nonneg ν (ds 0) (ys 0) hν (hds 0)),
      doob_chain_eq ν hν n (Fin.tail ds) (fun i => hds i.succ) (ds 0) (ys 0) (Fin.tail ys)]

/-- Every finite Doob product is finite, including states outside its support. -/
theorem brownianDoobFinitePDF_ne_top (ν : ℝ) (n : ℕ) (ds : Fin n → ℝ≥0) (x : ℝ)
    (ys : Fin n → ℝ) : brownianDoobFinitePDF ν n ds x ys ≠ ∞ := by
  induction n generalizing x with
  | zero => exact ENNReal.one_ne_top
  | succ n ih =>
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ih (Fin.tail ds) (ys 0) (Fin.tail ys))

/-- Only the first transition changes when the initial state tends to zero. -/
theorem brownianDoobFinitePDF_tendsto_entrance (ν : ℝ) (hν : 0 < ν) (n : ℕ)
    (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i) (ys : Fin n → ℝ) :
    Tendsto (fun x => brownianDoobFinitePDF ν n ds x ys) (𝓝[>] 0)
      (𝓝 (brownianEntranceFinitePDF ν n ds ys)) := by
  cases n with
  | zero => exact tendsto_const_nhds
  | succ n =>
      exact ENNReal.Tendsto.mul_const
        (ENNReal.tendsto_ofReal (conditionedPositiveTransitionDensity_tendsto_entrance ν (ds 0) (ys 0) hν (hds 0)))
        (Or.inr (brownianDoobFinitePDF_ne_top ν n (Fin.tail ds) (ys 0) (Fin.tail ys)))

/-- Entrance products are measurable limits of the actual positive-start densities. -/
theorem measurable_brownianEntranceFinitePDF (ν : ℝ) (hν : 0 < ν) (n : ℕ)
    (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i) :
    Measurable (brownianEntranceFinitePDF ν n ds) := by
  let xs : ℕ → ℝ := fun k => 1/((k : ℝ)+1)
  have hxs (k : ℕ) : 0 < xs k := one_div_pos.mpr (by positivity)
  have hxlim : Tendsto xs atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Filter.Eventually.of_forall hxs⟩
  exact measurable_of_tendsto_metrizable
    (fun k => measurable_brownianDoobFinitePDF ν hν n ds hds (xs k) (hxs k))
    (tendsto_pi_nhds.mpr (fun ys => (brownianDoobFinitePDF_tendsto_entrance ν hν n ds hds ys).comp hxlim))

private theorem negative_pdf_eq (ν : ℝ) (hν : 0 < ν) (n : ℕ)
    (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i) (ys : Fin n → ℝ) :
    ENNReal.ofReal (max 0 (negativeConditionedFDDDensity ν
      (List.ofFn fun i => (brownianFirstHitTimes n ds i : ℝ)) (List.ofFn ys))) =
        brownianEntranceFinitePDF ν n ds (-ys) := by
  rw [brownianEntranceFinitePDF_eq_conditionedPositiveFDDDensity ν hν n ds hds]
  have he : List.ofFn ys = (List.ofFn (-ys)).map (fun y => -y) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    simp only [Function.comp_apply,Pi.neg_apply,neg_neg]
  rw [he,negativeConditionedFDDDensity_reflect,ENNReal.ofReal_max,ENNReal.ofReal_zero,
    max_eq_right (show (0 : ℝ≥0∞) ≤ _ from bot_le)]

/-- The given entrance law has precisely the reflected positive-coordinate density. -/
theorem negativeConditionedLaw_finite_positive_lintegral (Q : Measure BrownianPath)
    (ν : ℝ) (hν : 0 < ν) (hQ : IsNegativeConditionedBrownianLaw ν Q) (n : ℕ)
    (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i) (F : (Fin n → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ q, F (fun i => -q (brownianFirstHitTimes n ds i)) ∂Q) =
      ∫⁻ ys, brownianEntranceFinitePDF ν n ds ys*F ys := by
  let _ := hQ.2.1
  by_cases hn : 0 < n
  · have hmap := hQ.2.2.2 n hn (brownianFirstHitTimes n ds)
      (fun i => brownianFirstHitTimes_pos n ds hds i) (strictMono_brownianFirstHitTimes n ds hds)
    have hEval : Measurable (fun q : BrownianPath => fun i => q (brownianFirstHitTimes n ds i)) :=
      Measurable.of_eval (fun i => ContinuousMap.measurable_eval _)
    have hneg : Measurable (fun ys : Fin n → ℝ => F (-ys)) := hF.comp measurable_neg
    have hm : Measurable (fun ys : Fin n → ℝ => ENNReal.ofReal (max 0
      (negativeConditionedFDDDensity ν (List.ofFn fun i => (brownianFirstHitTimes n ds i : ℝ)) (List.ofFn ys)))) := by
      simp_rw [negative_pdf_eq ν hν n ds hds]
      exact (measurable_brownianEntranceFinitePDF ν hν n ds hds).comp measurable_neg
    calc
      _ = ∫⁻ ys, F (-ys) ∂Q.map (fun q i => q (brownianFirstHitTimes n ds i)) :=
        (lintegral_map hneg hEval).symm
      _ = ∫⁻ ys, brownianEntranceFinitePDF ν n ds (-ys)*F (-ys) := by
        rw [hmap,lintegral_withDensity_eq_lintegral_mul _ hm hneg]
        exact lintegral_congr (fun ys => congrArg (fun a => a*F (-ys)) (negative_pdf_eq ν hν n ds hds ys))
      _ = _ := lintegral_neg_eq_self (fun ys => brownianEntranceFinitePDF ν n ds ys*F ys)
  · have hz : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have he (ys : Fin 0 → ℝ) : ys = Fin.elim0 := Subsingleton.elim _ _
    have hv : (volume : Measure (Fin 0 → ℝ)) univ = 1 := Measure.pi_empty_univ (fun _ : Fin 0 => (volume : Measure ℝ))
    simp only [he,brownianEntranceFinitePDF,one_mul,lintegral_const,measure_univ,hv,mul_one]

/-- The finite entrance density has mass one, as a consequence of the given path law. -/
theorem lintegral_brownianEntranceFinitePDF_one (Q : Measure BrownianPath)
    (ν : ℝ) (hν : 0 < ν) (hQ : IsNegativeConditionedBrownianLaw ν Q) (n : ℕ)
    (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i) :
    (∫⁻ ys, brownianEntranceFinitePDF ν n ds ys) = 1 := by
  let _ := hQ.2.1
  simpa only [mul_one,lintegral_one,measure_univ] using
    (negativeConditionedLaw_finite_positive_lintegral Q ν hν hQ n ds hds (fun _ => 1) measurable_const).symm

/-- Actual upper conditioning tends to the given entrance law on bounded continuous cylinders. -/
theorem brownianBelowConditionedLaw_tendsto_entrance_cylinder (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν : ℝ) (hν : 0 < ν)
    (Q : Measure BrownianPath) (hQ : IsNegativeConditionedBrownianLaw ν Q)
    (xs : ℕ → ℝ) (hxs : ∀ k, 0 < xs k) (hxlim : Tendsto xs atTop (𝓝 0))
    (n : ℕ) (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i)
    (F : (Fin n → ℝ) → ℝ≥0∞) (hF : Continuous F)
    (K : ℝ≥0∞) (hK : K ≠ ∞) (hbound : ∀ ys, F ys ≤ K) :
    Tendsto (fun k => ∫⁻ q, F (fun i => q (brownianFirstHitTimes n ds i))
        ∂brownianBelowConditionedLaw P ν (xs k)) atTop
      (𝓝 (∫⁻ q, F (fun i => q (brownianFirstHitTimes n ds i)) ∂Q)) := by
  have hwithin : Tendsto xs atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨hxlim,Filter.Eventually.of_forall hxs⟩
  let fn : ℕ → (Fin n → ℝ) → ℝ≥0∞ := fun k => brownianDoobFinitePDF ν n ds (xs k)
  let g := brownianEntranceFinitePDF ν n ds
  let φ : ℕ → (Fin n → ℝ) → ℝ≥0∞ := fun k ys => F (fun i => xs k-ys i)
  let ψ : (Fin n → ℝ) → ℝ≥0∞ := fun ys => F (-ys)
  have hφ (k : ℕ) : Measurable (φ k) := hF.measurable.comp
    (Measurable.of_eval (fun i => measurable_const.sub (measurable_pi_apply i)))
  have hψ : Measurable ψ := hF.measurable.comp measurable_neg
  have hφlim (ys : Fin n → ℝ) : Tendsto (fun k => φ k ys) atTop (𝓝 (ψ ys)) := by
    apply hF.continuousAt.tendsto.comp
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [zero_sub,Pi.neg_apply] using hxlim.sub (tendsto_const_nhds (x := ys i))
  have hlim := density_test_limit volume fn g
    (fun k => measurable_brownianDoobFinitePDF ν hν n ds hds (xs k) (hxs k))
    (measurable_brownianEntranceFinitePDF ν hν n ds hds)
    (fun k => lintegral_brownianDoobFinitePDF_one P hB ν hν n ds hds (xs k) (hxs k))
    (lintegral_brownianEntranceFinitePDF_one Q ν hν hQ n ds hds)
    (fun ys => (brownianDoobFinitePDF_tendsto_entrance ν hν n ds hds ys).comp hwithin)
    φ ψ hφ K hK (fun k ys => hbound _) hφlim
  have hactual (k : ℕ) : (∫⁻ ys, fn k ys*φ k ys) =
      ∫⁻ q, F (fun i => q (brownianFirstHitTimes n ds i)) ∂brownianBelowConditionedLaw P ν (xs k) := by
    have hm : Measurable (fun q : BrownianPath => fun i => xs k-q (brownianFirstHitTimes n ds i)) :=
      Measurable.of_eval (fun i => measurable_const.sub (ContinuousMap.measurable_eval _))
    have he := brownianBelowConditionedLaw_finite_positive_density_map P hB ν (xs k) hν (hxs k) n ds hds
    calc
      _ = ∫⁻ ys, φ k ys ∂volume.withDensity (brownianDoobFinitePDF ν n ds (xs k)) :=
        (lintegral_withDensity_eq_lintegral_mul _
          (measurable_brownianDoobFinitePDF ν hν n ds hds (xs k) (hxs k)) (hφ k)).symm
      _ = ∫⁻ ys, φ k ys ∂(brownianBelowConditionedLaw P ν (xs k)).map
          (fun q i => xs k-q (brownianFirstHitTimes n ds i)) := by rw [he]
      _ = _ := by
        rw [lintegral_map (hφ k) hm]
        apply lintegral_congr
        intro q
        apply congrArg F
        funext i
        exact sub_sub_cancel _ _
  have hgiven : (∫⁻ ys, g ys*ψ ys) = ∫⁻ q, F (fun i => q (brownianFirstHitTimes n ds i)) ∂Q := by
    rw [← negativeConditionedLaw_finite_positive_lintegral Q ν hν hQ n ds hds ψ hψ]
    apply lintegral_congr
    intro q
    apply congrArg F
    funext i
    exact neg_neg _
  simp_rw [hactual,hgiven] at hlim
  exact hlim


end DOZZ.Proofs
