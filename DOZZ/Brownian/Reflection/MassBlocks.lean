/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ReflectionJointInputLaw
public import DOZZ.Statements.Brownian.IsOrderedTwoSidedConditionedCoupling
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import DOZZ.Brownian.Lateral.RadialProjection
public import DOZZ.Statements.Brownian.IsLateralGMCOf
public import DOZZ.Brownian.Lateral.UpperConditionedBlocks
public import DOZZ.GMC.MomentPositivity
public import DOZZ.GMC.Construction.GMCIntensityAdapter

/-!
# Reflection-mass carriers, coupling transfer and block envelopes

A reflection moment depends only on the joint law of the conditioned path pair and the lateral
measure, so any carrier of the conditioned path law placed next to the lateral measure on a
product space reproduces it; on the ordered coupling the mass is monotone in the drift, and
dominated convergence by `1 + J_0^u` gives the small-power endpoint limit. The lateral measure is
a.s. nonzero as soon as the chaos charges one set avoiding the origin.

The two-sided reflection mass is an origin atom plus two half-line masses, the negative half read
on the reflected lateral measure. Each unit block is bounded by a radial envelope times the
lateral block mass; independence factors block moments, and subadditivity (orders at most one) or
infinite Minkowski (orders above one) sums them. Hölder separates the envelope into a one-time
exponential moment and a unit-increment moment. No independence between the two halves is used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- A conditioned two-sided process lives on a probability space. -/
theorem isProbabilityMeasure_of_twoSidedConditioned {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : Ω → BrownianPath × BrownianPath} {ν : ℝ}
    (hB : IsTwoSidedConditionedBrownianProcess P B ν) : IsProbabilityMeasure P :=
  (Measure.isProbabilityMeasure_map_iff hB.1.1).1 hB.1.2.2.1

/-- The path pair of a conditioned two-sided process is almost everywhere measurable. -/
theorem aemeasurable_of_twoSidedConditioned {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : Ω → BrownianPath × BrownianPath} {ν : ℝ}
    (hB : IsTwoSidedConditionedBrownianProcess P B ν) : AEMeasurable B P :=
  (hB.1.1.prodMk hB.2.1.1).congr (Eventually.of_forall fun _ => rfl)

/-- Transplanting a carrier of the same path law next to the given lateral measure preserves the
joint input law. -/
theorem reflectionInput_law_eq_prod_carrier
    {Ω Ωc : Type*} [MeasurableSpace Ω] [MeasurableSpace Ωc]
    (P : Measure Ω) (Pc : Measure Ωc) (ν : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (Bc : Ωc → BrownianPath × BrownianPath)
    (hB : IsTwoSidedConditionedBrownianProcess P B ν) (hZ : AEMeasurable Z P)
    (hInd : IndepFun B Z P) (hBc : IsTwoSidedConditionedBrownianProcess Pc Bc ν) :
    P.map (fun ω => (B ω, Z ω)) = (Pc.prod P).map (fun ω => (Bc ω.1, Z ω.2)) := by
  have := isProbabilityMeasure_of_twoSidedConditioned hB
  have := isProbabilityMeasure_of_twoSidedConditioned hBc
  have hBm := aemeasurable_of_twoSidedConditioned hB
  have hBcm := aemeasurable_of_twoSidedConditioned hBc
  have hBlaw : P.map B = Pc.map Bc := twoSidedConditionedPathPair_law_eq P Pc B Bc ν hB hBc
  have hBcfst : AEMeasurable (fun ω : Ωc × Ω => Bc ω.1) (Pc.prod P) :=
    hBcm.comp_quasiMeasurePreserving (measurePreserving_fst.quasiMeasurePreserving)
  have hZsnd : AEMeasurable (fun ω : Ωc × Ω => Z ω.2) (Pc.prod P) :=
    hZ.comp_quasiMeasurePreserving (measurePreserving_snd.quasiMeasurePreserving)
  have hLeft : P.map (fun ω => (B ω, Z ω)) = (P.map B).prod (P.map Z) :=
    (indepFun_iff_map_prod_eq_prod_map_map hBm hZ).1 hInd
  have hRight : (Pc.prod P).map (fun ω => (Bc ω.1, Z ω.2)) =
      ((Pc.prod P).map (fun ω : Ωc × Ω => Bc ω.1)).prod
        ((Pc.prod P).map (fun ω : Ωc × Ω => Z ω.2)) :=
    (indepFun_iff_map_prod_eq_prod_map_map hBcfst hZsnd).1 (indepFun_prod₀ hBcm hZ)
  have hfst : (Pc.prod P).map (fun ω : Ωc × Ω => Bc ω.1) = Pc.map Bc := by
    have h := AEMeasurable.map_map_of_aemeasurable
      (by rw [measurePreserving_fst.map_eq]; exact hBcm) measurable_fst.aemeasurable
      (μ := Pc.prod P) (g := Bc) (f := Prod.fst)
    rw [measurePreserving_fst.map_eq] at h
    exact h.symm
  have hsnd : (Pc.prod P).map (fun ω : Ωc × Ω => Z ω.2) = P.map Z := by
    have h := AEMeasurable.map_map_of_aemeasurable
      (by rw [measurePreserving_snd.map_eq]; exact hZ) measurable_snd.aemeasurable
      (μ := Pc.prod P) (g := Z) (f := Prod.snd)
    rw [measurePreserving_snd.map_eq] at h
    exact h.symm
  rw [hLeft, hRight, hfst, hsnd, hBlaw]

/-- Equal joint input laws give equal expectations of every a.e.-measurable input functional. -/
theorem lintegral_reflectionInput_eq_of_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    (pair : Ω → (BrownianPath × BrownianPath) × Measure ℝ)
    (pair' : Ω' → (BrownianPath × BrownianPath) × Measure ℝ)
    (hpair : AEMeasurable pair P) (hpair' : AEMeasurable pair' P')
    (hLaw : P.map pair = P'.map pair')
    (F : (BrownianPath × BrownianPath) × Measure ℝ → ℝ≥0∞)
    (hF : AEMeasurable F (P.map pair)) :
    (∫⁻ ω, F (pair ω) ∂P) = ∫⁻ ω, F (pair' ω) ∂P' := by
  have hF' : AEMeasurable F (P'.map pair') := hLaw ▸ hF
  rw [← lintegral_map' hF hpair, ← lintegral_map' hF' hpair', hLaw]

/-- Every real power of the reflection mass has the same expectation on a transplanted carrier of
the conditioned path law. -/
theorem twoSidedReflectionMass_rpow_lintegral_eq_prod_carrier
    {Ω Ωc : Type*} [MeasurableSpace Ω] [MeasurableSpace Ωc]
    (P : Measure Ω) (Pc : Measure Ωc) (γ ν p : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (Bc : Ωc → BrownianPath × BrownianPath)
    (hB : IsTwoSidedConditionedBrownianProcess P B ν) (hZ : IsLateralGMCOf P γ Z)
    (hInd : IndepFun B Z P) (hBc : IsTwoSidedConditionedBrownianProcess Pc Bc ν) :
    (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ B Z ω) p ∂P) =
      ∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (fun ω : Ωc × Ω => Bc ω.1)
        (fun ω => Z ω.2) ω) p ∂(Pc.prod P) := by
  have := isProbabilityMeasure_of_twoSidedConditioned hB
  have := isProbabilityMeasure_of_twoSidedConditioned hBc
  have hZm : AEMeasurable Z P := hZ.2.2.2.1
  have hBm := aemeasurable_of_twoSidedConditioned hB
  have hBcm := aemeasurable_of_twoSidedConditioned hBc
  let pair : Ω → (BrownianPath × BrownianPath) × Measure ℝ := fun ω => (B ω, Z ω)
  let pair' : Ωc × Ω → (BrownianPath × BrownianPath) × Measure ℝ :=
    fun ω => (Bc ω.1, Z ω.2)
  have hpair : AEMeasurable pair P := hBm.prodMk hZm
  have hpair' : AEMeasurable pair' (Pc.prod P) :=
    (hBcm.comp_quasiMeasurePreserving measurePreserving_fst.quasiMeasurePreserving).prodMk
      (hZm.comp_quasiMeasurePreserving measurePreserving_snd.quasiMeasurePreserving)
  have hLaw : P.map pair = (Pc.prod P).map pair' :=
    reflectionInput_law_eq_prod_carrier P Pc ν B Z Bc hB hZm hInd hBc
  have hLocal : ∀ᵐ ω ∂P, LocallyFiniteOnTranslationWindows (pair ω).2 := by
    filter_upwards [hZ.2.2.2.2.1] with ω hω
    intro n
    simpa [LocallyFiniteOnTranslationWindows, translationWindow] using
      hω (-(n : ℝ)) (n : ℝ)
  have hMass := aemeasurable_reflectionMassInput_map_of_locallyFinite P γ pair hpair hLocal
  have hpow : Measurable (fun x : ℝ≥0∞ => ENNReal.rpow x p) :=
    ENNReal.continuous_rpow_const.measurable
  exact lintegral_reflectionInput_eq_of_law P (Pc.prod P) pair pair' hpair hpair' hLaw
    (fun z => ENNReal.rpow (twoSidedReflectionMassInput γ z) p)
    (hpow.comp_aemeasurable hMass)

/-- The joined two-sided value is a measurable function of the signed time. -/
theorem measurable_twoSidedConditionedValue {Ω : Type*}
    (B : Ω → BrownianPath × BrownianPath) (ω : Ω) :
    Measurable (twoSidedConditionedValue B ω) := by
  have h1 : Continuous (fun s : ℝ => (B ω).1 (Real.toNNReal s)) :=
    (B ω).1.continuous.comp continuous_real_toNNReal
  have h2 : Continuous (fun s : ℝ => (B ω).2 (Real.toNNReal (-s))) :=
    (B ω).2.continuous.comp (continuous_real_toNNReal.comp continuous_neg)
  have he : twoSidedConditionedValue B ω = fun s =>
      if 0 ≤ s then (B ω).1 (Real.toNNReal s) else (B ω).2 (Real.toNNReal (-s)) := by
    funext s
    unfold twoSidedConditionedValue
    by_cases hs : 0 ≤ s
    · simp only [hs, dite_true, ite_true, Real.toNNReal_of_nonneg hs]
      rfl
    · have hs' : 0 ≤ -s := by linarith
      simp only [hs, dite_false, ite_false, Real.toNNReal_of_nonneg hs']
      rfl
  rw [he]
  exact Measurable.ite (measurableSet_le measurable_const measurable_id) h1.measurable
    h2.measurable

/-- The exponential integrand of the reflection mass is measurable in the signed time. -/
theorem measurable_twoSidedReflectionIntegrand {Ω : Type*} (γ : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (ω : Ω) :
    Measurable (fun s => ENNReal.ofReal (Real.exp (γ * twoSidedConditionedValue B ω s))) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul (measurable_twoSidedConditionedValue B ω)))

/-- A nonzero lateral measure gives a strictly positive reflection mass. -/
theorem twoSidedReflectionMass_pos_of_ne_zero {Ω : Type*} (γ : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) (ω : Ω) (hZ : Z ω ≠ 0) :
    0 < twoSidedReflectionMass γ B Z ω := by
  unfold twoSidedReflectionMass
  rw [lintegral_pos_iff_support (measurable_twoSidedReflectionIntegrand γ B ω)]
  have hsupp : Function.support
      (fun s => ENNReal.ofReal (Real.exp (γ * twoSidedConditionedValue B ω s))) = univ := by
    ext s
    simp [Real.exp_pos]
  rw [hsupp]
  exact Measure.measure_univ_pos.mpr hZ

/-- Pathwise lower paths give a smaller reflection mass. -/
theorem twoSidedReflectionMass_le_of_le {Ω : Type*} (γ : ℝ) (hγ : 0 ≤ γ)
    (B B' : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) (ω : Ω)
    (h₁ : ∀ t, (B' ω).1 t ≤ (B ω).1 t) (h₂ : ∀ t, (B' ω).2 t ≤ (B ω).2 t) :
    twoSidedReflectionMass γ B' Z ω ≤ twoSidedReflectionMass γ B Z ω := by
  unfold twoSidedReflectionMass
  apply lintegral_mono
  intro s
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hγ
  unfold twoSidedConditionedValue
  by_cases hs : 0 ≤ s
  · simp only [hs, dite_true]
    exact h₁ _
  · simp only [hs, dite_false]
    exact h₂ _

/-- A power of order `t ≤ u` is controlled by `1 + x ^ u`. -/
theorem ennreal_rpow_le_one_add_rpow (x : ℝ≥0∞) {t u : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    x ^ t ≤ 1 + x ^ u := by
  rcases le_or_gt x 1 with hx | hx
  · exact (ENNReal.rpow_le_one hx ht).trans le_self_add
  · exact (ENNReal.rpow_le_rpow_of_exponent_le hx.le htu).trans le_add_self

/-- A positive finite base raised to a vanishing exponent tends to one. -/
theorem tendsto_ennreal_rpow_nhds_one {ι : Type*} {l : Filter ι} {a : ℝ≥0∞}
    (ha : 0 < a) (ha' : a < ⊤) {e : ι → ℝ} (he : Tendsto e l (𝓝 0)) :
    Tendsto (fun i => a ^ e i) l (𝓝 1) := by
  have hreal : 0 < a.toReal := ENNReal.toReal_pos ha.ne' ha'.ne
  have heq : (fun i => a ^ e i) = fun i => ENNReal.ofReal (a.toReal ^ e i) := by
    funext i
    rw [← ENNReal.ofReal_rpow_of_pos hreal, ENNReal.ofReal_toReal ha'.ne]
  rw [heq]
  have hc : Tendsto (fun i => a.toReal ^ e i) l (𝓝 (a.toReal ^ (0 : ℝ))) :=
    (Real.continuousAt_const_rpow hreal.ne').tendsto.comp he
  rw [Real.rpow_zero] at hc
  have h := (ENNReal.continuous_ofReal.tendsto 1).comp hc
  rw [ENNReal.ofReal_one] at h
  exact h

/-- Powers of order `e i → 0` of quantities squeezed between two positive finite bounds tend to
one. -/
theorem tendsto_ennreal_rpow_of_squeeze {ι : Type*} {l : Filter ι} {a b : ℝ≥0∞}
    (ha : 0 < a) (hb : b < ⊤) {f : ι → ℝ≥0∞} {e : ι → ℝ} (he : Tendsto e l (𝓝 0))
    (he0 : ∀ᶠ i in l, 0 ≤ e i) (hf : ∀ᶠ i in l, a ≤ f i ∧ f i ≤ b) :
    Tendsto (fun i => f i ^ e i) l (𝓝 1) := by
  have hab : ∀ᶠ i in l, a ≤ b := hf.mono fun i hi => hi.1.trans hi.2
  rcases l.eq_or_neBot with hl | hl
  · rw [hl]
    exact tendsto_bot
  obtain ⟨i, hi⟩ := hab.exists
  have hb0 : 0 < b := ha.trans_le hi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_ennreal_rpow_nhds_one ha (lt_of_le_of_lt hi hb) he)
    (tendsto_ennreal_rpow_nhds_one hb0 hb he)
  · filter_upwards [he0, hf] with i hi0 hfi
    exact ENNReal.rpow_le_rpow hfi.1 hi0
  · filter_upwards [he0, hf] with i hi0 hfi
    exact ENNReal.rpow_le_rpow hfi.2 hi0

/-- On an ordered coupling transplanted next to a lateral measure, small-power reflection moments
tend to one at the zero-drift endpoint. The inputs are one positive moment at zero drift and
almost-sure nonvanishing of the lateral measure; the domination is `1 + J_0 ^ u`. -/
theorem coupling_zeroDrift_rpow_tendsto_one
    {Ωc Ω : Type*} [MeasurableSpace Ωc] [MeasurableSpace Ω]
    (Pc : Measure Ωc) [IsProbabilityMeasure Pc]
    (Bc : ℝ → Ωc → BrownianPath × BrownianPath)
    (hcoup : IsOrderedTwoSidedConditionedCoupling Pc Bc)
    (P : Measure Ω) (γ : ℝ) (hγ : 0 < γ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (hZpos : ∀ᵐ ω ∂P, Z ω ≠ 0) (u : ℝ) (hu : 0 < u)
    (hmom : (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (fun ω : Ωc × Ω => Bc 0 ω.1)
      (fun ω => Z ω.2) ω) u ∂(Pc.prod P)) < ⊤)
    (e : ℝ → ℝ) (he : Tendsto e (𝓝[>] 0) (𝓝 0)) (he0 : ∀ ν, 0 < ν → 0 ≤ e ν) :
    Tendsto (fun ν => ∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ
      (fun ω : Ωc × Ω => Bc ν ω.1) (fun ω => Z ω.2) ω) (e ν) ∂(Pc.prod P))
      (𝓝[>] 0) (𝓝 1) := by
  have hP : IsProbabilityMeasure P := hZ.2.2.1
  let J : ℝ → Ωc × Ω → ℝ≥0∞ := fun ν ω =>
    twoSidedReflectionMass γ (fun ω : Ωc × Ω => Bc ν ω.1) (fun ω => Z ω.2) ω
  have hfst := (measurePreserving_fst (μ := Pc) (ν := P)).quasiMeasurePreserving
  have hsnd := (measurePreserving_snd (μ := Pc) (ν := P)).quasiMeasurePreserving
  -- the coupling order, read on the product carrier
  have hord : ∀ᵐ ω ∂(Pc.prod P), ∀ ν ν' : ℝ, 0 ≤ ν → ν ≤ ν' → J ν' ω ≤ J ν ω := by
    filter_upwards [hfst.ae (hcoup.2.mono fun x hx => hx.1)] with ω hω ν ν' hν hνν'
    exact twoSidedReflectionMass_le_of_le γ hγ.le (fun ω : Ωc × Ω => Bc ν ω.1)
      (fun ω : Ωc × Ω => Bc ν' ω.1) (fun ω => Z ω.2) ω
      (fun t => (hω ν ν' hν hνν' t).1) (fun t => (hω ν ν' hν hνν' t).2.2.1)
  -- measurability of every reflection mass with nonnegative drift
  have hlocal : ∀ᵐ ω ∂(Pc.prod P), LocallyFiniteOnTranslationWindows (Z ω.2) := by
    have h : ∀ᵐ ω ∂P, LocallyFiniteOnTranslationWindows (Z ω) := by
      filter_upwards [hZ.2.2.2.2.1] with ω hω
      intro n
      simpa [LocallyFiniteOnTranslationWindows, translationWindow] using
        hω (-(n : ℝ)) (n : ℝ)
    exact hsnd.ae (p := fun x => LocallyFiniteOnTranslationWindows (Z x)) h
  have hJm : ∀ ν : ℝ, 0 ≤ ν → AEMeasurable (J ν) (Pc.prod P) := by
    intro ν hν
    have hBc := aemeasurable_of_twoSidedConditioned (hcoup.1 ν hν)
    have hpair : AEMeasurable (fun ω : Ωc × Ω => (Bc ν ω.1, Z ω.2)) (Pc.prod P) :=
      (hBc.comp_quasiMeasurePreserving hfst).prodMk
        (hZ.2.2.2.1.comp_quasiMeasurePreserving hsnd)
    exact (aemeasurable_reflectionMassInput_map_of_locallyFinite (Pc.prod P) γ
      (fun ω : Ωc × Ω => (Bc ν ω.1, Z ω.2)) hpair hlocal).comp_aemeasurable hpair
  -- finiteness at zero drift and positivity at drift one
  have hfin : ∀ᵐ ω ∂(Pc.prod P), J 0 ω < ⊤ := by
    have hpow : AEMeasurable (fun ω => J 0 ω ^ u) (Pc.prod P) :=
      (ENNReal.continuous_rpow_const.measurable).comp_aemeasurable (hJm 0 le_rfl)
    filter_upwards [ae_lt_top' hpow hmom.ne] with ω hω
    exact lt_top_iff_ne_top.mpr fun htop => by
      rw [htop, ENNReal.top_rpow_of_pos hu] at hω
      exact lt_irrefl _ hω
  have hpos : ∀ᵐ ω ∂(Pc.prod P), 0 < J 1 ω := by
    filter_upwards [hsnd.ae hZpos] with ω hω
    exact twoSidedReflectionMass_pos_of_ne_zero γ (fun ω : Ωc × Ω => Bc 1 ω.1)
      (fun ω => Z ω.2) ω hω
  -- dominated convergence
  have hIoo : ∀ᶠ ν in 𝓝[>] (0 : ℝ), ν ∈ Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)
  have hsmall : ∀ᶠ ν in 𝓝[>] (0 : ℝ), 0 < ν ∧ ν < 1 ∧ e ν ≤ u :=
    (hIoo.and (he.eventually (eventually_le_nhds hu))).mono fun ν hν =>
      ⟨hν.1.1, hν.1.2, hν.2⟩
  have hlim := tendsto_lintegral_filter_of_dominated_convergence'
    (μ := Pc.prod P) (l := 𝓝[>] (0 : ℝ)) (F := fun ν ω => J ν ω ^ e ν)
    (f := fun _ => (1 : ℝ≥0∞)) (fun ω => 1 + J 0 ω ^ u)
    (hsmall.mono fun ν hν =>
      (ENNReal.continuous_rpow_const.measurable).comp_aemeasurable (hJm ν hν.1.le))
    (hsmall.mono fun ν hν => by
      filter_upwards [hord] with ω hω
      exact (ENNReal.rpow_le_rpow (hω 0 ν le_rfl hν.1.le) (he0 ν hν.1)).trans
        (ennreal_rpow_le_one_add_rpow _ (he0 ν hν.1) hν.2.2))
    (by
      rw [lintegral_add_left measurable_const]
      simp only [lintegral_const, measure_univ, mul_one]
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hmom.ne⟩)
    (by
      filter_upwards [hord, hfin, hpos] with ω hω h0 h1
      apply tendsto_ennreal_rpow_of_squeeze h1 h0 he
        (eventually_nhdsWithin_of_forall fun ν hν => he0 ν hν)
      filter_upwards [hsmall] with ν hν
      exact ⟨hω ν 1 hν.1.le hν.2.1.le, hω 0 ν le_rfl hν.1.le⟩)
  rw [lintegral_const, measure_univ, mul_one] at hlim
  exact hlim

/-- A lateral projection is nonzero as soon as its chaos charges a set avoiding the origin. -/
theorem lateralProjectedGMC_ne_zero_of_pos (γ : ℝ) (A : TwoSidedPath) (M : Measure ℂ)
    (O : Set ℂ) (hO : MeasurableSet O) (h0 : (0 : ℂ) ∉ O) (hM : 0 < M O) :
    lateralProjectedGMC γ A M ≠ 0 := by
  intro hzero
  let w : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (if ‖x‖ = 0 then 0 else
    Real.exp (-γ * A (-Real.log ‖x‖) + γ * Q γ * |Real.log ‖x‖|))
  have hw : w = lateralRadialWeight γ A := rfl
  have hwm : Measurable w := by
    rw [hw]
    exact measurable_lateralRadialWeight.comp
      ((measurable_const.prodMk measurable_const).prodMk measurable_id)
  have hg : Measurable (fun x : ℂ => -Real.log ‖x‖) := by fun_prop
  have huniv : (M.withDensity w) univ = 0 := by
    have h := congrArg (fun μ : Measure ℝ => μ univ) hzero
    simp only [lateralProjectedGMC, Measure.coe_zero, Pi.zero_apply] at h
    rw [Measure.map_apply hg MeasurableSet.univ, preimage_univ] at h
    exact h
  have hO0 : (M.withDensity w) O = 0 := measure_mono_null (subset_univ O) huniv
  rw [withDensity_apply _ hO] at hO0
  have hae : w =ᵐ[M.restrict O] 0 := (lintegral_eq_zero_iff hwm).mp hO0
  have hnull : (M.restrict O) {x | w x ≠ 0} = 0 := by
    have hae' : ∀ᵐ x ∂(M.restrict O), w x = 0 := hae
    rw [ae_iff] at hae'
    exact hae'
  have hsub : O ⊆ {x | w x ≠ 0} := by
    intro x hx
    have hx0 : x ≠ 0 := fun h => h0 (h ▸ hx)
    rw [hw]
    exact (lateralRadialWeight_pos hx0).1.ne'
  have hmeas : MeasurableSet {x | w x ≠ 0} := (hwm (measurableSet_singleton 0)).compl
  rw [Measure.restrict_apply hmeas, inter_eq_right.mpr hsub] at hnull
  exact (ne_of_gt hM) hnull

/-- Almost-sure positivity of every equator GMC on one set avoiding the origin makes every source
lateral measure almost surely nonzero. -/
theorem lateralGMC_ne_zero_ae_of_chaos_pos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z) (O : Set ℂ)
    (hO : MeasurableSet O) (h0 : (0 : ℂ) ∉ O)
    (hpos : ∀ (X : Ω → Distr) (M : Ω → Measure ℂ), IsEquatorGFF P X → IsGMCOf P X γ M →
      ∀ᵐ ω ∂P, 0 < M ω O) :
    ∀ᵐ ω ∂P, Z ω ≠ 0 := by
  obtain ⟨X, M, hX, hM, A, -, -, -, -, -, -, -, -, he⟩ := hZ.2.2.2.2.2.2.2.2
  filter_upwards [he, hpos X M hX hM] with ω hω hMω
  rw [hω]
  exact lateralProjectedGMC_ne_zero_of_pos γ (A ω) (M ω) O hO h0 hMω

/-- The equator chaos has no atom at the origin, almost surely. -/
theorem equatorGFF_GMC_origin_null_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) : ∀ᵐ ω ∂P, M ω {0} = 0 := by
  have hm : AEMeasurable (fun ω => M ω {0}) P :=
    (Measure.measurable_coe (measurableSet_singleton 0)).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM)
  apply (lintegral_eq_zero_iff' hm).1
  rw [equatorGFF_GMC_intensity P X hX γ hγ hγ2 M hM {0} (measurableSet_singleton 0)]
  exact withDensity_absolutelyContinuous _ _ (measure_singleton 0)


/-- Reflection of a measure on the line is a measurable operation. -/
theorem measurable_measure_map_neg :
    Measurable (fun μ : Measure ℝ => μ.map (fun s : ℝ => -s)) :=
  Measure.measurable_map _ measurable_neg

/-- Interval masses of the reflected measure. -/
theorem measure_map_neg_Ioc (μ : Measure ℝ) (a b : ℝ) :
    (μ.map (fun s : ℝ => -s)) (Ioc a b) = μ (Ico (-b) (-a)) := by
  rw [Measure.map_apply measurable_neg measurableSet_Ioc]
  congr 1
  ext x
  simp only [mem_preimage, mem_Ioc, mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- The reflected measure inherits finiteness on bounded intervals. -/
theorem map_neg_Ioc_lt_top_of_Icc {μ : Measure ℝ} (hμ : ∀ a b : ℝ, μ (Icc a b) < ⊤) (a b : ℝ) :
    (μ.map (fun s : ℝ => -s)) (Ioc a b) < ⊤ := by
  rw [measure_map_neg_Ioc]
  exact lt_of_le_of_lt (measure_mono Ico_subset_Icc_self) (hμ _ _)

/-- On the open positive half-line the two-sided value is the first entrance path. -/
theorem twoSidedConditionedValue_of_pos {Ω : Type*} (B : Ω → BrownianPath × BrownianPath)
    (ω : Ω) {s : ℝ} (hs : 0 < s) :
    twoSidedConditionedValue B ω s = (B ω).1 (Real.toNNReal s) := by
  have h : 0 ≤ s := hs.le
  simp only [twoSidedConditionedValue, h, dite_true, Real.toNNReal_of_nonneg h]
  rfl

/-- On the open negative half-line the two-sided value is the second entrance path read at `-s`. -/
theorem twoSidedConditionedValue_of_neg {Ω : Type*} (B : Ω → BrownianPath × BrownianPath)
    (ω : Ω) {s : ℝ} (hs : s < 0) :
    twoSidedConditionedValue B ω s = (B ω).2 (Real.toNNReal (-s)) := by
  have h : ¬ 0 ≤ s := not_le.mpr hs
  have h' : 0 ≤ -s := by linarith
  simp only [twoSidedConditionedValue, h, dite_false, Real.toNNReal_of_nonneg h']
  rfl

/-- At the origin the two-sided value is the first entrance path at time zero. -/
theorem twoSidedConditionedValue_zero {Ω : Type*} (B : Ω → BrownianPath × BrownianPath)
    (ω : Ω) :
    twoSidedConditionedValue B ω 0 = (B ω).1 0 := by
  simp only [twoSidedConditionedValue, le_refl, dite_true]
  rfl

/-- The exponential radial weight along the positive half-line is a measurable function. -/
theorem measurable_positiveLateralWeight (γ : ℝ) (p : BrownianPath) :
    Measurable (fun s : ℝ => ENNReal.ofReal (Real.exp (γ * p (Real.toNNReal s)))) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
    (p.continuous.measurable.comp measurable_real_toNNReal)))

/-- The two-sided reflection mass is the origin atom plus two half-line masses; the negative half
is read on the reflected measure. -/
theorem twoSidedReflectionMass_eq_halves {Ω : Type*} (γ : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) (ω : Ω) :
    twoSidedReflectionMass γ B Z ω =
      ENNReal.ofReal (Real.exp (γ * (B ω).1 0)) * Z ω {0} +
        positiveLateralMass γ (B ω).1 (Z ω) +
          positiveLateralMass γ (B ω).2 ((Z ω).map (fun s : ℝ => -s)) := by
  let f : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.exp (γ * twoSidedConditionedValue B ω s))
  have hsplit : (univ : Set ℝ) = Iio 0 ∪ ({0} ∪ Ioi 0) := by
    ext x
    simp only [mem_univ, mem_union, mem_Iio, mem_singleton_iff, mem_Ioi, true_iff]
    rcases lt_trichotomy x 0 with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hd1 : Disjoint (Iio (0 : ℝ)) ({0} ∪ Ioi 0) := by
    refine disjoint_left.mpr (fun x hx hx' => ?_)
    have hx0 : x < 0 := hx
    rcases hx' with h | h
    · have h0 : x = 0 := h
      linarith
    · have h0 : 0 < x := h
      linarith
  have hd2 : Disjoint ({0} : Set ℝ) (Ioi 0) := by
    refine disjoint_left.mpr (fun x hx hx' => ?_)
    have h0 : x = 0 := hx
    have h1 : 0 < x := hx'
    linarith
  have hneg : ∫⁻ s in Iio 0, f s ∂(Z ω) =
      positiveLateralMass γ (B ω).2 ((Z ω).map (fun s : ℝ => -s)) := by
    unfold positiveLateralMass
    rw [setLIntegral_map measurableSet_Ioi (measurable_positiveLateralWeight γ (B ω).2)
      measurable_neg]
    have hpre : (fun s : ℝ => -s) ⁻¹' Ioi (0 : ℝ) = Iio 0 := by
      ext x
      simp
    rw [hpre]
    refine setLIntegral_congr_fun measurableSet_Iio ?_
    intro x hx
    simp only [f, twoSidedConditionedValue_of_neg B ω (mem_Iio.mp hx)]
  have hzero : ∫⁻ s in {0}, f s ∂(Z ω) =
      ENNReal.ofReal (Real.exp (γ * (B ω).1 0)) * Z ω {0} := by
    rw [lintegral_singleton]
    simp only [f, twoSidedConditionedValue_zero]
  have hpos : ∫⁻ s in Ioi 0, f s ∂(Z ω) = positiveLateralMass γ (B ω).1 (Z ω) := by
    unfold positiveLateralMass
    refine setLIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    simp only [f, twoSidedConditionedValue_of_pos B ω (mem_Ioi.mp hx)]
  calc twoSidedReflectionMass γ B Z ω = ∫⁻ s in univ, f s ∂(Z ω) := by
        rw [Measure.restrict_univ]
        rfl
    _ = ∫⁻ s in Iio 0 ∪ ({0} ∪ Ioi 0), f s ∂(Z ω) := by rw [hsplit]
    _ = ∫⁻ s in Iio 0, f s ∂(Z ω) + (∫⁻ s in {0}, f s ∂(Z ω) + ∫⁻ s in Ioi 0, f s ∂(Z ω)) := by
        rw [lintegral_union ((measurableSet_singleton 0).union measurableSet_Ioi) hd1,
          lintegral_union measurableSet_Ioi hd2]
    _ = _ := by
        rw [hneg, hzero, hpos]
        ac_rfl

/-- A half-line block is almost everywhere measurable as soon as the path and measure are, and the
measure is almost surely finite on bounded intervals. -/
theorem positiveLateralBlock_aemeasurable_of_finite {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) (n : ℝ≥0) (B : Ω → BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : AEMeasurable Z P)
    (hfin : ∀ᵐ ω ∂P, ∀ a b : ℝ, Z ω (Ioc a b) < ⊤) :
    AEMeasurable (fun ω => positiveLateralBlock γ n (B ω) (Z ω)) P := by
  let I : Set ℝ := Ioc (n : ℝ) ((n : ℝ) + 1)
  let f : BrownianPath × ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (γ * z.1 (Real.toNNReal z.2)))
  have hf : Measurable f := by
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
      (continuous_eval.comp (continuous_fst.prodMk
        (continuous_real_toNNReal.comp continuous_snd))).measurable))
  have hk := measurable_lintegral_finiteMeasure_parameter hf
  have hr : Measurable (fun μ : Measure ℝ => finiteRestrictionOnSet I μ) :=
    measurable_finiteRestrictionOnSet I measurableSet_Ioc
  have hrest := hr.comp_aemeasurable hZ
  have hp : AEMeasurable (fun ω => (B ω, finiteRestrictionOnSet I (Z ω))) P :=
    hB.prodMk hrest
  have hext := hk.comp_aemeasurable hp
  apply hext.congr
  filter_upwards [hfin] with ω hω
  have hI : Z ω I < ⊤ := hω n ((n : ℝ) + 1)
  have he : (finiteRestrictionOnSet I (Z ω) : Measure ℝ) = (Z ω).restrict I := by
    simp [finiteRestrictionOnSet, hI]
  change (∫⁻ s, f (B ω, s) ∂(finiteRestrictionOnSet I (Z ω) : Measure ℝ)) = _
  rw [he]
  rfl

/-- The same for the whole half-line mass. -/
theorem positiveLateralMass_aemeasurable_of_finite {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) (B : Ω → BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : AEMeasurable Z P)
    (hfin : ∀ᵐ ω ∂P, ∀ a b : ℝ, Z ω (Ioc a b) < ⊤) :
    AEMeasurable (fun ω => positiveLateralMass γ (B ω) (Z ω)) P := by
  have hm : AEMeasurable (fun ω => ∑' n : ℕ, positiveLateralBlock γ n (B ω) (Z ω)) P :=
    AEMeasurable.tsum (fun n : ℕ =>
      positiveLateralBlock_aemeasurable_of_finite P γ n B Z hB hZ hfin)
  exact hm.congr (ae_of_all _ (fun ω => (positiveLateralMass_eq_tsum_blocks γ (B ω) (Z ω)).symm))

/-- Finite subadditivity of `x ↦ x ^ q` for `0 < q ≤ 1`. -/
theorem ennreal_finset_sum_rpow_le {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (∑ i ∈ s, a i) ^ q ≤ ∑ i ∈ s, a i ^ q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ENNReal.zero_rpow_of_pos hq0]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (ENNReal.rpow_add_le_add_rpow _ _ hq0.le hq1).trans (add_le_add le_rfl ih)

/-- Countable subadditivity of `x ↦ x ^ q` for `0 < q ≤ 1`. -/
theorem ennreal_tsum_rpow_le {ι : Type*} (a : ι → ℝ≥0∞) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (∑' i, a i) ^ q ≤ ∑' i, a i ^ q := by
  have hroot : (∑' i, a i) ≤ (∑' i, a i ^ q) ^ (1 / q) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    have hs := ennreal_finset_sum_rpow_le s a hq0 hq1
    have hle : (∑ i ∈ s, a i ^ q) ≤ ∑' i, a i ^ q := ENNReal.sum_le_tsum s
    calc (∑ i ∈ s, a i) = ((∑ i ∈ s, a i) ^ q) ^ (1 / q) := by
          rw [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
      _ ≤ (∑' i, a i ^ q) ^ (1 / q) :=
          ENNReal.rpow_le_rpow (hs.trans hle) (one_div_nonneg.mpr hq0.le)
  calc (∑' i, a i) ^ q ≤ ((∑' i, a i ^ q) ^ (1 / q)) ^ q := ENNReal.rpow_le_rpow hroot hq0.le
    _ = ∑' i, a i ^ q := by
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]

/-- A sum of three terms raised to a nonnegative power. -/
theorem ennreal_add3_rpow_le (a b c : ℝ≥0∞) {q : ℝ} (hq : 0 ≤ q) :
    (a + b + c) ^ q ≤ 3 ^ q * (a ^ q + b ^ q + c ^ q) := by
  let m := max a (max b c)
  have hsum : a + b + c ≤ 3 * m := by
    have ha : a ≤ m := le_max_left _ _
    have hb : b ≤ m := (le_max_left _ _).trans (le_max_right _ _)
    have hc : c ≤ m := (le_max_right _ _).trans (le_max_right _ _)
    calc a + b + c ≤ m + m + m := add_le_add (add_le_add ha hb) hc
      _ = 3 * m := by ring
  have hm : m ^ q ≤ a ^ q + b ^ q + c ^ q := by
    rcases le_total b c with hbc | hbc
    · rcases le_total a c with hac | hac
      · have : m = c := by simp [m, hbc, hac]
        rw [this]
        exact le_add_self
      · have : m = a := by simp [m, hbc, hac]
        rw [this, add_assoc]
        exact le_self_add
    · rcases le_total a b with hab | hab
      · have : m = b := by simp [m, hbc, hab]
        rw [this]
        exact (le_add_self : b ^ q ≤ a ^ q + b ^ q).trans le_self_add
      · have : m = a := by simp [m, hbc, hab]
        rw [this, add_assoc]
        exact le_self_add
  calc (a + b + c) ^ q ≤ (3 * m) ^ q := ENNReal.rpow_le_rpow hsum hq
    _ = 3 ^ q * m ^ q := ENNReal.mul_rpow_of_nonneg _ _ hq
    _ ≤ 3 ^ q * (a ^ q + b ^ q + c ^ q) := mul_le_mul_right hm _

/-- Positive half-line moments of order at most one from independent block envelopes. -/
theorem positiveLateralMass_rpow_lintegral_le_of_envelope
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ q : ℝ) (hγ : 0 ≤ γ)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (B : Ω → BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : AEMeasurable Z P)
    (hfin : ∀ᵐ ω ∂P, ∀ a b : ℝ, Z ω (Ioc a b) < ⊤) (hi : IndepFun B Z P)
    (L : ℝ≥0∞) (hL : ∀ n : ℕ, (∫⁻ ω, (Z ω (Ioc (n : ℝ) ((n : ℝ) + 1))) ^ q ∂P) ≤ L)
    (g : ℕ → ℝ≥0∞) (hg : ∀ n : ℕ, (∫⁻ ω, positiveBlockEnvelope (q * γ) n (B ω) ∂P) ≤ g n) :
    (∫⁻ ω, (positiveLateralMass γ (B ω) (Z ω)) ^ q ∂P) ≤ L * ∑' n, g n := by
  calc (∫⁻ ω, (positiveLateralMass γ (B ω) (Z ω)) ^ q ∂P)
      ≤ ∫⁻ ω, ∑' n : ℕ, (positiveLateralBlock γ n (B ω) (Z ω)) ^ q ∂P := by
        apply lintegral_mono
        intro ω
        beta_reduce
        rw [positiveLateralMass_eq_tsum_blocks]
        exact ennreal_tsum_rpow_le _ hq0 hq1
    _ = ∑' n : ℕ, ∫⁻ ω, (positiveLateralBlock γ n (B ω) (Z ω)) ^ q ∂P :=
        lintegral_tsum fun n => (ENNReal.continuous_rpow_const.measurable).comp_aemeasurable
          (positiveLateralBlock_aemeasurable_of_finite P γ n B Z hB hZ hfin)
    _ ≤ ∑' n : ℕ, g n * L := by
        apply ENNReal.tsum_le_tsum
        intro n
        have h := positiveLateralBlock_moment_le_independent_envelope P γ q hγ hq0.le n
          B Z hB hZ hi
        refine h.trans (mul_le_mul' (hg n) ?_)
        simpa only [NNReal.coe_natCast] using hL n
    _ = L * ∑' n, g n := by rw [ENNReal.tsum_mul_right, mul_comm]

/-- Positive half-line moments of order at least one from independent block envelopes, by
infinite Minkowski. -/
theorem positiveLateralMass_rpow_lintegral_le_of_envelope_of_one_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ q : ℝ) (hγ : 0 ≤ γ)
    (hq1 : 1 ≤ q) (B : Ω → BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : AEMeasurable Z P)
    (hfin : ∀ᵐ ω ∂P, ∀ a b : ℝ, Z ω (Ioc a b) < ⊤) (hi : IndepFun B Z P)
    (L : ℝ≥0∞) (hL : ∀ n : ℕ, (∫⁻ ω, (Z ω (Ioc (n : ℝ) ((n : ℝ) + 1))) ^ q ∂P) ≤ L)
    (g : ℕ → ℝ≥0∞) (hg : ∀ n : ℕ, (∫⁻ ω, positiveBlockEnvelope (q * γ) n (B ω) ∂P) ≤ g n) :
    (∫⁻ ω, (positiveLateralMass γ (B ω) (Z ω)) ^ q ∂P) ≤
      (∑' n, (g n * L) ^ (1 / q)) ^ q := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  have hmass := lintegral_tsum_rpow_le_root_moments_power P
    (fun n : ℕ => fun ω => positiveLateralBlock γ n (B ω) (Z ω))
    (fun n => positiveLateralBlock_aemeasurable_of_finite P γ n B Z hB hZ hfin) q hq1
  have hblock : ∀ n : ℕ, (∫⁻ ω, (positiveLateralBlock γ n (B ω) (Z ω)) ^ q ∂P) ≤ g n * L := by
    intro n
    have h := positiveLateralBlock_moment_le_independent_envelope P γ q hγ hq0.le n
      B Z hB hZ hi
    refine h.trans (mul_le_mul' (hg n) ?_)
    simpa only [NNReal.coe_natCast] using hL n
  have hroot : (∑' n : ℕ,
      (∫⁻ ω, (positiveLateralBlock γ n (B ω) (Z ω)) ^ q ∂P) ^ (1 / q)) ≤
        ∑' n, (g n * L) ^ (1 / q) :=
    ENNReal.tsum_le_tsum fun n => ENNReal.rpow_le_rpow (hblock n) (one_div_nonneg.mpr hq0.le)
  calc (∫⁻ ω, (positiveLateralMass γ (B ω) (Z ω)) ^ q ∂P)
      = ∫⁻ ω, (∑' n : ℕ, positiveLateralBlock γ n (B ω) (Z ω)) ^ q ∂P := by
        simp only [positiveLateralMass_eq_tsum_blocks]
    _ ≤ _ := hmass
    _ ≤ _ := ENNReal.rpow_le_rpow hroot hq0.le

/-- Hölder separates the block envelope into a one-time exponential moment and a unit-increment
exponential moment, with conjugate exponents `r` and `r / (r - 1)`. -/
theorem positiveBlockEnvelope_lintegral_le (Q : Measure BrownianPath) (θ r : ℝ) (hθ : 0 ≤ θ)
    (hr : 1 < r) (n : ℝ≥0) :
    (∫⁻ p, positiveBlockEnvelope θ n p ∂Q) ≤
      (∫⁻ p, ENNReal.ofReal (Real.exp (r * θ * p n)) ∂Q) ^ (1 / r) *
        (∫⁻ p, ENNReal.ofReal (Real.exp (r / (r - 1) * θ *
          brownianUnitNorm (brownianShiftPath n p))) ∂Q) ^ ((r - 1) / r) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hr1 : 0 < r - 1 := sub_pos.mpr hr
  have hshift : Continuous (fun p : BrownianPath => brownianShiftPath n p) :=
    continuous_brownianShiftPath.comp (continuous_const.prodMk continuous_id)
  have hF : AEMeasurable (fun p : BrownianPath =>
      ENNReal.ofReal (Real.exp (r * θ * p n))) Q :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (ContinuousMap.measurable_eval n)))).aemeasurable
  have hG : AEMeasurable (fun p : BrownianPath => ENNReal.ofReal (Real.exp (r / (r - 1) * θ *
      brownianUnitNorm (brownianShiftPath n p)))) Q :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
      (continuous_brownianUnitNorm.comp hshift).measurable))).aemeasurable
  have hsplit : ∀ p : BrownianPath, positiveBlockEnvelope θ n p =
      (ENNReal.ofReal (Real.exp (r * θ * p n))) ^ (1 / r) *
        (ENNReal.ofReal (Real.exp (r / (r - 1) * θ *
          brownianUnitNorm (brownianShiftPath n p)))) ^ ((r - 1) / r) := by
    intro p
    rw [ennreal_exp_rpow, ennreal_exp_rpow, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add, positiveBlockEnvelope, abs_of_nonneg hθ]
    congr 2
    field_simp
  have hsum : 1 / r + (r - 1) / r = 1 := by
    field_simp
    ring
  calc (∫⁻ p, positiveBlockEnvelope θ n p ∂Q)
      = ∫⁻ p, (ENNReal.ofReal (Real.exp (r * θ * p n))) ^ (1 / r) *
        (ENNReal.ofReal (Real.exp (r / (r - 1) * θ *
          brownianUnitNorm (brownianShiftPath n p)))) ^ ((r - 1) / r) ∂Q :=
        lintegral_congr fun p => hsplit p
    _ ≤ _ := ENNReal.lintegral_mul_norm_pow_le hF hG (one_div_nonneg.mpr hr0.le)
        (div_nonneg hr1.le hr0.le) hsum

/-- The block sum controlling a half-line moment of order `q`, by subadditivity for `q ≤ 1` and
by infinite Minkowski for `q > 1`. -/
noncomputable def halfLineBlockBound (q : ℝ) (L : ℝ≥0∞) (g : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  if q ≤ 1 then L * ∑' n, g n else (∑' n, (g n * L) ^ (1 / q)) ^ q

/-- Half-line moments from block envelopes, for every positive order. -/
theorem positiveLateralMass_rpow_lintegral_le_blockBound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ q : ℝ) (hγ : 0 ≤ γ) (hq0 : 0 < q)
    (B : Ω → BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : AEMeasurable Z P)
    (hfin : ∀ᵐ ω ∂P, ∀ a b : ℝ, Z ω (Ioc a b) < ⊤) (hi : IndepFun B Z P)
    (L : ℝ≥0∞) (hL : ∀ n : ℕ, (∫⁻ ω, (Z ω (Ioc (n : ℝ) ((n : ℝ) + 1))) ^ q ∂P) ≤ L)
    (g : ℕ → ℝ≥0∞) (hg : ∀ n : ℕ, (∫⁻ ω, positiveBlockEnvelope (q * γ) n (B ω) ∂P) ≤ g n) :
    (∫⁻ ω, (positiveLateralMass γ (B ω) (Z ω)) ^ q ∂P) ≤ halfLineBlockBound q L g := by
  unfold halfLineBlockBound
  split_ifs with hq1
  · exact positiveLateralMass_rpow_lintegral_le_of_envelope P γ q hγ hq0 hq1 B Z hB hZ hfin hi
      L hL g hg
  · exact positiveLateralMass_rpow_lintegral_le_of_envelope_of_one_le P γ q hγ
      (le_of_lt (not_le.mp hq1)) B Z hB hZ hfin hi L hL g hg

/-- The block bound is finite when the lateral bound is finite and the envelopes are summable
(order at most one), or their `q`th roots are summable (order above one). -/
theorem halfLineBlockBound_lt_top {q : ℝ} (hq0 : 0 < q) {L : ℝ≥0∞} (hL : L < ⊤)
    {g : ℕ → ℝ≥0∞} (hg : q ≤ 1 → ∑' n, g n < ⊤) (hgroot : 1 < q → ∑' n, g n ^ (1 / q) < ⊤) :
    halfLineBlockBound q L g < ⊤ := by
  unfold halfLineBlockBound
  split_ifs with hq1
  · exact ENNReal.mul_lt_top hL (hg hq1)
  · apply ENNReal.rpow_lt_top_of_nonneg hq0.le
    have hsplit : ∀ n, (g n * L) ^ (1 / q) = g n ^ (1 / q) * L ^ (1 / q) := fun n =>
      ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hq0.le)
    simp_rw [hsplit, ENNReal.tsum_mul_right]
    exact (ENNReal.mul_lt_top (hgroot (lt_of_not_ge hq1))
      (ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hq0.le) hL.ne)).ne

/-- Two-sided reflection moments from half-line envelopes of the two paths. -/
theorem twoSidedReflectionMass_rpow_lintegral_le_blockBound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ q : ℝ) (hγ : 0 ≤ γ) (hq0 : 0 < q)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZm : AEMeasurable Z P)
    (hZfin : ∀ᵐ ω ∂P, ∀ a b : ℝ, Z ω (Icc a b) < ⊤) (hZ0 : ∀ᵐ ω ∂P, Z ω {0} = 0)
    (hInd : IndepFun B Z P)
    (L : ℝ≥0∞) (hL : ∀ a : ℝ, (∫⁻ ω, (Z ω (Icc a (a + 1))) ^ q ∂P) ≤ L)
    (g : ℕ → ℝ≥0∞)
    (hg₁ : ∀ n : ℕ, (∫⁻ ω, positiveBlockEnvelope (q * γ) n (B ω).1 ∂P) ≤ g n)
    (hg₂ : ∀ n : ℕ, (∫⁻ ω, positiveBlockEnvelope (q * γ) n (B ω).2 ∂P) ≤ g n) :
    (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ B Z ω) q ∂P) ≤
      3 ^ q * (halfLineBlockBound q L g + halfLineBlockBound q L g) := by
  let Z' : Ω → Measure ℝ := fun ω => (Z ω).map (fun s : ℝ => -s)
  have hB₁ : AEMeasurable (fun ω => (B ω).1) P := measurable_fst.comp_aemeasurable hB
  have hB₂ : AEMeasurable (fun ω => (B ω).2) P := measurable_snd.comp_aemeasurable hB
  have hZ'm : AEMeasurable Z' P := measurable_measure_map_neg.comp_aemeasurable hZm
  have hfin₁ : ∀ᵐ ω ∂P, ∀ a b : ℝ, Z ω (Ioc a b) < ⊤ := by
    filter_upwards [hZfin] with ω hω a b
    exact lt_of_le_of_lt (measure_mono Ioc_subset_Icc_self) (hω a b)
  have hfin₂ : ∀ᵐ ω ∂P, ∀ a b : ℝ, Z' ω (Ioc a b) < ⊤ := by
    filter_upwards [hZfin] with ω hω a b
    exact map_neg_Ioc_lt_top_of_Icc hω a b
  have hi₁ : IndepFun (fun ω => (B ω).1) Z P := hInd.comp measurable_fst measurable_id
  have hi₂ : IndepFun (fun ω => (B ω).2) Z' P :=
    hInd.comp measurable_snd measurable_measure_map_neg
  have hL₁ : ∀ n : ℕ, (∫⁻ ω, (Z ω (Ioc (n : ℝ) ((n : ℝ) + 1))) ^ q ∂P) ≤ L := by
    intro n
    refine le_trans (lintegral_mono fun ω => ?_) (hL n)
    exact ENNReal.rpow_le_rpow (measure_mono Ioc_subset_Icc_self) hq0.le
  have hL₂ : ∀ n : ℕ, (∫⁻ ω, (Z' ω (Ioc (n : ℝ) ((n : ℝ) + 1))) ^ q ∂P) ≤ L := by
    intro n
    refine le_trans (lintegral_mono fun ω => ?_) (hL (-((n : ℝ) + 1)))
    simp only [Z']
    rw [measure_map_neg_Ioc]
    refine ENNReal.rpow_le_rpow (measure_mono ?_) hq0.le
    intro x hx
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hH₁ := positiveLateralMass_rpow_lintegral_le_blockBound P γ q hγ hq0
    (fun ω => (B ω).1) Z hB₁ hZm hfin₁ hi₁ L hL₁ g hg₁
  have hH₂ := positiveLateralMass_rpow_lintegral_le_blockBound P γ q hγ hq0
    (fun ω => (B ω).2) Z' hB₂ hZ'm hfin₂ hi₂ L hL₂ g hg₂
  have hH₁m : AEMeasurable (fun ω => positiveLateralMass γ (B ω).1 (Z ω)) P :=
    positiveLateralMass_aemeasurable_of_finite P γ _ Z hB₁ hZm hfin₁
  have hH₂m : AEMeasurable (fun ω => positiveLateralMass γ (B ω).2 (Z' ω)) P :=
    positiveLateralMass_aemeasurable_of_finite P γ _ Z' hB₂ hZ'm hfin₂
  calc (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ B Z ω) q ∂P)
      ≤ ∫⁻ ω, 3 ^ q * ((positiveLateralMass γ (B ω).1 (Z ω)) ^ q +
          (positiveLateralMass γ (B ω).2 (Z' ω)) ^ q) ∂P := by
        apply lintegral_mono_ae
        filter_upwards [hZ0] with ω hω
        change (twoSidedReflectionMass γ B Z ω) ^ q ≤ _
        rw [twoSidedReflectionMass_eq_halves, hω, mul_zero, zero_add]
        calc (positiveLateralMass γ (B ω).1 (Z ω) + positiveLateralMass γ (B ω).2 (Z' ω)) ^ q
            = (0 + positiveLateralMass γ (B ω).1 (Z ω) +
                positiveLateralMass γ (B ω).2 (Z' ω)) ^ q := by rw [zero_add]
          _ ≤ 3 ^ q * (0 ^ q + (positiveLateralMass γ (B ω).1 (Z ω)) ^ q +
                (positiveLateralMass γ (B ω).2 (Z' ω)) ^ q) :=
              ennreal_add3_rpow_le _ _ _ hq0.le
          _ = _ := by rw [ENNReal.zero_rpow_of_pos hq0, zero_add]
    _ = 3 ^ q * ((∫⁻ ω, (positiveLateralMass γ (B ω).1 (Z ω)) ^ q ∂P) +
          ∫⁻ ω, (positiveLateralMass γ (B ω).2 (Z' ω)) ^ q ∂P) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq0.le
          (by norm_num : (3 : ℝ≥0∞) ≠ ⊤))]
        congr 1
        exact lintegral_add_left' ((ENNReal.continuous_rpow_const.measurable).comp_aemeasurable
          hH₁m) _
    _ ≤ 3 ^ q * (halfLineBlockBound q L g + halfLineBlockBound q L g) :=
        mul_le_mul_right (add_le_add hH₁ hH₂) _

end DOZZ.Proofs

end
