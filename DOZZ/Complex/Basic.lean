/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Complex.Defs
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Meromorphic.IsolatedZeros
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Elementary complex analysis

The dominated-integral theorem propagates integrability from the center by the
mean value inequality on the real-convex polydisc. Meromorphic normal forms
supply gluing and the dense-period identity while retaining the punctured-germ
formulation. Quantitative real layer cake supplies the uniform-family boundary
limit, and rational residue lemmas support the Mellin transform arguments.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The finite-coordinate polydisc is open, including in dimension zero. -/
theorem isOpen_complexPolydisc {N : ℕ} (a : Fin N → ℂ) (R : Fin N → ℝ) :
    IsOpen (complexPolydisc a R) := by
  have heq : complexPolydisc a R = ⋂ i, {z : Fin N → ℂ | ‖z i - a i‖ < R i} := by
    ext z
    simp [complexPolydisc]
  rw [heq]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt ((continuous_apply i).sub continuous_const).norm continuous_const

/-- Positive radii put the center in the polydisc. -/
theorem mem_complexPolydisc_center {N : ℕ} (a : Fin N → ℂ) (R : Fin N → ℝ)
    (hR : ∀ i, 0 < R i) : a ∈ complexPolydisc a R := by
  simpa [complexPolydisc] using hR

/-- Coordinate balls are real-convex, so their finite product is real-convex. -/
theorem convex_complexPolydisc {N : ℕ} (a : Fin N → ℂ) (R : Fin N → ℝ) :
    Convex ℝ (complexPolydisc a R) := by
  have h : complexPolydisc a R = Set.pi Set.univ (fun i => Metric.ball (a i) (R i)) := by
    ext z
    simp [complexPolydisc, Metric.mem_ball, dist_eq_norm]
  rw [h]
  exact convex_pi fun i _ => convex_ball (a i) (R i)

/-- Proof of `DOZZ.differentiableOn_integral_polydisc`: dominated differentiation on a polydisc. -/
theorem differentiableOn_integral_polydisc {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (P : Measure Ω) (a : Fin N → ℂ) (R : Fin N → ℝ)
    (hR : ∀ i, 0 < R i) (F : (Fin N → ℂ) → Ω → ℂ)
    (F' : (Fin N → ℂ) → Ω → ((Fin N → ℂ) →L[ℂ] ℂ)) (bound : Ω → ℝ)
    (hF : ∀ z ∈ complexPolydisc a R, AEStronglyMeasurable (F z) P)
    (hF' : ∀ z ∈ complexPolydisc a R, AEStronglyMeasurable (F' z) P)
    (hbase : Integrable (F a) P) (hbound : Integrable bound P)
    (hdom : ∀ᵐ ω ∂P, ∀ z ∈ complexPolydisc a R, ‖F' z ω‖ ≤ bound ω)
    (hderiv : ∀ᵐ ω ∂P, ∀ z ∈ complexPolydisc a R,
      HasFDerivAt (fun w => F w ω) (F' z ω) z) :
    DifferentiableOn ℂ (fun z => ∫ ω, F z ω ∂P) (complexPolydisc a R) ∧
      ∀ z ∈ complexPolydisc a R,
        Integrable (F z) P ∧ Integrable (F' z) P ∧
        HasFDerivAt (fun w => ∫ ω, F w ω ∂P) (∫ ω, F' z ω ∂P) z := by
  have ha := mem_complexPolydisc_center a R hR
  have hint : ∀ z ∈ complexPolydisc a R, Integrable (F z) P := by
    intro z hz
    have hdiff : Integrable (fun ω => F z ω - F a ω) P := by
      apply (hbound.norm.mul_const ‖z - a‖).mono' ((hF z hz).sub hbase.aestronglyMeasurable)
      filter_upwards [hdom, hderiv] with ω hb hd
      exact (Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun w hw => (hd w hw).hasFDerivWithinAt) hb
        (convex_complexPolydisc a R) ha hz).trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
    convert hdiff.add hbase using 1
    ext ω
    exact (sub_add_cancel _ _).symm
  have hresult : ∀ z ∈ complexPolydisc a R,
      Integrable (F z) P ∧ Integrable (F' z) P ∧
      HasFDerivAt (fun w => ∫ ω, F w ω ∂P) (∫ ω, F' z ω ∂P) z := by
    intro z hz
    have hderint : Integrable (F' z) P := by
      apply hbound.norm.mono' (hF' z hz)
      filter_upwards [hdom] with ω hb
      exact (hb z hz).trans (le_abs_self _)
    have hnhds := (isOpen_complexPolydisc a R).mem_nhds hz
    exact ⟨hint z hz, hderint,
      hasFDerivAt_integral_of_dominated_of_fderiv_le hnhds
        (Filter.eventually_of_mem hnhds fun w hw => hF w hw) (hint z hz) (hF' z hz) hdom hbound hderiv⟩
  exact ⟨fun z hz => (hresult z hz).2.2.differentiableAt.differentiableWithinAt, hresult⟩

/-- Compatible meromorphic germs have equal normalized values on an overlap. -/
theorem normalized_eq_of_compatible_germs {ι : Type*} (U : ι → Set ℂ)
    (f : ι → ℂ → ℂ) (hf : ∀ i, MeromorphicOn (f i) (U i))
    (hcompat : ∀ i j z, z ∈ U i → z ∈ U j → f i =ᶠ[𝓝[≠] z] f j)
    (i j : ι) (z : ℂ) (hi : z ∈ U i) (hj : z ∈ U j) :
    toMeromorphicNFOn (f i) (U i) z = toMeromorphicNFOn (f j) (U j) z := by
  have hni := meromorphicNFOn_toMeromorphicNFOn (f i) (U i) hi
  have hnj := meromorphicNFOn_toMeromorphicNFOn (f j) (U j) hj
  have hne := ((hf i).toMeromorphicNFOn_eq_self_on_nhdsNE hi).trans
    ((hcompat i j z hi hj).trans
      ((hf j).toMeromorphicNFOn_eq_self_on_nhdsNE hj).symm)
  exact ((hni.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hnj).mp hne).eq_of_nhds

/-- A normalized representative can be selected without assuming a nonempty index type.

On the union we choose an index containing the point; on its complement the
value is immaterial. Compatibility makes this choice locally equal to every
normalized piece, which proves meromorphicity and the required germ equality.
-/
theorem exists_meromorphicOn_iUnion_gluing {ι : Type*}
    (U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i)) (f : ι → ℂ → ℂ)
    (hf : ∀ i, MeromorphicOn (f i) (U i))
    (hcompat : ∀ i j z, z ∈ U i → z ∈ U j → f i =ᶠ[𝓝[≠] z] f j) :
    ∃ F : ℂ → ℂ, MeromorphicOn F (⋃ i, U i) ∧
      (∀ i z, z ∈ U i → F =ᶠ[𝓝[≠] z] f i) := by
  classical
  let index (z : ℂ) (hz : z ∈ ⋃ i, U i) : ι := Classical.choose (mem_iUnion.mp hz)
  have hindex (z : ℂ) (hz : z ∈ ⋃ i, U i) : z ∈ U (index z hz) :=
    Classical.choose_spec (mem_iUnion.mp hz)
  let F : ℂ → ℂ := fun z => if hz : z ∈ ⋃ i, U i then
    toMeromorphicNFOn (f (index z hz)) (U (index z hz)) z else 0
  have heq (i : ι) (z : ℂ) (hz : z ∈ U i) :
      F z = toMeromorphicNFOn (f i) (U i) z := by
    have hzu : z ∈ ⋃ i, U i := mem_iUnion.mpr ⟨i, hz⟩
    simp only [F, dite_eq_left hzu]
    exact normalized_eq_of_compatible_germs U f hf hcompat _ i z (hindex z hzu) hz
  have hlocal (i : ι) (z : ℂ) (hz : z ∈ U i) :
      F =ᶠ[𝓝 z] toMeromorphicNFOn (f i) (U i) :=
    Filter.eventually_of_mem ((hU i).mem_nhds hz) fun w hw => heq i w hw
  have hpiece (i : ι) (z : ℂ) (hz : z ∈ U i) : F =ᶠ[𝓝[≠] z] f i :=
    ((hlocal i z hz).filter_mono nhdsWithin_le_nhds).trans
      ((hf i).toMeromorphicNFOn_eq_self_on_nhdsNE hz)
  refine ⟨F, ?_, hpiece⟩
  intro z hz
  obtain ⟨i, hi⟩ := mem_iUnion.mp hz
  exact (MeromorphicAt.meromorphicAt_congr (hpiece i z hi)).mpr (hf i z hi)

/-- Proof of `DOZZ.exists_meromorphicOn_strip_gluing`: strip gluing, including uniqueness at the
level of germs. -/
theorem exists_meromorphicOn_strip_gluing {ι : Type*}
    (h : ℝ) (hh : 0 < h) (U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = horizontalStrip h) (f : ι → ℂ → ℂ)
    (hf : ∀ i, MeromorphicOn (f i) (U i))
    (hcompat : ∀ i j z, z ∈ U i → z ∈ U j → f i =ᶠ[𝓝[≠] z] f j) :
    ∃ F : ℂ → ℂ, MeromorphicOn F (horizontalStrip h) ∧
      (∀ i z, z ∈ U i → F =ᶠ[𝓝[≠] z] f i) ∧
      (∀ G : ℂ → ℂ, MeromorphicOn G (horizontalStrip h) →
        (∀ i z, z ∈ U i → G =ᶠ[𝓝[≠] z] f i) →
        ∀ z ∈ horizontalStrip h, F =ᶠ[𝓝[≠] z] G) := by
  have _positive_width : 0 < h := hh
  obtain ⟨F, hF, hpiece⟩ := exists_meromorphicOn_iUnion_gluing U hU f hf hcompat
  refine ⟨F, hcover ▸ hF, hpiece, ?_⟩
  intro G _ hG z hz
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ hz)
  exact (hpiece i z hi).trans (hG i z hi).symm

/-- Real translations preserve the strip, in both directions. -/
@[simp] theorem add_real_mem_horizontalStrip (h : ℝ) (z : ℂ) (t : ℝ) :
    z + (t : ℂ) ∈ horizontalStrip h ↔ z ∈ horizontalStrip h := by
  simp [horizontalStrip]

/-- The strip is open. -/
theorem isOpen_horizontalStrip (h : ℝ) : IsOpen (horizontalStrip h) :=
  isOpen_lt Complex.continuous_im.abs continuous_const

/-- The strip is convex over the reals. -/
theorem convex_horizontalStrip (h : ℝ) : Convex ℝ (horizontalStrip h) := by
  have heq : horizontalStrip h = Complex.imCLM ⁻¹' Ioo (-h) h := by
    ext z
    simp [horizontalStrip, abs_lt]
  rw [heq]
  exact (convex_Ioo (-h) h).linear_preimage Complex.imCLM.toLinearMap

/-- Positive strip width puts the origin in its interior. -/
theorem zero_mem_horizontalStrip {h : ℝ} (hh : 0 < h) :
    (0 : ℂ) ∈ horizontalStrip h := by
  simpa [horizontalStrip] using hh

/-- Germ periods become value periods after normalization.

Normal form, rather than continuity of a possibly polar representative, supplies
the implication from punctured equality to equality at the center.
-/
theorem normalized_period_on_strip (h : ℝ) (f : ℂ → ℂ)
    (hf : MeromorphicOn f (horizontalStrip h)) (t : ℝ)
    (hp : ∀ z ∈ horizontalStrip h,
      (fun w => f (w + (t : ℂ))) =ᶠ[𝓝[≠] z] f) :
    ∀ z ∈ horizontalStrip h,
      toMeromorphicNFOn f (horizontalStrip h) (z + (t : ℂ)) =
        toMeromorphicNFOn f (horizontalStrip h) z := by
  intro z hz
  let g := toMeromorphicNFOn f (horizontalStrip h)
  have hshift : z + (t : ℂ) ∈ horizontalStrip h :=
    (add_real_mem_horizontalStrip h z t).mpr hz
  have htrans : Tendsto (fun w : ℂ => w + (t : ℂ))
      (𝓝[≠] z) (𝓝[≠] (z + (t : ℂ))) := by
    change Filter.map (Homeomorph.addRight (t : ℂ)) (𝓝[≠] z) ≤ _
    rw [Homeomorph.map_punctured_nhds_eq]
    exact le_rfl
  have hne : (fun w => g (w + (t : ℂ))) =ᶠ[𝓝[≠] z] g :=
    ((hf.toMeromorphicNFOn_eq_self_on_nhdsNE hshift).comp_tendsto htrans).trans
      ((hp z hz).trans (hf.toMeromorphicNFOn_eq_self_on_nhdsNE hz).symm)
  have hn := meromorphicNFOn_toMeromorphicNFOn f (horizontalStrip h)
  have hntrans : MeromorphicNFAt (fun w => g (w + (t : ℂ))) z :=
    (hn hshift).comp_analyticAt (g := fun w => w + (t : ℂ)) (by fun_prop)
  exact ((hntrans.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hn hz)).mp hne).eq_of_nhds

/-- The real value periods on a strip form an additive subgroup. -/
def stripPeriodSubgroup (h : ℝ) (g : ℂ → ℂ) : AddSubgroup ℝ where
  carrier := {t | ∀ z ∈ horizontalStrip h, g (z + (t : ℂ)) = g z}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb z hz
    calc
      g (z + ((a + b : ℝ) : ℂ)) = g ((z + (a : ℂ)) + (b : ℂ)) := by
        rw [Complex.ofReal_add, add_assoc]
      _ = g (z + (a : ℂ)) := hb _ ((add_real_mem_horizontalStrip h z a).mpr hz)
      _ = g z := ha z hz
  neg_mem' := by
    intro a ha z hz
    have hz' := (add_real_mem_horizontalStrip h z (-a)).mpr hz
    have heq := ha (z + ((-a : ℝ) : ℂ)) hz'
    simpa using heq.symm

/-- Dense real periods give equal values arbitrarily close to each point.

Only positive periods in an arbitrarily small interval are used, so every
witness differs from the center. No continuity assumption is needed here.
-/
theorem frequently_eq_of_dense_stripPeriods (h : ℝ) (g : ℂ → ℂ)
    (hdense : Dense (stripPeriodSubgroup h g : Set ℝ))
    (z : ℂ) (hz : z ∈ horizontalStrip h) :
    ∃ᶠ w in 𝓝[≠] z, g w = g z := by
  rw [Filter.frequently_iff]
  intro V hV
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hV
  obtain ⟨t, ht, htpos, htlt⟩ := hdense.exists_mem_open isOpen_Ioo
    (show (Ioo (0 : ℝ) ε).Nonempty from ⟨ε / 2, by constructor <;> linarith⟩)
  refine ⟨z + (t : ℂ), hball ⟨?_, ?_⟩, ht z hz⟩
  · simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
    exact htlt
  · simp only [mem_compl_iff, mem_singleton_iff, add_eq_left]
    exact_mod_cast htpos.ne'

/-- A meromorphic function in normal form with dense value periods is locally constant.

The isolated-zero principle applied to `g - g z` rules out poles at the same
time that it proves constancy. In particular, no regular-point selection or
separate argument about polar orders is necessary.
-/
theorem locally_constant_of_dense_stripPeriods (h : ℝ) (g : ℂ → ℂ)
    (hg : MeromorphicNFOn g (horizontalStrip h))
    (hdense : Dense (stripPeriodSubgroup h g : Set ℝ)) :
    ∀ z ∈ horizontalStrip h, g =ᶠ[𝓝 z] (fun _ => g z) := by
  intro z hz
  have hne : g =ᶠ[𝓝[≠] z] (fun _ => g z) :=
    ((hg hz).meromorphicAt.frequently_eq_iff_eventuallyEq analyticAt_const.meromorphicAt).mp
      (frequently_eq_of_dense_stripPeriods h g hdense z hz)
  exact ((hg hz).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    analyticAt_const.meromorphicNFAt).mp hne

/-- Proof of `DOZZ.meromorphicOn_strip_constant_of_dense_periods`: the dense-period identity, with
uniqueness of the constant germ. -/
theorem meromorphicOn_strip_constant_of_dense_periods
    (h : ℝ) (hh : 0 < h) (f : ℂ → ℂ) (hf : MeromorphicOn f (horizontalStrip h))
    (T₁ T₂ : ℝ) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (hirr : ∀ q : ℚ, T₁ / T₂ ≠ (q : ℝ))
    (hp₁ : ∀ z ∈ horizontalStrip h,
      (fun w => f (w + (T₁ : ℂ))) =ᶠ[𝓝[≠] z] f)
    (hp₂ : ∀ z ∈ horizontalStrip h,
      (fun w => f (w + (T₂ : ℂ))) =ᶠ[𝓝[≠] z] f) :
    ∃! c : ℂ, ∀ z ∈ horizontalStrip h, f =ᶠ[𝓝[≠] z] (fun _ => c) := by
  have _positive_periods := And.intro hT₁ hT₂
  let g := toMeromorphicNFOn f (horizontalStrip h)
  have hn : MeromorphicNFOn g (horizontalStrip h) :=
    meromorphicNFOn_toMeromorphicNFOn f (horizontalStrip h)
  have h₁ : T₁ ∈ stripPeriodSubgroup h g := normalized_period_on_strip h f hf T₁ hp₁
  have h₂ : T₂ ∈ stripPeriodSubgroup h g := normalized_period_on_strip h f hf T₂ hp₂
  have hirr' : Irrational (T₁ / T₂) := by
    rintro ⟨q, hq⟩
    exact hirr q hq.symm
  have hdense : Dense (stripPeriodSubgroup h g : Set ℝ) :=
    (dense_addSubgroupClosure_pair_iff.mpr hirr').mono
      ((AddSubgroup.closure_le _).mpr (by simpa only [pair_subset_iff, SetLike.mem_coe] using And.intro h₁ h₂))
  have hlocal := locally_constant_of_dense_stripPeriods h g hn hdense
  have hder : ∀ z ∈ horizontalStrip h, HasDerivAt g 0 z := fun z hz =>
    (hlocal z hz).hasDerivAt_iff.mpr (hasDerivAt_const z (g z))
  have hopen := isOpen_horizontalStrip h
  have hconn := (convex_horizontalStrip h).isPreconnected
  have hzero := zero_mem_horizontalStrip hh
  have heq : ∀ z ∈ horizontalStrip h, g z = g 0 := fun z hz =>
    hopen.is_const_of_deriv_eq_zero hconn
      (fun w hw => (hder w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hder w hw).deriv) hz hzero
  have hconstant : ∀ z ∈ horizontalStrip h, f =ᶠ[𝓝[≠] z] (fun _ => g 0) := by
    intro z hz
    exact (hf.toMeromorphicNFOn_eq_self_on_nhdsNE hz).symm.trans
      ((Filter.eventually_of_mem (hopen.mem_nhds hz) fun w hw => heq w hw).filter_mono nhdsWithin_le_nhds)
  refine ⟨g 0, hconstant, ?_⟩
  intro c hc
  have he := (hc 0 hzero).symm.trans (hconstant 0 hzero)
  obtain ⟨w, hw⟩ := he.exists
  exact hw

/-- The rational subtraction is meromorphic on the entire plane.

Its totalized values at the poles are irrelevant to meromorphicity. Neither
nonzero coefficients nor a strict ordering of the two poles is needed here.
-/
theorem meromorphic_twoTailRational (c₁ c₂ β₁ β₂ : ℝ) :
    Meromorphic (twoTailRational c₁ c₂ β₁ β₂) := by
  intro z
  unfold twoTailRational
  fun_prop

/-- Clearing just the pole being tested gives an expression continuous there.

The other denominator stays nonzero. Keeping the equality on the punctured
neighborhood avoids claiming equality of totalized functions at the pole.
-/
theorem pole_product_eventuallyEq (p q c d : ℂ) (r : ℂ → ℂ) :
    (fun s => (s - p) * (c * s / (p - s) + d * s / (q - s) + r s))
      =ᶠ[𝓝[≠] p]
    (fun s => -c * s + (s - p) * (d * s / (q - s) + r s)) := by
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsp : s ≠ p := by simpa using hs
  have hps : p - s ≠ 0 := sub_ne_zero.mpr hsp.symm
  calc
    (s - p) * (c * s / (p - s) + d * s / (q - s) + r s) =
        (s - p) * (c * s / (p - s)) +
          (s - p) * (d * s / (q - s) + r s) := by ring
    _ = -c * s + (s - p) * (d * s / (q - s) + r s) := by
      congr 1
      field_simp
      ring

/-- A holomorphic remainder does not affect the residue of a distinct simple pole.

Continuity at the pole suffices for this supporting lemma. The Mellin transform theorems
still require the construction and holomorphy of their remainders from the
probabilistic hypotheses.
-/
theorem tendsto_pole_product (p q c d : ℂ) (hpq : p ≠ q)
    (r : ℂ → ℂ) (hr : ContinuousAt r p) :
    Tendsto (fun s => (s - p) * (c * s / (p - s) + d * s / (q - s) + r s))
      (𝓝[≠] p) (𝓝 (-c * p)) := by
  have hother : ContinuousAt (fun s => d * s / (q - s) + r s) p :=
    ((continuousAt_const.mul continuousAt_id).div
      (continuousAt_const.sub continuousAt_id) (sub_ne_zero.mpr hpq.symm)).add hr
  have hcont : ContinuousAt
      (fun s => -c * s + (s - p) * (d * s / (q - s) + r s)) p :=
    (continuousAt_const.mul continuousAt_id).add
      ((continuousAt_id.sub continuousAt_const).mul hother)
  have ht : Tendsto
      (fun s => -c * s + (s - p) * (d * s / (q - s) + r s))
      (𝓝[≠] p) (𝓝 (-c * p)) := by
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  exact ht.congr' (pole_product_eventuallyEq p q c d r).symm

/-- The first rational residue, provided the remainder is continuous there. -/
theorem tendsto_twoTailRational_first (c₁ c₂ β₁ β₂ : ℝ) (hβ : β₁ ≠ β₂)
    (r : ℂ → ℂ) (hr : ContinuousAt r (β₁ : ℂ)) :
    Tendsto (fun s => (s - (β₁ : ℂ)) * (twoTailRational c₁ c₂ β₁ β₂ s + r s))
      (𝓝[≠] (β₁ : ℂ)) (𝓝 (-(β₁ * c₁ : ℝ) : ℂ)) := by
  have hne : (β₁ : ℂ) ≠ (β₂ : ℂ) := by exact_mod_cast hβ
  have ht := tendsto_pole_product (β₁ : ℂ) (β₂ : ℂ) (c₁ : ℂ) (c₂ : ℂ) hne r hr
  have hid : (-(β₁ * c₁ : ℝ) : ℂ) = -(c₁ : ℂ) * (β₁ : ℂ) := by
    push_cast
    ring
  rw [hid]
  exact ht

/-- The second rational residue, provided the remainder is continuous there. -/
theorem tendsto_twoTailRational_second (c₁ c₂ β₁ β₂ : ℝ) (hβ : β₁ ≠ β₂)
    (r : ℂ → ℂ) (hr : ContinuousAt r (β₂ : ℂ)) :
    Tendsto (fun s => (s - (β₂ : ℂ)) * (twoTailRational c₁ c₂ β₁ β₂ s + r s))
      (𝓝[≠] (β₂ : ℂ)) (𝓝 (-(β₂ * c₂ : ℝ) : ℂ)) := by
  have ht := tendsto_twoTailRational_first c₂ c₁ β₂ β₁ hβ.symm r hr
  convert ht using 1
  funext s
  unfold twoTailRational
  ring

/-- The positive moment strip is open. -/
theorem isOpen_positiveMomentStrip (b : ℝ) : IsOpen (positiveMomentStrip b) := by
  change IsOpen ({s : ℂ | 0 < s.re} ∩ {s : ℂ | s.re < b})
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

/-- A point strictly between the two positive-real-part boundaries lies in the strip. -/
theorem mem_positiveMomentStrip_real {b t : ℝ} (ht : 0 < t) (htb : t < b) :
    (t : ℂ) ∈ positiveMomentStrip b := by
  exact ⟨ht, htb⟩

/-- The upper tail is measurable as a real function of the threshold. -/
theorem measurable_realUpperTail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : AEMeasurable Y P) :
    Measurable (realUpperTail P Y hY) := by
  exact (show Antitone (fun t => P {ω | t < Y ω}) from
    fun _ _ hst => measure_mono fun _ hy => hst.trans_lt hy).measurable.ennreal_toReal

/-- The tail is nonnegative and at most one. -/
theorem realUpperTail_bounds {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : AEMeasurable Y P) (t : ℝ) :
    0 ≤ realUpperTail P Y hY t ∧ realUpperTail P Y hY t ≤ 1 :=
  ⟨ENNReal.toReal_nonneg, measureReal_le_one⟩

/-- Positive-order layer cake, with integrability deduced from the weighted tail.

This bridges Mathlib's nonnegative extended integral to an ordinary integral.
It requires only a.e. measurability of the random variable. Integrability is
proved before the ordinary integral is used.
-/
theorem integral_rpow_eq_tail_of_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : AEMeasurable Y P)
    (hpos : ∀ᵐ ω ∂P, 0 ≤ Y ω) (p : ℝ) (hp : 0 < p)
    (htail : IntegrableOn (fun t => realUpperTail P Y hY t * t ^ (p - 1)) (Ioi 0)) :
    Integrable (fun ω => Y ω ^ p) P ∧
      (∫ ω, Y ω ^ p ∂P) = p * ∫ t in Ioi 0, realUpperTail P Y hY t * t ^ (p - 1) := by
  have hynn : 0 ≤ᵐ[P] (fun ω => Y ω ^ p) := hpos.mono fun ω hω => Real.rpow_nonneg hω p
  have hym : AEStronglyMeasurable (fun ω => Y ω ^ p) P :=
    (hY.pow_const p).aestronglyMeasurable
  have htnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t => realUpperTail P Y hY t * t ^ (p - 1)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg ht.le _)
  have heq : (∫⁻ t in Ioi (0 : ℝ), P {ω | t < Y ω} * ENNReal.ofReal (t ^ (p - 1))) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (realUpperTail P Y hY t * t ^ (p - 1)) := by
    apply lintegral_congr
    intro t
    unfold realUpperTail
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (measure_ne_top P _)]
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul P hpos hY hp
  rw [heq] at hlayer
  have hint : Integrable (fun ω => Y ω ^ p) P := by
    refine ⟨hym, (hasFiniteIntegral_iff_ofReal hynn).mpr ?_⟩
    rw [hlayer]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ((hasFiniteIntegral_iff_ofReal htnn).mp htail.hasFiniteIntegral)
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hynn hym, hlayer, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hp.le]
  rw [← integral_eq_lintegral_of_nonneg_ae htnn htail.aestronglyMeasurable]

/-- A strict power tail gives a finite moment and a quantitative subtraction error.

The bounded-mass contribution costs at most one. The error on `(1, ∞)`
costs `C * p / (β + η - p)`. This bound is uniform in the distribution and
its tail coefficient, which is the input needed for the family bridge.
-/
theorem realMoment_tail_error {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : AEMeasurable Y P)
    (hpos : ∀ᵐ ω ∂P, 0 ≤ Y ω) (c β η C p : ℝ)
    (hp : 0 < p) (hpβ : p < β) (hη : 0 < η) (_hC : 0 ≤ C)
    (htail : ∀ t : ℝ, 1 ≤ t →
      |realUpperTail P Y hY t - c * t ^ (-β)| ≤ C * t ^ (-β - η)) :
    Integrable (fun ω => Y ω ^ p) P ∧
      |(∫ ω, Y ω ^ p ∂P) - c * p / (β - p)| ≤ 1 + C * p / (β + η - p) := by
  let T := fun t => realUpperTail P Y hY t * t ^ (p - 1)
  let E := fun t => (realUpperTail P Y hY t - c * t ^ (-β)) * t ^ (p - 1)
  let M := fun t : ℝ => c * t ^ (p - 1 - β)
  have hmT : Measurable T :=
    (measurable_realUpperTail P Y hY).mul (measurable_id.pow_const _)
  have hmE : Measurable E :=
    ((measurable_realUpperTail P Y hY).sub
      ((measurable_id.pow_const _).const_mul c)).mul (measurable_id.pow_const _)
  have hlowPow : IntegrableOn (fun t : ℝ => t ^ (p - 1)) (Ioc 0 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith)
  have hlowDom : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1), ‖T t‖ ≤ t ^ (p - 1) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    have hb := realUpperTail_bounds P Y hY t
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb.1 (Real.rpow_nonneg ht.1.le _))]
    exact mul_le_of_le_one_left (Real.rpow_nonneg ht.1.le _) hb.2
  have hlow : IntegrableOn T (Ioc 0 1) := hlowPow.mono' hmT.aestronglyMeasurable.restrict hlowDom
  have hEPow : IntegrableOn (fun t : ℝ => C * t ^ (p - 1 - β - η)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : p - 1 - β - η < -1) zero_lt_one).const_mul C
  have hEDom : ∀ᵐ t ∂volume.restrict (Ioi (1 : ℝ)), ‖E t‖ ≤ C * t ^ (p - 1 - β - η) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    calc
      ‖E t‖ = |realUpperTail P Y hY t - c * t ^ (-β)| * t ^ (p - 1) := by
        dsimp only [E]
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      _ ≤ (C * t ^ (-β - η)) * t ^ (p - 1) :=
        mul_le_mul_of_nonneg_right (htail t ht.le) (Real.rpow_nonneg ht0.le _)
      _ = C * t ^ (p - 1 - β - η) := by
        rw [mul_assoc, ← Real.rpow_add ht0]
        congr 2
        ring
  have hE : IntegrableOn E (Ioi 1) := hEPow.mono' hmE.aestronglyMeasurable.restrict hEDom
  have hM : IntegrableOn M (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : p - 1 - β < -1) zero_lt_one).const_mul c
  have hdecomp : EqOn (fun t => E t + M t) T (Ioi 1) := by
    intro t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hpow : t ^ (-β) * t ^ (p - 1) = t ^ (p - 1 - β) := by
      rw [← Real.rpow_add ht0]
      congr 1
      ring
    dsimp [E, M, T]
    rw [sub_mul, mul_assoc, hpow]
    ring
  have hhigh : IntegrableOn T (Ioi 1) :=
    (hE.add hM).congr_fun hdecomp measurableSet_Ioi
  have hwhole : IntegrableOn T (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 from zero_le_one), integrableOn_union]
    exact ⟨hlow, hhigh⟩
  obtain ⟨hint, hmoment⟩ := integral_rpow_eq_tail_of_integrable P Y hY hpos p hp hwhole
  have hpowLow : (∫ t : ℝ in Ioc 0 1, t ^ (p - 1)) = 1 / p := by
    rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 from zero_le_one),
      integral_rpow (Or.inl (by linarith : -1 < p - 1))]
    simp [Real.zero_rpow hp.ne', sub_add_cancel]
  have hpowHigh (a : ℝ) (ha : a < -1) :
      (∫ t : ℝ in Ioi 1, t ^ a) = -1 / (a + 1) := by
    simpa using integral_Ioi_rpow_of_lt ha zero_lt_one
  have hMint : (∫ t in Ioi 1, M t) = c / (β - p) := by
    dsimp only [M]
    rw [integral_const_mul, hpowHigh _ (by linarith)]
    have heq : p - 1 - β + 1 = -(β - p) := by ring
    rw [heq]
    field_simp
  have hEbound : |∫ t in Ioi 1, E t| ≤ C / (β + η - p) := by
    have hb := norm_integral_le_of_norm_le hEPow hEDom
    rw [Real.norm_eq_abs, integral_const_mul, hpowHigh _ (by linarith)] at hb
    have heq : p - 1 - β - η + 1 = -(β + η - p) := by ring
    rw [heq] at hb
    have halg : C * (-1 / -(β + η - p)) = C / (β + η - p) := by
      simp only [div_neg, neg_div, neg_neg, mul_one_div]
    rwa [halg] at hb
  have hlowBound : |∫ t in Ioc 0 1, T t| ≤ 1 / p := by
    simpa only [Real.norm_eq_abs, hpowLow] using norm_integral_le_of_norm_le hlowPow hlowDom
  have hsplit : (∫ t in Ioi 0, T t) =
      (∫ t in Ioc 0 1, T t) + (∫ t in Ioi 1, E t) + c / (β - p) := by
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 from zero_le_one),
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hlow hhigh]
    rw [← setIntegral_congr_fun measurableSet_Ioi hdecomp, integral_add hE hM, hMint]
    ring
  refine ⟨hint, ?_⟩
  calc
    |(∫ ω, Y ω ^ p ∂P) - c * p / (β - p)| =
        p * |(∫ t in Ioc 0 1, T t) + (∫ t in Ioi 1, E t)| := by
      rw [hmoment, hsplit]
      have halg : p * (((∫ t in Ioc 0 1, T t) + (∫ t in Ioi 1, E t)) +
          c / (β - p)) - c * p / (β - p) =
          p * ((∫ t in Ioc 0 1, T t) + (∫ t in Ioi 1, E t)) := by ring
      rw [halg, abs_mul, abs_of_pos hp]
    _ ≤ p * (|∫ t in Ioc 0 1, T t| + |∫ t in Ioi 1, E t|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) hp.le
    _ ≤ p * (1 / p + C / (β + η - p)) :=
      mul_le_mul_of_nonneg_left (add_le_add hlowBound hEbound) hp.le
    _ = 1 + C * p / (β + η - p) := by
      rw [mul_add, mul_one_div_cancel hp.ne']
      ring

/-- Exact uniform-family bridge; the proof first controls real moments uniformly. -/
theorem complexMoment_uniform_tail_bridge {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℝ → Ω → ℝ)
    (c : ℝ → ℝ) (c₀ β η γ d₀ C : ℝ)
    (hβ : 0 < β) (hη : 0 < η) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hC : 0 ≤ C)
    (hY : ∀ d : ℝ, 0 < d → d < d₀ → AEMeasurable (Y d) P)
    (hpos : ∀ d : ℝ, 0 < d → d < d₀ → ∀ᵐ ω ∂P, 0 ≤ Y d ω)
    (hc : Tendsto c (𝓝[>] 0) (𝓝 c₀))
    (htail : ∀ (d : ℝ) (hd : 0 < d) (hd' : d < d₀) (t : ℝ), 1 ≤ t →
      |realUpperTail P (Y d) (hY d hd hd') t - c d * t ^ (-β)| ≤ C * t ^ (-β - η)) :
    (∀ d : ℝ, 0 < d → d < min d₀ (γ * β) →
      Integrable (fun ω => (Y d ω : ℂ) ^ ((β - d / γ : ℝ) : ℂ)) P) ∧
    Tendsto (fun d : ℝ => (d : ℂ) *
      (∫ ω, (Y d ω : ℂ) ^ ((β - d / γ : ℝ) : ℂ) ∂P))
      (𝓝[>] 0) (𝓝 ((γ * β * c₀ : ℝ) : ℂ)) := by
  let p : ℝ → ℝ := fun d => β - d / γ
  let m : ℝ → ℝ := fun d => ∫ ω, Y d ω ^ p d ∂P
  have hmin : 0 < min d₀ (γ * β) := lt_min hd₀ (mul_pos hγ hβ)
  have hexp (d : ℝ) (hd : 0 < d) (hd' : d < min d₀ (γ * β)) :
      0 < p d ∧ p d < β := by
    have hdiv : d / γ < β := (div_lt_iff₀ hγ).mpr (by simpa [mul_comm] using (lt_min_iff.mp hd').2)
    have hdivpos := div_pos hd hγ
    dsimp [p]
    constructor <;> linarith
  have hmoment (d : ℝ) (hd : 0 < d) (hd' : d < min d₀ (γ * β)) :
      Integrable (fun ω => Y d ω ^ p d) P ∧
      |m d - c d * p d / (β - p d)| ≤ 1 + C * p d / (β + η - p d) := by
    have hd₀' := (lt_min_iff.mp hd').1
    exact realMoment_tail_error P (Y d) (hY d hd hd₀') (hpos d hd hd₀')
      (c d) β η C (p d) (hexp d hd hd').1 (hexp d hd hd').2 hη hC (htail d hd hd₀')
  have hcpow (d : ℝ) (hd : 0 < d) (hd' : d < d₀) :
      (fun ω => (Y d ω : ℂ) ^ ((p d : ℝ) : ℂ)) =ᵐ[P]
        (fun ω => ((Y d ω ^ p d : ℝ) : ℂ)) :=
    (hpos d hd hd').mono fun ω hω => (Complex.ofReal_cpow hω (p d)).symm
  have hnear : ∀ᶠ d : ℝ in 𝓝[>] 0, 0 < d ∧ d < min d₀ (γ * β) := by
    filter_upwards [self_mem_nhdsWithin,
      (Filter.eventually_of_mem (Iio_mem_nhds hmin) fun d hd => hd).filter_mono nhdsWithin_le_nhds]
      with d hd hd' using ⟨hd, hd'⟩
  have herrBound : ∀ᶠ d : ℝ in 𝓝[>] 0,
      ‖d * m d - γ * p d * c d‖ ≤ d * (1 + C * β / η) := by
    filter_upwards [hnear] with d hd
    have hpd := hexp d hd.1 hd.2
    have hrat : p d / (β + η - p d) ≤ β / η :=
      (div_le_div_of_nonneg_left hpd.1.le hη (by linarith)).trans
        (div_le_div_of_nonneg_right hpd.2.le hη.le)
    have halg : d * m d - γ * p d * c d =
        d * (m d - c d * p d / (β - p d)) := by
      dsimp only [p]
      field_simp [hd.1.ne', hγ.ne']
      ring
    rw [halg, Real.norm_eq_abs, abs_mul, abs_of_pos hd.1]
    calc
      d * |m d - c d * p d / (β - p d)| ≤
          d * (1 + C * p d / (β + η - p d)) :=
        mul_le_mul_of_nonneg_left (hmoment d hd.1 hd.2).2 hd.1.le
      _ ≤ d * (1 + C * β / η) := by
        apply mul_le_mul_of_nonneg_left _ hd.1.le
        have hs : C * p d / (β + η - p d) ≤ C * β / η := by
          simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hrat hC
        exact add_le_add le_rfl hs
  have hdlim : Tendsto (fun d : ℝ => d) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hplim : Tendsto p (𝓝[>] 0) (𝓝 β) := by
    simpa [p] using tendsto_const_nhds.sub (hdlim.div_const γ)
  have herr : Tendsto (fun d => d * m d - γ * p d * c d) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
    squeeze_zero_norm' herrBound (by simpa using hdlim.mul_const (1 + C * β / η))
  have hmain : Tendsto (fun d => γ * p d * c d) (𝓝[>] 0) (𝓝 (γ * β * c₀)) :=
    (tendsto_const_nhds.mul hplim).mul hc
  have hreal : Tendsto (fun d => d * m d) (𝓝[>] 0) (𝓝 (γ * β * c₀)) := by
    simpa only [sub_add_cancel, zero_add] using herr.add hmain
  refine ⟨?_, ?_⟩
  · intro d hd hd'
    exact (Complex.ofRealCLM.integrable_comp (hmoment d hd hd').1).congr
      (hcpow d hd (lt_min_iff.mp hd').1).symm
  · have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
    apply hcomplex.congr'
    filter_upwards [hnear] with d hd
    rw [integral_congr_ae (hcpow d hd.1 (lt_min_iff.mp hd.2).1), integral_complex_ofReal]
    exact Complex.ofReal_mul d (m d)

end DOZZ.Proofs
