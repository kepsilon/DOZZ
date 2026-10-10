/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.AdmissibleGMCCountableTests
public import DOZZ.GMC.AdmissibleGMCRestriction
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Topology.Algebra.Support

/-! Countable dense compact tests determine locally finite measures carried by an open chart. -/

@[expose] public section

open MeasureTheory Set Topology
open scoped Topology CompactlySupported ENNReal

namespace DOZZ.Proofs

/-- A countable family of locally dense compactly supported tests determines locally finite
measures carried by an open planar chart. -/
theorem admissible_countable_tests_determine_chart_measures
    (U : Set ℂ) (hU : IsOpen U) (μ ν : Measure ℂ)
    (hμsupp : μ Uᶜ = 0) (hνsupp : ν Uᶜ = 0)
    (hμfin : ∀ K : Set ℂ, IsCompact K → K ⊆ U → μ K < ∞)
    (hνfin : ∀ K : Set ℂ, IsCompact K → K ⊆ U → ν K < ∞)
    (K : ℕ → Set ℂ)
    (hKcompact : ∀ n, IsCompact (K n)) (hKU : ∀ n, K n ⊆ U)
    (hKcofinal : ∀ L, IsCompact L → L ⊆ U → ∃ n, L ⊆ K n)
    (f : ℕ × ℕ → BoundedContinuousFunction ℂ ℝ)
    (hfK : ∀ n m, HasCompactSupport (f (n, m) : ℂ → ℝ) ∧
      tsupport (f (n, m) : ℂ → ℝ) ⊆ K n)
    (hdense : ∀ n (g : C(ℂ, ℝ)), HasCompactSupport g → tsupport g ⊆ K n →
      ∀ δ : ℝ, 0 < δ → ∃ m, ∀ x, ‖f (n, m) x - g x‖ < δ)
    (hfamily : ∀ n m, ∫ x, f (n, m) x ∂μ = ∫ x, f (n, m) x ∂ν) :
    μ = ν := by
  have : LocallyCompactSpace (↥U) := hU.locallyCompactSpace
  have : SigmaCompactSpace (↥U) := inferInstance
  have : BorelSpace (↥U) := inferInstance
  let μU : Measure (↥U) := μ.comap Subtype.val
  let νU : Measure (↥U) := ν.comap Subtype.val
  let e := MeasurableEmbedding.subtype_coe hU.measurableSet
  have hμUfinite : IsFiniteMeasureOnCompacts μU := by
    constructor
    intro S hS
    rw [e.comap_apply]
    apply hμfin (Subtype.val '' S) (hS.image continuous_subtype_val)
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have hνUfinite : IsFiniteMeasureOnCompacts νU := by
    constructor
    intro S hS
    rw [e.comap_apply]
    apply hνfin (Subtype.val '' S) (hS.image continuous_subtype_val)
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have : IsFiniteMeasureOnCompacts μU := hμUfinite
  have : IsFiniteMeasureOnCompacts νU := hνUfinite
  have hμUreg : μU.Regular := inferInstance
  have hνUreg : νU.Regular := inferInstance
  have : μU.Regular := hμUreg
  have : νU.Regular := hνUreg
  have hUintegrals : ∀ g : C_c(↥U, ℝ), ∫ x, g x ∂μU = ∫ x, g x ∂νU := by
    intro g
    let gext : ℂ → ℝ := Subtype.val.extend (fun x : ↥U => g x) 0
    have hgextval (x : ↥U) : gext x = g x := by
      simp [gext]
    have hgextCont : Continuous gext :=
      HasCompactSupport.continuous_extend_zero hU g.continuous g.hasCompactSupport'
    have hgextCompact : HasCompactSupport gext :=
      g.hasCompactSupport'.extend_zero continuous_subtype_val
    have hgextSupport : tsupport gext ⊆ U := by
      exact (g.hasCompactSupport'.tsupport_extend_zero_subset continuous_subtype_val).trans
        (by simp)
    let gC : C(ℂ, ℝ) := ⟨gext, hgextCont⟩
    obtain ⟨n, hgnK⟩ := hKcofinal (tsupport gext) hgextCompact.isCompact hgextSupport
    let W : Set (↥U) := Subtype.val ⁻¹' K n
    have hWcompact : IsCompact W := by
      have : CompactSpace (↥(K n)) := isCompact_iff_compactSpace.mp (hKcompact n)
      let j : ↥(K n) → ↥U := fun x => ⟨x.1, hKU n x.2⟩
      have hj : Continuous j := by fun_prop
      have hrange : Set.range j = W := by
        ext x
        constructor
        · rintro ⟨y, rfl⟩
          exact y.2
        · intro hx
          refine ⟨⟨x.1, hx⟩, ?_⟩
          exact Subtype.ext rfl
      rw [← hrange]
      exact isCompact_range hj
    have hWμ : μU W < ∞ := by
      rw [e.comap_apply]
      have himage : Subtype.val '' W = K n := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨⟨x, hKU n hx⟩, hx, rfl⟩
      rw [himage]
      exact hμfin (K n) (hKcompact n) (hKU n)
    have hWν : νU W < ∞ := by
      rw [e.comap_apply]
      have himage : Subtype.val '' W = K n := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨⟨x, hKU n hx⟩, hx, rfl⟩
      rw [himage]
      exact hνfin (K n) (hKcompact n) (hKU n)
    have hWmeas : MeasurableSet W := by
      change MeasurableSet (Subtype.val ⁻¹' K n)
      exact (hKcompact n).isClosed.measurableSet.preimage continuous_subtype_val.measurable
    let gCc : C_c(ℂ, ℝ) := ⟨gC, hgextCompact⟩
    let qg : BoundedContinuousFunction ℂ ℝ := gCc.toBoundedContinuousFunction
    have hqgSupport : tsupport (qg : ℂ → ℝ) ⊆ U := by
      change tsupport gext ⊆ U
      exact hgextSupport
    have hqgK : tsupport (qg : ℂ → ℝ) ⊆ K n := by
      change tsupport gext ⊆ K n
      exact hgnK
    have hqgOnU (x : ↥U) : qg x = g x := by
      change gC x.1 = g x
      simpa [gC] using hgextval x
    have hlift (lam : Measure ℂ) (lamU : Measure (↥U))
        (hlam : lamU = lam.comap Subtype.val) (q : BoundedContinuousFunction ℂ ℝ)
        (hq : tsupport (q : ℂ → ℝ) ⊆ U) :
        ∫ x : ↥U, q x ∂lamU = ∫ x, q x ∂lam := by
      rw [hlam, integral_subtype_comap hU.measurableSet]
      exact integral_restrict_eq_integral_of_zero_on_compl lam U hU.measurableSet q
        (boundedContinuousFunction_eq_zero_off_tsupport_subset q U hq)
    have hqgμ : ∫ x : ↥U, qg x ∂μU = ∫ x, qg x ∂μ :=
      hlift μ μU rfl qg hqgSupport
    have hqgν : ∫ x : ↥U, qg x ∂νU = ∫ x, qg x ∂ν :=
      hlift ν νU rfl qg hqgSupport
    have hgμ : ∫ x : ↥U, g x ∂μU = ∫ x, qg x ∂μU := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => (hqgOnU x).symm
    have hgν : ∫ x : ↥U, g x ∂νU = ∫ x, qg x ∂νU := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => (hqgOnU x).symm
    have hfamilyU (m : ℕ) :
        ∫ x : ↥U, f (n, m) x ∂μU = ∫ x : ↥U, f (n, m) x ∂νU := by
      have hμ := hlift μ μU rfl (f (n, m)) ((hfK n m).2.trans (hKU n))
      have hν := hlift ν νU rfl (f (n, m)) ((hfK n m).2.trans (hKU n))
      calc
        ∫ x : ↥U, f (n, m) x ∂μU = ∫ x, f (n, m) x ∂μ := hμ
        _ = ∫ x, f (n, m) x ∂ν := hfamily n m
        _ = ∫ x : ↥U, f (n, m) x ∂νU := hν.symm
    have hgμInt : Integrable g μU := g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport'
    have hgνInt : Integrable g νU := g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport'
    have hclose (lamU : Measure (↥U)) (hlamfin : IsFiniteMeasureOnCompacts lamU)
        (hlamW : lamU W < ∞) (q : BoundedContinuousFunction ℂ ℝ)
        (hqK : tsupport (q : ℂ → ℝ) ⊆ K n) (δ : ℝ) (hδ : 0 < δ)
        (happrox : ∀ x, ‖q x - gC x‖ < δ) :
        ‖∫ x : ↥U, g x ∂lamU - ∫ x : ↥U, q x ∂lamU‖ ≤ δ * lamU.real W := by
      have : IsFiniteMeasureOnCompacts lamU := hlamfin
      have hgint : Integrable g lamU :=
        g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport'
      have hqUzero : ∀ x, x ∉ W → q x = 0 := by
        intro x hx
        have hxK : (x : ℂ) ∉ K n := hx
        exact image_eq_zero_of_notMem_tsupport (fun hs => hxK (hqK hs))
      have hqsupp : HasCompactSupport (fun x : ↥U => q x) :=
        HasCompactSupport.of_support_subset_isCompact hWcompact
          (Function.support_subset_iff'.mpr fun x hx => hqUzero x hx)
      have hqint : Integrable (fun x : ↥U => q x) lamU :=
        (q.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport hqsupp
      let d : ↥U → ℝ := fun x => g x - q x
      have hdcont : Continuous d := by fun_prop
      have hdzero : ∀ x, x ∉ W → d x = 0 := by
        intro x hxW
        have hxK : (x : ℂ) ∉ K n := hxW
        have hgzero : g x = 0 := by
          rw [← hgextval x]
          exact image_eq_zero_of_notMem_tsupport (fun hs => hxK (hgnK hs))
        have hqzero : q x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun hs => hxK (hqK hs))
        simp [d, hgzero, hqzero]
      have hdsupp : HasCompactSupport d :=
        HasCompactSupport.of_support_subset_isCompact hWcompact
          (Function.support_subset_iff'.mpr hdzero)
      have hdint : Integrable d lamU := hdcont.integrable_of_hasCompactSupport hdsupp
      have hdnorm : Integrable (fun x => ‖d x‖) lamU := hdint.norm
      have hconstOn : IntegrableOn (fun _ : ↥U => δ) W lamU :=
        integrableOn_const hlamW.ne
      have hindicator : Integrable (W.indicator (fun _ : ↥U => δ)) lamU :=
        hconstOn.integrable_indicator hWcompact.measurableSet
      have hbound : ∀ x, ‖d x‖ ≤ W.indicator (fun _ : ↥U => δ) x := by
        intro x
        by_cases hx : x ∈ W
        · simp [Set.indicator, hx, d]
          have h := happrox x.1
          have hcg : gC x.1 = g x := by simpa [gC] using hgextval x
          rw [hcg] at h
          rw [abs_sub_comm]
          exact h.le
        · have hzero := hdzero x hx
          simp [Set.indicator, hx, hzero]
      have hmono := integral_mono hdnorm hindicator hbound
      calc
        ‖∫ x : ↥U, g x ∂lamU - ∫ x : ↥U, q x ∂lamU‖ = ‖∫ x : ↥U, d x ∂lamU‖ := by
          rw [integral_sub hgint hqint]
        _ ≤ ∫ x : ↥U, ‖d x‖ ∂lamU := norm_integral_le_integral_norm _
        _ ≤ ∫ x : ↥U, W.indicator (fun _ : ↥U => δ) x ∂lamU := hmono
        _ = δ * lamU.real W := by
          rw [integral_indicator_const δ hWmeas]
          simp [smul_eq_mul, mul_comm]
    have hpoint (lamU : Measure (↥U)) (hlamfin : IsFiniteMeasureOnCompacts lamU)
        (hlamW : lamU W < ∞) (δ : ℝ) (hδ : 0 < δ) :
        ∀ m, (∀ x, ‖f (n, m) x - gC x‖ < δ) →
          ‖∫ x : ↥U, g x ∂lamU - ∫ x : ↥U, f (n, m) x ∂lamU‖ ≤ δ * lamU.real W := by
      intro m happrox
      exact hclose lamU hlamfin hlamW (f (n, m)) (hfK n m).2 δ hδ happrox
    let Mμ : ℝ := μU.real W
    let Mν : ℝ := νU.real W
    have hMμ : 0 ≤ Mμ := by simp [Mμ]
    have hMν : 0 ≤ Mν := by simp [Mν]
    by_contra hne
    have hD : 0 < ‖(∫ x : ↥U, g x ∂μU) - ∫ x : ↥U, g x ∂νU‖ := by
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    let δ : ℝ := ‖(∫ x : ↥U, g x ∂μU) - ∫ x : ↥U, g x ∂νU‖ /
      (2 * (Mμ + Mν + 1))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨m, happrox⟩ := hdense n gC hgextCompact hgnK δ hδ
    have hμclose :
        ‖∫ x : ↥U, g x ∂μU - ∫ x : ↥U, f (n, m) x ∂μU‖ ≤ δ * Mμ := by
      simpa [Mμ] using hpoint μU hμUfinite hWμ δ hδ m happrox
    have hνclose :
        ‖∫ x : ↥U, g x ∂νU - ∫ x : ↥U, f (n, m) x ∂νU‖ ≤ δ * Mν := by
      simpa [Mν] using hpoint νU hνUfinite hWν δ hδ m happrox
    have hdecomp :
        (∫ x : ↥U, g x ∂μU) - ∫ x : ↥U, g x ∂νU =
          ((∫ x : ↥U, g x ∂μU) - ∫ x : ↥U, f (n, m) x ∂μU) +
            ((∫ x : ↥U, f (n, m) x ∂νU) - ∫ x : ↥U, g x ∂νU) := by
      rw [hfamilyU m]
      ring
    have hDle :
        ‖(∫ x : ↥U, g x ∂μU) - ∫ x : ↥U, g x ∂νU‖ ≤ δ * Mμ + δ * Mν := by
      rw [hdecomp]
      calc
        ‖_ + _‖ ≤
            ‖(∫ x : ↥U, g x ∂μU) - ∫ x : ↥U, f (n, m) x ∂μU‖ +
              ‖(∫ x : ↥U, f (n, m) x ∂νU) - ∫ x : ↥U, g x ∂νU‖ := norm_add_le _ _
        _ ≤ δ * Mμ + δ * Mν := by
          apply add_le_add hμclose
          simpa [norm_sub_rev] using hνclose
    have hfactor : (Mμ + Mν) / (2 * (Mμ + Mν + 1)) < 1 := by
      apply (div_lt_one (by positivity : 0 < 2 * (Mμ + Mν + 1))).2
      nlinarith
    have hsmall : δ * Mμ + δ * Mν <
        ‖(∫ x : ↥U, g x ∂μU) - ∫ x : ↥U, g x ∂νU‖ := by
      calc
        δ * Mμ + δ * Mν =
            ‖(∫ x : ↥U, g x ∂μU) - ∫ x : ↥U, g x ∂νU‖ *
              ((Mμ + Mν) / (2 * (Mμ + Mν + 1))) := by
          dsimp [δ]
          ring
        _ <
          ‖(∫ x : ↥U, g x ∂μU) - ∫ x : ↥U, g x ∂νU‖ * 1 :=
          mul_lt_mul_of_pos_left hfactor hD
        _ = ‖(∫ x : ↥U, g x ∂μU) - ∫ x : ↥U, g x ∂νU‖ := by ring
    exact (not_lt_of_ge hDle) hsmall
  have hμae : ∀ᵐ x ∂μ, x ∈ U := by
    rw [ae_iff]
    exact hμsupp
  have hνae : ∀ᵐ x ∂ν, x ∈ U := by
    rw [ae_iff]
    exact hνsupp
  have hμrestrict : μ.restrict U = μ := Measure.restrict_eq_self_of_ae_mem hμae
  have hνrestrict : ν.restrict U = ν := Measure.restrict_eq_self_of_ae_mem hνae
  have hrange : Set.range (Subtype.val : ↥U → ℂ) = U := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hmapμ : μU.map Subtype.val = μ.restrict U := by
    change (μ.comap Subtype.val).map Subtype.val = μ.restrict U
    rw [e.map_comap μ, hrange]
  have hmapν : νU.map Subtype.val = ν.restrict U := by
    change (ν.comap Subtype.val).map Subtype.val = ν.restrict U
    rw [e.map_comap ν, hrange]
  calc
    μ = μ.restrict U := hμrestrict.symm
    _ = μU.map Subtype.val := hmapμ.symm
    _ = νU.map Subtype.val := congrArg (fun lam : Measure (↥U) => lam.map Subtype.val) <|
      Measure.ext_of_integral_eq_on_compactlySupported hUintegrals
    _ = ν.restrict U := hmapν
    _ = ν := hνrestrict


end DOZZ.Proofs
