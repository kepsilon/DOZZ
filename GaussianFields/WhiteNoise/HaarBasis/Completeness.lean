/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.WhiteNoise.HaarBasis.DyadicAlgebra

/-!
# GaussianFields Haar basis completeness

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace Topology symmDiff
open Filter

namespace GaussianFields

/-- The finite scale-zero cell window with radius `n`. -/
@[expose]
def dyadicCellWindow (d n : Nat) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ : Fin d => Finset.Icc (-(n : ℤ)) (n : ℤ)

@[simp]
theorem mem_dyadicCellWindow {d n : Nat} {cell : Fin d → ℤ} :
    cell ∈ dyadicCellWindow d n ↔
      ∀ r : Fin d, -(n : ℤ) ≤ cell r ∧ cell r ≤ (n : ℤ) := by
  simp [dyadicCellWindow, Fintype.mem_piFinset]

theorem dyadicCellWindow_mono {d m n : Nat} (hmn : m ≤ n) :
    dyadicCellWindow d m ⊆ dyadicCellWindow d n := by
  intro cell hcell
  rw [mem_dyadicCellWindow] at hcell ⊢
  intro r
  have hmn_int : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
  exact ⟨le_trans (neg_le_neg hmn_int) (hcell r).1, le_trans (hcell r).2 hmn_int⟩

/-- The finite union of scale-zero dyadic boxes in a coordinate radius `n`. -/
@[expose]
def dyadicBoxWindow (d n : Nat) : Set (Vec d) :=
  ⋃ cell ∈ dyadicCellWindow d n, dyadicBox 0 cell

theorem dyadicBoxWindow_eq_finsetUnion (d n : Nat) :
    dyadicBoxWindow d n = dyadicBoxFinsetUnion (d := d) 0 (dyadicCellWindow d n) := by
  rfl

/-- The cells of a fixed scale `N` whose dyadic boxes make up the scale-zero window. -/
@[expose]
def dyadicWindowCellFinsetAtScale (d m N : Nat) : Finset (Fin d → ℤ) :=
  (dyadicCellWindow d m).biUnion (dyadicDescendantCellFinset N)

theorem dyadicBoxWindow_eq_finsetUnion_atScale (d m N : Nat) :
    dyadicBoxWindow d m =
      dyadicBoxFinsetUnion (d := d) (N : ℤ) (dyadicWindowCellFinsetAtScale d m N) := by
  rw [dyadicBoxWindow_eq_finsetUnion]
  simpa [dyadicWindowCellFinsetAtScale] using
    dyadicBoxFinsetUnion_refine_nat (d := d) (n := 0) (N := N) (Nat.zero_le N)
      (dyadicCellWindow d m)

theorem dyadicBox_inter_dyadicBoxWindow_eq_finsetUnion {d : Nat}
    (j m : Nat) (cell : Fin d → ℤ) :
    dyadicBox (j : ℤ) cell ∩ dyadicBoxWindow d m =
      dyadicBoxFinsetUnion (d := d) (j : ℤ)
        ({cell} ∩ dyadicWindowCellFinsetAtScale d m j) := by
  rw [dyadicBoxFinsetUnion_inter]
  rw [dyadicBoxFinsetUnion_singleton, dyadicBoxWindow_eq_finsetUnion_atScale]

/-- Every dyadic-algebra set becomes a finite union of same-scale dyadic boxes after restriction to
a finite dyadic window. -/
theorem nonnegativeDyadicBoxAlgebra_inter_window_eq_finsetUnion {d : Nat}
    {s : Set (Vec d)} (hs : s ∈ nonnegativeDyadicBoxAlgebra d) (m : Nat) :
    ∃ n : Nat, ∃ cells : Finset (Fin d → ℤ),
      s ∩ dyadicBoxWindow d m =
        dyadicBoxFinsetUnion (d := d) (n : ℤ) cells := by
  classical
  unfold nonnegativeDyadicBoxAlgebra at hs
  induction hs using generateSetAlgebra_induction with
  | base t ht =>
      rcases ht with ⟨p, rfl⟩
      refine ⟨p.1, {p.2} ∩ dyadicWindowCellFinsetAtScale d m p.1, ?_⟩
      exact dyadicBox_inter_dyadicBoxWindow_eq_finsetUnion p.1 m p.2
  | empty =>
      refine ⟨0, ∅, ?_⟩
      simp [dyadicBoxFinsetUnion_empty]
  | compl t _ ih =>
      rcases ih with ⟨n, cells, hcells⟩
      refine ⟨n, dyadicWindowCellFinsetAtScale d m n \ cells, ?_⟩
      calc
        tᶜ ∩ dyadicBoxWindow d m =
            dyadicBoxWindow d m \ (t ∩ dyadicBoxWindow d m) := by
              ext x
              by_cases hxt : x ∈ t <;> by_cases hxW : x ∈ dyadicBoxWindow d m <;>
                simp [hxt, hxW]
        _ = dyadicBoxFinsetUnion (d := d) (n : ℤ) (dyadicWindowCellFinsetAtScale d m n) \
            dyadicBoxFinsetUnion (d := d) (n : ℤ) cells := by
              rw [hcells, dyadicBoxWindow_eq_finsetUnion_atScale]
        _ = dyadicBoxFinsetUnion (d := d) (n : ℤ)
            (dyadicWindowCellFinsetAtScale d m n \ cells) := by
              rw [dyadicBoxFinsetUnion_diff]
  | union t u _ _ iht ihu =>
      rcases iht with ⟨nt, cellsT, hcellsT⟩
      rcases ihu with ⟨nu, cellsU, hcellsU⟩
      let N : Nat := max nt nu
      let cellsT' : Finset (Fin d → ℤ) :=
        cellsT.biUnion (dyadicDescendantCellFinset (N - nt))
      let cellsU' : Finset (Fin d → ℤ) :=
        cellsU.biUnion (dyadicDescendantCellFinset (N - nu))
      refine ⟨N, cellsT' ∪ cellsU', ?_⟩
      have hTref :
          dyadicBoxFinsetUnion (d := d) (nt : ℤ) cellsT =
            dyadicBoxFinsetUnion (d := d) (N : ℤ) cellsT' := by
        exact dyadicBoxFinsetUnion_refine_nat (d := d) (n := nt) (N := N)
          (Nat.le_max_left nt nu) cellsT
      have hUref :
          dyadicBoxFinsetUnion (d := d) (nu : ℤ) cellsU =
            dyadicBoxFinsetUnion (d := d) (N : ℤ) cellsU' := by
        exact dyadicBoxFinsetUnion_refine_nat (d := d) (n := nu) (N := N)
          (Nat.le_max_right nt nu) cellsU
      calc
        (t ∪ u) ∩ dyadicBoxWindow d m =
            (t ∩ dyadicBoxWindow d m) ∪ (u ∩ dyadicBoxWindow d m) := by
              ext x
              constructor
              · intro hx
                rcases hx.1 with hxt | hxu
                · exact Or.inl ⟨hxt, hx.2⟩
                · exact Or.inr ⟨hxu, hx.2⟩
              · intro hx
                rcases hx with hx | hx
                · exact ⟨Or.inl hx.1, hx.2⟩
                · exact ⟨Or.inr hx.1, hx.2⟩
        _ = dyadicBoxFinsetUnion (d := d) (nt : ℤ) cellsT ∪
            dyadicBoxFinsetUnion (d := d) (nu : ℤ) cellsU := by
              rw [hcellsT, hcellsU]
        _ = dyadicBoxFinsetUnion (d := d) (N : ℤ) cellsT' ∪
            dyadicBoxFinsetUnion (d := d) (N : ℤ) cellsU' := by
              rw [hTref, hUref]
        _ = dyadicBoxFinsetUnion (d := d) (N : ℤ) (cellsT' ∪ cellsU') := by
              rw [dyadicBoxFinsetUnion_union]

theorem nonnegativeDyadicBoxAlgebra_inter_window_mem_finsetUnionFamily {d : Nat}
    {s : Set (Vec d)} (hs : s ∈ nonnegativeDyadicBoxAlgebra d) (m : Nat) :
    s ∩ dyadicBoxWindow d m ∈ nonnegativeDyadicBoxFinsetUnionFamily d := by
  rcases nonnegativeDyadicBoxAlgebra_inter_window_eq_finsetUnion (d := d) hs m with
    ⟨n, cells, hcells⟩
  exact ⟨(n, cells), hcells.symm⟩

theorem measurableSet_dyadicBoxWindow (d n : Nat) :
    MeasurableSet (dyadicBoxWindow d n) := by
  simpa [dyadicBoxWindow_eq_finsetUnion] using
    measurableSet_dyadicBoxFinsetUnion (d := d) 0 (dyadicCellWindow d n)

theorem dyadicBoxWindow_mono {d m n : Nat} (hmn : m ≤ n) :
    dyadicBoxWindow d m ⊆ dyadicBoxWindow d n := by
  intro x hx
  unfold dyadicBoxWindow at hx ⊢
  rcases Set.mem_iUnion.1 hx with ⟨cell, hcell⟩
  rcases Set.mem_iUnion.1 hcell with ⟨hmem, hxcell⟩
  exact Set.mem_iUnion.2 ⟨cell, Set.mem_iUnion.2 ⟨dyadicCellWindow_mono hmn hmem, hxcell⟩⟩

theorem dyadicBoxWindow_mem_nonnegativeDyadicBoxAlgebra (d n : Nat) :
    dyadicBoxWindow d n ∈ nonnegativeDyadicBoxAlgebra d := by
  unfold dyadicBoxWindow
  exact (isSetAlgebra_nonnegativeDyadicBoxAlgebra d).biUnion_mem
    (dyadicCellWindow d n) fun cell _hcell =>
      nonnegativeDyadicBoxFamily_subset_algebra d ⟨(0, cell), rfl⟩

theorem volume_dyadicBoxWindow_lt_top (d n : Nat) :
    (volume : Measure (Vec d)) (dyadicBoxWindow d n) < ∞ := by
  unfold dyadicBoxWindow
  exact measure_biUnion_lt_top (μ := (volume : Measure (Vec d)))
    (s := (dyadicCellWindow d n : Set (Fin d → ℤ)))
    (Finset.finite_toSet _) fun cell _hcell =>
      lt_top_iff_ne_top.2 (volume_dyadicBox_ne_top 0 cell)

theorem volume_dyadicBoxWindow_ne_top (d n : Nat) :
    (volume : Measure (Vec d)) (dyadicBoxWindow d n) ≠ ∞ :=
  (volume_dyadicBoxWindow_lt_top d n).ne

theorem indicatorConstLp_dyadicBoxWindow_mem_haarBasisSubmodule (d n : Nat) :
    indicatorConstLp 2 (measurableSet_dyadicBoxWindow d n)
      (volume_dyadicBoxWindow_ne_top d n) (1 : ℝ) ∈ haarBasisSubmodule d := by
  simpa [dyadicBoxWindow_eq_finsetUnion] using
    indicatorConstLp_dyadicBoxFinsetUnion_mem_haarBasisSubmodule_of_nonnegative
      (d := d) (j := 0) (by norm_num) (dyadicCellWindow d n)

theorem iUnion_dyadicBoxWindow_eq_univ (d : Nat) :
    (⋃ n : ℕ, dyadicBoxWindow d n) = Set.univ := by
  refine Set.eq_univ_iff_forall.2 ?_
  intro x
  let cell : Fin d → ℤ := fun r => ⌊x r⌋
  let n : ℕ := ∑ r : Fin d, Int.natAbs (cell r)
  refine Set.mem_iUnion.2 ⟨n, ?_⟩
  unfold dyadicBoxWindow
  refine Set.mem_iUnion.2 ⟨cell, ?_⟩
  refine Set.mem_iUnion.2 ⟨?_, ?_⟩
  · rw [mem_dyadicCellWindow]
    intro r
    have hnat : Int.natAbs (cell r) ≤ n := by
      exact Finset.single_le_sum (fun i _hi => Nat.zero_le (Int.natAbs (cell i)))
        (Finset.mem_univ r)
    have habs : |cell r| ≤ (n : ℤ) := by
      have hcast : ((Int.natAbs (cell r) : ℕ) : ℤ) ≤ (n : ℤ) := by
        exact_mod_cast hnat
      simpa [Int.natCast_natAbs] using hcast
    exact abs_le.1 habs
  · intro r _hr
    simpa [cell, dyadicPower] using mem_dyadicInterval_floor 0 (x r)

theorem iInter_diff_dyadicBoxWindow_eq_empty {d : Nat} (s : Set (Vec d)) :
    (⋂ n : ℕ, s \ dyadicBoxWindow d n) = ∅ := by
  ext x
  constructor
  · intro hx
    have hxuniv : x ∈ (⋃ n : ℕ, dyadicBoxWindow d n) := by
      rw [iUnion_dyadicBoxWindow_eq_univ d]
      trivial
    rcases Set.mem_iUnion.1 hxuniv with ⟨n, hxn⟩
    exact ((Set.mem_iInter.1 hx) n).2 hxn
  · intro hx
    cases hx

/-- The measure of the part of a finite-measure set outside the dyadic windows tends to zero. -/
theorem tendsto_measure_diff_dyadicBoxWindow {d : Nat}
    {s : Set (Vec d)} (hs : MeasurableSet s)
    (hμs : (volume : Measure (Vec d)) s ≠ ∞) :
    Tendsto
      (fun n : ℕ => (volume : Measure (Vec d)) (s \ dyadicBoxWindow d n))
      atTop (𝓝 0) := by
  let μ : Measure (Vec d) := volume
  let tail : ℕ → Set (Vec d) := fun n => s \ dyadicBoxWindow d n
  have htail_null : ∀ n, NullMeasurableSet (tail n) μ := by
    intro n
    exact (hs.diff (measurableSet_dyadicBoxWindow d n)).nullMeasurableSet
  have htail_anti : Antitone tail := by
    intro m n hmn x hx
    exact ⟨hx.1, fun hxWm => hx.2 (dyadicBoxWindow_mono hmn hxWm)⟩
  have htail_finite : ∃ n, μ (tail n) ≠ ∞ := by
    refine ⟨0, ne_top_of_le_ne_top hμs ?_⟩
    exact measure_mono (Set.sdiff_subset)
  have htail_inter : (⋂ n : ℕ, tail n) = ∅ := by
    simpa [tail] using iInter_diff_dyadicBoxWindow_eq_empty (d := d) s
  have h :=
    tendsto_measure_iInter_atTop (μ := μ) htail_null htail_anti htail_finite
  simpa [Function.comp_def, htail_inter, tail, μ] using h

/-- Truncating a finite-measure set by dyadic windows converges to the original indicator in
`L²`. -/
theorem tendsto_indicatorConstLp_inter_dyadicBoxWindow {d : Nat}
    {s : Set (Vec d)} (hs : MeasurableSet s)
    (hμs : (volume : Measure (Vec d)) s ≠ ∞) :
    Tendsto
      (fun n : ℕ =>
        indicatorConstLp 2 (hs.inter (measurableSet_dyadicBoxWindow d n))
          (ne_top_of_le_ne_top hμs (measure_mono (Set.inter_subset_left)))
          (1 : ℝ))
      atTop
      (𝓝 (indicatorConstLp 2 hs hμs (1 : ℝ))) := by
  let μ : Measure (Vec d) := volume
  let tail : ℕ → Set (Vec d) := fun n => s \ dyadicBoxWindow d n
  have htail_null : ∀ n, NullMeasurableSet (tail n) μ := by
    intro n
    exact (hs.diff (measurableSet_dyadicBoxWindow d n)).nullMeasurableSet
  have htail_anti : Antitone tail := by
    intro m n hmn x hx
    exact ⟨hx.1, fun hxWm => hx.2 (dyadicBoxWindow_mono hmn hxWm)⟩
  have htail_finite : ∃ n, μ (tail n) ≠ ∞ := by
    refine ⟨0, ne_top_of_le_ne_top hμs ?_⟩
    exact measure_mono (Set.sdiff_subset)
  have htail_inter : (⋂ n : ℕ, tail n) = ∅ := by
    simpa [tail] using iInter_diff_dyadicBoxWindow_eq_empty (d := d) s
  have htail_tendsto : Tendsto (fun n : ℕ => μ (tail n)) atTop (𝓝 0) := by
    have h :=
      tendsto_measure_iInter_atTop (μ := μ) htail_null htail_anti htail_finite
    simpa [Function.comp_def, htail_inter] using h
  have hsymm : ∀ n : ℕ, (s ∩ dyadicBoxWindow d n) ∆ s = tail n := by
    intro n
    ext x
    by_cases hxs : x ∈ s <;> by_cases hxW : x ∈ dyadicBoxWindow d n <;>
      simp [tail, Set.symmDiff_def, hxs, hxW]
  have hsymm_tendsto :
      Tendsto (fun n : ℕ => μ ((s ∩ dyadicBoxWindow d n) ∆ s)) atTop (𝓝 0) := by
    simpa [hsymm] using htail_tendsto
  exact tendsto_indicatorConstLp_set
    (p := (2 : ℝ≥0∞)) (μ := μ) (s := s) (hs := hs) (hμs := hμs)
    (t := fun n : ℕ => s ∩ dyadicBoxWindow d n)
    (ht := fun n => hs.inter (measurableSet_dyadicBoxWindow d n))
    (hμt := fun n => ne_top_of_le_ne_top hμs (measure_mono (Set.inter_subset_left)))
    (c := (1 : ℝ)) (by norm_num) hsymm_tendsto

/-- The dyadic scale-zero windows give finite spanning sets belonging to the dyadic algebra. -/
@[expose]
def finiteSpanningSetsIn_nonnegativeDyadicBoxAlgebra (d : Nat) :
    (volume : Measure (Vec d)).FiniteSpanningSetsIn (nonnegativeDyadicBoxAlgebra d) where
  set := dyadicBoxWindow d
  set_mem := dyadicBoxWindow_mem_nonnegativeDyadicBoxAlgebra d
  finite := volume_dyadicBoxWindow_lt_top d
  spanning := iUnion_dyadicBoxWindow_eq_univ d

/-- The dyadic algebra is measure-dense for Lebesgue measure on `R^d`. -/
theorem measureDense_nonnegativeDyadicBoxAlgebra (d : Nat) :
    (volume : Measure (Vec d)).MeasureDense (nonnegativeDyadicBoxAlgebra d) :=
  Measure.MeasureDense.of_generateFrom_isSetAlgebra_sigmaFinite
    (μ := (volume : Measure (Vec d)))
    (𝒜 := nonnegativeDyadicBoxAlgebra d)
    (isSetAlgebra_nonnegativeDyadicBoxAlgebra d)
    (finiteSpanningSetsIn_nonnegativeDyadicBoxAlgebra d)
    (measurableSpace_eq_generateFrom_nonnegativeDyadicBoxAlgebra d)

/-- Finite unions of same-scale nonnegative dyadic boxes are measure-dense.  This is the concrete
AKM/Haar approximation statement: start with a dyadic-algebra approximant, truncate it to a large
dyadic window, and refine that finite Boolean expression to one common dyadic scale. -/
theorem measureDense_nonnegativeDyadicBoxFinsetUnionFamily (d : Nat) :
    (volume : Measure (Vec d)).MeasureDense
      (nonnegativeDyadicBoxFinsetUnionFamily d) where
  measurable s hs := measurableSet_of_mem_nonnegativeDyadicBoxFinsetUnionFamily hs
  approx s hs hμs ε hε := by
    classical
    have hε_half : 0 < ε / 2 := by linarith
    rcases (measureDense_nonnegativeDyadicBoxAlgebra d).fin_meas_approx
        hs hμs (ε / 2) hε_half with
      ⟨t, ht_alg, hμt, hst⟩
    have ht_meas : MeasurableSet t :=
      (measureDense_nonnegativeDyadicBoxAlgebra d).measurable t ht_alg
    have htail_tendsto := tendsto_measure_diff_dyadicBoxWindow
      (d := d) ht_meas hμt
    have htarget_pos : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) :=
      ENNReal.ofReal_pos.2 hε_half
    have htail_eventually :
        ∀ᶠ n in atTop,
          (volume : Measure (Vec d)) (t \ dyadicBoxWindow d n) <
            ENNReal.ofReal (ε / 2) :=
      htail_tendsto.eventually (Iio_mem_nhds htarget_pos)
    rcases eventually_atTop.1 htail_eventually with ⟨N, hN⟩
    let u : Set (Vec d) := t ∩ dyadicBoxWindow d N
    have hu_mem : u ∈ nonnegativeDyadicBoxFinsetUnionFamily d :=
      nonnegativeDyadicBoxAlgebra_inter_window_mem_finsetUnionFamily
        (d := d) ht_alg N
    refine ⟨u, hu_mem, ?_⟩
    have htu : t ∆ u = t \ dyadicBoxWindow d N := by
      ext x
      by_cases hxt : x ∈ t <;> by_cases hxW : x ∈ dyadicBoxWindow d N <;>
        simp [u, Set.symmDiff_def, hxt, hxW]
    calc
      (volume : Measure (Vec d)) (s ∆ u) ≤
          (volume : Measure (Vec d)) (s ∆ t) +
            (volume : Measure (Vec d)) (t ∆ u) :=
        measure_symmDiff_le s t u
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
        exact ENNReal.add_lt_add hst (by simpa [htu] using hN N le_rfl)
      _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1
        ring

/-- Any finite-measure indicator can be approximated in `L²` by indicators of finite-measure sets
from the dyadic algebra. -/
theorem indicatorConstLp_mem_closure_nonnegativeDyadicBoxAlgebra_indicators
    {d : Nat} {s : Set (Vec d)} (hs : MeasurableSet s)
    (hμs : (volume : Measure (Vec d)) s ≠ ∞) :
    indicatorConstLp 2 hs hμs (1 : ℝ) ∈
      closure
        {indicatorConstLp 2
          ((measureDense_nonnegativeDyadicBoxAlgebra d).measurable t ht) hμt (1 : ℝ) |
            (t : Set (Vec d)) (ht : t ∈ nonnegativeDyadicBoxAlgebra d)
              (hμt : (volume : Measure (Vec d)) t ≠ ∞)} := by
  exact
    (measureDense_nonnegativeDyadicBoxAlgebra d).indicatorConstLp_subset_closure
      (p := (2 : ℝ≥0∞)) (c := (1 : ℝ)) ⟨s, hs, hμs, rfl⟩

/-- Any finite-measure indicator belongs to the closed span of the explicit inhomogeneous Haar
system. -/
theorem indicatorConstLp_mem_haarBasisSubmodule_topologicalClosure
    {d : Nat} {s : Set (Vec d)} (hs : MeasurableSet s)
    (hμs : (volume : Measure (Vec d)) s ≠ ∞) :
    indicatorConstLp 2 hs hμs (1 : ℝ) ∈
      (haarBasisSubmodule d).topologicalClosure := by
  let 𝒟 : Set (Lp ℝ 2 (volume : Measure (Vec d))) :=
    {indicatorConstLp 2
      ((measureDense_nonnegativeDyadicBoxFinsetUnionFamily d).measurable t ht) hμt (1 : ℝ) |
        (t : Set (Vec d)) (ht : t ∈ nonnegativeDyadicBoxFinsetUnionFamily d)
          (hμt : (volume : Measure (Vec d)) t ≠ ∞)}
  have h_dense :
      indicatorConstLp 2 hs hμs (1 : ℝ) ∈ closure 𝒟 := by
    exact
      (measureDense_nonnegativeDyadicBoxFinsetUnionFamily d).indicatorConstLp_subset_closure
        (p := (2 : ℝ≥0∞)) (c := (1 : ℝ)) ⟨s, hs, hμs, rfl⟩
  have h𝒟_subset :
      𝒟 ⊆ ((haarBasisSubmodule d).topologicalClosure :
        Set (Lp ℝ 2 (volume : Measure (Vec d)))) := by
    intro f hf
    rcases hf with ⟨t, ht, hμt, rfl⟩
    exact (haarBasisSubmodule d).le_topologicalClosure
      (indicatorConstLp_mem_haarBasisSubmodule_of_mem_nonnegativeDyadicBoxFinsetUnionFamily
        ht ((measureDense_nonnegativeDyadicBoxFinsetUnionFamily d).measurable t ht) hμt)
  exact closure_minimal h𝒟_subset
    (haarBasisSubmodule d).isClosed_topologicalClosure h_dense

/-- Multiplying a unit-valued constant indicator in `L²` gives the corresponding constant
indicator. -/
theorem smul_indicatorConstLp_one {d : Nat} {s : Set (Vec d)}
    (hs : MeasurableSet s) (hμs : (volume : Measure (Vec d)) s ≠ ∞) (c : ℝ) :
    c • indicatorConstLp 2 hs hμs (1 : ℝ) =
      indicatorConstLp 2 hs hμs c := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_smul c (indicatorConstLp 2 hs hμs (1 : ℝ)),
    indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := (volume : Measure (Vec d)))
      (hs := hs) (hμs := hμs) (c := (1 : ℝ)),
    indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := (volume : Measure (Vec d)))
      (hs := hs) (hμs := hμs) (c := c)] with x hsmul hone hc
  rw [hsmul]
  change c * (indicatorConstLp 2 hs hμs (1 : ℝ) : Lp ℝ 2 (volume : Measure (Vec d))) x =
    (indicatorConstLp 2 hs hμs c : Lp ℝ 2 (volume : Measure (Vec d))) x
  rw [hone, hc]
  by_cases hx : x ∈ s
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-- If every finite-measure indicator belongs to the closed Haar span, then the Haar span is
dense in `L²(R^d)`.  This is the `Lp.induction` bridge used by the completeness proof. -/
theorem haarBasisSubmodule_topologicalClosure_eq_top_of_indicatorConstLp
    (d : Nat)
    (hindicator :
      ∀ {s : Set (Vec d)} (hs : MeasurableSet s)
        (hμs : (volume : Measure (Vec d)) s ≠ ∞),
          indicatorConstLp 2 hs hμs (1 : ℝ) ∈
            (haarBasisSubmodule d).topologicalClosure) :
    (haarBasisSubmodule d).topologicalClosure = ⊤ := by
  classical
  let M : Submodule ℝ (Lp ℝ 2 (volume : Measure (Vec d))) :=
    (haarBasisSubmodule d).topologicalClosure
  have hclosed : IsClosed {f : Lp ℝ 2 (volume : Measure (Vec d)) | f ∈ M} := by
    change IsClosed (M : Set (Lp ℝ 2 (volume : Measure (Vec d))))
    exact (haarBasisSubmodule d).isClosed_topologicalClosure
  have hall : ∀ f : Lp ℝ 2 (volume : Measure (Vec d)), f ∈ M := by
    refine Lp.induction (E := ℝ) (μ := (volume : Measure (Vec d)))
      (p := (2 : ℝ≥0∞)) (motive := fun f => f ∈ M)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) ?_ ?_ hclosed
    · intro c s hs hμs_lt
      have hμs : (volume : Measure (Vec d)) s ≠ ∞ := ne_of_lt hμs_lt
      rw [Lp.simpleFunc.coe_indicatorConst]
      rw [← smul_indicatorConstLp_one hs hμs c]
      exact M.smul_mem c (hindicator hs hμs)
    · intro f g _hf _hg _hdisjoint hf_mem hg_mem
      exact M.add_mem hf_mem hg_mem
  exact eq_top_iff.2 fun f _hf => hall f

/-- The explicit inhomogeneous Haar system has dense span in `L²(R^d)`. -/
theorem haarBasisSubmodule_topologicalClosure_eq_top (d : Nat) :
    (haarBasisSubmodule d).topologicalClosure = ⊤ :=
  haarBasisSubmodule_topologicalClosure_eq_top_of_indicatorConstLp d
    (fun hs hμs => indicatorConstLp_mem_haarBasisSubmodule_topologicalClosure hs hμs)

/-- The explicit inhomogeneous Haar system as a Hilbert basis of `L²(R^d)`. -/
@[expose]
noncomputable def haarHilbertBasis (d : Nat) :
    HilbertBasis (HaarBasisIndex d) ℝ (Lp ℝ 2 (volume : Measure (Vec d))) :=
  HilbertBasis.mk (orthonormal_haarBasisLp d) (by
    change ⊤ ≤ (haarBasisSubmodule d).topologicalClosure
    rw [haarBasisSubmodule_topologicalClosure_eq_top d])

theorem coe_haarHilbertBasis (d : Nat) :
    ⇑(haarHilbertBasis d) =
      (haarBasisLp : HaarBasisIndex d → Lp ℝ 2 (volume : Measure (Vec d))) :=
  HilbertBasis.coe_mk _ _

end GaussianFields

end
