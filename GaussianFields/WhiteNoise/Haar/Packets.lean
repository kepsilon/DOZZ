/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.WhiteNoise.Haar.OneDimensional

/-!
# GaussianFields multidimensional Haar packets

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace

namespace GaussianFields

/-- The tensor-product Haar packet on `R^d`. -/
@[expose]
noncomputable def haarPacket {d : Nat} (idx : HaarIndex d) : Vec d → ℝ :=
  fun x => ∏ r : Fin d, haar1D idx.scale (idx.cell r) (idx.signature r) (x r)

/-- The child cell selected by a Boolean left/right side vector. -/
@[expose]
def haarChildCell {d : Nat} (cell : Fin d → ℤ) (side : Fin d → Bool) : Fin d → ℤ :=
  fun r => (2 : ℤ) * cell r + if side r then 1 else 0

/-- The coefficient of a parent packet in the tensor expansion of a father child. -/
@[expose]
noncomputable def haarChildCoefficient {d : Nat}
    (side signature : Fin d → Bool) : ℝ :=
  ∏ r : Fin d,
    (Real.sqrt 2)⁻¹ * (if side r && signature r then (-1 : ℝ) else 1)

theorem haarPacket_child_father_refine_pointwise {d : Nat} (j : ℤ)
    (cell : Fin d → ℤ) (side : Fin d → Bool) (x : Vec d) :
    haarPacket
        { scale := j + 1
          cell := haarChildCell cell side
          signature := fun _ => false } x =
      ∑ signature : Fin d → Bool,
        haarChildCoefficient side signature *
          haarPacket { scale := j, cell := cell, signature := signature } x := by
  unfold haarPacket haarChildCell haarChildCoefficient
  simp_rw [haar1D_child_father_refine_bool]
  rw [Finset.prod_univ_sum]
  congr
  ext signature
  rw [← Finset.prod_mul_distrib]

/-- The dyadic box in `R^d` associated with scale `j` and integer cell `cell`. -/
@[expose]
def dyadicBox {d : Nat} (j : ℤ) (cell : Fin d → ℤ) : Set (Vec d) :=
  Set.pi Set.univ fun r => dyadicInterval j (cell r)

theorem measurableSet_dyadicBox {d : Nat} (j : ℤ) (cell : Fin d → ℤ) :
    MeasurableSet (dyadicBox j cell) := by
  unfold dyadicBox
  exact MeasurableSet.pi Set.countable_univ fun r _ => measurableSet_dyadicInterval j (cell r)

theorem volume_dyadicBox_ne_top {d : Nat} (j : ℤ) (cell : Fin d → ℤ) :
    volume (dyadicBox j cell) ≠ ∞ := by
  unfold dyadicBox dyadicInterval
  rw [Real.volume_pi_Ico]
  exact ENNReal.prod_ne_top fun r _ => ENNReal.ofReal_ne_top

theorem haarPacket_father_eq_indicator_dyadicBox {d : Nat}
    (j : ℤ) (cell : Fin d → ℤ) (x : Vec d) :
    haarPacket { scale := j, cell := cell, signature := fun _ => false } x =
      (∏ _r : Fin d, haarScaleFactor j) *
        Set.indicator (dyadicBox j cell) (fun _ : Vec d => (1 : ℝ)) x := by
  unfold haarPacket
  calc
    ∏ r : Fin d, haar1D j (cell r) false (x r) =
        ∏ r : Fin d,
          haarScaleFactor j *
            Set.indicator (dyadicInterval j (cell r)) (fun _ : ℝ => (1 : ℝ)) (x r) := by
          refine Finset.prod_congr rfl ?_
          intro r _hr
          exact haar1D_father_eq_indicator_dyadicInterval j (cell r) (x r)
    _ = (∏ _r : Fin d, haarScaleFactor j) *
        ∏ r : Fin d,
          Set.indicator (dyadicInterval j (cell r)) (fun _ : ℝ => (1 : ℝ)) (x r) := by
          rw [← Finset.prod_mul_distrib]
    _ = (∏ _r : Fin d, haarScaleFactor j) *
        Set.indicator (dyadicBox j cell) (fun _ : Vec d => (1 : ℝ)) x := by
          congr 1
          have h := Set.indicator_pi_one_apply
            (M₀ := ℝ) (s := (Finset.univ : Finset (Fin d)))
            (t := fun r => dyadicInterval j (cell r)) (f := x)
          have honeReal : (fun _ : ℝ => (1 : ℝ)) = (1 : ℝ → ℝ) := by
            funext y
            rfl
          have honeVec : (fun _ : Vec d => (1 : ℝ)) = (1 : Vec d → ℝ) := by
            funext y
            rfl
          rw [honeReal, honeVec, dyadicBox]
          simpa only [Finset.coe_univ] using h.symm

@[fun_prop]
theorem measurable_haarPacket {d : Nat} (idx : HaarIndex d) :
    Measurable (haarPacket idx) := by
  unfold haarPacket
  fun_prop

theorem haarPacket_sq {d : Nat} (idx : HaarIndex d) (x : Vec d) :
    haarPacket idx x ^ (2 : Nat) =
      ∏ r : Fin d, haar1D idx.scale (idx.cell r) (idx.signature r) (x r) ^ (2 : Nat) := by
  unfold haarPacket
  rw [pow_two, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro r _hr
  rw [pow_two]

theorem integrable_haarPacket_sq {d : Nat} (idx : HaarIndex d) :
    Integrable (fun x : Vec d => haarPacket idx x ^ (2 : Nat))
      (volume : Measure (Vec d)) := by
  have hprod :
      Integrable
        (fun x : Vec d =>
          ∏ r : Fin d, haar1D idx.scale (idx.cell r) (idx.signature r) (x r) ^ (2 : Nat))
        (volume : Measure (Vec d)) := by
    rw [MeasureTheory.volume_pi]
    exact MeasureTheory.Integrable.fintype_prod
      (𝕜 := ℝ) (ι := Fin d) (E := ℝ) (μ := fun _ => (volume : Measure ℝ))
      (f := fun r y => haar1D idx.scale (idx.cell r) (idx.signature r) y ^ (2 : Nat))
      (fun r => integrable_haar1D_sq idx.scale (idx.cell r) (idx.signature r))
  refine hprod.congr (ae_of_all _ ?_)
  intro x
  exact (haarPacket_sq idx x).symm

theorem memLp_haarPacket {d : Nat} (idx : HaarIndex d) :
    MemLp (haarPacket idx) 2 (volume : Measure (Vec d)) := by
  rw [memLp_two_iff_integrable_sq]
  · exact integrable_haarPacket_sq idx
  · exact (measurable_haarPacket idx).aestronglyMeasurable

/-- The tensor-product Haar packet as an `L²(R^d)` vector. -/
@[expose]
noncomputable def haarPacketLp {d : Nat} (idx : HaarIndex d) :
    Lp ℝ 2 (volume : Measure (Vec d)) :=
  (memLp_haarPacket idx).toLp (haarPacket idx)

theorem inner_haarPacketLp_eq_integral {d : Nat} (idx₁ idx₂ : HaarIndex d) :
    ⟪haarPacketLp idx₁, haarPacketLp idx₂⟫_ℝ =
      ∫ x : Vec d, haarPacket idx₁ x * haarPacket idx₂ x ∂volume := by
  rw [haarPacketLp, haarPacketLp, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_haarPacket idx₁).coeFn_toLp,
    (memLp_haarPacket idx₂).coeFn_toLp] with x hx₁ hx₂
  simp [hx₁, hx₂, mul_comm]

private theorem coeFn_finset_sum_lp_real {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} (s : Finset ι) (f : ι → Lp ℝ 2 μ) :
    ⇑(∑ i ∈ s, f i) =ᵐ[μ] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction with
  | empty =>
      filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
      simpa using hx
  | insert i s hi ih =>
      filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with x hadd hsum
      rw [Finset.sum_insert hi]
      rw [Finset.sum_insert hi]
      rw [hadd, Pi.add_apply]
      rw [hsum]

theorem haarPacketLp_child_father_refine {d : Nat} (j : ℤ)
    (cell : Fin d → ℤ) (side : Fin d → Bool) :
    haarPacketLp
        { scale := j + 1
          cell := haarChildCell cell side
          signature := fun _ => false } =
      ∑ signature : Fin d → Bool,
        haarChildCoefficient side signature •
          haarPacketLp { scale := j, cell := cell, signature := signature } := by
  refine Lp.ext ?_
  let child : HaarIndex d :=
    { scale := j + 1
      cell := haarChildCell cell side
      signature := fun _ => false }
  let parent : (Fin d → Bool) → HaarIndex d :=
    fun signature => { scale := j, cell := cell, signature := signature }
  filter_upwards [(memLp_haarPacket child).coeFn_toLp,
    coeFn_finset_sum_lp_real (Finset.univ : Finset (Fin d → Bool))
      (fun signature =>
        haarChildCoefficient side signature • haarPacketLp (parent signature)),
    ae_all_iff.2 fun signature =>
      Lp.coeFn_smul (haarChildCoefficient side signature) (haarPacketLp (parent signature)),
    ae_all_iff.2 fun signature => (memLp_haarPacket (parent signature)).coeFn_toLp] with
    x hchild hsum hsmul hparent
  change (haarPacketLp child) x =
    (∑ signature : Fin d → Bool,
      haarChildCoefficient side signature • haarPacketLp (parent signature)) x
  change ((memLp_haarPacket child).toLp (haarPacket child)) x =
    (∑ signature : Fin d → Bool,
      haarChildCoefficient side signature • haarPacketLp (parent signature)) x
  rw [hchild, hsum]
  simp_rw [hsmul]
  change haarPacket child x =
    ∑ signature : Fin d → Bool,
      haarChildCoefficient side signature * (haarPacketLp (parent signature)) x
  unfold haarPacketLp
  simp_rw [hparent]
  exact haarPacket_child_father_refine_pointwise j cell side x

theorem haarPacket_mul_product {d : Nat} (idx₁ idx₂ : HaarIndex d) (x : Vec d) :
    haarPacket idx₁ x * haarPacket idx₂ x =
      ∏ r : Fin d,
        haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) (x r) *
          haar1D idx₂.scale (idx₂.cell r) (idx₂.signature r) (x r) := by
  unfold haarPacket
  rw [← Finset.prod_mul_distrib]

theorem integral_haarPacket_mul_product {d : Nat} (idx₁ idx₂ : HaarIndex d) :
    ∫ x : Vec d, haarPacket idx₁ x * haarPacket idx₂ x ∂volume =
      ∏ r : Fin d,
        ∫ y : ℝ,
          haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) y *
            haar1D idx₂.scale (idx₂.cell r) (idx₂.signature r) y ∂volume := by
  calc
    ∫ x : Vec d, haarPacket idx₁ x * haarPacket idx₂ x ∂volume =
        ∫ x : Vec d,
          ∏ r : Fin d,
            haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) (x r) *
              haar1D idx₂.scale (idx₂.cell r) (idx₂.signature r) (x r) ∂volume := by
          refine integral_congr_ae (ae_of_all _ ?_)
          intro x
          exact haarPacket_mul_product idx₁ idx₂ x
    _ = ∏ r : Fin d,
        ∫ y : ℝ,
          haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) y *
            haar1D idx₂.scale (idx₂.cell r) (idx₂.signature r) y ∂volume := by
          change ∫ x : (Fin d → ℝ),
              ∏ r : Fin d,
                (fun y : ℝ =>
                  haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) y *
                    haar1D idx₂.scale (idx₂.cell r) (idx₂.signature r) y) (x r)
              =
            ∏ r : Fin d,
              ∫ y : ℝ,
                (fun y : ℝ =>
                  haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) y *
                    haar1D idx₂.scale (idx₂.cell r) (idx₂.signature r) y) y
          exact MeasureTheory.integral_fintype_prod_volume_eq_prod
            (𝕜 := ℝ) (ι := Fin d) (E := fun _ => ℝ)
            (fun r y =>
              haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) y *
                haar1D idx₂.scale (idx₂.cell r) (idx₂.signature r) y)

theorem integral_haarPacket_mul_adjacent_of_fine_signature_true {d : Nat}
    (idx₁ idx₂ : HaarIndex d) (hscale : idx₂.scale = idx₁.scale + 1)
    {r : Fin d} (hsig : idx₂.signature r = true) :
    ∫ x : Vec d, haarPacket idx₁ x * haarPacket idx₂ x ∂volume = 0 := by
  rw [integral_haarPacket_mul_product idx₁ idx₂]
  apply Finset.prod_eq_zero (Finset.mem_univ r)
  rw [hscale, hsig]
  exact integral_haar1D_mul_adjacent_child_mother idx₁.scale
    (idx₁.cell r) (idx₂.cell r) (idx₁.signature r)

theorem integral_haarPacket_mul_finer_of_signature_true_nat_succ {d : Nat}
    (idx₁ idx₂ : HaarIndex d) (n : ℕ)
    (hscale : idx₂.scale = idx₁.scale + ((n + 1 : ℕ) : ℤ))
    {r : Fin d} (hsig : idx₂.signature r = true) :
    ∫ x : Vec d, haarPacket idx₁ x * haarPacket idx₂ x ∂volume = 0 := by
  rw [integral_haarPacket_mul_product idx₁ idx₂]
  apply Finset.prod_eq_zero (Finset.mem_univ r)
  rw [hscale, hsig]
  exact integral_haar1D_mul_finer_mother_nat_succ idx₁.scale
    (idx₁.cell r) (idx₂.cell r) (idx₁.signature r) n

theorem inner_haarPacketLp_finer_of_signature_true_nat_succ {d : Nat}
    (idx₁ idx₂ : HaarIndex d) (n : ℕ)
    (hscale : idx₂.scale = idx₁.scale + ((n + 1 : ℕ) : ℤ))
    {r : Fin d} (hsig : idx₂.signature r = true) :
    ⟪haarPacketLp idx₁, haarPacketLp idx₂⟫_ℝ = 0 := by
  rw [inner_haarPacketLp_eq_integral]
  exact integral_haarPacket_mul_finer_of_signature_true_nat_succ idx₁ idx₂ n hscale hsig

theorem haarPacket_mul_same_scale {d : Nat} (idx₁ idx₂ : HaarIndex d)
    (hscale : idx₁.scale = idx₂.scale) (x : Vec d) :
    haarPacket idx₁ x * haarPacket idx₂ x =
      ∏ r : Fin d,
        haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) (x r) *
          haar1D idx₁.scale (idx₂.cell r) (idx₂.signature r) (x r) := by
  unfold haarPacket
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro r _hr
  rw [← hscale]

theorem integral_haarPacket_mul_same_scale {d : Nat} (idx₁ idx₂ : HaarIndex d)
    (hscale : idx₁.scale = idx₂.scale) :
    ∫ x : Vec d, haarPacket idx₁ x * haarPacket idx₂ x ∂volume =
      ∏ r : Fin d,
        (if idx₁.cell r = idx₂.cell r then
          if idx₁.signature r = idx₂.signature r then (1 : ℝ) else 0
        else 0) := by
  calc
    ∫ x : Vec d, haarPacket idx₁ x * haarPacket idx₂ x ∂volume =
        ∫ x : Vec d,
          ∏ r : Fin d,
            haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) (x r) *
              haar1D idx₁.scale (idx₂.cell r) (idx₂.signature r) (x r) ∂volume := by
          refine integral_congr_ae (ae_of_all _ ?_)
          intro x
          exact haarPacket_mul_same_scale idx₁ idx₂ hscale x
    _ = ∏ r : Fin d,
        ∫ y : ℝ,
          haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) y *
            haar1D idx₁.scale (idx₂.cell r) (idx₂.signature r) y ∂volume := by
          change ∫ x : (Fin d → ℝ),
              ∏ r : Fin d,
                (fun y : ℝ =>
                  haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) y *
                    haar1D idx₁.scale (idx₂.cell r) (idx₂.signature r) y) (x r)
              =
            ∏ r : Fin d,
              ∫ y : ℝ,
                (fun y : ℝ =>
                  haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) y *
                    haar1D idx₁.scale (idx₂.cell r) (idx₂.signature r) y) y
          exact MeasureTheory.integral_fintype_prod_volume_eq_prod
            (𝕜 := ℝ) (ι := Fin d) (E := fun _ => ℝ)
            (fun r y =>
              haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) y *
                haar1D idx₁.scale (idx₂.cell r) (idx₂.signature r) y)
    _ = ∏ r : Fin d,
        (if idx₁.cell r = idx₂.cell r then
          if idx₁.signature r = idx₂.signature r then (1 : ℝ) else 0
        else 0) := by
          congr 1
          ext r
          exact integral_haar1D_mul_haar1D_same_scale idx₁.scale
            (idx₁.cell r) (idx₂.cell r) (idx₁.signature r) (idx₂.signature r)

theorem prod_haarPacket_same_scale_inner_eq_ite {d : Nat} (idx₁ idx₂ : HaarIndex d)
    (hscale : idx₁.scale = idx₂.scale) :
    (∏ r : Fin d,
        (if idx₁.cell r = idx₂.cell r then
          if idx₁.signature r = idx₂.signature r then (1 : ℝ) else 0
        else 0)) =
      if idx₁ = idx₂ then 1 else 0 := by
  by_cases hidx : idx₁ = idx₂
  · subst idx₂
    simp
  · have hne : ∃ r : Fin d, idx₁.cell r ≠ idx₂.cell r ∨
        idx₁.signature r ≠ idx₂.signature r := by
      by_contra hnot
      push Not at hnot
      apply hidx
      have hcell : idx₁.cell = idx₂.cell := funext fun r => (hnot r).1
      have hsig : idx₁.signature = idx₂.signature := funext fun r => (hnot r).2
      cases idx₁
      cases idx₂
      simp at hscale hcell hsig ⊢
      exact ⟨hscale, hcell, hsig⟩
    rcases hne with ⟨r, hrcell | hrsig⟩
    · rw [ite_eq_right hidx]
      apply Finset.prod_eq_zero (Finset.mem_univ r)
      simp [hrcell]
    · rw [ite_eq_right hidx]
      apply Finset.prod_eq_zero (Finset.mem_univ r)
      simp [hrsig]

theorem integral_haarPacket_mul_same_scale_ite {d : Nat} (idx₁ idx₂ : HaarIndex d)
    (hscale : idx₁.scale = idx₂.scale) :
    ∫ x : Vec d, haarPacket idx₁ x * haarPacket idx₂ x ∂volume =
      if idx₁ = idx₂ then 1 else 0 := by
  rw [integral_haarPacket_mul_same_scale idx₁ idx₂ hscale]
  exact prod_haarPacket_same_scale_inner_eq_ite idx₁ idx₂ hscale

/-- Same-scale tensor Haar `L²` inner products reduce to equality of full packet indices. -/
theorem inner_haarPacketLp_same_scale {d : Nat} (idx₁ idx₂ : HaarIndex d)
    (hscale : idx₁.scale = idx₂.scale) :
    ⟪haarPacketLp idx₁, haarPacketLp idx₂⟫_ℝ =
      if idx₁ = idx₂ then 1 else 0 := by
  rw [haarPacketLp, haarPacketLp, MeasureTheory.L2.inner_def]
  calc
    ∫ x : Vec d,
        inner (𝕜 := ℝ)
          ((memLp_haarPacket idx₁).toLp (haarPacket idx₁) x)
          ((memLp_haarPacket idx₂).toLp (haarPacket idx₂) x)
        ∂volume =
        ∫ x : Vec d, haarPacket idx₁ x * haarPacket idx₂ x ∂volume := by
          refine integral_congr_ae ?_
          filter_upwards [(memLp_haarPacket idx₁).coeFn_toLp,
            (memLp_haarPacket idx₂).coeFn_toLp] with x hx₁ hx₂
          simp [hx₁, hx₂, mul_comm]
    _ = if idx₁ = idx₂ then 1 else 0 :=
      integral_haarPacket_mul_same_scale_ite idx₁ idx₂ hscale

/-- The corrected tensor-product Haar wavelet packet. -/
@[expose]
noncomputable def haarWaveletPacket {d : Nat} (idx : HaarWaveletIndex d) : Vec d → ℝ :=
  haarPacket idx.toHaarIndex

@[fun_prop]
theorem measurable_haarWaveletPacket {d : Nat} (idx : HaarWaveletIndex d) :
    Measurable (haarWaveletPacket idx) :=
  measurable_haarPacket idx.toHaarIndex

theorem exists_true_of_ne_false_signature {d : Nat} {signature : Fin d → Bool}
    (h : signature ≠ fun _ => false) :
    ∃ r : Fin d, signature r = true := by
  by_contra hnot
  push Not at hnot
  apply h
  funext r
  cases hsig : signature r
  · rfl
  · exact False.elim (hnot r hsig)

/-- Adjacent-scale tensor Haar wavelets are orthogonal when the second packet is one scale finer. -/
theorem integral_haarWaveletPacket_mul_adjacent {d : Nat}
    (idx₁ idx₂ : HaarWaveletIndex d) (hscale : idx₂.scale = idx₁.scale + 1) :
    ∫ x : Vec d, haarWaveletPacket idx₁ x * haarWaveletPacket idx₂ x ∂volume = 0 := by
  rcases exists_true_of_ne_false_signature idx₂.signature.property with ⟨r, hsig⟩
  exact integral_haarPacket_mul_adjacent_of_fine_signature_true
    idx₁.toHaarIndex idx₂.toHaarIndex hscale hsig

theorem integral_haarWaveletPacket_mul_adjacent_symm {d : Nat}
    (idx₁ idx₂ : HaarWaveletIndex d) (hscale : idx₁.scale = idx₂.scale + 1) :
    ∫ x : Vec d, haarWaveletPacket idx₁ x * haarWaveletPacket idx₂ x ∂volume = 0 := by
  calc
    ∫ x : Vec d, haarWaveletPacket idx₁ x * haarWaveletPacket idx₂ x ∂volume =
        ∫ x : Vec d, haarWaveletPacket idx₂ x * haarWaveletPacket idx₁ x ∂volume := by
          refine integral_congr_ae (ae_of_all _ ?_)
          intro x
          ring
    _ = 0 := by
          exact integral_haarWaveletPacket_mul_adjacent idx₂ idx₁ hscale

theorem integral_haarWaveletPacket_mul_finer_nat_succ {d : Nat}
    (idx₁ idx₂ : HaarWaveletIndex d) (n : ℕ)
    (hscale : idx₂.scale = idx₁.scale + ((n + 1 : ℕ) : ℤ)) :
    ∫ x : Vec d, haarWaveletPacket idx₁ x * haarWaveletPacket idx₂ x ∂volume = 0 := by
  rcases exists_true_of_ne_false_signature idx₂.signature.property with ⟨r, hsig⟩
  exact integral_haarPacket_mul_finer_of_signature_true_nat_succ
    idx₁.toHaarIndex idx₂.toHaarIndex n hscale hsig

theorem integral_haarWaveletPacket_mul_finer_nat_succ_symm {d : Nat}
    (idx₁ idx₂ : HaarWaveletIndex d) (n : ℕ)
    (hscale : idx₁.scale = idx₂.scale + ((n + 1 : ℕ) : ℤ)) :
    ∫ x : Vec d, haarWaveletPacket idx₁ x * haarWaveletPacket idx₂ x ∂volume = 0 := by
  calc
    ∫ x : Vec d, haarWaveletPacket idx₁ x * haarWaveletPacket idx₂ x ∂volume =
        ∫ x : Vec d, haarWaveletPacket idx₂ x * haarWaveletPacket idx₁ x ∂volume := by
          refine integral_congr_ae (ae_of_all _ ?_)
          intro x
          ring
    _ = 0 := integral_haarWaveletPacket_mul_finer_nat_succ idx₂ idx₁ n hscale

theorem memLp_haarWaveletPacket {d : Nat} (idx : HaarWaveletIndex d) :
    MemLp (haarWaveletPacket idx) 2 (volume : Measure (Vec d)) := by
  change MemLp (haarPacket idx.toHaarIndex) 2 (volume : Measure (Vec d))
  exact memLp_haarPacket idx.toHaarIndex

/-- The corrected tensor-product Haar wavelet packet as an `L²(R^d)` vector. -/
@[expose]
noncomputable def haarWaveletPacketLp {d : Nat} (idx : HaarWaveletIndex d) :
    Lp ℝ 2 (volume : Measure (Vec d)) :=
  (memLp_haarWaveletPacket idx).toLp (haarWaveletPacket idx)

theorem haarWaveletPacketLp_eq_haarPacketLp {d : Nat} (idx : HaarWaveletIndex d) :
    haarWaveletPacketLp idx = haarPacketLp idx.toHaarIndex :=
  rfl

theorem inner_haarWaveletPacketLp_same_scale {d : Nat} (idx₁ idx₂ : HaarWaveletIndex d)
    (hscale : idx₁.scale = idx₂.scale) :
    ⟪haarWaveletPacketLp idx₁, haarWaveletPacketLp idx₂⟫_ℝ =
      if idx₁ = idx₂ then 1 else 0 := by
  rw [haarWaveletPacketLp, haarWaveletPacketLp, MeasureTheory.L2.inner_def]
  calc
    ∫ x : Vec d,
        inner (𝕜 := ℝ)
          ((memLp_haarWaveletPacket idx₁).toLp (haarWaveletPacket idx₁) x)
          ((memLp_haarWaveletPacket idx₂).toLp (haarWaveletPacket idx₂) x)
        ∂volume =
        ∫ x : Vec d, haarWaveletPacket idx₁ x * haarWaveletPacket idx₂ x ∂volume := by
          refine integral_congr_ae ?_
          filter_upwards [(memLp_haarWaveletPacket idx₁).coeFn_toLp,
            (memLp_haarWaveletPacket idx₂).coeFn_toLp] with x hx₁ hx₂
          simp [hx₁, hx₂, mul_comm]
    _ = if idx₁ = idx₂ then 1 else 0 := by
          change ∫ x : Vec d, haarPacket idx₁.toHaarIndex x * haarPacket idx₂.toHaarIndex x
              ∂volume = if idx₁ = idx₂ then 1 else 0
          rw [integral_haarPacket_mul_same_scale_ite idx₁.toHaarIndex idx₂.toHaarIndex hscale]
          by_cases hidx : idx₁ = idx₂
          · simp [hidx]
          · have hraw : idx₁.toHaarIndex ≠ idx₂.toHaarIndex := by
              intro hraw
              exact hidx (HaarWaveletIndex.toHaarIndex_injective hraw)
            simp [hidx, hraw]

theorem inner_haarWaveletPacketLp_adjacent {d : Nat}
    (idx₁ idx₂ : HaarWaveletIndex d) (hscale : idx₂.scale = idx₁.scale + 1) :
    ⟪haarWaveletPacketLp idx₁, haarWaveletPacketLp idx₂⟫_ℝ = 0 := by
  rw [haarWaveletPacketLp, haarWaveletPacketLp, MeasureTheory.L2.inner_def]
  calc
    ∫ x : Vec d,
        inner (𝕜 := ℝ)
          ((memLp_haarWaveletPacket idx₁).toLp (haarWaveletPacket idx₁) x)
          ((memLp_haarWaveletPacket idx₂).toLp (haarWaveletPacket idx₂) x)
        ∂volume =
        ∫ x : Vec d, haarWaveletPacket idx₁ x * haarWaveletPacket idx₂ x ∂volume := by
          refine integral_congr_ae ?_
          filter_upwards [(memLp_haarWaveletPacket idx₁).coeFn_toLp,
            (memLp_haarWaveletPacket idx₂).coeFn_toLp] with x hx₁ hx₂
          simp [hx₁, hx₂, mul_comm]
    _ = 0 := integral_haarWaveletPacket_mul_adjacent idx₁ idx₂ hscale

theorem inner_haarWaveletPacketLp_finer_nat_succ {d : Nat}
    (idx₁ idx₂ : HaarWaveletIndex d) (n : ℕ)
    (hscale : idx₂.scale = idx₁.scale + ((n + 1 : ℕ) : ℤ)) :
    ⟪haarWaveletPacketLp idx₁, haarWaveletPacketLp idx₂⟫_ℝ = 0 := by
  rw [haarWaveletPacketLp, haarWaveletPacketLp, MeasureTheory.L2.inner_def]
  calc
    ∫ x : Vec d,
        inner (𝕜 := ℝ)
          ((memLp_haarWaveletPacket idx₁).toLp (haarWaveletPacket idx₁) x)
          ((memLp_haarWaveletPacket idx₂).toLp (haarWaveletPacket idx₂) x)
        ∂volume =
        ∫ x : Vec d, haarWaveletPacket idx₁ x * haarWaveletPacket idx₂ x ∂volume := by
          refine integral_congr_ae ?_
          filter_upwards [(memLp_haarWaveletPacket idx₁).coeFn_toLp,
            (memLp_haarWaveletPacket idx₂).coeFn_toLp] with x hx₁ hx₂
          simp [hx₁, hx₂, mul_comm]
    _ = 0 := integral_haarWaveletPacket_mul_finer_nat_succ idx₁ idx₂ n hscale

theorem inner_haarWaveletPacketLp_finer_nat_succ_symm {d : Nat}
    (idx₁ idx₂ : HaarWaveletIndex d) (n : ℕ)
    (hscale : idx₁.scale = idx₂.scale + ((n + 1 : ℕ) : ℤ)) :
    ⟪haarWaveletPacketLp idx₁, haarWaveletPacketLp idx₂⟫_ℝ = 0 := by
  rw [← inner_conj_symm]
  simp [inner_haarWaveletPacketLp_finer_nat_succ idx₂ idx₁ n hscale]

theorem exists_nat_succ_scale_gap {j₁ j₂ : ℤ} (h : j₁ < j₂) :
    ∃ n : ℕ, j₂ = j₁ + ((n + 1 : ℕ) : ℤ) := by
  let m : ℕ := (j₂ - j₁).toNat
  have hm_cast : (m : ℤ) = j₂ - j₁ := by
    exact Int.toNat_sub_of_le (show j₁ ≤ j₂ from le_of_lt h)
  have hm_pos : 0 < m := by
    have hdiff_pos : 0 < j₂ - j₁ := sub_pos.mpr h
    have hdiff_cast_pos : 0 < (m : ℤ) := by
      simpa [hm_cast] using hdiff_pos
    exact_mod_cast hdiff_cast_pos
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hm_pos)
  refine ⟨n, ?_⟩
  have hm_eq : m = n + 1 := by omega
  have hgap : (j₂ - j₁ : ℤ) = ((n + 1 : ℕ) : ℤ) := by
    rw [← hm_cast, hm_eq]
  omega

theorem integral_haarWaveletPacket_mul_of_scale_lt {d : Nat}
    (idx₁ idx₂ : HaarWaveletIndex d) (hscale : idx₁.scale < idx₂.scale) :
    ∫ x : Vec d, haarWaveletPacket idx₁ x * haarWaveletPacket idx₂ x ∂volume = 0 := by
  obtain ⟨n, hn⟩ := exists_nat_succ_scale_gap hscale
  exact integral_haarWaveletPacket_mul_finer_nat_succ idx₁ idx₂ n hn

theorem integral_haarWaveletPacket_mul_of_scale_gt {d : Nat}
    (idx₁ idx₂ : HaarWaveletIndex d) (hscale : idx₂.scale < idx₁.scale) :
    ∫ x : Vec d, haarWaveletPacket idx₁ x * haarWaveletPacket idx₂ x ∂volume = 0 := by
  obtain ⟨n, hn⟩ := exists_nat_succ_scale_gap hscale
  exact integral_haarWaveletPacket_mul_finer_nat_succ_symm idx₁ idx₂ n hn

theorem inner_haarWaveletPacketLp_of_scale_lt {d : Nat}
    (idx₁ idx₂ : HaarWaveletIndex d) (hscale : idx₁.scale < idx₂.scale) :
    ⟪haarWaveletPacketLp idx₁, haarWaveletPacketLp idx₂⟫_ℝ = 0 := by
  obtain ⟨n, hn⟩ := exists_nat_succ_scale_gap hscale
  exact inner_haarWaveletPacketLp_finer_nat_succ idx₁ idx₂ n hn

theorem inner_haarWaveletPacketLp_of_scale_gt {d : Nat}
    (idx₁ idx₂ : HaarWaveletIndex d) (hscale : idx₂.scale < idx₁.scale) :
    ⟪haarWaveletPacketLp idx₁, haarWaveletPacketLp idx₂⟫_ℝ = 0 := by
  obtain ⟨n, hn⟩ := exists_nat_succ_scale_gap hscale
  exact inner_haarWaveletPacketLp_finer_nat_succ_symm idx₁ idx₂ n hn

theorem inner_haarWaveletPacketLp (d : Nat) (idx₁ idx₂ : HaarWaveletIndex d) :
    ⟪haarWaveletPacketLp idx₁, haarWaveletPacketLp idx₂⟫_ℝ =
      if idx₁ = idx₂ then 1 else 0 := by
  by_cases hscale_eq : idx₁.scale = idx₂.scale
  · rw [inner_haarWaveletPacketLp_same_scale idx₁ idx₂ hscale_eq]
  · have hlt_or_gt : idx₁.scale < idx₂.scale ∨ idx₂.scale < idx₁.scale :=
      lt_or_gt_of_ne hscale_eq
    rw [ite_eq_right]
    · rcases hlt_or_gt with hlt | hgt
      · exact inner_haarWaveletPacketLp_of_scale_lt idx₁ idx₂ hlt
      · exact inner_haarWaveletPacketLp_of_scale_gt idx₁ idx₂ hgt
    · intro hidx
      exact hscale_eq (by rw [hidx])

theorem orthonormal_haarWaveletPacketLp (d : Nat) :
    Orthonormal ℝ (fun idx : HaarWaveletIndex d => haarWaveletPacketLp idx) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  exact inner_haarWaveletPacketLp d i j

end GaussianFields

end
