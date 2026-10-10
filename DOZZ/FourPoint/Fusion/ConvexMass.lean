/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.RootOnlyInverseMoments
/-! # Positive segments of extended masses -/
@[expose] public section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs
/-- Every nonpositive moment of a convex mass segment is bounded by the two endpoint moments. -/
theorem fusion_convexMass_inverse_bound (a b : ℝ≥0∞) (t s : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ≤ 0) :
    (ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * b) ^ s ≤ a ^ s + b ^ s := by
  have hsum : ENNReal.ofReal t + ENNReal.ofReal (1 - t) = 1 := by
    rw [← ENNReal.ofReal_add ht.1 (sub_nonneg.mpr ht.2)]
    simp
  rcases le_total a b with hab | hba
  · have h : a ≤ ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * b := by
      calc
        a = (ENNReal.ofReal t + ENNReal.ofReal (1 - t)) * a := by rw [hsum, one_mul]
        _ ≤ _ := by rw [add_mul]; exact add_le_add le_rfl (mul_le_mul' le_rfl hab)
    exact (ennreal_rpow_antitone_of_nonpos h hs).trans le_self_add
  · have h : b ≤ ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * b := by
      calc
        b = (ENNReal.ofReal t + ENNReal.ofReal (1 - t)) * b := by rw [hsum, one_mul]
        _ ≤ _ := by rw [add_mul]; exact add_le_add (mul_le_mul' le_rfl hba) le_rfl
    exact (ennreal_rpow_antitone_of_nonpos h hs).trans le_add_self

/-- Positive finite endpoints give a positive finite segment, including its endpoints. -/
theorem fusion_convexMass_pos_finite (a b : ℝ≥0∞) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (ha0 : a ≠ 0) (hat : a ≠ ⊤) (hb0 : b ≠ 0) (hbt : b ≠ ⊤) :
    ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * b ≠ 0 ∧
      ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * b ≠ ⊤ := by
  refine ⟨?_, ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hat,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbt⟩⟩
  by_cases ht0 : t = 0
  · simpa only [ht0, ENNReal.ofReal_zero, zero_mul, sub_zero, ENNReal.ofReal_one, one_mul, zero_add] using hb0
  · exact ne_of_gt ((ENNReal.mul_pos (ENNReal.ofReal_pos.mpr
      (lt_of_le_of_ne ht.1 (Ne.symm ht0))).ne' ha0).trans_le le_self_add)

/-- Convex combinations of finite endpoint masses converging to the same limit also converge
in probability. Independence is not needed. -/
theorem fusion_convexMass_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (a b : ℕ → Ω → ℝ≥0∞) (g : Ω → ℝ≥0∞)
    (ha : ∀ n, AEMeasurable (a n) P) (hb : ∀ n, AEMeasurable (b n) P)
    (haf : ∀ n, ∀ᵐ ω ∂P, a n ω ≠ ⊤) (hbf : ∀ n, ∀ᵐ ω ∂P, b n ω ≠ ⊤)
    (hac : TendstoInMeasure P (fun n ω => (a n ω).toReal) atTop (fun ω => (g ω).toReal))
    (hbc : TendstoInMeasure P (fun n ω => (b n ω).toReal) atTop (fun ω => (g ω).toReal))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    TendstoInMeasure P (fun n ω =>
      (ENNReal.ofReal t * a n ω + ENNReal.ofReal (1 - t) * b n ω).toReal)
      atTop (fun ω => (g ω).toReal) := by
  let f := fun n ω => t * (a n ω).toReal + (1 - t) * (b n ω).toReal
  have ham : ∀ n, AEStronglyMeasurable (fun ω => (a n ω).toReal) P :=
    fun n => (ha n).ennreal_toReal.aestronglyMeasurable
  have hbm : ∀ n, AEStronglyMeasurable (fun ω => (b n ω).toReal) P :=
    fun n => (hb n).ennreal_toReal.aestronglyMeasurable
  have hfm : ∀ n, AEStronglyMeasurable (f n) P := fun n =>
    ((ham n).const_mul t).add ((hbm n).const_mul (1 - t))
  have hc : TendstoInMeasure P f atTop (fun ω => (g ω).toReal) := by
    apply (exists_seq_tendstoInMeasure_atTop_iff hfm).mpr
    intro ns hns
    obtain ⟨u, hu, hua⟩ := (exists_seq_tendstoInMeasure_atTop_iff ham).mp hac ns hns
    obtain ⟨v, hv, hvb⟩ := (exists_seq_tendstoInMeasure_atTop_iff hbm).mp hbc (ns ∘ u) (hns.comp hu)
    refine ⟨u ∘ v, hu.comp hv, ?_⟩
    filter_upwards [hua, hvb] with ω hωa hωb
    have h := ((hωa.comp hv.tendsto_atTop).const_mul t).add (hωb.const_mul (1 - t))
    have he : t * (g ω).toReal + (1 - t) * (g ω).toReal = (g ω).toReal := by ring
    rw [he] at h
    exact h
  apply TendstoInMeasure.congr_left _ hc
  intro n
  filter_upwards [haf n, hbf n] with ω hωa hωb
  simp only [f, ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωa)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωb), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal ht.1, ENNReal.toReal_ofReal (sub_nonneg.mpr ht.2)]
end DOZZ.Proofs
