/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Roots.ChargeSegments
public import DOZZ.Roots.FormulaRegularity
public import DOZZ.Roots.MeromorphicContinuation
public import DOZZ.Roots.Normalization
public import DOZZ.Correlations.Analytic.StructureConstantHolomorphic
import DOZZ.Complex.Identity
import Mathlib.Topology.Connected.LocallyConnected
/-! # Continuing the calibrated cube identity to the finite extended domain -/
@[expose] public section
open MeasureTheory Set Filter Topology
namespace DOZZ.Proofs
/-- A calibrated near-Q cube determines the unit-volume moment at every pole-free extended triple. -/
theorem roots_unitVolume_of_cube {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ η : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ) (hη : 0 < η) (hηQ : 3 * η < Q γ)
    (U : ℂ → ℂ) (hU : IsUpsilon γ U) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hcube : ∀ a b c : ℝ, Q γ - η < a → a < Q γ → Q γ - η < b → b < Q γ →
      Q γ - η < c → c < Q γ → (unitVolumeStructureConstant P M γ a b c : ℂ) =
        ((μ : ℂ) ^ (sExp γ a b c : ℂ) / Complex.Gamma (sExp γ a b c)) * dozzFormula γ μ U a b c)
    (a b c : ℝ) (hα : ExtendedSeiberg3 γ a b c) (hs : ∀ n : ℕ, sExp γ a b c ≠ -(n : ℝ)) :
    (unitVolumeStructureConstant P M γ a b c : ℂ) =
      ((μ : ℂ) ^ (sExp γ a b c : ℂ) / Complex.Gamma (sExp γ a b c)) * dozzFormula γ μ U a b c := by
  let q := Q γ - η / 2
  let α : Fin 3 → ℝ := ![a, b, c]
  let A : ℂ → Fin 3 → ℂ := fun z i => (q : ℂ) + z * ((α i - q : ℝ) : ℂ)
  let G := fun z : ℂ => ((μ : ℂ) ^ ((A z 0 + A z 1 + A z 2 - 2 * Q γ) / γ) /
    Complex.Gamma ((A z 0 + A z 1 + A z 2 - 2 * Q γ) / γ)) * dozzFormula γ μ U (A z 0) (A z 1) (A z 2)
  have hqlo : Q γ - η < q := by dsimp only [q]; linarith only [hη]
  have hqhi : q < Q γ := by dsimp only [q]; linarith only [hη]
  have hqα := roots_extended_cube hγ hηQ hqlo hqhi hqlo hqhi hqlo hqhi
  have hqs : 0 < sExp γ q q q := by
    apply div_pos _ hγ
    dsimp only [q]
    linarith only [hηQ, hη]
  have hqsp : ∀ n : ℕ, sExp γ q q q ≠ -(n : ℝ) := fun n hn =>
    (not_lt_of_ge (neg_nonpos.mpr (Nat.cast_nonneg n))) (hn ▸ hqs)
  have hA : Differentiable ℂ A := by
    apply differentiable_pi.mpr
    intro i
    exact (differentiable_const _).add (differentiable_id.mul_const _)
  have hAr (t : ℝ) : A (t : ℂ) = complexifyNCharges (fun i => q + t * (α i - q)) := by
    ext i
    simp only [A, complexifyNCharges]
    push_cast
    ring
  obtain ⟨V, hVo, hVα, f, hfd, hfv⟩ := unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM
  let W := A ⁻¹' V
  have hWo : IsOpen W := hVo.preimage hA.continuous
  have hWpath : ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) ∈ W := by
    intro t ht
    change A (t : ℂ) ∈ V
    rw [hAr]
    apply hVα
    have hd := roots_extendedSeiberg3_segment hγ hα hqα t ht
    convert hd using 1 <;> simp only [α, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  have hW0 : (0 : ℂ) ∈ W := by simpa only [Complex.ofReal_zero] using hWpath 0 ⟨le_rfl, zero_le_one⟩
  have hW1 : (1 : ℂ) ∈ W := by simpa only [Complex.ofReal_one] using hWpath 1 ⟨zero_le_one, le_rfl⟩
  let T := connectedComponentIn W (0 : ℂ)
  have hT0 : (0 : ℂ) ∈ T := mem_connectedComponentIn hW0
  have hT1 : (1 : ℂ) ∈ T := by
    have hpre := (show IsPreconnected (Icc (0 : ℝ) 1) from isPreconnected_Icc).image (fun t : ℝ => (t : ℂ)) Complex.continuous_ofReal.continuousOn
    have him : Complex.ofReal '' Icc (0 : ℝ) 1 ⊆ W := by rintro _ ⟨t, ht, rfl⟩; exact hWpath t ht
    have hsub := hpre.subset_connectedComponentIn (mem_image_of_mem Complex.ofReal ⟨le_rfl, zero_le_one⟩) him
    exact hsub (mem_image_of_mem Complex.ofReal ⟨zero_le_one, le_rfl⟩)
  have hFdiff : DifferentiableOn ℂ (fun z => f (A z)) W :=
    hfd.comp hA.differentiableOn (fun _ hz => hz)
  have hFm : MeromorphicOn (fun z => f (A z)) T := by
    intro z hz
    exact (hFdiff.analyticAt (hWo.mem_nhds (connectedComponentIn_subset W 0 hz))).meromorphicAt
  have hGm : MeromorphicOn G T :=
    (roots_formula_line_meromorphic hγ hγ2 hμ hU (fun i z => A z i)
      (fun i => (differentiable_const _).add (differentiable_id.mul_const _))).mono_set (subset_univ T)
  have hF0 : AnalyticAt ℂ (fun z => f (A z)) 0 := hFdiff.analyticAt (hWo.mem_nhds hW0)
  have hG0 : AnalyticAt ℂ G 0 := roots_formula_line_analyticAt hγ hγ2 hμ hU (fun i z => A z i) 0
    (fun i => ((differentiable_const _).add (differentiable_id.mul_const _)).analyticAt 0)
    q q q (by simp only [A, zero_mul, add_zero]) (by simp only [A, zero_mul, add_zero])
    (by simp only [A, zero_mul, add_zero]) hqα hqsp
  have hreal : ∀ᶠ t : ℝ in nhds 0, f (A (t : ℂ)) = G (t : ℂ) := by
    have hlo : ∀ᶠ t : ℝ in nhds 0, ∀ i : Fin 3, Q γ - η < q + t * (α i - q) := by
      rw [eventually_all]
      intro i
      have hc : ContinuousAt (fun t : ℝ => q + t * (α i - q)) 0 := by fun_prop
      exact continuousAt_const.eventually_lt hc (by simpa only [zero_mul, add_zero] using hqlo)
    have hhi : ∀ᶠ t : ℝ in nhds 0, ∀ i : Fin 3, q + t * (α i - q) < Q γ := by
      rw [eventually_all]
      intro i
      have hc : ContinuousAt (fun t : ℝ => q + t * (α i - q)) 0 := by fun_prop
      exact hc.tendsto.eventually_lt_const (by simpa only [zero_mul, add_zero] using hqhi)
    filter_upwards [hlo, hhi] with t htlo hthi
    let β := fun i : Fin 3 => q + t * (α i - q)
    have hβ := roots_extended_cube hγ hηQ (htlo 0) (hthi 0) (htlo 1) (hthi 1) (htlo 2) (hthi 2)
    rw [hAr, hfv β hβ, hcube (β 0) (β 1) (β 2) (htlo 0) (hthi 0) (htlo 1) (hthi 1) (htlo 2) (hthi 2)]
    dsimp only [G]
    rw [hAr]
    simp only [complexifyNCharges, sExp, β]
    push_cast
    rfl
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hreal
  have hfreq := frequently_eq_of_real_interval 0 R hR (fun z => f (A z)) G
    (fun t ht => hball (by simpa only [Metric.mem_ball, Real.dist_eq] using ht))
  have heq : (fun z => f (A z)) =ᶠ[nhds 0] G :=
    (hF0.frequently_eq_iff_eventually_eq hG0).mp hfreq
  have hG1 : AnalyticAt ℂ G 1 := roots_formula_line_analyticAt hγ hγ2 hμ hU (fun i z => A z i) 1
    (fun i => ((differentiable_const _).add (differentiable_id.mul_const _)).analyticAt 1)
    a b c (by simp only [A, α, Matrix.cons_val_zero, one_mul]; push_cast; ring)
    (by simp only [A, α, Matrix.cons_val_one, Matrix.cons_val_zero, one_mul]; push_cast; ring)
    (by simp only [A, α, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_mul]; push_cast; ring) hα hs
  have he := roots_eq_of_meromorphic_continuation T isPreconnected_connectedComponentIn
    (fun z => f (A z)) G hFm hGm 0 1 hT0 hT1 heq
    (hFdiff.analyticAt (hWo.mem_nhds hW1)).continuousAt hG1.continuousAt
  have hA1 : A 1 = complexifyNCharges α := by ext i; simp only [A, complexifyNCharges, one_mul]; push_cast; ring
  rw [hA1, hfv α hα] at he
  simpa only [G, hA1, complexifyNCharges, α, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    sExp, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat] using he
end DOZZ.Proofs
