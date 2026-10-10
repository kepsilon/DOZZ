/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.FirstStrip.Seed
public import DOZZ.ShiftEquations.DualR.Segment
public import DOZZ.Statements.Defs.IsEquatorGFF
public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.Statements.Complex.HorizontalStrip
import DOZZ.ShiftEquations.Shift.ShiftGluing
import DOZZ.ShiftEquations.Residual.Calibration
import DOZZ.ShiftEquations.Residual.Joint
import DOZZ.ShiftEquations.Quotient.Divisors
import DOZZ.Correlations.Analytic.StructureConstantHolomorphic
import DOZZ.Brownian.Reflection.RtheorAnalytic
import DOZZ.ShiftEquations.Reflection.RbarContinuity
import DOZZ.ShiftEquations.Gluing.Meromorphy

/-!
# The first structure shift on a strip, from the unreflected formula

Fix spectators `α₂, α₃ ∈ (Q - η, Q)`. The continued slice `g(z) = C_f(z, α₂, α₃)`
(`DOZZ.unitVolumeStructureConstant_holomorphic_near_extended_domain`) is holomorphic near `(2η, Q)`
and equals the structure constant there. By the unreflected formula and the classification
(`firstShift_real_of_unreflected`) the first structure shift `C(x) = -𝒜(x - γ/2) C(x - γ)/(πμ)`
holds at every real `x ∈ (γ + 2η, Q)`. On a subinterval where `𝒜` has no zero or pole,
`g(x - γ) = m(x) g(x)` with the meromorphic multiplier `m = -πμ/𝒜(· - γ/2)`; the strip continuation
`exists_meromorphicOn_strip_of_shift` extends `g` to a meromorphic function on a strip with this
shift near every point, and the cut-off makes the first shift hold along the codiscrete filter of
`ℂ` ([KRV, §11]: "Therefore `F` extends to a meromorphic function on a strip").
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- **The first structure shift on a strip from the unreflected formula.** `hUnreflectedFormula` is the conclusion
of `DOZZ.gammaHalf_full_unreflected_formula` at the given field, chaos, coupling and cosmological
constant; the diagonal classification `DOZZ.degenerateFourPoint_diagonal_classification` is used
directly. -/
theorem structureConstant_first_shift_strip_of_unreflected
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ η : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hη : 0 < η ∧ Q γ - 2 * η > γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (α₂ α₃ : ℝ)
    (hα₂ : Q γ - η < α₂ ∧ α₂ < Q γ)
    (hα₃ : Q γ - η < α₃ ∧ α₃ < Q γ)
    (hUnreflectedFormula : ∀ {H : ℂ → ℂ → ℂ → ℂ → ℂ}, IsGaussHypergeometricFamily H → ∀ α₁ α₂ α₃ : ℝ,
      γ / 2 < α₁ → α₁ < 2 / γ → α₂ < Q γ → α₃ < Q γ → 2 * Q γ + γ / 2 < α₁ + α₂ + α₃ →
      let a := gaussParameterA γ (γ / 2) α₁ α₂ α₃
      let b := gaussParameterB γ (γ / 2) α₁ α₂ α₃
      let c := gaussParameterC γ (γ / 2) α₁
      ∀ z ∈ gaussCutPlane,
        fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z =
          structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ *
              ‖gaussFMinus H a b c z‖ ^ 2 +
            (-μ * (planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re) *
              structureConstant P M γ μ (α₁ + γ / 2) α₂ α₃ *
                ‖gaussFPlus H a b c z‖ ^ 2) :
    ∃ h : ℝ, 0 < h ∧ ∃ C : ℂ → ℂ,
      MeromorphicOn C {z | |z.im| < h} ∧
      (∀ α : ℝ, 2 * η < α → α < Q γ →
        C (α : ℂ) = (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
      ∀ᶠ z in codiscrete ℂ,
        C (z + γ / 2) =
          -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) *
            C (z - γ / 2) := by
  obtain ⟨V₃, hV₃, hV₃mem, f₃, hf₃, hf₃eq⟩ :=
    unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM
  obtain ⟨hη0, hηQ⟩ := hη
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hγh : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ (by norm_num) hγ]
    linarith only [mul_lt_mul'' hγ2 hγ2 hγ.le hγ.le]
  have hγc : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ.ne'
  have hμc : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ.ne'
  have hπc : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  -- the continued slice and its window of holomorphy
  set ℓ : ℂ → Fin 3 → ℂ := tripleFirst (α₂ : ℂ) (α₃ : ℂ) with hℓ
  set g : ℂ → ℂ := fun z => structureConstantH f₃ γ μ (ℓ z) with hg
  set W : Set ℂ := ℓ ⁻¹' V₃ ∩ {z | 0 < (sExpC γ (ℓ z)).re} with hW
  have hsc : Continuous fun z => sExpC γ (ℓ z) := by
    unfold sExpC
    exact ((((differentiable_pi.mp (differentiable_tripleFirst _ _) 0).continuous.add
      (differentiable_pi.mp (differentiable_tripleFirst _ _) 1).continuous).add
      (differentiable_pi.mp (differentiable_tripleFirst _ _) 2).continuous).sub
      continuous_const).div_const _
  have hWo : IsOpen W := (hV₃.preimage (differentiable_tripleFirst _ _).continuous).inter
    (isOpen_lt continuous_const (Complex.continuous_re.comp hsc))
  have hgd : DifferentiableOn ℂ g W := fun z hz =>
    (analyticAt_structureConstantH_comp' hV₃ hf₃ hμ (differentiable_tripleFirst _ _) hz.1
      (analyticAt_Gamma_of_ne fun n hn => by
        have h : 0 < (sExpC γ (ℓ z)).re := hz.2
        rw [hn] at h
        simp at h
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)).differentiableAt.differentiableWithinAt
  have hES : ∀ x : ℝ, 2 * η < x → x < Q γ → ExtendedSeiberg3 γ x α₂ α₃ := fun x h1 h2 =>
    extendedSeiberg3_slice hγ hγ2 ⟨hη0, hηQ⟩ hα₂ hα₃ (by
      have : max (α₂ - α₃) (α₃ - α₂) < η := max_lt (by linarith [hα₂.2, hα₃.1])
        (by linarith [hα₂.1, hα₃.2])
      linarith) h2
  have hWab : ∀ x : ℝ, 2 * η < x → x < Q γ → (x : ℂ) ∈ W := fun x h1 h2 => by
    refine ⟨?_, ?_⟩
    · show ℓ x ∈ V₃
      rw [hℓ, tripleFirst_ofReal]
      exact hV₃mem _ (hES x h1 h2)
    · show 0 < (sExpC γ (ℓ x)).re
      rw [hℓ, tripleFirst_ofReal, sExpC_complexify, Complex.ofReal_re]
      unfold sExp
      exact div_pos (by simp; linarith [hα₂.1, hα₃.1]) hγ
  have hgv : ∀ x : ℝ, 2 * η < x → x < Q γ → g x = (structureConstant P M γ μ x α₂ α₃ : ℂ) :=
    fun x h1 h2 => by
      simp only [hg, hℓ]
      rw [tripleFirst_ofReal]
      exact structureConstantH_complexify P M hμ ![x, α₂, α₃] (hf₃eq ![x, α₂, α₃] (hES x h1 h2))
  -- the shift coefficient and the multiplier
  set A : ℂ → ℂ := fun z => shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) with hA
  have hAm : MeromorphicOn A univ := meromorphicOn_shiftCoeffA γ _ _ _
  have hAne : ∀ᶠ z in codiscrete ℂ, A z ≠ 0 :=
    eventually_shiftCoeffA_ne_zero γ _ _ (div_ne_zero hγc two_ne_zero)
      (lFun_ne_zero (fun n => by
        have h := ofReal_ne_neg_nat_of_mem (r := -(γ / 2) ^ 2) (Or.inl
          ⟨by linarith only [mul_lt_mul'' hγ2 hγ2 hγ.le hγ.le], by
          linarith only [sq_pos_of_pos hγ]⟩) n
        intro hn
        apply h
        rw [← hn]
        push_cast
        ring) (fun n => by
        have h := ofReal_ne_neg_nat_of_mem (r := 1 + (γ / 2) ^ 2)
          (Or.inr (Or.inr ⟨by linarith only [sq_pos_of_pos hγ],
            by linarith only [mul_lt_mul'' hγ2 hγ2 hγ.le hγ.le]⟩)) n
        intro hn
        apply h
        rw [← hn]
        push_cast
        ring))
  -- a window where `𝒜(· - γ/2)` is analytic and nonzero
  set x₀ : ℝ := (γ + 2 * η + Q γ) / 2 with hx₀
  obtain ⟨u, ⟨hu1, hu2⟩, hu3⟩ : ∃ u : ℝ, (AnalyticAt ℂ A (((x₀ + u : ℝ) : ℂ) - γ / 2) ∧
      A (((x₀ + u : ℝ) : ℂ) - γ / 2) ≠ 0) ∧ u ∈ Ioo (-((Q γ - γ - 2 * η) / 4))
        ((Q γ - γ - 2 * η) / 4) := by
    have e1 := eventually_ofReal_affine (x₀ := x₀ - γ / 2) (s := 1) one_ne_zero
      (hAm (((x₀ - γ / 2 : ℝ) : ℂ)) (mem_univ _)).eventually_analyticAt
    have e2 := eventually_ofReal_affine (p := fun z => A z ≠ 0) (x₀ := x₀ - γ / 2) (s := 1)
      one_ne_zero ((eventually_codiscrete_iff_forall_eventually_nhdsNE.mp hAne) _)
    have hI : Ioo (-((Q γ - γ - 2 * η) / 4)) ((Q γ - γ - 2 * η) / 4) ∈ 𝓝 (0 : ℝ) :=
      Ioo_mem_nhds (by linarith) (by linarith)
    obtain ⟨u, ⟨h1, h2⟩, h3⟩ := ((e1.and e2).and (nhdsWithin_le_nhds hI)).exists
    have e : (((x₀ - γ / 2 + u * 1 : ℝ) : ℂ)) = ((x₀ + u : ℝ) : ℂ) - γ / 2 := by
      push_cast; ring
    rw [e] at h1 h2
    exact ⟨u, ⟨h1, h2⟩, h3⟩
  set x₁ : ℝ := x₀ + u with hx₁
  have hx₁a : γ + 2 * η < x₁ := by rw [hx₁, hx₀]; linarith [hu3.1]
  have hx₁b : x₁ < Q γ := by rw [hx₁, hx₀]; linarith [hu3.2]
  have hloc : ∀ᶠ x : ℝ in 𝓝 x₁, AnalyticAt ℂ A ((x : ℂ) - γ / 2) ∧ A ((x : ℂ) - γ / 2) ≠ 0 := by
    have hc : ContinuousAt (fun x : ℝ => (x : ℂ) - γ / 2) x₁ := by fun_prop
    have h1 := eventually_analyticAt_comp (φ := fun x : ℝ => (x : ℂ) - γ / 2) hc hu1
    have h2 : ∀ᶠ x : ℝ in 𝓝 x₁, A ((x : ℂ) - γ / 2) ≠ 0 :=
      (ContinuousAt.comp (f := fun x : ℝ => (x : ℂ) - γ / 2) (x := x₁) hu1.continuousAt
        hc).eventually_ne hu2
    exact h1.and h2
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff.mp hloc
  set d₁ : ℝ := max (x₁ - δ / 2) (γ + 2 * η) with hd₁
  set d₂ : ℝ := min (x₁ + δ / 2) (Q γ) with hd₂
  have hd₁₂ : d₁ < d₂ := max_lt (lt_min (by linarith) (by linarith)) (lt_min (by linarith)
    (by linarith))
  have hd₁a : 2 * η + γ ≤ d₁ := by rw [hd₁]; linarith [le_max_right (x₁ - δ / 2) (γ + 2 * η)]
  have hd₂b : d₂ ≤ Q γ := min_le_right _ _
  -- the multiplier and the real relation
  set m : ℂ → ℂ := fun z => -((Real.pi : ℂ) * μ) * (A (z - γ / 2))⁻¹ with hm
  have hmm : MeromorphicOn m univ := fun z _ =>
    (MeromorphicAt.const _ z).fun_mul ((hAm (z - γ / 2) (mem_univ _)).comp_analyticAt
      (g := fun w : ℂ => w - γ / 2) (by fun_prop)).inv
  have hm0 : ∃ z₀ : ℂ, AnalyticAt ℂ m z₀ ∧ m z₀ ≠ 0 := by
    refine ⟨(x₁ : ℂ), ?_, ?_⟩
    · have ha : AnalyticAt ℂ (fun z : ℂ => A (z - γ / 2)) (x₁ : ℂ) :=
        AnalyticAt.comp_of_eq (g := A) (f := fun z : ℂ => z - γ / 2) hu1 (by fun_prop) rfl
      exact analyticAt_const.mul (ha.inv hu2)
    · simp only [hm]
      exact mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero hπc hμc)) (inv_ne_zero hu2)
  have hrel : ∀ x : ℝ, d₁ < x → x < d₂ → g ((x : ℂ) - (γ : ℂ)) = m x * g x := by
    intro x h1 h2
    have hxa : γ + 2 * η < x := lt_of_le_of_lt (le_max_right _ _) h1
    have hxb : x < Q γ := lt_of_lt_of_le h2 (min_le_right _ _)
    have hxδ : dist x x₁ < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor
      · linarith [le_max_left (x₁ - δ / 2) (γ + 2 * η)]
      · linarith [min_le_left (x₁ + δ / 2) (Q γ)]
    have hAx := (hδball hxδ).2
    have hl1 : γ / 2 < x - γ / 2 := by linarith
    have hl2 : x - γ / 2 < 2 / γ := by linarith
    have hls : 2 * Q γ + γ / 2 < x - γ / 2 + α₂ + α₃ := by linarith [hα₂.1, hα₃.1]
    have hseed := firstShift_real_of_unreflected P X M (α₁ := x - γ / 2) (α₂ := α₂) (α₃ := α₃)
      hγ hγ2 hμ hX hM (fun hH => hUnreflectedFormula hH (x - γ / 2) α₂ α₃ hl1 hl2 hα₂.2 hα₃.2 hls) hl1 hl2
      hα₂.2 hα₃.2 hls
    rw [show x - γ / 2 + γ / 2 = x by ring, show x - γ / 2 - γ / 2 = x - γ by ring,
      show ((x - γ / 2 : ℝ) : ℂ) = (x : ℂ) - γ / 2 by push_cast; ring] at hseed
    rw [show (x : ℂ) - (γ : ℂ) = ((x - γ : ℝ) : ℂ) by push_cast; ring,
      hgv (x - γ) (by linarith) (by linarith), hgv x (by linarith) hxb]
    simp only [hm]
    change A ((x : ℂ) - γ / 2) ≠ 0 at hAx
    rw [hseed]
    simp only [hA] at hAx ⊢
    generalize shiftCoeffA γ (γ / 2) ((x : ℂ) - γ / 2) (α₂ : ℂ) (α₃ : ℂ) = a at hAx ⊢
    field_simp
  -- the strip continuation
  obtain ⟨h, hh, G, hGm, hGg, hGrel⟩ := exists_meromorphicOn_strip_of_shift (c := γ) (a := 2 * η)
    (b := Q γ) hγ (by linarith) hd₁a hd₁₂ hd₂b hWo hWab hgd hmm hm0 hrel
  -- the first shift near every point of the strip
  have hrel' : ∀ w ∈ horizontalStrip h, ∀ᶠ z in 𝓝[≠] w,
      G (z + ((γ / 2 : ℝ) : ℂ)) = (fun z => -(1 / (Real.pi * μ)) * A z) z *
        G (z + ((-(γ / 2) : ℝ) : ℂ)) := by
    intro w hw
    have hw' : w + ((γ / 2 : ℝ) : ℂ) ∈ horizontalStrip h := add_ofReal_mem_horizontalStrip_glue hw _
    have h1 := ShiftGluing.eventually_comp_add (z := w) ((γ / 2 : ℝ) : ℂ) (hGrel _ hw')
    have h2 := (eventually_codiscrete_iff_forall_eventually_nhdsNE.mp hAne) w
    filter_upwards [h1, h2] with z hz hAz
    have e1 : z + ((γ / 2 : ℝ) : ℂ) - (γ : ℂ) = z + ((-(γ / 2) : ℝ) : ℂ) := by push_cast; ring
    have e2 : z + ((γ / 2 : ℝ) : ℂ) - (γ : ℂ) / 2 = z := by push_cast; ring
    rw [e1] at hz
    simp only [hm, e2] at hz
    rw [hz]
    field_simp
  have hcut := cutoff_relation_codiscrete hh (γ / 2) (-(γ / 2)) hrel'
  refine ⟨h / 2, half_pos hh, cutoffStrip (h / 2) G,
    meromorphicOn_cutoffStrip hGm (half_le_self hh.le), fun α h1 h2 => ?_, ?_⟩
  · rw [cutoffStrip_of_lt (by simp only [Complex.ofReal_im, abs_zero]; positivity), hGg α h1 h2]
    exact hgv α h1 h2
  · filter_upwards [hcut] with z hz
    simp only [hA] at hz
    convert hz using 2 <;> push_cast <;> ring_nf

end DOZZ.Proofs

end
