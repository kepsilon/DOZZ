/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Continuity.FourPoint
public import DOZZ.Statements.Defs.StructureConstant
import DOZZ.GMC.Moments.RhoCoulomb
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-! # Continuity of the structure constant in `γ`

The structure constant is `2 μ^{-s} γ⁻¹ Γ(s) E[ρ^{-s}]` with `s = (α₁ + α₂ + α₃ - 2Q)/γ`.
Fix `γ₀ ∈ (0, 2)` with `s > 0` and every charge below `Q` at `γ₀`. All of these are open
conditions, so they hold on a compact neighbourhood `K₀` of `γ₀`. On `K₀`, the moment `E[ρ^{-s}]`
is the four-point Coulomb moment at the parameters `(γ, (0, α₁(γ), α₂, α₃))`:

* a vanishing charge contributes the factor `x ^ 0 = 1` to the Coulomb weight;
* `ρ` is the two-root Coulomb mass almost surely, since the GMC has no atoms at the roots;
* the four-point Seiberg exponent with a vanishing charge is `s`.

The moment is therefore continuous on `K₀` by the joint continuity of the four-point moment in
`(γ, α)`. The prefactor `2 μ^{-s} γ⁻¹ Γ(s)` is continuous at `γ₀` since `s > 0` there. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- A vanishing charge at the first of three finite roots does not change the Coulomb mass: its
weight is `x ^ 0 = 1`. -/
theorem bpzSG_coulombMass_zero_first (γ : ℝ) (m : Measure ℂ) (z : ℂ) (a b c : ℝ) :
    coulombMass γ m ![0, a, b] ![z, 0, 1] c = coulombMass γ m ![a, b] ![0, 1] c := by
  unfold coulombMass
  refine lintegral_congr fun x => ?_
  simp [Fin.prod_univ_three, Fin.prod_univ_two]

/-- The four-point Seiberg exponent with a vanishing first charge is the three-point one. -/
theorem bpzSG_nPointSExp_zero_first (γ a b c : ℝ) :
    nPointSExp γ ![0, a, b, c] = sExp γ a b c := by
  simp [nPointSExp, sExp, Fin.sum_univ_four]

/-- For `γ ∈ (0, 2)`, the moment of `rho` is the four-point Coulomb moment with a vanishing
charge at the root `z`. -/
theorem bpzSG_moment_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (M : Ω → Measure ℂ) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hM : IsGMCOf P X γ M) (z : ℂ) (a b c : ℝ) :
    (∫⁻ ω, rho γ (M ω) a b c ^ (-sExp γ a b c) ∂P) =
      ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) ![0, a, b] ![z, 0, 1] c)
        (-nPointSExp γ ![0, a, b, c]) ∂P := by
  refine lintegral_congr_ae ?_
  filter_upwards [gmc_rho_eq_coulombMass_ae P X hX γ hγ hγ2 M hM a b c] with ω hω
  rw [hω, bpzSG_coulombMass_zero_first, bpzSG_nPointSExp_zero_first]
  rfl

/-- The Seiberg exponent is continuous in `γ` for a continuously varying first charge. -/
theorem bpzSG_continuousAt_sExp {f : ℝ → ℝ} (hf : Continuous f) (α₂ α₃ : ℝ) {γ₀ : ℝ}
    (hγ₀ : γ₀ ≠ 0) : ContinuousAt (fun γ => sExp γ (f γ) α₂ α₃) γ₀ := by
  have hQ : ContinuousAt Q γ₀ := by
    unfold Q
    exact (continuousAt_const.div continuousAt_id hγ₀).add (continuousAt_id.div_const 2)
  unfold sExp
  exact (((hf.continuousAt.add continuousAt_const).add continuousAt_const).sub
    (continuousAt_const.mul hQ)).div continuousAt_id hγ₀

/-- The admissibility conditions at `γ₀` hold on a neighbourhood of `γ₀`. -/
theorem bpzSG_domain_nhds {f : ℝ → ℝ} (hf : Continuous f) (α₂ α₃ : ℝ) {γ₀ : ℝ}
    (hγ₀ : γ₀ ∈ Ioo (0 : ℝ) 2) (h1 : f γ₀ < Q γ₀) (h2 : α₂ < Q γ₀) (h3 : α₃ < Q γ₀)
    (hs : 0 < sExp γ₀ (f γ₀) α₂ α₃) :
    ∀ᶠ γ in 𝓝 γ₀, γ ∈ Ioo (0 : ℝ) 2 ∧ f γ < Q γ ∧ α₂ < Q γ ∧ α₃ < Q γ ∧
      0 < sExp γ (f γ) α₂ α₃ := by
  have hQ : ContinuousAt Q γ₀ := by
    unfold Q
    exact (continuousAt_const.div continuousAt_id hγ₀.1.ne').add (continuousAt_id.div_const 2)
  filter_upwards [Ioo_mem_nhds hγ₀.1 hγ₀.2, hf.continuousAt.eventually_lt hQ h1,
    continuousAt_const.eventually_lt hQ h2, continuousAt_const.eventually_lt hQ h3,
    continuousAt_const.eventually_lt (bpzSG_continuousAt_sExp hf α₂ α₃ hγ₀.1.ne') hs] with
    γ hγ hf' h2' h3' hs'
  exact ⟨hγ, hf', h2', h3', hs'⟩

/-- The four-point charges `(0, a, b, c)` lie in the extended Seiberg domain when all charges are
below `Q` and the Seiberg exponent is positive. -/
theorem bpzSG_extendedSeiberg {γ a b c : ℝ} (hγ : 0 < γ) (ha : a < Q γ) (hb : b < Q γ)
    (hc : c < Q γ) (hs : 0 < sExp γ a b c) : ExtendedSeibergN γ ![0, a, b, c] := by
  have hQ : 0 < Q γ := by
    unfold Q
    positivity
  have hlt : ∀ i, (![0, a, b, c] : Fin 4 → ℝ) i < Q γ := by
    intro i
    fin_cases i
    · exact hQ
    · exact ha
    · exact hb
    · exact hc
  have hns : -nPointSExp γ ![0, a, b, c] < 0 := by
    rw [bpzSG_nPointSExp_zero_first]
    linarith
  refine ⟨hlt, hns.trans (by positivity), fun i => hns.trans ?_⟩
  exact mul_pos (div_pos two_pos hγ) (sub_pos.mpr (hlt i))

/-- The prefactor `2 μ^{-s} γ⁻¹ Γ(s)` is continuous at `γ₀` where `s > 0`. -/
theorem bpzSG_continuousAt_prefactor {μ : ℝ} (hμ : 0 < μ) {f : ℝ → ℝ} (hf : Continuous f)
    (α₂ α₃ : ℝ) {γ₀ : ℝ} (hγ₀ : γ₀ ≠ 0) (hs : 0 < sExp γ₀ (f γ₀) α₂ α₃) :
    ContinuousAt (fun γ => 2 * μ ^ (-sExp γ (f γ) α₂ α₃) / γ *
      Real.Gamma (sExp γ (f γ) α₂ α₃)) γ₀ := by
  have hsc := bpzSG_continuousAt_sExp hf α₂ α₃ hγ₀
  have hpow : ContinuousAt (fun γ => μ ^ (-sExp γ (f γ) α₂ α₃)) γ₀ :=
    ContinuousAt.rpow continuousAt_const hsc.neg (Or.inl hμ.ne')
  have hG : ContinuousAt Real.Gamma (sExp γ₀ (f γ₀) α₂ α₃) :=
    (Real.differentiableOn_Gamma_Ioi.differentiableAt (Ioi_mem_nhds hs)).continuousAt
  exact ((continuousAt_const.mul hpow).div continuousAt_id hγ₀).mul
    (ContinuousAt.comp (f := fun γ => sExp γ (f γ) α₂ α₃) hG hsc)

/-- Along a family of GMC measures, the structure constant with a continuously varying first
charge is continuous in `γ`. -/
theorem bpz_continuousAt_structureConstant_gamma {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (Mfam : ℝ → Ω → Measure ℂ)
    (hMfam : ∀ γ' ∈ Ioo (0 : ℝ) 2, IsGMCOf P X γ' (Mfam γ')) (μ : ℝ) (hμ : 0 < μ)
    {f : ℝ → ℝ} (hf : Continuous f) (α₂ α₃ : ℝ) {γ₀ : ℝ} (hγ₀ : γ₀ ∈ Ioo (0 : ℝ) 2)
    (h1 : f γ₀ < Q γ₀) (h2 : α₂ < Q γ₀) (h3 : α₃ < Q γ₀) (hs : 0 < sExp γ₀ (f γ₀) α₂ α₃) :
    ContinuousAt (fun γ' => structureConstant P (Mfam γ') γ' μ (f γ') α₂ α₃) γ₀ := by
  obtain ⟨K₀, hK₀nhds, hK₀sub, hK₀cpt⟩ :=
    local_compact_nhds (bpzSG_domain_nhds hf α₂ α₃ hγ₀ h1 h2 h3 hs)
  let J : ℝ → ℝ × (Fin 4 → ℝ) := fun γ => (γ, ![0, f γ, α₂, α₃])
  have hJ : Continuous J := by
    unfold J
    fun_prop
  have hKdom : ∀ q ∈ J '' K₀, 0 < q.1 ∧ q.1 < 2 ∧ ExtendedSeibergN q.1 q.2 := by
    rintro _ ⟨γ, hγ, rfl⟩
    obtain ⟨hγ', hf', h2', h3', hs'⟩ := hK₀sub hγ
    exact ⟨hγ'.1, hγ'.2, bpzSG_extendedSeiberg hγ'.1 hf' h2' h3' hs'⟩
  have hM : ∀ q ∈ J '' K₀, IsGMCOf P X q.1 (Mfam q.1) := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact hMfam γ (hK₀sub hγ).1
  have hcont := fourPointMoment_jointly_continuous_parameters P X Mfam 2
    ⟨two_ne_zero, by norm_num⟩ (J '' K₀) (hK₀cpt.image hJ) hKdom hX hM
  have hat := (hcont.comp hJ.continuousOn (mapsTo_image J K₀)).continuousAt hK₀nhds
  have hmom : ContinuousAt (fun γ => (∫⁻ ω, rho γ (Mfam γ ω) (f γ) α₂ α₃ ^
      (-sExp γ (f γ) α₂ α₃) ∂P).toReal) γ₀ := by
    refine hat.congr ?_
    filter_upwards [hK₀nhds] with γ hγ
    obtain ⟨hγ', -⟩ := hK₀sub hγ
    simp only [Function.comp_apply, J]
    rw [bpzSG_moment_eq P X hX (Mfam γ) hγ'.1 hγ'.2 (hMfam γ hγ') 2 (f γ) α₂ α₃]
    rfl
  exact (bpzSG_continuousAt_prefactor hμ hf α₂ α₃ hγ₀.1.ne' hs).mul hmom

end DOZZ.Proofs
