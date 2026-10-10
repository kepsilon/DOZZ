/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.DOZZAlgebra.GenericLocus
import DOZZ.DOZZAlgebra.FormulaReflection
import DOZZ.Upsilon.ZeroStructure
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The three-to-two DOZZ limit
-/

@[expose] public section

open Complex Filter Set Topology

namespace DOZZ.Proofs

variable {γ : ℝ}

private lemma bridge_real_mul_cpow {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (z : ℂ) :
    ((a * b ^ r : ℝ) : ℂ) ^ z =
      (a : ℂ) ^ z * (b : ℂ) ^ ((r : ℂ) * z) := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ha (Real.rpow_nonneg hb r)]
  have hlog : Complex.log (b : ℂ) = (Real.log b : ℂ) := (Complex.ofReal_log hb).symm
  have him : (Complex.log (b : ℂ) * (r : ℂ)).im = 0 := by
    rw [hlog]
    simp
  have h₁ : -Real.pi < (Complex.log (b : ℂ) * (r : ℂ)).im := by
    rw [him]
    linarith [Real.pi_pos]
  have h₂ : (Complex.log (b : ℂ) * (r : ℂ)).im ≤ Real.pi := by
    rw [him]
    exact le_of_lt Real.pi_pos
  rw [Complex.ofReal_cpow hb r, ← Complex.cpow_mul z h₁ h₂]

/-- The field identity behind the residue factorization in `dozzFormula_bridge`, over abstract
complex numbers so that `field_simp` never sees the special functions. -/
private lemma dozzFormula_bridge_algebra {x d u a b v₀ v₂ ε : ℂ} (hε : ε ≠ 0) (hv₀ : v₀ ≠ 0)
    (hv₂ : v₂ ≠ 0) (hb : b ≠ 0) :
    ε * (x * (d * u * (ε * a) * u) / (v₀ * (ε / 2 * b) * v₂ * (ε / 2 * b))) =
      4 * x * d * u * u * a / (v₀ * v₂ * b * b) := by
  field_simp
  ring

/-- The three-to-two bridge follows by factoring the simple zero at the
origin and applying the two shift equations. -/
theorem dozzFormula_bridge {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {μ : ℝ} (hμ : 0 < μ) (hU : IsUpsilon γ U) :
    ∀ᶠ α in codiscrete ℂ,
      Tendsto (fun ε : ℂ => ε * dozzFormula γ μ U α ε α) (𝓝[≠] 0)
        (𝓝 (4 * reflectionDOZZ γ μ α)) := by
  let b : ℂ := (γ : ℂ) / 2
  let c : ℂ := 2 / (γ : ℂ)
  let T : ℝ := dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2)
  have hTpos : 0 < T := by
    dsimp [T]
    exact mul_pos (dozzBase_pos hγ hγ2 hμ)
      (Real.rpow_pos_of_pos (div_pos hγ (by norm_num)) _)
  let d : ℂ := deriv U 0
  have hUzero : U 0 = 0 := by
    apply (IsUpsilon.eq_zero_iff hγ hγ2 hU 0).2
    exact ⟨0, 0, Or.inl (by simp)⟩
  have hderiv : HasDerivAt U d 0 := by
    exact (hU.1 0).hasDerivAt
  have hquot : Tendsto (fun z : ℂ => U z / z) (𝓝[≠] (0 : ℂ)) (𝓝 d) := by
    apply (tendsto_congr' ?_).mpr hderiv.tendsto_slope_zero
    filter_upwards [self_mem_nhdsWithin] with z _
    simp [hUzero, div_eq_mul_inv, mul_comm]
  have hUbne : U ((γ : ℂ) / 2) ≠ 0 := by
    have hbpos : 0 < γ / 2 := div_pos hγ (by norm_num)
    have hbQ : γ / 2 < Q γ := by
      unfold Q
      have hpos : 0 < 2 / γ := div_pos (by norm_num) hγ
      linarith
    have hre : 0 < (((γ / 2 : ℝ) : ℂ).re) := by simpa using hbpos
    have hreQ : (((γ / 2 : ℝ) : ℂ).re) < Q γ := by simpa using hbQ
    have hreal : U ((γ / 2 : ℝ) : ℂ) ≠ 0 := by
      rw [hU.2 _ hre hreQ]
      exact Complex.exp_ne_zero _
    have hcast : ((γ / 2 : ℝ) : ℂ) = (γ : ℂ) / 2 := by
      exact Complex.ofReal_div γ 2
    rw [← hcast]
    exact hreal
  have hdne : d ≠ 0 := by
    dsimp [d]
    rw [IsUpsilon.deriv_zero hγ hγ2 hU]
    exact hUbne
  have hhalfArg : Tendsto (fun ε : ℂ => ε / 2)
      (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : ContinuousAt (fun ε : ℂ => ε / 2) 0 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : ε ≠ 0 := by simpa using hε
      exact div_ne_zero hε0 (by norm_num)
  have hhalfquot : Tendsto (fun ε : ℂ => U (ε / 2) / (ε / 2))
      (𝓝[≠] (0 : ℂ)) (𝓝 d) := hquot.comp hhalfArg

  have hUα := eventually_upsilon_affine_ne_zero hγ hU (c := 1) (d := 0) (by norm_num)
  have hUαQ := eventually_upsilon_affine_ne_zero hγ hU (c := 1)
    (d := -(Q γ : ℂ)) (by norm_num)
  have hshift := eventually_upsilon_shift_Q hγ hγ2 hU
  filter_upwards [hUα, hUαQ, hshift] with α hUα hUαQ hshift
  have hUα' : U α ≠ 0 := by simpa using hUα
  have hUαQ' : U (α - Q γ) ≠ 0 := by
    have harg : α - Q γ = (1 : ℂ) * α + -(Q γ : ℂ) := by ring
    rw [harg]
    exact hUαQ
  let q : ℂ := 2 * ((Q γ : ℂ) - α) / (γ : ℂ)
  let e : ℂ := (γ : ℂ) * ((Q γ : ℂ) - α) - (4 / (γ : ℂ)) * ((Q γ : ℂ) - α)
  let g₁ : ℂ := Complex.Gamma (-((γ : ℂ) * ((Q γ : ℂ) - α) / 2)) /
    Complex.Gamma ((γ : ℂ) * ((Q γ : ℂ) - α) / 2)
  let g₂ : ℂ := Complex.Gamma (-(2 * ((Q γ : ℂ) - α) / (γ : ℂ))) /
    Complex.Gamma (2 * ((Q γ : ℂ) - α) / (γ : ℂ))
  let K : ℂ := -b ^ e * g₁ * g₂
  have hshift' : U α = K * U (α - Q γ) := by
    simpa [K, g₁, g₂, b, e] using hshift

  have hTsplit : ((T : ℝ) : ℂ) ^ q =
      ((dozzBase γ μ : ℝ) : ℂ) ^ q * b ^ (((2 - γ ^ 2 / 2 : ℝ) : ℂ) * q) := by
    have h := bridge_real_mul_cpow (a := dozzBase γ μ) (b := γ / 2)
      (r := 2 - γ ^ 2 / 2) (z := q) (le_of_lt (dozzBase_pos hγ hγ2 hμ)) (by positivity)
    simpa [T, b, Complex.ofReal_mul] using h
  have hqe : (((2 - γ ^ 2 / 2 : ℝ) : ℂ) * q) + e = 0 := by
    dsimp [q, e]
    unfold Q
    push_cast
    field_simp [hγ.ne']
    ring
  have hpowCancel : ((T : ℝ) : ℂ) ^ q * b ^ e =
      ((dozzBase γ μ : ℝ) : ℂ) ^ q := by
    rw [hTsplit, show b = ((γ / 2 : ℝ) : ℂ) by dsimp [b]; push_cast; ring]
    calc
      ((dozzBase γ μ : ℝ) : ℂ) ^ q *
          ((γ / 2 : ℝ) : ℂ) ^ (((2 - γ ^ 2 / 2 : ℝ) : ℂ) * q) *
            ((γ / 2 : ℝ) : ℂ) ^ e =
        ((dozzBase γ μ : ℝ) : ℂ) ^ q *
          ((γ / 2 : ℝ) : ℂ) ^ ((((2 - γ ^ 2 / 2 : ℝ) : ℂ) * q) + e) := by
            have hbne : ((γ / 2 : ℝ) : ℂ) ≠ 0 :=
              Complex.ofReal_ne_zero.mpr (by positivity)
            calc
              _ = ((dozzBase γ μ : ℝ) : ℂ) ^ q *
                  (((γ / 2 : ℝ) : ℂ) ^ (((2 - γ ^ 2 / 2 : ℝ) : ℂ) * q) *
                    ((γ / 2 : ℝ) : ℂ) ^ e) := by ring
              _ = _ := by rw [(Complex.cpow_add _ _ hbne).symm]
      _ = ((dozzBase γ μ : ℝ) : ℂ) ^ q := by rw [hqe]; simp
  have hcoef : ((T : ℝ) : ℂ) ^ q * K = reflectionDOZZ γ μ α := by
    calc
      ((T : ℝ) : ℂ) ^ q * K = -(((T : ℝ) : ℂ) ^ q * b ^ e) * g₁ * g₂ := by
        dsimp [K]
        ring
      _ = -(((dozzBase γ μ : ℝ) : ℂ) ^ q) * g₁ * g₂ := by rw [hpowCancel]
      _ = reflectionDOZZ γ μ α := by
        unfold reflectionDOZZ
        rfl

  let A : ℂ → ℂ := fun ε => U ε / ε
  let B : ℂ → ℂ := fun ε => U (ε / 2) / (ε / 2)
  let V₀ : ℂ → ℂ := fun ε => U (α - Q γ + ε / 2)
  let V₂ : ℂ → ℂ := fun ε => U (α - ε / 2)
  let P : ℂ → ℂ := fun ε =>
    ((T : ℝ) : ℂ) ^ ((2 * Q γ - (α + ε + α)) / γ)
  let N : ℂ → ℂ := fun ε => 4 * P ε * d * U α * U α * A ε
  let D : ℂ → ℂ := fun ε => V₀ ε * V₂ ε * B ε * B ε
  have hPexp : Tendsto (fun ε : ℂ => (2 * Q γ - (α + ε + α)) / γ)
      (𝓝[≠] (0 : ℂ)) (𝓝 q) := by
    have hc : ContinuousAt (fun ε : ℂ => (2 * Q γ - (α + ε + α)) / γ) 0 := by fun_prop
    have hEval : (2 * (Q γ : ℂ) - (α + α)) / (γ : ℂ) = q := by
      dsimp [q]
      ring
    simpa only [add_zero, hEval] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hTslit : ((T : ℝ) : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.2 hTpos
  have hP : Tendsto P (𝓝[≠] (0 : ℂ)) (𝓝 (((T : ℝ) : ℂ) ^ q)) := by
    simpa [P] using tendsto_const_nhds.cpow hPexp hTslit
  have hA : Tendsto A (𝓝[≠] (0 : ℂ)) (𝓝 d) := by simpa [A] using hquot
  have hB : Tendsto B (𝓝[≠] (0 : ℂ)) (𝓝 d) := by simpa [B] using hhalfquot
  have hv₀arg : Tendsto (fun ε : ℂ => α - Q γ + ε / 2)
      (𝓝[≠] (0 : ℂ)) (𝓝 (α - Q γ)) := by
    have hc : ContinuousAt (fun ε : ℂ => α - Q γ + ε / 2) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hv₂arg : Tendsto (fun ε : ℂ => α - ε / 2)
      (𝓝[≠] (0 : ℂ)) (𝓝 α) := by
    have hc : ContinuousAt (fun ε : ℂ => α - ε / 2) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hV₀ : Tendsto V₀ (𝓝[≠] (0 : ℂ)) (𝓝 (U (α - Q γ))) := by
    simpa [V₀, Function.comp_def] using (hU.1 (α - Q γ)).continuousAt.tendsto.comp hv₀arg
  have hV₂ : Tendsto V₂ (𝓝[≠] (0 : ℂ)) (𝓝 (U α)) := by
    simpa [V₂, Function.comp_def] using (hU.1 α).continuousAt.tendsto.comp hv₂arg
  have hV₀ne := hV₀.eventually_ne hUαQ'
  have hV₂ne := hV₂.eventually_ne hUα'
  have hBne := hB.eventually_ne hdne
  have hN : Tendsto N (𝓝[≠] (0 : ℂ))
      (𝓝 (4 * ((T : ℝ) : ℂ) ^ q * d * U α * U α * d)) := by
    have h₁ : Tendsto (fun ε : ℂ => (4 : ℂ) * P ε)
        (𝓝[≠] (0 : ℂ)) (𝓝 ((4 : ℂ) * ((T : ℝ) : ℂ) ^ q)) :=
      tendsto_const_nhds.mul hP
    have h₂ : Tendsto (fun ε : ℂ => ((4 : ℂ) * P ε) * d)
        (𝓝[≠] (0 : ℂ)) (𝓝 ((4 : ℂ) * ((T : ℝ) : ℂ) ^ q * d)) :=
      h₁.mul tendsto_const_nhds
    have h₃ : Tendsto (fun ε : ℂ => (((4 : ℂ) * P ε) * d) * U α)
        (𝓝[≠] (0 : ℂ)) (𝓝 ((4 : ℂ) * ((T : ℝ) : ℂ) ^ q * d * U α)) :=
      h₂.mul tendsto_const_nhds
    have h₄ : Tendsto (fun ε : ℂ => ((((4 : ℂ) * P ε) * d) * U α) * U α)
        (𝓝[≠] (0 : ℂ)) (𝓝 ((4 : ℂ) * ((T : ℝ) : ℂ) ^ q * d * U α * U α)) :=
      h₃.mul tendsto_const_nhds
    have h₅ : Tendsto (fun ε : ℂ => (((((4 : ℂ) * P ε) * d) * U α) * U α) * A ε)
        (𝓝[≠] (0 : ℂ)) (𝓝 ((4 : ℂ) * ((T : ℝ) : ℂ) ^ q * d * U α * U α * d)) :=
      h₄.mul hA
    simpa [N, mul_assoc] using h₅
  have hD : Tendsto D (𝓝[≠] (0 : ℂ))
      (𝓝 (U (α - Q γ) * U α * d * d)) := by
    have h₁ := hV₀.mul hV₂
    have h₂ := h₁.mul hB
    have h₃ := h₂.mul hB
    simpa [D, mul_assoc] using h₃
  have hDne : U (α - Q γ) * U α * d * d ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hUαQ' hUα') hdne) hdne
  have hfactor : ∀ᶠ ε : ℂ in 𝓝[≠] (0 : ℂ),
      ε * dozzFormula γ μ U α ε α = N ε / D ε := by
    filter_upwards [self_mem_nhdsWithin, hV₀ne, hV₂ne, hBne]
      with ε hε hV₀ne hV₂ne hBne
    have hε0 : ε ≠ 0 := by simpa using hε
    have hhalfne : ε / 2 ≠ 0 := div_ne_zero hε0 (by norm_num)
    have hUε : U ε = ε * A ε := by
      dsimp [A]
      field_simp [hε0]
    have hUhalf : U (ε / 2) = (ε / 2) * B ε := by
      dsimp [B]
      field_simp [hhalfne]
    have harg₀ : (α + ε + α - 2 * Q γ) / 2 = α - Q γ + ε / 2 := by ring
    have harg₁ : (α + ε + α) / 2 - α = ε / 2 := by ring
    have harg₂ : (α + ε + α) / 2 - ε = α - ε / 2 := by ring
    unfold dozzFormula
    rw [harg₀, harg₁, harg₂, hUε, hUhalf]
    exact dozzFormula_bridge_algebra hε0 hV₀ne hV₂ne hBne
  have hlimit := hN.div hD hDne
  have hlimit_eq :
      (4 * ((T : ℝ) : ℂ) ^ q * d * U α * U α * d) /
          (U (α - Q γ) * U α * d * d) = 4 * reflectionDOZZ γ μ α := by
    have hKne : K ≠ 0 := by
      intro hK
      apply hUα'
      rw [hshift', hK]
      simp
    calc
      _ = 4 * (((T : ℝ) : ℂ) ^ q * K) := by
        rw [hshift']
        field_simp [hUαQ', hUα', hdne, hKne]
      _ = _ := by rw [hcoef]
  have hlimit' : Tendsto (fun ε : ℂ => N ε / D ε) (𝓝[≠] (0 : ℂ))
      (𝓝 (4 * reflectionDOZZ γ μ α)) := by
    rw [← hlimit_eq]
    exact hlimit
  exact (tendsto_congr' hfactor).mpr hlimit'

end DOZZ.Proofs

end
