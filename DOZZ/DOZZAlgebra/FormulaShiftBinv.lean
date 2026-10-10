/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.DOZZAlgebra.GenericLocus
import DOZZ.Upsilon.FullShifts
import DOZZ.Upsilon.StripIdentities
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The first DOZZ formula shift on its finite generic locus
-/

@[expose] public section

open Complex Filter Set Topology

namespace DOZZ.Proofs

variable {γ : ℝ}

/-- The DOZZ formula shift by `γ/2`, proved directly on a codiscrete finite locus. -/
theorem dozzFormula_shift_binv {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hγk : ∀ k : ℕ, 4 / γ ^ 2 ≠ (k : ℝ)) {μ : ℝ} (hμ : 0 < μ)
    (hU : IsUpsilon γ U) (α₂ α₃ : ℂ) :
    ∀ᶠ α₁ in codiscrete ℂ,
      dozzFormula γ μ U (α₁ + 2 / γ) α₂ α₃ =
        -(1 / (Real.pi * dualMu γ μ)) * shiftCoeffA γ (2 / γ) α₁ α₂ α₃ *
          dozzFormula γ μ U (α₁ - 2 / γ) α₂ α₃ := by
  let c : ℂ := (2 / γ : ℝ)
  let s : ℂ := (γ / 2 : ℝ)
  let d₀ : ℂ := (α₂ + α₃ - c - 2 * (Q γ : ℂ)) / 2
  let d₁ : ℂ := (α₂ + α₃ - c) / 2
  let d₂ : ℂ := (-α₂ + α₃ - c) / 2
  let d₃ : ℂ := (α₂ - α₃ - c) / 2
  let v₀ : ℂ → ℂ := fun α => (1 / 2 : ℂ) * α + d₀
  let v₁ : ℂ → ℂ := fun α => (-1 / 2 : ℂ) * α + d₁
  let v₂ : ℂ → ℂ := fun α => (1 / 2 : ℂ) * α + d₂
  let v₃ : ℂ → ℂ := fun α => (1 / 2 : ℂ) * α + d₃
  let v₀p : ℂ → ℂ := fun α => (1 / 2 : ℂ) * α + (d₀ + c)
  let v₁p : ℂ → ℂ := fun α => (-1 / 2 : ℂ) * α + (d₁ + c)
  let v₂p : ℂ → ℂ := fun α => (1 / 2 : ℂ) * α + (d₂ + c)
  let v₃p : ℂ → ℂ := fun α => (1 / 2 : ℂ) * α + (d₃ + c)
  let k : ℂ → ℂ := fun z => lFun (c * z) * s ^ (4 / (γ : ℂ) * z - 1)
  let T : ℝ := dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2)
  let Tc : ℂ := (T : ℂ)
  let rR : ℝ := 4 / γ ^ 2
  let r : ℂ := (rR : ℂ)
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have hc : c ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    dsimp [c]
    exact div_ne_zero (by norm_num) hγ.ne'
  have hcCast : c = ((2 / γ : ℝ) : ℂ) := by rfl
  have hcComplex : c = (2 / (γ : ℂ)) := by
    rw [hcCast]
    norm_cast
  have hsCast : s = ((γ / 2 : ℝ) : ℂ) := rfl
  have hs : s ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    dsimp [s]
    exact div_ne_zero hγ.ne' (by norm_num)
  have hγpos : 0 < γ := hγ
  have hsR : 0 < γ / 2 := by positivity
  have hTpos : 0 < T := by
    dsimp [T]
    exact mul_pos (dozzBase_pos hγ hγ2 hμ) (Real.rpow_pos_of_pos hsR _)
  have hTc : Tc ≠ 0 := Complex.ofReal_ne_zero.mpr hTpos.ne'
  have hrpos : 0 < rR := by dsimp [rR]; positivity
  have hrCast : r = ((4 / γ ^ 2 : ℝ) : ℂ) := rfl
  have hrne : ∀ n : ℕ, rR ≠ (n : ℝ) := by
    intro n
    exact hγk n
  have hΓr : Complex.Gamma r ≠ 0 := by
    rw [hrCast, Complex.Gamma_ofReal]
    exact_mod_cast (Real.Gamma_pos_of_pos hrpos).ne'
  have hΓnegr : Complex.Gamma (-r) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have hrEq : r = (n : ℂ) := neg_inj.mp hn
    change (rR : ℂ) = (n : ℂ) at hrEq
    have : rR = (n : ℝ) := by exact_mod_cast hrEq
    exact (hrne n) this
  have hΓ1r : Complex.Gamma (1 - r) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have hreal : 1 - rR = -(n : ℝ) := by
      have hrEq : 1 - r = -(n : ℂ) := hn
      change (1 - (rR : ℂ)) = -(n : ℂ) at hrEq
      exact_mod_cast hrEq
    have : rR = ((n + 1 : ℕ) : ℝ) := by
      have hncast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_cast
      rw [hncast]
      linarith
    exact (hrne (n + 1)) this
  have hLr : lFun r ≠ 0 := by
    unfold lFun
    exact div_ne_zero hΓr hΓ1r
  have hrne0 : r ≠ 0 := by exact Complex.ofReal_ne_zero.mpr hrpos.ne'
  have hLprod := lFun_mul_neg hrne0 hΓr hΓnegr
  have hsum : rR * (2 - γ ^ 2 / 2) + 4 = 4 * Q γ / γ := by
    dsimp [rR]
    unfold Q
    field_simp [hγ.ne']
    ring
  have hbase : 0 < dozzBase γ μ := dozzBase_pos hγ hγ2 hμ
  have hbaseNe : (dozzBase γ μ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hbase.ne'
  have hTpow : Tc ^ r =
      (((dozzBase γ μ) ^ rR * (γ / 2) ^ (rR * (2 - γ ^ 2 / 2)) : ℝ) : ℂ) := by
    rw [show Tc = (T : ℂ) by rfl, show r = (rR : ℂ) by rfl,
      ← Complex.ofReal_cpow hTpos.le]
    apply congrArg (fun x : ℝ => (x : ℂ))
    dsimp [T]
    rw [Real.mul_rpow hbase.le (Real.rpow_nonneg hsR.le _)]
    rw [← Real.rpow_mul hsR.le]
    congr 1
    ring_nf
  have hbaseId : Tc ^ r * (-(lFun (-r)) / (Real.pi * dualMu γ μ)) =
      s ^ ((4 * Q γ / γ : ℝ) : ℂ) := by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hDpowC : ((dozzBase γ μ : ℝ) : ℂ) ^ r ≠ 0 := by
      apply Complex.cpow_ne_zero_iff.mpr
      exact Or.inl hbaseNe
    have hdual : dualMu γ μ =
        ((dozzBase γ μ : ℝ) : ℂ) ^ r / (Real.pi * lFun r) := by
      rfl
    have hgamma4 : (γ / 2) ^ 4 = 1 / rR ^ 2 := by
      dsimp [rR]
      field_simp [hγ.ne']
      ring
    have hprod : -(r ^ 2 * lFun (-r) * lFun r) = 1 := by
      calc
        -(r ^ 2 * lFun (-r) * lFun r) = r ^ 2 * (-(lFun r * lFun (-r))) := by ring
        _ = r ^ 2 * (1 / r ^ 2) := by rw [hLprod]; ring
        _ = 1 := by field_simp [hrne0]
    have hcoef : ((dozzBase γ μ : ℝ) : ℂ) ^ r *
        (-(lFun (-r)) / (Real.pi * dualMu γ μ)) = 1 / r ^ 2 := by
      rw [hdual]
      field_simp [hpi, hLr, hDpowC]
      rw [hprod]
    have hgamma4Real : (γ / 2) ^ (4 : ℝ) = 1 / rR ^ 2 := by
      calc
        (γ / 2) ^ (4 : ℝ) = (γ / 2) ^ (4 : ℕ) := Real.rpow_natCast _ _
        _ = 1 / rR ^ 2 := hgamma4
    have hscalarReal : (γ / 2) ^ (rR * (2 - γ ^ 2 / 2)) *
        (1 / rR ^ 2) = (γ / 2) ^ (4 * Q γ / γ) := by
      calc
        _ = (γ / 2) ^ (rR * (2 - γ ^ 2 / 2)) * (γ / 2) ^ (4 : ℝ) := by rw [← hgamma4Real]
        _ = (γ / 2) ^ (rR * (2 - γ ^ 2 / 2) + 4) := (Real.rpow_add hsR _ _).symm
        _ = (γ / 2) ^ (4 * Q γ / γ) := by rw [hsum]
    rw [hTpow]
    have hDpowCast : ((dozzBase γ μ) ^ rR : ℝ) =
        ((dozzBase γ μ : ℝ) : ℂ) ^ r := by
      rw [show r = (rR : ℂ) by rfl, Complex.ofReal_cpow hbase.le]
    have hcoefCast : 1 / r ^ 2 = ((1 / rR ^ 2 : ℝ) : ℂ) := by
      rw [hrCast]
      exact_mod_cast (show 1 / rR ^ 2 = 1 / rR ^ 2 by rfl)
    have hpowS : s ^ ((4 * Q γ / γ : ℝ) : ℂ) =
        (((γ / 2) ^ (4 * Q γ / γ) : ℝ) : ℂ) := by
      rw [hsCast, Complex.ofReal_cpow hsR.le]
    calc
      (((dozzBase γ μ) ^ rR * (γ / 2) ^ (rR * (2 - γ ^ 2 / 2)) : ℝ) : ℂ) *
          (-(lFun (-r)) / (Real.pi * dualMu γ μ)) =
          (((γ / 2) ^ (rR * (2 - γ ^ 2 / 2)) : ℝ) : ℂ) *
            (((dozzBase γ μ : ℝ) : ℂ) ^ r *
              (-(lFun (-r)) / (Real.pi * dualMu γ μ))) := by
                rw [Complex.ofReal_mul, hDpowCast]
                ring
      _ = (((γ / 2) ^ (rR * (2 - γ ^ 2 / 2)) : ℝ) : ℂ) * (1 / r ^ 2) := by
        rw [hcoef]
      _ = (((γ / 2) ^ (rR * (2 - γ ^ 2 / 2)) : ℝ) : ℂ) *
          ((1 / rR ^ 2 : ℝ) : ℂ) := by rw [hcoefCast]
      _ = (((γ / 2) ^ (rR * (2 - γ ^ 2 / 2)) * (1 / rR ^ 2) : ℝ) : ℂ) := by
        rw [Complex.ofReal_mul]
      _ = (((γ / 2) ^ (4 * Q γ / γ) : ℝ) : ℂ) := by
        exact_mod_cast hscalarReal
      _ = s ^ ((4 * Q γ / γ : ℝ) : ℂ) := hpowS.symm
  have hSexp : ((4 * Q γ / γ : ℝ) : ℂ) =
      (γ : ℂ)⁻¹ * (Q γ : ℂ) * 4 := by
    push_cast
    field_simp [hγ.ne']
  have hScpow : s ^ ((4 * Q γ / γ : ℝ) : ℂ) =
      s ^ ((γ : ℂ)⁻¹ * (Q γ : ℂ) * 4) := by
    congr 1
  let pplus : ℂ → ℂ := fun α =>
    (2 * (Q γ : ℂ) - (α + c + α₂ + α₃)) / (γ : ℂ)
  let pminus : ℂ → ℂ := fun α =>
    (2 * (Q γ : ℂ) - (α - c + α₂ + α₃)) / (γ : ℂ)
  have hexp : ∀ α : ℂ, pplus α = pminus α - r := by
    intro α
    dsimp [pplus, pminus, c, r, rR]
    push_cast
    field_simp [hγ.ne']
    ring_nf
  have hpow : ∀ α : ℂ, Tc ^ pplus α = Tc ^ pminus α / Tc ^ r := by
    intro α
    rw [hexp α, Complex.cpow_sub _ _ hTc]
  have hαm : ∀ z : ℂ, z - 2 / γ = z - c := by
    intro z
    rw [hcComplex]

  let poleA := eventually_affine_ne_neg_nat (c := c) (d := 0) hc
  let poleAm := eventually_affine_ne_neg_nat (c := c) (d := -c ^ 2) hc
  let poleV₀ := eventually_affine_ne_neg_nat (c := c / 2) (d := c * d₀) (by
    exact div_ne_zero hc (by norm_num))
  let poleV₁ := eventually_affine_ne_neg_nat (c := -c / 2) (d := c * d₁) (by
    exact div_ne_zero (neg_ne_zero.mpr hc) (by norm_num))
  let poleV₂ := eventually_affine_ne_neg_nat (c := c / 2) (d := c * d₂) (by
    exact div_ne_zero hc (by norm_num))
  let poleV₃ := eventually_affine_ne_neg_nat (c := c / 2) (d := c * d₃) (by
    exact div_ne_zero hc (by norm_num))
  let nonzeroV₀ := eventually_upsilon_affine_ne_zero hγ hU (c := (1 / 2 : ℂ))
    (d := d₀) (by norm_num)
  let nonzeroV₀p := eventually_upsilon_affine_ne_zero hγ hU (c := (1 / 2 : ℂ))
    (d := d₀ + c) (by norm_num)
  let nonzeroV₁ := eventually_upsilon_affine_ne_zero hγ hU (c := (-1 / 2 : ℂ))
    (d := d₁) (by norm_num)
  let nonzeroV₁p := eventually_upsilon_affine_ne_zero hγ hU (c := (-1 / 2 : ℂ))
    (d := d₁ + c) (by norm_num)
  let nonzeroV₂ := eventually_upsilon_affine_ne_zero hγ hU (c := (1 / 2 : ℂ))
    (d := d₂) (by norm_num)
  let nonzeroV₂p := eventually_upsilon_affine_ne_zero hγ hU (c := (1 / 2 : ℂ))
    (d := d₂ + c) (by norm_num)
  let nonzeroV₃ := eventually_upsilon_affine_ne_zero hγ hU (c := (1 / 2 : ℂ))
    (d := d₃) (by norm_num)
  let nonzeroV₃p := eventually_upsilon_affine_ne_zero hγ hU (c := (1 / 2 : ℂ))
    (d := d₃ + c) (by norm_num)
  let lnonzeroV₀ := eventually_affine_lFun_ne_zero (c := c / 2) (d := c * d₀) (by
    exact div_ne_zero hc (by norm_num))
  let lnonzeroV₂ := eventually_affine_lFun_ne_zero (c := c / 2) (d := c * d₂) (by
    exact div_ne_zero hc (by norm_num))
  let lnonzeroV₃ := eventually_affine_lFun_ne_zero (c := c / 2) (d := c * d₃) (by
    exact div_ne_zero hc (by norm_num))
  filter_upwards [poleA, poleAm, poleV₀, poleV₁, poleV₂, poleV₃,
    nonzeroV₀, nonzeroV₀p, nonzeroV₁, nonzeroV₁p, nonzeroV₂, nonzeroV₂p,
    nonzeroV₃, nonzeroV₃p, lnonzeroV₀, lnonzeroV₂, lnonzeroV₃]
    with α hpa hpam hp₀ hp₁ hp₂ hp₃ hu₀ hu₀p hu₁ hu₁p hu₂ hu₂p hu₃ hu₃p hl₀ hl₂ hl₃
  have hnotA : ∀ n : ℕ, c * α ≠ -(n : ℂ) := by simpa using hpa
  have hnotAShift : ∀ n : ℕ, (2 / (γ : ℂ)) * α ≠ -(n : ℂ) := by
    simpa [hcComplex] using hnotA
  have hnotAm : ∀ n : ℕ, c * (α - c) ≠ -(n : ℂ) := by
    intro n hn
    apply hpam n
    convert hn using 1
    ring
  have hnotAmShift : ∀ n : ℕ, (2 / (γ : ℂ)) * (α - c) ≠ -(n : ℂ) := by
    simpa [hcComplex] using hnotAm
  have hnotV₀ : ∀ n : ℕ, c * v₀ α ≠ -(n : ℂ) := by
    intro n hn
    apply hp₀ n
    convert hn using 1
    simp [v₀]
    ring
  have hnotV₀Shift : ∀ n : ℕ, (2 / (γ : ℂ)) * v₀ α ≠ -(n : ℂ) := by
    simpa [hcComplex] using hnotV₀
  have hnotV₁ : ∀ n : ℕ, c * v₁ α ≠ -(n : ℂ) := by
    intro n hn
    apply hp₁ n
    convert hn using 1
    simp [v₁]
    ring
  have hnotV₁Shift : ∀ n : ℕ, (2 / (γ : ℂ)) * v₁ α ≠ -(n : ℂ) := by
    simpa [hcComplex] using hnotV₁
  have hnotV₂ : ∀ n : ℕ, c * v₂ α ≠ -(n : ℂ) := by
    intro n hn
    apply hp₂ n
    convert hn using 1
    simp [v₂]
    ring
  have hnotV₂Shift : ∀ n : ℕ, (2 / (γ : ℂ)) * v₂ α ≠ -(n : ℂ) := by
    simpa [hcComplex] using hnotV₂
  have hnotV₃ : ∀ n : ℕ, c * v₃ α ≠ -(n : ℂ) := by
    intro n hn
    apply hp₃ n
    convert hn using 1
    simp [v₃]
    ring
  have hnotV₃Shift : ∀ n : ℕ, (2 / (γ : ℂ)) * v₃ α ≠ -(n : ℂ) := by
    simpa [hcComplex] using hnotV₃
  have hsA := IsUpsilon.shift_binv hγ hγ2 hU α hnotAShift
  have hsAm := IsUpsilon.shift_binv hγ hγ2 hU (α - c) hnotAmShift
  have hs₀ := IsUpsilon.shift_binv hγ hγ2 hU (v₀ α) hnotV₀Shift
  have hs₁ := IsUpsilon.shift_binv hγ hγ2 hU (v₁ α) hnotV₁Shift
  have hs₂ := IsUpsilon.shift_binv hγ hγ2 hU (v₂ α) hnotV₂Shift
  have hs₃ := IsUpsilon.shift_binv hγ hγ2 hU (v₃ α) hnotV₃Shift
  have hnum : U (α + c) = k α * k (α - c) * U (α - c) := by
    have hsA' : U (α + c) = k α * U α := by simpa [k, hcComplex, hsCast] using hsA
    have hargAm : α - c + ((2 / γ : ℝ) : ℂ) = α := by
      rw [hcCast]
      ring
    have hsAm' : U α = k (α - c) * U (α - c) := by
      rw [← hargAm]
      simpa [k, hcComplex, hsCast] using hsAm
    rw [hsAm'] at hsA'
    simpa [mul_assoc] using hsA'
  have hu₀' : U (v₀ α + c) = k (v₀ α) * U (v₀ α) := by
    simpa [k, hcComplex, hsCast] using hs₀
  have hu₁' : U (v₁ α + c) = k (v₁ α) * U (v₁ α) := by
    simpa [k, hcComplex, hsCast] using hs₁
  have hu₂' : U (v₂ α + c) = k (v₂ α) * U (v₂ α) := by
    simpa [k, hcComplex, hsCast] using hs₂
  have hu₃' : U (v₃ α + c) = k (v₃ α) * U (v₃ α) := by
    simpa [k, hcComplex, hsCast] using hs₃
  have hv₀p : v₀p α = v₀ α + c := by dsimp [v₀p, v₀]; ring
  have hv₁p : v₁p α = v₁ α + c := by dsimp [v₁p, v₁]; ring
  have hv₂p : v₂p α = v₂ α + c := by dsimp [v₂p, v₂]; ring
  have hv₃p : v₃p α = v₃ α + c := by dsimp [v₃p, v₃]; ring
  have hdenPlus : U (v₀ α + c) * U (v₁ α) * U (v₂ α + c) * U (v₃ α + c) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · have h₀ : U (v₀ α + c) ≠ 0 := by rw [← hv₀p]; exact hu₀p
          exact h₀
        · exact hu₁
      · have h₂ : U (v₂ α + c) ≠ 0 := by rw [← hv₂p]; exact hu₂p
        exact h₂
    · have h₃ : U (v₃ α + c) ≠ 0 := by rw [← hv₃p]; exact hu₃p
      exact h₃
  have hdenMinus : U (v₀ α) * U (v₁ α + c) * U (v₂ α) * U (v₃ α) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · exact hu₀
        · have h₁ : U (v₁ α + c) ≠ 0 := by rw [← hv₁p]; exact hu₁p
          exact h₁
      · exact hu₂
    · exact hu₃
  have hUv₀p : U (v₀ α + c) ≠ 0 := by rw [← hv₀p]; exact hu₀p
  have hUv₁p : U (v₁ α + c) ≠ 0 := by rw [← hv₁p]; exact hu₁p
  have hUv₂p : U (v₂ α + c) ≠ 0 := by rw [← hv₂p]; exact hu₂p
  have hUv₃p : U (v₃ α + c) ≠ 0 := by rw [← hv₃p]; exact hu₃p
  have hargL₀ : c * v₀ α = c / 2 * α + c * d₀ := by dsimp [v₀]; ring
  have hargL₂ : c * v₂ α = c / 2 * α + c * d₂ := by dsimp [v₂]; ring
  have hargL₃ : c * v₃ α = c / 2 * α + c * d₃ := by dsimp [v₃]; ring
  have hL₀ : lFun (c * v₀ α) ≠ 0 := by rw [hargL₀]; exact hl₀
  have hL₂ : lFun (c * v₂ α) ≠ 0 := by rw [hargL₂]; exact hl₂
  have hL₃ : lFun (c * v₃ α) ≠ 0 := by rw [hargL₃]; exact hl₃

  have hWplus0 : ((α + 2 / γ + α₂ + α₃ - 2 * Q γ) / 2) = v₀p α := by
    dsimp [v₀p, d₀, c]
    push_cast
    ring
  have hWminus0 : ((α - 2 / γ + α₂ + α₃ - 2 * Q γ) / 2) = v₀ α := by
    dsimp [v₀, d₀, c]
    push_cast
    ring
  have hUplus1 : ((α + 2 / γ + α₂ + α₃) / 2 - (α + 2 / γ)) = v₁ α := by
    dsimp [v₁, d₁, c]
    push_cast
    ring
  have hUminus1 : ((α - 2 / γ + α₂ + α₃) / 2 - (α - 2 / γ)) = v₁p α := by
    dsimp [v₁p, d₁, c]
    push_cast
    ring
  have hUplus2 : ((α + 2 / γ + α₂ + α₃) / 2 - α₂) = v₂p α := by
    dsimp [v₂p, d₂, c]
    push_cast
    ring
  have hUminus2 : ((α - 2 / γ + α₂ + α₃) / 2 - α₂) = v₂ α := by
    dsimp [v₂, d₂, c]
    push_cast
    ring
  have hUplus3 : ((α + 2 / γ + α₂ + α₃) / 2 - α₃) = v₃p α := by
    dsimp [v₃p, d₃, c]
    push_cast
    ring
  have hUminus3 : ((α - 2 / γ + α₂ + α₃) / 2 - α₃) = v₃ α := by
    dsimp [v₃, d₃, c]
    push_cast
    ring
  have hCoeffArg₁ : c / 2 * ((α + α₂ + α₃) - 2 * α - c) = c * v₁ α := by
    dsimp [v₁, d₁]
    ring
  have hCoeffArg₀ : c / 2 * ((α + α₂ + α₃) - c - 2 * (Q γ : ℂ)) = c * v₀ α := by
    dsimp [v₀, d₀]
    ring
  have hCoeffArg₂ : c / 2 * ((α + α₂ + α₃) - 2 * α₂ - c) = c * v₂ α := by
    dsimp [v₂, d₂]
    ring
  have hCoeffArg₃ : c / 2 * ((α + α₂ + α₃) - 2 * α₃ - c) = c * v₃ α := by
    dsimp [v₃, d₃]
    ring
  have hcoeff : shiftCoeffA γ (2 / γ) α α₂ α₃ =
      lFun (-r) * lFun (c * α) * lFun (c * (α - c)) * lFun (c * v₁ α) /
        (lFun (c * v₀ α) * lFun (c * v₃ α) * lFun (c * v₂ α)) := by
    have hcsq : c ^ 2 = r := by
      rw [hcCast, hrCast]
      push_cast
      field_simp [hγ.ne']
      ring
    unfold shiftCoeffA
    rw [← hcComplex]
    rw [show -c ^ 2 = -r by rw [hcsq]]
    rw [show c * α - c ^ 2 = c * (α - c) by ring]
    rw [hCoeffArg₁, hCoeffArg₀, hCoeffArg₃, hCoeffArg₂]
  have hscalar : Tc ^ pplus α * k α * k (α - c) * k (v₁ α) =
      -(1 / (Real.pi * dualMu γ μ)) * shiftCoeffA γ (2 / γ) α α₂ α₃ *
        Tc ^ pminus α * k (v₀ α) * k (v₂ α) * k (v₃ α) := by
    have hpowL : s ^ (4 / (γ : ℂ) * α - 1) *
        s ^ (4 / (γ : ℂ) * (α - c) - 1) *
        s ^ (4 / (γ : ℂ) * v₁ α - 1) =
        s ^ ((4 / (γ : ℂ) * α - 1) +
          (4 / (γ : ℂ) * (α - c) - 1) + (4 / (γ : ℂ) * v₁ α - 1)) := by
      rw [← Complex.cpow_add _ _ hs, ← Complex.cpow_add _ _ hs]
    have hpowR : s ^ (4 / (γ : ℂ) * v₀ α - 1) *
        s ^ (4 / (γ : ℂ) * v₂ α - 1) *
        s ^ (4 / (γ : ℂ) * v₃ α - 1) =
        s ^ ((4 / (γ : ℂ) * v₀ α - 1) +
          (4 / (γ : ℂ) * v₂ α - 1) + (4 / (γ : ℂ) * v₃ α - 1)) := by
      rw [← Complex.cpow_add _ _ hs, ← Complex.cpow_add _ _ hs]
    have hExp : (4 / (γ : ℂ) * α - 1) +
        (4 / (γ : ℂ) * (α - c) - 1) + (4 / (γ : ℂ) * v₁ α - 1) =
        ((4 / (γ : ℂ) * v₀ α - 1) +
          (4 / (γ : ℂ) * v₂ α - 1) + (4 / (γ : ℂ) * v₃ α - 1)) +
          (4 * (Q γ : ℂ) / γ) := by
      dsimp [v₀, v₁, v₂, v₃, d₀, d₁, d₂, d₃, c]
      push_cast
      unfold Q
      field_simp [hγ.ne']
      ring
    rw [hpow α, hcoeff]
    dsimp [k]
    rw [show Tc ^ pminus α / Tc ^ r *
          (lFun (c * α) * s ^ (4 / (γ : ℂ) * α - 1)) *
          (lFun (c * (α - c)) * s ^ (4 / (γ : ℂ) * (α - c) - 1)) *
          (lFun (c * v₁ α) * s ^ (4 / (γ : ℂ) * v₁ α - 1)) =
          (Tc ^ pminus α / Tc ^ r) *
            (lFun (c * α) * lFun (c * (α - c)) * lFun (c * v₁ α)) *
              (s ^ (4 / (γ : ℂ) * α - 1) *
                s ^ (4 / (γ : ℂ) * (α - c) - 1) *
                s ^ (4 / (γ : ℂ) * v₁ α - 1)) by ring]
    rw [show -(1 / (Real.pi * dualMu γ μ)) *
          (lFun (-r) * lFun (c * α) * lFun (c * (α - c)) * lFun (c * v₁ α) /
            (lFun (c * v₀ α) * lFun (c * v₃ α) * lFun (c * v₂ α))) * Tc ^ pminus α *
          (lFun (c * v₀ α) * s ^ (4 / (γ : ℂ) * v₀ α - 1)) *
          (lFun (c * v₂ α) * s ^ (4 / (γ : ℂ) * v₂ α - 1)) *
          (lFun (c * v₃ α) * s ^ (4 / (γ : ℂ) * v₃ α - 1)) =
          -(1 / (Real.pi * dualMu γ μ)) *
            (lFun (-r) * lFun (c * α) * lFun (c * (α - c)) * lFun (c * v₁ α) /
              (lFun (c * v₀ α) * lFun (c * v₃ α) * lFun (c * v₂ α))) * Tc ^ pminus α *
            (lFun (c * v₀ α) * lFun (c * v₂ α) * lFun (c * v₃ α)) *
              (s ^ (4 / (γ : ℂ) * v₀ α - 1) *
                s ^ (4 / (γ : ℂ) * v₂ α - 1) *
                s ^ (4 / (γ : ℂ) * v₃ α - 1)) by ring]
    rw [hpowL, hpowR, hExp]
    rw [Complex.cpow_add _ _ hs]
    have hden : (Real.pi : ℂ) * dualMu γ μ ≠ 0 := by
      rw [dualMu]
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hbasepow : ((dozzBase γ μ : ℝ) : ℂ) ^ r ≠ 0 := by
        apply Complex.cpow_ne_zero_iff.mpr
        exact Or.inl hbaseNe
      exact mul_ne_zero hpi (div_ne_zero hbasepow (mul_ne_zero hpi hLr))
    field_simp [hden, hL₀, hL₂, hL₃]
    have hbaseDiv : s ^ ((γ : ℂ)⁻¹ * (Q γ : ℂ) * 4) * (Real.pi : ℂ) / Tc ^ r =
        -lFun (-r) / dualMu γ μ := by
      have hTcPow : Tc ^ r ≠ 0 := by
        apply Complex.cpow_ne_zero_iff.mpr
        exact Or.inl hTc
      have hh : Tc ^ r * (-(lFun (-r)) / (Real.pi * dualMu γ μ)) =
          s ^ ((γ : ℂ)⁻¹ * (Q γ : ℂ) * 4) := by
        rw [← hScpow]
        exact hbaseId
      have hh' := congrArg (fun z : ℂ => z * (Real.pi : ℂ)) hh
      apply (div_eq_iff hTcPow).2
      calc
        s ^ ((γ : ℂ)⁻¹ * (Q γ : ℂ) * 4) * (Real.pi : ℂ) =
            Tc ^ r * (-(lFun (-r)) / (Real.pi * dualMu γ μ)) * (Real.pi : ℂ) := hh'.symm
        _ = (-lFun (-r) / dualMu γ μ) * Tc ^ r := by
          field_simp [hden]
    let A : ℂ := Tc ^ pminus α * lFun (c * α) * lFun (c * α - c ^ 2) *
      lFun (c * v₁ α) * s ^ (v₀ α * (γ : ℂ)⁻¹ * 4 -
        (γ : ℂ) * (γ : ℂ)⁻¹ * 3 + v₂ α * (γ : ℂ)⁻¹ * 4 +
        v₃ α * (γ : ℂ)⁻¹ * 4)
    calc
      _ = A * (s ^ ((γ : ℂ)⁻¹ * (Q γ : ℂ) * 4) * (Real.pi : ℂ) / Tc ^ r) := by
        dsimp [A]
        ring_nf
      _ = A * (-lFun (-r) / dualMu γ μ) := by rw [hbaseDiv]
      _ = _ := by
        dsimp [A]
        have hExpFix : v₀ α * (γ : ℂ)⁻¹ * 4 -
            (γ : ℂ) * (γ : ℂ)⁻¹ * 3 + v₂ α * (γ : ℂ)⁻¹ * 4 +
              v₃ α * (γ : ℂ)⁻¹ * 4 =
            (4 * v₀ α - (γ : ℂ) + (4 * v₂ α - (γ : ℂ)) +
              (4 * v₃ α - (γ : ℂ))) / (γ : ℂ) := by
          field_simp [hγ.ne']
          ring
        rw [show s ^ (v₀ α * (γ : ℂ)⁻¹ * 4 -
            (γ : ℂ) * (γ : ℂ)⁻¹ * 3 + v₂ α * (γ : ℂ)⁻¹ * 4 +
              v₃ α * (γ : ℂ)⁻¹ * 4) =
            s ^ ((4 * v₀ α - (γ : ℂ) + (4 * v₂ α - (γ : ℂ)) +
              (4 * v₃ α - (γ : ℂ))) / (γ : ℂ)) by
                congr 1]
        rw [show c * α - c ^ 2 = c * (α - c) by ring]
        ring
  have hpowplus : Tc ^ pplus α =
      ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ) ^
        ((2 * Q γ - (α + 2 / γ + α₂ + α₃)) / γ) := by
    have hbaseT : Tc =
        ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ) := by
      simp [Tc, T, Complex.ofReal_mul]
    rw [hbaseT]
    congr 1
    dsimp [pplus]
    rw [hcComplex]
  have hpowminus : Tc ^ pminus α =
      ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ) ^
        ((2 * Q γ - (α - 2 / γ + α₂ + α₃)) / γ) := by
    have hbaseT : Tc =
        ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ) := by
      simp [Tc, T, Complex.ofReal_mul]
    rw [hbaseT]
    congr 1
    dsimp [pminus]
    rw [hcComplex]
  unfold dozzFormula
  rw [← hpowplus, ← hpowminus]
  rw [hWplus0, hWminus0, hUplus1, hUminus1,
    hUplus2, hUminus2, hUplus3, hUminus3]
  rw [hv₀p, hv₁p, hv₂p, hv₃p]
  rw [← mul_div_assoc]
  rw [div_eq_div_iff hdenPlus hdenMinus]
  rw [show α + 2 / γ = α + c by rw [hcComplex], hαm α,
    hnum, hu₀', hu₁', hu₂', hu₃']
  linear_combination
    (deriv U 0 * U (α - c) * U α₂ * U α₃ *
      U (v₀ α) * U (v₁ α) * U (v₂ α) * U (v₃ α)) * hscalar

end DOZZ.Proofs
