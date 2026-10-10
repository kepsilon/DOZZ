/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.DOZZAlgebra.GenericLocus
import DOZZ.Upsilon.FullShifts
import DOZZ.Upsilon.StripIdentities
import DOZZ.Upsilon.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The pointwise DOZZ reflection identity on a generic locus
-/

@[expose] public section

open Complex Filter Set Topology

namespace DOZZ.Proofs

variable {γ : ℝ}

private lemma real_mul_cpow {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (z : ℂ) :
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
  rw [Complex.ofReal_cpow hb r,
    ← Complex.cpow_mul z h₁ h₂]

/-- The two Υ shifts (`DOZZ.IsUpsilon.shift_b` and `DOZZ.IsUpsilon.shift_binv`) combine to the
reflection-coefficient ratio on a codiscrete set of arguments. -/
theorem eventually_upsilon_shift_Q {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hU : IsUpsilon γ U) :
    ∀ᶠ α : ℂ in codiscrete ℂ,
      U α = -( (γ : ℂ) / 2) ^
          ((γ : ℂ) * ((Q γ : ℂ) - α) - (4 / (γ : ℂ)) * ((Q γ : ℂ) - α)) *
        (Complex.Gamma (-((γ : ℂ) * ((Q γ : ℂ) - α) / 2)) /
          Complex.Gamma ((γ : ℂ) * ((Q γ : ℂ) - α) / 2)) *
        (Complex.Gamma (-(2 * ((Q γ : ℂ) - α) / (γ : ℂ))) /
          Complex.Gamma (2 * ((Q γ : ℂ) - α) / (γ : ℂ))) * U (α - Q γ) := by
  let b : ℂ := (γ : ℂ) / 2
  let c : ℂ := 2 / (γ : ℂ)
  let w : ℂ → ℂ := fun α => (Q γ : ℂ) - α
  let x : ℂ → ℂ := fun α => b * w α
  let y : ℂ → ℂ := fun α => c * w α
  let e : ℂ → ℂ := fun α => (γ : ℂ) * w α - (4 / (γ : ℂ)) * w α
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have hb : b ≠ 0 := by dsimp [b]; exact div_ne_zero hγc (by norm_num)
  have hc : c ≠ 0 := by dsimp [c]; exact div_ne_zero (by norm_num) hγc
  have hnot₁ := eventually_affine_ne_neg_nat (c := b) (d := -b * (Q γ : ℂ)) hb
  have hnot₂ := eventually_affine_ne_neg_nat (c := c)
    (d := 1 - c * (Q γ : ℂ)) hc
  have hΓx := eventually_affine_ne_neg_nat (c := -b) (d := b * (Q γ : ℂ))
    (neg_ne_zero.mpr hb)
  have hΓy := eventually_affine_ne_neg_nat (c := -c) (d := c * (Q γ : ℂ))
    (neg_ne_zero.mpr hc)
  filter_upwards [hnot₁, hnot₂, hΓx, hΓy] with α hnot₁ hnot₂ hΓx hΓy
  have hz₁ : ∀ n : ℕ, (γ / 2 : ℂ) * (α - Q γ) ≠ -(n : ℂ) := by
    intro n hn
    apply hnot₁ n
    convert hn using 1
    dsimp [b]
    ring
  have hz₂ : ∀ n : ℕ, (2 / γ : ℂ) * (α - Q γ + b) ≠ -(n : ℂ) := by
    intro n hn
    apply hnot₂ n
    have harg : (2 / γ : ℂ) * (α - Q γ + b) = c * α + (1 - c * (Q γ : ℂ)) := by
      dsimp [b, c]
      field_simp [hγc]
      ring
    rw [harg] at hn
    exact hn
  have hs₁ := IsUpsilon.shift_b hγ hγ2 hU (α - Q γ) hz₁
  have hs₂ := IsUpsilon.shift_binv hγ hγ2 hU (α - Q γ + b) hz₂
  have hsum : α - Q γ + b + 2 / γ = α := by
    dsimp [b]
    unfold Q
    push_cast
    field_simp [hγ.ne']
    ring
  have harg₁ : (γ / 2 : ℂ) * (α - Q γ) = -x α := by
      dsimp [x, w, b]
      ring
  have harg₂ : (2 / γ : ℂ) * (α - Q γ + b) = 1 - y α := by
      dsimp [y, w, b, c]
      field_simp [hγc]
      ring
  have hexp₂ : (4 / (γ : ℂ)) * (α - Q γ + b) - 1 =
        1 - (4 / (γ : ℂ)) * w α := by
      dsimp [w, b]
      unfold Q
      push_cast
      field_simp [hγ.ne']
      ring
  have hexp₁ : 1 - (γ : ℂ) * (α - Q γ) = 1 + (γ : ℂ) * w α := by
      dsimp [w]
      ring
  have hs₁' : U (α - Q γ + b) =
      lFun (-x α) * b ^ (1 + (γ : ℂ) * w α) * U (α - Q γ) := by
    have hs := hs₁
    rw [harg₁, hexp₁] at hs
    simpa [b] using hs
  have hs₂' : U (α - Q γ + b + 2 / γ) =
      lFun (1 - y α) * b ^ (1 - (4 / (γ : ℂ)) * w α) * U (α - Q γ + b) := by
    have hs := hs₂
    rw [harg₂, hexp₂] at hs
    simpa [b] using hs
  have hstep : U α =
      lFun (-x α) * b ^ (1 + (γ : ℂ) * w α) *
        (lFun (1 - y α) * b ^ (1 - (4 / (γ : ℂ)) * w α)) * U (α - Q γ) := by
    calc
      U α = U (α - Q γ + b + 2 / γ) := by rw [hsum]
      _ = lFun (1 - y α) * b ^ (1 - (4 / (γ : ℂ)) * w α) *
          U (α - Q γ + b) := hs₂'
      _ = _ := by rw [hs₁']; ring
  have hxne : ∀ n : ℕ, x α ≠ -(n : ℂ) := by
    intro n hn
    apply hΓx n
    have harg : x α = -b * α + b * (Q γ : ℂ) := by
      dsimp [x, w]
      ring
    rw [← harg]
    exact hn
  have hnegxne : ∀ n : ℕ, -x α ≠ -(n : ℂ) := by
    intro n hn
    apply hnot₁ n
    have harg : -x α = b * α - b * (Q γ : ℂ) := by
      dsimp [x, w]
      ring
    convert hn using 1
    dsimp [x, w, b]
    ring_nf
  have hyne : ∀ n : ℕ, y α ≠ -(n : ℂ) := by
    intro n hn
    apply hΓy n
    have harg : y α = -c * α + c * (Q γ : ℂ) := by
      dsimp [y, w]
      ring
    rw [← harg]
    exact hn
  have hnegyne : ∀ n : ℕ, -y α ≠ -(n : ℂ) := by
    intro n hn
    have harg : 1 - y α = c * α + (1 - c * (Q γ : ℂ)) := by
      dsimp [y, w]
      ring
    cases n with
    | zero =>
        apply hΓy 0
        have hzero : -c * α + c * (Q γ : ℂ) = 0 := by
          dsimp [y, w] at hn ⊢
          have hw : c * ((Q γ : ℂ) - α) = 0 := by simpa using hn
          calc
            -c * α + c * (Q γ : ℂ) = c * ((Q γ : ℂ) - α) := by ring
            _ = 0 := hw
        simpa using hzero
    | succ n =>
        apply hnot₂ n
        rw [← harg]
        have hy : y α = ((n + 1 : ℕ) : ℂ) := by
          have hneg : -y α = -((n + 1 : ℕ) : ℂ) := hn
          calc
            y α = -(-y α) := by ring
            _ = -(-((n + 1 : ℕ) : ℂ)) := congrArg Neg.neg hneg
            _ = _ := by push_cast; ring
        have : 1 - y α = -(n : ℂ) := by rw [hy]; push_cast; ring
        exact this
  have hΓx₀ : Complex.Gamma (x α) ≠ 0 := Complex.Gamma_ne_zero hxne
  have hΓmx : Complex.Gamma (-x α) ≠ 0 := Complex.Gamma_ne_zero hnegxne
  have hΓy₀ : Complex.Gamma (y α) ≠ 0 := Complex.Gamma_ne_zero hyne
  have hΓmy : Complex.Gamma (-y α) ≠ 0 := Complex.Gamma_ne_zero hnegyne
  have hx₀ : x α ≠ 0 := by intro h; simp [h] at hΓx₀
  have hy₀ : y α ≠ 0 := by intro h; simp [h] at hΓy₀
  have hrecx : Complex.Gamma (1 + x α) = x α * Complex.Gamma (x α) := by
    simpa [add_comm] using Complex.Gamma_add_one (x α) hx₀
  have hrecy : Complex.Gamma (1 - y α) = -y α * Complex.Gamma (-y α) := by
    simpa [sub_eq_add_neg, add_comm] using
      Complex.Gamma_add_one (-y α) (neg_ne_zero.mpr hy₀)
  have hL : lFun (-x α) * lFun (1 - y α) =
      -(1 / b ^ 2) *
        (Complex.Gamma (-x α) / Complex.Gamma (x α)) *
        (Complex.Gamma (-y α) / Complex.Gamma (y α)) := by
    have hxy : y α * b ^ 2 = x α := by
      dsimp [x, y, b, c]
      field_simp [hγc]
    unfold lFun
    rw [show 1 - -x α = 1 + x α by ring, hrecx, hrecy,
      show 1 - (1 - y α) = y α by ring]
    field_simp [hx₀, hy₀, hΓx₀, hΓmx, hΓy₀, hΓmy, hb]
    rw [hxy]
  have hpow : b ^ (1 + (γ : ℂ) * w α) *
      b ^ (1 - (4 / (γ : ℂ)) * w α) = b ^ (2 + e α) := by
    rw [← Complex.cpow_add _ _ hb]
    congr 1
    dsimp [e]
    ring
  have hpow2 : b ^ (2 + e α) = b ^ 2 * b ^ e α := by
    rw [Complex.cpow_add _ _ hb]
    simp
  have hfinal :
      lFun (-x α) * b ^ (1 + (γ : ℂ) * w α) *
        (lFun (1 - y α) * b ^ (1 - (4 / (γ : ℂ)) * w α)) =
      -(b ^ e α) *
        (Complex.Gamma (-x α) / Complex.Gamma (x α)) *
        (Complex.Gamma (-y α) / Complex.Gamma (y α)) := by
    rw [show lFun (-x α) * b ^ (1 + (γ : ℂ) * w α) *
        (lFun (1 - y α) * b ^ (1 - (4 / (γ : ℂ)) * w α)) =
        (lFun (-x α) * lFun (1 - y α)) *
          (b ^ (1 + (γ : ℂ) * w α) * b ^ (1 - (4 / (γ : ℂ)) * w α)) by ring]
    rw [hL, hpow, hpow2]
    field_simp [hb]
  calc
    U α = lFun (-x α) * b ^ (1 + (γ : ℂ) * w α) *
        (lFun (1 - y α) * b ^ (1 - (4 / (γ : ℂ)) * w α)) * U (α - Q γ) := hstep
    _ = _ := by rw [hfinal]; dsimp [x, y, w, e, b, c]; ring_nf

/-- DOZZ reflection follows pointwise from the two Υ shifts and reflection symmetry. -/
theorem dozzFormula_reflection {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {μ : ℝ} (hμ : 0 < μ) (hU : IsUpsilon γ U) (α₂ α₃ : ℂ) :
    ∀ᶠ α₁ in codiscrete ℂ,
      dozzFormula γ μ U α₁ α₂ α₃ =
        reflectionDOZZ γ μ α₁ * dozzFormula γ μ U (2 * Q γ - α₁) α₂ α₃ := by
  let d₀ : ℂ → ℂ := fun α => (α + α₂ + α₃ - 2 * Q γ) / 2
  let d₁ : ℂ → ℂ := fun α => (α₂ + α₃ - α) / 2
  let d₂ : ℂ → ℂ := fun α => (α + α₃ - α₂) / 2
  let d₃ : ℂ → ℂ := fun α => (α + α₂ - α₃) / 2
  have he₀ := eventually_upsilon_affine_ne_zero hγ hU (c := 1 / 2)
    (d := (α₂ + α₃ - 2 * (Q γ : ℂ)) / 2) (by norm_num)
  have he₁ := eventually_upsilon_affine_ne_zero hγ hU (c := -1 / 2)
    (d := (α₂ + α₃) / 2) (by norm_num)
  have he₂ := eventually_upsilon_affine_ne_zero hγ hU (c := 1 / 2)
    (d := (α₃ - α₂) / 2) (by norm_num)
  have he₃ := eventually_upsilon_affine_ne_zero hγ hU (c := 1 / 2)
    (d := (α₂ - α₃) / 2) (by norm_num)
  have hshift := eventually_upsilon_shift_Q hγ hγ2 hU
  filter_upwards [he₀, he₁, he₂, he₃, hshift] with α he₀ he₁ he₂ he₃ hshift
  have hden0 : U (d₀ α) ≠ 0 := by
    have harg : d₀ α = 1 / 2 * α + (α₂ + α₃ - 2 * Q γ) / 2 := by dsimp [d₀]; ring
    rw [harg]
    exact he₀
  have hden1 : U (d₁ α) ≠ 0 := by
    have harg : d₁ α = -1 / 2 * α + (α₂ + α₃) / 2 := by dsimp [d₁]; ring
    rw [harg]
    exact he₁
  have hden2 : U (d₂ α) ≠ 0 := by
    have harg : d₂ α = 1 / 2 * α + (α₃ - α₂) / 2 := by dsimp [d₂]; ring
    rw [harg]
    exact he₂
  have hden3 : U (d₃ α) ≠ 0 := by
    have harg : d₃ α = 1 / 2 * α + (α₂ - α₃) / 2 := by dsimp [d₃]; ring
    rw [harg]
    exact he₃
  have hr0 : U ((2 * Q γ - α + α₂ + α₃ - 2 * Q γ) / 2) = U (d₁ α) := by
    congr 1
    dsimp [d₁]
    unfold Q
    push_cast
    ring
  have hr1 : U ((2 * Q γ - α + α₂ + α₃) / 2 - (2 * Q γ - α)) = U (d₀ α) := by
    congr 1
    dsimp [d₀]
    unfold Q
    push_cast
    ring
  have hr2 : U ((2 * Q γ - α + α₂ + α₃) / 2 - α₂) = U (d₃ α) := by
    have h := IsUpsilon.reflect hγ hγ2 hU (d₃ α)
    have harg : ((2 * Q γ - α + α₂ + α₃) / 2 - α₂) = Q γ - d₃ α := by
      dsimp [d₃]
      unfold Q
      push_cast
      ring
    rw [harg]
    exact h
  have hr3 : U ((2 * Q γ - α + α₂ + α₃) / 2 - α₃) = U (d₂ α) := by
    have h := IsUpsilon.reflect hγ hγ2 hU (d₂ α)
    have harg : ((2 * Q γ - α + α₂ + α₃) / 2 - α₃) = Q γ - d₂ α := by
      dsimp [d₂]
      unfold Q
      push_cast
      ring
    rw [harg]
    exact h
  have hden : U (d₀ α) * U (d₁ α) * U (d₂ α) * U (d₃ α) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hden0 hden1) hden2) hden3
  let T : ℝ := dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2)
  let q : ℂ := 2 * ((Q γ : ℂ) - α) / (γ : ℂ)
  let e : ℂ := (γ : ℂ) * ((Q γ : ℂ) - α) - (4 / (γ : ℂ)) * ((Q γ : ℂ) - α)
  let b : ℂ := (γ : ℂ) / 2
  have hTpos : 0 < T := by
    dsimp [T]
    exact mul_pos (dozzBase_pos hγ hγ2 hμ) (Real.rpow_pos_of_pos (by positivity) _)
  have hTsplit : ((T : ℝ) : ℂ) ^ q =
      ((dozzBase γ μ : ℝ) : ℂ) ^ q *
        b ^ (((2 - γ ^ 2 / 2 : ℝ) : ℂ) * q) := by
    have h := real_mul_cpow (a := dozzBase γ μ) (b := γ / 2)
      (r := 2 - γ ^ 2 / 2) (z := q) (le_of_lt (dozzBase_pos hγ hγ2 hμ)) (by positivity)
    simpa [T, b, Complex.ofReal_mul] using h
  have hqe : (((2 - γ ^ 2 / 2 : ℝ) : ℂ) * q) + e = 0 := by
    dsimp [q, e]
    unfold Q
    push_cast
    field_simp [hγ.ne']
    ring
  have hpowCancel :
      ((T : ℝ) : ℂ) ^ q * b ^ e =
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
  have hshift' : U α =
      -b ^ e *
        (Complex.Gamma (-((γ : ℂ) * ((Q γ : ℂ) - α) / 2)) /
          Complex.Gamma ((γ : ℂ) * ((Q γ : ℂ) - α) / 2)) *
        (Complex.Gamma (-(2 * ((Q γ : ℂ) - α) / (γ : ℂ))) /
          Complex.Gamma (2 * ((Q γ : ℂ) - α) / (γ : ℂ))) * U (2 * Q γ - α) := by
    rw [hshift]
    congr 1
    have h := IsUpsilon.reflect hγ hγ2 hU (2 * Q γ - α)
    have harg : Q γ - (2 * Q γ - α) = α - Q γ := by ring_nf
    rw [harg] at h
    exact h
  have hpref :
      ((T : ℝ) : ℂ) ^ ((2 * Q γ - (α + α₂ + α₃)) / γ) =
        ((T : ℝ) : ℂ) ^ ((2 * Q γ - ((2 * Q γ - α) + α₂ + α₃)) / γ) *
          ((T : ℝ) : ℂ) ^ q := by
    have hTne : ((T : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hTpos.ne'
    have hexp : (2 * Q γ - (α + α₂ + α₃)) / γ =
        ((2 * Q γ - ((2 * Q γ - α) + α₂ + α₃)) / γ) + q := by
      dsimp [q]
      field_simp [hγ.ne']
      ring
    rw [hexp, Complex.cpow_add _ _ hTne]
  have harg0 : (α + α₂ + α₃ - 2 * Q γ) / 2 = d₀ α := by dsimp [d₀]
  have harg1 : (α + α₂ + α₃) / 2 - α = d₁ α := by dsimp [d₁]; ring
  have harg2 : (α + α₂ + α₃) / 2 - α₂ = d₂ α := by dsimp [d₂]; ring
  have harg3 : (α + α₂ + α₃) / 2 - α₃ = d₃ α := by dsimp [d₃]; ring
  have hdenL :
      U ((α + α₂ + α₃ - 2 * Q γ) / 2) * U ((α + α₂ + α₃) / 2 - α) *
        U ((α + α₂ + α₃) / 2 - α₂) * U ((α + α₂ + α₃) / 2 - α₃) ≠ 0 := by
    rw [harg0, harg1, harg2, harg3]
    exact hden
  have hdenEq : U (d₁ α) * U (d₀ α) * U (d₃ α) * U (d₂ α) =
      U ((α + α₂ + α₃ - 2 * Q γ) / 2) * U ((α + α₂ + α₃) / 2 - α) *
        U ((α + α₂ + α₃) / 2 - α₂) * U ((α + α₂ + α₃) / 2 - α₃) := by
    rw [← harg0, ← harg1, ← harg2, ← harg3]
    ring
  unfold dozzFormula
  rw [hr0, hr1, hr2, hr3]
  have hdenR : U (d₁ α) * U (d₀ α) * U (d₃ α) * U (d₂ α) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hden1 hden0) hden3) hden2
  rw [← mul_div_assoc]
  rw [div_eq_div_iff hdenL hdenR]
  rw [hpref, hshift']
  let g₁ : ℂ := Complex.Gamma (-((γ : ℂ) * ((Q γ : ℂ) - α) / 2)) /
    Complex.Gamma ((γ : ℂ) * ((Q γ : ℂ) - α) / 2)
  let g₂ : ℂ := Complex.Gamma (-(2 * ((Q γ : ℂ) - α) / (γ : ℂ))) /
    Complex.Gamma (2 * ((Q γ : ℂ) - α) / (γ : ℂ))
  let K : ℂ := -b ^ e * g₁ * g₂
  have hcoef : ((T : ℝ) : ℂ) ^ q * K = reflectionDOZZ γ μ α := by
    calc
      ((T : ℝ) : ℂ) ^ q * K = -(((T : ℝ) : ℂ) ^ q * b ^ e) * g₁ * g₂ := by
        dsimp [K]
        ring
      _ = -(((dozzBase γ μ : ℝ) : ℂ) ^ q) * g₁ * g₂ := by rw [hpowCancel]
      _ = reflectionDOZZ γ μ α := by
        unfold reflectionDOZZ
        rfl
  let pref₂ : ℂ := ((T : ℝ) : ℂ) ^ ((2 * Q γ - ((2 * Q γ - α) + α₂ + α₃)) / γ)
  let core : ℂ := deriv U 0 * U (2 * Q γ - α) * U α₂ * U α₃
  calc
    _ = pref₂ * (((T : ℝ) : ℂ) ^ q * K) * core *
          (U (d₁ α) * U (d₀ α) * U (d₃ α) * U (d₂ α)) := by
            dsimp [pref₂, core, K, g₁, g₂]
            ring
    _ = pref₂ * reflectionDOZZ γ μ α * core *
          (U (d₁ α) * U (d₀ α) * U (d₃ α) * U (d₂ α)) := by rw [hcoef]
    _ = reflectionDOZZ γ μ α * (pref₂ * core) *
          (U ((α + α₂ + α₃ - 2 * Q γ) / 2) * U ((α + α₂ + α₃) / 2 - α) *
            U ((α + α₂ + α₃) / 2 - α₂) * U ((α + α₂ + α₃) / 2 - α₃)) := by
              rw [hdenEq]
              ring
    _ = _ := by dsimp [pref₂, core]

end DOZZ.Proofs

end
