/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
public import DOZZ.Upsilon.JointContinuityIntegral
import DOZZ.Upsilon.Continuation
import DOZZ.Upsilon.FullShifts
import DOZZ.Upsilon.Uniqueness
import DOZZ.Upsilon.ZeroStructure
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Joint parameter and argument continuity of the entire Upsilon family
-/

@[expose] public section

open Complex Filter MeasureTheory Set Topology

namespace DOZZ.Proofs

private noncomputable def jointShiftN (γ : ℝ) (n : ℕ) : ℂ :=
  ((n : ℝ) * (γ / 2) : ℂ)

private noncomputable def jointShiftFactor (γ : ℝ) (w : ℂ) : ℂ :=
  ((γ / 2 : ℝ) : ℂ) ^ ((γ : ℂ) * w - 1) *
    Complex.Gamma (1 - (γ / 2 : ℝ) * w) *
      (Complex.Gamma ((γ / 2 : ℝ) * w))⁻¹

private noncomputable def jointShiftChain (γ : ℝ) : ℕ → ℂ → ℂ
  | 0, _ => 1
  | n + 1, w => jointShiftFactor γ w *
      jointShiftChain γ n (w + (γ / 2 : ℝ))

private theorem jointShiftN_re (γ : ℝ) (n : ℕ) :
    (jointShiftN γ n).re = (n : ℝ) * (γ / 2) := by
  simp [jointShiftN]

private theorem jointShiftN_succ (γ : ℝ) (n : ℕ) :
    jointShiftN γ (n + 1) = jointShiftN γ n + (γ / 2 : ℝ) := by
  simp [jointShiftN, Nat.cast_add]
  ring

private theorem exists_shift_into_strip {γ : ℝ} (hγ : 0 < γ)
    {x : ℝ} (hxQ : x < Q γ) :
    ∃ n : ℕ, 0 < x + (n : ℝ) * (γ / 2) ∧ x + (n : ℝ) * (γ / 2) < Q γ := by
  have hb : 0 < γ / 2 := by positivity
  have hbQ : γ / 2 < Q γ := by
    unfold Q
    have hpos : 0 < 2 / γ := by positivity
    linarith
  by_cases hx : 0 < x
  · exact ⟨0, by simpa, by simpa using hxQ⟩
  · have hx0 : x ≤ 0 := le_of_not_gt hx
    let y := -x / (γ / 2)
    have hy0 : 0 ≤ y := by dsimp [y]; exact div_nonneg (neg_nonneg.mpr hx0) hb.le
    let N := Nat.floor y
    let n := N + 1
    have hfloor : (N : ℝ) ≤ y := Nat.floor_le hy0
    have hfloorlt : y < (N : ℝ) + 1 := Nat.lt_floor_add_one y
    have hnlt : y < (n : ℝ) := by simpa [n] using hfloorlt
    have hne : y * (γ / 2) = -x := by
      dsimp [y]
      field_simp [ne_of_gt hb]
    have hlow : 0 < x + (n : ℝ) * (γ / 2) := by
      have hmul := mul_lt_mul_of_pos_right hnlt hb
      rw [hne] at hmul
      nlinarith
    have hnle : (n : ℝ) ≤ y + 1 := by
      calc
        (n : ℝ) = (N : ℝ) + 1 := by simp [n]
        _ ≤ y + 1 := by linarith [hfloor]
    have hupp : x + (n : ℝ) * (γ / 2) ≤ γ / 2 := by
      have hmul := mul_le_mul_of_nonneg_right hnle hb.le
      calc
        x + (n : ℝ) * (γ / 2) ≤ x + (y + 1) * (γ / 2) := by linarith
        _ = γ / 2 := by rw [add_mul, hne]; ring
    exact ⟨n, hlow, lt_of_le_of_lt hupp hbQ⟩

private theorem IsUpsilon.eq_shiftChain {γ : ℝ} {U : ℂ → ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hU : IsUpsilon γ U)
    (w : ℂ) (n : ℕ) (hfinal :
      0 < (w + jointShiftN γ n).re ∧ (w + jointShiftN γ n).re < Q γ) :
    U w = jointShiftChain γ n w * U (w + jointShiftN γ n) := by
  induction n generalizing w with
  | zero => simp [jointShiftN, jointShiftChain]
  | succ n ih =>
      have hfinalEq : w + jointShiftN γ (n + 1) =
          (w + (γ / 2 : ℝ)) + jointShiftN γ n := by
        rw [jointShiftN_succ]
        abel
      have hfinal' : 0 < ((w + (γ / 2 : ℝ)) + jointShiftN γ n).re ∧
          ((w + (γ / 2 : ℝ)) + jointShiftN γ n).re < Q γ := by
        rw [← hfinalEq]
        exact hfinal
      have hfinalRe : (w + jointShiftN γ (n + 1)).re =
          w.re + (n + 1 : ℝ) * (γ / 2) := by
        simp [Complex.add_re, jointShiftN_re]
      have hstepLen : γ / 2 ≤ (n + 1 : ℝ) * (γ / 2) := by
        have hn : (1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        simpa using mul_le_mul_of_nonneg_right hn (show 0 ≤ γ / 2 by positivity)
      have hQb : Q γ - γ / 2 = 2 / γ := by unfold Q; ring
      have hw : w.re < 2 / γ := by
        have hlast := hfinal.2
        rw [hfinalRe] at hlast
        calc
          w.re < Q γ - (n + 1 : ℝ) * (γ / 2) := by linarith
          _ ≤ Q γ - γ / 2 := by linarith
          _ = 2 / γ := hQb
      have hrec := IsUpsilon.shift_b_reciprocal hγ hγ2 hU w hw
      have hrest := ih (w + (γ / 2 : ℝ)) hfinal'
      have hShiftArg : w + (γ / 2 : ℝ) = w + (γ / 2 : ℂ) := by
        push_cast
        ring
      rw [hShiftArg] at hrest
      rw [hrest] at hrec
      simpa [jointShiftChain, jointShiftFactor, hfinalEq, mul_assoc] using hrec.symm

private theorem jointShiftFactor_continuousAt {γ₀ : ℝ} {w₀ : ℂ}
    (hγ₀ : 0 < γ₀) (hw₀ : w₀.re < 2 / γ₀) :
    ContinuousAt (fun p : ℝ × ℂ => jointShiftFactor p.1 p.2) (γ₀, w₀) := by
  let b : ℝ × ℂ → ℂ := fun p => ((p.1 / 2 : ℝ) : ℂ)
  let γC : ℝ × ℂ → ℂ := fun p => (p.1 : ℂ)
  let arg₁ : ℝ × ℂ → ℂ := fun p => 1 - b p * p.2
  let arg₂ : ℝ × ℂ → ℂ := fun p => b p * p.2
  let exponent : ℝ × ℂ → ℂ := fun p => γC p * p.2 - 1
  have hb : ContinuousAt b (γ₀, w₀) := by fun_prop
  have hγC : ContinuousAt γC (γ₀, w₀) := by fun_prop
  have hw : ContinuousAt Prod.snd (γ₀, w₀) := continuousAt_snd
  have hbase : b (γ₀, w₀) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    simp [b]
    positivity
  have hexp : ContinuousAt exponent (γ₀, w₀) := by
    dsimp [exponent]
    exact (hγC.mul hw).sub continuousAt_const
  have hpow : ContinuousAt (fun p => b p ^ exponent p) (γ₀, w₀) :=
    hb.cpow hexp hbase
  have hbwRe : (b (γ₀, w₀) * w₀).re = (γ₀ / 2) * w₀.re := by
    simp [b, Complex.mul_re]
  have hscale : (γ₀ / 2) * w₀.re < 1 := by
    have hmul := mul_lt_mul_of_pos_left hw₀ (by positivity : 0 < γ₀ / 2)
    have hcancel : (γ₀ / 2) * (2 / γ₀) = 1 := by
      field_simp [hγ₀.ne']
    rw [hcancel] at hmul
    exact hmul
  have harg₁re : 0 < (arg₁ (γ₀, w₀)).re := by
    simp only [arg₁, Complex.sub_re, Complex.one_re, hbwRe]
    linarith
  have harg₁ : ContinuousAt arg₁ (γ₀, w₀) := by fun_prop
  have hGamma0 : ContinuousAt Complex.Gamma (arg₁ (γ₀, w₀)) :=
    Complex.continuousAt_Gamma _ (by
      intro m hm
      apply Complex.Gamma_ne_zero_of_re_pos harg₁re
      rw [hm]
      exact Complex.Gamma_neg_nat_eq_zero m)
  have hGamma : ContinuousAt (fun p => Complex.Gamma (arg₁ p)) (γ₀, w₀) :=
    hGamma0.comp harg₁
  have harg₂ : ContinuousAt arg₂ (γ₀, w₀) := by fun_prop
  have hInv0 : ContinuousAt (fun s : ℂ => (Complex.Gamma s)⁻¹)
      (arg₂ (γ₀, w₀)) :=
    (Complex.differentiable_one_div_Gamma (arg₂ (γ₀, w₀))).continuousAt
  have hInv : ContinuousAt (fun p => (Complex.Gamma (arg₂ p))⁻¹) (γ₀, w₀) :=
    hInv0.comp harg₂
  change ContinuousAt (fun p => b p ^ exponent p * Complex.Gamma (arg₁ p) *
    (Complex.Gamma (arg₂ p))⁻¹) (γ₀, w₀)
  exact (hpow.mul hGamma).mul hInv

private theorem jointShiftChain_continuousAt {γ₀ : ℝ} {w₀ : ℂ}
    (hγ₀ : 0 < γ₀) (n : ℕ)
    (hstep : ∀ j : ℕ, j < n → (w₀ + jointShiftN γ₀ j).re < 2 / γ₀) :
    ContinuousAt (fun p : ℝ × ℂ => jointShiftChain p.1 n p.2) (γ₀, w₀) := by
  induction n generalizing w₀ with
  | zero => simpa [jointShiftChain] using (continuousAt_const : ContinuousAt (fun _ : ℝ × ℂ => (1 : ℂ)) (γ₀, w₀))
  | succ n ih =>
      have hstep0 : w₀.re < 2 / γ₀ := by simpa [jointShiftN] using hstep 0 (by omega)
      have hstep' : ∀ j : ℕ, j < n →
          ((w₀ + (γ₀ / 2 : ℝ)) + jointShiftN γ₀ j).re < 2 / γ₀ := by
        intro j hj
        have h := hstep (j + 1) (by omega)
        have heq : (w₀ + (γ₀ / 2 : ℝ)) + jointShiftN γ₀ j =
            w₀ + jointShiftN γ₀ (j + 1) := by
          rw [jointShiftN_succ]
          abel
        rw [← heq] at h
        exact h
      have hfactor : ContinuousAt (fun p : ℝ × ℂ => jointShiftFactor p.1 p.2)
          (γ₀, w₀) := jointShiftFactor_continuousAt hγ₀ hstep0
      have hmap : ContinuousAt (fun p : ℝ × ℂ =>
          (p.1, p.2 + (p.1 / 2 : ℝ))) (γ₀, w₀) := by fun_prop
      have hrest : ContinuousAt (fun p : ℝ × ℂ =>
          jointShiftChain p.1 n (p.2 + (p.1 / 2 : ℝ))) (γ₀, w₀) := by
        have hIH : ContinuousAt (fun q : ℝ × ℂ => jointShiftChain q.1 n q.2)
            (γ₀, w₀ + (γ₀ / 2 : ℝ)) := by
          exact ih (w₀ := w₀ + (γ₀ / 2 : ℝ)) hstep'
        change ContinuousAt
          ((fun q : ℝ × ℂ => jointShiftChain q.1 n q.2) ∘
            (fun p : ℝ × ℂ => (p.1, p.2 + (p.1 / 2 : ℝ)))) (γ₀, w₀)
        exact ContinuousAt.comp
          (f := fun p : ℝ × ℂ => (p.1, p.2 + (p.1 / 2 : ℝ)))
          (g := fun q : ℝ × ℂ => jointShiftChain q.1 n q.2)
          (x := (γ₀, w₀)) hIH hmap
      change ContinuousAt (fun p : ℝ × ℂ =>
        jointShiftFactor p.1 p.2 *
          jointShiftChain p.1 n (p.2 + (p.1 / 2 : ℝ))) (γ₀, w₀)
      exact hfactor.mul hrest

private noncomputable def jointChartArg (reflect : Bool) (p : ℝ × ℂ) : ℂ :=
  if reflect then (Q p.1 : ℂ) - p.2 else p.2

private noncomputable def jointShiftChart (reflect : Bool) (n : ℕ)
    (p : ℝ × ℂ) : ℂ :=
  jointShiftChain p.1 n (jointChartArg reflect p) *
    Complex.exp (upsilonLog p.1 (jointChartArg reflect p + jointShiftN p.1 n))

private theorem jointChartArg_continuousAt {γ₀ : ℝ} {z₀ : ℂ} (reflect : Bool)
    (hγ₀ : γ₀ ≠ 0) :
    ContinuousAt (jointChartArg reflect) (γ₀, z₀) := by
  cases reflect
  · change ContinuousAt (fun p : ℝ × ℂ => p.2) (γ₀, z₀)
    exact continuousAt_snd
  · have hQ : ContinuousAt (fun p : ℝ × ℂ => (Q p.1 : ℂ)) (γ₀, z₀) := by
      have hQ' : ContinuousAt (fun p : ℝ × ℂ => Q p.1) (γ₀, z₀) := by
        have hQγ : ContinuousAt Q γ₀ := by
          fun_prop (disch := assumption) [Q]
        exact ContinuousAt.comp (f := fun p : ℝ × ℂ => p.1) (g := Q)
          (x := (γ₀, z₀)) hQγ continuousAt_fst
      exact ContinuousAt.comp (f := fun p : ℝ × ℂ => Q p.1)
        (g := fun x : ℝ => (x : ℂ)) (x := (γ₀, z₀))
        Complex.continuous_ofReal.continuousAt hQ'
    change ContinuousAt (fun p : ℝ × ℂ => (Q p.1 : ℂ) - p.2) (γ₀, z₀)
    exact hQ.sub continuousAt_snd

private theorem jointShiftChart_continuousAt {γ₀ : ℝ} {z₀ : ℂ}
    (reflect : Bool) (n : ℕ) (hγ₀ : 0 < γ₀)
    (hfinal : 0 < (jointChartArg reflect (γ₀, z₀) + jointShiftN γ₀ n).re ∧
      (jointChartArg reflect (γ₀, z₀) + jointShiftN γ₀ n).re < Q γ₀) :
    ContinuousAt (jointShiftChart reflect n) (γ₀, z₀) := by
  let w₀ := jointChartArg reflect (γ₀, z₀)
  let v₀ := w₀ + jointShiftN γ₀ n
  have hγ₀ne : γ₀ ≠ 0 := hγ₀.ne'
  have hArg : ContinuousAt (jointChartArg reflect) (γ₀, z₀) :=
    jointChartArg_continuousAt reflect hγ₀ne
  have hN : ContinuousAt (fun p : ℝ × ℂ => jointShiftN p.1 n) (γ₀, z₀) := by
    dsimp [jointShiftN]
    fun_prop
  have hW : ContinuousAt (fun p : ℝ × ℂ =>
      jointChartArg reflect p + jointShiftN p.1 n) (γ₀, z₀) := hArg.add hN
  have hW0 : jointChartArg reflect (γ₀, z₀) + jointShiftN γ₀ n = v₀ := rfl
  have hstep : ∀ j : ℕ, j < n → (w₀ + jointShiftN γ₀ j).re < 2 / γ₀ := by
    intro j hj
    have hjn : (j : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hj)
    have hb : 0 < γ₀ / 2 := by positivity
    have hmon : (j : ℝ) * (γ₀ / 2) + γ₀ / 2 ≤ (n : ℝ) * (γ₀ / 2) := by
      calc
        (j : ℝ) * (γ₀ / 2) + γ₀ / 2 = ((j : ℝ) + 1) * (γ₀ / 2) := by ring
        _ ≤ (n : ℝ) * (γ₀ / 2) := mul_le_mul_of_nonneg_right hjn hb.le
    have hfinalRe : v₀.re = w₀.re + (n : ℝ) * (γ₀ / 2) := by
      simp [v₀, Complex.add_re, jointShiftN_re]
    have hstepRe : (w₀ + jointShiftN γ₀ j).re =
        w₀.re + (j : ℝ) * (γ₀ / 2) := by
      simp [Complex.add_re, jointShiftN_re]
    rw [hstepRe]
    have hQminus : Q γ₀ - γ₀ / 2 = 2 / γ₀ := by
      unfold Q
      ring
    calc
      w₀.re + (j : ℝ) * (γ₀ / 2) ≤ v₀.re - γ₀ / 2 := by
        rw [hfinalRe]
        linarith
      _ < Q γ₀ - γ₀ / 2 := by linarith [hfinal.2]
      _ = 2 / γ₀ := hQminus
  have hChainOuter : ContinuousAt
      (fun q : ℝ × ℂ => jointShiftChain q.1 n q.2) (γ₀, w₀) :=
    jointShiftChain_continuousAt hγ₀ n hstep
  have hChainMap : ContinuousAt (fun p : ℝ × ℂ => (p.1, jointChartArg reflect p))
      (γ₀, z₀) := continuousAt_fst.prodMk hArg
  have hChain : ContinuousAt (fun p : ℝ × ℂ =>
      jointShiftChain p.1 n (jointChartArg reflect p)) (γ₀, z₀) := by
    change ContinuousAt
      ((fun q : ℝ × ℂ => jointShiftChain q.1 n q.2) ∘
        (fun p : ℝ × ℂ => (p.1, jointChartArg reflect p))) (γ₀, z₀)
    exact ContinuousAt.comp
      (f := fun p : ℝ × ℂ => (p.1, jointChartArg reflect p))
      (g := fun q : ℝ × ℂ => jointShiftChain q.1 n q.2)
      (x := (γ₀, z₀)) hChainOuter hChainMap
  have hQ : ContinuousAt (fun p : ℝ × ℂ => Q p.1) (γ₀, z₀) := by
    have hQγ : ContinuousAt Q γ₀ := by
      fun_prop (disch := assumption) [Q]
    exact ContinuousAt.comp (f := fun p : ℝ × ℂ => p.1) (g := Q)
      (x := (γ₀, z₀)) hQγ continuousAt_fst
  have hWre : ContinuousAt (fun p : ℝ × ℂ =>
      (jointChartArg reflect p + jointShiftN p.1 n).re) (γ₀, z₀) :=
    ContinuousAt.comp (f := fun p : ℝ × ℂ =>
      jointChartArg reflect p + jointShiftN p.1 n) (g := Complex.re)
      (x := (γ₀, z₀)) Complex.continuous_re.continuousAt hW
  have hGap : ContinuousAt (fun p : ℝ × ℂ => Q p.1 -
      (jointChartArg reflect p + jointShiftN p.1 n).re) (γ₀, z₀) :=
    hQ.sub hWre
  have hLogOuter : ContinuousAt (Function.uncurry upsilonLog) (γ₀, v₀) :=
    upsilonLog_continuousAt_joint hγ₀ hfinal.1 hfinal.2
  have hLogMap : ContinuousAt (fun p : ℝ × ℂ =>
      (p.1, jointChartArg reflect p + jointShiftN p.1 n)) (γ₀, z₀) :=
    continuousAt_fst.prodMk hW
  have hLog : ContinuousAt (fun p : ℝ × ℂ =>
      upsilonLog p.1 (jointChartArg reflect p + jointShiftN p.1 n)) (γ₀, z₀) := by
    change ContinuousAt
      ((Function.uncurry upsilonLog) ∘
        (fun p : ℝ × ℂ => (p.1, jointChartArg reflect p + jointShiftN p.1 n)))
      (γ₀, z₀)
    exact ContinuousAt.comp
      (f := fun p : ℝ × ℂ =>
        (p.1, jointChartArg reflect p + jointShiftN p.1 n))
      (g := Function.uncurry upsilonLog) (x := (γ₀, z₀)) hLogOuter hLogMap
  change ContinuousAt (fun p : ℝ × ℂ =>
    jointShiftChain p.1 n (jointChartArg reflect p) *
      Complex.exp (upsilonLog p.1 (jointChartArg reflect p + jointShiftN p.1 n)))
    (γ₀, z₀)
  exact hChain.mul (continuous_exp.continuousAt.comp hLog)

private theorem IsUpsilon.eq_jointShiftChart {γ : ℝ} {U : ℂ → ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hU : IsUpsilon γ U)
    (reflect : Bool) (n : ℕ) (z : ℂ)
    (hfinal : 0 < (jointChartArg reflect (γ, z) + jointShiftN γ n).re ∧
      (jointChartArg reflect (γ, z) + jointShiftN γ n).re < Q γ) :
    U z = jointShiftChart reflect n (γ, z) := by
  cases reflect with
  | false =>
      have hchain := IsUpsilon.eq_shiftChain hγ hγ2 hU z n (by simpa [jointChartArg] using hfinal)
      have hstrip := hU.2 (z + jointShiftN γ n) hfinal.1 hfinal.2
      calc
        U z = jointShiftChain γ n z * U (z + jointShiftN γ n) := hchain
        _ = jointShiftChain γ n z * Complex.exp
            (upsilonLog γ (z + jointShiftN γ n)) := by rw [hstrip]
        _ = jointShiftChart false n (γ, z) := by
          simp [jointShiftChart, jointChartArg]
  | true =>
      let w := (Q γ : ℂ) - z
      have hreflect : U z = U w := by
        simpa [w] using (_root_.DOZZ.Proofs.IsUpsilon.reflect hγ hγ2 hU z).symm
      have hchain := IsUpsilon.eq_shiftChain hγ hγ2 hU w n (by
        simpa [jointChartArg, w] using hfinal)
      have hstrip := hU.2 (w + jointShiftN γ n) hfinal.1 hfinal.2
      calc
        U z = U w := hreflect
        _ = jointShiftChain γ n w * Complex.exp (upsilonLog γ (w + jointShiftN γ n)) := by
          rw [hchain, hstrip]
        _ = jointShiftChart true n (γ, z) := by
          simp [jointShiftChart, jointChartArg, w]

/-- Joint continuity of `Υ_{γ/2}(z)` in `(γ, z)` (see the continuity arguments in [KRV, §10.6] and
[KRV, §11]). -/
theorem IsUpsilon.continuousOn_uncurry {U : ℝ → ℂ → ℂ}
    (hU : ∀ γ ∈ Ioo (0 : ℝ) 2, IsUpsilon γ (U γ)) :
    ContinuousOn (Function.uncurry U) (Ioo 0 2 ×ˢ univ) := by
  intro p hp
  rcases hp with ⟨hγp, _⟩
  rcases hγp with ⟨hγlo, hγhi⟩
  let γ₀ := p.1
  let z₀ := p.2
  have hγ₀ : 0 < γ₀ := hγlo
  have hγ₀2 : γ₀ < 2 := hγhi
  have hγ₀ne : γ₀ ≠ 0 := hγ₀.ne'
  have hU₀ : IsUpsilon γ₀ (U γ₀) := hU γ₀ ⟨hγ₀, hγ₀2⟩
  let reflect := if z₀.re < Q γ₀ then false else true
  have hxQ : (jointChartArg reflect p).re < Q γ₀ := by
    by_cases h : z₀.re < Q γ₀
    · simp [reflect, h, jointChartArg, γ₀, z₀]
    · have hzQ : z₀.re ≥ Q γ₀ := le_of_not_gt h
      have hQpos : 0 < Q γ₀ := by
        unfold Q
        positivity
      simp only [reflect, h, jointChartArg, γ₀, z₀, ite_false, ite_true,
        Complex.sub_re, Complex.ofReal_re]
      linarith
  obtain ⟨n, hfinal0, hfinalQ⟩ := exists_shift_into_strip hγ₀ hxQ
  let W : ℝ × ℂ → ℂ := fun q => jointChartArg reflect q + jointShiftN q.1 n
  have hWcont : ContinuousAt W p := by
    have hA := jointChartArg_continuousAt (γ₀ := γ₀) (z₀ := z₀) reflect hγ₀ne
    have hN : ContinuousAt (fun q : ℝ × ℂ => jointShiftN q.1 n) p := by
      dsimp [jointShiftN]
      fun_prop
    exact hA.add hN
  have hQcont : ContinuousAt (fun q : ℝ × ℂ => Q q.1) p := by
    have hQγ : ContinuousAt Q γ₀ := by
      fun_prop (disch := assumption) [Q]
    exact ContinuousAt.comp (f := fun q : ℝ × ℂ => q.1) (g := Q)
      (x := p) hQγ continuousAt_fst
  have hWre : ContinuousAt (fun q : ℝ × ℂ => (W q).re) p :=
    ContinuousAt.comp (f := W) (g := Complex.re) (x := p)
      Complex.continuous_re.continuousAt hWcont
  have hGapcont : ContinuousAt (fun q : ℝ × ℂ => Q q.1 - (W q).re) p :=
    hQcont.sub hWre
  have hnear : ∀ᶠ q : ℝ × ℂ in 𝓝 p,
      0 < q.1 ∧ q.1 < 2 ∧ 0 < (W q).re ∧ (W q).re < Q q.1 := by
    have hlo : ∀ᶠ q : ℝ × ℂ in 𝓝 p, 0 < q.1 :=
      continuousAt_fst.eventually (isOpen_Ioi.mem_nhds hγ₀)
    have hhi : ∀ᶠ q : ℝ × ℂ in 𝓝 p, q.1 < 2 :=
      continuousAt_fst.eventually (isOpen_Iio.mem_nhds (show γ₀ ∈ Iio 2 from hγ₀2))
    have hWlo : ∀ᶠ q : ℝ × ℂ in 𝓝 p, 0 < (W q).re :=
      hWre.eventually (isOpen_Ioi.mem_nhds (by simpa [W, γ₀, z₀, jointShiftN_re,
        Complex.add_re] using hfinal0))
    have hWhi : ∀ᶠ q : ℝ × ℂ in 𝓝 p, 0 < Q q.1 - (W q).re :=
      hGapcont.eventually (isOpen_Ioi.mem_nhds (sub_pos.mpr (by
        simpa [W, γ₀, z₀, jointShiftN_re, Complex.add_re] using hfinalQ)))
    filter_upwards [hlo, hhi, hWlo, hWhi] with q hqlo hqhi hqWlo hqWhi
    exact ⟨hqlo, hqhi, hqWlo, by linarith⟩
  have hchart0 := jointShiftChart_continuousAt reflect n hγ₀ (by
    simpa [γ₀, z₀, jointShiftN_re, Complex.add_re] using And.intro hfinal0 hfinalQ)
  have heq : Function.uncurry U =ᶠ[𝓝 p] jointShiftChart reflect n := by
    filter_upwards [hnear] with q hq
    have hUq : IsUpsilon q.1 (U q.1) := hU q.1 ⟨hq.1, hq.2.1⟩
    exact IsUpsilon.eq_jointShiftChart hq.1 hq.2.1 hUq reflect n q.2 ⟨hq.2.2.1, hq.2.2.2⟩
  have hAt : ContinuousAt (Function.uncurry U) p := hchart0.congr_of_eventuallyEq heq
  exact hAt.continuousWithinAt

end DOZZ.Proofs

end
