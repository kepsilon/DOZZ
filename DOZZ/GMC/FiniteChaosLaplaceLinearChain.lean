/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosLaplaceBounds
public import DOZZ.GMC.StandardGaussianBoundedStein

/-! The Laplace score chain rule along an arbitrary finite-dimensional linear image. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter
open MeasureTheory ProbabilityTheory
open scoped Topology

/-- The linear image of a finite field vector. -/
def finiteChaosLinearImageVector {ι : Type*}
    [Fintype ι] (A : ι → ι → ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun i => ∑ l, A i l * x l

/-- Varying one standard Gaussian coordinate through a linear image differentiates the
finite-chaos Laplace score by the corresponding linear combination of its field-coordinate
derivatives. This is the test-specific chain rule needed to use the singular-safe standard
Gaussian Stein formula along a covariance square root. -/
theorem finiteChaos_laplace_score_hasDerivAt_linearImage_coordinate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → ℝ) (a v : ι → ℝ) (γ s : ℝ)
    (x : ι → ℝ) (i k : ι) :
    HasDerivAt
      (fun r => finiteChaosVectorWeight a v γ
        (finiteChaosLinearImageVector A (Function.update x k r)) i *
        (-s * Real.exp (-s * finiteChaosVectorMass a v γ
          (finiteChaosLinearImageVector A (Function.update x k r)))) )
      (∑ j, A j k * (γ * (if i = j then
          finiteChaosVectorWeight a v γ (finiteChaosLinearImageVector A x) i *
            (-s * Real.exp (-s * finiteChaosVectorMass a v γ
              (finiteChaosLinearImageVector A x))) else 0) +
        γ * finiteChaosVectorWeight a v γ (finiteChaosLinearImageVector A x) i *
          finiteChaosVectorWeight a v γ (finiteChaosLinearImageVector A x) j *
            (s ^ 2 * Real.exp (-s * finiteChaosVectorMass a v γ
              (finiteChaosLinearImageVector A x))))) (x k) := by
  classical
  let T := finiteChaosLinearImageVector A
  let F' : ℝ → ℝ := fun z => -s * Real.exp (-s * z)
  let F'' : ℝ → ℝ := fun z => s ^ 2 * Real.exp (-s * z)
  have hT (j : ι) : HasDerivAt (fun r => T (Function.update x k r) j)
      (A j k) (x k) := by
    have hupd (r : ℝ) (l : ι) :
        Function.update x k r l = x l + (if l = k then r - x k else 0) := by
      by_cases hl : l = k
      · subst l
        simp
      · simp [Function.update_of_ne, hl]
    have hform (r : ℝ) : T (Function.update x k r) j = T x j + A j k * (r - x k) := by
      dsimp [T, finiteChaosLinearImageVector]
      calc
        _ = ∑ l, (A j l * x l + A j l * (if l = k then r - x k else 0)) := by
              apply Finset.sum_congr rfl
              intro l hl
              rw [hupd]
              ring
        _ = (∑ l, A j l * x l) + A j k * (r - x k) := by
              rw [Finset.sum_add_distrib]
              congr 1
              rw [Finset.sum_eq_single k]
              · simp
              · intro l hl hne
                simp [hne]
              · simp
        _ = T x j + A j k * (r - x k) := by
              simp [T, finiteChaosLinearImageVector]
    have hsub : HasDerivAt (fun r : ℝ => r - x k) 1 (x k) := by
      simpa using (hasDerivAt_id (x k)).sub_const (x k)
    have hmul : HasDerivAt (fun r : ℝ => A j k * (r - x k)) (A j k) (x k) := by
      simpa using hsub.const_mul (A j k)
    have hsum := (hasDerivAt_const (x k) (T x j)).add hmul
    simpa using hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall hform)
  have hExp (j : ι) : HasDerivAt
      (fun r => γ * T (Function.update x k r) j - γ ^ 2 / 2 * v j)
      (γ * A j k) (x k) := by
    convert ((hT j).const_mul γ).sub
      (hasDerivAt_const (x k) (γ ^ 2 / 2 * v j)) using 1; simp
  have hWeight (j : ι) : HasDerivAt
      (fun r => finiteChaosVectorWeight a v γ (T (Function.update x k r)) j)
      (γ * A j k * finiteChaosVectorWeight a v γ (T x) j) (x k) := by
    have hexp := (Real.hasDerivAt_exp
      (γ * T (Function.update x k (x k)) j - γ ^ 2 / 2 * v j)).comp (x k) (hExp j)
    convert hexp.const_mul (a j) using 1
    · ext r
      simp [finiteChaosVectorWeight]
    · simp [finiteChaosVectorWeight, Function.update_eq_self]
      ring
  have hMass : HasDerivAt
      (fun r => finiteChaosVectorMass a v γ (T (Function.update x k r)))
      (γ * ∑ j, A j k * finiteChaosVectorWeight a v γ (T x) j) (x k) := by
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun j hj => hWeight j)
    have hderiv :
        (∑ j, γ * A j k * finiteChaosVectorWeight a v γ (T x) j) =
          γ * ∑ j, A j k * finiteChaosVectorWeight a v γ (T x) j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    simpa [finiteChaosVectorMass, hderiv] using hsum
  have hF' : ∀ z, HasDerivAt F' (F'' z) z := by
    intro z
    have hlin : HasDerivAt (fun u : ℝ => -s * u) (-s) z := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id z).const_mul (-s)
    have hexp : HasDerivAt (fun u : ℝ => Real.exp (-s * u))
        (Real.exp (-s * z) * (-s)) z :=
      (Real.hasDerivAt_exp (-s * z)).comp z hlin
    have hmul := hexp.const_mul (-s)
    have hmul' : HasDerivAt (fun u : ℝ => -s * Real.exp (-s * u))
        (s ^ 2 * Real.exp (-s * z)) z := by
      convert hmul using 1
      ring
    simpa [F', F''] using hmul'
  have hFmass : HasDerivAt
      (fun r => F' (finiteChaosVectorMass a v γ (T (Function.update x k r))))
      (F'' (finiteChaosVectorMass a v γ (T x)) *
        (γ * ∑ j, A j k * finiteChaosVectorWeight a v γ (T x) j)) (x k) := by
    have h := (hF' (finiteChaosVectorMass a v γ (T (Function.update x k (x k))))).comp
      (x k) hMass
    simpa only [Function.comp_def, Function.update_eq_self] using h
  have hscore := (hWeight i).mul hFmass
  have hsum :
      (∑ j, A j k * (γ * (if i = j then
          finiteChaosVectorWeight a v γ (T x) i * F' (finiteChaosVectorMass a v γ (T x))
            else 0) + γ * finiteChaosVectorWeight a v γ (T x) i *
          finiteChaosVectorWeight a v γ (T x) j * F'' (finiteChaosVectorMass a v γ (T x)))) =
        γ * A i k * finiteChaosVectorWeight a v γ (T x) i *
            F' (finiteChaosVectorMass a v γ (T x)) +
          finiteChaosVectorWeight a v γ (T x) i * F'' (finiteChaosVectorMass a v γ (T x)) *
            (γ * ∑ j, A j k * finiteChaosVectorWeight a v γ (T x) j) := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    have hdiag :
        (∑ j, A j k * (γ * (if i = j then
          finiteChaosVectorWeight a v γ (T x) i * F' (finiteChaosVectorMass a v γ (T x))
            else 0)) =
          A i k * (γ * finiteChaosVectorWeight a v γ (T x) i *
            F' (finiteChaosVectorMass a v γ (T x)))) := by
      rw [Finset.sum_eq_single i]
      · simp only [ite_true]
        ring_nf
      · intro j hj hne
        have hij : i ≠ j := fun h => hne h.symm
        simp [hij]
      · simp
    rw [hdiag]
    have hmix :
        (∑ j, A j k * (γ * finiteChaosVectorWeight a v γ (T x) i *
          finiteChaosVectorWeight a v γ (T x) j * F'' (finiteChaosVectorMass a v γ (T x)))) =
          γ * finiteChaosVectorWeight a v γ (T x) i *
            F'' (finiteChaosVectorMass a v γ (T x)) *
              (∑ j, A j k * finiteChaosVectorWeight a v γ (T x) j) := by
      calc
        _ = ∑ j, (γ * finiteChaosVectorWeight a v γ (T x) i *
            F'' (finiteChaosVectorMass a v γ (T x))) *
              (A j k * finiteChaosVectorWeight a v γ (T x) j) := by
                apply Finset.sum_congr rfl
                intro j hj
                ring
        _ = _ := by rw [Finset.mul_sum]
    rw [hmix]
    ring
  convert hscore using 1
  rw [hsum]
  simp [F', F'', Function.update_eq_self]
  ring

/-- Casts the real derivative statement from the inner-product-space module structure to the
semiring module structure used by the bounded standard-Gaussian Stein lemma
`gaussianLinearImage_pi_integration_by_parts_of_bounded`. The two module structures act by the same
real multiplication. -/
theorem real_hasDerivAt_to_semiring_module
    {f : ℝ → ℝ} {f' x : ℝ} (h : HasDerivAt f f' x) :
    @HasDerivAt ℝ DenselyNormedField.toNontriviallyNormedField ℝ
      Real.instAddCommGroup Semiring.toModule
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace _ f f' x := by
  have hAdd : (Real.normedAddCommGroup.toAddCommGroup : AddCommGroup ℝ) =
      Real.instAddCommGroup := by rfl
  have hMod : (RCLike.toInnerProductSpaceReal.toModule : Module ℝ ℝ) =
      Semiring.toModule := by
    ext a y
    rfl
  cases hAdd
  cases hMod
  exact h

/-- The bounded Laplace score satisfies covariance integration by parts under every square linear
image of a standard Gaussian vector. The row-Gram covariance may be singular. -/
theorem finiteChaos_laplace_score_standardGaussian_ibp
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (a v : Fin (n + 1) → ℝ) (γ s : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hs : 0 ≤ s) (i : Fin (n + 1)) :
    ∫ x, (∑ k, A i k * x k) *
        (finiteChaosVectorWeight a v γ (fun j => ∑ k, A j k * x k) i *
          (-s * Real.exp (-s * finiteChaosVectorMass a v γ
            (fun j => ∑ k, A j k * x k))))
        ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) =
      ∑ j, (∑ k, A i k * A j k) *
        ∫ x,
          (γ * (if i = j then
              finiteChaosVectorWeight a v γ (fun l => ∑ k, A l k * x k) i *
                (-s * Real.exp (-s * finiteChaosVectorMass a v γ
                  (fun l => ∑ k, A l k * x k))) else 0) +
            γ * finiteChaosVectorWeight a v γ (fun l => ∑ k, A l k * x k) i *
              finiteChaosVectorWeight a v γ (fun l => ∑ k, A l k * x k) j *
                (s ^ 2 * Real.exp (-s * finiteChaosVectorMass a v γ
                  (fun l => ∑ k, A l k * x k))))
          ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  classical
  let T : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ :=
    fun x j => ∑ k, A j k * x k
  let G : (Fin (n + 1) → ℝ) → ℝ := fun x =>
    finiteChaosVectorWeight a v γ x i *
      (-s * Real.exp (-s * finiteChaosVectorMass a v γ x))
  let D : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ := fun x j =>
    γ * (if i = j then finiteChaosVectorWeight a v γ x i *
        (-s * Real.exp (-s * finiteChaosVectorMass a v γ x)) else 0) +
      γ * finiteChaosVectorWeight a v γ x i * finiteChaosVectorWeight a v γ x j *
        (s ^ 2 * Real.exp (-s * finiteChaosVectorMass a v γ x))
  have hLin (z : Fin (n + 1) → ℝ) :
      finiteChaosLinearImageVector A z = fun j => ∑ l, A j l * z l := by
    funext j
    rfl
  have hderiv : ∀ k (y : Fin n → ℝ) r,
      HasDerivAt
        (fun u => G (fun j => ∑ l, A j l *
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k).symm (u, y) l))
        (∑ j, A j k * D
          (fun j => ∑ l, A j l *
            (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k).symm (r, y) l) j) r := by
    intro k y r
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k
    let x : Fin (n + 1) → ℝ := e.symm (r, y)
    have hxk : x k = r := by simp [x, e]
    have hpath (u : ℝ) : e.symm (u, y) = Function.update x k u := by
      change Fin.insertNth k u y =
        Function.update (β := fun _ : Fin (n + 1) => ℝ) x k u
      rw [show x = Fin.insertNth k r y by rfl]
      exact (Fin.update_insertNth (α := fun _ : Fin (n + 1) => ℝ) k r u y).symm
    have hpoint := finiteChaos_laplace_score_hasDerivAt_linearImage_coordinate
      A a v γ s x i k
    have hfun : (fun u => G (T (e.symm (u, y)))) =
        (fun u => finiteChaosVectorWeight a v γ
          (finiteChaosLinearImageVector A (Function.update x k u)) i *
            (-s * Real.exp (-s * finiteChaosVectorMass a v γ
              (finiteChaosLinearImageVector A (Function.update x k u))))) := by
      funext u
      rw [hpath u]
      rfl
    have hcongr := hpoint.congr_of_eventuallyEq
      (Filter.EventuallyEq.of_eq hfun)
    have hcongr' := real_hasDerivAt_to_semiring_module hcongr
    simpa [e, x, hxk, G, D, T, finiteChaosLinearImageVector,
      MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, hLin] using hcongr'
  have hGmeas : Measurable G := by
    change Measurable (fun x => finiteChaosVectorWeight a v γ x i *
      (-s * Real.exp (-s * finiteChaosVectorMass a v γ x)))
    fun_prop [finiteChaosVectorWeight, finiteChaosVectorMass]
  have hDmeas : Measurable D := by
    apply measurable_pi_iff.mpr
    intro j
    by_cases hij : i = j
    · simp [D, hij]
      fun_prop [finiteChaosVectorWeight, finiteChaosVectorMass]
    · simp [D, hij]
      fun_prop [finiteChaosVectorWeight, finiteChaosVectorMass]
  have hGBound : ∀ x, ‖G (T x)‖ ≤ 1 := by
    intro x
    simpa [G, T] using
      finiteChaos_laplace_first_weight_bound a v γ s ha hs (T x) i
  have hDBound : ∀ x j, ‖D (T x) j‖ ≤ 5 * |γ| := by
    intro x j
    simpa [D, T] using
      finiteChaos_laplace_score_derivative_norm_le a v γ s ha hs (T x) i j
  simpa [T, G, D] using
    gaussianLinearImage_pi_integration_by_parts_of_bounded A G D hderiv
      hGmeas hDmeas 1 (5 * |γ|) hGBound hDBound i

/-- Conditional form of the Laplace-score IBP with a deterministic field shift. It is the
single-block identity used after fixing the other independent interpolation block. -/
theorem finiteChaos_laplace_score_shifted_standardGaussian_ibp
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (c a v : Fin (n + 1) → ℝ) (γ s : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hs : 0 ≤ s) (i : Fin (n + 1)) :
    ∫ x, (∑ k, A i k * x k) *
        (finiteChaosVectorWeight a v γ
          (fun j => ∑ k, A j k * x k + c j) i *
          (-s * Real.exp (-s * finiteChaosVectorMass a v γ
            (fun j => ∑ k, A j k * x k + c j))))
        ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) =
      ∑ j, (∑ k, A i k * A j k) *
        ∫ x,
          (γ * (if i = j then
              finiteChaosVectorWeight a v γ
                (fun l => ∑ k, A l k * x k + c l) i *
                (-s * Real.exp (-s * finiteChaosVectorMass a v γ
                  (fun l => ∑ k, A l k * x k + c l))) else 0) +
            γ * finiteChaosVectorWeight a v γ
              (fun l => ∑ k, A l k * x k + c l) i *
              finiteChaosVectorWeight a v γ
                (fun l => ∑ k, A l k * x k + c l) j *
                (s ^ 2 * Real.exp (-s * finiteChaosVectorMass a v γ
                  (fun l => ∑ k, A l k * x k + c l))))
          ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  let a' : Fin (n + 1) → ℝ := fun j => a j * Real.exp (γ * c j)
  have ha' : ∀ j, 0 ≤ a' j := by
    intro j
    exact mul_nonneg (ha j) (Real.exp_nonneg _)
  have hweight (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
      finiteChaosVectorWeight a' v γ
          (fun l => ∑ k, A l k * x k) j =
    finiteChaosVectorWeight a v γ
          (fun l => ∑ k, A l k * x k + c l) j := by
    simp only [finiteChaosVectorWeight, a']
    calc
      a j * Real.exp (γ * c j) * Real.exp
          (γ * ∑ k, A j k * x k - γ ^ 2 / 2 * v j) =
        a j * (Real.exp (γ * c j) * Real.exp
          (γ * ∑ k, A j k * x k - γ ^ 2 / 2 * v j)) := by ring
      _ = a j * Real.exp
          (γ * c j + (γ * ∑ k, A j k * x k - γ ^ 2 / 2 * v j)) := by
            rw [← Real.exp_add]
      _ = a j * Real.exp
          (γ * (∑ k, A j k * x k + c j) - γ ^ 2 / 2 * v j) := by
            congr 2
            ring
  have hmass (x : Fin (n + 1) → ℝ) :
      finiteChaosVectorMass a' v γ
          (fun l => ∑ k, A l k * x k) =
        finiteChaosVectorMass a v γ
          (fun l => ∑ k, A l k * x k + c l) := by
    unfold finiteChaosVectorMass
    apply Finset.sum_congr rfl
    intro j hj
    exact hweight x j
  simpa [hweight, hmass] using
    finiteChaos_laplace_score_standardGaussian_ibp A a' v γ s ha' hs i

end DOZZ.Proofs
