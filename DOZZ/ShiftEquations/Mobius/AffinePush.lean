/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.TestFn
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.RingTheory.Complex

/-!
# Affine pushforward of test functions

For `a b : ℂ` the pushforward of a test function `f` by the affine map `y ↦ a y + b`, normalized
by the Jacobian `‖a‖²`, is the test function `x ↦ ‖a‖⁻² f ((x - b) / a)`. It is built as a
continuous linear map `TestFn →L[ℝ] TestFn` through the universal property of the inductive limit
topology: on the space of test functions supported in a compact set `K` it is a continuous linear
map into the test functions supported in the image of `K`, because the `i`-th derivative of the
pushforward is controlled by the `i`-th derivative of `f` with the factor `‖a⁻¹‖ ^ i`. For
`a = 0` the map is `0`. The change of variables `x = a y + b` scales Lebesgue measure on `ℂ` by
`‖a‖²`, which gives the duality identity
`∫ affinePushTestFn a b f * g = ∫ f * (g ∘ (a · + b))` without integrability hypotheses.
-/

@[expose] public section

open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff

namespace DOZZ.Proofs

/-- The affine homeomorphism `y ↦ a y + b` of the plane, for `a ≠ 0`. -/
noncomputable def affinePushHomeo (a b : ℂ) (ha : a ≠ 0) : ℂ ≃ₜ ℂ where
  toFun y := a * y + b
  invFun x := (x - b) / a
  left_inv y := by field_simp; ring
  right_inv x := by field_simp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The affine map `y ↦ a y + b` scales Lebesgue measure on the plane by `‖a‖²`, so the pushforward
of `volume` is `‖a‖⁻²` times `volume`. -/
theorem affinePush_map_volume (a b : ℂ) (ha : a ≠ 0) :
    Measure.map (fun y : ℂ => a * y + b) (volume : Measure ℂ) =
      ENNReal.ofReal (‖a‖ ^ 2)⁻¹ • volume := by
  have hdet : LinearMap.det (Algebra.lmul ℝ ℂ a : ℂ →ₗ[ℝ] ℂ) = ‖a‖ ^ 2 := by
    rw [← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
  have hpos : 0 < ‖a‖ ^ 2 := by positivity
  have hlin : Measure.map (fun y : ℂ => a * y) (volume : Measure ℂ) =
      ENNReal.ofReal (‖a‖ ^ 2)⁻¹ • volume := by
    have := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ)
      (f := (Algebra.lmul ℝ ℂ a : ℂ →ₗ[ℝ] ℂ)) (by rw [hdet]; exact hpos.ne')
    rw [hdet, abs_of_nonneg (inv_nonneg.mpr hpos.le)] at this
    exact this
  have hcomp : (fun y : ℂ => a * y + b) = (fun z : ℂ => z + b) ∘ (fun y : ℂ => a * y) := rfl
  rw [hcomp, ← Measure.map_map (measurable_add_const b) (measurable_const_mul a), hlin,
    Measure.map_smul _ (measurable_add_const b).aemeasurable,
    Measure.IsAddRightInvariant.map_add_right_eq_self (μ := volume) b]

/-- Change of variables for the affine map `y ↦ a y + b` on the plane, for every real function. -/
theorem affinePush_integral_comp (a b : ℂ) (ha : a ≠ 0) (G : ℂ → ℝ) :
    ∫ y, G (a * y + b) = (‖a‖ ^ 2)⁻¹ * ∫ x, G x := by
  have h := (affinePushHomeo a b ha).measurableEmbedding.integral_map (μ := volume) G
  have hφ : ⇑(affinePushHomeo a b ha) = fun y => a * y + b := rfl
  rw [hφ, affinePush_map_volume a b ha, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (by positivity)), smul_eq_mul] at h
  exact h.symm

/-- The `i`-th derivative of the pushforward `x ↦ ‖a‖⁻² f ((x - b) / a)` of a smooth function is
bounded by `‖a‖⁻² ‖a⁻¹‖ ^ i` times the `i`-th derivative of `f` at the pulled-back point. -/
theorem affinePush_norm_iteratedFDeriv_le (a b : ℂ) {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (i : ℕ)
    (x : ℂ) :
    ‖iteratedFDeriv ℝ i (fun x => (‖a‖ ^ 2)⁻¹ * f ((x - b) / a)) x‖ ≤
      (‖a‖ ^ 2)⁻¹ * ‖a⁻¹‖ ^ i * ‖iteratedFDeriv ℝ i f ((x - b) / a)‖ := by
  set L : ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ a⁻¹ with hL
  have hLapp : ∀ y, L y = y / a := fun y => by simp [hL, div_eq_inv_mul]
  have hfun : (fun x : ℂ => (‖a‖ ^ 2)⁻¹ * f ((x - b) / a)) =
      fun x => (‖a‖ ^ 2)⁻¹ • (f ∘ L) (x - b) := by
    funext x
    simp [hLapp]
  have hfL : ContDiff ℝ ∞ (f ∘ L) := hf.comp L.contDiff
  have hdiff : ContDiffAt ℝ i (fun z => (f ∘ L) (z - b)) x :=
    ((hfL.comp (contDiff_id.sub contDiff_const)).contDiffAt).of_le (by exact_mod_cast le_top)
  have h2 := L.iteratedFDeriv_comp_right hf (x - b) (i := i) (by exact_mod_cast le_top)
  rw [hfun, iteratedFDeriv_const_smul_apply' hdiff, iteratedFDeriv_comp_sub, h2, norm_smul,
    Real.norm_of_nonneg (by positivity), hLapp]
  calc
    (‖a‖ ^ 2)⁻¹ * ‖(iteratedFDeriv ℝ i f ((x - b) / a)).compContinuousLinearMap fun _ => L‖
        ≤ (‖a‖ ^ 2)⁻¹ * (‖iteratedFDeriv ℝ i f ((x - b) / a)‖ * ∏ _ : Fin i, ‖L‖) := by
          gcongr
          exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ (‖a‖ ^ 2)⁻¹ * (‖iteratedFDeriv ℝ i f ((x - b) / a)‖ * ‖a⁻¹‖ ^ i) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          gcongr
          exact ContinuousLinearMap.opNorm_mul_apply_le ℝ ℂ a⁻¹
    _ = (‖a‖ ^ 2)⁻¹ * ‖a⁻¹‖ ^ i * ‖iteratedFDeriv ℝ i f ((x - b) / a)‖ := by ring

/-- The image of a compact set `K` under the affine map `y ↦ a y + b`, as a compact set. -/
noncomputable def affinePushCompacts (a b : ℂ) (K : Compacts ℂ) : Compacts ℂ :=
  K.map (fun y : ℂ => a * y + b) (by fun_prop)

/-- The underlying set of `affinePushCompacts a b K` is the image of `K`. -/
theorem affinePushCompacts_coe (a b : ℂ) (K : Compacts ℂ) :
    (affinePushCompacts a b K : Set ℂ) = (fun y : ℂ => a * y + b) '' K :=
  Compacts.coe_map _ _

/-- A point outside the image of `K` has its pullback `(x - b) / a` outside `K`. -/
theorem affinePush_notMem_of_notMem_image (a b : ℂ) (ha : a ≠ 0) (K : Compacts ℂ) {x : ℂ}
    (hx : x ∉ (affinePushCompacts a b K : Set ℂ)) : (x - b) / a ∉ (K : Set ℂ) := by
  intro h
  refine hx ?_
  rw [affinePushCompacts_coe]
  refine ⟨(x - b) / a, h, ?_⟩
  field_simp
  ring

/-- Pushforward by `y ↦ a y + b` as a continuous linear map from the test functions supported in a
compact set `K` to those supported in the image of `K`. -/
noncomputable def affinePushSupportedCLM (a b : ℂ) (ha : a ≠ 0) (K : Compacts ℂ) :
    𝓓_{K}(ℂ, ℝ) →L[ℝ] 𝓓_{affinePushCompacts a b K}(ℂ, ℝ) :=
  ContDiffMapSupportedIn.mkCLM ℝ (fun f x => (‖a‖ ^ 2)⁻¹ * f ((x - b) / a))
    (fun f g x => by simp [mul_add])
    (fun c f x => by simp [mul_left_comm])
    (fun f => contDiff_const.mul (f.contDiff.comp ((contDiff_id.sub contDiff_const).div_const a)))
    (fun f x hx => by
      have := f.zero_on_compl (affinePush_notMem_of_notMem_image a b ha K hx)
      simp [this])
    (fun i _ => ⟨{i}, (‖a‖ ^ 2)⁻¹ * ‖a⁻¹‖ ^ i, by positivity, fun f x _ => by
      refine (affinePush_norm_iteratedFDeriv_le a b f.contDiff i x).trans ?_
      rw [Finset.sup_singleton]
      gcongr
      exact ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ⟩)

/-- The pushforward `x ↦ ‖a‖⁻² f ((x - b) / a)` of a test function, as a test function, for
`a ≠ 0`. -/
noncomputable def affinePushOfNeZero (a b : ℂ) (ha : a ≠ 0) (f : TestFn) : TestFn :=
  ⟨fun x => (‖a‖ ^ 2)⁻¹ * f ((x - b) / a),
    contDiff_const.mul (f.contDiff.comp ((contDiff_id.sub contDiff_const).div_const a)),
    (f.hasCompactSupport.comp_homeomorph (affinePushHomeo a b ha).symm).mul_left,
    fun _ _ => trivial⟩

/-- The pushforward by `y ↦ a y + b`, for `a ≠ 0`, as a continuous linear map of test functions. -/
noncomputable def affinePushTestFnAux (a b : ℂ) (ha : a ≠ 0) : TestFn →L[ℝ] TestFn :=
  TestFunction.limitCLM ℝ (affinePushOfNeZero a b ha)
    (fun K _ => TestFunction.ofSupportedInCLM ℝ (fun _ _ => trivial) ∘L
      affinePushSupportedCLM a b ha K)
    (fun _ _ _ => by ext x; rfl)

open scoped Classical in
/-- Pushforward of a test function by `y ↦ a y + b`, normalized by the Jacobian:
`(affinePushTestFn a b f) x = ‖a‖⁻² f((x - b)/a)` for `a ≠ 0` (and `0` for `a = 0`). -/
noncomputable def affinePushTestFn (a b : ℂ) : TestFn →L[ℝ] TestFn :=
  if ha : a = 0 then 0 else affinePushTestFnAux a b ha

/-- Pointwise formula for the pushforward of a test function by `y ↦ a y + b`, for `a ≠ 0`. -/
theorem affinePushTestFn_apply (a b : ℂ) (ha : a ≠ 0) (f : TestFn) (x : ℂ) :
    affinePushTestFn a b f x = (‖a‖ ^ 2)⁻¹ * f ((x - b) / a) := by
  have h : affinePushTestFn a b = affinePushTestFnAux a b ha := dite_eq_right ha
  rw [h]
  rfl


/-- Change of variables: pairing the pushforward with `g` is pairing `f` with `g ∘ (a · + b)`. -/
theorem integral_affinePushTestFn_mul (a b : ℂ) (ha : a ≠ 0) (f : TestFn) (g : ℂ → ℝ) :
    ∫ x, affinePushTestFn a b f x * g x = ∫ y, f y * g (a * y + b) := by
  have hc : (‖a‖ ^ 2)⁻¹ ≠ 0 := by positivity
  have h := affinePush_integral_comp a b ha (fun x => affinePushTestFn a b f x * g x)
  have hy : ∀ y, affinePushTestFn a b f (a * y + b) * g (a * y + b) =
      (‖a‖ ^ 2)⁻¹ * (f y * g (a * y + b)) := fun y => by
    rw [affinePushTestFn_apply a b ha, add_sub_cancel_right, mul_div_cancel_left₀ _ ha, mul_assoc]
  simp_rw [hy, integral_const_mul] at h
  exact (mul_left_cancel₀ hc h).symm


end DOZZ.Proofs

end
