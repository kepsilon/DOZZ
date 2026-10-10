/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Shift.RbarShift
public import DOZZ.Statements.Brownian.ReflectionR

/-!
# From the unit-volume shift to the full shift

With `p(z) = 2(Q - z)/γ`, the full coefficient is `R(z) = μ^{p(z)} Γ(-p(z)) p(z) R̄(z)`
([KRV, (deffullR)]). Since `p(z - γ/2) = p(z) + 1` and `Γ(-p) = (-p-1) Γ(-p-1)`, the unit-volume
shift `R̄(z - γ/2) = m(z) R̄(z)` with `m = p π / D` becomes the full shift
`R(z - γ/2) = -(μ π) R(z) / D(z)` wherever `p(z) ≠ -1`; no division by `D` is needed, so the
identity also holds where `D` vanishes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace DOZZ.Proofs

/-- The complexified reflection exponent `p(z) = 2(Q - z)/γ`. -/
noncomputable def reflectionExponentC (γ : ℝ) (z : ℂ) : ℂ := 2 * ((Q γ : ℂ) - z) / γ

/-- The full coefficient built from a unit-volume coefficient `G`. -/
noncomputable def reflectionRFromBar (γ μ : ℝ) (G : ℂ → ℂ) (z : ℂ) : ℂ :=
  (μ : ℂ) ^ reflectionExponentC γ z * Complex.Gamma (-reflectionExponentC γ z) *
    reflectionExponentC γ z * G z

theorem reflectionExponentC_ofReal (γ α : ℝ) :
    reflectionExponentC γ α = (reflectionExponent γ α : ℂ) := by
  unfold reflectionExponentC reflectionExponent
  push_cast
  ring

theorem reflectionExponentC_sub_half {γ : ℝ} (hγ : 0 < γ) (z : ℂ) :
    reflectionExponentC γ (z - γ / 2) = reflectionExponentC γ z + 1 := by
  unfold reflectionExponentC
  have hγ0 : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ.ne'
  field_simp
  ring

/-- **The full coefficient at a real charge.** -/
theorem reflectionRFromBar_ofReal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {γ μ : ℝ} (hμ : 0 < μ) {G : ℂ → ℂ} (α : ℝ) (B : Ω → BrownianPath × BrownianPath)
    (Z : Ω → Measure ℝ) (hG : G α = (reflectionBarR P γ α B Z : ℂ)) :
    reflectionRFromBar γ μ G α = (reflectionR P γ μ α B Z : ℂ) := by
  unfold reflectionRFromBar reflectionR
  rw [reflectionExponentC_ofReal, hG, ← Complex.ofReal_cpow hμ.le, ← Complex.ofReal_neg,
    Complex.Gamma_ofReal]
  push_cast
  ring

/-- **The full coefficient is meromorphic where the unit-volume one is.** -/
theorem meromorphicOn_reflectionRFromBar {γ μ : ℝ} (hμ : 0 < μ) {G : ℂ → ℂ} {U : Set ℂ}
    (hG : MeromorphicOn G U) : MeromorphicOn (reflectionRFromBar γ μ G) U := by
  intro z hz
  have hp : AnalyticAt ℂ (reflectionExponentC γ) z := by
    unfold reflectionExponentC
    fun_prop
  have hμ0 : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ.ne'
  have hpow : AnalyticAt ℂ (fun w => (μ : ℂ) ^ reflectionExponentC γ w) z := by
    have hd : Differentiable ℂ (fun w => (μ : ℂ) ^ reflectionExponentC γ w) := fun w =>
      (show DifferentiableAt ℂ (reflectionExponentC γ) w by
        unfold reflectionExponentC
        fun_prop).const_cpow (Or.inl hμ0)
    exact hd.analyticAt z
  have hΓ : MeromorphicAt (fun w => Complex.Gamma (-reflectionExponentC γ w)) z :=
    (Meromorphic.Gamma _).comp_analyticAt (g := fun w => -reflectionExponentC γ w) hp.neg
  exact ((hpow.meromorphicAt.mul hΓ).mul hp.meromorphicAt).mul (hG z hz)

/-- **The unit-volume shift gives the full shift**, off `p(z) = -1`. -/
theorem reflectionRFromBar_shift {γ μ : ℝ} (hγ : 0 < γ) (hμ : 0 < μ) {G : ℂ → ℂ} {w : ℂ}
    (hrel : G (w - (γ / 2 : ℝ)) = rbarShiftMultiplier γ w * G w)
    (hp : reflectionExponentC γ w + 1 ≠ 0) :
    reflectionRFromBar γ μ G (w - γ / 2) =
      -(μ * Real.pi : ℂ) * reflectionRFromBar γ μ G w /
        (lFun (-((γ : ℂ) ^ 2) / 4) * lFun ((γ : ℂ) * w / 2 - (γ : ℂ) ^ 2 / 4) *
          lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * w / 2)) := by
  have hμ0 : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ.ne'
  have hw : w - (γ : ℂ) / 2 = w - ((γ / 2 : ℝ) : ℂ) := by push_cast; ring
  unfold reflectionRFromBar
  rw [hw, hrel, ← hw, reflectionExponentC_sub_half hγ, Complex.cpow_add _ _ hμ0,
    Complex.cpow_one]
  have hΓ : Complex.Gamma (-reflectionExponentC γ w) =
      (-(reflectionExponentC γ w + 1)) * Complex.Gamma (-(reflectionExponentC γ w + 1)) := by
    rw [← Complex.Gamma_add_one _ (neg_ne_zero.mpr hp)]
    ring_nf
  rw [hΓ]
  unfold rbarShiftMultiplier
  rw [show 2 * ((Q γ : ℂ) - w) / γ = reflectionExponentC γ w from rfl]
  ring

end DOZZ.Proofs

end
