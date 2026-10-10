/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Order.Interval.Set.Disjoint
public import GaussianFields.Ambient.Euclidean
public import GaussianFields.WhiteNoise.Isonormal

/-!
# GaussianFields ABK scale-space white noise

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped Convolution ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace GaussianFields


/-! ## Scale-space white noise -/

/-- The scale-space `R^{1+d}` used by the ABK construction. -/
abbrev ScaleSpace (d : Nat) := Vec (d + 1)

/-- The product-coordinate split `R^{1+d} ≃ R × R^d`, with coordinate `0` as scale. -/
@[expose]
noncomputable def scaleSpaceMeasurableEquiv (d : Nat) :
    ScaleSpace d ≃ᵐ ℝ × Vec d :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0

/-- The split into scale and spatial coordinates preserves Lebesgue volume. -/
theorem scaleSpaceMeasurePreserving (d : Nat) :
    MeasurePreserving (scaleSpaceMeasurableEquiv d) := by
  simpa [ScaleSpace, scaleSpaceMeasurableEquiv] using
    (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0)

/-- The scale coordinate in `R^{1+d}`. -/
@[expose]
def scaleCoord {d : Nat} (z : ScaleSpace d) : ℝ :=
  z 0

/-- The spatial coordinates in `R^{1+d}`. -/
@[expose]
def spaceCoord {d : Nat} (z : ScaleSpace d) : Vec d :=
  fun i => z (Fin.succ i)

@[simp]
theorem scaleSpaceMeasurableEquiv_fst {d : Nat} (z : ScaleSpace d) :
    (scaleSpaceMeasurableEquiv d z).1 = scaleCoord z :=
  rfl

@[simp]
theorem scaleSpaceMeasurableEquiv_snd {d : Nat} (z : ScaleSpace d) :
    (scaleSpaceMeasurableEquiv d z).2 = spaceCoord z :=
  rfl

/-- The deterministic Hilbert space for ABK scale-space white noise. -/
noncomputable abbrev ScaleSpaceWhiteNoiseHilbert (d : Nat) :=
  ScalarWhiteNoiseHilbert (d + 1)

/-- The concrete sample space for ABK scale-space white noise. -/
abbrev ScaleSpaceWhiteNoiseSpace (d : Nat) :=
  ScalarWhiteNoiseSpace (d + 1)

/-- The concrete probability measure for ABK scale-space white noise. -/
@[expose]
noncomputable def scaleSpaceWhiteNoiseMeasure (d : Nat) :
    Measure (ScaleSpaceWhiteNoiseSpace d) :=
  scalarWhiteNoiseMeasure (d + 1)

instance instIsProbabilityMeasure_scaleSpaceWhiteNoiseMeasure (d : Nat) :
    IsProbabilityMeasure (scaleSpaceWhiteNoiseMeasure d) := by
  rw [scaleSpaceWhiteNoiseMeasure]
  infer_instance

/-- White noise on `R^{1+d}`, reused from the concrete scalar white-noise construction. -/
@[expose]
noncomputable def scaleSpaceWhiteNoiseL2 (d : Nat) :
    ScaleSpaceWhiteNoiseHilbert d →ₗᵢ[ℝ] Lp ℝ 2 (scaleSpaceWhiteNoiseMeasure d) :=
  scalarWhiteNoiseL2 (d + 1)

@[simp]
theorem scaleSpaceWhiteNoiseL2_apply {d : Nat} (f : ScaleSpaceWhiteNoiseHilbert d) :
    scaleSpaceWhiteNoiseL2 d f = scalarWhiteNoiseL2 (d + 1) f :=
  rfl

theorem covariance_scaleSpaceWhiteNoiseL2 {d : Nat}
    (f g : ScaleSpaceWhiteNoiseHilbert d) :
    cov[scaleSpaceWhiteNoiseL2 d f, scaleSpaceWhiteNoiseL2 d g;
        scaleSpaceWhiteNoiseMeasure d] =
      ⟪f, g⟫_ℝ := by
  exact covariance_scalarWhiteNoiseL2 f g

/-! ## Deterministic ABK test data -/

/-- Mean-zero compact test functions used in the ABK log-correlated field construction. -/
structure MeanZeroTestFunction (d : Nat) where
  /-- The underlying scalar function. -/
  toFun : Vec d → ℝ
  /-- The test function is continuous. -/
  continuous : Continuous toFun
  /-- The test function has compact support. -/
  hasCompactSupport : HasCompactSupport toFun
  /-- The test function is integrable. -/
  integrable : Integrable toFun (volume : Measure (Vec d))
  /-- The test function is square-integrable. -/
  memLp_two : MemLp toFun 2 (volume : Measure (Vec d))
  /-- The test function has mean zero. -/
  integral_eq_zero : ∫ x, toFun x ∂(volume : Measure (Vec d)) = 0

namespace MeanZeroTestFunction

instance {d : Nat} : CoeFun (MeanZeroTestFunction d) (fun _ => Vec d → ℝ) where
  coe ψ := ψ.toFun

@[ext]
theorem ext {d : Nat} {ψ φ : MeanZeroTestFunction d} (h : ∀ x, ψ x = φ x) : ψ = φ := by
  cases ψ
  cases φ
  simp only [mk.injEq]
  exact funext h

end MeanZeroTestFunction

/-- A deterministic ABK cutoff.  The analytic estimates below use the compact support,
boundedness, radiality, and Lipschitz control encoded here. -/
structure ABKCutoff (d : Nat) where
  /-- The underlying cutoff function. -/
  toFun : Vec d → ℝ
  /-- The cutoff is continuous. -/
  continuous : Continuous toFun
  /-- The cutoff has compact support. -/
  hasCompactSupport : HasCompactSupport toFun
  /-- The cutoff is square-integrable. -/
  memLp_two : MemLp toFun 2 (volume : Measure (Vec d))
  /-- The support is contained in the Euclidean unit ball. -/
  support_subset_unitBall : Function.support toFun ⊆ {x | euclideanNorm x ≤ 1}
  /-- The cutoff is identically one on the Euclidean ball of radius `1 / 2`. -/
  eq_one_of_norm_le_half : ∀ x, euclideanNorm x ≤ (1 / 2 : ℝ) → toFun x = 1
  /-- The cutoff is bounded between zero and one. -/
  nonneg : ∀ x, 0 ≤ toFun x
  /-- The cutoff is bounded above by one. -/
  le_one : ∀ x, toFun x ≤ 1
  /-- The cutoff is radial. -/
  radial : ∀ x y, euclideanNorm x = euclideanNorm y → toFun x = toFun y
  /-- A global Lipschitz bound, enough for the large-scale mean-zero estimate. -/
  lipschitz : ∃ L, 0 ≤ L ∧
    ∀ x y, |toFun x - toFun y| ≤ L * euclideanNorm (x - y)

namespace ABKCutoff

instance {d : Nat} : CoeFun (ABKCutoff d) (fun _ => Vec d → ℝ) where
  coe ζ := ζ.toFun

end ABKCutoff

end GaussianFields

end
