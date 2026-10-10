/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.NormalizedCutoffIdentity
public import DOZZ.Correlations.Analytic.NormalizedIncrementTilt

/-! The analytic observable increment is controlled by the actual retained mass increment. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- Holomorphic uniqueness aligns the vertex cutoffs, after which the integral norm inequality
and real Gaussian tilt give the literal Coulomb mass-power increment. -/
theorem normalized_cutoff_increment_norm_le
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (z : Fin N → ℂ) (r s : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s)
    (O₀ O₁ : Set ℂ) (ho₀ : IsOpen O₀) (hb₀ : Bornology.IsBounded O₀) (hn₀ : O₀.Nonempty)
    (ho₁ : IsOpen O₁) (hb₁ : Bornology.IsBounded O₁) (hn₁ : O₁.Nonempty)
    (hO₀ : O₀ ⊆ retainedRegion z r) (hO₁ : O₁ ⊆ retainedRegion z s)
    (a R : Fin (N + 1) → ℝ) (hR : ∀ i, 0 < R i)
    (hbulk : ∀ β ∈ complexPolydisc (fun i => (a i : ℂ)) R,
      (complexMomentPower γ β).re < 4 / γ ^ 2)
    (β : Fin (N + 1) → ℂ) (hβ : β ∈ complexPolydisc (fun i => (a i : ℂ)) R) :
    let b := fun i => (β i).re
    let L := fun ω => ∑ i, b i * Xc ω (mixedVertexCenters z i) (mixedVertexTimes N s i)
    let p := complexMomentPower γ β
    let A := γ * ∑ i, b i.castSucc * equatorCircleMean (z i) s
    ENNReal.ofReal ‖normalizedVertexMoment P Xc M O₁ γ z s β -
      normalizedVertexMoment P Xc M O₀ γ z r β‖ ≤
      ENNReal.ofReal (Real.exp ((normalizedVertexPolynomial P Xc γ z s β).re +
        gaussianVariance P L / 2 + A * p.re)) *
        ∫⁻ ω, ENNReal.ofReal
          ‖((∫⁻ x in O₁, coulombWeight γ (fun i => b i.castSucc) z (b (Fin.last N)) x ∂M ω).toReal : ℂ) ^ p -
            ((∫⁻ x in O₀, coulombWeight γ (fun i => b i.castSucc) z (b (Fin.last N)) x ∂M ω).toReal : ℂ) ^ p‖ ∂P := by
  dsimp only
  have he := normalized_vertex_fixed_region_eqOn P X hX γ hγ hγ2 M hM Xc hc
    z r s hr hrs O₀ ho₀ hb₀ hn₀ hO₀ a R hR hbulk hβ
  rw [← he]
  have h₀ := (normalized_vertex_moment_holomorphic P X hX γ hγ hγ2 M hM Xc hc
    O₀ ho₀ hb₀ hn₀ z s).1 β (hbulk β hβ)
  have h₁ := (normalized_vertex_moment_holomorphic P X hX γ hγ hγ2 M hM Xc hc
    O₁ ho₁ hb₁ hn₁ z s).1 β (hbulk β hβ)
  let F (O : Set ℂ) (ω : Ω) := Complex.exp (normalizedVertexPolynomial P Xc γ z s β +
    ∑ i, β i * (Xc ω (mixedVertexCenters z i) (mixedVertexTimes N s i) : ℂ)) *
    ((M ω O).toReal : ℂ) ^ complexMomentPower γ β
  change ENNReal.ofReal ‖(∫ ω, F O₁ ω ∂P) - (∫ ω, F O₀ ω ∂P)‖ ≤ _
  rw [← integral_sub h₁ h₀]
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal ‖F O₁ ω - F O₀ ω‖ ∂P := by
      simpa only [ofReal_norm] using
        enorm_integral_le_lintegral_enorm (fun ω => F O₁ ω - F O₀ ω)
    _ = _ := by
      simp only [F, ← mul_sub]
      exact normalized_vertex_increment_tilt_norm P X hX γ hγ hγ2 M hM Xc hc
        β z s (hr.trans hrs) O₁ O₀ ho₁.measurableSet ho₀.measurableSet hO₁
          (hO₀.trans (retainedRegion_mono z hrs))

end DOZZ.Proofs
