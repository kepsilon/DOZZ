/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.MomentConvergence
public import DOZZ.GMC.SharpMoments.LocationTransfer

/-! The real-limit passage for increasing retained regions. -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- Increasing retained masses converge in every fixed real moment for which the appropriate
endpoint envelope is finite: the full mass for positive powers and the first retained mass for
negative powers. -/
theorem retained_mass_moment_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ≥0∞) (g : Ω → ℝ≥0∞) (p : ℝ)
    (hf : ∀ n, AEMeasurable (f n) P)
    (horder : ∀ᵐ ω ∂P, ∀ n, f 0 ω ≤ f n ω ∧ f n ω ≤ g ω)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hpos : 0 ≤ p → (∫⁻ ω, g ω ^ p ∂P) < ⊤)
    (hneg : p < 0 → (∫⁻ ω, f 0 ω ^ p ∂P) < ⊤) :
    Tendsto (fun n => ∫⁻ ω, f n ω ^ p ∂P) atTop (𝓝 (∫⁻ ω, g ω ^ p ∂P)) := by
  let bound : Ω → ℝ≥0∞ := fun ω => if 0 ≤ p then g ω ^ p else f 0 ω ^ p
  apply tendsto_lintegral_of_dominated_convergence' (F := fun n ω => f n ω ^ p)
    (μ := P) bound
  · exact fun n => (hf n).pow_const p
  · intro n
    filter_upwards [horder] with ω hω
    dsimp [bound]
    split_ifs with hp
    · exact ENNReal.rpow_le_rpow (hω n).2 hp
    · exact ennreal_rpow_antitone_of_nonpos (hω n).1 (lt_of_not_ge hp).le
  · by_cases hp : 0 ≤ p
    · simpa only [bound, ite_eq_left hp] using (hpos hp).ne
    · simpa only [bound, ite_eq_right hp] using (hneg (lt_of_not_ge hp)).ne
  · filter_upwards [hlim] with ω hω
    exact ENNReal.continuous_rpow_const.continuousAt.tendsto.comp hω

end DOZZ.Proofs
