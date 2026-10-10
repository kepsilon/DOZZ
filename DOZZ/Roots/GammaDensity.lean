/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Roots.ParameterNeighborhood
public import DOZZ.Roots.Normalization
import Mathlib.Topology.Instances.Irrational
import Mathlib.Topology.ClusterPt
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
/-! # Irrational-square density and pole-free gamma neighborhoods -/
@[expose] public section
open MeasureTheory Set Filter Topology
namespace DOZZ.Proofs
/-- Irrational squared parameters occur in every neighborhood of a positive gamma. -/
theorem roots_frequently_irrational_sq (γ : ℝ) (hγ : 0 < γ) :
    ∃ᶠ g : ℝ in nhds γ, Irrational (g ^ 2) := by
  rw [Filter.frequently_iff]
  intro V hV
  have ht : Tendsto Real.sqrt (nhds (γ ^ 2)) (nhds γ) := by
    have ht := Real.continuous_sqrt.tendsto (γ ^ 2)
    have he : Real.sqrt (γ ^ 2) = γ := Real.sqrt_sq hγ.le
    rw [he] at ht
    exact ht
  have hq : ∀ᶠ q : ℝ in nhds (γ ^ 2), Real.sqrt q ∈ V ∧ 0 ≤ q := by
    filter_upwards [ht.eventually hV, ((continuousAt_const.eventually_lt (show ContinuousAt (fun q : ℝ => q) (γ ^ 2) from continuousAt_id) (by positivity : (0 : ℝ) < γ ^ 2)))] with q hq hpos
    exact ⟨hq, hpos.le⟩
  have hi : ∃ᶠ q : ℝ in nhds (γ ^ 2), Irrational q :=
    mem_closure_iff_frequently.mp (dense_irrational (γ ^ 2))
  obtain ⟨q, hqi, hqV, hqpos⟩ := (hi.and_eventually hq).exists
  exact ⟨Real.sqrt q, hqV, by rwa [Real.sq_sqrt hqpos]⟩
/-- The zero-mode exponent is continuous as gamma varies away from zero. -/
theorem roots_sExp_gamma_continuousAt (γ a b c : ℝ) (hγ : γ ≠ 0) :
    ContinuousAt (fun g => sExp g a b c) γ := by
  unfold sExp
  exact (continuousAt_const.sub (continuousAt_const.mul (continuousAt_Q hγ))).div continuousAt_id hγ
/-- Avoidance of all Gamma poles persists locally at a pole-free triple. -/
theorem roots_poleFree_gamma_nhds (γ a b c : ℝ) (hγ : γ ≠ 0)
    (hs : ∀ n : ℕ, sExp γ a b c ≠ -(n : ℝ)) :
    ∀ᶠ g : ℝ in nhds γ, ∀ n : ℕ, sExp g a b c ≠ -(n : ℝ) := by
  have hS : ContinuousAt (fun g : ℝ => (sExp g a b c : ℂ)) γ :=
    Complex.continuous_ofReal.continuousAt.comp (roots_sExp_gamma_continuousAt γ a b c hγ)
  have hc : ContinuousAt (fun g : ℝ => (Complex.Gamma (sExp g a b c : ℂ))⁻¹) γ := by
    simpa only [Function.comp_def] using Complex.differentiable_one_div_Gamma.continuous.continuousAt.comp (f := fun g : ℝ => (sExp g a b c : ℂ)) hS
  have hΓ : (Complex.Gamma (sExp γ a b c : ℂ))⁻¹ ≠ 0 := inv_ne_zero
    (Complex.Gamma_ne_zero (fun n hn => hs n (Complex.ofReal_inj.mp
      (by simpa only [Complex.ofReal_neg, Complex.ofReal_natCast] using hn))))
  have he : ∀ᶠ g : ℝ in nhds γ, (Complex.Gamma (sExp g a b c : ℂ))⁻¹ ≠ 0 :=
    hc.eventually_ne hΓ
  filter_upwards [he] with g hg n hn
  apply hg
  rw [hn, Complex.ofReal_neg, Complex.ofReal_natCast, Complex.Gamma_neg_nat_eq_zero, inv_zero]
/-- The full structure constant is continuous in gamma at every finite extended triple. -/
theorem roots_structureConstant_gamma_continuousAt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : ℝ → Ω → Measure ℂ) (hX : IsEquatorGFF P X)
    (hM : ∀ g, 0 < g → g < 2 → IsGMCOf P X g (M g))
    (γ μ a b c : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα : ExtendedSeiberg3 γ a b c) (hs : ∀ n : ℕ, sExp γ a b c ≠ -(n : ℝ)) :
    ContinuousAt (fun g => structureConstant P (M g) g μ a b c) γ := by
  have hS := roots_sExp_gamma_continuousAt γ a b c hγ.ne'
  have hpow := (Real.continuous_const_rpow hμ.ne').continuousAt.comp hS.neg
  have hΓ := (Real.differentiableAt_Gamma hs).continuousAt.comp (f := fun g => sExp g a b c) hS
  have hm := roots_unitVolume_gamma_continuousAt P X M hX hM γ a b c hγ hγ2 hα
  simpa only [Function.comp_def, Pi.mul_def, Pi.neg_def, residue_structureConstant_eq_unitVolume] using (hpow.mul hΓ).mul hm
end DOZZ.Proofs
