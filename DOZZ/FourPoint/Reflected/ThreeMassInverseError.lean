/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.ReflectedOuter.InverseDifference
/-! Removing the intermediate buffer costs its first-order retained-mass moment. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

theorem reflected_three_mass_inverse_error
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F I B O : Ω → ℝ≥0∞)
    (hF : AEMeasurable F P) (hI : AEMeasurable I P) (hO : AEMeasurable O P)
    (p : ℝ) (hp : 0 < p)
    (heq : ∀ᵐ ω ∂P, F ω = (I ω+O ω)+B ω)
    (hOf : ∀ᵐ ω ∂P, 0 < O ω) (hFf : ∀ᵐ ω ∂P, F ω ≠ ⊤)
    (hInv : (∫⁻ ω, O ω^(-p) ∂P) < ⊤)
    (hBuffer : (∫⁻ ω, B ω*O ω^(-(p+1)) ∂P) < ⊤) :
    |(∫⁻ ω, F ω^(-p) ∂P).toReal-(∫⁻ ω, (I ω+O ω)^(-p) ∂P).toReal| ≤
      p*(∫⁻ ω, B ω*O ω^(-(p+1)) ∂P).toReal := by
  let S := fun ω => I ω+O ω
  let R := fun ω => ENNReal.ofReal p*(B ω*O ω^(-(p+1)))
  have hS : AEMeasurable S P := hI.add hO
  have hFinv : (∫⁻ ω, F ω^(-p) ∂P) ≠ ⊤ := ne_top_of_le_ne_top hInv.ne
    (lintegral_mono_ae (heq.mono fun ω hω => by
      rw [hω]
      exact ennreal_rpow_antitone_of_nonpos
        ((le_add_left le_rfl : O ω ≤ I ω+O ω).trans le_self_add) (neg_nonpos.mpr hp.le)))
  have hSinv : (∫⁻ ω, S ω^(-p) ∂P) ≠ ⊤ := ne_top_of_le_ne_top hInv.ne
    (lintegral_mono fun ω => ennreal_rpow_antitone_of_nonpos
      (le_add_left le_rfl : O ω ≤ S ω) (neg_nonpos.mpr hp.le))
  have hR : (∫⁻ ω, R ω ∂P) = ENNReal.ofReal p*(∫⁻ ω, B ω*O ω^(-(p+1)) ∂P) :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hRfin : (∫⁻ ω, R ω ∂P) ≠ ⊤ := hR ▸ ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBuffer.ne
  have hFG : ∀ᵐ ω ∂P, F ω^(-p) ≤ S ω^(-p)+R ω := by
    filter_upwards [heq] with ω hω
    rw [hω]
    exact (ennreal_rpow_antitone_of_nonpos le_self_add (neg_nonpos.mpr hp.le)).trans
      le_self_add
  have hGF : ∀ᵐ ω ∂P, S ω^(-p) ≤ F ω^(-p)+R ω := by
    filter_upwards [heq,hOf,hFf] with ω he ho hf
    have hsfin : S ω ≠ ⊤ := ne_top_of_le_ne_top hf (he ▸ le_self_add)
    have hbfin : B ω ≠ ⊤ := ne_top_of_le_ne_top hf (he ▸ le_add_left le_rfl)
    have hsz : S ω ≠ 0 := ne_zero_of_lt (ho.trans_le (le_add_left le_rfl))
    have hb := reflected_ennreal_inverse_add_bound p hp (S ω) (B ω) hsz hsfin hbfin
    rw [← he] at hb
    apply hb.trans
    apply add_le_add_right
    have hpow := ennreal_rpow_antitone_of_nonpos (le_add_left le_rfl : O ω ≤ S ω)
      (by linarith only [hp] : -(p+1) ≤ 0)
    simpa only [R,mul_assoc] using mul_le_mul_right hpow (ENNReal.ofReal p*B ω)
  have h := reflected_lintegral_toReal_difference_bound P (fun ω => F ω^(-p))
    (fun ω => S ω^(-p)) R (hF.pow_const (-p)) (hS.pow_const (-p)) hFinv hSinv hRfin hFG hGF
  rw [hR,ENNReal.toReal_mul,ENNReal.toReal_ofReal hp.le] at h
  exact h

end DOZZ.Proofs
