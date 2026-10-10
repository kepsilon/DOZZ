/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-! Factorization of nonnegative product integrals over finite product measures. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace DOZZ.Proofs

private theorem lintegral_fin_pi_prod
    {α : Type*} [MeasurableSpace α] {n : ℕ}
    (μ : Fin n → Measure α) (f : Fin n → α → ℝ≥0∞)
    (hμ : ∀ i, SigmaFinite (μ i)) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → α, ∏ i, f i (x i) ∂Measure.pi μ =
      ∏ i, ∫⁻ y, f i y ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      let μTail : Fin n → Measure α := fun i => μ i.succ
      let fTail : Fin n → α → ℝ≥0∞ := fun i => f i.succ
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0
      have hμTail (i : Fin n) : SigmaFinite (μTail i) := hμ i.succ
      have hfTail (i : Fin n) : Measurable (fTail i) := hf i.succ
      have htarget : Measurable (fun x : Fin (n + 1) → α => ∏ i, f i (x i)) := by
        fun_prop
      have hpair : Measurable (fun z : α × (Fin n → α) =>
          f 0 z.1 * ∏ i, f i.succ (z.2 i)) := by
        fun_prop
      have hform (z : α × (Fin n → α)) :
          (∏ i : Fin (n + 1), f i (e.symm z i)) =
            f 0 z.1 * ∏ i : Fin n, f i.succ (z.2 i) := by
        rw [Fin.prod_univ_succ]
        congr 1
      calc
        ∫⁻ x : Fin (n + 1) → α, ∏ i, f i (x i) ∂Measure.pi μ =
            ∫⁻ z : α × (Fin n → α),
              (∏ i : Fin (n + 1), f i (e.symm z i))
                ∂((μ 0).prod (Measure.pi μTail)) := by
              symm
              exact (measurePreserving_piFinSuccAbove μ 0).symm.lintegral_comp
                htarget
        _ = ∫⁻ z : α × (Fin n → α),
              f 0 z.1 * ∏ i : Fin n, f i.succ (z.2 i)
                ∂((μ 0).prod (Measure.pi μTail)) := by
              apply lintegral_congr_ae
              exact ae_of_all _ hform
        _ = ∫⁻ x, ∫⁻ y,
              f 0 x * ∏ i : Fin n, f i.succ (y i) ∂Measure.pi μTail ∂μ 0 := by
              exact lintegral_prod
                (fun z : α × (Fin n → α) => f 0 z.1 * ∏ i : Fin n, f i.succ (z.2 i))
                hpair.aemeasurable
        _ = ∫⁻ x, f 0 x * (∏ i : Fin n, ∫⁻ y, f i.succ y ∂μ i.succ) ∂μ 0 := by
              apply lintegral_congr_ae
              exact ae_of_all _ fun x => by
                change ∫⁻ y, f 0 x * ∏ i : Fin n, f i.succ (y i)
                    ∂Measure.pi μTail = _
                rw [lintegral_const_mul (f 0 x) (by fun_prop)]
                congr 1
                simpa [μTail, fTail] using ih μTail fTail hμTail hfTail
        _ = (∫⁻ x, f 0 x ∂μ 0) *
              ∏ i : Fin n, ∫⁻ y, f i.succ y ∂μ i.succ := by
              rw [lintegral_mul_const _ (hf 0)]
        _ = ∏ i : Fin (n + 1), ∫⁻ y, f i y ∂μ i := by
              rw [Fin.prod_univ_succ]

/-- The integral of a product of coordinatewise nonnegative functions over a finite product
measure factors into the product of the coordinate integrals. -/
theorem lintegral_pi_prod
    {α κ : Type*} [MeasurableSpace α] [Fintype κ]
    (μ : κ → Measure α) (f : κ → α → ℝ≥0∞)
    (hμ : ∀ i, SigmaFinite (μ i)) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : κ → α, ∏ i, f i (x i) ∂Measure.pi μ =
      ∏ i, ∫⁻ y, f i y ∂μ i := by
  classical
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let μ' : Fin (Fintype.card κ) → Measure α := fun i => μ (e i)
  let f' : Fin (Fintype.card κ) → α → ℝ≥0∞ := fun i => f (e i)
  have hμ' (i : Fin (Fintype.card κ)) : SigmaFinite (μ' i) := hμ (e i)
  have hf' (i : Fin (Fintype.card κ)) : Measurable (f' i) := hf (e i)
  have htarget : Measurable (fun x : κ → α => ∏ i, f i (x i)) := by fun_prop
  let pe := MeasurableEquiv.piCongrLeft (fun _ : κ => α) e
  have hstep := (measurePreserving_piCongrLeft (α := fun _ : κ => α) μ e).lintegral_comp htarget
  have hprod (x : Fin (Fintype.card κ) → α) :
      (∏ i : κ, f i (pe x i)) = ∏ i : Fin (Fintype.card κ), f (e i) (x i) := by
    calc
      (∏ i : κ, f i (pe x i)) =
          ∏ i : Fin (Fintype.card κ), f (e i) (pe x (e i)) := by
            symm
            exact Equiv.prod_comp e (fun i => f i (pe x i))
      _ = _ := by
            apply Finset.prod_congr rfl
            intro i hi
            simp [pe, MeasurableEquiv.piCongrLeft_apply_apply]
  calc
    ∫⁻ x : κ → α, ∏ i, f i (x i) ∂Measure.pi μ =
        ∫⁻ x : Fin (Fintype.card κ) → α, ∏ i : κ, f i (pe x i)
          ∂Measure.pi μ' := hstep.symm
    _ = ∫⁻ x : Fin (Fintype.card κ) → α, ∏ i, f (e i) (x i)
          ∂Measure.pi μ' := by
          apply lintegral_congr_ae
          exact ae_of_all _ hprod
    _ = ∏ i : Fin (Fintype.card κ), ∫⁻ y, f (e i) y ∂μ (e i) :=
          lintegral_fin_pi_prod μ' f' hμ' hf'
    _ = ∏ i : κ, ∫⁻ y, f i y ∂μ i := by
          exact Equiv.prod_comp e (fun i => ∫⁻ y, f i y ∂μ i)


end DOZZ.Proofs
