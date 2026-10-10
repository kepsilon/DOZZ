module

public import DOZZ.GMC.MomentAnnularSummability

/-! Sharp-domain algebra for the dyadic weighted annulus argument. -/

@[expose] public section

open scoped ENNReal

namespace DOZZ.Proofs

/-- Strict slack in the positive weighted moment range makes the annular scaling exponent
positive. -/
theorem weightedGmcMomentExponent_pos_of_sharp_range
    {γ α p : ℝ} (hγ : 0 < γ) (hp : 0 < p)
    (hpRange : p < min (4 / γ ^ 2) (2 / γ * (Q γ - α))) :
    0 < γ * (Q γ - α) * p - γ ^ 2 * p ^ 2 / 2 := by
  have hpInsert : p < 2 * (Q γ - α) / γ := by
    calc
      p < 2 / γ * (Q γ - α) := (lt_min_iff.mp hpRange).2
      _ = 2 * (Q γ - α) / γ := by ring
  exact (weightedGmcMomentExponent_pos_iff hγ hp).2 hpInsert


end DOZZ.Proofs
