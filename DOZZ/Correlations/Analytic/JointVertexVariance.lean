/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.MixedRadiusTiltPotential
import DOZZ.GMC.Assembly.AdmissibleGMC

/-! Full covariance expansion of the real joint Wick polynomial. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- Joint variance is the quadratic form of the full raw covariance matrix. -/
theorem vertex_variance_expansion
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) (L : I → Ω → ℝ) (hL : ∀ i, MemLp (L i) 2 P) (a : I → ℝ) :
    gaussianVariance P (fun ω => ∑ i, a i * L i ω) =
      ∑ i, ∑ j, a i * a j * gaussianCovariance P (L i) (L j) := by
  classical
  let Z (i : I) (ω : Ω) := a i * L i ω
  have hm (i : I) : MemLp (Z i) 2 P := (hL i).const_mul (a i)
  have hs : MemLp (fun ω => ∑ i, Z i ω) 2 P :=
    memLp_finsetSum Finset.univ (fun i _ => hm i)
  change gaussianCovariance P (fun ω => ∑ i, Z i ω) (fun ω => ∑ i, Z i ω) = _
  rw [gaussianCovariance_finset_sum_right P _ Z Finset.univ hs (fun i _ => hm i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [DOZZ.Assembly.gaussianCovariance_comm,
    gaussianCovariance_finset_sum_right P (Z i) Z Finset.univ (hm i) (fun j _ => hm j)]
  apply Finset.sum_congr rfl
  intro j _
  unfold gaussianCovariance
  have he : (fun ω => Z i ω * Z j ω) =
      fun ω => (a i * a j) * (L i ω * L j ω) := by
    funext ω
    dsimp only [Z]
    ring
  rw [he, integral_const_mul]

end DOZZ.Proofs
