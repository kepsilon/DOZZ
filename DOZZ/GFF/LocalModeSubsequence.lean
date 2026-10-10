/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.CommonSubsequence
public import DOZZ.GFF.AELpSquareSummability
public import DOZZ.GFF.HaarDistributionPartial
public import DOZZ.GFF.TorusModeHS
public import Mathlib.Logic.Encodable.Pi

/-!
# DOZZ.GFF.LocalModeSubsequence

One deterministic subsequence of finite Haar distributions converges almost everywhere on every
mode in the countable family of local torus-box H² coordinates.
-/

@[expose] public section

open MeasureTheory Filter
open scoped InnerProductSpace Topology ENNReal NNReal

namespace DOZZ

/-- A local mode is a radius together with a real cosine or sine frequency. -/
abbrev GFFLocalModeIndex := ℕ × Sum (Fin 2 → ℤ) (Fin 2 → ℤ)

/-- The positive physical radius assigned to a natural-number local chart. -/
def gffLocalModeRadius (R : ℕ) : ℝ := (R : ℝ) + 1

/-- The physical side length of the torus box assigned to a local chart. -/
def gffLocalModeBoxSide (R : ℕ) : ℝ := 2 * gffLocalModeRadius R + 4

theorem gffLocalModeRadius_pos (R : ℕ) : 0 < gffLocalModeRadius R := by
  unfold gffLocalModeRadius
  positivity

/-- The normalized cosine coordinate of a local Fourier chart as a compactly supported test. -/
noncomputable def gffLocalCosSobolevModeTest (R : ℕ) (k : Fin 2 → ℤ) : TestFn := by
  exact (torusSobolevWeight k)⁻¹ • localTorusCosTest (gffLocalModeRadius R)
    (gffLocalModeBoxSide R) (gffLocalModeRadius_pos R) k

/-- The normalized sine coordinate of a local Fourier chart as a compactly supported test. -/
noncomputable def gffLocalSinSobolevModeTest (R : ℕ) (k : Fin 2 → ℤ) : TestFn := by
  exact (torusSobolevWeight k)⁻¹ • localTorusSinTest (gffLocalModeRadius R)
    (gffLocalModeBoxSide R) (gffLocalModeRadius_pos R) k

/-- The H²-normalized compactly supported real trigonometric mode for an index. -/
noncomputable def gffLocalSobolevModeTest (i : GFFLocalModeIndex) : TestFn := by
  cases i.2 with
  | inl k => exact gffLocalCosSobolevModeTest i.1 k
  | inr k => exact gffLocalSinSobolevModeTest i.1 k

private noncomputable def gffLocalModeIndexOfNat (n : ℕ) : GFFLocalModeIndex :=
  (Encodable.decode n).getD default

private theorem gffLocalModeIndexOfNat_encode (i : GFFLocalModeIndex) :
    gffLocalModeIndexOfNat (Encodable.encode i) = i := by
  simp [gffLocalModeIndexOfNat]

/-- A summable deterministic energy family gives almost-sure square summability of its white-noise
evaluations. -/
theorem ae_summable_equatorWhiteNoiseSq_of_summable_energy {ι : Type*} [Countable ι]
    (t : ι → TestFn)
    (henergy : Summable fun i => ‖equatorKernelLimitMap (t i)‖ ^ 2) :
    ∀ᵐ ω ∂GaussianFields.scalarWhiteNoiseMeasure 3,
      Summable fun i =>
        (GaussianFields.scalarWhiteNoiseL2 3 (equatorKernelLimitMap (t i)) ω) ^ 2 := by
  let μ := GaussianFields.scalarWhiteNoiseMeasure 3
  let W : ι → Lp ℝ 2 μ := fun i =>
    GaussianFields.scalarWhiteNoiseL2 3 (equatorKernelLimitMap (t i))
  let eNN : ι → ℝ≥0 := fun i => ‖equatorKernelLimitMap (t i)‖₊ ^ 2
  have hNN : Summable eNN := by
    apply NNReal.summable_coe.1
    convert henergy using 1
    ext i
    simp [eNN]
  have hfiniteNN : (∑' i, (eNN i : ℝ≥0∞)) ≠ ∞ :=
    ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr (NNReal.summable_coe.2 hNN)
  have hnorm (i : ι) : eLpNorm (W i) 2 μ = ENNReal.ofReal
      ‖equatorKernelLimitMap (t i)‖ := by
    calc
      eLpNorm (W i) 2 μ = ENNReal.ofReal (ENNReal.toReal (eLpNorm (W i) 2 μ)) := by
        symm
        exact ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (W i))
      _ = ENNReal.ofReal ‖W i‖ := by rw [Lp.norm_def]
      _ = ENNReal.ofReal ‖equatorKernelLimitMap (t i)‖ := by simp [W]
  have hmoment (i : ι) :
    eLpNorm (fun ω => (W i ω) ^ 2) 1 μ = (eNN i : ℝ≥0∞) := by
    rw [eLpNorm_sq_eq_eLpNorm_two_sq (fun ω => W i ω)
      (Lp.aestronglyMeasurable (W i)), hnorm]
    simp [eNN, enorm_eq_nnnorm]
  have hfinite :
      ∑' i, eLpNorm (fun ω => (W i ω) ^ 2) 1 μ ≠ ∞ := by
    rw [show (∑' i, eLpNorm (fun ω => (W i ω) ^ 2) 1 μ) =
      ∑' i, (eNN i : ℝ≥0∞) from tsum_congr hmoment]
    exact hfiniteNN
  have hae := ae_summable_sq_of_tsum_eLpNorm_sq_ne_top
    (fun i ω => W i ω) hfinite
  simpa [W] using hae

/-- The local cosine-mode white-noise coefficients are square summable almost everywhere. -/
theorem ae_summable_gffLocalCosSobolevModeEvaluation (R : ℕ) :
    ∀ᵐ ω ∂GaussianFields.scaleSpaceWhiteNoiseMeasure 2,
      Summable fun k : Fin 2 → ℤ =>
        (GaussianFields.scalarWhiteNoiseL2 3
          (equatorKernelLimitMap (gffLocalCosSobolevModeTest R k)) ω) ^ 2 := by
  have h := ae_summable_equatorWhiteNoiseSq_of_summable_energy
    (gffLocalCosSobolevModeTest R)
    (summable_localTorusCosHSEnergy (gffLocalModeRadius R)
      (gffLocalModeBoxSide R) (gffLocalModeRadius_pos R))
  simpa [GaussianFields.scaleSpaceWhiteNoiseMeasure,
    GaussianFields.scalarWhiteNoiseMeasure] using h

/-- The local sine-mode white-noise coefficients are square summable almost everywhere. -/
theorem ae_summable_gffLocalSinSobolevModeEvaluation (R : ℕ) :
    ∀ᵐ ω ∂GaussianFields.scaleSpaceWhiteNoiseMeasure 2,
      Summable fun k : Fin 2 → ℤ =>
        (GaussianFields.scalarWhiteNoiseL2 3
          (equatorKernelLimitMap (gffLocalSinSobolevModeTest R k)) ω) ^ 2 := by
  have h := ae_summable_equatorWhiteNoiseSq_of_summable_energy
    (gffLocalSinSobolevModeTest R)
    (summable_localTorusSinHSEnergy (gffLocalModeRadius R)
      (gffLocalModeBoxSide R) (gffLocalModeRadius_pos R))
  simpa [GaussianFields.scaleSpaceWhiteNoiseMeasure,
    GaussianFields.scalarWhiteNoiseMeasure] using h

/-- The finite Haar truncations have a common almost-surely convergent subsequence on all local
H² modes. The index is countable (`ℕ × Sum (ℤ²) (ℤ²)`), and each coordinate converges in measure by
the G4 isometry. -/
theorem equatorHaarPartial_exists_common_localMode_subseq :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ ω ∂GaussianFields.scaleSpaceWhiteNoiseMeasure 2,
        ∀ i : GFFLocalModeIndex,
          Tendsto
            (fun n => equatorHaarPartialDistribution
              (GaussianFields.gaussianIndexTruncation
                (GaussianFields.HaarBasisIndex 3) (ns n))
              ω (gffLocalSobolevModeTest i))
            atTop
            (𝓝 (GaussianFields.scalarWhiteNoiseL2 3
              (equatorKernelLimitMap (gffLocalSobolevModeTest i)) ω)) := by
  let μ := GaussianFields.gaussianSequenceMeasure
    (GaussianFields.HaarBasisIndex 3)
  let F : ℕ → ℕ → GaussianFields.ScaleSpaceWhiteNoiseSpace 2 → ℝ := fun n j ω =>
    equatorHaarPartialDistribution
      (GaussianFields.gaussianIndexTruncation
        (GaussianFields.HaarBasisIndex 3) n)
      ω (gffLocalSobolevModeTest (gffLocalModeIndexOfNat j))
  let g : ℕ → GaussianFields.ScaleSpaceWhiteNoiseSpace 2 → ℝ := fun j ω =>
    GaussianFields.scalarWhiteNoiseL2 3
      (equatorKernelLimitMap (gffLocalSobolevModeTest (gffLocalModeIndexOfNat j))) ω
  have hF : ∀ j, TendstoInMeasure μ (fun n ω => F n j ω) atTop (g j) := by
    intro j
    simpa [F, g, μ] using
      equatorHaarPartialEvaluation_tendstoInMeasure
        (gffLocalSobolevModeTest (gffLocalModeIndexOfNat j))
  obtain ⟨ns, hns, hae⟩ := exists_common_subseq_tendsto_ae μ F g hF
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hae] with ω hω
  intro i
  simpa [F, g, gffLocalModeIndexOfNat_encode] using hω (Encodable.encode i)


end DOZZ

end
