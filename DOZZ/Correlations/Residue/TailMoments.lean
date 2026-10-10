/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Complex.ComplexMomentUniformTailBridge
public import DOZZ.Statements.Complex.ComplexMomentTwoTailResidues

/-! Real positive-moment residues from the Mellin tail statements
`DOZZ.complexMoment_uniform_tail_bridge` and `DOZZ.complexMoment_two_tail_residues`. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The complex Abelian limit `DOZZ.complexMoment_uniform_tail_bridge` gives the real moment
residue, with the same uniform family and coefficient. No limiting-variable-only tail assumption
is substituted. -/
theorem residue_real_uniform_tail_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℝ → Ω → ℝ) (c : ℝ → ℝ) (c₀ β η γ d₀ C : ℝ)
    (hβ : 0 < β) (hη : 0 < η) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hC : 0 ≤ C)
    (hY : ∀ d, 0 < d → d < d₀ → AEMeasurable (Y d) P)
    (hpos : ∀ d, 0 < d → d < d₀ → ∀ᵐ ω ∂P, 0 ≤ Y d ω)
    (hc : Tendsto c (𝓝[>] 0) (𝓝 c₀))
    (htail : ∀ d (hd : 0 < d) (hd' : d < d₀) t, 1 ≤ t →
      |realUpperTail P (Y d) (hY d hd hd') t - c d * t ^ (-β)| ≤ C * t ^ (-β - η)) :
    Tendsto (fun d => d * ∫ ω, Y d ω ^ (β - d / γ) ∂P)
      (𝓝[>] 0) (𝓝 (γ * β * c₀)) := by
  have h := (complexMoment_uniform_tail_bridge P Y c c₀ β η γ d₀ C
    hβ hη hγ hd₀ hC hY hpos hc htail).2
  have hre := Complex.continuous_re.continuousAt.tendsto.comp h
  have hnear : ∀ᶠ d : ℝ in 𝓝[>] 0, 0 < d ∧ d < d₀ := by
    filter_upwards [self_mem_nhdsWithin, (Filter.eventually_of_mem (Iio_mem_nhds hd₀) (fun _ h => h)).filter_mono nhdsWithin_le_nhds] with d hd hd'
    exact ⟨hd, hd'⟩
  apply hre.congr'
  filter_upwards [hnear] with d hd
  have heq : (fun ω => (Y d ω : ℂ) ^ ((β - d / γ : ℝ) : ℂ)) =ᵐ[P]
      fun ω => ((Y d ω ^ (β - d / γ) : ℝ) : ℂ) :=
    (hpos d hd.1 hd.2).mono (fun ω hω => (Complex.ofReal_cpow hω _).symm)
  dsimp only [Function.comp_def]
  rw [integral_congr_ae heq, integral_complex_ofReal, ← Complex.ofReal_mul]
  rfl

/-- A finite extended mass has exactly the same upper tail as its real value. -/
theorem residue_realUpperTail_toReal
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ≥0∞) (hY : AEMeasurable Y P) (hfinite : ∀ᵐ ω ∂P, Y ω ≠ ⊤)
    (t : ℝ) (ht : 0 ≤ t) :
    realUpperTail P (fun ω => (Y ω).toReal) (ENNReal.measurable_toReal.comp_aemeasurable hY) t =
      (P {ω | ENNReal.ofReal t < Y ω}).toReal := by
  unfold realUpperTail
  congr 1
  apply measure_congr
  filter_upwards [hfinite] with ω hω
  exact propext (ENNReal.ofReal_lt_iff_lt_toReal ht hω).symm

end DOZZ.Proofs
