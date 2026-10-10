/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Continuity.ProbabilityLimit
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The exponent of the normalized insertion moment in the two sphere charts. -/
noncomputable def continuityCoulombPower {N : ℕ} (c : ContinuityCoulombParameter N) : ℝ :=
  (2 * Q c.1 - (∑ k, c.2.2.1 k + c.2.2.2)) / c.1

/-- A uniform higher moment preserves expectations when both the nonnegative
random base and the real power vary, including through power zero. -/
theorem continuity_integral_varying_power
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ≥0∞) (g : Ω → ℝ≥0∞) (p : ℕ → ℝ) (p₀ : ℝ)
    (hf : ∀ n, AEMeasurable (f n) P) (hg : AEMeasurable g P)
    (hfp : ∀ n, ∀ᵐ ω ∂P, f n ω ^ p n ≠ ⊤)
    (hgfin : ∀ᵐ ω ∂P, g ω ≠ ⊤) (hgpos : ∀ᵐ ω ∂P, g ω ≠ 0)
    (hconv : TendstoInMeasure P (fun n ω => (f n ω).toReal) atTop
      (fun ω => (g ω).toReal)) (hp : Tendsto p atTop (𝓝 p₀))
    (η : ℝ) (hη : 0 < η) (B : ℝ≥0∞) (hB : B < ⊤)
    (hbound : ∀ n, ∫⁻ ω, f n ω ^ ((1 + η) * p n) ∂P ≤ B) :
    Tendsto (fun n => (∫⁻ ω, f n ω ^ p n ∂P).toReal) atTop
      (𝓝 (∫⁻ ω, g ω ^ p₀ ∂P).toReal) := by
  have hF : ∀ n, AEStronglyMeasurable (fun ω => (f n ω ^ p n).toReal) P :=
    fun n => ((hf n).pow_const (p n)).ennreal_toReal.aestronglyMeasurable
  have hnorm : ∀ n, ∫⁻ ω, ‖(f n ω ^ p n).toReal‖ₑ ^ (1 + η) ∂P ≤ B := by
    intro n
    refine (le_of_eq (lintegral_congr_ae ?_)).trans (hbound n)
    filter_upwards [hfp n] with ω hω
    rw [Real.enorm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hω,
      ← ENNReal.rpow_mul, mul_comm (p n)]
  have hgp : ∀ᵐ ω ∂P, g ω ^ p₀ ≠ ⊤ := by
    filter_upwards [hgfin, hgpos] with ω hfin hpos
    exact ENNReal.rpow_ne_top_of_ne_zero hpos hfin
  obtain ⟨_hint, hlim⟩ := gmc_integral_limit_of_higher_moment P
    (fun n ω => (f n ω ^ p n).toReal) (fun ω => (g ω ^ p₀).toReal) hF
    (continuity_tendstoInMeasure_varying_rpow P f g p p₀ hf hgfin hgpos hconv hp)
    (1 + η) (by linarith) B hB hnorm
  have hn (n : ℕ) : (∫⁻ ω, f n ω ^ p n ∂P).toReal = ∫ ω, (f n ω ^ p n).toReal ∂P :=
    (integral_toReal ((hf n).pow_const (p n))
      ((hfp n).mono fun _ h => h.lt_top)).symm
  have hg' : (∫⁻ ω, g ω ^ p₀ ∂P).toReal = ∫ ω, (g ω ^ p₀).toReal ∂P :=
    (integral_toReal (hg.pow_const p₀) (hgp.mono fun _ h => h.lt_top)).symm
  simpa only [hn, hg'] using hlim

/-- The uniform higher cutoff moment passes to the actual singular masses.
Each parameter keeps its own Seiberg power; the bound is common over the compact set. -/
theorem continuity_coulomb_higher_moment
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (M : ℝ → Ω → Measure ℂ)
    (hM : ∀ γ ∈ Ioo (0 : ℝ) 2, IsGMCOf P X γ (M γ))
    (S : Set (ContinuityCoulombParameter N)) (hS : IsCompact S)
    (hadm : ∀ c ∈ S, 0 < c.1 ∧ c.1 < 2 ∧ Function.Injective c.2.1 ∧
      (∀ k, c.2.2.1 k < Q c.1) ∧ c.2.2.2 < Q c.1 ∧
      continuityCoulombPower c < 4 / c.1 ^ 2 ∧
      (∀ k, continuityCoulombPower c < 2 / c.1 * (Q c.1 - c.2.2.1 k)) ∧
      continuityCoulombPower c < 2 / c.1 * (Q c.1 - c.2.2.2)) :
    ∃ η : ℝ, 0 < η ∧ ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ c ∈ S,
      ∫⁻ ω, (coulombMass c.1 (M c.1 ω) c.2.2.1 c.2.1 c.2.2.2) ^
        ((1 + η) * continuityCoulombPower c) ∂P ≤ B := by
  let _ : IsProbabilityMeasure P := hX.1
  let partition := continuityChartPartition
  obtain ⟨hprob, η, hη, B, hB, hbound⟩ := equatorGFF_extendedSeiberg_cutoff_UI P X hX Xc hXc
    partition M hM S hS hadm
  refine ⟨η, hη, B, hB, fun c hc => ?_⟩
  obtain ⟨hγ, hγ2, hz, hα, hinf, _⟩ := hadm c hc
  have hMc := hM c.1 ⟨hγ, hγ2⟩
  have hfin := continuity_coulombMass_positive_finite_ae P X hX c.1 hγ hγ2 (M c.1)
    hMc c.2.1 hz c.2.2.1 c.2.2.2 hα hinf
  have hconv : TendstoInMeasure P
      (fun r ω => (regularizedCoulombMass P Xc c.1 partition c.2.2.1 c.2.1 c.2.2.2 r ω).toReal)
      atTop (fun ω => (coulombMass c.1 (M c.1 ω) c.2.2.1 c.2.1 c.2.2.2).toReal) := by
    intro ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hprob ε hε)
      (fun _ => zero_le) (fun r => le_iSup_of_le c (le_iSup_of_le hc le_rfl))
  exact momentConv_lintegral_rpow_limit_le P
    (fun n : ℕ => regularizedCoulombMass P Xc c.1 partition c.2.2.1 c.2.1 c.2.2.2 n)
    (fun ω => coulombMass c.1 (M c.1 ω) c.2.2.1 c.2.1 c.2.2.2)
    (fun n => (continuity_regularizedCoulombMass_measurable P X hX Xc hXc partition n c).aemeasurable)
    (fun n => continuity_regularizedCoulombMass_finite_ae P X hX Xc hXc partition n c)
    (hfin.mono fun _ h => h.2) (hconv.comp tendsto_natCast_atTop_atTop)
    ((1 + η) * continuityCoulombPower c) B (fun n => hbound c hc n (Nat.cast_nonneg n))

/-- Full joint continuity of the actual normalized Coulomb moment on compact
strict parameter sets, uniformly dominated by the cutoff estimate
`DOZZ.equatorGFF_extendedSeiberg_cutoff_UI`. -/
theorem continuity_coulomb_moment_on_compact
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (M : ℝ → Ω → Measure ℂ)
    (hM : ∀ γ ∈ Ioo (0 : ℝ) 2, IsGMCOf P X γ (M γ))
    (S : Set (ContinuityCoulombParameter N)) (hS : IsCompact S)
    (hadm : ∀ c ∈ S, 0 < c.1 ∧ c.1 < 2 ∧ Function.Injective c.2.1 ∧
      (∀ k, c.2.2.1 k < Q c.1) ∧ c.2.2.2 < Q c.1 ∧
      continuityCoulombPower c < 4 / c.1 ^ 2 ∧
      (∀ k, continuityCoulombPower c < 2 / c.1 * (Q c.1 - c.2.2.1 k)) ∧
      continuityCoulombPower c < 2 / c.1 * (Q c.1 - c.2.2.2)) :
    ContinuousOn (fun c => (∫⁻ ω,
      (coulombMass c.1 (M c.1 ω) c.2.2.1 c.2.1 c.2.2.2) ^ continuityCoulombPower c ∂P).toReal) S := by
  let _ : IsProbabilityMeasure P := hX.1
  obtain ⟨η, hη, B, hB, hb⟩ := continuity_coulomb_higher_moment P X hX Xc hXc M hM S hS hadm
  let G : S → Ω → ℝ≥0∞ := fun c ω => coulombMass c.val.1 (M c.val.1 ω)
    c.val.2.2.1 c.val.2.1 c.val.2.2.2
  let p : S → ℝ := fun c => continuityCoulombPower c.val
  have hm : ∀ c : S, AEMeasurable (G c) P := fun c =>
    gmc_coulombMass_aemeasurable P X hX c.val.1 (hadm c.val c.property).1
      (hadm c.val c.property).2.1 _ (hM _ ⟨(hadm c.val c.property).1,
        (hadm c.val c.property).2.1⟩) _ _ _
  have hf : ∀ c : S, ∀ᵐ ω ∂P, 0 < G c ω ∧ G c ω ≠ ⊤ := fun c =>
    continuity_coulombMass_positive_finite_ae P X hX _ (hadm c.val c.property).1
      (hadm c.val c.property).2.1 _ (hM _ ⟨(hadm c.val c.property).1,
        (hadm c.val c.property).2.1⟩) _ (hadm c.val c.property).2.2.1 _ _
      (hadm c.val c.property).2.2.2.1 (hadm c.val c.property).2.2.2.2.1
  have hp : Continuous p := by
    unfold p continuityCoulombPower Q
    fun_prop (disch := intro c; exact (hadm c.val c.property).1.ne')
  rw [continuousOn_iff_continuous_domRestrict, continuous_iff_seqContinuous]
  intro cs c₀ hcs
  apply continuity_integral_varying_power P (fun n => G (cs n)) (G c₀) (fun n => p (cs n)) (p c₀)
    (fun n => hm (cs n)) (hm c₀)
  · intro n
    filter_upwards [hf (cs n)] with ω hω
    exact ENNReal.rpow_ne_top_of_ne_zero hω.1.ne' hω.2
  · exact (hf c₀).mono fun _ h => h.2
  · exact (hf c₀).mono fun _ h => h.1.ne'
  · exact (coulombMass_continuous_in_measure_on_compact P X hX Xc hXc M hM S hS
      (fun c hc => ⟨(hadm c hc).1, (hadm c hc).2.1, (hadm c hc).2.2.1,
        (hadm c hc).2.2.2.1, (hadm c hc).2.2.2.2.1⟩) c₀).comp hcs
  · exact (hp.tendsto c₀).comp hcs
  · exact hη
  · exact hB
  · exact fun n => hb (cs n).val (cs n).property

end DOZZ.Proofs
