/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.SumTail.OneTail
public import DOZZ.Correlations.SumTail.Sandwich
public import DOZZ.Correlations.SumTail.ExtendedEvents
public import DOZZ.Statements.Correlations.SeparatedSingularMassJointTail

/-! `DOZZ.twoInsertion_tail_sum_uniform` reduced to precisely the one-insertion input
`DOZZ.oneInsertion_tail_uniform`, with its full ceiling retained. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology
namespace DOZZ.Proofs

/-- The sole hypothesis is the literal uniform one-insertion conclusion (the statement
`DOZZ.oneInsertion_tail_uniform`). The joint-tail inequality
`DOZZ.separatedSingularMass_joint_tail`, all localization and power estimates, and the common
reflection witness are supplied here. -/
theorem sumtail_twoInsertion_tail_sum_uniform_of_oneInsertion_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (K2 K3 : Set ℂ) (hK2 : IsCompact K2) (hK3 : IsCompact K3)
    (hpos2 : ∀ z ∈ K2, 2 ≤ ‖z‖) (hpos3 : ∀ z ∈ K3, 2 ≤ ‖z‖)
    (hsep : ∀ z2 ∈ K2, ∀ z3 ∈ K3, 3 ≤ ‖z2 - z3‖)
    (A2 A3 : Set ℝ) (hA2 : IsCompact A2) (hA3 : IsCompact A3)
    (hα2 : ∀ α ∈ A2, γ / 2 < α ∧ α < Q γ)
    (hα3 : ∀ α ∈ A3, γ / 2 < α ∧ α < Q γ)
    (F2s F3s : ℂ → Set (ℂ → ℝ)) (radius supBound derivBound lowerBound : ℝ)
    (hF2 : UniformPositiveC1Family K2 F2s radius supBound derivBound lowerBound)
    (hF3 : UniformPositiveC1Family K3 F3s radius supBound derivBound lowerBound)
    (hone : ∀
    (Kz : Set ℂ) (_hKz : IsCompact Kz) (_hz : ∀ z ∈ Kz, 2 ≤ ‖z‖)
    (Kα : Set ℝ) (_hKα : IsCompact Kα)
    (_hα : ∀ α ∈ Kα, γ / 2 < α ∧ α < Q γ)
    (Family : ℂ → Set (ℂ → ℝ)) (radius supBound derivBound lowerBound : ℝ)
    (_hFamily : UniformPositiveC1Family Kz Family radius supBound derivBound lowerBound),
    ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
      IsSourceLateralProjection P X γ M Z ∧
        (∀ α ∈ Kα, IsReflectionData P γ α (B α) Z) ∧
        ∀ η : ℝ, 0 < η → (∀ α ∈ Kα, η < oneInsertionErrorCeiling γ α) →
          ∃ C : ℝ, 0 ≤ C ∧
            ∀ z ∈ Kz, ∀ α ∈ Kα, ∀ F ∈ Family z, ∀ x : ℝ, 1 ≤ x →
              |(P {ω | ENNReal.ofReal x < localSingularMass M F z γ α ω}).toReal -
                oneInsertionTailCoefficient γ α z (F z) (reflectionBarR P γ α (B α) Z) *
                  Real.rpow x (-reflectionExponent γ α)| ≤
                C * Real.rpow x (-reflectionExponent γ α - η) ) :
    ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
      IsSourceLateralProjection P X γ M Z ∧
        (∀ α, (α ∈ A2 ∨ α ∈ A3) → IsReflectionData P γ α (B α) Z) ∧
        ∀ θ : ℝ, 0 < θ → ∃ C : ℝ, 0 ≤ C ∧
          ∀ z2 ∈ K2, ∀ z3 ∈ K3, ∀ α2 ∈ A2, ∀ α3 ∈ A3,
            ∀ F2 ∈ F2s z2, ∀ F3 ∈ F3s z3, ∀ x : ℝ, 1 ≤ x →
              |(P {ω | ENNReal.ofReal x <
                  localSingularMass M F2 z2 γ α2 ω + localSingularMass M F3 z3 γ α3 ω}).toReal -
                (oneInsertionTailCoefficient γ α2 z2 (F2 z2) (reflectionBarR P γ α2 (B α2) Z) *
                    Real.rpow x (-reflectionExponent γ α2) +
                  oneInsertionTailCoefficient γ α3 z3 (F3 z3) (reflectionBarR P γ α3 (B α3) Z) *
                    Real.rpow x (-reflectionExponent γ α3))| ≤
                C * Real.rpow x (-(twoInsertionTailCeiling γ α2 α3 - θ)) := by
  classical
  let _ : IsProbabilityMeasure P := hX.1
  let Kz := K2 ∪ K3
  let Kα := A2 ∪ A3
  have hαK (α : ℝ) (ha : α ∈ Kα) : γ/2 < α ∧ α < Q γ := by
    rcases ha with ha | ha
    · exact hα2 α ha
    · exact hα3 α ha
  let Family (z : ℂ) : Set (ℂ → ℝ) := {F | (z ∈ K2 ∧ F ∈ F2s z) ∨ (z ∈ K3 ∧ F ∈ F3s z)}
  have hFamily : UniformPositiveC1Family Kz Family radius supBound derivBound lowerBound := by
    refine ⟨hF2.1,hF2.2.1,hF2.2.2.1,hF2.2.2.2.1,?_⟩
    intro z _ F hF
    change (z ∈ K2 ∧ F ∈ F2s z) ∨ (z ∈ K3 ∧ F ∈ F3s z) at hF
    rcases hF with hF | hF
    · exact hF2.2.2.2.2 z hF.1 F hF.2
    · exact hF3.2.2.2.2 z hF.1 F hF.2
  have hzK (z : ℂ) (hz : z ∈ Kz) : 2 ≤ ‖z‖ := by
    rcases hz with hz | hz
    · exact hpos2 z hz
    · exact hpos3 z hz
  obtain ⟨B,Z,hsource,hBall⟩ := exists_source_reflection_witness P X M γ hγ hγ2 hX hM
  have hBK (α : ℝ) (ha : α ∈ Kα) := hBall α (hαK α ha).2
  refine ⟨B,Z,hsource,fun α ha => hBK α ha,?_⟩
  intro θ hθ
  let d := θ/4
  have hd : 0 < d := by dsimp [d]; positivity
  have hdθ : d ≤ θ := by dsimp [d]; linarith only [hθ]
  obtain ⟨C,hC,hCb⟩ := sumtail_uniform_one_tail_for_common_witness P X M γ hγ hone
    Kz (hK2.union hK3) hzK Kα (hA2.union hA3) hαK
    Family radius supBound derivBound lowerBound hFamily B Z hBK d hd
  let H := 1+C
  have hH : 0 ≤ H := by dsimp [H]; linarith only [hC]
  have hpcont : Continuous (reflectionExponent γ) := by unfold reflectionExponent; fun_prop
  obtain ⟨m,hm,hmK⟩ := (hA2.union hA3).exists_forall_le' hpcont.continuousOn
    (fun α ha => (residue_critical_order_bounds γ α hγ (hαK α ha).1 (hαK α ha).2).1)
  let ε := min (θ/4) (m/2)
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεK (α : ℝ) (ha : α ∈ Kα) : ε < reflectionExponent γ α := by
    have hb := min_le_right (θ/4) (m/2)
    have hh := hmK α ha
    dsimp [ε]
    linarith only [hb,hh,hm]
  have hεθ : 2*ε ≤ θ := by
    have hb := min_le_left (θ/4) (m/2)
    dsimp [ε]
    linarith only [hb,hθ]
  obtain ⟨D,hD,hDb⟩ := DOZZ.separatedSingularMass_joint_tail P X M γ hγ hγ2 hX hM
    K2 K3 hK2 hK3 hpos2 hpos3 hsep A2 A3 hA2 hA3 hα2 hα3
    F2s F3s radius supBound derivBound lowerBound hF2 hF3 ε hε
    (fun α ha => hεK α (Or.inl ha)) (fun α ha => hεK α (Or.inr ha))
  let T : ℝ := 4/γ^2
  have hT : 0 ≤ T := by dsimp [T]; positivity
  refine ⟨(1+2*H)*4^(T+1)+(2*C+D+2*((C+H*T)*2^(T+1))+2*D*2^T),by positivity,?_⟩
  intro z2 hz2 z3 hz3 α2 hα2mem α3 hα3mem F2 hF2mem F3 hF3mem x hx
  let W2 := localSingularMass M F2 z2 γ α2
  let W3 := localSingularMass M F3 z3 γ α3
  let c2 := oneInsertionTailCoefficient γ α2 z2 (F2 z2) (reflectionBarR P γ α2 (B α2) Z)
  let c3 := oneInsertionTailCoefficient γ α3 z3 (F3 z3) (reflectionBarR P γ α3 (B α3) Z)
  have hf2 := hF2.2.2.2.2 z2 hz2 F2 hF2mem
  have hf3 := hF3.2.2.2.2 z3 hz3 F3 hF3mem
  have hfin2 : ∀ᵐ ω ∂P, W2 ω ≠ ⊤ := sumtail_localMass_ae_finite P X M γ hγ hγ2 hX hM
    F2 z2 α2 supBound (hα2 α2 hα2mem) (fun x => (hf2.2.1 x).2)
  have hfin3 : ∀ᵐ ω ∂P, W3 ω ≠ ⊤ := sumtail_localMass_ae_finite P X M γ hγ hγ2 hX hM
    F3 z3 α3 supBound (hα3 α3 hα3mem) (fun x => (hf3.2.1 x).2)
  have hone2 (t : ℝ) (ht : 1 ≤ t) :
      |P.real {ω | t < (W2 ω).toReal}-c2*t^(-reflectionExponent γ α2)| ≤
        C*t^(-reflectionExponent γ α2-oneInsertionErrorCeiling γ α2+d) := by
    have hb := hCb z2 (Or.inl hz2) α2 (Or.inl hα2mem) F2 (Or.inl ⟨hz2,hF2mem⟩) t ht
    change |P.real {ω | ENNReal.ofReal t < W2 ω}-c2*t^(-reflectionExponent γ α2)| ≤ _ at hb
    rw [sumtail_extended_event_eq_real P W2 hfin2 t (by linarith only [ht])] at hb
    exact hb
  have hone3 (t : ℝ) (ht : 1 ≤ t) :
      |P.real {ω | t < (W3 ω).toReal}-c3*t^(-reflectionExponent γ α3)| ≤
        C*t^(-reflectionExponent γ α3-oneInsertionErrorCeiling γ α3+d) := by
    have hb := hCb z3 (Or.inr hz3) α3 (Or.inr hα3mem) F3 (Or.inr ⟨hz3,hF3mem⟩) t ht
    change |P.real {ω | ENNReal.ofReal t < W3 ω}-c3*t^(-reflectionExponent γ α3)| ≤ _ at hb
    rw [sumtail_extended_event_eq_real P W3 hfin3 t (by linarith only [ht])] at hb
    exact hb
  have hcoeff (c p e : ℝ) (W : Ω → ℝ≥0∞)
      (hb : |P.real {ω | 1 < (W ω).toReal}-c*1^(-p)| ≤ C*1^(-p-e+d)) : |c| ≤ H := by
    simp only [Real.one_rpow,mul_one] at hb
    have hh := abs_le.mp hb
    have hn : 0 ≤ P.real {ω | 1 < (W ω).toReal} := measureReal_nonneg
    have hp : P.real {ω | 1 < (W ω).toReal} ≤ 1 := measureReal_le_one
    dsimp [H]
    apply abs_le.mpr
    constructor <;> linarith only [hh.1,hh.2,hn,hp]
  have hc2 := hcoeff c2 _ _ W2 (hone2 1 le_rfl)
  have hc3 := hcoeff c3 _ _ W3 (hone3 1 le_rfl)
  have hjoint (u v : ℝ) (hu : 1 ≤ u) (hv : 1 ≤ v) :
      P.real {ω | u < (W2 ω).toReal ∧ v < (W3 ω).toReal} ≤
        D*u^(-reflectionExponent γ α2+ε)*v^(-reflectionExponent γ α3+ε) := by
    have hb := hDb z2 hz2 z3 hz3 α2 hα2mem α3 hα3mem F2 hF2mem F3 hF3mem u v hu hv
    change P.real {ω | ENNReal.ofReal u < W2 ω ∧ ENNReal.ofReal v < W3 ω} ≤ _ at hb
    rw [sumtail_extended_joint_eq_real P W2 W3 hfin2 hfin3 u v
      (by linarith only [hu]) (by linarith only [hv])] at hb
    simpa only [Real.rpow_eq_pow] using hb
  obtain ⟨hp2,hp2T⟩ := residue_critical_order_bounds γ α2 hγ (hα2 α2 hα2mem).1 (hα2 α2 hα2mem).2
  obtain ⟨hp3,hp3T⟩ := residue_critical_order_bounds γ α3 hγ (hα3 α3 hα3mem).1 (hα3 α3 hα3mem).2
  obtain ⟨hb2,hb3,hs2,hs3,hj2,hj3⟩ := sumtail_ceiling_bounds γ α2 α3
  have hmeas3 := localSingularMass_aemeasurable P X hX γ hγ hγ2 M hM F3 hf3.1 z3 α3
  have hb := sumtail_real_sum_error P (fun ω => (W2 ω).toReal) (fun ω => (W3 ω).toReal)
    (ENNReal.measurable_toReal.comp_aemeasurable hmeas3)
    (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)
    T _ _ _ _ d ε (twoInsertionTailCeiling γ α2 α3) θ C H D c2 c3
    hp2 hp3 hp2T.le hp3T.le
    (sumtail_one_error_lt_one γ α2 hγ (hα2 α2 hα2mem).1 (hα2 α2 hα2mem).2).le
    (sumtail_one_error_lt_one γ α3 hγ (hα3 α3 hα3mem).1 (hα3 α3 hα3mem).2).le
    hd.le hdθ hε.le hεθ hC hH hD hc2 hc3 hb2 hb3 hs2 hs3 hj2 hj3 hone2 hone3 hjoint x hx
  rw [← sumtail_extended_sum_eq_real P W2 W3 hfin2 hfin3 x (by linarith only [hx])] at hb
  have he : -(twoInsertionTailCeiling γ α2 α3-θ) = -twoInsertionTailCeiling γ α2 α3+θ := by ring
  simpa only [W2,W3,c2,c3,Measure.real,Real.rpow_eq_pow,he] using hb

end DOZZ.Proofs
