/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.DualR.ShiftGood
public import DOZZ.Statements.Complex.HorizontalStrip
public import DOZZ.Statements.Defs.StructureConstant
public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
public import DOZZ.Statements.Correlations.ComplexifyNCharges
import DOZZ.Brownian.Reflection.RtheorAnalytic

/-!
# Factors along real segments of charges

Along a real segment of charge triples `t ↦ p + t (q - p)`, complexified in `t`:

* the continued structure constant `C_f` is meromorphic on the preimage of the holomorphy domain,
  equals the physical structure constant at real parameters in the extended Seiberg domain, and is
  analytic at `t = 1` when `Γ` is analytic at `s(q)`;
* a strip-meromorphic function composed with a real segment is meromorphic on the preimage of the
  strip, which contains every real parameter.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- A complexified real segment of charge triples. -/
noncomputable def segT (a₀ a₁ b₀ b₁ c₀ c₁ : ℝ) (t : ℂ) : Fin 3 → ℂ :=
  ![segC a₀ a₁ t, segC b₀ b₁ t, segC c₀ c₁ t]

theorem differentiable_segT (a₀ a₁ b₀ b₁ c₀ c₁ : ℝ) :
    Differentiable ℂ (segT a₀ a₁ b₀ b₁ c₀ c₁) := by
  rw [differentiable_pi]
  intro i
  fin_cases i
  · exact differentiable_segC a₀ a₁
  · exact differentiable_segC b₀ b₁
  · exact differentiable_segC c₀ c₁

theorem vec3_ofReal (a b c : ℝ) :
    (![(a : ℂ), (b : ℂ), (c : ℂ)] : Fin 3 → ℂ) = complexifyNCharges ![a, b, c] := by
  funext i
  fin_cases i <;> simp [complexifyNCharges]

theorem segT_ofReal (a₀ a₁ b₀ b₁ c₀ c₁ t : ℝ) :
    segT a₀ a₁ b₀ b₁ c₀ c₁ (t : ℂ) =
      complexifyNCharges ![a₀ + t * (a₁ - a₀), b₀ + t * (b₁ - b₀), c₀ + t * (c₁ - c₀)] := by
  unfold segT
  rw [segC_ofReal, segC_ofReal, segC_ofReal, vec3_ofReal]

theorem segT_one (a₀ a₁ b₀ b₁ c₀ c₁ : ℝ) :
    segT a₀ a₁ b₀ b₁ c₀ c₁ 1 = complexifyNCharges ![a₁, b₁, c₁] := by
  unfold segT
  rw [segC_one, segC_one, segC_one, vec3_ofReal]

/-- Real points of a segment between two extended Seiberg triples lie in any open set containing
the complexified extended Seiberg domain. -/
theorem segT_mem {γ : ℝ} (hγ : 0 < γ) {V : Set (Fin 3 → ℂ)}
    (hVmem : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) → complexifyNCharges α ∈ V)
    {a₀ a₁ b₀ b₁ c₀ c₁ : ℝ} (h₀ : ExtendedSeiberg3 γ a₀ b₀ c₀)
    (h₁ : ExtendedSeiberg3 γ a₁ b₁ c₁) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    segT a₀ a₁ b₀ b₁ c₀ c₁ (t : ℂ) ∈ V := by
  rw [segT_ofReal]
  exact hVmem _ (extendedSeiberg3_segment hγ h₀ h₁ ht0 ht1)

/-- The continued structure constant at a real point of a segment. -/
theorem segH_ofReal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ)
    {γ μ : ℝ} (hμ : 0 < μ) {f : (Fin 3 → ℂ) → ℂ}
    (hfeq : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) →
      f (complexifyNCharges α) = (unitVolumeStructureConstant P M γ (α 0) (α 1) (α 2) : ℂ))
    {a₀ a₁ b₀ b₁ c₀ c₁ t : ℝ}
    (h : ExtendedSeiberg3 γ (a₀ + t * (a₁ - a₀)) (b₀ + t * (b₁ - b₀)) (c₀ + t * (c₁ - c₀))) :
    structureConstantH f γ μ (segT a₀ a₁ b₀ b₁ c₀ c₁ (t : ℂ)) =
      (structureConstant P M γ μ (a₀ + t * (a₁ - a₀)) (b₀ + t * (b₁ - b₀))
        (c₀ + t * (c₁ - c₀)) : ℂ) := by
  rw [segT_ofReal]
  exact structureConstantH_complexify P M hμ _ (hfeq _ h)

/-- The continued structure constant at the end of a segment. -/
theorem segH_one {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ)
    {γ μ : ℝ} (hμ : 0 < μ) {f : (Fin 3 → ℂ) → ℂ}
    (hfeq : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) →
      f (complexifyNCharges α) = (unitVolumeStructureConstant P M γ (α 0) (α 1) (α 2) : ℂ))
    {a₀ a₁ b₀ b₁ c₀ c₁ : ℝ} (h : ExtendedSeiberg3 γ a₁ b₁ c₁) :
    structureConstantH f γ μ (segT a₀ a₁ b₀ b₁ c₀ c₁ 1) =
      (structureConstant P M γ μ a₁ b₁ c₁ : ℂ) := by
  rw [segT_one]
  exact structureConstantH_complexify P M hμ _ (hfeq _ h)

/-- The continued structure constant is meromorphic along a segment, on the preimage of the
holomorphy domain. -/
theorem segH_meromorphicOn {f : (Fin 3 → ℂ) → ℂ} {V : Set (Fin 3 → ℂ)} (hV : IsOpen V)
    (hf : DifferentiableOn ℂ f V) {γ μ : ℝ} (hμ : 0 < μ) (a₀ a₁ b₀ b₁ c₀ c₁ : ℝ) :
    MeromorphicOn (fun t => structureConstantH f γ μ (segT a₀ a₁ b₀ b₁ c₀ c₁ t))
      (segT a₀ a₁ b₀ b₁ c₀ c₁ ⁻¹' V) :=
  meromorphicOn_structureConstantH_comp hV hf hμ (differentiable_segT a₀ a₁ b₀ b₁ c₀ c₁)

/-- The continued structure constant is analytic at the end of a segment when `Γ` is analytic at
the `s`-parameter of the endpoint. -/
theorem segH_analyticAt_one {f : (Fin 3 → ℂ) → ℂ} {V : Set (Fin 3 → ℂ)} (hV : IsOpen V)
    (hf : DifferentiableOn ℂ f V) {γ μ : ℝ} (hμ : 0 < μ) {a₀ a₁ b₀ b₁ c₀ c₁ : ℝ}
    (hmem : complexifyNCharges ![a₁, b₁, c₁] ∈ V)
    (hs : AnalyticAt ℂ Complex.Gamma (sExp γ a₁ b₁ c₁ : ℂ)) :
    AnalyticAt ℂ (fun t => structureConstantH f γ μ (segT a₀ a₁ b₀ b₁ c₀ c₁ t)) 1 := by
  refine analyticAt_structureConstantH_comp' hV hf hμ (differentiable_segT a₀ a₁ b₀ b₁ c₀ c₁)
    (by rw [segT_one]; exact hmem) ?_
  rw [segT_one, sExpC_complexify]
  exact hs

/-- A strip-meromorphic function along a real segment. -/
theorem segR_meromorphicOn {R : ℂ → ℂ} {h : ℝ} (hR : MeromorphicOn R (horizontalStrip h))
    (a₀ a₁ : ℝ) :
    MeromorphicOn (fun t => R (segC a₀ a₁ t)) (segC a₀ a₁ ⁻¹' horizontalStrip h) :=
  fun t ht => (hR _ ht).comp_analyticAt (g := segC a₀ a₁) (analyticAt_segC a₀ a₁ t)

/-- A function analytic at the endpoint is analytic along the segment at `t = 1`. -/
theorem segR_analyticAt_one {R : ℂ → ℂ} {a₀ a₁ : ℝ} (hR : AnalyticAt ℂ R (a₁ : ℂ)) :
    AnalyticAt ℂ (fun t => R (segC a₀ a₁ t)) 1 :=
  AnalyticAt.comp_of_eq (g := R) (f := segC a₀ a₁) hR (analyticAt_segC a₀ a₁ 1) (segC_one a₀ a₁)

/-- Real parameters of a segment map into a strip. -/
theorem segC_mem_horizontalStrip {h : ℝ} (hh : 0 < h) (a₀ a₁ t : ℝ) :
    segC a₀ a₁ (t : ℂ) ∈ horizontalStrip h := by
  rw [segC_ofReal]
  exact ofReal_mem_horizontalStrip hh _

end DOZZ.Proofs

end
