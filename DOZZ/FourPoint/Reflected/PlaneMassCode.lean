/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.ChartMassMeasurable
/-! Measurable plane-mass codes on arbitrary measure inputs for the stopped-past observable. -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- A finite restriction with a measurable zero fallback. -/
noncomputable def reflectedFinitePlaneRestriction (K : Set ℂ) (μ : Measure ℂ) : FiniteMeasure ℂ :=
  if h : μ K < ⊤ then ⟨μ.restrict K,isFiniteMeasure_restrict.mpr h.ne⟩ else 0

theorem reflected_finitePlaneRestriction_measurable (K : Set ℂ) (hK : MeasurableSet K) :
    Measurable (reflectedFinitePlaneRestriction K) := by
  have hg : MeasurableSet {μ : Measure ℂ | μ K < ⊤} :=
    measurableSet_lt (Measure.measurable_coe hK) measurable_const
  have hm : Measurable (fun μ : Measure ℂ => (reflectedFinitePlaneRestriction K μ : Measure ℂ)) := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have he : (fun μ : Measure ℂ => (reflectedFinitePlaneRestriction K μ : Measure ℂ) s) =
        (fun μ => if μ K < ⊤ then μ (s ∩ K) else 0) := by
      funext μ
      by_cases h : μ K < ⊤
      · simp [reflectedFinitePlaneRestriction,h,Measure.restrict_apply hs]
      · simp [reflectedFinitePlaneRestriction,h]
    rw [he]
    exact Measurable.ite hg (Measure.measurable_coe (hs.inter hK)) measurable_const
  exact Measurable.subtype_mk hm

def reflectedPuncturedPlane : Set ℂ := ({0} : Set ℂ)ᶜ

/-- A fixed compact exhaustion of the punctured plane. -/
noncomputable def reflectedPuncturedExhaustion : CompactExhaustion reflectedPuncturedPlane := by
  let _ : LocallyCompactSpace reflectedPuncturedPlane :=
    (isClosed_singleton (x := (0 : ℂ))).isOpen_compl.locallyCompactSpace
  exact CompactExhaustion.choice _

noncomputable def reflectedPuncturedCompact (n : ℕ) : Set ℂ :=
  Subtype.val '' reflectedPuncturedExhaustion n

/-- A globally measurable code agrees with the full punctured mass on locally finite inputs. -/
noncomputable def reflectedPuncturedMassCode {A : Type*} (F : A × ℂ → ℝ≥0∞)
    (p : A × Measure ℂ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ∫⁻ x, F (p.1,x) ∂(reflectedFinitePlaneRestriction (reflectedPuncturedCompact n) p.2 : Measure ℂ)

theorem reflected_puncturedMassCode_measurable {A : Type*} [MeasurableSpace A]
    (F : A × ℂ → ℝ≥0∞) (hF : Measurable F) : Measurable (reflectedPuncturedMassCode F) := by
  apply Measurable.iSup
  intro n
  have hK : IsCompact (reflectedPuncturedCompact n) :=
    (reflectedPuncturedExhaustion.isCompact n).image continuous_subtype_val
  exact (measurable_lintegral_finiteMeasure_parameter hF).comp
    (measurable_fst.prodMk ((reflected_finitePlaneRestriction_measurable _ hK.measurableSet).comp measurable_snd))

theorem reflected_puncturedMassCode_eq {A : Type*} (F : A × ℂ → ℝ≥0∞)
    (p : A) (μ : Measure ℂ)
    (hfin : ∀ K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → μ K < ⊤) :
    reflectedPuncturedMassCode F (p,μ) = ∫⁻ x in ({0} : Set ℂ)ᶜ, F (p,x) ∂μ := by
  have hK (n : ℕ) : IsCompact (reflectedPuncturedCompact n) :=
    (reflectedPuncturedExhaustion.isCompact n).image continuous_subtype_val
  have hK0 (n : ℕ) : reflectedPuncturedCompact n ⊆ ({0} : Set ℂ)ᶜ := by
    rintro x ⟨y,-,rfl⟩
    exact y.property
  have hKm : Monotone reflectedPuncturedCompact := fun _ _ h => image_mono
    (reflectedPuncturedExhaustion.subset h)
  have hKe : (⋃ n,reflectedPuncturedCompact n) = ({0} : Set ℂ)ᶜ := by
    ext x
    constructor
    · rintro ⟨-,⟨n,rfl⟩,hx⟩
      exact hK0 n hx
    · intro hx
      obtain ⟨n,hn⟩ := reflectedPuncturedExhaustion.exists_mem ⟨x,hx⟩
      exact mem_iUnion.mpr ⟨n,⟨⟨x,hx⟩,hn,rfl⟩⟩
  unfold reflectedPuncturedMassCode
  have he (n : ℕ) : (reflectedFinitePlaneRestriction (reflectedPuncturedCompact n) μ : Measure ℂ) =
      μ.restrict (reflectedPuncturedCompact n) := by
    simp [reflectedFinitePlaneRestriction,hfin _ (hK n) (hK0 n)]
  simp_rw [he]
  rw [← hKe]
  exact (setLIntegral_iUnion_of_directed _ hKm.directed_le).symm

end DOZZ.Proofs
