/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Assembly.KernelCauchy

/-! Good and bad cutoff masses of bounded nonnegative Borel tests and the cutoff `L¹` Cauchy estimate on a charge interval. -/

@[expose] public section

/-! ### Good masses

Barrier-good cutoff masses of bounded nonnegative Borel tests are uniformly Cauchy in `L¹`.

The mixed second moment of two good masses is the spatial integral of the growing-barrier
two-root kernel. The kernel `L¹` Cauchy property bounds the mean-square difference, uniformly
over tests bounded by `L` and charges in a compact interval. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Assembly

open DOZZ.Proofs

/-- The Wick weight is jointly measurable in the sample and the point. -/
theorem admissibleLogWickWeight_measurable_joint
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (g ε : ℝ) :
    Measurable (fun q : Ω × ℂ => admissibleLogWickWeight P Y g ε q.2 q.1) := by
  have hv0 := admissibleLogRegularization_variance_measurable P U dens ε₀ Y hY ε
  have hvar : Measurable (fun q : Ω × ℂ => gaussianVariance P (fun ω => Y ω ε q.2)) :=
    hv0.comp measurable_snd
  have hfield : Measurable (fun q : Ω × ℂ => Y q.1 ε q.2) := hY.measurableAtScale ε
  unfold admissibleLogWickWeight
  fun_prop

/-- Cutoff Wick mass of a nonnegative test restricted to an event in sample and point. -/
noncomputable def wickEventMass {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (μ : Measure ℂ) (Y : Ω → ℝ → ℂ → ℝ) (g r : ℝ) (E : Set (Ω × ℂ))
    (f : ℂ → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (f x) * admissibleLogWickWeight P Y g (Real.exp (-r)) x ω *
    Set.indicator E (fun _ => (1 : ℝ≥0∞)) (ω, x) ∂μ

theorem wickEventMass_integrand_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (g r : ℝ) (E : Set (Ω × ℂ))
    (hE : MeasurableSet E) (f : ℂ → ℝ) (hf : Measurable f) :
    Measurable (fun q : Ω × ℂ => ENNReal.ofReal (f q.2) *
      admissibleLogWickWeight P Y g (Real.exp (-r)) q.2 q.1 *
      Set.indicator E (fun _ => (1 : ℝ≥0∞)) q) :=
  ((ENNReal.measurable_ofReal.comp (hf.comp measurable_snd)).mul
    (admissibleLogWickWeight_measurable_joint P U dens ε₀ Y hY g _)).mul
    (measurable_const.indicator hE)

theorem wickEventMass_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (μ : Measure ℂ) [SFinite μ]
    (g r : ℝ) (E : Set (Ω × ℂ)) (hE : MeasurableSet E) (f : ℂ → ℝ) (hf : Measurable f) :
    Measurable (wickEventMass P μ Y g r E f) :=
  (wickEventMass_integrand_measurable P U dens ε₀ Y hY g r E hE f hf).lintegral_prod_right'

/-- Tonelli: the mixed second moment of two event masses is the spatial integral of the
two-root event kernel. -/
theorem lintegral_wickEventMass_mul
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (μ : Measure ℂ) [SFinite μ]
    (g r s : ℝ) (E₁ E₂ : Set (Ω × ℂ)) (hE₁ : MeasurableSet E₁) (hE₂ : MeasurableSet E₂)
    (f : ℂ → ℝ) (hf : Measurable f) :
    ∫⁻ ω, wickEventMass P μ Y g r E₁ f ω * wickEventMass P μ Y g s E₂ f ω ∂P =
      ∫⁻ p, ENNReal.ofReal (f p.1) * ENNReal.ofReal (f p.2) *
        ∫⁻ ω, admissibleLogWickWeight P Y g (Real.exp (-r)) p.1 ω *
          admissibleLogWickWeight P Y g (Real.exp (-s)) p.2 ω *
          Set.indicator E₁ (fun _ => (1 : ℝ≥0∞)) (ω, p.1) *
          Set.indicator E₂ (fun _ => (1 : ℝ≥0∞)) (ω, p.2) ∂P ∂(μ.prod μ) := by
  let F : Ω → ℂ → ℝ≥0∞ := fun ω x => ENNReal.ofReal (f x) *
    admissibleLogWickWeight P Y g (Real.exp (-r)) x ω * Set.indicator E₁ (fun _ => 1) (ω, x)
  let G : Ω → ℂ → ℝ≥0∞ := fun ω x => ENNReal.ofReal (f x) *
    admissibleLogWickWeight P Y g (Real.exp (-s)) x ω * Set.indicator E₂ (fun _ => 1) (ω, x)
  have hF : Measurable (fun q : Ω × ℂ => F q.1 q.2) :=
    wickEventMass_integrand_measurable P U dens ε₀ Y hY g r E₁ hE₁ f hf
  have hG : Measurable (fun q : Ω × ℂ => G q.1 q.2) :=
    wickEventMass_integrand_measurable P U dens ε₀ Y hY g s E₂ hE₂ f hf
  have hFω (ω : Ω) : Measurable (F ω) :=
    hF.comp (f := fun x : ℂ => (ω, x)) (measurable_const.prodMk measurable_id)
  have hGω (ω : Ω) : Measurable (G ω) :=
    hG.comp (f := fun x : ℂ => (ω, x)) (measurable_const.prodMk measurable_id)
  have hH : Measurable (fun q : Ω × (ℂ × ℂ) => F q.1 q.2.1 * G q.1 q.2.2) :=
    (hF.comp (f := fun q : Ω × (ℂ × ℂ) => (q.1, q.2.1))
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      (hG.comp (f := fun q : Ω × (ℂ × ℂ) => (q.1, q.2.2))
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  calc ∫⁻ ω, wickEventMass P μ Y g r E₁ f ω * wickEventMass P μ Y g s E₂ f ω ∂P =
        ∫⁻ ω, ∫⁻ p, F ω p.1 * G ω p.2 ∂(μ.prod μ) ∂P := by
          apply lintegral_congr
          intro ω
          rw [lintegral_prod_mul (hFω ω).aemeasurable (hGω ω).aemeasurable]
          rfl
    _ = ∫⁻ p, ∫⁻ ω, F ω p.1 * G ω p.2 ∂P ∂(μ.prod μ) :=
          lintegral_lintegral_swap hH.aemeasurable
    _ = _ := by
          apply lintegral_congr
          intro p
          have hmeasW : Measurable (fun ω => admissibleLogWickWeight P Y g (Real.exp (-r)) p.1 ω *
              admissibleLogWickWeight P Y g (Real.exp (-s)) p.2 ω *
              Set.indicator E₁ (fun _ => (1 : ℝ≥0∞)) (ω, p.1) *
              Set.indicator E₂ (fun _ => (1 : ℝ≥0∞)) (ω, p.2)) := by
            have h1 := (admissibleLogWickWeight_measurable_joint P U dens ε₀ Y hY g
              (Real.exp (-r))).comp (measurable_id.prodMk (measurable_const (a := p.1)))
            have h2 := (admissibleLogWickWeight_measurable_joint P U dens ε₀ Y hY g
              (Real.exp (-s))).comp (measurable_id.prodMk (measurable_const (a := p.2)))
            have h3 : Measurable (fun ω : Ω => Set.indicator E₁ (fun _ => (1 : ℝ≥0∞)) (ω, p.1)) :=
              (measurable_const.indicator hE₁).comp (measurable_id.prodMk measurable_const)
            have h4 : Measurable (fun ω : Ω => Set.indicator E₂ (fun _ => (1 : ℝ≥0∞)) (ω, p.2)) :=
              (measurable_const.indicator hE₂).comp (measurable_id.prodMk measurable_const)
            exact ((h1.mul h2).mul h3).mul h4
          rw [← lintegral_const_mul _ hmeasW]
          apply lintegral_congr
          intro ω
          simp only [F, G]
          ring

/-- The growing-barrier kernel is the two-root event kernel of the growing barrier events. -/
theorem growingPairKernel_eq_event_kernel
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ → ℂ → ℝ) (g a : ℝ) (k₀ : ℕ) (r s : ℝ) (p : ℂ × ℂ) :
    growingPairKernel P Y g a k₀ r s p =
      ∫⁻ ω, admissibleLogWickWeight P Y g (Real.exp (-r)) p.1 ω *
        admissibleLogWickWeight P Y g (Real.exp (-s)) p.2 ω *
        Set.indicator (admissibleGrowingBarrierSet Y a k₀ r) (fun _ => (1 : ℝ≥0∞)) (ω, p.1) *
        Set.indicator (admissibleGrowingBarrierSet Y a k₀ s) (fun _ => (1 : ℝ≥0∞))
          (ω, p.2) ∂P := by
  unfold growingPairKernel compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel
  simp only [ite_self]

/-- The squared symmetric difference plus twice the product is at most the sum of squares. -/
theorem ennDist_sq_add_two_mul_le (a b : ℝ≥0∞) :
    ennDist a b ^ 2 + 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by
  by_cases ha : a = ⊤
  · subst ha; simp
  by_cases hb : b = ⊤
  · subst hb; simp
  rcases le_total a b with h | h
  · obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, (add_tsub_cancel_of_le h).symm⟩
    have hd : ennDist a (a + d) = d := by
      unfold ennDist
      rw [tsub_eq_zero_of_le le_self_add, zero_add, ENNReal.add_sub_cancel_left ha]
    rw [hd]
    exact le_of_eq (by ring)
  · obtain ⟨d, rfl⟩ : ∃ d, a = b + d := ⟨a - b, (add_tsub_cancel_of_le h).symm⟩
    have hd : ennDist (b + d) b = d := by
      unfold ennDist
      rw [tsub_eq_zero_of_le le_self_add, add_zero, ENNReal.add_sub_cancel_left hb]
    rw [hd]
    exact le_of_eq (by ring)

/-- Abstract mean-square bound from comparison of the diagonal and mixed second moments. -/
theorem lintegral_ennDist_sq_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A B : Ω → ℝ≥0∞)
    (hA : Measurable A) (hB : Measurable B)
    (hAB : ∫⁻ ω, A ω * B ω ∂P ≠ ⊤) (D₁ D₂ : ℝ≥0∞)
    (h₁ : ∫⁻ ω, A ω * A ω ∂P ≤ ∫⁻ ω, A ω * B ω ∂P + D₁)
    (h₂ : ∫⁻ ω, B ω * B ω ∂P ≤ ∫⁻ ω, A ω * B ω ∂P + D₂) :
    ∫⁻ ω, ennDist (A ω) (B ω) ^ 2 ∂P ≤ D₁ + D₂ := by
  have hpt : ∀ ω, ennDist (A ω) (B ω) ^ 2 + 2 * (A ω * B ω) ≤ A ω * A ω + B ω * B ω := by
    intro ω
    have h := ennDist_sq_add_two_mul_le (A ω) (B ω)
    simpa [pow_two] using h
  have hint := lintegral_mono (μ := P) hpt
  have hABm : Measurable (fun ω => A ω * B ω) := hA.mul hB
  have h2ABm : Measurable (fun ω => 2 * (A ω * B ω)) := hABm.const_mul 2
  have hAAm : Measurable (fun ω => A ω * A ω) := hA.mul hA
  rw [lintegral_add_right _ h2ABm, lintegral_add_left hAAm, lintegral_const_mul 2 hABm] at hint
  have hsum : ∫⁻ ω, ennDist (A ω) (B ω) ^ 2 ∂P + 2 * ∫⁻ ω, A ω * B ω ∂P ≤
      (D₁ + D₂) + 2 * ∫⁻ ω, A ω * B ω ∂P := by
    calc _ ≤ ∫⁻ ω, A ω * A ω ∂P + ∫⁻ ω, B ω * B ω ∂P := hint
      _ ≤ (∫⁻ ω, A ω * B ω ∂P + D₁) + (∫⁻ ω, A ω * B ω ∂P + D₂) := add_le_add h₁ h₂
      _ = (D₁ + D₂) + 2 * ∫⁻ ω, A ω * B ω ∂P := by ring
  exact (ENNReal.add_le_add_iff_right (ENNReal.mul_ne_top (by norm_num) hAB)).mp hsum

/-- Cauchy–Schwarz for a nonnegative random variable on a probability space. -/
theorem lintegral_le_rpow_lintegral_sq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ≥0∞) (hX : AEMeasurable X P) :
    ∫⁻ ω, X ω ∂P ≤ (∫⁻ ω, X ω ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two hX
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ,
    ENNReal.one_rpow] at h
  have hsq : ∀ ω, X ω ^ (2 : ℝ) = X ω ^ 2 := fun ω => ENNReal.rpow_two (X ω)
  simp only [hsq] at h
  simpa using h

/-- The barrier-good cutoff mass of a test on the compact chart `K`. -/
noncomputable abbrev goodMass {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (K : Set ℂ) (Y : Ω → ℝ → ℂ → ℝ)
    (g a : ℝ) (k₀ : ℕ) (r : ℝ) (f : ℂ → ℝ) (ω : Ω) : ℝ≥0∞ :=
  wickEventMass P ((logRegularizationReference U dens).restrict K) Y g r
    (admissibleGrowingBarrierSet Y a k₀ r) f ω

theorem ennDist_measurable {α : Type*} [MeasurableSpace α] {F G : α → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) : Measurable (fun x => ennDist (F x) (G x)) :=
  (hF.sub hG).add (hG.sub hF)

theorem le_add_ennDist (x y : ℝ≥0∞) : x ≤ y + ennDist x y := by
  unfold ennDist
  calc x ≤ y + (x - y) := le_add_tsub
    _ ≤ y + ((x - y) + (y - x)) := by gcongr; exact le_self_add

/-- Barrier-good cutoff masses of tests with values in `[0, L]` are Cauchy in `L¹(P)` as both
cutoffs vanish, uniformly over such tests and charges in a compact interval. -/
theorem goodMass_L1_uniform_cauchy
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (gLo gHi a η κ : ℝ) (hgLo : 0 < gLo) (hgLoHi : gLo ≤ gHi) (hga : gHi < a)
    (ha2 : a < 2 * gLo) (hη : 0 < η) (hη1 : η < 1) (hκ : 0 < κ) (hκ2 : κ < 2)
    (hκexp : ∀ g ∈ Icc gLo gHi, g ^ 2 - ((1 - η) ^ 2 * (2 * g - a) ^ 2 / (2 * (1 + η))) ≤ κ)
    (k₀ : ℕ) (hk₀cut : Real.exp (-(k₀ : ℝ)) ≤ ε₀)
    (hvar : ∀ k : ℕ, k₀ ≤ k → ∀ x ∈ K,
      1 ≤ gaussianVariance P (fun ω => Y ω (Real.exp (-(k : ℝ))) x))
    (L : ℝ) (hL : 0 ≤ L) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ r s : ℝ, R ≤ r → R ≤ s → ∀ g ∈ Icc gLo gHi, ∀ f : ℂ → ℝ, Measurable f →
      (∀ x, 0 ≤ f x) → (∀ x, f x ≤ L) →
      ∫⁻ ω, ennDist (goodMass P U dens K Y g a k₀ r f ω)
        (goodMass P U dens K Y g a k₀ s f ω) ∂P < ENNReal.ofReal ε := by
  set μ := chartPairMeasure U dens K with hμdef
  set ε' : ℝ := ε ^ 2 / (2 * (L ^ 2 + 1)) with hε'def
  have hε' : 0 < ε' := by positivity
  obtain ⟨R₁, hR₁⟩ := growingPairKernel_L1_uniform_cauchy P U dens ε₀ Y hY K hK hKU gLo gHi a
    η κ hgLo hgLoHi hga ha2 hη hη1 hκ hκ2 hκexp k₀ hk₀cut hvar ε' hε'
  obtain ⟨R₀, Maj, hMajm, hMajInt, hle⟩ := growingPairKernel_ae_le_integrable_majorant P U dens
    ε₀ Y hY K hK hKU gLo gHi a η κ hgLo hgLoHi hga ha2 hη hη1 hκ hκ2 hκexp k₀
  refine ⟨max R₀ R₁, ?_⟩
  intro r s hr hs g hg f hf hf0 hfL
  have hbarr (t : ℝ) : MeasurableSet (admissibleGrowingBarrierSet Y a k₀ t) :=
    admissibleGrowingBarrierSet_measurable P U dens ε₀ Y hY a k₀ t
  have hmeasJ (t : ℝ) : Measurable (goodMass P U dens K Y g a k₀ t f) :=
    wickEventMass_measurable P U dens ε₀ Y hY _ g t _ (hbarr t) f hf
  have hKer (t t' : ℝ) : Measurable (growingPairKernel P Y g a k₀ t t') :=
    growingPairKernel_measurable P U dens ε₀ Y hY g a k₀ t t'
  have hff : Measurable (fun p : ℂ × ℂ => ENNReal.ofReal (f p.1) * ENNReal.ofReal (f p.2)) :=
    (ENNReal.measurable_ofReal.comp (hf.comp measurable_fst)).mul
      (ENNReal.measurable_ofReal.comp (hf.comp measurable_snd))
  have hffL (p : ℂ × ℂ) : ENNReal.ofReal (f p.1) * ENNReal.ofReal (f p.2) ≤
      ENNReal.ofReal L ^ 2 := by
    rw [pow_two]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hfL _)) (ENNReal.ofReal_le_ofReal (hfL _))
  have hmom (t t' : ℝ) : ∫⁻ ω, goodMass P U dens K Y g a k₀ t f ω *
      goodMass P U dens K Y g a k₀ t' f ω ∂P =
      ∫⁻ p, ENNReal.ofReal (f p.1) * ENNReal.ofReal (f p.2) *
        growingPairKernel P Y g a k₀ t t' p ∂μ := by
    rw [lintegral_wickEventMass_mul P U dens ε₀ Y hY _ g t t' _ _ (hbarr t) (hbarr t') f hf]
    apply lintegral_congr
    intro p
    rw [growingPairKernel_eq_event_kernel]
  have hcompare (t₁ t₂ t₃ t₄ : ℝ) :
      ∫⁻ p, ENNReal.ofReal (f p.1) * ENNReal.ofReal (f p.2) *
          growingPairKernel P Y g a k₀ t₁ t₂ p ∂μ ≤
        ∫⁻ p, ENNReal.ofReal (f p.1) * ENNReal.ofReal (f p.2) *
          growingPairKernel P Y g a k₀ t₃ t₄ p ∂μ +
        ENNReal.ofReal L ^ 2 * ∫⁻ p, ennDist (growingPairKernel P Y g a k₀ t₁ t₂ p)
          (growingPairKernel P Y g a k₀ t₃ t₄ p) ∂μ := by
    have hm34 : Measurable (fun p : ℂ × ℂ => ENNReal.ofReal (f p.1) * ENNReal.ofReal (f p.2) *
        growingPairKernel P Y g a k₀ t₃ t₄ p) := hff.mul (hKer t₃ t₄)
    rw [← lintegral_const_mul _ (ennDist_measurable (hKer t₁ t₂) (hKer t₃ t₄)),
      ← lintegral_add_left hm34]
    apply lintegral_mono
    intro p
    calc ENNReal.ofReal (f p.1) * ENNReal.ofReal (f p.2) * growingPairKernel P Y g a k₀ t₁ t₂ p
        ≤ ENNReal.ofReal (f p.1) * ENNReal.ofReal (f p.2) *
            (growingPairKernel P Y g a k₀ t₃ t₄ p + ennDist (growingPairKernel P Y g a k₀ t₁ t₂ p)
              (growingPairKernel P Y g a k₀ t₃ t₄ p)) := by gcongr; exact le_add_ennDist _ _
      _ = ENNReal.ofReal (f p.1) * ENNReal.ofReal (f p.2) * growingPairKernel P Y g a k₀ t₃ t₄ p +
            ENNReal.ofReal (f p.1) * ENNReal.ofReal (f p.2) * ennDist
              (growingPairKernel P Y g a k₀ t₁ t₂ p) (growingPairKernel P Y g a k₀ t₃ t₄ p) := by
            ring
      _ ≤ _ := by beta_reduce; gcongr; exact hffL p
  have hR₀r : R₀ ≤ r := le_trans (le_max_left _ _) hr
  have hR₀s : R₀ ≤ s := le_trans (le_max_left _ _) hs
  have hR₁r : R₁ ≤ r := le_trans (le_max_right _ _) hr
  have hR₁s : R₁ ≤ s := le_trans (le_max_right _ _) hs
  have hABfin : ∫⁻ ω, goodMass P U dens K Y g a k₀ r f ω *
      goodMass P U dens K Y g a k₀ s f ω ∂P ≠ ⊤ := by
    rw [hmom r s]
    have hdom := hle r s hR₀r hR₀s g hg
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal L ^ 2 * ∫⁻ p, Maj p ∂μ)
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hMajInt) ?_
    rw [← lintegral_const_mul _ hMajm]
    apply lintegral_mono_ae
    filter_upwards [hdom] with p hp
    exact mul_le_mul' (hffL p) hp
  have h₁ := hcompare r r r s
  have h₂ := hcompare s s r s
  rw [← hmom, ← hmom] at h₁
  rw [← hmom, ← hmom] at h₂
  have hsym : ∫⁻ ω, goodMass P U dens K Y g a k₀ s f ω *
      goodMass P U dens K Y g a k₀ s f ω ∂P = ∫⁻ ω, goodMass P U dens K Y g a k₀ s f ω *
      goodMass P U dens K Y g a k₀ s f ω ∂P := rfl
  have hsq := lintegral_ennDist_sq_le P _ _ (hmeasJ r) (hmeasJ s) hABfin _ _ h₁ h₂
  have hD₁ := hR₁ r r r s hR₁r hR₁r hR₁r hR₁s g hg
  have hD₂ := hR₁ s s r s hR₁s hR₁s hR₁r hR₁s g hg
  have hsmall : ENNReal.ofReal L ^ 2 * ∫⁻ p, ennDist (growingPairKernel P Y g a k₀ r r p)
        (growingPairKernel P Y g a k₀ r s p) ∂μ +
      ENNReal.ofReal L ^ 2 * ∫⁻ p, ennDist (growingPairKernel P Y g a k₀ s s p)
        (growingPairKernel P Y g a k₀ r s p) ∂μ < ENNReal.ofReal (ε ^ 2) := by
    calc _ ≤ ENNReal.ofReal L ^ 2 * ENNReal.ofReal ε' + ENNReal.ofReal L ^ 2 * ENNReal.ofReal ε' :=
          add_le_add (mul_le_mul_right hD₁.le _) (mul_le_mul_right hD₂.le _)
      _ = ENNReal.ofReal (L ^ 2 * (2 * ε')) := by
          rw [← ENNReal.ofReal_pow hL, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
      _ < ENNReal.ofReal (ε ^ 2) := by
          rw [ENNReal.ofReal_lt_ofReal_iff (by positivity), hε'def]
          have hden : 0 < 2 * (L ^ 2 + 1) := by positivity
          rw [show L ^ 2 * (2 * (ε ^ 2 / (2 * (L ^ 2 + 1)))) = ε ^ 2 * (L ^ 2 / (L ^ 2 + 1)) by
            field_simp]
          have hfrac : L ^ 2 / (L ^ 2 + 1) < 1 := by
            rw [div_lt_one (by positivity)]; linarith
          have hε2 : 0 < ε ^ 2 := by positivity
          calc ε ^ 2 * (L ^ 2 / (L ^ 2 + 1)) < ε ^ 2 * 1 := mul_lt_mul_of_pos_left hfrac hε2
            _ = ε ^ 2 := mul_one _
  have hcs := lintegral_le_rpow_lintegral_sq P (fun ω => ennDist
    (goodMass P U dens K Y g a k₀ r f ω) (goodMass P U dens K Y g a k₀ s f ω))
    (ennDist_measurable (hmeasJ r) (hmeasJ s)).aemeasurable
  calc _ ≤ _ := hcs
    _ < ENNReal.ofReal (ε ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_lt_rpow (lt_of_le_of_lt hsq hsmall) (by norm_num)
    _ = ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_sq hε.le]

end DOZZ.Assembly

/-! ### Full cutoff masses on a charge interval

Full cutoff masses of bounded nonnegative Borel tests are uniformly Cauchy in `L¹`.

The full cutoff mass is the barrier-good mass plus the barrier-bad mass. The bad mass is small in
expectation by the one-root tilted barrier tail, uniformly once the barrier starts at a large
scale; the good mass is Cauchy for each fixed start. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Assembly

open DOZZ.Proofs

/-- The full cutoff mass of a test on the compact chart `K`. -/
noncomputable abbrev chartMass {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (K : Set ℂ) (Y : Ω → ℝ → ℂ → ℝ)
    (g r : ℝ) (f : ℂ → ℝ) (ω : Ω) : ℝ≥0∞ :=
  wickEventMass P ((logRegularizationReference U dens).restrict K) Y g r Set.univ f ω

/-- The barrier-bad cutoff mass of a test on the compact chart `K`. -/
noncomputable abbrev badMass {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (K : Set ℂ) (Y : Ω → ℝ → ℂ → ℝ)
    (g a : ℝ) (k₀ : ℕ) (r : ℝ) (f : ℂ → ℝ) (ω : Ω) : ℝ≥0∞ :=
  wickEventMass P ((logRegularizationReference U dens).restrict K) Y g r
    (admissibleGrowingBarrierSet Y a k₀ r)ᶜ f ω

/-- The full cutoff mass splits into its barrier-good and barrier-bad parts. -/
theorem chartMass_eq_good_add_bad
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (K : Set ℂ)
    (g a : ℝ) (k₀ : ℕ) (r : ℝ) (f : ℂ → ℝ) (hf : Measurable f) (ω : Ω) :
    chartMass P U dens K Y g r f ω =
      goodMass P U dens K Y g a k₀ r f ω + badMass P U dens K Y g a k₀ r f ω := by
  have hA := admissibleGrowingBarrierSet_measurable P U dens ε₀ Y hY a k₀ r
  have hmeas : Measurable (fun x : ℂ => ENNReal.ofReal (f x) *
      admissibleLogWickWeight P Y g (Real.exp (-r)) x ω *
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ r) (fun _ => (1 : ℝ≥0∞)) (ω, x)) :=
    (wickEventMass_integrand_measurable P U dens ε₀ Y hY g r _ hA f hf).comp
      (measurable_const.prodMk measurable_id : Measurable (fun x : ℂ => (ω, x)))
  unfold chartMass goodMass badMass wickEventMass
  rw [← lintegral_add_left hmeas]
  apply lintegral_congr
  intro x
  by_cases hx : (ω, x) ∈ admissibleGrowingBarrierSet Y a k₀ r
  · rw [Set.indicator_of_mem (Set.mem_univ _), Set.indicator_of_mem hx,
      Set.indicator_of_notMem (show (ω, x) ∉ (admissibleGrowingBarrierSet Y a k₀ r)ᶜ from
        fun h => h hx)]
    ring
  · rw [Set.indicator_of_mem (Set.mem_univ _), Set.indicator_of_notMem hx,
      Set.indicator_of_mem (show (ω, x) ∈ (admissibleGrowingBarrierSet Y a k₀ r)ᶜ from hx)]
    ring

/-- The symmetric difference is subadditive under addition. -/
theorem ennDist_add_add_le (a b c d : ℝ≥0∞) :
    ennDist (a + b) (c + d) ≤ ennDist a c + ennDist b d := by
  unfold ennDist
  calc (a + b - (c + d)) + (c + d - (a + b)) ≤ ((a - c) + (b - d)) + ((c - a) + (d - b)) :=
        add_le_add add_tsub_add_le_tsub_add_tsub add_tsub_add_le_tsub_add_tsub
    _ = ((a - c) + (c - a)) + ((b - d) + (d - b)) := by ring

/-- Reindex a tail sum supported at or above `k₀`. -/
theorem tsum_indicator_ge_le_tsum_nat_add (k₀ : ℕ) (T f : ℕ → ℝ≥0∞) (S : Set ℕ)
    (hS : S ⊆ {k | k₀ ≤ k}) (hT : ∀ k ∈ S, T k ≤ f k) :
    ∑' k : ℕ, Set.indicator S T k ≤ ∑' j : ℕ, f (j + k₀) := by
  classical
  have hle : ∀ k, Set.indicator S T k ≤ Set.indicator {k | k₀ ≤ k} f k := by
    intro k
    by_cases hk : k ∈ S
    · rw [Set.indicator_of_mem hk, Set.indicator_of_mem (hS hk)]
      exact hT k hk
    · rw [Set.indicator_of_notMem hk]
      exact zero_le
  refine (ENNReal.tsum_le_tsum hle).trans (le_of_eq ?_)
  have hinj : Function.Injective (fun j : ℕ => j + k₀) := fun i j h => by simpa using h
  have hsupp : Function.support (Set.indicator {k : ℕ | k₀ ≤ k} f) ⊆
      Set.range (fun j : ℕ => j + k₀) := by
    intro k hk
    have hkm : k₀ ≤ k := by
      by_contra h
      exact hk (Set.indicator_of_notMem h f)
    exact ⟨k - k₀, by show k - k₀ + k₀ = k; omega⟩
  rw [← hinj.tsum_eq hsupp]
  apply tsum_congr
  intro j
  rw [Set.indicator_of_mem (show j + k₀ ∈ {k : ℕ | k₀ ≤ k} from
    show k₀ ≤ j + k₀ by omega)]

/-- One root violates its growing barrier with exponentially small tilted weight, uniformly for
charges in `[gLo, gHi]` once the barrier starts at a large scale. -/
theorem wick_root_barrier_violation_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (gLo gHi a : ℝ), 0 < gLo → gHi < a → ∀ k₀ : ℕ,
      Real.exp (-(k₀ : ℝ)) ≤ ε₀ → C < (k₀ : ℝ) → gHi * C ≤ (a - gHi) * (k₀ : ℝ) / 2 →
      ∀ g ∈ Icc gLo gHi, ∀ r : ℝ, ∀ x ∈ K,
        ∫⁻ ω, admissibleLogWickWeight P Y g (Real.exp (-r)) x ω *
          Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)ᶜ (fun _ => (1 : ℝ≥0∞)) (ω, x) ∂P ≤
          ∑' j : ℕ, ENNReal.ofReal (Real.exp (-((a - gHi) ^ 2 * ((j + k₀ : ℕ) : ℝ) / 16))) := by
  obtain ⟨C, hC, htail⟩ := admissible_coarse_barrier_tail_rate P U dens ε₀ Y hY K hK hKU
  refine ⟨C, hC, ?_⟩
  intro gLo gHi a hgLo hga k₀ hk₀cut hk₀C hk₀gap g hg r x hx
  have hgpos : 0 < g := lt_of_lt_of_le hgLo hg.1
  have hga' : g < a := lt_of_le_of_lt hg.2 hga
  let w : Ω → ℝ≥0∞ := fun ω => admissibleLogWickWeight P Y g (Real.exp (-r)) x ω
  have hw : Measurable w := admissibleLogWickWeight_measurable_sample P U dens ε₀ Y hY g _ x
  let bad : ℕ → Ω → Prop := fun k ω =>
    k₀ ≤ k ∧ (k : ℝ) ≤ r ∧ a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) x
  have hset (k : ℕ) : MeasurableSet {ω | bad k ω} := by
    by_cases hk : k₀ ≤ k ∧ (k : ℝ) ≤ r
    · have hEq : {ω | bad k ω} = {ω | a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) x} := by
        ext ω; simp [bad, hk]
      rw [hEq]
      exact measurableSet_lt measurable_const
        (admissible_field_measurable_sample P U dens ε₀ Y hY _ x)
    · have hEq : {ω | bad k ω} = ∅ :=
        Set.eq_empty_of_forall_notMem fun ω h => hk ⟨h.1, h.2.1⟩
      rw [hEq]; exact MeasurableSet.empty
  have hunion := lintegral_mul_indicator_exists_le_tsum P w bad
    (fun k => (hw.mul (measurable_const.indicator (hset k))).aemeasurable)
  have hevent (ω : Ω) : Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)ᶜ
      (fun _ => (1 : ℝ≥0∞)) (ω, x) = Set.indicator {ω | ∃ k, bad k ω}
      (fun _ => (1 : ℝ≥0∞)) ω := by
    have hiff : (ω, x) ∈ (admissibleGrowingBarrierSet Y a k₀ r)ᶜ ↔ ω ∈ {ω | ∃ k, bad k ω} := by
      simp only [Set.mem_compl_iff, admissibleGrowingBarrierSet, Set.mem_ofPred_eq, not_forall,
        not_le, bad]
      constructor
      · rintro ⟨k, hk₀, hkr, hk⟩
        exact ⟨k, hk₀, hkr, hk⟩
      · rintro ⟨k, hk₀, hkr, hk⟩
        exact ⟨k, hk₀, hkr, hk⟩
    by_cases h : (ω, x) ∈ (admissibleGrowingBarrierSet Y a k₀ r)ᶜ
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mp h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hiff.mpr h'))]
  calc ∫⁻ ω, admissibleLogWickWeight P Y g (Real.exp (-r)) x ω *
        Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)ᶜ (fun _ => (1 : ℝ≥0∞)) (ω, x) ∂P
      = ∫⁻ ω, w ω * Set.indicator {ω | ∃ k, bad k ω} (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
        apply lintegral_congr; intro ω; rw [hevent]
    _ ≤ ∑' k, ∫⁻ ω, w ω * Set.indicator {ω | bad k ω} (fun _ => (1 : ℝ≥0∞)) ω ∂P := hunion
    _ = ∑' k, Set.indicator {k : ℕ | k₀ ≤ k ∧ (k : ℝ) ≤ r} (fun k => ∫⁻ ω, w ω *
          Set.indicator {ω | a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) x}
            (fun _ => (1 : ℝ≥0∞)) ω ∂P) k := by
        apply tsum_congr
        intro k
        by_cases hk : k₀ ≤ k ∧ (k : ℝ) ≤ r
        · have hEq : {ω | bad k ω} = {ω | a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) x} := by
            ext ω; simp [bad, hk]
          rw [hEq, Set.indicator_of_mem (show k ∈ {k : ℕ | k₀ ≤ k ∧ (k : ℝ) ≤ r} from hk)]
        · have hEq : {ω | bad k ω} = ∅ :=
            Set.eq_empty_of_forall_notMem fun ω h => hk ⟨h.1, h.2.1⟩
          rw [hEq, Set.indicator_of_notMem (show k ∉ {k : ℕ | k₀ ≤ k ∧ (k : ℝ) ≤ r} from hk)]
          simp
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (Real.exp (-((a - gHi) ^ 2 * ((j + k₀ : ℕ) : ℝ) / 16))) := by
        apply tsum_indicator_ge_le_tsum_nat_add k₀ _
          (fun k => ENNReal.ofReal (Real.exp (-((a - gHi) ^ 2 * (k : ℝ) / 16))))
          _ (fun k hk => hk.1)
        intro k hk
        have hk₀k : (k₀ : ℝ) ≤ k := by exact_mod_cast hk.1
        have hkcut : Real.exp (-(k : ℝ)) ≤ ε₀ :=
          le_trans (Real.exp_le_exp.mpr (by linarith)) hk₀cut
        have hkC : C < (k : ℝ) := lt_of_lt_of_le hk₀C hk₀k
        have hrk : Real.exp (-r) ≤ Real.exp (-(k : ℝ)) := Real.exp_le_exp.mpr (by linarith [hk.2])
        have hgapk : g * C ≤ (a - g) * (k : ℝ) / 2 := by
          have h1 : g * C ≤ gHi * C := mul_le_mul_of_nonneg_right hg.2 hC
          have h2 : (a - gHi) * (k₀ : ℝ) ≤ (a - g) * (k : ℝ) := by
            apply mul_le_mul (by linarith [hg.2]) hk₀k (Nat.cast_nonneg _) (by linarith)
          linarith
        refine (htail k hkcut hkC x hx (Real.exp (-r)) (Real.exp_pos _) hrk g a hgpos hga'
          hgapk).trans ?_
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have h1 : 0 ≤ a - gHi := (sub_pos.mpr hga).le
        have h2 : a - gHi ≤ a - g := by linarith [hg.2]
        have hsq : (a - gHi) ^ 2 ≤ (a - g) ^ 2 := pow_le_pow_left₀ h1 h2 2
        have hn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
        have := mul_le_mul_of_nonneg_right hsq hn
        linarith

/-- The expected bad mass on the chart is at most the test bound times the chart reference mass
times the omitted-barrier tail, uniformly for charges in `[gLo, gHi]`. -/
theorem lintegral_badMass_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (gLo gHi a : ℝ), 0 < gLo → gHi < a → ∀ k₀ : ℕ,
      Real.exp (-(k₀ : ℝ)) ≤ ε₀ → C < (k₀ : ℝ) → gHi * C ≤ (a - gHi) * (k₀ : ℝ) / 2 →
      ∀ g ∈ Icc gLo gHi, ∀ r : ℝ, ∀ (L : ℝ) (f : ℂ → ℝ), Measurable f → (∀ x, f x ≤ L) →
        ∫⁻ ω, badMass P U dens K Y g a k₀ r f ω ∂P ≤
          ENNReal.ofReal L * logRegularizationReference U dens K *
            ∑' j : ℕ, ENNReal.ofReal (Real.exp (-((a - gHi) ^ 2 * ((j + k₀ : ℕ) : ℝ) / 16))) := by
  obtain ⟨C, hC, hviol⟩ := wick_root_barrier_violation_le P U dens ε₀ Y hY K hK hKU
  refine ⟨C, hC, ?_⟩
  intro gLo gHi a hgLo hga k₀ hk₀cut hk₀C hk₀gap g hg r L f hf hfL
  set τ := ∑' j : ℕ, ENNReal.ofReal (Real.exp (-((a - gHi) ^ 2 * ((j + k₀ : ℕ) : ℝ) / 16)))
  have hAc : MeasurableSet (admissibleGrowingBarrierSet Y a k₀ r)ᶜ :=
    (admissibleGrowingBarrierSet_measurable P U dens ε₀ Y hY a k₀ r).compl
  have hF := wickEventMass_integrand_measurable P U dens ε₀ Y hY g r _ hAc f hf
  have hswap := lintegral_lintegral_swap (μ := P)
    (ν := (logRegularizationReference U dens).restrict K)
    (f := fun ω x => ENNReal.ofReal (f x) * admissibleLogWickWeight P Y g (Real.exp (-r)) x ω *
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)ᶜ (fun _ => (1 : ℝ≥0∞)) (ω, x))
    hF.aemeasurable
  unfold badMass wickEventMass
  rw [hswap]
  calc ∫⁻ x, ∫⁻ ω, ENNReal.ofReal (f x) * admissibleLogWickWeight P Y g (Real.exp (-r)) x ω *
        Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)ᶜ (fun _ => (1 : ℝ≥0∞)) (ω, x) ∂P
        ∂(logRegularizationReference U dens).restrict K
      ≤ ∫⁻ _, ENNReal.ofReal L * τ ∂(logRegularizationReference U dens).restrict K := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
        have hmeasω : Measurable (fun ω => admissibleLogWickWeight P Y g (Real.exp (-r)) x ω *
            Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)ᶜ (fun _ => (1 : ℝ≥0∞)) (ω, x)) :=
          (admissibleLogWickWeight_measurable_sample P U dens ε₀ Y hY g _ x).mul
            ((measurable_const.indicator hAc).comp (measurable_id.prodMk measurable_const))
        calc ∫⁻ ω, ENNReal.ofReal (f x) * admissibleLogWickWeight P Y g (Real.exp (-r)) x ω *
              Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)ᶜ (fun _ => (1 : ℝ≥0∞))
                (ω, x) ∂P
            = ENNReal.ofReal (f x) * ∫⁻ ω, admissibleLogWickWeight P Y g (Real.exp (-r)) x ω *
              Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)ᶜ (fun _ => (1 : ℝ≥0∞))
                (ω, x) ∂P := by
              rw [← lintegral_const_mul _ hmeasω]
              apply lintegral_congr; intro ω; ring
          _ ≤ ENNReal.ofReal L * τ :=
              mul_le_mul' (ENNReal.ofReal_le_ofReal (hfL x))
                (hviol gLo gHi a hgLo hga k₀ hk₀cut hk₀C hk₀gap g hg r x hx)
    _ = ENNReal.ofReal L * logRegularizationReference U dens K * τ := by
        rw [lintegral_const, Measure.restrict_apply_univ]
        ring

/-- Full cutoff masses of tests with values in `[0, L]` are Cauchy in `L¹(P)` as both cutoffs
vanish, uniformly over such tests and charges in a compact interval admitting barrier
parameters. -/
theorem chartMass_L1_uniform_cauchy_interval
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (gLo gHi a η κ : ℝ) (hgLo : 0 < gLo) (hgLoHi : gLo ≤ gHi) (hga : gHi < a)
    (ha2 : a < 2 * gLo) (hη : 0 < η) (hη1 : η < 1) (hκ : 0 < κ) (hκ2 : κ < 2)
    (hκexp : ∀ g ∈ Icc gLo gHi, g ^ 2 - ((1 - η) ^ 2 * (2 * g - a) ^ 2 / (2 * (1 + η))) ≤ κ)
    (L : ℝ) (hL : 0 ≤ L) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ r s : ℝ, R ≤ r → R ≤ s → ∀ g ∈ Icc gLo gHi, ∀ f : ℂ → ℝ, Measurable f →
      (∀ x, 0 ≤ f x) → (∀ x, f x ≤ L) →
      ∫⁻ ω, ennDist (chartMass P U dens K Y g r f ω) (chartMass P U dens K Y g s f ω) ∂P <
        ENNReal.ofReal ε := by
  obtain ⟨Cb, hCb, hbad⟩ := lintegral_badMass_le P U dens ε₀ Y hY K hK hKU
  obtain ⟨Cv, hCv, hvarB⟩ := hY.coarseVarianceBound K hK hKU
  have hσK := admissible_logRegularization_reference_measure_ne_top P U dens ε₀ Y hY K hK hKU
  set τ : ℕ → ℝ≥0∞ := fun N => ∑' j : ℕ,
    ENNReal.ofReal (Real.exp (-((a - gHi) ^ 2 * ((j + N : ℕ) : ℝ) / 16))) with hτdef
  have hτ : Tendsto τ atTop (𝓝 0) := tendsto_compatible_mixed_double_root_barrier_tail_sum gHi a hga
  have hcoef : ENNReal.ofReal L * logRegularizationReference U dens K ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hσK
  have hbadlim : Tendsto (fun N => ENNReal.ofReal L * logRegularizationReference U dens K * τ N)
      atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul hτ (Or.inr hcoef)
    rwa [mul_zero] at h
  have hε3 : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 3) := ENNReal.ofReal_pos.mpr (by linarith)
  have hev : ∀ᶠ k₀ : ℕ in atTop, Real.exp (-(k₀ : ℝ)) ≤ ε₀ ∧ Cb < (k₀ : ℝ) ∧
      gHi * Cb ≤ (a - gHi) * (k₀ : ℝ) / 2 ∧ Cv + 1 ≤ (k₀ : ℝ) ∧
      ENNReal.ofReal L * logRegularizationReference U dens K * τ k₀ < ENNReal.ofReal (ε / 3) := by
    have hpos : 0 < a - gHi := sub_pos.mpr hga
    obtain ⟨N, hN⟩ := exists_natural_scale_after_covariance_errors (max Cb Cv + 1) 1 1 1 ε₀
      (by positivity) one_pos one_pos one_pos hY.cutoffPositive
    obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 * (gHi * Cb) / (a - gHi))
    filter_upwards [eventually_ge_atTop N, eventually_ge_atTop N₂,
      hbadlim.eventually (gt_mem_nhds hε3)] with k₀ hk₀N hk₀N₂ hk₀bad
    have hNk : (N : ℝ) ≤ k₀ := by exact_mod_cast hk₀N
    have hN₂k : (N₂ : ℝ) ≤ k₀ := by exact_mod_cast hk₀N₂
    refine ⟨le_trans (Real.exp_le_exp.mpr (by linarith)) hN.1, ?_, ?_, ?_, hk₀bad⟩
    · have := hN.2.1
      have : Cb ≤ max Cb Cv := le_max_left _ _
      linarith
    · have h := (div_lt_iff₀ hpos).mp (lt_of_lt_of_le hN₂ hN₂k)
      linarith
    · have := hN.2.1
      have : Cv ≤ max Cb Cv := le_max_right _ _
      linarith
  obtain ⟨k₀, hk₀cut, hk₀C, hk₀gap, hk₀var, hk₀bad⟩ := hev.exists
  have hvar : ∀ k : ℕ, k₀ ≤ k → ∀ x ∈ K,
      1 ≤ gaussianVariance P (fun ω => Y ω (Real.exp (-(k : ℝ))) x) := by
    intro k hk x hx
    have hkk : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
    have hkcut : Real.exp (-(k : ℝ)) ≤ ε₀ := le_trans (Real.exp_le_exp.mpr (by linarith)) hk₀cut
    have h := (abs_le.mp (hvarB k hkcut x hx)).1
    linarith
  obtain ⟨R, hR⟩ := goodMass_L1_uniform_cauchy P U dens ε₀ Y hY K hK hKU gLo gHi a η κ hgLo
    hgLoHi hga ha2 hη hη1 hκ hκ2 hκexp k₀ hk₀cut hvar L hL (ε / 3) (by linarith)
  refine ⟨R, ?_⟩
  intro r s hr hs g hg f hf hf0 hfL
  have hA (t : ℝ) := admissibleGrowingBarrierSet_measurable P U dens ε₀ Y hY a k₀ t
  have hJm (t : ℝ) : Measurable (goodMass P U dens K Y g a k₀ t f) :=
    wickEventMass_measurable P U dens ε₀ Y hY _ g t _ (hA t) f hf
  have hBm (t : ℝ) : Measurable (badMass P U dens K Y g a k₀ t f) :=
    wickEventMass_measurable P U dens ε₀ Y hY _ g t _ (hA t).compl f hf
  have hpt (ω : Ω) : ennDist (chartMass P U dens K Y g r f ω) (chartMass P U dens K Y g s f ω) ≤
      ennDist (goodMass P U dens K Y g a k₀ r f ω) (goodMass P U dens K Y g a k₀ s f ω) +
        (badMass P U dens K Y g a k₀ r f ω + badMass P U dens K Y g a k₀ s f ω) := by
    rw [chartMass_eq_good_add_bad P U dens ε₀ Y hY K g a k₀ r f hf ω,
      chartMass_eq_good_add_bad P U dens ε₀ Y hY K g a k₀ s f hf ω]
    exact (ennDist_add_add_le _ _ _ _).trans (add_le_add le_rfl (ennDist_le_add _ _))
  have hbadr := hbad gLo gHi a hgLo hga k₀ hk₀cut hk₀C hk₀gap g hg r L f hf hfL
  have hbads := hbad gLo gHi a hgLo hga k₀ hk₀cut hk₀C hk₀gap g hg s L f hf hfL
  calc _ ≤ ∫⁻ ω, ennDist (goodMass P U dens K Y g a k₀ r f ω)
          (goodMass P U dens K Y g a k₀ s f ω) +
        (badMass P U dens K Y g a k₀ r f ω + badMass P U dens K Y g a k₀ s f ω) ∂P :=
        lintegral_mono hpt
    _ = ∫⁻ ω, ennDist (goodMass P U dens K Y g a k₀ r f ω)
          (goodMass P U dens K Y g a k₀ s f ω) ∂P +
        (∫⁻ ω, badMass P U dens K Y g a k₀ r f ω ∂P +
          ∫⁻ ω, badMass P U dens K Y g a k₀ s f ω ∂P) := by
        rw [lintegral_add_left (ennDist_measurable (hJm r) (hJm s)), lintegral_add_left (hBm r)]
    _ < ENNReal.ofReal (ε / 3) + (ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3)) := by
        have hle : ∫⁻ ω, badMass P U dens K Y g a k₀ r f ω ∂P +
            ∫⁻ ω, badMass P U dens K Y g a k₀ s f ω ∂P ≤
            ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) :=
          add_le_add (hbadr.trans hk₀bad.le) (hbads.trans hk₀bad.le)
        exact ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
          ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩) hle) (hR r s hr hs g hg f hf hf0 hfL) hle
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith),
          ← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1
        ring

end DOZZ.Assembly
