/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.IsCircleAverage
public import DOZZ.Statements.Defs.IsEquatorGFF
public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.Statements.GMC.IsCenteredJointlyGaussian
public import DOZZ.Statements.GMC.IsGaussianL2Limit
public import DOZZ.GFFStructure.GaussianClosure
public import DOZZ.GMC.Construction.CircleAverageJointVersion
public import DOZZ.GMC.Construction.GMCUniqueAe
public import DOZZ.GMC.FiniteGaussianTilt
public import DOZZ.GMC.GaussianInputs
public import Mathlib.MeasureTheory.Constructions.Cylinders

/-! Finite-coordinate Cameron--Martin transport for test evaluations and circle averages. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

noncomputable def testCircleCoordinate {Ω : Type*} (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (r : ℝ) : ℂ ⊕ TestFn → Ω → ℝ :=
  Sum.elim (fun x ω => Xc ω x r) (fun f ω => X ω f)

/-- A fixed cutoff measure is measurable for the raw field sigma algebra whenever its circle
field has a raw jointly measurable version. -/
private theorem regularizedGMC_raw_measurable_of_joint
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ)
    (hRaw : Measurable[(equatorGFFRawDistributionSigma X).prod (borel ℂ)]
      (fun p : Ω × ℂ => Xc p.1 p.2 r)) :
    Measurable[equatorGFFRawDistributionSigma X]
      (fun ω => regularizedGMC P Xc γ r ω) := by
  classical
  let _ : IsProbabilityMeasure P := hX.1
  have hVmeas : Measurable (fun x : ℂ => ∫ ω, Xc ω x r ^ 2 ∂P) := by
    let q : ℂ → Ω → ℝ := fun x ω => Xc ω x r ^ 2
    have hq : Measurable (Function.uncurry q) := by
      have hbase : Measurable (fun p : ℂ × Ω => Xc p.2 p.1 r) :=
        (hXc.1 r).comp measurable_swap
      have hEq : (fun p : ℂ × Ω => Xc p.2 p.1 r ^ 2) =
          fun p => Xc p.2 p.1 r * Xc p.2 p.1 r := by
        funext p
        ring
      change Measurable (fun p : ℂ × Ω => Xc p.2 p.1 r ^ 2)
      rw [hEq]
      exact hbase.mul hbase
    change Measurable (fun x => ∫ ω, q x ω ∂P)
    exact hq.stronglyMeasurable.integral_prod_right.measurable
  let V : ℂ → ℝ := fun x => ∫ ω, Xc ω x r ^ 2 ∂P
  have hVmeas' : Measurable V := by simpa [V] using hVmeas
  have hnormPlus : Measurable (fun x : ℂ => normPlus x) := by
    unfold normPlus
    exact measurable_const.max measurable_norm
  let density : Ω × ℂ → ℝ≥0∞ := fun p => ENNReal.ofReal
    (Real.exp (γ * Xc p.1 p.2 r - γ ^ 2 / 2 * V p.2) * normPlus p.2 ^ (-4 : ℝ))
  have hdensity : Measurable[(equatorGFFRawDistributionSigma X).prod (borel ℂ)] density := by
    have hfield : Measurable[(equatorGFFRawDistributionSigma X).prod (borel ℂ)]
        (fun p : Ω × ℂ => Xc p.1 p.2 r) := hRaw
    have hnorm : Measurable[(equatorGFFRawDistributionSigma X).prod (borel ℂ)]
        (fun p : Ω × ℂ => normPlus p.2) :=
      hnormPlus.comp measurable_snd
    have hvariance : Measurable[(equatorGFFRawDistributionSigma X).prod (borel ℂ)]
        (fun p : Ω × ℂ => V p.2) :=
      hVmeas'.comp measurable_snd
    dsimp [density]
    have hExponent : Measurable[(equatorGFFRawDistributionSigma X).prod (borel ℂ)]
        (fun p : Ω × ℂ => γ * Xc p.1 p.2 r - γ ^ 2 / 2 * V p.2) := by
      have hleft := hfield.const_mul γ
      have hright := hvariance.const_mul (γ ^ 2 / 2)
      change Measurable[(equatorGFFRawDistributionSigma X).prod (borel ℂ)]
        ((fun p : Ω × ℂ => γ * Xc p.1 p.2 r) -
          fun p => γ ^ 2 / 2 * V p.2)
      simpa [mul_comm] using hleft.sub hright
    have hWeight : Measurable[(equatorGFFRawDistributionSigma X).prod (borel ℂ)]
        (fun p : Ω × ℂ => normPlus p.2 ^ (-4 : ℝ)) := by
      fun_prop
    exact ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp hExponent).mul hWeight)
  refine @Measure.measurable_of_measurable_coe ℂ Ω _
    (equatorGFFRawDistributionSigma X) (fun ω => regularizedGMC P Xc γ r ω) ?_
  intro A hA
  let G : Ω × ℂ → ℝ≥0∞ := fun p => if p.2 ∈ A then density p else 0
  have hG : Measurable[(equatorGFFRawDistributionSigma X).prod (borel ℂ)] G :=
    Measurable.ite (hA.preimage measurable_snd) hdensity measurable_const
  have hsection (ω : Ω) :
      (∫⁻ x in A, density (ω, x) ∂volume) = ∫⁻ x, G (ω, x) ∂volume := by
    rw [← lintegral_indicator hA]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ A <;> simp [G, hx]
  have hEval : (fun ω => regularizedGMC P Xc γ r ω A) =
      fun ω => ∫⁻ x, G (ω, x) ∂volume := by
    funext ω
    change (volume.withDensity (fun x => ENNReal.ofReal
      (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * V x) * normPlus x ^ (-4 : ℝ))) A) = _
    rw [withDensity_apply _ hA]
    change (∫⁻ x in A, density (ω, x) ∂volume) = _
    exact hsection ω
  rw [hEval]
  exact @Measurable.lintegral_prod_right' Ω ℂ
    (equatorGFFRawDistributionSigma X) (borel ℂ) volume _ G hG

/-- The canonical circle-average witness can be chosen jointly measurable for the raw field sigma
algebra at each radius. -/
private theorem exists_raw_equatorGFF_circle_average_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (X : Ω → Distr) (hX : IsEquatorGFF P X) :
    ∃ Xc : Ω → ℂ → ℝ → ℝ, IsCircleAverage P X Xc ∧
      ∀ r, Measurable[(equatorGFFRawDistributionSigma X).prod (borel ℂ)]
        (fun p : Ω × ℂ => Xc p.1 p.2 r) := by
  let _ : IsProbabilityMeasure P := hX.1
  obtain ⟨f, W, Y, hgap, hcross, hW, hY, hproc, hmean, hcov⟩ :=
    exists_equatorGFF_circle_L2_geometry X hX
  have hmeas (p : ℂ × ℝ) : Measurable (Y p) := (hY p).2.1
  have hmem (p : ℂ × ℝ) : MemLp (Y p) 2 P := (hY p).2.2.1
  have hmod (r : ℝ) := exists_continuous_circleL2_modification_at_radius
    Y hmeas hmem hproc hmean hcov r
  choose Z hZmeas hZcont hZeq using hmod
  have hjoint (r : ℝ) := exists_raw_joint_continuous_modification P
    (equatorGFFRawDistributionSigma X)
    (fun ω x => Z r x ω) (ae_of_all P (hZcont r))
    (fun x => ⟨Y (x, r), (hY (x, r)).1, (hZeq r x).symm⟩)
  choose G hGjoint hGae using hjoint
  let Xc : Ω → ℂ → ℝ → ℝ := fun ω x r => G r ω x
  have hmap : Measurable[mΩ] (fun ω => fun g : TestFn => X ω g) :=
    measurable_pi_iff.mpr (fun g => (hX.2 g).1)
  have hm0 : equatorGFFRawDistributionSigma X ≤ mΩ := by
    dsimp [equatorGFFRawDistributionSigma]
    exact hmap.comap_le
  have hprod : (equatorGFFRawDistributionSigma X).prod (borel ℂ) ≤ mΩ.prod (borel ℂ) := by
    rw [MeasurableSpace.prod, MeasurableSpace.prod]
    exact sup_le_sup (MeasurableSpace.comap_mono hm0) le_rfl
  have hmeasXc (r : ℝ) : Measurable (fun p : Ω × ℂ => Xc p.1 p.2 r) :=
    (hGjoint r).mono hprod le_rfl
  have hXcY (x : ℂ) (r : ℝ) : (fun ω => Xc ω x r) =ᵐ[P] fun ω => Y (x, r) ω := by
    filter_upwards [hGae r, hZeq r x] with ω hG hZ
    exact (hG x).trans hZ
  refine ⟨Xc, ?_, hGjoint⟩
  refine ⟨hmeasXc, fun x r => ?_, ?_⟩
  · exact MemLp.ae_eq (hXcY x r).symm (hmem (x, r))
  · intro x r g hg
    let p : ℂ × ℝ := (x, r)
    let U : ℕ → Lp ℝ 2 P := fun n =>
      (equatorGFF_test_memLp X hX (g n)).toLp (fun ω => X ω (g n))
    have hUT : Tendsto U atTop (𝓝 (W p)) := by
      exact equatorGFF_testL2_tendsto_to_circle_limit X hX x r
        (f p) (hgap p) (W p) (hW p) g hg
    have hTarget : (fun ω => Xc ω x r) =ᵐ[P] ⇑(W p) := by
      exact (hXcY x r).trans (hY p).2.2.2.1
    exact tendsto_eLpNorm_sub_of_L2_versions P U (W p)
      (fun n ω => X ω (g n)) (fun ω => Xc ω x r)
      (fun n => (equatorGFF_test_memLp X hX (g n)).coeFn_toLp.symm)
      hTarget hUT

/-- Adjoining one Gaussian `L²` limit to any finite family of test evaluations and circle
averages preserves joint Gaussianity. -/
private theorem testCircleFamily_with_L_isGaussianProcess
    {Ω T : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (r : ℝ)
    (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L)
    (coord : T → ℂ ⊕ TestFn) :
    IsGaussianProcess
      (fun i : Option T => fun ω =>
        match i with
        | none => L ω
        | some t => testCircleCoordinate X Xc r (coord t) ω) P := by
  let _ : IsProbabilityMeasure P := hX.1
  obtain ⟨hLmem, fL, hLapprox⟩ := hL
  let Z : ℕ → Option T → Ω → ℝ := fun n i ω =>
    match i with
    | none => X ω (fL n)
    | some t => testCircleCoordinate X Xc r (coord t) ω
  let W : Option T → Ω → ℝ := fun i ω =>
    match i with
    | none => L ω
    | some t => testCircleCoordinate X Xc r (coord t) ω
  have hBase := circleAverage_tests_isGaussianProcess X Xc hX hXc
  have hBaseCut : IsGaussianProcess
      (fun c => testCircleCoordinate X Xc r c) P := by
    convert hBase.comp_right (fun c : ℂ ⊕ TestFn =>
      Sum.elim (fun x => Sum.inl (x, r)) Sum.inr c) using 1
    funext c ω
    cases c <;> rfl
  have hZ : ∀ n, IsGaussianProcess (Z n) P := by
    intro n
    have hMapped := hBaseCut.comp_right (fun i : Option T =>
      match i with
      | none => Sum.inr (fL n)
      | some t => coord t)
    have hMapped' : IsGaussianProcess (fun i => fun ω => Z n i ω) P := by
      convert hMapped using 1
      funext i ω
      cases i <;> rfl
    simpa [Z] using hMapped'
  have hW : ∀ i, MemLp (W i) 2 P := by
    intro i
    cases i with
    | none => exact hLmem
    | some t =>
        cases hcoord : coord t with
        | inl x =>
            simpa [W, testCircleCoordinate, hcoord] using hXc.2.1 x r
        | inr f =>
            simpa [W, testCircleCoordinate, hcoord] using equatorGFF_test_memLp X hX f
  have hApprox : ∀ i,
      Tendsto (fun n => eLpNorm (fun ω => Z n i ω - W i ω) 2 P)
        atTop (𝓝 0) := by
    intro i
    cases i with
    | none =>
        have hcomm : ∀ n,
            eLpNorm (fun ω => X ω (fL n) - L ω) 2 P =
              eLpNorm (fun ω => L ω - X ω (fL n)) 2 P := by
          intro n
          exact eLpNorm_sub_comm _ _ _ _
        simpa only [Z, W, hcomm] using hLapprox
    | some t =>
        convert (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0)) using 1
        · funext n
          simp [Z, W]
  exact isGaussianProcess_of_eLpNorm_sub Z W hZ hW hApprox

/-- Finite-dimensional tilt for any selected collection of test and circle-average coordinates.
The only nonzero tilt coefficient is on `L`; consequently all selected coordinates shift by their
covariance with `L`. -/
theorem equatorGFF_finite_test_circle_tilt
    {Ω T : Type*} [MeasurableSpace Ω] [Fintype T]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (r : ℝ)
    (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L)
    (coord : T → ℂ ⊕ TestFn) (t : ℝ)
    (F : (Option T → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (t * L ω - t ^ 2 / 2 * gaussianVariance P L)) *
      F (fun i => match i with
        | none => L ω
        | some j => testCircleCoordinate X Xc r (coord j) ω) ∂P) =
    ∫⁻ ω, F (fun i =>
      (match i with
        | none => L ω
        | some j => testCircleCoordinate X Xc r (coord j) ω) +
      match i with
        | none => t * gaussianVariance P L
        | some j => t * gaussianCovariance P
            (fun ω => testCircleCoordinate X Xc r (coord j) ω) L) ∂P := by
  let Z : Ω → Option T → ℝ := fun ω i =>
    match i with
    | none => L ω
    | some j => testCircleCoordinate X Xc r (coord j) ω
  let a : Option T → ℝ := fun i => if i.isNone then t else 0
  let _ : IsProbabilityMeasure P := hX.1
  have hProc := testCircleFamily_with_L_isGaussianProcess P X hX Xc hXc r L hL coord
  have hMeanL : (∫ ω, L ω ∂P) = 0 := by
    obtain ⟨hLmem, fL, hLapprox⟩ := hL
    have hcomm : ∀ n,
        eLpNorm (fun ω => X ω (fL n) - L ω) 2 P =
          eLpNorm (fun ω => L ω - X ω (fL n)) 2 P := by
      intro n
      exact eLpNorm_sub_comm _ _ _ _
    have hLapprox' : Tendsto
        (fun n => eLpNorm (fun ω => X ω (fL n) - L ω) 2 P) atTop (𝓝 0) := by
      simpa only [hcomm] using hLapprox
    exact integral_eq_zero_of_eLpNorm_sub
      (fun n => equatorGFF_test_memLp X hX (fL n)) hLmem
      (fun n => equatorGFF_test_integral X hX (fL n)) hLapprox'
  have hMeanCoord (j : T) :
    (∫ ω, testCircleCoordinate X Xc r (coord j) ω ∂P) = 0 := by
    cases hcoord : coord j with
    | inl x =>
        change (∫ ω, Xc ω x r ∂P) = 0
        exact (circleAverage_isGaussianProcess P X Xc hX hXc).2 x r
    | inr f => exact equatorGFF_test_integral X hX f
  have hCentered : IsCenteredJointlyGaussian P Z := by
    apply centeredJointlyGaussian_of_isGaussianProcess P (fun i ω => Z ω i) ?_ ?_
    · simpa [Z] using hProc
    · intro i
      cases i with
      | none => exact hMeanL
      | some j => exact hMeanCoord j
  have hTilt := finite_gaussian_tilt P Z hCentered a F hF
  have hExponent (ω : Ω) :
      (∑ i, a i * Z ω i) -
        (∑ i, ∑ j, a i * gaussianCovariance P (fun ω => Z ω i)
          (fun ω => Z ω j) * a j) / 2 =
      t * L ω - t ^ 2 / 2 * gaussianVariance P L := by
    simp [a, Z, gaussianVariance, gaussianCovariance]
    ring
  have hShift (ω : Ω) (i : Option T) :
      Z ω i + ∑ j, gaussianCovariance P (fun ω => Z ω i)
        (fun ω => Z ω j) * a j =
      Z ω i + match i with
        | none => t * gaussianVariance P L
        | some j => t * gaussianCovariance P (fun ω => Z ω j) L := by
    cases i with
    | none =>
        simp [a, Z, gaussianVariance, gaussianCovariance]
        ring
    | some k =>
        simp [a, Z, gaussianCovariance]
        ring
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (Real.exp
        ((∑ i, a i * Z ω i) -
          (∑ i, ∑ j, a i * gaussianCovariance P (fun ω => Z ω i)
            (fun ω => Z ω j) * a j) / 2)) * F (Z ω) ∂P := by
          apply lintegral_congr_ae
          exact ae_of_all _ (fun ω => by
            change ENNReal.ofReal (Real.exp (t * L ω - t ^ 2 / 2 * gaussianVariance P L)) *
              F (Z ω) = ENNReal.ofReal (Real.exp
                ((∑ i, a i * Z ω i) -
                  (∑ i, ∑ j, a i * gaussianCovariance P (fun ω => Z ω i)
                    (fun ω => Z ω j) * a j) / 2)) * F (Z ω)
            rw [← hExponent ω])
    _ = ∫⁻ ω, F (fun i => Z ω i +
        ∑ j, gaussianCovariance P (fun ω => Z ω i)
          (fun ω => Z ω j) * a j) ∂P := hTilt
    _ = _ := by
          apply lintegral_congr_ae
          exact ae_of_all _ (fun ω => by
            change F (fun i => Z ω i + ∑ j, gaussianCovariance P
              (fun ω => Z ω i) (fun ω => Z ω j) * a j) =
              F (fun i => (match i with
                | none => L ω
                | some j => testCircleCoordinate X Xc r (coord j) ω) + match i with
                  | none => t * gaussianVariance P L
                  | some j => t * gaussianCovariance P
                    (fun ω => testCircleCoordinate X Xc r (coord j) ω) L)
            apply congrArg F
            funext i
            change Z ω i + ∑ j, gaussianCovariance P (fun ω => Z ω i)
              (fun ω => Z ω j) * a j = Z ω i + match i with
                | none => t * gaussianVariance P L
                | some j => t * gaussianCovariance P (fun ω => Z ω j) L
            exact hShift ω i)

/-- Cameron--Martin transport of the full product-sigma process of test evaluations together with
the fixed-radius circle averages. This is the law-level input before applying a measurable
cutoff-chaos map. -/
theorem equatorGFF_tilted_test_circle_law
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (r t : ℝ)
    (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L) :
    Measure.map (fun ω (c : ℂ ⊕ TestFn) => testCircleCoordinate X Xc r c ω)
        (P.withDensity (fun ω => ENNReal.ofReal (Real.exp
          (t * L ω - t ^ 2 / 2 * gaussianVariance P L)))) =
      Measure.map (fun ω c => testCircleCoordinate X Xc r c ω +
        t * gaussianCovariance P (fun ω => testCircleCoordinate X Xc r c ω) L) P := by
  classical
  let eval : Ω → ℂ ⊕ TestFn → ℝ := fun ω c => testCircleCoordinate X Xc r c ω
  let evalShift : Ω → ℂ ⊕ TestFn → ℝ := fun ω c => eval ω c +
    t * gaussianCovariance P (fun ω => eval ω c) L
  let density : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp
    (t * L ω - t ^ 2 / 2 * gaussianVariance P L))
  let μ : Measure (ℂ ⊕ TestFn → ℝ) := Measure.map eval (P.withDensity density)
  let ν : Measure (ℂ ⊕ TestFn → ℝ) := Measure.map evalShift P
  have hEval : Measurable eval := by
    rw [measurable_pi_iff]
    intro c
    cases c with
    | inl x =>
        exact (hXc.1 r).comp (measurable_id.prodMk measurable_const)
    | inr f => exact (hX.2 f).1
  have hEvalShift : Measurable evalShift := by
    rw [measurable_pi_iff]
    intro c
    exact (measurable_pi_iff.mp hEval c).add measurable_const
  have hDensity : AEMeasurable density P := by
    have hlog : AEMeasurable (fun ω => t * L ω - t ^ 2 / 2 * gaussianVariance P L) P := by
      exact (hL.1.aemeasurable.const_mul t).sub (measurable_const.aemeasurable)
    exact (Real.measurable_exp.comp_aemeasurable hlog).ennreal_ofReal
  have hCylinder (s : Finset (ℂ ⊕ TestFn)) (S : Set (∀ i : s, ℝ))
      (hS : MeasurableSet S) :
      μ (MeasureTheory.cylinder s S) = ν (MeasureTheory.cylinder s S) := by
    let coord : s → ℂ ⊕ TestFn := fun i => i.val
    let family : Ω → Option s → ℝ := fun ω i =>
      match i with
      | none => L ω
      | some j => eval ω (coord j)
    let project : (Option s → ℝ) → (∀ i : s, ℝ) := fun y i => y (some i)
    let F : (Option s → ℝ) → ℝ≥0∞ := S.indicator (fun _ => 1) ∘ project
    have hProject : Measurable project := by fun_prop
    have hF : Measurable F := by
      dsimp [F]
      exact (measurable_const.indicator hS).comp hProject
    have hTilt := equatorGFF_finite_test_circle_tilt P X hX Xc hXc r L hL
      coord t F hF
    have hFinite :
        (∫⁻ ω, density ω * F (family ω) ∂P) =
          ∫⁻ ω, F (fun i => family ω i + match i with
            | none => t * gaussianVariance P L
            | some j => t * gaussianCovariance P (fun ω => eval ω (coord j)) L) ∂P := by
      change (∫⁻ ω, ENNReal.ofReal (Real.exp
          (t * L ω - t ^ 2 / 2 * gaussianVariance P L)) *
          F (fun i => match i with
            | none => L ω
            | some j => testCircleCoordinate X Xc r (coord j) ω) ∂P) =
        ∫⁻ ω, F (fun i =>
          (match i with
            | none => L ω
            | some j => testCircleCoordinate X Xc r (coord j) ω) +
          match i with
            | none => t * gaussianVariance P L
            | some j => t * gaussianCovariance P
                (fun ω => testCircleCoordinate X Xc r (coord j) ω) L) ∂P
      exact hTilt
    have hPreEval : MeasurableSet (eval ⁻¹' MeasureTheory.cylinder s S) :=
      (hS.cylinder).preimage hEval
    have hPreShift : MeasurableSet (evalShift ⁻¹' MeasureTheory.cylinder s S) :=
      (hS.cylinder).preimage hEvalShift
    have hLeft : μ (MeasureTheory.cylinder s S) =
        ∫⁻ ω, density ω * F (family ω) ∂P := by
      dsimp [μ]
      rw [Measure.map_apply hEval (hS.cylinder), withDensity_apply density hPreEval,
        ← lintegral_indicator hPreEval]
      apply lintegral_congr_ae
      exact ae_of_all _ (fun ω => by
        have hproject : project (family ω) = s.restrict (eval ω) := by
          funext i
          simp [project, family, coord, eval]
        by_cases hx : eval ω ∈ MeasureTheory.cylinder s S
        · have hxS : s.restrict (eval ω) ∈ S := by simpa using hx
          simp [F, hproject, hx, hxS]
        · have hxS : s.restrict (eval ω) ∉ S := by simpa using hx
          simp [F, hproject, hx, hxS])
    have hRight : ν (MeasureTheory.cylinder s S) =
        ∫⁻ ω, F (fun i => family ω i + match i with
          | none => t * gaussianVariance P L
          | some j => t * gaussianCovariance P (fun ω => eval ω (coord j)) L) ∂P := by
      dsimp [ν]
      rw [Measure.map_apply hEvalShift (hS.cylinder)]
      calc
        P (evalShift ⁻¹' MeasureTheory.cylinder s S) =
            ∫⁻ ω, (evalShift ⁻¹' MeasureTheory.cylinder s S).indicator
              (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
                symm
                rw [lintegral_indicator_const hPreShift 1]
                simp
        _ = ∫⁻ ω, F (fun i => family ω i + match i with
            | none => t * gaussianVariance P L
            | some j => t * gaussianCovariance P (fun ω => eval ω (coord j)) L) ∂P := by
              apply lintegral_congr_ae
              exact ae_of_all _ (fun ω => by
                have hcoord (i : s) :
                    family ω (some i) + t * gaussianCovariance P
                      (fun ω => eval ω (coord i)) L = evalShift ω (coord i) := by
                  simp [family, evalShift, coord]
                have hproject : project (fun i => family ω i + match i with
                    | none => t * gaussianVariance P L
                    | some j => t * gaussianCovariance P (fun ω => eval ω (coord j)) L) =
                    s.restrict (evalShift ω) := by
                  funext i
                  exact hcoord i
                by_cases hx : evalShift ω ∈ MeasureTheory.cylinder s S
                · have hxS : s.restrict (evalShift ω) ∈ S := by simpa using hx
                  simp [F, hproject, hx, hxS]
                · have hxS : s.restrict (evalShift ω) ∉ S := by simpa using hx
                  simp [F, hproject, hx, hxS])
    exact hLeft.trans (hFinite.trans hRight.symm)
  let C : Set (Set (ℂ ⊕ TestFn → ℝ)) :=
    MeasureTheory.measurableCylinders (fun _ : ℂ ⊕ TestFn => ℝ)
  have hCylinders : ∀ A ∈ C, μ A = ν A := by
    intro A hA
    obtain ⟨s, S, hS, rfl⟩ :=
      (MeasureTheory.mem_measurableCylinders (α := fun _ : ℂ ⊕ TestFn => ℝ) A).mp hA
    exact hCylinder s S hS
  have hUnivC : Set.univ ∈ C :=
    MeasureTheory.univ_mem_measurableCylinders (fun _ : ℂ ⊕ TestFn => ℝ)
  have hνUniv : ν Set.univ = 1 := by
    rw [Measure.map_apply hEvalShift MeasurableSet.univ]
    exact hX.1.measure_univ
  have hμUniv : μ Set.univ = 1 := by rw [hCylinders Set.univ hUnivC, hνUniv]
  have hMeasuresUniv : μ Set.univ = ν Set.univ := by rw [hμUniv, hνUniv]
  have hFiniteμ : IsFiniteMeasure μ := ⟨by rw [hμUniv]; simp⟩
  exact @ext_of_generate_finite (ℂ ⊕ TestFn → ℝ) _ μ ν C
    (by simpa [C] using
      (MeasureTheory.generateFrom_measurableCylinders (α := fun _ : ℂ ⊕ TestFn => ℝ)).symm)
    MeasureTheory.isPiSystem_measurableCylinders hFiniteμ hCylinders hMeasuresUniv

end DOZZ.Proofs
