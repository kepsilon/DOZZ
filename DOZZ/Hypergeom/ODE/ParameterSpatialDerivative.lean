/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ParameterSeriesFamily
public import DOZZ.Hypergeom.ODE.ParameterSeriesUniformFDeriv
public import DOZZ.Hypergeom.ODE.SeriesSpatialDerivative

/-! Parameter regularity of spatial derivatives on the ordinary-series disk. -/

@[expose] public section

open Filter
open scoped Topology

namespace DOZZ.Proofs

private theorem gaussParameterPoleFreeDomain_shift_add_one
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussParameterPoleFreeDomain) :
    (p.1 + 1, p.2.1 + 1, p.2.2 + 1) ∈ gaussParameterPoleFreeDomain := by
  intro n hn
  apply hp (n + 1)
  have h' : p.2.2 = -((n + 1 : ℕ) : ℂ) := by
    push_cast at hn ⊢
    linear_combination hn
  exact h'

/-- The spatial derivative of any characterized family is the shifted-series value on the unit
disk. This uses only its ordinary-series characterization and is independent of the chosen
global continuation. -/
theorem IsGaussHypergeometricFamily.hasDerivAt_unitDisk
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (a b c z : ℂ)
    (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) (hz : ‖z‖ < 1) :
    HasDerivAt (H a b c)
      (a * b / c * H (a + 1) (b + 1) (c + 1) z) z := by
  have hchar := hH a b c hc
  have hseries := ordinaryHypergeometric_hasDerivAt_unitDisk a b c z hc hz
  have hzball : z ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hnear : (H a b c) =ᶠ[𝓝 z] ordinaryHypergeometric a b c := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzball] with w hw
    have hwnorm : ‖w‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hw
    exact hchar.2 w hwnorm
  have hseriesShift : H (a + 1) (b + 1) (c + 1) z =
      ordinaryHypergeometric (a + 1) (b + 1) (c + 1) z := by
    have hcShift : ∀ n : ℕ, c + 1 ≠ -(n : ℂ) := by
      intro n heq
      apply hc (n + 1)
      have h' : c = -((n + 1 : ℕ) : ℂ) := by
        push_cast at heq ⊢
        linear_combination heq
      exact h'
    exact (hH (a + 1) (b + 1) (c + 1) hcShift).2 z hz
  rw [← hseriesShift] at hseries
  exact hseries.congr_of_eventuallyEq hnear

/-- At each admissible parameter tuple, the spatial derivative at a fixed unit-disk point varies
holomorphically with all three parameters. This supplies the derivative entries in the midpoint
Cramer formulas for the connection matrix. -/
theorem IsGaussHypergeometricFamily.differentiableAt_params_deriv_unitDisk
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) {p : ℂ × ℂ × ℂ}
    (hp : p ∈ gaussParameterPoleFreeDomain) {z : ℂ} (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ =>
      deriv (fun w => H q.1 q.2.1 q.2.2 w) z) p := by
  let shift : ℂ × ℂ × ℂ → ℂ × ℂ × ℂ := fun q => q + ((1 : ℂ), 1, 1)
  have hpShift : shift p ∈ gaussParameterPoleFreeDomain := by
    exact gaussParameterPoleFreeDomain_shift_add_one hp
  have hshiftOn :=
    IsGaussHypergeometricFamily.differentiableOn_params_unitDisk hH hz
  have hshiftAt : DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ => H q.1 q.2.1 q.2.2 z) (shift p) :=
    (hshiftOn (shift p) hpShift).differentiableAt
      (gaussParameterPoleFreeDomain_isOpen.mem_nhds hpShift)
  have hshiftMap : DifferentiableAt ℂ shift p := by
    fun_prop
  have hshiftComp : DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ => H (q.1 + 1) (q.2.1 + 1) (q.2.2 + 1) z) p := by
    change DifferentiableAt ℂ
      ((fun q : ℂ × ℂ × ℂ => H q.1 q.2.1 q.2.2 z) ∘ shift) p
    exact hshiftAt.comp p hshiftMap
  have hpC : p.2.2 ≠ 0 := by
    intro hzero
    exact hp 0 (by simpa using hzero)
  have hfactor : DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ => q.1 * q.2.1 / q.2.2) p := by
    fun_prop (disch := assumption)
  have hright : DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ =>
        q.1 * q.2.1 / q.2.2 * H (q.1 + 1) (q.2.1 + 1) (q.2.2 + 1) z) p :=
    hfactor.mul hshiftComp
  have hlocal : (fun q : ℂ × ℂ × ℂ =>
      deriv (fun w => H q.1 q.2.1 q.2.2 w) z) =ᶠ[𝓝 p]
      (fun q =>
        q.1 * q.2.1 / q.2.2 * H (q.1 + 1) (q.2.1 + 1) (q.2.2 + 1) z) := by
    filter_upwards [gaussParameterPoleFreeDomain_isOpen.mem_nhds hp] with q hq
    exact (IsGaussHypergeometricFamily.hasDerivAt_unitDisk hH
      q.1 q.2.1 q.2.2 z hq hz).deriv
  exact hright.congr_of_eventuallyEq hlocal

/-- On the ordinary-series disk, the full first-order state `(H, H')` varies
parameter-differentiably. This packages the value and spatial-derivative regularity as the initial
data for a parameterized Picard disk. -/
theorem IsGaussHypergeometricFamily.differentiableAt_params_state_unitDisk
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) {p : ℂ × ℂ × ℂ}
    (hp : p ∈ gaussParameterPoleFreeDomain) {z : ℂ} (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ =>
      (H q.1 q.2.1 q.2.2 z, deriv (fun w => H q.1 q.2.1 q.2.2 w) z)) p := by
  have hvalueOn := IsGaussHypergeometricFamily.differentiableOn_params_unitDisk hH hz
  have hvalue : DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ => H q.1 q.2.1 q.2.2 z) p :=
    (hvalueOn p hp).differentiableAt (gaussParameterPoleFreeDomain_isOpen.mem_nhds hp)
  have hderiv := IsGaussHypergeometricFamily.differentiableAt_params_deriv_unitDisk
    hH hp hz
  exact hvalue.prodMk hderiv

private theorem exists_compact_norm_bound
    {X Y : Type*} [TopologicalSpace X] [NormedAddCommGroup Y]
    {K : Set X} (hK : IsCompact K) (f : X → Y) (hf : ContinuousOn f K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, ‖f x‖ ≤ B := by
  have hnorm : ContinuousOn (fun x => ‖f x‖) K := hf.norm
  obtain ⟨B, hB⟩ := bddAbove_def.mp (hK.bddAbove_image hnorm)
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro x hx
  have hle := hB (‖f x‖) ⟨x, hx, rfl⟩
  exact hle.trans (le_max_left _ _)

private theorem gaussParameterFactor_contDiffOn :
    ContDiffOn ℂ ⊤ (fun p : ℂ × ℂ × ℂ => p.1 * p.2.1 / p.2.2)
      gaussParameterPoleFreeDomain := by
  intro p hp
  have hpC : p.2.2 ≠ 0 := by
    intro h
    exact hp 0 (by simpa using h)
  fun_prop (disch := assumption)

/-- The parameter derivative of the spatial derivative of a characterized Gauss family is
locally uniformly bounded on the unit disk. The shifted-series identity reduces this to the
ordinary value and parameter-derivative bounds. -/
theorem exists_local_uniform_gaussSpatialDerivative_fderiv_bound
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (p : ℂ × ℂ × ℂ)
    (hp : p ∈ gaussParameterPoleFreeDomain) (z : ℂ) (hz : ‖z‖ < 1) :
    ∃ r B : ℝ, 0 < r ∧ 0 ≤ B ∧
      ∀ q ∈ Metric.ball p r,
        ‖fderiv ℂ (fun v : ℂ × ℂ × ℂ =>
          deriv (fun w => H v.1 v.2.1 v.2.2 w) z) q‖ ≤ B := by
  let shift : ℂ × ℂ × ℂ → ℂ × ℂ × ℂ := fun q => q + ((1 : ℂ), 1, 1)
  let factor : ℂ × ℂ × ℂ → ℂ := fun q => q.1 * q.2.1 / q.2.2
  let seriesValue : ℂ × ℂ × ℂ → ℂ := fun q =>
    ordinaryHypergeometric (shift q).1 (shift q).2.1 (shift q).2.2 z
  let spatialDerivative : ℂ × ℂ × ℂ → ℂ := fun q =>
    deriv (fun w => H q.1 q.2.1 q.2.2 w) z
  have hpShift : shift p ∈ gaussParameterPoleFreeDomain := by
    exact gaussParameterPoleFreeDomain_shift_add_one hp
  obtain ⟨rV, MV, hrV, hMV, hVbound⟩ :=
    exists_local_uniform_ordinaryHypergeometric_fderiv_bound p z hp hz
  obtain ⟨rS, MS, hrS, hMS, hSbound⟩ :=
    exists_local_uniform_ordinaryHypergeometric_fderiv_bound (shift p) z hpShift hz
  let U : Set (ℂ × ℂ × ℂ) :=
    gaussParameterPoleFreeDomain ∩
      ((shift ⁻¹' Metric.ball (shift p) rS) ∩ Metric.ball p rV)
  have hUopen : IsOpen U := by
    apply gaussParameterPoleFreeDomain_isOpen.inter
    exact (Metric.isOpen_ball.preimage (by fun_prop)).inter Metric.isOpen_ball
  have hpU : p ∈ U := by
    refine ⟨hp, ?_, Metric.mem_ball_self hrV⟩
    exact Metric.mem_ball_self hrS
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen p hpU
  let r : ℝ := ε / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hrε : r < ε := by dsimp [r]; linarith
  let K : Set (ℂ × ℂ × ℂ) := Metric.closedBall p r
  have hKcompact : IsCompact K := isCompact_closedBall p r
  have hKsub : K ⊆ U := by
    intro q hq
    exact hball (Metric.closedBall_subset_ball hrε hq)
  have hKdomain : K ⊆ gaussParameterPoleFreeDomain := by
    intro q hq
    exact (hKsub hq).1
  have hKshift : ∀ q ∈ K, shift q ∈ Metric.ball (shift p) rS := by
    intro q hq
    exact (hKsub hq).2.1
  have hKvalueBall : ∀ q ∈ K, q ∈ Metric.ball p rV := by
    intro q hq
    exact (hKsub hq).2.2
  have hfactorSmooth : ContDiffOn ℂ ⊤ factor gaussParameterPoleFreeDomain := by
    simpa [factor] using gaussParameterFactor_contDiffOn
  have hfactorCont : ContinuousOn factor K :=
    hfactorSmooth.continuousOn.mono hKdomain
  have hfactorFderivContDomain : ContinuousOn
      (fun q => fderiv ℂ factor q) gaussParameterPoleFreeDomain :=
    hfactorSmooth.continuousOn_fderiv_of_isOpen
      gaussParameterPoleFreeDomain_isOpen (by norm_num)
  have hfactorFderivCont : ContinuousOn (fun q => fderiv ℂ factor q) K :=
    hfactorFderivContDomain.mono hKdomain
  obtain ⟨CF, hCF, hfactorBound⟩ :=
    exists_compact_norm_bound hKcompact factor hfactorCont
  obtain ⟨DF, hDF, hfactorFderivBound⟩ :=
    exists_compact_norm_bound hKcompact (fun q => fderiv ℂ factor q) hfactorFderivCont
  have hseriesValueDiffOn : DifferentiableOn ℂ seriesValue K := by
    intro q hq
    have hqShift := gaussParameterPoleFreeDomain_shift_add_one (hKdomain hq)
    have hseries := ordinaryHypergeometric_differentiableAt_params (shift q) z hqShift hz
    have hshift : DifferentiableAt ℂ shift q := by
      dsimp [shift]
      fun_prop
    exact (hseries.comp q hshift).differentiableWithinAt
  have hseriesValueCont : ContinuousOn seriesValue K := hseriesValueDiffOn.continuousOn
  obtain ⟨CV, hCV, hseriesValueBound⟩ :=
    exists_compact_norm_bound hKcompact seriesValue hseriesValueCont
  have hseriesFderivBound : ∀ q ∈ K, ‖fderiv ℂ seriesValue q‖ ≤ MS := by
    intro q hq
    have hqShift := gaussParameterPoleFreeDomain_shift_add_one (hKdomain hq)
    have hseries := ordinaryHypergeometric_differentiableAt_params (shift q) z hqShift hz
    have hshift : HasFDerivAt shift (ContinuousLinearMap.id ℂ (ℂ × ℂ × ℂ)) q := by
      simpa [shift] using
        (hasFDerivAt_id (𝕜 := ℂ) q).add_const ((1 : ℂ), 1, 1)
    have hcomp := hseries.hasFDerivAt.comp q hshift
    have hshiftFderiv : fderiv ℂ shift q = ContinuousLinearMap.id ℂ (ℂ × ℂ × ℂ) :=
      hshift.fderiv
    have hcompFderiv : fderiv ℂ seriesValue q =
        (fderiv ℂ (fun v : ℂ × ℂ × ℂ =>
          ordinaryHypergeometric v.1 v.2.1 v.2.2 z) (shift q)).comp
          (ContinuousLinearMap.id ℂ (ℂ × ℂ × ℂ)) := by
      simpa [seriesValue, Function.comp_def, hshiftFderiv] using hcomp.fderiv
    rw [hcompFderiv]
    calc
      ‖(fderiv ℂ (fun v : ℂ × ℂ × ℂ =>
          ordinaryHypergeometric v.1 v.2.1 v.2.2 z) (shift q)).comp
          (ContinuousLinearMap.id ℂ (ℂ × ℂ × ℂ))‖ ≤
          ‖fderiv ℂ (fun v : ℂ × ℂ × ℂ =>
            ordinaryHypergeometric v.1 v.2.1 v.2.2 z) (shift q)‖ *
            ‖ContinuousLinearMap.id ℂ (ℂ × ℂ × ℂ)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ MS * 1 := by
        gcongr
        · exact hSbound (shift q) (hKshift q hq)
        · exact ContinuousLinearMap.norm_id_le
      _ = MS := mul_one _
  have hformula : ∀ q ∈ U, spatialDerivative q = factor q * seriesValue q := by
    intro q hq
    have hqPole : q ∈ gaussParameterPoleFreeDomain := hq.1
    have hqShift := gaussParameterPoleFreeDomain_shift_add_one hqPole
    have hderiv := IsGaussHypergeometricFamily.hasDerivAt_unitDisk hH
      q.1 q.2.1 q.2.2 z hqPole hz
    have hseries := (hH (shift q).1 (shift q).2.1 (shift q).2.2 hqShift).2 z hz
    have hseries' : H (q.1 + 1) (q.2.1 + 1) (q.2.2 + 1) z =
        ordinaryHypergeometric (q.1 + 1) (q.2.1 + 1) (q.2.2 + 1) z := by
      simpa [shift] using hseries
    have hresult : deriv (fun w => H q.1 q.2.1 q.2.2 w) z =
        factor q * seriesValue q := by
      rw [hderiv.deriv, hseries']
      rfl
    exact hresult
  have hB : 0 ≤ CV * DF + CF * MS := by positivity
  refine ⟨r, CV * DF + CF * MS, hr, hB, ?_⟩
  intro q hq
  have hqK : q ∈ K := Metric.ball_subset_closedBall hq
  have hqU : q ∈ U := hKsub hqK
  have hfactorAt : DifferentiableAt ℂ factor q := by
    exact (hfactorSmooth.contDiffAt
      (gaussParameterPoleFreeDomain_isOpen.mem_nhds hqU.1)).differentiableAt (by norm_num)
  have hqShift := gaussParameterPoleFreeDomain_shift_add_one (hKdomain hqK)
  have hseriesAt : DifferentiableAt ℂ seriesValue q := by
    have hseries := ordinaryHypergeometric_differentiableAt_params (shift q) z hqShift hz
    have hshift : DifferentiableAt ℂ shift q := by
      dsimp [shift]
      fun_prop
    exact hseries.comp q hshift
  have hproductAt : DifferentiableAt ℂ (fun v => factor v * seriesValue v) q :=
    hfactorAt.mul hseriesAt
  have hleftAt : DifferentiableAt ℂ spatialDerivative q :=
    IsGaussHypergeometricFamily.differentiableAt_params_deriv_unitDisk hH hqU.1 hz
  have hlocal : spatialDerivative =ᶠ[𝓝 q] fun v => factor v * seriesValue v := by
    filter_upwards [hUopen.mem_nhds hqU] with v hv
    exact hformula v hv
  have hleft : HasFDerivAt spatialDerivative (fderiv ℂ spatialDerivative q) q :=
    hleftAt.hasFDerivAt
  have hright : HasFDerivAt (fun v => factor v * seriesValue v)
      (fderiv ℂ spatialDerivative q) q := hlocal.hasFDerivAt_iff.mp hleft
  have hderivEq : fderiv ℂ spatialDerivative q =
      fderiv ℂ (fun v => factor v * seriesValue v) q :=
    hright.unique hproductAt.hasFDerivAt
  have hproduct := hfactorAt.hasFDerivAt.mul hseriesAt.hasFDerivAt
  calc
    ‖fderiv ℂ spatialDerivative q‖ =
        ‖fderiv ℂ (fun v => factor v * seriesValue v) q‖ := by rw [hderivEq]
    _ = ‖factor q • fderiv ℂ seriesValue q + seriesValue q • fderiv ℂ factor q‖ := by
      change ‖fderiv ℂ (factor * seriesValue) q‖ = _
      rw [hproduct.fderiv]
    _ ≤
        ‖factor q • fderiv ℂ seriesValue q‖ +
          ‖seriesValue q • fderiv ℂ factor q‖ := norm_add_le _ _
    _ = ‖factor q‖ * ‖fderiv ℂ seriesValue q‖ +
          ‖seriesValue q‖ * ‖fderiv ℂ factor q‖ := by simp [norm_smul]
    _ ≤ CF * MS + CV * DF := by
      gcongr
      · exact hfactorBound q hqK
      · exact hseriesFderivBound q hqK
      · exact hseriesValueBound q hqK
      · exact hfactorFderivBound q hqK
    _ = CV * DF + CF * MS := by ring

/-- The Fréchet derivative of the full state `(H,H')` is bounded uniformly on a parameter
neighborhood at every point of the ordinary-series disk. This provides the initial-state bound
needed by the parameterized Picard recursion. -/
theorem exists_local_uniform_gaussState_fderiv_bound
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (p : ℂ × ℂ × ℂ)
    (hp : p ∈ gaussParameterPoleFreeDomain) (z : ℂ) (hz : ‖z‖ < 1) :
    ∃ r B : ℝ, 0 < r ∧ 0 ≤ B ∧
      ∀ q ∈ Metric.ball p r,
        ‖fderiv ℂ (fun v : ℂ × ℂ × ℂ =>
          (H v.1 v.2.1 v.2.2 z, deriv (fun w => H v.1 v.2.1 v.2.2 w) z)) q‖ ≤ B := by
  let value : ℂ × ℂ × ℂ → ℂ := fun q => H q.1 q.2.1 q.2.2 z
  let spatialDerivative : ℂ × ℂ × ℂ → ℂ := fun q =>
    deriv (fun w => H q.1 q.2.1 q.2.2 w) z
  let state : ℂ × ℂ × ℂ → ℂ × ℂ := fun q => (value q, spatialDerivative q)
  obtain ⟨rV, MV, hrV, hMV, hVbound⟩ :=
    exists_local_uniform_ordinaryHypergeometric_fderiv_bound p z hp hz
  obtain ⟨rD, MD, hrD, hMD, hDbound⟩ :=
    exists_local_uniform_gaussSpatialDerivative_fderiv_bound hH p hp z hz
  let U : Set (ℂ × ℂ × ℂ) := gaussParameterPoleFreeDomain ∩ Metric.ball p rV
  have hUopen : IsOpen U :=
    gaussParameterPoleFreeDomain_isOpen.inter Metric.isOpen_ball
  have hpU : p ∈ U := ⟨hp, Metric.mem_ball_self hrV⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen p hpU
  let r₀ : ℝ := ε / 2
  have hr₀ : 0 < r₀ := by dsimp [r₀]; linarith
  have hr₀ε : r₀ < ε := by dsimp [r₀]; linarith
  let r : ℝ := min r₀ rD
  have hr : 0 < r := by dsimp [r]; exact lt_min hr₀ hrD
  have hB : 0 ≤ max MV MD := le_max_of_le_left hMV
  refine ⟨r, max MV MD, hr, hB, ?_⟩
  intro q hq
  have hrle₀ : r ≤ r₀ := by dsimp [r]; exact min_le_left _ _
  have hrleD : r ≤ rD := by dsimp [r]; exact min_le_right _ _
  have hqε : q ∈ Metric.ball p ε :=
    Metric.ball_subset_ball (le_of_lt (lt_of_le_of_lt hrle₀ hr₀ε)) hq
  have hqU : q ∈ U := hball hqε
  have hqDomain : q ∈ gaussParameterPoleFreeDomain := hqU.1
  have hqV : q ∈ Metric.ball p rV := hqU.2
  have hqD : q ∈ Metric.ball p rD := Metric.ball_subset_ball hrleD hq
  have hvalueAt : DifferentiableAt ℂ value q := by
    have hvalueOn := IsGaussHypergeometricFamily.differentiableOn_params_unitDisk hH hz
    exact (hvalueOn q hqDomain).differentiableAt
      (gaussParameterPoleFreeDomain_isOpen.mem_nhds hqDomain)
  have hseriesAt : DifferentiableAt ℂ
      (fun v : ℂ × ℂ × ℂ => ordinaryHypergeometric v.1 v.2.1 v.2.2 z) q :=
    ordinaryHypergeometric_differentiableAt_params q z hqDomain hz
  have hvalueNear : value =ᶠ[𝓝 q]
      (fun v : ℂ × ℂ × ℂ => ordinaryHypergeometric v.1 v.2.1 v.2.2 z) := by
    filter_upwards [gaussParameterPoleFreeDomain_isOpen.mem_nhds hqDomain] with v hv
    exact (hH v.1 v.2.1 v.2.2 hv).2 z hz
  have hvalueFderivEq : fderiv ℂ value q =
      fderiv ℂ (fun v : ℂ × ℂ × ℂ => ordinaryHypergeometric v.1 v.2.1 v.2.2 z) q := by
    have hlocal := hvalueNear.hasFDerivAt_iff.mp hvalueAt.hasFDerivAt
    exact hlocal.unique hseriesAt.hasFDerivAt
  have hstateAt : DifferentiableAt ℂ state q := by
    exact IsGaussHypergeometricFamily.differentiableAt_params_state_unitDisk hH hqDomain hz
  have hderivAt : DifferentiableAt ℂ spatialDerivative q :=
    IsGaussHypergeometricFamily.differentiableAt_params_deriv_unitDisk hH hqDomain hz
  have hstateFderiv : fderiv ℂ state q =
      (fderiv ℂ value q).prod (fderiv ℂ spatialDerivative q) := by
    have hpair := hvalueAt.hasFDerivAt.prodMk hderivAt.hasFDerivAt
    have hpair' := hpair.fderiv
    simpa [state, value, spatialDerivative] using hpair'
  rw [hstateFderiv, ContinuousLinearMap.opNorm_prod]
  simp only [Prod.norm_def]
  apply max_le_max
  · rw [hvalueFderivEq]
    exact hVbound q hqV
  · exact hDbound q hqD

/-- The Gauss state `(H,H')` is locally bounded in parameters at every admissible tuple on the
ordinary-series disk. -/
theorem exists_local_uniform_gaussState_norm_bound
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (p : ℂ × ℂ × ℂ)
    (hp : p ∈ gaussParameterPoleFreeDomain) (z : ℂ) (hz : ‖z‖ < 1) :
    ∃ r Y : ℝ, 0 < r ∧ 0 ≤ Y ∧
      ∀ q ∈ Metric.ball p r,
        ‖(H q.1 q.2.1 q.2.2 z, deriv (fun w => H q.1 q.2.1 q.2.2 w) z)‖ ≤ Y := by
  let state : ℂ × ℂ × ℂ → ℂ × ℂ := fun q =>
    (H q.1 q.2.1 q.2.2 z, deriv (fun w => H q.1 q.2.1 q.2.2 w) z)
  have hstate : DifferentiableAt ℂ state p :=
    IsGaussHypergeometricFamily.differentiableAt_params_state_unitDisk hH hp hz
  obtain ⟨r, hr, hnear⟩ :=
    (Metric.continuousAt_iff.mp hstate.continuousAt) 1 zero_lt_one
  let Y : ℝ := ‖state p‖ + 1
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  refine ⟨r, Y, hr, hY, ?_⟩
  intro q hq
  have hdist : dist (state q) (state p) < 1 := hnear (Metric.mem_ball.mp hq)
  have hnorm : ‖state q - state p‖ < 1 := by simpa [dist_eq_norm] using hdist
  have hbound : ‖state q‖ ≤ ‖state p‖ + 1 := by
    calc
      ‖state q‖ = ‖(state q - state p) + state p‖ := by congr 1; abel
      _ ≤ ‖state q - state p‖ + ‖state p‖ := norm_add_le _ _
      _ ≤ 1 + ‖state p‖ := by linarith
      _ = ‖state p‖ + 1 := by ring
  exact hbound

/-- The seed state and its parameter derivative have simultaneous local bounds, giving the two
initial-data constants used in differentiated Picard estimates. -/
theorem exists_local_uniform_gaussState_value_and_fderiv_bounds
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (p : ℂ × ℂ × ℂ)
    (hp : p ∈ gaussParameterPoleFreeDomain) (z : ℂ) (hz : ‖z‖ < 1) :
    ∃ r Y D : ℝ, 0 < r ∧ 0 ≤ Y ∧ 0 ≤ D ∧
      ∀ q ∈ Metric.ball p r,
        ‖(H q.1 q.2.1 q.2.2 z, deriv (fun w => H q.1 q.2.1 q.2.2 w) z)‖ ≤ Y ∧
        ‖fderiv ℂ (fun v : ℂ × ℂ × ℂ =>
          (H v.1 v.2.1 v.2.2 z, deriv (fun w => H v.1 v.2.1 v.2.2 w) z)) q‖ ≤ D := by
  obtain ⟨rY, Y, hrY, hY, hYbound⟩ :=
    exists_local_uniform_gaussState_norm_bound hH p hp z hz
  obtain ⟨rD, D, hrD, hD, hDbound⟩ :=
    exists_local_uniform_gaussState_fderiv_bound hH p hp z hz
  let r : ℝ := min rY rD
  have hr : 0 < r := by dsimp [r]; exact lt_min hrY hrD
  have hrY' : r ≤ rY := by dsimp [r]; exact min_le_left _ _
  have hrD' : r ≤ rD := by dsimp [r]; exact min_le_right _ _
  refine ⟨r, Y, D, hr, hY, hD, ?_⟩
  intro q hq
  have hqY : q ∈ Metric.ball p rY := Metric.ball_subset_ball hrY' hq
  have hqD : q ∈ Metric.ball p rD := Metric.ball_subset_ball hrD' hq
  exact ⟨hYbound q hqY, hDbound q hqD⟩

end DOZZ.Proofs
