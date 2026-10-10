/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ParameterPicardGaussSeed
public import DOZZ.Hypergeom.ODE.ParameterPicardPath
public import DOZZ.Hypergeom.ODE.UniformParameterPicardPath
public import DOZZ.Hypergeom.ODE.CutPlaneCanonicalPath
public import DOZZ.Hypergeom.ODE.NegativeCutPlaneContinuation

/-! Parameter differentiability of a characterized Gauss family propagated along compact path
tubes by parameterized Picard chains. -/

@[expose] public section

open Set unitInterval

namespace DOZZ.Proofs

/-- A parameterized Gauss state is differentiable at the endpoint of any regular slit-plane path
that starts in the ordinary-series disk. -/
theorem IsGaussHypergeometricFamily.differentiableAt_params_of_path
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (p : GaussParam)
    (hp : p ∈ gaussParameterPoleFreeDomain) (c z : ℂ) (hc : ‖c‖ < 1)
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hstart : γ 0 = c) (hend : γ 1 = z)
    (hpath : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ gaussRegularPlane)
    (hpathSlit : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ gaussSlitPlane) :
    DifferentiableAt ℂ (fun q : GaussParam => H q.1 q.2.1 q.2.2 z) p := by
  obtain ⟨rSeed, Y₀, D₀, hrSeed, hY₀, hD₀, hseed⟩ :=
    exists_local_uniform_gaussState_value_and_fderiv_bounds hH p hp c hc
  obtain ⟨ε, hε, hdomain⟩ :=
    Metric.isOpen_iff.mp gaussParameterPoleFreeDomain_isOpen p hp
  let ρ : ℝ := min (rSeed / 2) (ε / 2)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (by positivity) (by positivity)
  let s : Set GaussParam := Metric.ball p ρ
  let K : Set GaussParam := Metric.closedBall p ρ
  have hs : IsOpen s := Metric.isOpen_ball
  have hsconn : IsPreconnected s := (convex_ball p ρ).isPreconnected
  have hpS : p ∈ s := Metric.mem_ball_self hρ
  have hKcompact : IsCompact K := isCompact_closedBall p ρ
  have hsK : s ⊆ K := Metric.ball_subset_closedBall
  have hKdomain : K ⊆ gaussParameterPoleFreeDomain := by
    intro q hq
    apply hdomain
    apply Metric.mem_ball.mpr
    have hdist := Metric.mem_closedBall.mp hq
    have hρε : ρ < ε := by
      dsimp [ρ]
      exact (min_le_right _ _).trans_lt (by linarith)
    exact hdist.trans_lt hρε
  have hseedRadius : ρ < rSeed := by
    dsimp [ρ]
    exact (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨rTube, M₀, L₀, hrTube, hM₀, hL₀, htube⟩ :=
    exists_uniform_gaussSystem_parameterized_disks_on_path
      hKcompact hγ hpath hpathSlit
  let M : ℝ := max M₀ 1
  let L : ℝ := max L₀ 1
  let Y : ℝ := max Y₀ 1
  let D : ℝ := max D₀ 1
  let B : ℝ := M * D + L * Y
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hMpositive : 0 < M := by dsimp [M]; positivity
  have hLpositive : 0 < L := by dsimp [L]; positivity
  have hYpositive : 0 < Y := by dsimp [Y]; positivity
  have hDpositive : 0 < D := by dsimp [D]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let r : ℝ := min (rTube / 2)
    (min (1 / (2 * (M + 1))) (D / (2 * (B + 1))))
  have hr : 0 < r := by
    dsimp [r]
    refine lt_min (by positivity) (lt_min ?_ ?_)
    · positivity
    · positivity
  have hrTubeLe : r ≤ rTube := by
    dsimp [r]
    exact (min_le_left _ _).trans (by linarith)
  have hrM : M * r ≤ (1 / 2 : ℝ) := by
    have hrsmall : r ≤ 1 / (2 * (M + 1)) := by
      dsimp [r]
      exact (min_le_right _ _).trans (min_le_left _ _)
    have hfrac : M * (1 / (2 * (M + 1))) ≤ (1 / 2 : ℝ) := by
      rw [show M * (1 / (2 * (M + 1))) = M / (2 * (M + 1)) by ring]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (M + 1))).2
      nlinarith
    exact (mul_le_mul_of_nonneg_left hrsmall hM).trans hfrac
  have hcontract : r * (M * D + L * Y) ≤ D * (1 / 2 : ℝ) := by
    have hrsmall : r ≤ D / (2 * (B + 1)) := by
      dsimp [r]
      exact (min_le_right _ _).trans (min_le_right _ _)
    have hmul := mul_le_mul_of_nonneg_right hrsmall (by positivity : 0 ≤ B + 1)
    have hcalc : (D / (2 * (B + 1))) * (B + 1) = D * (1 / 2 : ℝ) := by
      field_simp
    calc
      r * (M * D + L * Y) = r * B := by simp [B]
      _ ≤ r * (B + 1) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hr)
        linarith
      _ ≤ (D / (2 * (B + 1))) * (B + 1) := hmul
      _ = D * (1 / 2 : ℝ) := hcalc

  let A : GaussParam → ℂ → (ℂ × ℂ →L[ℂ] (ℂ × ℂ)) := fun q w =>
    gaussSystemOperator q.1 q.2.1 q.2.2 w
  let DA : GaussParam → ℂ → GaussParam →L[ℂ]
      ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) := gaussParamOperatorFDeriv
  let y₀ : GaussParam → ℂ × ℂ := fun q => gaussFamilyStateAt H c q
  let Dy₀ : GaussParam → GaussParam →L[ℂ] (ℂ × ℂ) :=
    fun q => gaussFamilyStateFDerivAt H c q
  let F : GaussParam → ℂ → ℂ × ℂ := fun q w =>
    (H q.1 q.2.1 q.2.2 w, deriv (fun u => H q.1 q.2.1 q.2.2 u) w)
  have hA : ∀ t ∈ Icc (0 : ℝ) 1, ∀ q,
      DifferentiableOn ℂ (A q) (Metric.ball (γ t) r) := by
    intro t ht q
    rcases htube t ht with ⟨hgeometry, hdiff, hDcontinuous, hAbound, hDAbound, hAderiv⟩
    have hregular : Metric.ball (γ t) r ⊆ gaussRegularPlane := by
      intro w hw
      exact (hgeometry w (Metric.ball_subset_ball hrTubeLe hw)).1
    exact (gaussSystemOperator_differentiableOn q.1 q.2.1 q.2.2).mono
      (by simpa [A] using hregular)
  have hDA : ∀ t ∈ Icc (0 : ℝ) 1, ∀ q,
      ContinuousOn (DA q) (Metric.ball (γ t) r) := by
    intro t ht q
    rcases htube t ht with ⟨hgeometry, hdiff, hDcontinuous, hAbound, hDAbound, hAderiv⟩
    have hregular : Metric.ball (γ t) r ⊆ gaussRegularPlane := by
      intro w hw
      exact (hgeometry w (Metric.ball_subset_ball hrTubeLe hw)).1
    exact (gaussSystemOperator_param_fderiv_continuousOn q).mono
      (by simpa [DA] using hregular)
  have hAderiv : ∀ t ∈ Icc (0 : ℝ) 1, ∀ q ∈ s, ∀ w ∈ Metric.ball (γ t) r,
      HasFDerivAt (fun q' => A q' w) (DA q w) q := by
    intro t ht q hq w hw
    rcases htube t ht with ⟨hgeometry, hdiff, hDcontinuous, hAbound, hDAbound, hAderiv⟩
    have hqK : q ∈ K := hsK hq
    have hwTube : w ∈ Metric.ball (γ t) rTube := Metric.mem_ball.mpr
      ((Metric.mem_ball.mp hw).trans_le hrTubeLe)
    simpa [A, DA] using hAderiv q hqK w hwTube
  have hAbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ q ∈ s, ∀ w ∈ Metric.ball (γ t) r,
      ‖A q w‖ ≤ M := by
    intro t ht q hq w hw
    rcases htube t ht with ⟨hgeometry, hdiff, hDcontinuous, hAbound, hDAbound, hAderiv⟩
    have hqK : q ∈ K := hsK hq
    have hwTube : w ∈ Metric.ball (γ t) rTube := Metric.mem_ball.mpr
      ((Metric.mem_ball.mp hw).trans_le hrTubeLe)
    exact (hAbound q hqK w hwTube).trans (le_max_left _ _)
  have hDAbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ q ∈ s, ∀ w ∈ Metric.ball (γ t) r,
      ‖DA q w‖ ≤ L := by
    intro t ht q hq w hw
    rcases htube t ht with ⟨hgeometry, hdiff, hDcontinuous, hAbound, hDAbound, hAderiv⟩
    have hqK : q ∈ K := hsK hq
    have hwTube : w ∈ Metric.ball (γ t) rTube := Metric.mem_ball.mpr
      ((Metric.mem_ball.mp hw).trans_le hrTubeLe)
    exact (hDAbound q hqK w hwTube).trans (le_max_left _ _)
  have hyderiv : ∀ q ∈ s, HasFDerivAt y₀ (Dy₀ q) q := by
    intro q hq
    have hqDomain : q ∈ gaussParameterPoleFreeDomain := hKdomain (hsK hq)
    have hdiff := IsGaussHypergeometricFamily.differentiableAt_params_state_unitDisk
      hH hqDomain hc
    change HasFDerivAt
      (fun q' => (H q'.1 q'.2.1 q'.2.2 c,
        deriv (fun w => H q'.1 q'.2.1 q'.2.2 w) c))
      (fderiv ℂ (fun q' => (H q'.1 q'.2.1 q'.2.2 c,
        deriv (fun w => H q'.1 q'.2.1 q'.2.2 w) c)) q) q
    exact hdiff.hasFDerivAt
  have hybound : ∀ q ∈ s, ‖y₀ q‖ ≤ Y := by
    intro q hq
    change q ∈ Metric.ball p ρ at hq
    have hqSeed : q ∈ Metric.ball p rSeed := by
      apply Metric.mem_ball.mpr
      exact lt_trans (Metric.mem_ball.mp hq) hseedRadius
    calc
      ‖y₀ q‖ = ‖(H q.1 q.2.1 q.2.2 c,
          deriv (fun w => H q.1 q.2.1 q.2.2 w) c)‖ := by rfl
      _ ≤ Y₀ := (hseed q hqSeed).1
      _ ≤ Y := by dsimp [Y]; exact le_max_left Y₀ 1
  have hDybound : ∀ q ∈ s, ‖Dy₀ q‖ ≤ D := by
    intro q hq
    change q ∈ Metric.ball p ρ at hq
    have hqSeed : q ∈ Metric.ball p rSeed := by
      apply Metric.mem_ball.mpr
      exact lt_trans (Metric.mem_ball.mp hq) hseedRadius
    calc
      ‖Dy₀ q‖ = ‖fderiv ℂ (fun v : GaussParam =>
          (H v.1 v.2.1 v.2.2 c,
            deriv (fun w => H v.1 v.2.1 v.2.2 w) c)) q‖ := by rfl
      _ ≤ D₀ := (hseed q hqSeed).2
      _ ≤ D := by dsimp [D]; exact le_max_left D₀ 1
  obtain ⟨N, hN, hclose, hchain⟩ :=
    exists_parameterizedPicardPathSeed_hasFDerivAt
      hγ s hs hsconn r hr A hA DA hDA M L Y D hM hL hY hD hrM hcontract
      hAderiv hAbound hDAbound y₀ Dy₀ hyderiv hybound hDybound p hpS
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  let centers : ℕ → ℂ := fun i => γ ((i : ℝ) / (N : ℝ))
  have htime : ∀ i : ℕ, i ≤ N → (i : ℝ) / (N : ℝ) ∈ Icc (0 : ℝ) 1 := by
    intro i hi
    constructor
    · positivity
    · apply (div_le_one hNreal).2
      exact_mod_cast hi
  have hcentersclose : ∀ i < N, centers (i + 1) ∈ Metric.ball (centers i) r := by
    intro i hi
    simpa [centers] using hclose i hi
  have hAcenters : ∀ i ≤ N, ∀ q,
      DifferentiableOn ℂ (A q) (Metric.ball (centers i) r) := by
    intro i hi q
    simpa [centers] using hA _ (htime i hi) q
  have hAboundsCenters : ∀ i ≤ N, ∀ q ∈ s, ∀ w ∈ Metric.ball (centers i) r,
      ‖A q w‖ ≤ M := by
    intro i hi q hq w hw
    exact hAbound _ (htime i hi) q hq w (by simpa [centers] using hw)
  have hFderiv : ∀ i ≤ N, ∀ q ∈ s, ∀ w ∈ Metric.ball (centers i) r,
      HasDerivAt (F q) (A q w (F q w)) w := by
    intro i hi q hq w hw
    have ht := htime i hi
    rcases htube _ ht with ⟨hgeometry, hdiff, hDcontinuous, hAbound, hDAbound, hAderiv⟩
    have hwTube : w ∈ Metric.ball (γ ((i : ℝ) / (N : ℝ))) rTube := by
      apply Metric.mem_ball.mpr
      exact (Metric.mem_ball.mp (by simpa [centers] using hw)).trans_le hrTubeLe
    have hwhere := hgeometry w hwTube
    have hqDomain : q ∈ gaussParameterPoleFreeDomain := hKdomain (hsK hq)
    simpa [F, A] using IsGaussHypergeometricFamily.state_hasDerivAt_gaussSystem hH
      q.1 q.2.1 q.2.2 hqDomain (z := w) hwhere.2 hwhere.1
  have hstartPath : ∀ q ∈ s, y₀ q = F q (centers 0) := by
    intro q hq
    rw [show centers 0 = c by simp [centers, hstart]]
    rfl
  have hidentified := parameterizedPicardPathSeed_eq_solution
    centers N r M hr hM s A hAcenters hAboundsCenters y₀ F hFderiv hstartPath
    hcentersclose
  have hendCenter : centers N = z := by
    dsimp [centers]
    rw [div_self hNreal.ne', hend]
  have hseedDeriv := (hchain p hpS).1
  have hseedDeriv' : HasFDerivAt
      (parameterizedPicardPathSeed centers A y₀ N)
      (parameterizedPicardPathSeedFDeriv centers A DA y₀ Dy₀ N p) p := by
    simpa [centers] using hseedDeriv
  have hseedEq : ∀ q ∈ s,
      parameterizedPicardPathSeed centers A y₀ N q = F q z := by
    intro q hq
    rw [hidentified q hq, hendCenter]
  have hstateDeriv : HasFDerivAt (fun q => F q z)
      (parameterizedPicardPathSeedFDeriv centers A DA y₀ Dy₀ N p) p := by
    apply hseedDeriv'.congr_of_eventuallyEq
    filter_upwards [hs.mem_nhds hpS] with q hq
    exact (hseedEq q hq).symm
  have hvalueDeriv := hstateDeriv.differentiableAt.fst
  simpa [F] using hvalueDeriv

private theorem gaussCutPlane_subset_slitPlane :
    gaussCutPlane ⊆ gaussSlitPlane := by
  intro z hz
  change z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) at hz
  change z.im ≠ 0 ∨ z.re < 1
  rcases hz with him | ⟨_, hlt⟩
  · exact Or.inl him
  · exact Or.inr hlt

private theorem gaussNegativeCutPlane_subset_slitPlane :
    gaussNegativeCutPlane ⊆ gaussSlitPlane := by
  intro z hz
  change z.im ≠ 0 ∨ z.re < 0 at hz
  change z.im ≠ 0 ∨ z.re < 1
  rcases hz with him | hlt
  · exact Or.inl him
  · exact Or.inr (hlt.trans (by norm_num : (0 : ℝ) < 1))

/-- Joint parameter holomorphy of the characterized continuation away from denominator poles; this
is the proof of `DOZZ.IsGaussHypergeometricFamily.differentiableOn_params`. -/
theorem IsGaussHypergeometricFamily.differentiableOn_params
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) {z : ℂ} (hz : z ∈ gaussSlitPlane) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => H p.1 p.2.1 p.2.2 z)
      {p | ∀ n : ℕ, p.2.2 ≠ -(n : ℂ)} := by
  intro p hp
  have hpDomain : p ∈ gaussParameterPoleFreeDomain := hp
  by_cases hzzero : z = 0
  · subst z
    have hunit : ‖(0 : ℂ)‖ < 1 := by norm_num
    have hdiff := IsGaussHypergeometricFamily.differentiableOn_params_unitDisk
      hH hunit p hpDomain
    exact hdiff
  by_cases hzcut : z ∈ gaussCutPlane
  · let z' : gaussCutPlane := ⟨z, hzcut⟩
    let γ : ℝ → ℂ := gaussCutPlanePathFunction
      (gaussCutPlaneCanonicalPath z')
    have hproj0 : Set.projIcc 0 1 zero_le_one 0 = (0 : unitInterval) :=
      Set.projIcc_of_mem zero_le_one (by norm_num)
    have hproj1 : Set.projIcc 0 1 zero_le_one 1 = (1 : unitInterval) :=
      Set.projIcc_of_mem zero_le_one (by norm_num)
    have hstart : γ 0 = (1 / 2 : ℂ) := by
      change (gaussCutPlaneCanonicalPath z'
        (Set.projIcc 0 1 zero_le_one 0) : ℂ) = _
      rw [hproj0]
      exact congrArg Subtype.val (gaussCutPlaneCanonicalPath z').source
    have hend : γ 1 = z := by
      change (gaussCutPlaneCanonicalPath z'
        (Set.projIcc 0 1 zero_le_one 1) : ℂ) = z
      rw [hproj1]
      exact congrArg Subtype.val (gaussCutPlaneCanonicalPath z').target
    have hregular : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ gaussRegularPlane := by
      intro t ht
      exact gaussCutPlane_subset_regularPlane
        (gaussCutPlaneCanonicalPath_mem z' t)
    have hslit : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ gaussSlitPlane := by
      intro t ht
      exact gaussCutPlane_subset_slitPlane
        (gaussCutPlaneCanonicalPath_mem z' t)
    have hdiff := IsGaussHypergeometricFamily.differentiableAt_params_of_path
      hH p hpDomain (1 / 2 : ℂ) z (by norm_num)
      (gaussCutPlaneCanonicalPath_continuousOn z') hstart hend hregular hslit
    exact hdiff.differentiableWithinAt
  · have hnegative : z ∈ gaussNegativeCutPlane := by
      change z.im ≠ 0 ∨ z.re < 0
      rcases hz with him | hre
      · exact Or.inl him
      · have him0 : z.im = 0 := by
          by_contra him
          exact hzcut (Or.inl him)
        by_cases hreNeg : z.re < 0
        · exact Or.inr hreNeg
        · have hreNonneg : 0 ≤ z.re := le_of_not_gt hreNeg
          have hreNe : z.re ≠ 0 := by
            intro hre0
            apply hzzero
            exact Complex.ext hre0 him0
          have hrePos : 0 < z.re := lt_of_le_of_ne hreNonneg (Ne.symm hreNe)
          exact False.elim (hzcut (Or.inr ⟨hrePos, hre⟩))
    let z' : gaussNegativeCutPlane := ⟨z, hnegative⟩
    let γ : ℝ → ℂ := subtypePathFunction
      (gaussNegativeCutPlaneCanonicalPath z')
    have hproj0 : Set.projIcc 0 1 zero_le_one 0 = (0 : unitInterval) :=
      Set.projIcc_of_mem zero_le_one (by norm_num)
    have hproj1 : Set.projIcc 0 1 zero_le_one 1 = (1 : unitInterval) :=
      Set.projIcc_of_mem zero_le_one (by norm_num)
    have hstart : γ 0 = (-1 / 2 : ℂ) := by
      change (gaussNegativeCutPlaneCanonicalPath z'
        (Set.projIcc 0 1 zero_le_one 0) : ℂ) = _
      rw [hproj0]
      exact congrArg Subtype.val (gaussNegativeCutPlaneCanonicalPath z').source
    have hend : γ 1 = z := by
      change (gaussNegativeCutPlaneCanonicalPath z'
        (Set.projIcc 0 1 zero_le_one 1) : ℂ) = z
      rw [hproj1]
      exact congrArg Subtype.val (gaussNegativeCutPlaneCanonicalPath z').target
    have hregular : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ gaussRegularPlane := by
      intro t ht
      exact gaussNegativeCutPlane_subset_regularPlane
        (gaussNegativeCutPlaneCanonicalPath_mem z' t)
    have hslit : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ gaussSlitPlane := by
      intro t ht
      exact gaussNegativeCutPlane_subset_slitPlane
        (gaussNegativeCutPlaneCanonicalPath_mem z' t)
    have hdiff := IsGaussHypergeometricFamily.differentiableAt_params_of_path
      hH p hpDomain (-1 / 2 : ℂ) z (by norm_num)
      (gaussNegativeCutPlaneCanonicalPath_continuousOn z') hstart hend hregular hslit
    exact hdiff.differentiableWithinAt

end DOZZ.Proofs
