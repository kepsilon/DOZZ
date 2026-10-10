/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ParameterCoefficients

/-! Joint compact bounds for the Gauss system over parameter and spatial compacta. -/

@[expose] public section

namespace DOZZ.Proofs

/-- The Gauss system operator has one norm bound on the product of a compact parameter set and
a compact spatial set avoiding the regular singular points. This is the uniform coefficient
bound needed when the Picard disk chain is varied over a parameter neighborhood. -/
theorem exists_joint_uniform_gaussSystemOperator_norm_bound
    {K : Set (ℂ × ℂ × ℂ)} {Z : Set ℂ}
    (hK : IsCompact K) (hZ : IsCompact Z) (hZreg : Z ⊆ gaussRegularPlane) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ K, ∀ z ∈ Z,
      ‖gaussSystemOperator p.1 p.2.1 p.2.2 z‖ ≤ M := by
  let S : Set ((ℂ × ℂ × ℂ) × ℂ) := K ×ˢ Z
  let U : Set ((ℂ × ℂ × ℂ) × ℂ) := {q | q.2 ∈ gaussRegularPlane}
  have hScompact : IsCompact S := hK.prod hZ
  have hSsub : S ⊆ U := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    exact hZreg hz
  have hden : ContinuousOn (fun q : (ℂ × ℂ × ℂ) × ℂ => q.2 * (1 - q.2))
      U := by
    fun_prop
  have hinv : ContinuousOn
      (fun q : (ℂ × ℂ × ℂ) × ℂ => (q.2 * (1 - q.2))⁻¹)
      U := hden.inv₀ (by
        rintro ⟨p, z⟩ hz
        exact mul_ne_zero hz.1 (sub_ne_zero.mpr (Ne.symm hz.2)))
  have hcoeff₁ : ContinuousOn
      (fun q : (ℂ × ℂ × ℂ) × ℂ => gaussSystemCoeff₁ q.1.1 q.1.2.1 q.2)
      U := by
    change ContinuousOn
      (fun q : (ℂ × ℂ × ℂ) × ℂ => (q.2 * (1 - q.2))⁻¹ * (q.1.1 * q.1.2.1))
      U
    exact hinv.mul (by fun_prop)
  have hcoeff₂ : ContinuousOn
      (fun q : (ℂ × ℂ × ℂ) × ℂ => gaussSystemCoeff₂ q.1.1 q.1.2.1 q.1.2.2 q.2)
      U := by
    change ContinuousOn
      (fun q : (ℂ × ℂ × ℂ) × ℂ => (q.2 * (1 - q.2))⁻¹ *
        ((q.1.1 + q.1.2.1 + 1) * q.2 - q.1.2.2))
      U
    exact hinv.mul (by fun_prop)
  let firstOutput : ℂ →L[ℂ] ℂ × ℂ :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (1, 0)
  let secondOutput : ℂ →L[ℂ] ℂ × ℂ :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (0, 1)
  let firstComponent : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
    firstOutput.comp (ContinuousLinearMap.snd ℂ ℂ ℂ)
  let secondFromFirst : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
    secondOutput.comp (ContinuousLinearMap.fst ℂ ℂ ℂ)
  let secondFromSecond : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
    secondOutput.comp (ContinuousLinearMap.snd ℂ ℂ ℂ)
  have hfirst : ContinuousOn (fun _ : (ℂ × ℂ × ℂ) × ℂ => firstComponent) S :=
    continuousOn_const
  have hsecondFirst : ContinuousOn
      (fun _ : (ℂ × ℂ × ℂ) × ℂ => secondFromFirst) S := continuousOn_const
  have hsecondSecond : ContinuousOn
      (fun _ : (ℂ × ℂ × ℂ) × ℂ => secondFromSecond) S := continuousOn_const
  have hrow₁ : ContinuousOn
      (fun q : (ℂ × ℂ × ℂ) × ℂ =>
        gaussSystemCoeff₁ q.1.1 q.1.2.1 q.2 • secondFromFirst) S := by
    exact (hcoeff₁.mono hSsub).smul hsecondFirst
  have hrow₂ : ContinuousOn
      (fun q : (ℂ × ℂ × ℂ) × ℂ =>
        gaussSystemCoeff₂ q.1.1 q.1.2.1 q.1.2.2 q.2 • secondFromSecond) S := by
    exact (hcoeff₂.mono hSsub).smul hsecondSecond
  let A : (ℂ × ℂ × ℂ) × ℂ → ℂ × ℂ →L[ℂ] ℂ × ℂ :=
    fun q => gaussSystemOperator q.1.1 q.1.2.1 q.1.2.2 q.2
  have hA : ContinuousOn A S := by
    change ContinuousOn
      (fun q : (ℂ × ℂ × ℂ) × ℂ => firstComponent +
        (gaussSystemCoeff₁ q.1.1 q.1.2.1 q.2 • secondFromFirst +
          gaussSystemCoeff₂ q.1.1 q.1.2.1 q.1.2.2 q.2 • secondFromSecond)) S
    exact hfirst.add (hrow₁.add hrow₂)
  have hnorm : ContinuousOn (fun q => ‖A q‖) S := hA.norm
  obtain ⟨B, hB⟩ := bddAbove_def.mp (hScompact.bddAbove_image hnorm)
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro p hp z hz
  have hle := hB ‖A (p, z)‖ ⟨(p, z), ⟨hp, hz⟩, rfl⟩
  exact le_trans hle (le_max_left _ _)

/-- Joint parameter and spatial domain of the regular first-order Gauss system. -/
def gaussSystemJointParameterDomain : Set ((ℂ × ℂ × ℂ) × ℂ) :=
  {q | q.2 ∈ gaussRegularPlane}

private theorem gaussSystemJointParameterDomain_isOpen :
    IsOpen gaussSystemJointParameterDomain :=
  gaussRegularPlane_isOpen.preimage continuous_snd

/-- The coefficient operator is smooth jointly in its parameters and regular spatial variable. -/
theorem gaussSystemOperator_joint_contDiffOn :
    ContDiffOn ℂ ⊤
      (fun q : (ℂ × ℂ × ℂ) × ℂ =>
        gaussSystemOperator q.1.1 q.1.2.1 q.1.2.2 q.2)
      gaussSystemJointParameterDomain := by
  intro q hq
  have hden : q.2 * (1 - q.2) ≠ 0 :=
    mul_ne_zero hq.1 (sub_ne_zero.mpr (Ne.symm hq.2))
  fun_prop (disch := assumption)
    [gaussSystemOperator, gaussSystemCoeff₁, gaussSystemCoeff₂]

/-- The parameter derivative of a fixed-spatial slice is the joint derivative restricted to
parameter directions. -/
theorem gaussSystemOperator_param_fderiv_eq_joint_comp
    (p : ℂ × ℂ × ℂ) {z : ℂ} (hz : z ∈ gaussRegularPlane) :
    fderiv ℂ (fun q : ℂ × ℂ × ℂ =>
        gaussSystemOperator q.1 q.2.1 q.2.2 z) p =
      (fderiv ℂ
        (fun q : (ℂ × ℂ × ℂ) × ℂ =>
          gaussSystemOperator q.1.1 q.1.2.1 q.1.2.2 q.2) (p, z)).comp
        (ContinuousLinearMap.inl ℂ (ℂ × ℂ × ℂ) ℂ) := by
  let F : (ℂ × ℂ × ℂ) × ℂ → ℂ × ℂ →L[ℂ] ℂ × ℂ :=
    fun q => gaussSystemOperator q.1.1 q.1.2.1 q.1.2.2 q.2
  have hpz : (p, z) ∈ gaussSystemJointParameterDomain := hz
  have hF : ContDiffOn ℂ ⊤ F gaussSystemJointParameterDomain := by
    exact gaussSystemOperator_joint_contDiffOn
  have hFAt : DifferentiableAt ℂ F (p, z) := by
    have hcF : ContDiffAt ℂ ⊤ F (p, z) :=
      hF.contDiffAt (gaussSystemJointParameterDomain_isOpen.mem_nhds hpz)
    exact hcF.differentiableAt (by simp)
  have hmap : HasFDerivAt (fun q : ℂ × ℂ × ℂ => (q, z))
      (ContinuousLinearMap.inl ℂ (ℂ × ℂ × ℂ) ℂ) p := by
    fun_prop
  have hcomp := (hFAt.hasFDerivAt.comp p hmap).fderiv
  change fderiv ℂ (fun q : ℂ × ℂ × ℂ => F (q, z)) p = _ at hcomp
  simpa [F] using hcomp

/-- The parameter derivative of the Gauss-system coefficient operator, at fixed spatial point. -/
noncomputable def gaussParamOperatorFDeriv (p : ℂ × ℂ × ℂ) (z : ℂ) :
    (ℂ × ℂ × ℂ) →L[ℂ] ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) :=
  fderiv ℂ (fun q : ℂ × ℂ × ℂ =>
    gaussSystemOperator q.1 q.2.1 q.2.2 z) p

/-- The parameter derivative of the Gauss-system operator varies continuously with the spatial
point on the regular plane. -/
theorem gaussSystemOperator_param_fderiv_continuousOn (p : ℂ × ℂ × ℂ) :
    ContinuousOn (gaussParamOperatorFDeriv p) gaussRegularPlane := by
  let J : (ℂ × ℂ × ℂ) × ℂ →
      (ℂ × ℂ →L[ℂ] (ℂ × ℂ)) := fun q =>
    gaussSystemOperator q.1.1 q.1.2.1 q.1.2.2 q.2
  let U : Set ((ℂ × ℂ × ℂ) × ℂ) := gaussSystemJointParameterDomain
  have hUopen : IsOpen U := gaussRegularPlane_isOpen.preimage continuous_snd
  have hJderiv : ContinuousOn (fun q => fderiv ℂ J q) U :=
    gaussSystemOperator_joint_contDiffOn.continuousOn_fderiv_of_isOpen
      hUopen (by norm_num)
  let sectionMap : ℂ → (ℂ × ℂ × ℂ) × ℂ := fun z => (p, z)
  have hsection : ContinuousOn sectionMap gaussRegularPlane :=
    continuousOn_const.prodMk continuousOn_id
  have hmap : Set.MapsTo sectionMap gaussRegularPlane U := by
    intro z hz
    exact hz
  have hsectionDeriv := hJderiv.comp hsection hmap
  let I : (ℂ × ℂ × ℂ) →L[ℂ] ((ℂ × ℂ × ℂ) × ℂ) :=
    ContinuousLinearMap.inl ℂ (ℂ × ℂ × ℂ) ℂ
  have hcompose : ContinuousOn
      (fun z => (fderiv ℂ J (p, z)).comp I) gaussRegularPlane := by
    simpa [sectionMap] using hsectionDeriv.clm_comp continuousOn_const
  have heq : ∀ z ∈ gaussRegularPlane,
      gaussParamOperatorFDeriv p z = (fderiv ℂ J (p, z)).comp I := by
    intro z hz
    exact gaussSystemOperator_param_fderiv_eq_joint_comp p hz
  exact hcompose.congr (by
    intro z hz
    exact heq z hz)

/-- At every regular spatial point, the fixed-point parameter derivative displayed above is the
Fréchet derivative of the Gauss-system operator with respect to `(a,b,c)`. -/
theorem gaussSystemOperator_param_hasFDerivAt
    (p : ℂ × ℂ × ℂ) (z : ℂ) :
    HasFDerivAt
      (fun q : ℂ × ℂ × ℂ => gaussSystemOperator q.1 q.2.1 q.2.2 z)
      (gaussParamOperatorFDeriv p z) p := by
  have hAt : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ =>
      gaussSystemOperator q.1 q.2.1 q.2.2 z) p := by
    fun_prop (disch := assumption)
      [gaussSystemOperator, gaussSystemCoeff₁, gaussSystemCoeff₂]
  exact hAt.hasFDerivAt

/-- On a compact set of regular parameter and spatial pairs, the full joint derivative of the
Gauss-system coefficient operator has one uniform norm bound. In particular this controls its
parameter derivative along every compact continuation path. -/
theorem exists_joint_uniform_gaussSystemOperator_fderiv_norm_bound
    {K : Set (ℂ × ℂ × ℂ)} {Z : Set ℂ}
    (hK : IsCompact K) (hZ : IsCompact Z) (hZreg : Z ⊆ gaussRegularPlane) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ K, ∀ z ∈ Z,
      ‖fderiv ℂ
        (fun q : (ℂ × ℂ × ℂ) × ℂ =>
          gaussSystemOperator q.1.1 q.1.2.1 q.1.2.2 q.2) (p, z)‖ ≤ M := by
  let X : Set ((ℂ × ℂ × ℂ) × ℂ) := K ×ˢ Z
  let U : Set ((ℂ × ℂ × ℂ) × ℂ) := gaussSystemJointParameterDomain
  let A : (ℂ × ℂ × ℂ) × ℂ → ℂ × ℂ →L[ℂ] ℂ × ℂ :=
    fun q => gaussSystemOperator q.1.1 q.1.2.1 q.1.2.2 q.2
  have hXcompact : IsCompact X := hK.prod hZ
  have hXsub : X ⊆ U := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    exact hZreg hz
  have hA : ContDiffOn ℂ ⊤ A U := gaussSystemOperator_joint_contDiffOn
  have hderiv : ContinuousOn (fun q => fderiv ℂ A q) U :=
    hA.continuousOn_fderiv_of_isOpen gaussSystemJointParameterDomain_isOpen (by norm_num)
  let S : Set ((ℂ × ℂ × ℂ) × ℂ →L[ℂ] (ℂ × ℂ →L[ℂ] ℂ × ℂ)) :=
    (fun q => fderiv ℂ A q) '' X
  have hScompact : IsCompact S := hXcompact.image_of_continuousOn (hderiv.mono hXsub)
  obtain ⟨B, hB⟩ := hScompact.isBounded.subset_closedBall
    (0 : (ℂ × ℂ × ℂ) × ℂ →L[ℂ] (ℂ × ℂ →L[ℂ] ℂ × ℂ))
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro p hp z hz
  have hmem : fderiv ℂ A (p, z) ∈ S := ⟨(p, z), ⟨hp, hz⟩, rfl⟩
  have hball : fderiv ℂ A (p, z) ∈ Metric.closedBall
      (0 : (ℂ × ℂ × ℂ) × ℂ →L[ℂ] (ℂ × ℂ →L[ℂ] ℂ × ℂ)) B := hB hmem
  have hdist : dist (fderiv ℂ A (p, z))
      (0 : (ℂ × ℂ × ℂ) × ℂ →L[ℂ] (ℂ × ℂ →L[ℂ] ℂ × ℂ)) ≤ B := by
    simpa only [Metric.mem_closedBall] using hball
  have hnorm : ‖fderiv ℂ A (p, z)‖ ≤ B := by
    calc
      ‖fderiv ℂ A (p, z)‖ = dist (fderiv ℂ A (p, z))
          (0 : (ℂ × ℂ × ℂ) × ℂ →L[ℂ] (ℂ × ℂ →L[ℂ] ℂ × ℂ)) :=
        (dist_zero_right (fderiv ℂ A (p, z))).symm
      _ ≤ B := hdist
  exact hnorm.trans (le_max_left _ _)

/-- The parameter derivative of the fixed-spatial Gauss operator is uniformly bounded on compact
regular parameter/spatial pairs. -/
theorem exists_joint_uniform_gaussSystemOperator_param_fderiv_norm_bound
    {K : Set (ℂ × ℂ × ℂ)} {Z : Set ℂ}
    (hK : IsCompact K) (hZ : IsCompact Z) (hZreg : Z ⊆ gaussRegularPlane) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ K, ∀ z ∈ Z,
      ‖fderiv ℂ (fun q : ℂ × ℂ × ℂ =>
        gaussSystemOperator q.1 q.2.1 q.2.2 z) p‖ ≤ M := by
  obtain ⟨M, hM, hbound⟩ :=
    exists_joint_uniform_gaussSystemOperator_fderiv_norm_bound hK hZ hZreg
  refine ⟨M, hM, ?_⟩
  intro p hp z hz
  have hjoint := hbound p hp z hz
  rw [gaussSystemOperator_param_fderiv_eq_joint_comp p (hZreg hz)]
  let J := fderiv ℂ
    (fun q : (ℂ × ℂ × ℂ) × ℂ =>
      gaussSystemOperator q.1.1 q.1.2.1 q.1.2.2 q.2) (p, z)
  let I := ContinuousLinearMap.inl ℂ (ℂ × ℂ × ℂ) ℂ
  calc
    ‖J.comp I‖ ≤ ‖J‖ * ‖I‖ := ContinuousLinearMap.opNorm_comp_le J I
    _ ≤ M * ‖I‖ := mul_le_mul_of_nonneg_right hjoint (norm_nonneg _)
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.norm_inl_le_one ℂ (ℂ × ℂ × ℂ) ℂ) hM
    _ = M := mul_one _

end DOZZ.Proofs
