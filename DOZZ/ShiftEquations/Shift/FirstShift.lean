/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Shift.FullShift
public import DOZZ.ShiftEquations.Shift.ShiftGluing
public import DOZZ.ShiftEquations.Rbar.Representation

/-!
# `DOZZ.reflectionR_first_shift_meromorphic` from its inputs

The holomorphic `R̄`-representation (`DOZZ.reflectionBarR_holomorphic_representation`) gives
`g = coefficient · C̄ₕ(z, γ, z)`, holomorphic near `(γ/2, Q)` with `g = R̄` there. The two-pole
residue identity gives `g(x - γ/2) = m(x) g(x)` for `x` close to `Q`, so `g` continues by the shift
equation to a meromorphic `G` on a horizontal strip ([KRV, §10.2]). Then `R = μ^p Γ(-p) p G` is
meromorphic, equals the probabilistic `R` on `(γ/2, Q)`, and satisfies the first shift near every
point of the strip; extending it by `0` off a thinner strip makes the shift hold along the
codiscrete filter of `ℂ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace DOZZ.Proofs

/-- `l` is nonzero on `(1, 2)`. -/
theorem lR_ne_zero_of_mem_one_two {v : ℝ} (h1 : 1 < v) (h2 : v < 2) : lR v ≠ 0 :=
  div_ne_zero (Real.Gamma_pos_of_pos (by linarith)).ne'
    (Real.Gamma_ne_zero (real_ne_neg_nat_of_frac (k := -1) (by push_cast; linarith)
      (by push_cast; linarith)))

/-- The shift multiplier is analytic and nonzero at a real point of `(γ, Q)`. -/
theorem rbarShiftMultiplier_analyticAt_ne_zero {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ z₀ : ℂ, AnalyticAt ℂ (rbarShiftMultiplier γ) z₀ ∧ rbarShiftMultiplier γ z₀ ≠ 0 := by
  obtain ⟨hQ, hQ2, hγh, h42, h2⟩ := slice_facts hγ hγ2
  set a₁ : ℝ := (γ + Q γ) / 2 with ha₁
  have hγQ : γ < Q γ := by rw [hQ]; linarith
  have ha₁1 : γ < a₁ := by rw [ha₁]; linarith
  have ha₁2 : a₁ < Q γ := by rw [ha₁]; linarith
  have hopen : IsOpen {z : ℂ | γ < z.re ∧ z.re < Q γ} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  refine ⟨a₁, (differentiableOn_rbarShiftMultiplier hγ hγ2).analyticAt
    (hopen.mem_nhds ⟨by rw [Complex.ofReal_re]; exact ha₁1, by rw [Complex.ofReal_re]; exact ha₁2⟩),
    ?_⟩
  rw [rbarShiftMultiplier_ofReal, Complex.ofReal_ne_zero]
  unfold rbarShiftMultiplierReal
  have hγQ' : γ * Q γ = 2 + γ ^ 2 / 2 := by rw [hQ]; field_simp
  have hu1 : γ * γ < γ * a₁ := mul_lt_mul_of_pos_left ha₁1 hγ
  have hu2 : γ * a₁ < γ * Q γ := mul_lt_mul_of_pos_left ha₁2 hγ
  have hγsq : γ ^ 2 < 4 := by nlinarith
  refine div_ne_zero (mul_ne_zero (div_ne_zero (mul_ne_zero two_ne_zero (by linarith))
    hγ.ne') Real.pi_ne_zero) (mul_ne_zero (mul_ne_zero ?_ ?_) ?_)
  · exact lR_ne_zero_of_mem_neg (by nlinarith) (by nlinarith)
  · exact lR_ne_zero_of_mem_unit (by nlinarith) (by nlinarith)
  · exact lR_ne_zero_of_mem_one_two (by nlinarith) (by nlinarith)

/-- Off one point, eventually in every punctured neighborhood. -/
theorem eventually_ne_nhdsNE_any (x c : ℂ) : ∀ᶠ w in 𝓝[≠] x, w ≠ c := by
  by_cases hxc : x = c
  · subst hxc
    exact self_mem_nhdsWithin
  · exact nhdsWithin_le_nhds (eventually_ne_nhds hxc)

/-- **`DOZZ.reflectionR_first_shift_meromorphic` from its inputs.** The hypotheses are, at the given
field and chaos, the unit-volume conjunct of `gammaHalf_crossing`, the conclusions of
`unitVolumeStructureConstant_threeToTwo_residue_bridge`, of `twoInsertion_tail_sum_uniform` (through
the two-pole expansion) and of `unitVolumeStructureConstant_holomorphic_near_extended_domain`. -/
theorem reflectionR_first_shift_meromorphic_of_deps
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hCross : ∀ μ α' ε α : ℝ, 0 < μ → γ / 2 < ε → ε < 2 / γ → α < Q γ → α' < Q γ →
      2 * Q γ < α + α' + ε - γ / 2 →
      unitVolumeStructureConstant P M γ (α' - γ / 2) ε α =
        gammaHalfUnitCrossingMultiplier γ μ α' ε α *
          unitVolumeStructureConstant P M γ α' (ε + γ / 2) α)
    (hBridge : ∀ α2 α3 : ℝ, 0 < α2 ∧ α2 ≤ α3 ∧ γ / 2 < α3 ∧ α3 < Q γ →
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧ IsReflectionData P γ α3 (B α3) Z ∧
        Tendsto (fun ε : ℝ => ε * unitVolumeStructureConstant P M γ
            (α3 - α2 + ε) α2 α3) (𝓝[>] 0)
          (𝓝 (bridgeMultiplicity α2 α3 * reflectionExponent γ α3 *
            reflectionBarR P γ α3 (B α3) Z)))
    (hTail : ∀ (K2 K3 : Set ℂ) (_ : IsCompact K2) (_ : IsCompact K3)
      (_ : ∀ z ∈ K2, 2 ≤ ‖z‖) (_ : ∀ z ∈ K3, 2 ≤ ‖z‖)
      (_ : ∀ z2 ∈ K2, ∀ z3 ∈ K3, 3 ≤ ‖z2 - z3‖)
      (A2 A3 : Set ℝ) (_ : IsCompact A2) (_ : IsCompact A3)
      (_ : ∀ α ∈ A2, γ / 2 < α ∧ α < Q γ)
      (_ : ∀ α ∈ A3, γ / 2 < α ∧ α < Q γ)
      (F2s F3s : ℂ → Set (ℂ → ℝ)) (radius supBound derivBound lowerBound : ℝ)
      (_ : UniformPositiveC1Family K2 F2s radius supBound derivBound lowerBound)
      (_ : UniformPositiveC1Family K3 F3s radius supBound derivBound lowerBound),
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
                  C * Real.rpow x (-(twoInsertionTailCeiling γ α2 α3 - θ)))
    (hHolo : ∃ V : Set (Fin 3 → ℂ), IsOpen V ∧
      (∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) → complexifyNCharges α ∈ V) ∧
      ∃ f : (Fin 3 → ℂ) → ℂ, DifferentiableOn ℂ f V ∧
        ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) →
          f (complexifyNCharges α) =
            (unitVolumeStructureConstant P M γ (α 0) (α 1) (α 2) : ℂ)) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α : ℝ, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ R : ℂ → ℂ,
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) =
                  (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              ∀ᶠ z in codiscrete ℂ,
                R (z - γ / 2) =
                  -(μ * Real.pi : ℂ) * R z /
                    (lFun (-((γ : ℂ) ^ 2) / 4) *
                      lFun ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4) *
                      lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2)) := by
  obtain ⟨V₃, hV₃, hV₃mem, f₃, hf₃, hf₃eq⟩ := id hHolo
  obtain ⟨hQ, hQ2, hγh, h42, h2⟩ := slice_facts hγ hγ2
  -- the holomorphic `R̄`-representation on the whole reflection interval
  obtain ⟨B, Z, hSLP, hRD, V, hV, hVI, f, -, -, hcf, hcoef⟩ :=
    reflectionBarR_holomorphic_representation_of_deps P X M γ hγ hγ2 hX hM hCross hBridge hHolo
      (Ioo (γ / 2) (Q γ)) (fun α hα => hα)
  set g : ℂ → ℂ := fun z => rbarCoefficient γ z * f z with hg
  -- the unit-volume shift near `Q`
  obtain ⟨η₀, hη₀, hwin⟩ := exists_twoPoleWindow hγ hγ2
  set η₁ := min η₀ (2 / γ - γ / 2) with hη₁
  have hη₁pos : 0 < η₁ := lt_min hη₀ (by linarith)
  have hη₁le : η₁ ≤ 2 / γ - γ / 2 := min_le_right _ _
  have hrel : ∀ x : ℝ, Q γ - η₁ < x → x < Q γ →
      g ((x : ℂ) - ((γ / 2 : ℝ) : ℂ)) = rbarShiftMultiplier γ x * g x := by
    intro x hx1 hx2
    obtain ⟨δ, hW⟩ := hwin (Q γ - x) (by linarith)
      (by have := min_le_left η₀ (2 / γ - γ / 2); linarith)
    have hx3 : γ < x := by linarith
    have hshift := reflectionBarR_shift_of_window P X M hγ hγ2 hX hM hCross hBridge hTail hV₃
      hV₃mem hf₃ hf₃eq hW (B (x - γ / 2)) Z
      (by rw [sub_sub_cancel]; exact hRD _ ⟨by linarith, by linarith⟩) (B x) Z
      (by rw [sub_sub_cancel]; exact hRD _ ⟨by linarith, hx2⟩)
    rw [sub_sub_cancel] at hshift
    simp only [hg]
    rw [← Complex.ofReal_sub, hcoef (x - γ / 2) ⟨by linarith, by linarith⟩,
      hcoef x ⟨by linarith, hx2⟩, rbarShiftMultiplier_ofReal, hshift]
    push_cast
    ring
  -- continuation by the shift equation
  obtain ⟨h, hh, G, hGm, hGg, hGrel⟩ := exists_meromorphicOn_strip_of_shift (c := γ / 2)
    (a := γ / 2) (b := Q γ) (d₁ := Q γ - η₁) (d₂ := Q γ) (by positivity)
    (by rw [hQ]; linarith) (by linarith) (by linarith) le_rfl hV
    (fun x h1 h2 => hVI x ⟨h1, h2⟩) hcf (meromorphicOn_rbarShiftMultiplier γ)
    (rbarShiftMultiplier_analyticAt_ne_zero hγ hγ2) hrel
  -- the full coefficient, cut off outside a thinner strip
  set R : ℂ → ℂ := reflectionRFromBar γ μ G with hR
  set Rf : ℂ → ℂ := fun z => if |z.im| < h / 2 then R z else 0 with hRf
  have hRfin : ∀ z : ℂ, |z.im| < h / 2 → Rf z = R z := fun z hz => by simp [hRf, hz]
  have hRfout : ∀ z : ℂ, ¬ |z.im| < h / 2 → Rf z = 0 := fun z hz => by simp [hRf, hz]
  refine ⟨B, Z, hSLP, fun α h1 h2 => hRD α ⟨h1, h2⟩, h / 2, half_pos hh, Rf, ?_, ?_, ?_⟩
  · -- meromorphy on the thinner strip
    intro z hz
    have hz' : |z.im| < h / 2 := hz
    have hzh : z ∈ horizontalStrip h := by
      change |z.im| < h
      linarith
    refine (meromorphicOn_reflectionRFromBar (γ := γ) hμ hGm z hzh).congr ?_
    have hopen : IsOpen {w : ℂ | |w.im| < h / 2} := isOpen_horizontalStrip (h / 2)
    filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hz')] with w hw
    exact (hRfin w hw).symm
  · -- values on the reflection interval
    intro α h1 h2
    rw [hRfin α (by rw [Complex.ofReal_im, abs_zero]; positivity)]
    exact reflectionRFromBar_ofReal P hμ α (B α) Z
      ((hGg α h1 h2).trans (hcoef α ⟨h1, h2⟩))
  · -- the first shift along the codiscrete filter
    rw [eventually_codiscrete_iff_forall_eventually_nhdsNE]
    intro x
    have hzero : ∀ w : ℂ, ¬ |w.im| < h / 2 →
        Rf (w - γ / 2) = -(μ * Real.pi : ℂ) * Rf w /
          (lFun (-((γ : ℂ) ^ 2) / 4) * lFun ((γ : ℂ) * w / 2 - (γ : ℂ) ^ 2 / 4) *
            lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * w / 2)) := fun w hw => by
      have hw' : ¬ |(w - γ / 2).im| < h / 2 := by
        simpa [Complex.sub_im] using hw
      rw [hRfout w hw, hRfout _ hw']
      simp
    by_cases hx : |x.im| < h
    · filter_upwards [hGrel x hx, eventually_ne_nhdsNE_any x (Q γ + γ / 2)] with w hw1 hw2
      by_cases hw : |w.im| < h / 2
      · have hw' : |(w - γ / 2).im| < h / 2 := by simpa [Complex.sub_im] using hw
        rw [hRfin w hw, hRfin _ hw']
        refine reflectionRFromBar_shift hγ hμ hw1 ?_
        intro hp
        apply hw2
        unfold reflectionExponentC at hp
        have hγ0 : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ.ne'
        field_simp at hp
        linear_combination (-1 / 2 : ℂ) * hp
      · exact hzero w hw
    · have hopen : IsOpen {w : ℂ | h / 2 < |w.im|} :=
        isOpen_lt continuous_const Complex.continuous_im.abs
      have hxo : h / 2 < |x.im| := by
        have := not_lt.mp hx
        linarith
      filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hxo)] with w hw
      exact hzero w (by
        change h / 2 < |w.im| at hw
        linarith)

end DOZZ.Proofs

end
