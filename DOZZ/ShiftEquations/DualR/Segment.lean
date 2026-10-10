/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Gluing.BandLine
public import DOZZ.Statements.Defs.ExtendedSeiberg3
public import DOZZ.Statements.Defs.LFun
import DOZZ.ShiftEquations.Gluing.BandNear
import DOZZ.ShiftEquations.Shift.ShiftGluing
import DOZZ.ShiftEquations.Shift.Reflection
import DOZZ.ShiftEquations.Rbar.Continuation

/-!
# Continuation of identities along real segments

The dual shift of the reflection coefficient is obtained by continuing identities between products
of meromorphic factors (structure constants, reflection coefficients, `l`-functions) along real
segments of convex domains of charges. This file collects the general tools:

* `eq_at_one_of_segment`: two functions meromorphic on an open set containing the real segment
  `[0, 1]` which agree just to the right of `0` agree at `1`, where both are analytic;
* convexity of the extended Seiberg domain along segments;
* analyticity of `Γ`, `l` and `1/l` at real points off their poles, and of compositions;
* genericity: a meromorphic function is analytic at all real points near a given point, except
  possibly the point itself.
-/

@[expose] public section

open Filter Topology Set

namespace DOZZ.Proofs

/-! ### The segment identity theorem -/

/-- **Segment continuation.** Two functions meromorphic on a set containing the real
segment `[0, 1]`, which agree at the real points just to the right of `0`, agree at `1` when both
are analytic there. -/
theorem eq_at_one_of_segment {F G : ℂ → ℂ} {U : Set ℂ}
    (hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (t : ℂ) ∈ U)
    (hF : MeromorphicOn F U) (hG : MeromorphicOn G U)
    (hstart : ∀ᶠ t : ℝ in 𝓝[>] 0, F t = G t)
    (hF1 : AnalyticAt ℂ F 1) (hG1 : AnalyticAt ℂ G 1) : F 1 = G 1 := by
  have h0U : ((0 : ℝ) : ℂ) ∈ U := hseg 0 le_rfl zero_le_one
  have hWU : connectedComponentIn U ((0 : ℝ) : ℂ) ⊆ U := connectedComponentIn_subset U _
  have hsegW : (fun s : ℝ => (s : ℂ)) '' Icc 0 1 ⊆ connectedComponentIn U ((0 : ℝ) : ℂ) :=
    (isPreconnected_Icc.image _ Complex.continuous_ofReal.continuousOn).subset_connectedComponentIn
      ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩ (image_subset_iff.mpr fun s hs => hseg s hs.1 hs.2)
  have h1W : (1 : ℂ) ∈ connectedComponentIn U ((0 : ℝ) : ℂ) := by
    have h : ((1 : ℝ) : ℂ) ∈ connectedComponentIn U ((0 : ℝ) : ℂ) :=
      hsegW ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
    rwa [Complex.ofReal_one] at h
  have hfreq : ∃ᶠ z in 𝓝[≠] ((0 : ℝ) : ℂ), F z = G z := by
    have h1 : ∃ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), F t = G t :=
      hstart.frequently.filter_mono (nhdsWithin_mono _ fun x (hx : (0 : ℝ) < x) => hx.ne')
    exact (tendsto_ofReal_nhdsNE_slice 0).frequently h1
  have hev := ShiftGluing.meromorphicOn_eventuallyEq_of_frequently (hF.mono_set hWU) (hG.mono_set hWU)
    isPreconnected_connectedComponentIn (mem_connectedComponentIn h0U) h1W hfreq
  exact eq_of_eventuallyEq_nhdsNE_of_continuousAt hev hF1.continuousAt hG1.continuousAt

/-- Points of a real segment, as complex affine functions of the parameter. -/
noncomputable def segC (a b : ℝ) (t : ℂ) : ℂ := (a : ℂ) + t * ((b : ℂ) - a)

theorem segC_ofReal (a b t : ℝ) : segC a b (t : ℂ) = ((a + t * (b - a) : ℝ) : ℂ) := by
  unfold segC
  push_cast
  ring

theorem segC_one (a b : ℝ) : segC a b 1 = (b : ℂ) := by
  unfold segC
  ring

theorem differentiable_segC (a b : ℝ) : Differentiable ℂ (segC a b) := by
  unfold segC
  fun_prop

theorem analyticAt_segC (a b : ℝ) (t : ℂ) : AnalyticAt ℂ (segC a b) t :=
  (differentiable_segC a b).analyticAt t

/-- Real points of a segment near its start. -/
theorem eventually_segC_mem {a b : ℝ} {N : Set ℝ} (hN : IsOpen N) (ha : a ∈ N) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, a + t * (b - a) ∈ N := by
  have hc : Continuous fun t : ℝ => a + t * (b - a) := by fun_prop
  have h := hc.continuousAt (x := 0) |>.preimage_mem_nhds (by simpa using hN.mem_nhds ha)
  exact nhdsWithin_le_nhds h

/-! ### Convexity of the extended Seiberg domain -/

theorem add_mul_sub_lt_of_lt {x y c t : ℝ} (hx : x < c) (hy : y < c) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : x + t * (y - x) < c := by
  have h1 : (1 - t) * x ≤ (1 - t) * c := mul_le_mul_of_nonneg_left hx.le (by linarith)
  have hrw : x + t * (y - x) = (1 - t) * x + t * y := by ring
  rcases eq_or_lt_of_le ht0 with h | h
  · rw [← h] at hrw ⊢
    linarith
  · have h2 : t * y < t * c := mul_lt_mul_of_pos_left hy h
    linarith

/-- The linear conditions behind the extended Seiberg bounds. -/
theorem extendedSeiberg3_linear {γ α₁ α₂ α₃ : ℝ} (hγ : 0 < γ)
    (h : ExtendedSeiberg3 γ α₁ α₂ α₃) :
    α₁ < Q γ ∧ α₂ < Q γ ∧ α₃ < Q γ ∧ 2 * Q γ - (α₁ + α₂ + α₃) < 4 / γ ∧
      2 * Q γ - (α₁ + α₂ + α₃) < 2 * (Q γ - α₁) ∧
      2 * Q γ - (α₁ + α₂ + α₃) < 2 * (Q γ - α₂) ∧
      2 * Q γ - (α₁ + α₂ + α₃) < 2 * (Q γ - α₃) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  have hs : -sExp γ α₁ α₂ α₃ = (2 * Q γ - (α₁ + α₂ + α₃)) / γ := by
    unfold sExp
    ring
  rw [hs, lt_min_iff, lt_min_iff, lt_min_iff] at h₄
  obtain ⟨k₀, k₁, k₂, k₃⟩ := h₄
  refine ⟨h₁, h₂, h₃, ?_, ?_, ?_, ?_⟩
  · rw [div_lt_iff₀ hγ] at k₀
    rwa [show 4 / γ ^ 2 * γ = 4 / γ by field_simp] at k₀
  · rw [div_lt_iff₀ hγ] at k₁
    rwa [show 2 / γ * (Q γ - α₁) * γ = 2 * (Q γ - α₁) by field_simp] at k₁
  · rw [div_lt_iff₀ hγ] at k₂
    rwa [show 2 / γ * (Q γ - α₂) * γ = 2 * (Q γ - α₂) by field_simp] at k₂
  · rw [div_lt_iff₀ hγ] at k₃
    rwa [show 2 / γ * (Q γ - α₃) * γ = 2 * (Q γ - α₃) by field_simp] at k₃

/-- **The extended Seiberg domain is convex.** -/
theorem extendedSeiberg3_segment {γ a₁ a₂ a₃ b₁ b₂ b₃ t : ℝ} (hγ : 0 < γ)
    (ha : ExtendedSeiberg3 γ a₁ a₂ a₃) (hb : ExtendedSeiberg3 γ b₁ b₂ b₃) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    ExtendedSeiberg3 γ (a₁ + t * (b₁ - a₁)) (a₂ + t * (b₂ - a₂)) (a₃ + t * (b₃ - a₃)) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := extendedSeiberg3_linear hγ ha
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := extendedSeiberg3_linear hγ hb
  refine extendedSeiberg3_of_lt hγ (add_mul_sub_lt_of_lt a1 b1 ht0 ht1)
    (add_mul_sub_lt_of_lt a2 b2 ht0 ht1) (add_mul_sub_lt_of_lt a3 b3 ht0 ht1) ?_ ?_ ?_ ?_
  · have h := add_mul_sub_lt_of_lt (sub_neg.mpr a4) (sub_neg.mpr b4) ht0 ht1
    have e : 2 * Q γ - (a₁ + t * (b₁ - a₁) + (a₂ + t * (b₂ - a₂)) + (a₃ + t * (b₃ - a₃))) -
        4 / γ = 2 * Q γ - (a₁ + a₂ + a₃) - 4 / γ + t * (2 * Q γ - (b₁ + b₂ + b₃) - 4 / γ -
          (2 * Q γ - (a₁ + a₂ + a₃) - 4 / γ)) := by ring
    linarith
  · have h := add_mul_sub_lt_of_lt (sub_neg.mpr a5) (sub_neg.mpr b5) ht0 ht1
    have e : 2 * Q γ - (a₁ + t * (b₁ - a₁) + (a₂ + t * (b₂ - a₂)) + (a₃ + t * (b₃ - a₃))) -
        2 * (Q γ - (a₁ + t * (b₁ - a₁))) = 2 * Q γ - (a₁ + a₂ + a₃) - 2 * (Q γ - a₁) +
          t * (2 * Q γ - (b₁ + b₂ + b₃) - 2 * (Q γ - b₁) -
            (2 * Q γ - (a₁ + a₂ + a₃) - 2 * (Q γ - a₁))) := by ring
    linarith
  · have h := add_mul_sub_lt_of_lt (sub_neg.mpr a6) (sub_neg.mpr b6) ht0 ht1
    have e : 2 * Q γ - (a₁ + t * (b₁ - a₁) + (a₂ + t * (b₂ - a₂)) + (a₃ + t * (b₃ - a₃))) -
        2 * (Q γ - (a₂ + t * (b₂ - a₂))) = 2 * Q γ - (a₁ + a₂ + a₃) - 2 * (Q γ - a₂) +
          t * (2 * Q γ - (b₁ + b₂ + b₃) - 2 * (Q γ - b₂) -
            (2 * Q γ - (a₁ + a₂ + a₃) - 2 * (Q γ - a₂))) := by ring
    linarith
  · have h := add_mul_sub_lt_of_lt (sub_neg.mpr a7) (sub_neg.mpr b7) ht0 ht1
    have e : 2 * Q γ - (a₁ + t * (b₁ - a₁) + (a₂ + t * (b₂ - a₂)) + (a₃ + t * (b₃ - a₃))) -
        2 * (Q γ - (a₃ + t * (b₃ - a₃))) = 2 * Q γ - (a₁ + a₂ + a₃) - 2 * (Q γ - a₃) +
          t * (2 * Q γ - (b₁ + b₂ + b₃) - 2 * (Q γ - b₃) -
            (2 * Q γ - (a₁ + a₂ + a₃) - 2 * (Q γ - a₃))) := by ring
    linarith

/-! ### Analyticity of `Γ`, `l` and `1/l` -/

/-- `Γ` is analytic off the non-positive integers. -/
theorem analyticAt_Gamma_of_ne {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(n : ℂ)) :
    AnalyticAt ℂ Complex.Gamma s := by
  have h1 : AnalyticAt ℂ (fun u => (Complex.Gamma u)⁻¹) s :=
    Complex.differentiable_one_div_Gamma.analyticAt _
  have h2 := h1.inv (inv_ne_zero (Complex.Gamma_ne_zero hs))
  have hfun : (fun u => (Complex.Gamma u)⁻¹)⁻¹ = Complex.Gamma := by
    funext u
    simp
  rwa [hfun] at h2

/-- `Γ` is analytic at positive reals. -/
theorem analyticAt_Gamma_ofReal_pos {r : ℝ} (hr : 0 < r) : AnalyticAt ℂ Complex.Gamma (r : ℂ) := by
  refine analyticAt_Gamma_of_ne fun n hn => ?_
  have h : r = -(n : ℝ) := by exact_mod_cast hn
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- `Γ` is analytic on `(-1, 0)`. -/
theorem analyticAt_Gamma_ofReal_neg_one_lt {r : ℝ} (h1 : -1 < r) (h2 : r < 0) :
    AnalyticAt ℂ Complex.Gamma (r : ℂ) := by
  refine analyticAt_Gamma_of_ne fun n hn => ?_
  have h : r = -(n : ℝ) := by exact_mod_cast hn
  rcases Nat.lt_or_ge n 1 with hn1 | hn1
  · interval_cases n
    simp only [Nat.cast_zero, neg_zero] at h
    linarith
  · have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith

/-- `l ∘ f` is analytic where `f` is and `Γ` is analytic at the value. -/
theorem analyticAt_lFun_comp {f : ℂ → ℂ} {t : ℂ} (hf : AnalyticAt ℂ f t)
    (hΓ : AnalyticAt ℂ Complex.Gamma (f t)) : AnalyticAt ℂ (fun s => lFun (f s)) t := by
  have h1 : AnalyticAt ℂ (fun s => Complex.Gamma (f s)) t :=
    AnalyticAt.comp_of_eq (g := Complex.Gamma) (f := f) hΓ hf rfl
  have h2 : AnalyticAt ℂ (fun s => (Complex.Gamma (1 - f s))⁻¹) t :=
    AnalyticAt.comp_of_eq (g := fun u => (Complex.Gamma u)⁻¹) (f := fun s => 1 - f s)
      (Complex.differentiable_one_div_Gamma.analyticAt _) (analyticAt_const.sub hf) rfl
  have hfun : (fun s => lFun (f s)) = fun s => Complex.Gamma (f s) * (Complex.Gamma (1 - f s))⁻¹ := by
    funext s
    unfold lFun
    rw [div_eq_mul_inv]
  rw [hfun]
  exact h1.mul h2

/-- `1/(l ∘ f)` is analytic where `f` is and `Γ` is analytic at `1 - f`. -/
theorem analyticAt_inv_lFun_comp {f : ℂ → ℂ} {t : ℂ} (hf : AnalyticAt ℂ f t)
    (hΓ : AnalyticAt ℂ Complex.Gamma (1 - f t)) :
    AnalyticAt ℂ (fun s => (lFun (f s))⁻¹) t := by
  have h1 : AnalyticAt ℂ (fun s => Complex.Gamma (1 - f s)) t :=
    AnalyticAt.comp_of_eq (g := Complex.Gamma) (f := fun s => 1 - f s) hΓ
      (analyticAt_const.sub hf) rfl
  have h2 : AnalyticAt ℂ (fun s => (Complex.Gamma (f s))⁻¹) t :=
    AnalyticAt.comp_of_eq (g := fun u => (Complex.Gamma u)⁻¹) (f := f)
      (Complex.differentiable_one_div_Gamma.analyticAt _) hf rfl
  have hfun : (fun s => (lFun (f s))⁻¹) =
      fun s => Complex.Gamma (1 - f s) * (Complex.Gamma (f s))⁻¹ := by
    funext s
    unfold lFun
    rw [inv_div, div_eq_mul_inv]
  rw [hfun]
  exact h1.mul h2

/-- `l ∘ f` is meromorphic where `f` is analytic. -/
theorem meromorphicAt_lFun_comp' {f : ℂ → ℂ} {t : ℂ} (hf : AnalyticAt ℂ f t) :
    MeromorphicAt (fun s => lFun (f s)) t := by
  have h1 : MeromorphicAt (fun s => Complex.Gamma (f s)) t :=
    (Meromorphic.Gamma _).comp_analyticAt (g := f) hf
  have h2 : MeromorphicAt (fun s => Complex.Gamma (1 - f s)) t :=
    (Meromorphic.Gamma _).comp_analyticAt (g := fun s => 1 - f s) (analyticAt_const.sub hf)
  unfold lFun
  exact h1.fun_div h2

/-! ### The continued structure constant along lines, with the `Γ` condition in analytic form -/

/-- **The continued structure constant is analytic** along analytic charge curves at points
where `Γ` is analytic at `s`. -/
theorem analyticAt_structureConstantH_comp' {f : (Fin 3 → ℂ) → ℂ} {V : Set (Fin 3 → ℂ)}
    (hV : IsOpen V) (hf : DifferentiableOn ℂ f V) {γ μ : ℝ} (hμ : 0 < μ)
    {ℓ : ℂ → Fin 3 → ℂ} (hℓ : Differentiable ℂ ℓ) {t : ℂ} (ht : ℓ t ∈ V)
    (hs : AnalyticAt ℂ Complex.Gamma (sExpC γ (ℓ t))) :
    AnalyticAt ℂ (fun t => structureConstantH f γ μ (ℓ t)) t := by
  have hUo : IsOpen (ℓ ⁻¹' V) := hV.preimage hℓ.continuous
  have hfℓ : DifferentiableOn ℂ (fun t => f (ℓ t)) (ℓ ⁻¹' V) :=
    hf.comp hℓ.differentiableOn fun _ hx => hx
  have hfa : AnalyticAt ℂ (fun t => f (ℓ t)) t := hfℓ.analyticAt (hUo.mem_nhds ht)
  have hsa : AnalyticAt ℂ (fun t => sExpC γ (ℓ t)) t := by
    unfold sExpC
    have h0 : AnalyticAt ℂ (fun t => ℓ t 0) t :=
      ((differentiable_pi.mp hℓ) 0).analyticAt t
    have h1 : AnalyticAt ℂ (fun t => ℓ t 1) t :=
      ((differentiable_pi.mp hℓ) 1).analyticAt t
    have h2 : AnalyticAt ℂ (fun t => ℓ t 2) t :=
      ((differentiable_pi.mp hℓ) 2).analyticAt t
    exact (((h0.add h1).add h2).sub analyticAt_const).div_const
  have hμs : (μ : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr hμ
  have hpow : AnalyticAt ℂ (fun t => (μ : ℂ) ^ (-sExpC γ (ℓ t))) t :=
    analyticAt_const.cpow hsa.neg hμs
  have hΓ : AnalyticAt ℂ (fun t => Complex.Gamma (sExpC γ (ℓ t))) t :=
    AnalyticAt.comp_of_eq hs hsa rfl
  exact (hpow.mul hΓ).mul hfa

/-! ### Genericity -/

/-- **Genericity along a real direction.** A function meromorphic at `z₀` is analytic at
`z₀ + u a` for all real `u ≠ 0` near `0`, when `a ≠ 0`. -/
theorem eventually_analyticAt_affine {φ : ℂ → ℂ} {z₀ a : ℂ} (hφ : MeromorphicAt φ z₀)
    (ha : a ≠ 0) : ∀ᶠ u : ℝ in 𝓝[≠] 0, AnalyticAt ℂ φ (z₀ + u * a) := by
  have ht : Tendsto (fun u : ℝ => z₀ + (u : ℂ) * a) (𝓝[≠] 0) (𝓝[≠] z₀) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous fun u : ℝ => z₀ + (u : ℂ) * a := by fun_prop
      have h0 := hc.tendsto 0
      simp only [Complex.ofReal_zero, zero_mul, add_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · refine eventually_nhdsWithin_of_forall fun u hu => ?_
      simp only [mem_compl_iff, mem_singleton_iff, add_eq_left, mul_eq_zero,
        Complex.ofReal_eq_zero, not_or]
      exact ⟨hu, ha⟩
  exact ht.eventually hφ.eventually_analyticAt

/-! ### Openness along curves -/

/-- An analyticity condition at a continuous function of a real parameter persists nearby. -/
theorem eventually_analyticAt_comp {g : ℂ → ℂ} {φ : ℝ → ℂ} {t₀ : ℝ} (hφ : ContinuousAt φ t₀)
    (h : AnalyticAt ℂ g (φ t₀)) : ∀ᶠ t in 𝓝 t₀, AnalyticAt ℂ g (φ t) :=
  hφ.preimage_mem_nhds h.eventually_analyticAt

/-- The extended Seiberg bounds persist along continuous curves. -/
theorem eventually_extendedSeiberg3 {γ : ℝ} {f₁ f₂ f₃ : ℝ → ℝ} {t₀ : ℝ}
    (h₁ : ContinuousAt f₁ t₀) (h₂ : ContinuousAt f₂ t₀) (h₃ : ContinuousAt f₃ t₀)
    (h : ExtendedSeiberg3 γ (f₁ t₀) (f₂ t₀) (f₃ t₀)) :
    ∀ᶠ t in 𝓝 t₀, ExtendedSeiberg3 γ (f₁ t) (f₂ t) (f₃ t) := by
  obtain ⟨k₁, k₂, k₃, k₄⟩ := h
  have hs : ContinuousAt (fun t => -sExp γ (f₁ t) (f₂ t) (f₃ t)) t₀ := by
    unfold sExp
    exact ((((h₁.add h₂).add h₃).sub continuousAt_const).div_const _).neg
  have hm : ContinuousAt (fun t => min (4 / γ ^ 2) (min (2 / γ * (Q γ - f₁ t))
      (min (2 / γ * (Q γ - f₂ t)) (2 / γ * (Q γ - f₃ t))))) t₀ :=
    continuousAt_const.min ((continuousAt_const.mul (continuousAt_const.sub h₁)).min
      ((continuousAt_const.mul (continuousAt_const.sub h₂)).min
        (continuousAt_const.mul (continuousAt_const.sub h₃))))
  filter_upwards [h₁.eventually_lt continuousAt_const k₁, h₂.eventually_lt continuousAt_const k₂,
    h₃.eventually_lt continuousAt_const k₃, hs.eventually_lt hm k₄] with t a₁ a₂ a₃ a₄
  exact ⟨a₁, a₂, a₃, a₄⟩

/-- Real affine parametrizations leave a point along the punctured filter. -/
theorem tendsto_affine_nhdsNE {z₀ a : ℂ} (ha : a ≠ 0) :
    Tendsto (fun u : ℝ => z₀ + u * a) (𝓝[≠] 0) (𝓝[≠] z₀) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have hc : Continuous fun u : ℝ => z₀ + (u : ℂ) * a := by fun_prop
    have h0 := hc.tendsto 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  · refine eventually_nhdsWithin_of_forall fun u hu => ?_
    simp only [mem_compl_iff, mem_singleton_iff, add_eq_left, mul_eq_zero,
      Complex.ofReal_eq_zero, not_or]
    exact ⟨hu, ha⟩

/-- A punctured-germ property at a real point pulls back along `u ↦ x₀ + s u`, `s ≠ 0`. -/
theorem eventually_ofReal_affine {p : ℂ → Prop} {x₀ s : ℝ} (hs : s ≠ 0)
    (h : ∀ᶠ z in 𝓝[≠] ((x₀ : ℝ) : ℂ), p z) : ∀ᶠ u : ℝ in 𝓝[≠] 0, p ((x₀ + u * s : ℝ) : ℂ) := by
  have ht := tendsto_affine_nhdsNE (z₀ := (x₀ : ℂ)) (a := (s : ℂ)) (Complex.ofReal_ne_zero.mpr hs)
  filter_upwards [ht.eventually h] with u hu
  have e : ((x₀ + u * s : ℝ) : ℂ) = (x₀ : ℂ) + (u : ℂ) * (s : ℂ) := by push_cast; ring
  rw [e]
  exact hu

end DOZZ.Proofs

end
