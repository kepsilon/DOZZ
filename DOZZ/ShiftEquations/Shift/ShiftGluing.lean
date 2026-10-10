/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Complex.Basic
public import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Meromorphic continuation by a shift equation

A function `g`, holomorphic on an open set `W` containing a real interval `(a, b)` longer than a
step `c`, which satisfies the shift equation `g (x - c) = m x * g x` on a real subinterval,
continues to a meromorphic function on a horizontal strip that still satisfies the shift
equation near every point (`exists_meromorphicOn_strip_of_shift`).

The proof is a gluing argument.

* The identity theorem for meromorphic functions on preconnected sets propagates the shift
  equation from the real subinterval to a complex rectangle around a base subinterval
  `(a', b')` of length strictly between `c` and `2 * c`.
* Continuing `g` by repeated use of the shift equation (division by `m` to the right,
  multiplication by `m` to the left) gives meromorphic pieces on the rectangles translated by
  multiples of `c`. Neighbouring pieces agree on punctured neighbourhoods, non-neighbouring
  rectangles are disjoint, and the rectangles cover a horizontal strip, so the pieces glue.
* Finally the glued function is modified on the real segment `(a, b)`, at a discrete set of
  points only, so that it agrees with `g` there exactly.

All auxiliary declarations live in the namespace `DOZZ.Proofs.ShiftGluing`.
-/

@[expose] public section

open Filter Topology Set

namespace DOZZ.Proofs

namespace ShiftGluing

/-! ### Identity theorem and nonvanishing of the multiplier -/

/-- Local meromorphic identity theorem: two functions meromorphic on a preconnected set which
agree frequently near one point of the set agree near every point of the set (punctured). -/
theorem meromorphicOn_eventuallyEq_of_frequently {f g : ℂ → ℂ} {U : Set ℂ}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) (hU : IsPreconnected U)
    {x₀ y : ℂ} (hx₀ : x₀ ∈ U) (hy : y ∈ U) (hfreq : ∃ᶠ z in 𝓝[≠] x₀, f z = g z) :
    f =ᶠ[𝓝[≠] y] g := by
  have hsub : MeromorphicOn (f - g) U := hf.sub hg
  have h0 : (f - g) =ᶠ[𝓝[≠] x₀] 0 := by
    refine ((hsub x₀ hx₀).frequently_zero_iff_eventuallyEq_zero).mp ?_
    exact hfreq.mono fun z hz => by simp [hz]
  have htop : meromorphicOrderAt (f - g) x₀ = ⊤ := meromorphicOrderAt_eq_top_iff.mpr h0
  have htop' := hsub.meromorphicOrderAt_eq_top_of_isPreconnected hU hx₀ hy htop
  have := meromorphicOrderAt_eq_top_iff.mp htop'
  exact this.mono fun z hz => sub_eq_zero.mp hz

/-- A function meromorphic on the whole plane, analytic and nonzero at one point, is nonzero on
a punctured neighbourhood of every point. -/
theorem eventually_ne_zero_nhdsNE_of_meromorphicOn_univ {m : ℂ → ℂ}
    (hm : MeromorphicOn m Set.univ) (hm0 : ∃ z₀ : ℂ, AnalyticAt ℂ m z₀ ∧ m z₀ ≠ 0) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, m w ≠ 0 := by
  obtain ⟨z₀, han, hne⟩ := hm0
  have h0 : meromorphicOrderAt m z₀ ≠ ⊤ := by
    rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hm z₀ (mem_univ z₀))]
    exact eventually_nhdsWithin_of_eventually_nhds (han.continuousAt.eventually_ne hne)
  have hz : meromorphicOrderAt m z ≠ ⊤ :=
    hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ z₀)
      (mem_univ z) h0
  exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hm z (mem_univ z))).mp hz

/-- The shift relation, known on a real subinterval, propagates along preconnected subsets of
the common domain `W ∩ (· - c)⁻¹' W` that contain a real point of the interval `(a + c, b)`. -/
theorem shift_relation_eventually {c a b d₁ d₂ : ℝ} (hc : 0 < c)
    (hd₁ : a + c ≤ d₁) (hd : d₁ < d₂) (hd₂ : d₂ ≤ b) {W : Set ℂ} (hW : IsOpen W)
    (hWab : ∀ x : ℝ, a < x → x < b → (x : ℂ) ∈ W) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g W)
    {m : ℂ → ℂ} (hm : MeromorphicOn m Set.univ)
    (hrel : ∀ x : ℝ, d₁ < x → x < d₂ → g ((x : ℂ) - c) = m x * g x)
    {P : Set ℂ} (hP : IsPreconnected P) (hPO : P ⊆ W ∩ (fun z : ℂ => z - c) ⁻¹' W)
    {x₁ : ℝ} (hx₁a : a + c < x₁) (hx₁b : x₁ < b) (hx₁P : (x₁ : ℂ) ∈ P) :
    ∀ y ∈ P, (fun z : ℂ => g (z - c)) =ᶠ[𝓝[≠] y] (fun z : ℂ => m z * g z) := by
  have hgan : AnalyticOnNhd ℂ g W := hg.analyticOnNhd hW
  have hL : MeromorphicOn (fun z : ℂ => g (z - c)) (W ∩ (fun z : ℂ => z - c) ⁻¹' W) := by
    intro z hz
    have hzc : z - (c : ℂ) ∈ W := hz.2
    have hsub : AnalyticAt ℂ (fun w : ℂ => w - (c : ℂ)) z := analyticAt_id.sub analyticAt_const
    exact ((hgan (z - c) hzc).comp_of_eq hsub rfl).meromorphicAt
  have hR : MeromorphicOn (fun z : ℂ => m z * g z) (W ∩ (fun z : ℂ => z - c) ⁻¹' W) :=
    fun z hz => (hm z (mem_univ z)).mul (hgan z hz.1).meromorphicAt
  have hSpre : IsPreconnected ((fun t : ℝ => (t : ℂ)) '' Ioo (a + c) b) :=
    isPreconnected_Ioo.image _ Complex.continuous_ofReal.continuousOn
  have hSO : (fun t : ℝ => (t : ℂ)) '' Ioo (a + c) b ⊆ W ∩ (fun z : ℂ => z - c) ⁻¹' W := by
    rintro _ ⟨t, ⟨ht1, ht2⟩, rfl⟩
    refine ⟨hWab t (by linarith) ht2, ?_⟩
    have hcast : ((t : ℂ) - (c : ℂ)) = ((t - c : ℝ) : ℂ) := by push_cast; ring
    show ((t : ℂ) - (c : ℂ)) ∈ W
    rw [hcast]
    exact hWab _ (by linarith) (by linarith)
  have hP'pre : IsPreconnected (P ∪ (fun t : ℝ => (t : ℂ)) '' Ioo (a + c) b) :=
    hP.union (x₁ : ℂ) hx₁P ⟨x₁, ⟨hx₁a, hx₁b⟩, rfl⟩ hSpre
  have hP'O : P ∪ (fun t : ℝ => (t : ℂ)) '' Ioo (a + c) b ⊆
      W ∩ (fun z : ℂ => z - c) ⁻¹' W := union_subset hPO hSO
  obtain ⟨x₀, hx₀1, hx₀2⟩ : ∃ x₀ : ℝ, d₁ < x₀ ∧ x₀ < d₂ :=
    ⟨(d₁ + d₂) / 2, by linarith, by linarith⟩
  have hx₀S : (x₀ : ℂ) ∈ (fun t : ℝ => (t : ℂ)) '' Ioo (a + c) b :=
    ⟨x₀, ⟨by linarith, by linarith⟩, rfl⟩
  have htend : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] x₀) (𝓝[≠] (x₀ : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun t ht => by simpa [Complex.ofReal_inj] using ht)
  have hev : ∀ᶠ t : ℝ in 𝓝[≠] x₀, g ((t : ℂ) - c) = m (t : ℂ) * g (t : ℂ) :=
    eventually_nhdsWithin_of_eventually_nhds
      (Filter.mem_of_superset (Ioo_mem_nhds hx₀1 hx₀2) fun t ht => hrel t ht.1 ht.2)
  have hfreq : ∃ᶠ z in 𝓝[≠] (x₀ : ℂ), g (z - c) = m z * g z :=
    htend.frequently (p := fun z : ℂ => g (z - c) = m z * g z) hev.frequently
  intro y hy
  exact meromorphicOn_eventuallyEq_of_frequently (hL.mono_set hP'O) (hR.mono_set hP'O) hP'pre
    (Or.inr hx₀S) (Or.inl hy) hfreq

/-! ### Translated rectangles and transport of punctured germs -/

/-- The open rectangle `{z | a + t < re z < b + t, |im z| < h}`. -/
def shiftRect (a b h t : ℝ) : Set ℂ := {z : ℂ | a + t < z.re ∧ z.re < b + t ∧ |z.im| < h}

/-- A translated rectangle is open. -/
theorem isOpen_shiftRect (a b h t : ℝ) : IsOpen (shiftRect a b h t) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt Complex.continuous_im.abs continuous_const))

/-- A translated rectangle is convex, hence preconnected. -/
theorem convex_shiftRect (a b h t : ℝ) : Convex ℝ (shiftRect a b h t) := by
  have heq : shiftRect a b h t =
      Complex.reCLM ⁻¹' Ioo (a + t) (b + t) ∩ Complex.imCLM ⁻¹' Ioo (-h) h := by
    ext z
    simp [shiftRect, abs_lt, and_assoc]
  rw [heq]
  exact ((convex_Ioo (a + t) (b + t)).linear_preimage Complex.reCLM.toLinearMap).inter
    ((convex_Ioo (-h) h).linear_preimage Complex.imCLM.toLinearMap)

/-- A real point lies in a translated rectangle iff it lies in the translated interval. -/
theorem ofReal_mem_shiftRect_iff {a b h t x : ℝ} (hh : 0 < h) :
    (x : ℂ) ∈ shiftRect a b h t ↔ a + t < x ∧ x < b + t := by
  simp [shiftRect, hh]

/-- Subtracting a real step moves a point of the rectangle to the translated rectangle. -/
theorem sub_mem_shiftRect {a b h t t' c : ℝ} {z : ℂ} (hz : z ∈ shiftRect a b h t)
    (ht : t' = t - c) : z - (c : ℂ) ∈ shiftRect a b h t' := by
  obtain ⟨h1, h2, h3⟩ := hz
  have e1 : (z - (c : ℂ)).re = z.re - c := by simp
  have e2 : (z - (c : ℂ)).im = z.im := by simp
  show a + t' < (z - (c : ℂ)).re ∧ (z - (c : ℂ)).re < b + t' ∧ |(z - (c : ℂ)).im| < h
  rw [e1, e2]
  exact ⟨by linarith, by linarith, h3⟩

/-- Adding a real step moves a point of the rectangle to the translated rectangle. -/
theorem add_mem_shiftRect {a b h t t' c : ℝ} {z : ℂ} (hz : z ∈ shiftRect a b h t)
    (ht : t' = t + c) : z + (c : ℂ) ∈ shiftRect a b h t' := by
  obtain ⟨h1, h2, h3⟩ := hz
  have e1 : (z + (c : ℂ)).re = z.re + c := by simp
  have e2 : (z + (c : ℂ)).im = z.im := by simp
  show a + t' < (z + (c : ℂ)).re ∧ (z + (c : ℂ)).re < b + t' ∧ |(z + (c : ℂ)).im| < h
  rw [e1, e2]
  exact ⟨by linarith, by linarith, h3⟩

/-- Punctured germs are transported by the translation `w ↦ w - c`. -/
theorem eventually_comp_sub {p : ℂ → Prop} {z : ℂ} (c : ℂ)
    (h : ∀ᶠ w in 𝓝[≠] (z - c), p w) : ∀ᶠ w in 𝓝[≠] z, p (w - c) := by
  have htend : Tendsto (fun w : ℂ => w - c) (𝓝[≠] z) (𝓝[≠] (z - c)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((continuous_sub_right c).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun w hw => by simpa using hw)
  exact htend.eventually h

/-- Punctured germs are transported by the translation `w ↦ w + c`. -/
theorem eventually_comp_add {p : ℂ → Prop} {z : ℂ} (c : ℂ)
    (h : ∀ᶠ w in 𝓝[≠] (z + c), p w) : ∀ᶠ w in 𝓝[≠] z, p (w + c) := by
  have htend : Tendsto (fun w : ℂ => w + c) (𝓝[≠] z) (𝓝[≠] (z + c)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((continuous_id.add continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun w hw => by simpa using hw)
  exact htend.eventually h

/-! ### The continuation pieces -/

/-- Continuation of `g` by `k` steps to the right, using `g z = g (z - c) / m z`. -/
noncomputable def shiftUp (c : ℝ) (m g : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => g
  | k + 1 => fun z => shiftUp c m g k (z - c) / m z

/-- Continuation of `g` by `k` steps to the left, using `g z = m (z + c) * g (z + c)`. -/
noncomputable def shiftDown (c : ℝ) (m g : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => g
  | k + 1 => fun z => m (z + c) * shiftDown c m g k (z + c)

/-- The integer-indexed family of continuations: `n ≥ 0` steps right, `n < 0` steps left. -/
noncomputable def shiftPiece (c : ℝ) (m g : ℂ → ℂ) : ℤ → ℂ → ℂ
  | Int.ofNat k => shiftUp c m g k
  | Int.negSucc k => shiftDown c m g (k + 1)

/-- Nonnegative indices select the right continuations. -/
theorem shiftPiece_natCast (c : ℝ) (m g : ℂ → ℂ) (k : ℕ) :
    shiftPiece c m g (k : ℤ) = shiftUp c m g k := rfl

/-- Nonpositive indices select the left continuations. -/
theorem shiftPiece_neg_natCast (c : ℝ) (m g : ℂ → ℂ) (k : ℕ) :
    shiftPiece c m g (-(k : ℤ)) = shiftDown c m g k := by
  cases k <;> rfl

/-- The `k`-th right continuation is meromorphic on the `k`-th translated rectangle. -/
theorem meromorphicOn_shiftUp {c a b h : ℝ} {m g : ℂ → ℂ} (hm : MeromorphicOn m Set.univ)
    (hg : MeromorphicOn g (shiftRect a b h 0)) (k : ℕ) :
    MeromorphicOn (shiftUp c m g k) (shiftRect a b h (k * c)) := by
  induction k with
  | zero => simpa [shiftUp] using hg
  | succ k ih =>
    intro z hz
    have hz' : z - (c : ℂ) ∈ shiftRect a b h (k * c) :=
      sub_mem_shiftRect hz (by push_cast; ring)
    have h1 : MeromorphicAt (fun w : ℂ => shiftUp c m g k (w - c)) z :=
      meromorphicAt_fun_comp_sub_const_iff_meromorphicAt.mpr (ih _ hz')
    exact h1.div (hm z (mem_univ z))

/-- The `k`-th left continuation is meromorphic on the rectangle translated by `-k * c`. -/
theorem meromorphicOn_shiftDown {c a b h : ℝ} {m g : ℂ → ℂ} (hm : MeromorphicOn m Set.univ)
    (hg : MeromorphicOn g (shiftRect a b h 0)) (k : ℕ) :
    MeromorphicOn (shiftDown c m g k) (shiftRect a b h (-(k * c))) := by
  induction k with
  | zero => simpa [shiftDown] using hg
  | succ k ih =>
    intro z hz
    have hz' : z + (c : ℂ) ∈ shiftRect a b h (-(k * c)) :=
      add_mem_shiftRect hz (by push_cast; ring)
    have h1 : MeromorphicAt (fun w : ℂ => shiftDown c m g k (w + c)) z :=
      meromorphicAt_fun_comp_add_const_iff_meromorphicAt.mpr (ih _ hz')
    have h2 : MeromorphicAt (fun w : ℂ => m (w + c)) z :=
      meromorphicAt_fun_comp_add_const_iff_meromorphicAt.mpr (hm (z + c) (mem_univ _))
    exact h2.mul h1

/-- Neighbouring right continuations agree on punctured neighbourhoods of the overlap. -/
theorem shiftUp_compat {c a b h : ℝ} {m g : ℂ → ℂ} (hm0 : ∀ z, ∀ᶠ w in 𝓝[≠] z, m w ≠ 0)
    (hrel : ∀ y ∈ shiftRect a b h 0 ∩ shiftRect a b h c,
      ∀ᶠ w in 𝓝[≠] y, g (w - c) = m w * g w) (k : ℕ) :
    ∀ z ∈ shiftRect a b h (k * c), z ∈ shiftRect a b h ((k + 1) * c) →
      ∀ᶠ w in 𝓝[≠] z, shiftUp c m g (k + 1) w = shiftUp c m g k w := by
  induction k with
  | zero =>
    intro z hz₁ hz₂
    have hz₁' : z ∈ shiftRect a b h 0 := by simpa using hz₁
    have hz₂' : z ∈ shiftRect a b h c := by simpa using hz₂
    filter_upwards [hrel z ⟨hz₁', hz₂'⟩, hm0 z] with w hw hmw
    show g (w - c) / m w = g w
    rw [hw, mul_div_cancel_left₀ _ hmw]
  | succ k ih =>
    intro z hz₁ hz₂
    have h₁ : z - (c : ℂ) ∈ shiftRect a b h (k * c) :=
      sub_mem_shiftRect hz₁ (by push_cast; ring)
    have h₂ : z - (c : ℂ) ∈ shiftRect a b h ((k + 1) * c) :=
      sub_mem_shiftRect hz₂ (by push_cast; ring)
    filter_upwards [eventually_comp_sub
      (p := fun w => shiftUp c m g (k + 1) w = shiftUp c m g k w) c (ih _ h₁ h₂)] with w hw
    show shiftUp c m g (k + 1) (w - c) / m w = shiftUp c m g k (w - c) / m w
    rw [hw]

/-- Neighbouring left continuations agree on punctured neighbourhoods of the overlap. -/
theorem shiftDown_compat {c a b h : ℝ} {m g : ℂ → ℂ}
    (hrel : ∀ y ∈ shiftRect a b h 0 ∩ shiftRect a b h c,
      ∀ᶠ w in 𝓝[≠] y, g (w - c) = m w * g w) (k : ℕ) :
    ∀ z ∈ shiftRect a b h (-((k + 1) * c)), z ∈ shiftRect a b h (-(k * c)) →
      ∀ᶠ w in 𝓝[≠] z, shiftDown c m g (k + 1) w = shiftDown c m g k w := by
  induction k with
  | zero =>
    intro z hz₁ hz₂
    have hz₁' : z + (c : ℂ) ∈ shiftRect a b h 0 := add_mem_shiftRect hz₁ (by push_cast; ring)
    have hz₂' : z + (c : ℂ) ∈ shiftRect a b h c := add_mem_shiftRect hz₂ (by push_cast; ring)
    filter_upwards [eventually_comp_add (p := fun w => g (w - c) = m w * g w) c
      (hrel _ ⟨hz₁', hz₂'⟩)] with w hw
    show m (w + c) * g (w + c) = g w
    have hw' : g (w + c - c) = m (w + c) * g (w + c) := hw
    rw [← hw', add_sub_cancel_right]
  | succ k ih =>
    intro z hz₁ hz₂
    have h₁ : z + (c : ℂ) ∈ shiftRect a b h (-((k + 1) * c)) :=
      add_mem_shiftRect hz₁ (by push_cast; ring)
    have h₂ : z + (c : ℂ) ∈ shiftRect a b h (-(k * c)) :=
      add_mem_shiftRect hz₂ (by push_cast; ring)
    filter_upwards [eventually_comp_add
      (p := fun w => shiftDown c m g (k + 1) w = shiftDown c m g k w) c (ih _ h₁ h₂)] with w hw
    show m (w + c) * shiftDown c m g (k + 1) (w + c) = m (w + c) * shiftDown c m g k (w + c)
    rw [hw]

/-- Every piece is meromorphic on its rectangle. -/
theorem meromorphicOn_shiftPiece {c a b h : ℝ} {m g : ℂ → ℂ} (hm : MeromorphicOn m Set.univ)
    (hg : MeromorphicOn g (shiftRect a b h 0)) (n : ℤ) :
    MeromorphicOn (shiftPiece c m g n) (shiftRect a b h (n * c)) := by
  cases n with
  | ofNat k =>
    have hk := meromorphicOn_shiftUp (c := c) hm hg k
    have e : (((Int.ofNat k : ℤ) : ℝ)) * c = k * c := by simp
    rw [e]
    exact hk
  | negSucc k =>
    have hk := meromorphicOn_shiftDown (c := c) hm hg (k + 1)
    have e : (((Int.negSucc k : ℤ) : ℝ)) * c = -(((k + 1 : ℕ) : ℝ) * c) := by
      rw [Int.cast_negSucc]; push_cast; ring
    rw [e]
    exact hk

/-- Neighbouring pieces agree on punctured neighbourhoods of the overlap of their rectangles. -/
theorem shiftPiece_adj {c a b h : ℝ} {m g : ℂ → ℂ} (hm0 : ∀ z, ∀ᶠ w in 𝓝[≠] z, m w ≠ 0)
    (hrel : ∀ y ∈ shiftRect a b h 0 ∩ shiftRect a b h c,
      ∀ᶠ w in 𝓝[≠] y, g (w - c) = m w * g w) (n : ℤ) {z : ℂ}
    (hz₁ : z ∈ shiftRect a b h (n * c)) (hz₂ : z ∈ shiftRect a b h ((n + 1 : ℤ) * c)) :
    ∀ᶠ w in 𝓝[≠] z, shiftPiece c m g n w = shiftPiece c m g (n + 1) w := by
  cases n with
  | ofNat k =>
    have e₁ : (((Int.ofNat k : ℤ) : ℝ)) * c = k * c := by simp
    have e₂ : ((((Int.ofNat k : ℤ) + 1 : ℤ) : ℝ)) * c = (k + 1) * c := by simp
    rw [e₁] at hz₁
    rw [e₂] at hz₂
    exact (shiftUp_compat hm0 hrel k z hz₁ hz₂).mono fun w hw => hw.symm
  | negSucc k =>
    have e₁ : (((Int.negSucc k : ℤ) : ℝ)) * c = -((k + 1) * c) := by
      rw [Int.cast_negSucc]; push_cast; ring
    have e₂ : ((((Int.negSucc k : ℤ) + 1 : ℤ) : ℝ)) * c = -(k * c) := by
      have : (Int.negSucc k : ℤ) + 1 = -(k : ℤ) := by omega
      rw [this]; push_cast; ring
    rw [e₁] at hz₁
    rw [e₂] at hz₂
    have e : (Int.negSucc k : ℤ) + 1 = -(k : ℤ) := by omega
    rw [e, shiftPiece_neg_natCast]
    exact shiftDown_compat hrel k z hz₁ hz₂

/-- Any two pieces agree on punctured neighbourhoods of the common points of their rectangles:
the rectangles of non-neighbouring pieces are disjoint because the base interval is shorter
than `2 * c`. -/
theorem shiftPiece_compat {c a b h : ℝ} {m g : ℂ → ℂ} (hc : 0 < c) (hlen : b - a < 2 * c)
    (hm0 : ∀ z, ∀ᶠ w in 𝓝[≠] z, m w ≠ 0)
    (hrel : ∀ y ∈ shiftRect a b h 0 ∩ shiftRect a b h c,
      ∀ᶠ w in 𝓝[≠] y, g (w - c) = m w * g w) (i j : ℤ) {z : ℂ}
    (hi : z ∈ shiftRect a b h (i * c)) (hj : z ∈ shiftRect a b h (j * c)) :
    ∀ᶠ w in 𝓝[≠] z, shiftPiece c m g i w = shiftPiece c m g j w := by
  wlog hij : i ≤ j generalizing i j
  · exact (this j i hj hi (le_of_not_ge hij)).mono fun w hw => hw.symm
  have hj1 : j ≤ i + 1 := by
    by_contra hcon
    have h2 : (i : ℝ) + 2 ≤ j := by exact_mod_cast (by omega : i + 2 ≤ j)
    obtain ⟨_, hi2, _⟩ := hi
    obtain ⟨hj1, _, _⟩ := hj
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ j - i - 2) hc.le]
  rcases (by omega : j = i ∨ j = i + 1) with rfl | rfl
  · exact Eventually.of_forall fun w => rfl
  · exact shiftPiece_adj hm0 hrel i hi hj

/-- The pieces satisfy the shift equation wherever the multiplier does not vanish. -/
theorem shiftPiece_rel {c : ℝ} {m g : ℂ → ℂ} (n : ℤ) (w : ℂ) (hw : m w ≠ 0) :
    shiftPiece c m g (n - 1) (w - c) = m w * shiftPiece c m g n w := by
  cases n with
  | ofNat k =>
    cases k with
    | zero =>
      show shiftDown c m g 1 (w - c) = m w * g w
      show m (w - c + c) * g (w - c + c) = m w * g w
      rw [sub_add_cancel]
    | succ k =>
      have e : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by omega
      have : Int.ofNat (k + 1) - 1 = (k : ℤ) := e
      rw [this, shiftPiece_natCast]
      show shiftUp c m g k (w - c) = m w * (shiftUp c m g k (w - c) / m w)
      rw [mul_div_cancel₀ _ hw]
  | negSucc k =>
    have e : (Int.negSucc k : ℤ) - 1 = -((k + 2 : ℕ) : ℤ) := by omega
    rw [e, shiftPiece_neg_natCast]
    show m (w - c + c) * shiftDown c m g (k + 1) (w - c + c) = m w * shiftDown c m g (k + 1) w
    rw [sub_add_cancel]

/-- The rectangles translated by the integer multiples of `c` cover the strip, because the base
interval is longer than `c`. -/
theorem iUnion_shiftRect_eq {a b c h : ℝ} (hc : 0 < c) (hlen : c < b - a) :
    (⋃ n : ℤ, shiftRect a b h (n * c)) = horizontalStrip h := by
  ext z
  simp only [mem_iUnion]
  constructor
  · rintro ⟨n, hn⟩
    exact hn.2.2
  · intro hz
    refine ⟨⌊(z.re - b) / c⌋ + 1, ?_⟩
    have h1 := Int.lt_floor_add_one ((z.re - b) / c)
    have h2 := Int.floor_le ((z.re - b) / c)
    rw [div_lt_iff₀ hc] at h1
    rw [le_div_iff₀ hc] at h2
    refine ⟨?_, ?_, hz⟩
    · push_cast
      nlinarith
    · push_cast
      nlinarith

/-- Gluing the pieces gives a meromorphic function on the strip which agrees with `g` near every
point of the base rectangle and satisfies the shift equation near every point of the strip. -/
theorem exists_meromorphicOn_strip_of_base_relation {c a b h : ℝ} (hc : 0 < c) (hh : 0 < h)
    (hlen : c < b - a) (hlen2 : b - a < 2 * c) {m g : ℂ → ℂ}
    (hm : MeromorphicOn m Set.univ) (hm0 : ∀ z, ∀ᶠ w in 𝓝[≠] z, m w ≠ 0)
    (hg : MeromorphicOn g (shiftRect a b h 0))
    (hrel : ∀ y ∈ shiftRect a b h 0 ∩ shiftRect a b h c,
      ∀ᶠ w in 𝓝[≠] y, g (w - c) = m w * g w) :
    ∃ F : ℂ → ℂ, MeromorphicOn F (horizontalStrip h) ∧
      (∀ z ∈ shiftRect a b h 0, F =ᶠ[𝓝[≠] z] g) ∧
      ∀ z ∈ horizontalStrip h, ∀ᶠ w in 𝓝[≠] z, F (w - c) = m w * F w := by
  obtain ⟨F, hF, hpiece, -⟩ := exists_meromorphicOn_strip_gluing h hh
    (fun n : ℤ => shiftRect a b h (n * c)) (fun n => isOpen_shiftRect _ _ _ _)
    (iUnion_shiftRect_eq hc hlen) (shiftPiece c m g) (meromorphicOn_shiftPiece hm hg)
    (fun i j z hi hj => shiftPiece_compat hc hlen2 hm0 hrel i j hi hj)
  refine ⟨F, hF, ?_, ?_⟩
  · intro z hz
    have hz' : z ∈ shiftRect a b h (((0 : ℤ) : ℝ) * c) := by simpa using hz
    exact hpiece 0 z hz'
  · intro z hz
    have hz' : z ∈ ⋃ n : ℤ, shiftRect a b h (n * c) := by
      rw [iUnion_shiftRect_eq hc hlen]
      exact hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp hz'
    have hzc : z - (c : ℂ) ∈ shiftRect a b h (((n - 1 : ℤ) : ℝ) * c) :=
      sub_mem_shiftRect hn (by push_cast; ring)
    have h1 : ∀ᶠ w in 𝓝[≠] z, F w = shiftPiece c m g n w := hpiece n z hn
    have h2 : ∀ᶠ w in 𝓝[≠] (z - c), F w = shiftPiece c m g (n - 1) w :=
      hpiece (n - 1) (z - c) hzc
    filter_upwards [h1, eventually_comp_sub c h2, hm0 z] with w h1w h3w hmw
    rw [h3w, h1w]
    exact shiftPiece_rel n w hmw

/-! ### Choosing the base rectangle -/

/-- A real compact interval inside an open set `W` has a rectangular neighbourhood inside `W`. -/
theorem exists_shiftRect_subset {a b : ℝ} {W : Set ℂ} (hW : IsOpen W)
    (hab : ∀ x : ℝ, a ≤ x → x ≤ b → (x : ℂ) ∈ W) :
    ∃ h : ℝ, 0 < h ∧ shiftRect a b h 0 ⊆ W := by
  have hK : IsCompact ((fun t : ℝ => (t : ℂ)) '' Icc a b) :=
    isCompact_Icc.image Complex.continuous_ofReal
  have hKW : (fun t : ℝ => (t : ℂ)) '' Icc a b ⊆ W := by
    rintro _ ⟨t, ⟨ht1, ht2⟩, rfl⟩
    exact hab t ht1 ht2
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hW hKW
  refine ⟨δ, hδ, fun z hz => hthick ?_⟩
  obtain ⟨h1, h2, h3⟩ := hz
  rw [Metric.mem_thickening_iff]
  refine ⟨(z.re : ℂ), ⟨z.re, ⟨by linarith, by linarith⟩, rfl⟩, ?_⟩
  have hdist : dist z (z.re : ℂ) = |z.im| := by
    rw [Complex.dist_eq_re_im]
    simp [Real.sqrt_sq_eq_abs]
  rw [hdist]
  exact h3

/-- An interval `(a, b)` longer than `c` contains a subinterval `(a', b')` of length strictly
between `c` and `2 * c`. -/
theorem exists_base_interval {c a b : ℝ} (hc : 0 < c) (hab : c < b - a) :
    ∃ a' b' : ℝ, a < a' ∧ b' < b ∧ c < b' - a' ∧ b' - a' < 2 * c := by
  have hm0 : c < min (b - a) (2 * c) := lt_min hab (by linarith)
  have hm1 : min (b - a) (2 * c) ≤ b - a := min_le_left _ _
  have hm2 : min (b - a) (2 * c) ≤ 2 * c := min_le_right _ _
  obtain ⟨L, hL1, hL2⟩ : ∃ L : ℝ, c < L ∧ L < min (b - a) (2 * c) :=
    ⟨(c + min (b - a) (2 * c)) / 2, by linarith, by linarith⟩
  refine ⟨a + (b - a - L) / 2, a + (b - a - L) / 2 + L, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ### Overriding the values on the real segment -/

/-- A meromorphic function which agrees with `g` near every point of a real segment can be
modified on that segment (it differs from the original only on a discrete set) so that it
agrees with `g` exactly there. -/
theorem exists_override_on_segment {a b h : ℝ} {g F : ℂ → ℂ}
    (hgc : ∀ x : ℝ, a < x → x < b → ContinuousAt g (x : ℂ))
    (hF : MeromorphicOn F (horizontalStrip h))
    (hFg : ∀ x : ℝ, a < x → x < b → F =ᶠ[𝓝[≠] (x : ℂ)] g) :
    ∃ G : ℂ → ℂ, (∀ x : ℝ, a < x → x < b → G x = g x) ∧
      ∀ z ∈ horizontalStrip h, G =ᶠ[𝓝[≠] z] F := by
  classical
  refine ⟨fun z => if z.im = 0 ∧ a < z.re ∧ z.re < b then g z else F z, ?_, ?_⟩
  · intro x hx1 hx2
    simp [hx1, hx2]
  · intro z hz
    filter_upwards [(hF z hz).eventually_analyticAt] with w hw
    by_cases hcond : w.im = 0 ∧ a < w.re ∧ w.re < b
    · obtain ⟨him, hwa, hwb⟩ := hcond
      have hwe : ((w.re : ℝ) : ℂ) = w := Complex.ext (by simp) (by simp [him])
      have hFgw : F =ᶠ[𝓝[≠] w] g := by
        have := hFg w.re hwa hwb
        rwa [hwe] at this
      have hcF : Tendsto F (𝓝[≠] w) (𝓝 (F w)) :=
        hw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have hcg : Tendsto g (𝓝[≠] w) (𝓝 (g w)) := by
        have := hgc w.re hwa hwb
        rw [hwe] at this
        exact this.tendsto.mono_left nhdsWithin_le_nhds
      have hFw : F w = g w := tendsto_nhds_unique (hcF.congr' hFgw) hcg
      show (if w.im = 0 ∧ a < w.re ∧ w.re < b then g w else F w) = F w
      rw [ite_eq_left ⟨him, hwa, hwb⟩, hFw]
    · show (if w.im = 0 ∧ a < w.re ∧ w.re < b then g w else F w) = F w
      rw [ite_eq_right hcond]

end ShiftGluing

open ShiftGluing

/-- **Meromorphic continuation by a shift equation.** A function holomorphic on an open set `W`
containing a real interval `(a, b)` longer than the step `c`, satisfying the shift equation
`g (x - c) = m x * g x` on a real subinterval, extends to a meromorphic function on a horizontal
strip which agrees with `g` on `(a, b)` and satisfies the shift equation near every point. -/
theorem exists_meromorphicOn_strip_of_shift {c a b d₁ d₂ : ℝ} (hc : 0 < c) (hab : c < b - a)
    (hd₁ : a + c ≤ d₁) (hd : d₁ < d₂) (hd₂ : d₂ ≤ b)
    {W : Set ℂ} (hW : IsOpen W) (hWab : ∀ x : ℝ, a < x → x < b → (x : ℂ) ∈ W)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g W)
    {m : ℂ → ℂ} (hm : MeromorphicOn m Set.univ) (hm0 : ∃ z₀ : ℂ, AnalyticAt ℂ m z₀ ∧ m z₀ ≠ 0)
    (hrel : ∀ x : ℝ, d₁ < x → x < d₂ → g ((x : ℂ) - c) = m x * g x) :
    ∃ h : ℝ, 0 < h ∧ ∃ G : ℂ → ℂ, MeromorphicOn G (horizontalStrip h) ∧
      (∀ x : ℝ, a < x → x < b → G x = g x) ∧
      ∀ z ∈ horizontalStrip h, ∀ᶠ w in 𝓝[≠] z, G (w - c) = m w * G w := by
  obtain ⟨a', b', haa', hb'b, hlen, hlen2⟩ := exists_base_interval hc hab
  obtain ⟨h, hh, hrectW⟩ := exists_shiftRect_subset (a := a') (b := b') hW
    (fun x hx1 hx2 => hWab x (by linarith) (by linarith))
  have hgan : AnalyticOnNhd ℂ g W := hg.analyticOnNhd hW
  have hm0' := eventually_ne_zero_nhdsNE_of_meromorphicOn_univ hm hm0
  -- the shift relation on the overlap of the base rectangle with its translate
  have hPpre : IsPreconnected (shiftRect a' b' h 0 ∩ shiftRect a' b' h c) :=
    ((convex_shiftRect _ _ _ _).inter (convex_shiftRect _ _ _ _)).isPreconnected
  have hPO : shiftRect a' b' h 0 ∩ shiftRect a' b' h c ⊆ W ∩ (fun z : ℂ => z - c) ⁻¹' W :=
    fun z hz => ⟨hrectW hz.1, hrectW (sub_mem_shiftRect hz.2 (by ring))⟩
  have hx₁P : (((a' + c + b') / 2 : ℝ) : ℂ) ∈ shiftRect a' b' h 0 ∩ shiftRect a' b' h c :=
    ⟨(ofReal_mem_shiftRect_iff hh).mpr ⟨by linarith, by linarith⟩,
      (ofReal_mem_shiftRect_iff hh).mpr ⟨by linarith, by linarith⟩⟩
  have hrelP := shift_relation_eventually hc hd₁ hd hd₂ hW hWab hg hm hrel hPpre hPO
    (x₁ := (a' + c + b') / 2) (by linarith) (by linarith) hx₁P
  have hg0 : MeromorphicOn g (shiftRect a' b' h 0) := hgan.meromorphicOn.mono_set hrectW
  obtain ⟨F, hF, hFg0, hFrel⟩ := exists_meromorphicOn_strip_of_base_relation hc hh hlen hlen2 hm
    hm0' hg0 fun y hy => hrelP y hy
  -- `F` agrees with `g` near every point of the real segment `(a, b)`
  have hFseg : ∀ x : ℝ, a < x → x < b → F =ᶠ[𝓝[≠] (x : ℂ)] g := by
    have hSpre : IsPreconnected ((fun t : ℝ => (t : ℂ)) '' Ioo a b) :=
      isPreconnected_Ioo.image _ Complex.continuous_ofReal.continuousOn
    have hSstrip : (fun t : ℝ => (t : ℂ)) '' Ioo a b ⊆ horizontalStrip h := by
      rintro _ ⟨t, _, rfl⟩
      simpa [horizontalStrip] using hh
    have hSW : (fun t : ℝ => (t : ℂ)) '' Ioo a b ⊆ W := by
      rintro _ ⟨t, ⟨ht1, ht2⟩, rfl⟩
      exact hWab t ht1 ht2
    have hx₂S : (((a' + b') / 2 : ℝ) : ℂ) ∈ (fun t : ℝ => (t : ℂ)) '' Ioo a b :=
      ⟨(a' + b') / 2, ⟨by linarith, by linarith⟩, rfl⟩
    have hx₂R : (((a' + b') / 2 : ℝ) : ℂ) ∈ shiftRect a' b' h 0 :=
      (ofReal_mem_shiftRect_iff hh).mpr ⟨by linarith, by linarith⟩
    intro x hx1 hx2
    exact meromorphicOn_eventuallyEq_of_frequently (hF.mono_set hSstrip)
      (hgan.meromorphicOn.mono_set hSW) hSpre hx₂S ⟨x, ⟨hx1, hx2⟩, rfl⟩
      (hFg0 _ hx₂R).frequently
  obtain ⟨G, hGg, hGF⟩ := exists_override_on_segment
    (fun x hx1 hx2 => (hgan _ (hWab x hx1 hx2)).continuousAt) hF hFseg
  refine ⟨h, hh, G, ?_, hGg, ?_⟩
  · intro z hz
    exact (hF z hz).congr (hGF z hz).symm
  · intro z hz
    have hzc : z - (c : ℂ) ∈ horizontalStrip h := by
      have hz' : |z.im| < h := hz
      show |(z - (c : ℂ)).im| < h
      simpa using hz'
    filter_upwards [hGF z hz, eventually_comp_sub c (hGF (z - c) hzc), hFrel z hz] with w h1 h2 h3
    rw [h2, h1, h3]

end DOZZ.Proofs

end
