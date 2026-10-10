/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Assembly.KernelTail

/-! Finite-barrier two-root kernels as tilted Gaussian rectangle probabilities, their uniform off-diagonal convergence, and the off-diagonal uniform Cauchy property of the growing-barrier kernels. -/

@[expose] public section

/-! ### Finite-barrier kernels

The finite-barrier two-root kernel as a tilted Gaussian rectangle probability.

The coarse barrier coordinates at the two roots between levels `k₀` and `m` are indexed by a
`Fin` type. In this form the uniform off-diagonal convergence of the compatible finite kernels
applies, uniformly for bounded charges. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Assembly

open DOZZ.Proofs

/-- An admissible regularization is jointly Gaussian along any finite family of admissible
cutoffs and points, indexed by an arbitrary finite type. -/
theorem admissible_isCenteredJointlyGaussian_fintype
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    {ι : Type*} [Fintype ι] (q : ι → ℝ × ℂ) (hq : ∀ i, 0 < (q i).1 ∧ (q i).1 ≤ ε₀) :
    IsCenteredJointlyGaussian P (fun ω i => Y ω (q i).1 (q i).2) := by
  let e := Fintype.equivFin ι
  have h := hY.gaussian (Fintype.card ι) (fun j => q (e.symm j)) (fun j => hq _)
  have h2 := centeredJointlyGaussian_reindex P e _ h
  simpa using h2

/-- Number of coarse barrier coordinates for two roots between levels `k₀` and `m`. -/
def pairCoarseCount (k₀ m : ℕ) : ℕ := (m + 1 - k₀) * 2

/-- The integer scale of a coarse barrier coordinate. -/
def pairCoarseScale (k₀ m : ℕ) (i : Fin (pairCoarseCount k₀ m)) : ℕ :=
  k₀ + ((finProdFinEquiv.symm i).1 : ℕ)

/-- The root carrying a coarse barrier coordinate. -/
def pairCoarseCenter (k₀ m : ℕ) (p : ℂ × ℂ) (i : Fin (pairCoarseCount k₀ m)) : ℂ :=
  if (finProdFinEquiv.symm i).2 = 0 then p.1 else p.2

theorem pairCoarseScale_ge (k₀ m : ℕ) (i : Fin (pairCoarseCount k₀ m)) :
    k₀ ≤ pairCoarseScale k₀ m i := Nat.le_add_right _ _

theorem pairCoarseScale_le (k₀ m : ℕ) (i : Fin (pairCoarseCount k₀ m)) :
    pairCoarseScale k₀ m i ≤ m := by
  have h := ((finProdFinEquiv.symm i).1).isLt
  unfold pairCoarseScale
  omega

theorem pairCoarseCenter_mem (k₀ m : ℕ) (p : ℂ × ℂ) (K : Set ℂ) (hp : p ∈ K ×ˢ K)
    (i : Fin (pairCoarseCount k₀ m)) : pairCoarseCenter k₀ m p i ∈ K := by
  unfold pairCoarseCenter
  split_ifs
  · exact hp.1
  · exact hp.2

/-- The level-`m` barrier at both roots is the finite coarse rectangle. -/
theorem pair_barrier_iff {Ω : Type*} (Y : Ω → ℝ → ℂ → ℝ) (a : ℝ) (k₀ m : ℕ) (ω : Ω)
    (p : ℂ × ℂ) :
    ((ω, p.1) ∈ admissibleGrowingBarrierSet Y a k₀ (m : ℝ) ∧
        (ω, p.2) ∈ admissibleGrowingBarrierSet Y a k₀ (m : ℝ)) ↔
      ∀ i, Y ω (Real.exp (-(pairCoarseScale k₀ m i : ℝ))) (pairCoarseCenter k₀ m p i) ≤
        a * (pairCoarseScale k₀ m i : ℝ) := by
  constructor
  · rintro ⟨hx, hy⟩ i
    have hge := pairCoarseScale_ge k₀ m i
    have hle : ((pairCoarseScale k₀ m i : ℕ) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast pairCoarseScale_le k₀ m i
    unfold pairCoarseCenter
    split_ifs
    · exact hx _ hge hle
    · exact hy _ hge hle
  · intro h
    have hcoord (k : ℕ) (hk₀ : k₀ ≤ k) (hkm : (k : ℝ) ≤ (m : ℝ)) (c : Fin 2) :
        Y ω (Real.exp (-(k : ℝ))) (if c = 0 then p.1 else p.2) ≤ a * (k : ℝ) := by
      have hkm' : k ≤ m := by exact_mod_cast hkm
      have hlt : k - k₀ < m + 1 - k₀ := by omega
      let i : Fin (pairCoarseCount k₀ m) := finProdFinEquiv (⟨k - k₀, hlt⟩, c)
      have hi := h i
      have hsymm : finProdFinEquiv.symm i = (⟨k - k₀, hlt⟩, c) := by
        simp [i]
      have hscale : pairCoarseScale k₀ m i = k := by
        unfold pairCoarseScale
        rw [hsymm]
        simp only
        omega
      have hcenter : pairCoarseCenter k₀ m p i = if c = 0 then p.1 else p.2 := by
        unfold pairCoarseCenter
        rw [hsymm]
      rw [hscale, hcenter] at hi
      exact hi
    refine ⟨fun k hk₀ hkm => ?_, fun k hk₀ hkm => ?_⟩
    · simpa using hcoord k hk₀ hkm 0
    · simpa using hcoord k hk₀ hkm 1

/-- The rectangle indicator of a measurable finite family is measurable. -/
theorem gaussianRectangleIndicator_measurable
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (Z : Ω → ι → ℝ) (hZ : ∀ i, Measurable (fun ω => Z ω i)) (b c : ι → ℝ) :
    Measurable (gaussianRectangleIndicator Z b c) := by
  classical
  have hset : MeasurableSet {ω | ∀ i, Z ω i + c i ≤ b i} := by
    have hEq : {ω | ∀ i, Z ω i + c i ≤ b i} = ⋂ i, {ω | Z ω i + c i ≤ b i} := by
      ext ω; simp
    rw [hEq]
    exact MeasurableSet.iInter fun i =>
      measurableSet_le ((hZ i).add measurable_const) measurable_const
  unfold gaussianRectangleIndicator
  exact Measurable.ite hset measurable_const measurable_const

/-- The finite-barrier kernel of two roots is the Wick covariance factor times a shifted Gaussian
rectangle probability. -/
theorem finiteBarrierPairKernel_eq_rectangle
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (g a : ℝ) (k₀ m : ℕ) (hk₀cut : Real.exp (-(k₀ : ℝ)) ≤ ε₀)
    (ε δ : ℝ) (hε : 0 < ε) (hεcut : ε ≤ ε₀) (hδ : 0 < δ) (hδcut : δ ≤ ε₀)
    (p : ℂ × ℂ) :
    compatibleAdmissibleSelectedFiniteBarrierPairKernel P Y Y g a k₀ m ε δ p.1 p.2
        true true =
      ENNReal.ofReal (Real.exp (g ^ 2 * gaussianCovariance P
          (fun ω => Y ω ε p.1) (fun ω => Y ω δ p.2)) *
        ∫ ω, gaussianRectangleIndicator
          (fun ω i => Y ω (Real.exp (-(pairCoarseScale k₀ m i : ℝ)))
            (pairCoarseCenter k₀ m p i))
          (fun i => a * (pairCoarseScale k₀ m i : ℝ))
          (fun i => g * gaussianCovariance P
              (fun ω => Y ω (Real.exp (-(pairCoarseScale k₀ m i : ℝ)))
                (pairCoarseCenter k₀ m p i)) (fun ω => Y ω ε p.1) +
            g * gaussianCovariance P
              (fun ω => Y ω (Real.exp (-(pairCoarseScale k₀ m i : ℝ)))
                (pairCoarseCenter k₀ m p i)) (fun ω => Y ω δ p.2)) ω ∂P) := by
  classical
  let n := pairCoarseCount k₀ m
  let scale := pairCoarseScale k₀ m
  let center := pairCoarseCenter k₀ m p
  let tup : Fin n ⊕ Bool → ℝ × ℂ := fun i =>
    match i with
    | .inl j => (Real.exp (-(scale j : ℝ)), center j)
    | .inr false => (ε, p.1)
    | .inr true => (δ, p.2)
  let V : Ω → Fin n ⊕ Bool → ℝ := fun ω i => Y ω (tup i).1 (tup i).2
  have hscalecut (j : Fin n) : Real.exp (-(scale j : ℝ)) ≤ ε₀ := by
    have hge : (k₀ : ℝ) ≤ (scale j : ℝ) := by exact_mod_cast pairCoarseScale_ge k₀ m j
    exact le_trans (Real.exp_le_exp.mpr (by linarith)) hk₀cut
  have hV : IsCenteredJointlyGaussian P V := by
    apply admissible_isCenteredJointlyGaussian_fintype P U dens ε₀ Y hY tup
    intro i
    rcases i with j | b
    · exact ⟨Real.exp_pos _, hscalecut j⟩
    · cases b
      · exact ⟨hε, hεcut⟩
      · exact ⟨hδ, hδcut⟩
  let barrier : Fin n → ℝ := fun j => a * (scale j : ℝ)
  have htilt := finite_gaussian_wick_pair_tilt_with_coarse_rectangle P V hV (.inr false)
    (.inr true) g Sum.inl barrier
  have hVp : (fun ω => V ω (.inr false)) = fun ω => Y ω ε p.1 := rfl
  have hVq : (fun ω => V ω (.inr true)) = fun ω => Y ω δ p.2 := rfl
  have hVj (j : Fin n) : (fun ω => V ω (.inl j)) =
      fun ω => Y ω (Real.exp (-(scale j : ℝ))) (center j) := rfl
  -- the left side is the finite-barrier kernel
  have hleft : compatibleAdmissibleSelectedFiniteBarrierPairKernel P Y Y g a k₀ m ε δ p.1 p.2
      true true =
      ∫⁻ ω, ENNReal.ofReal (Real.exp (g * V ω (.inr false) - g ^ 2 / 2 *
          gaussianVariance P (fun ω => V ω (.inr false)))) *
        ENNReal.ofReal (Real.exp (g * V ω (.inr true) - g ^ 2 / 2 *
          gaussianVariance P (fun ω => V ω (.inr true)))) *
        Set.indicator {z : Fin n ⊕ Bool → ℝ | ∀ i, z (Sum.inl i) ≤ barrier i}
          (fun _ => (1 : ℝ≥0∞)) (V ω) ∂P := by
    unfold compatibleAdmissibleSelectedFiniteBarrierPairKernel
    apply lintegral_congr
    intro ω
    have hI : Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ))
          (fun _ => (1 : ℝ≥0∞)) (ω, p.1) *
        Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ))
          (fun _ => (1 : ℝ≥0∞)) (ω, p.2) =
        Set.indicator {z : Fin n ⊕ Bool → ℝ | ∀ i, z (Sum.inl i) ≤ barrier i}
          (fun _ => (1 : ℝ≥0∞)) (V ω) := by
      by_cases hbar : ∀ i, V ω (Sum.inl i) ≤ barrier i
      · have hboth := (pair_barrier_iff Y a k₀ m ω p).mpr hbar
        rw [Set.indicator_of_mem hboth.1, Set.indicator_of_mem hboth.2,
          Set.indicator_of_mem (show V ω ∈ {z : Fin n ⊕ Bool → ℝ |
            ∀ i, z (Sum.inl i) ≤ barrier i} from hbar), mul_one]
      · rw [Set.indicator_of_notMem (show V ω ∉ {z : Fin n ⊕ Bool → ℝ |
            ∀ i, z (Sum.inl i) ≤ barrier i} from hbar)]
        have hnot : ¬ ((ω, p.1) ∈ admissibleGrowingBarrierSet Y a k₀ (m : ℝ) ∧
            (ω, p.2) ∈ admissibleGrowingBarrierSet Y a k₀ (m : ℝ)) :=
          fun h => hbar ((pair_barrier_iff Y a k₀ m ω p).mp h)
        by_cases hx : (ω, p.1) ∈ admissibleGrowingBarrierSet Y a k₀ (m : ℝ)
        · have hy : (ω, p.2) ∉ admissibleGrowingBarrierSet Y a k₀ (m : ℝ) :=
            fun hy => hnot ⟨hx, hy⟩
          rw [Set.indicator_of_notMem hy, mul_zero]
        · rw [Set.indicator_of_notMem hx, zero_mul]
    simp only [ite_self]
    rw [show ∀ u v w z : ℝ≥0∞, u * v * w * z = u * v * (w * z) from
      fun u v w z => by ring, hI]
    rfl
  -- the shifted rectangle
  let Z : Ω → Fin n → ℝ := fun ω j => Y ω (Real.exp (-(scale j : ℝ))) (center j)
  let shift : Fin n → ℝ := fun j =>
    g * gaussianCovariance P (fun ω => Z ω j) (fun ω => Y ω ε p.1) +
      g * gaussianCovariance P (fun ω => Z ω j) (fun ω => Y ω δ p.2)
  have hZmeas (j : Fin n) : Measurable (fun ω => Z ω j) :=
    admissible_field_measurable_sample P U dens ε₀ Y hY _ _
  have hrectMeas := gaussianRectangleIndicator_measurable Z hZmeas barrier shift
  have hrectInt : Integrable (gaussianRectangleIndicator Z barrier shift) P := by
    refine Integrable.of_bound hrectMeas.aestronglyMeasurable 1 (ae_of_all _ fun ω => ?_)
    unfold gaussianRectangleIndicator
    split_ifs <;> simp
  have hright : (∫⁻ ω, Set.indicator {z : Fin n ⊕ Bool → ℝ | ∀ i, z (Sum.inl i) ≤ barrier i}
      (fun _ => (1 : ℝ≥0∞)) (fun i => V ω i + g *
        gaussianCovariance P (fun ω => V ω i) (fun ω => V ω (.inr false)) + g *
        gaussianCovariance P (fun ω => V ω i) (fun ω => V ω (.inr true))) ∂P) =
      ENNReal.ofReal (∫ ω, gaussianRectangleIndicator Z barrier shift ω ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hrectInt (ae_of_all _ fun ω => by
      unfold gaussianRectangleIndicator; split_ifs <;> norm_num)]
    apply lintegral_congr
    intro ω
    have hiff : (∀ i, V ω (Sum.inl i) + g * gaussianCovariance P (fun ω => V ω (Sum.inl i))
        (fun ω => V ω (.inr false)) + g * gaussianCovariance P
          (fun ω => V ω (Sum.inl i)) (fun ω => V ω (.inr true)) ≤ barrier i) ↔
        (∀ i, Z ω i + shift i ≤ barrier i) := by
      apply forall_congr'
      intro i
      simp only [Z, shift, hVp, hVq, hVj, add_assoc]
      exact Iff.rfl
    by_cases hc : ∀ i, Z ω i + shift i ≤ barrier i
    · rw [Set.indicator_of_mem (show (fun i => V ω i + g *
          gaussianCovariance P (fun ω => V ω i) (fun ω => V ω (.inr false)) + g *
          gaussianCovariance P (fun ω => V ω i) (fun ω => V ω (.inr true))) ∈
          {z : Fin n ⊕ Bool → ℝ | ∀ i, z (Sum.inl i) ≤ barrier i} from hiff.mpr hc)]
      unfold gaussianRectangleIndicator
      simp [hc]
    · rw [Set.indicator_of_notMem (show (fun i => V ω i + g *
          gaussianCovariance P (fun ω => V ω i) (fun ω => V ω (.inr false)) + g *
          gaussianCovariance P (fun ω => V ω i) (fun ω => V ω (.inr true))) ∉
          {z : Fin n ⊕ Bool → ℝ | ∀ i, z (Sum.inl i) ≤ barrier i} from
            fun h => hc (hiff.mp h))]
      unfold gaussianRectangleIndicator
      simp [hc]
  have hcovsymm : gaussianCovariance P (fun ω => Y ω δ p.2) (fun ω => Y ω ε p.1) =
      gaussianCovariance P (fun ω => Y ω ε p.1) (fun ω => Y ω δ p.2) := by
    unfold gaussianCovariance
    congr 1
    funext ω
    ring
  have hprefactor : Real.exp (g ^ 2 / 2 *
      (gaussianCovariance P (fun ω => V ω (.inr false)) (fun ω => V ω (.inr true)) +
        gaussianCovariance P (fun ω => V ω (.inr true)) (fun ω => V ω (.inr false)))) =
      Real.exp (g ^ 2 * gaussianCovariance P (fun ω => Y ω ε p.1) (fun ω => Y ω δ p.2)) := by
    rw [hVp, hVq, hcovsymm]
    congr 1
    ring
  rw [hleft]
  simp only at htilt
  rw [htilt, hright, hprefactor, ← ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- Pairs of points of `K` at distance at least `s₀`. -/
def separatedPairs (K : Set ℂ) (s₀ : ℝ) : Set (ℂ × ℂ) :=
  (K ×ˢ K) ∩ {p | s₀ ≤ ‖p.1 - p.2‖}

theorem isCompact_separatedPairs (K : Set ℂ) (hK : IsCompact K) (s₀ : ℝ) :
    IsCompact (separatedPairs K s₀) :=
  (hK.prod hK).inter_right
    (isClosed_le continuous_const (continuous_fst.sub continuous_snd).norm)


/-- Finite-barrier kernels are uniformly Cauchy off the diagonal as both cutoffs vanish,
uniformly for bounded charges. -/
theorem finiteBarrierPairKernel_toReal_uniform_cauchy
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (a : ℝ) (k₀ m : ℕ) (hk₀m : k₀ ≤ m) (hk₀cut : Real.exp (-(k₀ : ℝ)) ≤ ε₀)
    (hvar : ∀ k : ℕ, k₀ ≤ k → ∀ x ∈ K,
      1 ≤ gaussianVariance P (fun ω => Y ω (Real.exp (-(k : ℝ))) x))
    (s₀ : ℝ) (hs₀ : 0 < s₀) (Γ : Set ℝ) (B : ℝ) (hB : 0 ≤ B) (hΓ : ∀ g ∈ Γ, |g| ≤ B)
    (η : ℝ) (hη : 0 < η) :
    ∃ R : ℝ, ∀ r s r' s' : ℝ, R ≤ r → R ≤ s → R ≤ r' → R ≤ s' → ∀ g ∈ Γ,
      ∀ p ∈ separatedPairs K s₀,
      |(compatibleAdmissibleSelectedFiniteBarrierPairKernel P Y Y g a k₀ m
          (Real.exp (-r)) (Real.exp (-s)) p.1 p.2 true true).toReal -
        (compatibleAdmissibleSelectedFiniteBarrierPairKernel P Y Y g a k₀ m
          (Real.exp (-r')) (Real.exp (-s')) p.1 p.2 true true).toReal| < η := by
  have hYY := isCompatibleAdmissibleRegularizations_self P U dens ε₀ Y hY
  have : Nonempty (Fin (pairCoarseCount k₀ m)) :=
    ⟨⟨0, by unfold pairCoarseCount; omega⟩⟩
  have hscalecut (i : Fin (pairCoarseCount k₀ m)) :
      Real.exp (-(pairCoarseScale k₀ m i : ℝ)) ≤ ε₀ := by
    have hge : (k₀ : ℝ) ≤ (pairCoarseScale k₀ m i : ℝ) := by
      exact_mod_cast pairCoarseScale_ge k₀ m i
    exact le_trans (Real.exp_le_exp.mpr (by linarith)) hk₀cut
  obtain ⟨H, _hH, coarseKernel, hconv⟩ := compatible_finite_mixed_pair_kernel_tendsto_uniformly
    P U dens ε₀ ε₀ Y Y hY hY hYY K hK hKU (separatedPairs K s₀)
    (isCompact_separatedPairs K hK s₀) inter_subset_left s₀ hs₀ (fun p hp => hp.2)
    (pairCoarseScale k₀ m) (fun i => by rw [min_self]; exact hscalecut i)
    (fun p i => pairCoarseCenter k₀ m p i)
    (fun p hp i => pairCoarseCenter_mem k₀ m p K hp.1 i)
    (fun p hp i => hvar _ (pairCoarseScale_ge k₀ m i) _ (pairCoarseCenter_mem k₀ m p K hp.1 i))
    (fun i => a * (pairCoarseScale k₀ m i : ℝ)) true true Γ B hB hΓ
  obtain ⟨δ, hδ, hδconv⟩ := hconv (η / 2) (half_pos hη)
  have hcut : 0 < min δ ε₀ := lt_min hδ hY.cutoffPositive
  refine ⟨-Real.log (min δ ε₀), ?_⟩
  intro r s r' s' hr hs hr' hs' g hg p hp
  have hexp (t : ℝ) (ht : -Real.log (min δ ε₀) ≤ t) :
      Real.exp (-t) ≤ min δ (min ε₀ ε₀) := by
    rw [min_self]
    calc Real.exp (-t) ≤ Real.exp (Real.log (min δ ε₀)) := Real.exp_le_exp.mpr (by linarith)
      _ = min δ ε₀ := Real.exp_log hcut
  have hle (t : ℝ) (ht : -Real.log (min δ ε₀) ≤ t) : Real.exp (-t) ≤ ε₀ := by
    have h := hexp t ht
    rw [min_self] at h
    exact h.trans (min_le_right _ _)
  have h1 := hδconv (Real.exp (-r)) (Real.exp (-s)) (Real.exp_pos _) (hexp r hr)
    (Real.exp_pos _) (hexp s hs) g hg p hp
  have h2 := hδconv (Real.exp (-r')) (Real.exp (-s')) (Real.exp_pos _) (hexp r' hr')
    (Real.exp_pos _) (hexp s' hs') g hg p hp
  simp only [ite_self] at h1 h2
  have hnonneg (ε δ' : ℝ) : 0 ≤ Real.exp (g ^ 2 * gaussianCovariance P
          (fun ω => Y ω ε p.1) (fun ω => Y ω δ' p.2)) *
        ∫ ω, gaussianRectangleIndicator
          (fun ω i => Y ω (Real.exp (-(pairCoarseScale k₀ m i : ℝ)))
            (pairCoarseCenter k₀ m p i))
          (fun i => a * (pairCoarseScale k₀ m i : ℝ))
          (fun i => g * gaussianCovariance P
              (fun ω => Y ω (Real.exp (-(pairCoarseScale k₀ m i : ℝ)))
                (pairCoarseCenter k₀ m p i)) (fun ω => Y ω ε p.1) +
            g * gaussianCovariance P
              (fun ω => Y ω (Real.exp (-(pairCoarseScale k₀ m i : ℝ)))
                (pairCoarseCenter k₀ m p i)) (fun ω => Y ω δ' p.2)) ω ∂P := by
    apply mul_nonneg (Real.exp_pos _).le
    apply integral_nonneg
    intro ω
    unfold gaussianRectangleIndicator
    split_ifs <;> norm_num
  rw [finiteBarrierPairKernel_eq_rectangle P U dens ε₀ Y hY g a k₀ m hk₀cut _ _
      (Real.exp_pos _) (hle r hr) (Real.exp_pos _) (hle s hs) p,
    finiteBarrierPairKernel_eq_rectangle P U dens ε₀ Y hY g a k₀ m hk₀cut _ _
      (Real.exp_pos _) (hle r' hr') (Real.exp_pos _) (hle s' hs') p,
    ENNReal.toReal_ofReal (hnonneg _ _), ENNReal.toReal_ofReal (hnonneg _ _)]
  calc _ ≤ _ := abs_sub_le _ (Real.exp (g ^ 2 * (Real.log (1 / ‖p.1 - p.2‖) + H p.1 p.2)) *
        (∫ ω, gaussianRectangleIndicator
          (fun ω i => Y ω (Real.exp (-(pairCoarseScale k₀ m i : ℝ))) (pairCoarseCenter k₀ m p i))
          (fun i => a * (pairCoarseScale k₀ m i : ℝ))
          (fun i => g * coarseKernel (pairCoarseScale k₀ m i) p.1 (pairCoarseCenter k₀ m p i) +
            g * coarseKernel (pairCoarseScale k₀ m i) p.2 (pairCoarseCenter k₀ m p i)) ω ∂P)) _
    _ < η / 2 + η / 2 := add_lt_add h1 (by rw [abs_sub_comm]; exact h2)
    _ = η := by ring

end DOZZ.Assembly

/-! ### Off-diagonal Cauchy property

Off the diagonal, the growing-barrier two-root kernels are uniformly Cauchy.

Truncate both growing barriers at a fixed level `m`; the omitted barriers cost a summable tail,
and the truncated kernels converge uniformly. Every estimate is uniform for charges in a compact
interval below the barrier slope. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Assembly

open DOZZ.Proofs

/-- The two-root growing-barrier Wick kernel of one admissible regularization. -/
noncomputable abbrev growingPairKernel {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ → ℂ → ℝ) (g a : ℝ) (k₀ : ℕ) (r s : ℝ) (p : ℂ × ℂ) : ℝ≥0∞ :=
  compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel P Y Y g a k₀ r s p.1 p.2 true true

/-- A real distance bound for two extended reals squeezed by an additive error. -/
theorem abs_toReal_sub_le_of_le_add {x y t : ℝ≥0∞} (hyx : y ≤ x) (hx : x ≤ y + t)
    (hxtop : x ≠ ⊤) (ht : t ≠ ⊤) : |x.toReal - y.toReal| ≤ t.toReal := by
  have hytop : y ≠ ⊤ := ne_top_of_le_ne_top hxtop hyx
  rw [← ENNReal.toReal_sub_of_le hyx hxtop, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono ht (tsub_le_iff_left.mpr hx)

/-- The summed omitted-barrier rate is monotone in the charge. -/
theorem tsum_barrier_rate_le_of_le (g gHi a : ℝ) (hg : g ≤ gHi) (hga : gHi < a) (N : ℕ) :
    ∑' j : ℕ, ENNReal.ofReal (Real.exp (-((a - g) ^ 2 * ((j + N : ℕ) : ℝ) / 16))) ≤
      ∑' j : ℕ, ENNReal.ofReal (Real.exp (-((a - gHi) ^ 2 * ((j + N : ℕ) : ℝ) / 16))) := by
  apply ENNReal.tsum_le_tsum
  intro j
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have h1 : 0 ≤ a - gHi := (sub_pos.mpr hga).le
  have h2 : a - gHi ≤ a - g := by linarith
  have hsq : (a - gHi) ^ 2 ≤ (a - g) ^ 2 := pow_le_pow_left₀ h1 h2 2
  have hn : (0 : ℝ) ≤ ((j + N : ℕ) : ℝ) := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_right hsq hn
  linarith

/-- Off-diagonal uniform Cauchy property of the growing-barrier kernels, uniformly for charges in
`[gLo, gHi]` with `gHi < a`. The kernels are finite there. -/
theorem growingPairKernel_offDiagonal_uniform_cauchy
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (gLo gHi a : ℝ) (hgLo : 0 < gLo) (hgLoHi : gLo ≤ gHi) (hga : gHi < a)
    (k₀ : ℕ) (hk₀cut : Real.exp (-(k₀ : ℝ)) ≤ ε₀)
    (hvar : ∀ k : ℕ, k₀ ≤ k → ∀ x ∈ K,
      1 ≤ gaussianVariance P (fun ω => Y ω (Real.exp (-(k : ℝ))) x))
    (s₀ : ℝ) (hs₀ : 0 < s₀) (η : ℝ) (hη : 0 < η) :
    ∃ R : ℝ, ∀ r s r' s' : ℝ, R ≤ r → R ≤ s → R ≤ r' → R ≤ s' →
      ∀ g ∈ Icc gLo gHi, ∀ p ∈ separatedPairs K s₀,
        growingPairKernel P Y g a k₀ r s p ≠ ⊤ ∧
        |(growingPairKernel P Y g a k₀ r s p).toReal -
          (growingPairKernel P Y g a k₀ r' s' p).toReal| < η := by
  obtain ⟨C, hC, htail⟩ := finiteBarrierPairKernel_le_growing_add_tail P U dens ε₀ Y hY K hK hKU
  let L : ℝ := Real.log (1 / s₀)
  have hL (p : ℂ × ℂ) (hp : p ∈ separatedPairs K s₀) :
      0 < ‖p.1 - p.2‖ ∧ Real.log (1 / ‖p.1 - p.2‖) ≤ L := by
    have hsep : s₀ ≤ ‖p.1 - p.2‖ := hp.2
    have hpos : 0 < ‖p.1 - p.2‖ := lt_of_lt_of_le hs₀ hsep
    refine ⟨hpos, Real.log_le_log (one_div_pos.mpr hpos) ?_⟩
    exact one_div_le_one_div_of_le hs₀ hsep
  let cHi : ℝ≥0∞ := ENNReal.ofReal (Real.exp (gHi ^ 2 * max (L + C) 0))
  let THi : ℕ → ℝ≥0∞ := fun N => ∑' j : ℕ,
    ENNReal.ofReal (Real.exp (-((a - gHi) ^ 2 * ((j + N : ℕ) : ℝ) / 16)))
  have hTHi : Tendsto THi atTop (𝓝 0) :=
    tendsto_compatible_mixed_double_root_barrier_tail_sum gHi a hga
  have hcHi : cHi ≠ ⊤ := ENNReal.ofReal_ne_top
  have herr : Tendsto (fun m : ℕ => 2 * (cHi * THi (m + 1))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => THi (m + 1)) atTop (𝓝 0) :=
      hTHi.comp (tendsto_add_atTop_nat 1)
    have h2 := ENNReal.Tendsto.const_mul h1 (Or.inr hcHi)
    rw [mul_zero] at h2
    have h3 := ENNReal.Tendsto.const_mul h2 (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
    rwa [mul_zero] at h3
  have hη4 : (0 : ℝ≥0∞) < ENNReal.ofReal (η / 4) := ENNReal.ofReal_pos.mpr (by linarith)
  -- choose the truncation level
  have hev : ∀ᶠ m : ℕ in atTop, k₀ ≤ m ∧ C < (m : ℝ) ∧
      gHi * (|L| + 2 * C) ≤ (a - gHi) * (m : ℝ) / 2 ∧
      2 * (cHi * THi (m + 1)) < ENNReal.ofReal (η / 4) := by
    have hlin : ∀ᶠ m : ℕ in atTop, gHi * (|L| + 2 * C) ≤ (a - gHi) * (m : ℝ) / 2 := by
      obtain ⟨N, hN⟩ := exists_nat_gt (2 * (gHi * (|L| + 2 * C)) / (a - gHi))
      filter_upwards [eventually_ge_atTop N] with m hm
      have hpos : 0 < a - gHi := sub_pos.mpr hga
      have hmN : (N : ℝ) ≤ m := by exact_mod_cast hm
      have h := (div_lt_iff₀ hpos).mp (lt_of_lt_of_le hN hmN)
      nlinarith
    have hC' : ∀ᶠ m : ℕ in atTop, C < (m : ℝ) := by
      obtain ⟨N, hN⟩ := exists_nat_gt C
      filter_upwards [eventually_ge_atTop N] with m hm
      exact lt_of_lt_of_le hN (by exact_mod_cast hm)
    filter_upwards [eventually_ge_atTop k₀, hC', hlin, herr.eventually (gt_mem_nhds hη4)]
      with m h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨m, hk₀m, hCm, hlinm, herrm⟩ := hev.exists
  have hmcut : Real.exp (-(m : ℝ)) ≤ ε₀ := by
    have : (k₀ : ℝ) ≤ m := by exact_mod_cast hk₀m
    exact le_trans (Real.exp_le_exp.mpr (by linarith)) hk₀cut
  obtain ⟨R, hR⟩ := finiteBarrierPairKernel_toReal_uniform_cauchy P U dens ε₀ Y hY K hK hKU a
    k₀ m hk₀m hk₀cut hvar s₀ hs₀ (Icc gLo gHi) gHi (hgLo.le.trans hgLoHi)
    (fun g hg => by rw [abs_of_pos (lt_of_lt_of_le hgLo hg.1)]; exact hg.2) (η / 2) (half_pos hη)
  -- the truncation estimate at one cutoff pair
  have htrunc (r s : ℝ) (hmr : (m : ℝ) ≤ r) (hms : (m : ℝ) ≤ s) (g : ℝ) (hg : g ∈ Icc gLo gHi)
      (p : ℂ × ℂ) (hp : p ∈ separatedPairs K s₀) :
      growingPairKernel P Y g a k₀ r s p ≠ ⊤ ∧
      compatibleAdmissibleSelectedFiniteBarrierPairKernel P Y Y g a k₀ m
          (Real.exp (-r)) (Real.exp (-s)) p.1 p.2 true true ≠ ⊤ ∧
      |(compatibleAdmissibleSelectedFiniteBarrierPairKernel P Y Y g a k₀ m
          (Real.exp (-r)) (Real.exp (-s)) p.1 p.2 true true).toReal -
        (growingPairKernel P Y g a k₀ r s p).toReal| < η / 4 := by
    have hgpos : 0 < g := lt_of_lt_of_le hgLo hg.1
    have hga' : g < a := lt_of_le_of_lt hg.2 hga
    obtain ⟨hpos, hLp⟩ := hL p hp
    have hrcut : Real.exp (-r) ≤ ε₀ := le_trans (Real.exp_le_exp.mpr (by linarith)) hmcut
    have hscut : Real.exp (-s) ≤ ε₀ := le_trans (Real.exp_le_exp.mpr (by linarith)) hmcut
    have hfin : compatibleAdmissibleSelectedFiniteBarrierPairKernel P Y Y g a k₀ m
        (Real.exp (-r)) (Real.exp (-s)) p.1 p.2 true true ≠ ⊤ := by
      rw [finiteBarrierPairKernel_eq_rectangle P U dens ε₀ Y hY g a k₀ m hk₀cut _ _
        (Real.exp_pos _) hrcut (Real.exp_pos _) hscut p]
      exact ENNReal.ofReal_ne_top
    have hle := compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel_le_finiteBarrier
      P Y Y g a k₀ m r s p.1 p.2 true true hmr hms
    have hlinG : g * (|L| + 2 * C) ≤ (a - g) * (m : ℝ) / 2 := by
      have hA : 0 ≤ |L| + 2 * C := by positivity
      have h1 : g * (|L| + 2 * C) ≤ gHi * (|L| + 2 * C) := mul_le_mul_of_nonneg_right hg.2 hA
      have h2 : (a - gHi) * (m : ℝ) / 2 ≤ (a - g) * (m : ℝ) / 2 := by
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have := mul_le_mul_of_nonneg_right (show a - gHi ≤ a - g by linarith [hg.2]) hm0
        linarith
      linarith
    have hup := htail k₀ m hCm hmcut r s hmr hms p.1 hp.1.1 p.2 hp.1.2 L hpos hLp g a hgpos
      hga' hlinG
    have hcg : ENNReal.ofReal (Real.exp (g ^ 2 * (L + C))) ≤ cHi := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hg2 : g ^ 2 ≤ gHi ^ 2 := pow_le_pow_left₀ hgpos.le hg.2 2
      have hmax : L + C ≤ max (L + C) 0 := le_max_left _ _
      have hmax0 : 0 ≤ max (L + C) 0 := le_max_right _ _
      calc g ^ 2 * (L + C) ≤ g ^ 2 * max (L + C) 0 :=
            mul_le_mul_of_nonneg_left hmax (sq_nonneg g)
        _ ≤ gHi ^ 2 * max (L + C) 0 := mul_le_mul_of_nonneg_right hg2 hmax0
    have hTg := tsum_barrier_rate_le_of_le g gHi a hg.2 hga (m + 1)
    have herrG : 2 * (ENNReal.ofReal (Real.exp (g ^ 2 * (L + C))) *
        ∑' j : ℕ, ENNReal.ofReal (Real.exp (-((a - g) ^ 2 * ((j + (m + 1) : ℕ) : ℝ) / 16)))) ≤
        2 * (cHi * THi (m + 1)) := by
      gcongr
    have herrfin : 2 * (cHi * THi (m + 1)) ≠ ⊤ := ne_top_of_lt herrm
    have hgtop : growingPairKernel P Y g a k₀ r s p ≠ ⊤ := ne_top_of_le_ne_top hfin hle
    refine ⟨hgtop, hfin, ?_⟩
    have habs := abs_toReal_sub_le_of_le_add hle (hup.trans (add_le_add_right herrG _)) hfin
      herrfin
    refine lt_of_le_of_lt habs ?_
    have := (ENNReal.toReal_lt_toReal herrfin ENNReal.ofReal_ne_top).mpr herrm
    rwa [ENNReal.toReal_ofReal (by linarith)] at this
  refine ⟨max R m, ?_⟩
  intro r s r' s' hr hs hr' hs' g hg p hp
  have hmr : (m : ℝ) ≤ r := le_trans (le_max_right _ _) hr
  have hms : (m : ℝ) ≤ s := le_trans (le_max_right _ _) hs
  have hmr' : (m : ℝ) ≤ r' := le_trans (le_max_right _ _) hr'
  have hms' : (m : ℝ) ≤ s' := le_trans (le_max_right _ _) hs'
  obtain ⟨htop, -, h1⟩ := htrunc r s hmr hms g hg p hp
  obtain ⟨-, -, h2⟩ := htrunc r' s' hmr' hms' g hg p hp
  have h3 := hR r s r' s' (le_trans (le_max_left _ _) hr) (le_trans (le_max_left _ _) hs)
    (le_trans (le_max_left _ _) hr') (le_trans (le_max_left _ _) hs') g hg p hp
  refine ⟨htop, ?_⟩
  set A := (growingPairKernel P Y g a k₀ r s p).toReal
  set A' := (growingPairKernel P Y g a k₀ r' s' p).toReal
  set F := (compatibleAdmissibleSelectedFiniteBarrierPairKernel P Y Y g a k₀ m
    (Real.exp (-r)) (Real.exp (-s)) p.1 p.2 true true).toReal
  set F' := (compatibleAdmissibleSelectedFiniteBarrierPairKernel P Y Y g a k₀ m
    (Real.exp (-r')) (Real.exp (-s')) p.1 p.2 true true).toReal
  calc |A - A'| = |(F - A') - (F - A)| := by ring_nf
    _ ≤ |F - A'| + |F - A| := abs_sub _ _
    _ ≤ (|F - F'| + |F' - A'|) + |F - A| := by
        gcongr
        exact abs_sub_le _ _ _
    _ < (η / 2 + η / 4) + η / 4 := by gcongr
    _ = η := by ring

end DOZZ.Assembly
