/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# Identity from real boxes

Scalar identity on each coordinate enlarges a real box to a complex
polydisc. Scalar identity on complex lines then propagates neighborhood
equality across an open preconnected domain. This argument does not assume
a several-variable power series theorem.
-/

@[expose] public section

open Filter Topology Set

namespace DOZZ.Proofs

/-- Equal values on a real interval accumulate at its real center. -/
theorem frequently_eq_of_real_interval (a R : ℝ) (hR : 0 < R) (f g : ℂ → ℂ)
    (heq : ∀ x : ℝ, |x - a| < R → f (x : ℂ) = g (x : ℂ)) :
    ∃ᶠ z in 𝓝[≠] (a : ℂ), f z = g z := by
  rw [Filter.frequently_iff]
  intro V hV
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hV
  let δ := min ε R / 2
  have hδ : 0 < δ := half_pos (lt_min hε hR)
  have hδε : δ < ε := (half_lt_self (lt_min hε hR)).trans_le (min_le_left _ _)
  have hδR : δ < R := (half_lt_self (lt_min hε hR)).trans_le (min_le_right _ _)
  refine ⟨((a + δ : ℝ) : ℂ), hball ⟨?_, ?_⟩, heq (a + δ) ?_⟩
  · simpa only [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub,
      add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ] using hδε
  · simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_inj, add_eq_left]
    exact hδ.ne'
  · simpa only [add_sub_cancel_left, abs_of_pos hδ] using hδR

/-- Scalar holomorphic identity from the real diameter of a disk. -/
theorem eqOn_ball_of_real_interval (a R : ℝ) (hR : 0 < R) (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (Metric.ball (a : ℂ) R))
    (hg : DifferentiableOn ℂ g (Metric.ball (a : ℂ) R))
    (heq : ∀ x : ℝ, |x - a| < R → f (x : ℂ) = g (x : ℂ)) :
    EqOn f g (Metric.ball (a : ℂ) R) :=
  (hf.analyticOnNhd Metric.isOpen_ball).eqOn_of_preconnected_of_frequently_eq
    (hg.analyticOnNhd Metric.isOpen_ball) (convex_ball _ _).isPreconnected
    (Metric.mem_ball_self hR) (frequently_eq_of_real_interval a R hR f g heq)

/-- A complex line parameterization is a real affine map as well. -/
noncomputable def complexLineAffine {N : ℕ} (a b : Fin N → ℂ) : ℂ →ᵃ[ℝ] (Fin N → ℂ) :=
  ((ContinuousLinearMap.toSpanSingleton ℂ (b - a)).restrictScalars ℝ).toLinearMap.toAffineMap +
    AffineMap.const ℝ ℂ a

/-- The affine map has the expected complex-line formula. -/
@[simp] theorem complexLineAffine_apply {N : ℕ} (a b : Fin N → ℂ) (t : ℂ) :
    complexLineAffine a b t = a + t • (b - a) := by
  simp [complexLineAffine, add_comm]



/-- Complex-line restriction is differentiable in its scalar complex parameter.

Although the affine structure used for convexity is real, the same formula
is complex differentiable. The two scalar roles are kept explicit here.
-/
theorem differentiable_complexLineAffine {N : ℕ} (a b : Fin N → ℂ) :
    Differentiable ℂ (complexLineAffine a b) := by
  have heq : (complexLineAffine a b : ℂ → (Fin N → ℂ)) =
      fun t => a + t • (b - a) := by
    funext t
    exact complexLineAffine_apply a b t
  rw [heq]
  exact (differentiable_const a).add (differentiable_id.smul_const (b - a))

/-- Neighborhood equality propagates throughout a complex ball by scalar lines. -/
theorem eqOn_ball_of_eventuallyEq {N : ℕ} (a : Fin N → ℂ) (R : ℝ)
    (f g : (Fin N → ℂ) → ℂ)
    (hf : DifferentiableOn ℂ f (Metric.ball a R))
    (hg : DifferentiableOn ℂ g (Metric.ball a R))
    (b : Fin N → ℂ) (hb : b ∈ Metric.ball a R) (heq : f =ᶠ[𝓝 b] g) :
    EqOn f g (Metric.ball a R) := by
  intro z hz
  let L : ℂ → (Fin N → ℂ) := fun t => b + t • (z - b)
  let V := L ⁻¹' Metric.ball a R
  have hL : Differentiable ℂ L := by
    have heq : L = (complexLineAffine b z : ℂ → (Fin N → ℂ)) := by
      funext t
      exact (complexLineAffine_apply b z t).symm
    rw [heq]
    exact differentiable_complexLineAffine b z
  have hV : IsOpen V := Metric.isOpen_ball.preimage hL.continuous
  have hconv : Convex ℝ V := by
    have hVeq : V = complexLineAffine b z ⁻¹' Metric.ball a R := by
      ext t
      simp [V, L]
    rw [hVeq]
    exact (convex_ball a R).affine_preimage (complexLineAffine b z)
  have hzero : (0 : ℂ) ∈ V := by simpa [V, L] using hb
  have hone : (1 : ℂ) ∈ V := by simpa [V, L] using hz
  have hfl : DifferentiableOn ℂ (f ∘ L) V :=
    hf.comp hL.differentiableOn (fun _ ht => ht)
  have hgl : DifferentiableOn ℂ (g ∘ L) V :=
    hg.comp hL.differentiableOn (fun _ ht => ht)
  have hfg : f ∘ L =ᶠ[𝓝 (0 : ℂ)] g ∘ L := by
    apply heq.comp_tendsto
    simpa [L] using hL.continuous.continuousAt.tendsto (x := (0 : ℂ))
  have hid := (hfl.analyticOnNhd hV).eqOn_of_preconnected_of_eventuallyEq
    (hgl.analyticOnNhd hV) hconv.isPreconnected hzero hfg hone
  simpa [Function.comp_def, L] using hid

/-- Scalar-line propagation gives identity on any open preconnected domain. -/
theorem eqOn_of_preconnected_of_eventuallyEq {N : ℕ} (U : Set (Fin N → ℂ))
    (hU : IsOpen U) (hconn : IsPreconnected U) (f g : (Fin N → ℂ) → ℂ)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (a : Fin N → ℂ) (ha : a ∈ U) (heq : f =ᶠ[𝓝 a] g) : EqOn f g U := by
  let Z := {z | f =ᶠ[𝓝 z] g}
  have hZ : IsOpen Z := isOpen_setOfPred_eventually_nhds
  have hseed : (U ∩ Z).Nonempty := ⟨a, ha, heq⟩
  have hclosed : closure Z ∩ U ⊆ Z := by
    intro z hz
    obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz.2)
    obtain ⟨b, hbZ, hbdist⟩ := Metric.mem_closure_iff.mp hz.1 R hR
    have hb : b ∈ Metric.ball z R := by
      simpa only [Metric.mem_ball, dist_comm] using hbdist
    have hid := eqOn_ball_of_eventuallyEq z R f g (hf.mono hRU) (hg.mono hRU) b hb hbZ
    exact Filter.eventually_of_mem (Metric.ball_mem_nhds z hR) fun w hw => hid hw
  have hsubset := hconn.subset_of_closure_inter_subset hZ hseed hclosed
  intro z hz
  exact (hsubset hz).eq_of_nhds

/-- Coordinates in `S` are complex; the other coordinates stay real. -/
def mixedCoordinates {N : ℕ} (S : Finset (Fin N)) (z : Fin N → ℂ) (x : Fin N → ℝ) :
    Fin N → ℂ := fun i => if i ∈ S then z i else (x i : ℂ)

/-- Before an index has been complexified, a real update commutes with mixing. -/
theorem mixedCoordinates_update {N : ℕ} (S : Finset (Fin N)) (z : Fin N → ℂ)
    (x : Fin N → ℝ) (i : Fin N) (hi : i ∉ S) (w : ℝ) :
    mixedCoordinates S z (Function.update x i w) =
      Function.update (mixedCoordinates S z x) i (w : ℂ) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [mixedCoordinates, hi]
  · simp [mixedCoordinates, hj]

/-- Complexifying an additional index is a complex update. -/
theorem mixedCoordinates_insert {N : ℕ} (S : Finset (Fin N)) (z : Fin N → ℂ)
    (x : Fin N → ℝ) (i : Fin N) :
    mixedCoordinates (insert i S) z x = Function.update (mixedCoordinates S z x) i (z i) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [mixedCoordinates]
  · simp [mixedCoordinates, hj]

/-- A mixture of points in a centered real box and its complex polydisc stays inside. -/
theorem mixedCoordinates_mem_polydisc {N : ℕ} (S : Finset (Fin N))
    (a : Fin N → ℝ) (R : Fin N → ℝ) (z : Fin N → ℂ)
    (hz : z ∈ complexPolydisc (fun i => (a i : ℂ)) R) (x : Fin N → ℝ)
    (hx : ∀ i, |x i - a i| < R i) :
    mixedCoordinates S z x ∈ complexPolydisc (fun i => (a i : ℂ)) R := by
  intro i
  by_cases hi : i ∈ S
  · simpa [mixedCoordinates, hi] using hz i
  · simpa [mixedCoordinates, hi, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] using hx i

/-- A coordinate update stays in the polydisc when its value stays in the coordinate disk. -/
theorem update_mem_polydisc {N : ℕ} (a : Fin N → ℂ) (R : Fin N → ℝ)
    (z : Fin N → ℂ) (hz : z ∈ complexPolydisc a R) (i : Fin N) (w : ℂ)
    (hw : w ∈ Metric.ball (a i) (R i)) : Function.update z i w ∈ complexPolydisc a R := by
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [Function.update_self, Metric.mem_ball, dist_eq_norm] using hw
  · simpa only [Function.update_of_ne hj] using hz j

/-- Scalar identity, one coordinate at a time, fills a real-centered polydisc.

The induction is over a finite set of already complexified coordinates. At
its empty stage the hypothesis supplies equality. At an insertion stage,
the old equality gives equality on the real diameter of the new coordinate
disk; scalar identity gives equality on the whole disk. The final stage is
all coordinates, including the empty family in dimension zero.
-/
theorem eqOn_polydisc_of_real_box {N : ℕ} (a : Fin N → ℝ) (R : Fin N → ℝ)
    (hR : ∀ i, 0 < R i) (f g : (Fin N → ℂ) → ℂ)
    (hf : DifferentiableOn ℂ f (complexPolydisc (fun i => (a i : ℂ)) R))
    (hg : DifferentiableOn ℂ g (complexPolydisc (fun i => (a i : ℂ)) R))
    (heq : ∀ x : Fin N → ℝ, (∀ i, |x i - a i| < R i) →
      f (fun i => (x i : ℂ)) = g (fun i => (x i : ℂ))) :
    EqOn f g (complexPolydisc (fun i => (a i : ℂ)) R) := by
  classical
  intro z hz
  have hmix : ∀ S : Finset (Fin N), ∀ x : Fin N → ℝ,
      (∀ i, |x i - a i| < R i) →
      f (mixedCoordinates S z x) = g (mixedCoordinates S z x) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        intro x hx
        have hempty : mixedCoordinates ∅ z x = fun i => (x i : ℂ) := by
          funext i
          simp only [mixedCoordinates, Finset.notMem_empty, ite_false]
        rw [hempty]
        exact heq x hx
    | @insert i S hi hS =>
        intro x hx
        let y := mixedCoordinates S z x
        have hy := mixedCoordinates_mem_polydisc S a R z hz x hx
        have hmap : MapsTo (Function.update y i) (Metric.ball (a i : ℂ) (R i))
            (complexPolydisc (fun j => (a j : ℂ)) R) :=
          fun w hw => update_mem_polydisc _ R y hy i w hw
        have hupdate : DifferentiableOn ℂ (Function.update y i)
            (Metric.ball (a i : ℂ) (R i)) :=
          fun w _ => (hasFDerivAt_update y w).differentiableAt.differentiableWithinAt
        have hfl := hf.comp hupdate hmap
        have hgl := hg.comp hupdate hmap
        have hreal : ∀ w : ℝ, |w - a i| < R i →
            f (Function.update y i (w : ℂ)) = g (Function.update y i (w : ℂ)) := by
          intro w hw
          have hx' : ∀ j, |Function.update x i w j - a j| < R j := by
            intro j
            by_cases hj : j = i
            · subst j
              simpa only [Function.update_self] using hw
            · simpa only [Function.update_of_ne hj] using hx j
          have hid := hS (Function.update x i w) hx'
          rw [mixedCoordinates_update S z x i hi w] at hid
          exact hid
        have hid := eqOn_ball_of_real_interval (a i) (R i) (hR i)
          (f ∘ Function.update y i) (g ∘ Function.update y i) hfl hgl hreal
          (show z i ∈ Metric.ball (a i : ℂ) (R i) by
            simpa only [Metric.mem_ball, dist_eq_norm] using hz i)
        rw [mixedCoordinates_insert]
        exact hid
  have hcenter : ∀ i, |a i - a i| < R i := by simpa using hR
  have hall : mixedCoordinates Finset.univ z a = z := by
    funext i
    simp only [mixedCoordinates, Finset.mem_univ, ite_true]
  simpa only [hall] using hmix Finset.univ a hcenter

/-- Coordinate radii below a positive number place the polydisc in its norm ball.

The positivity condition on the ball radius handles the empty coordinate
family: its norm is zero and the polydisc is the whole singleton space.
-/
theorem complexPolydisc_subset_ball {N : ℕ} (a : Fin N → ℂ) (R : Fin N → ℝ)
    (ε : ℝ) (hε : 0 < ε) (hR : ∀ i, R i ≤ ε) :
    complexPolydisc a R ⊆ Metric.ball a ε := by
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hε]
  exact fun i => (hz i).trans_le (hR i)


/-- The open polydisc is contained in the product of its closed coordinate disks. -/
theorem complexPolydisc_subset_closed_pi {N : ℕ} (a : Fin N → ℂ) (R : Fin N → ℝ) :
    complexPolydisc a R ⊆ Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)) := by
  intro z hz i _
  simpa only [Metric.mem_closedBall, dist_eq_norm] using (hz i).le

/-- Closed coordinate disks with strictly smaller radii fit in a norm ball. -/
theorem closed_pi_subset_ball {N : ℕ} (a : Fin N → ℂ) (R : Fin N → ℝ)
    (ε : ℝ) (hε : 0 < ε) (hR : ∀ i, R i < ε) :
    Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)) ⊆ Metric.ball a ε := by
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hε]
  intro i
  have hi := hz i (mem_univ i)
  have hnorm : ‖z i - a i‖ ≤ R i := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hi
  exact hnorm.trans_lt (hR i)

/-- The product of closed coordinate disks is compact in the finite product topology. -/
theorem isCompact_closed_pi {N : ℕ} (a : Fin N → ℂ) (R : Fin N → ℝ) :
    IsCompact (Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i))) :=
  isCompact_univ_pi fun i => isCompact_closedBall (a i) (R i)


/-- An open neighborhood contains a compact closed polydisc and its open interior.

The closed contour must lie in the domain before applying Cauchy integration.
The half-radius choice retains a strict margin at every coordinate. It also
avoids choosing a minimum over coordinates, so it applies in dimension zero.
-/
theorem exists_closed_polydisc_subset_open {N : ℕ} (U : Set (Fin N → ℂ))
    (hU : IsOpen U) (a : Fin N → ℂ) (ha : a ∈ U) :
    ∃ R : Fin N → ℝ, (∀ i, 0 < R i) ∧
      Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)) ⊆ U ∧
      complexPolydisc a R ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  let R : Fin N → ℝ := fun _ => ε / 2
  have hR : ∀ i, 0 < R i := fun _ => half_pos hε
  have hclosed : Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)) ⊆ U :=
    (closed_pi_subset_ball a R ε hε (fun _ => half_lt_self hε)).trans hball
  exact ⟨R, hR, hclosed, (complexPolydisc_subset_closed_pi a R).trans hclosed⟩

/-- An open neighborhood contains a polydisc with prescribed upper bounds on radii.

Choosing the radii coordinatewise avoids a minimum over an empty index type.
This is useful both for real-box identity and for nested Cauchy polydiscs.
-/
theorem exists_small_polydisc {N : ℕ} (U : Set (Fin N → ℂ)) (hU : IsOpen U)
    (a : Fin N → ℂ) (ha : a ∈ U) (r : Fin N → ℝ) (hr : ∀ i, 0 < r i) :
    ∃ R : Fin N → ℝ, (∀ i, 0 < R i) ∧ (∀ i, R i ≤ r i) ∧
      complexPolydisc a R ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  let R := fun i => min ε (r i)
  refine ⟨R, fun i => lt_min hε (hr i), fun i => min_le_right _ _, ?_⟩
  exact (complexPolydisc_subset_ball a R ε hε (fun i => min_le_left _ _)).trans hball

/-- The coordinatewise midpoint is strictly inside a nonempty real box. -/
theorem midpoint_mem_real_box {N : ℕ} (lo hi : Fin N → ℝ) (hbox : ∀ i, lo i < hi i) :
    ∀ i, lo i < (lo i + hi i) / 2 ∧ (lo i + hi i) / 2 < hi i := by
  intro i
  have h := hbox i
  constructor <;> linarith

/-- A positive centered radius bounded by both interval margins stays in the real interval. -/
theorem mem_real_interval_of_abs_sub_lt {a lo hi R x : ℝ}
    (hlo : R ≤ a - lo) (hhi : R ≤ hi - a) (hx : |x - a| < R) :
    lo < x ∧ x < hi := by
  have hb := abs_lt.mp hx
  constructor <;> linarith

/-- Around an interior real point, the containing complex domain and real box
admit a common positive polydisc. This supplies an actual complex neighborhood
rather than treating the real box itself as open in the complex space. -/
theorem exists_polydisc_inside_real_box {N : ℕ} (U : Set (Fin N → ℂ))
    (hU : IsOpen U) (a : Fin N → ℝ) (ha : (fun i => (a i : ℂ)) ∈ U)
    (lo hi : Fin N → ℝ) (hlo : ∀ i, lo i < a i) (hhi : ∀ i, a i < hi i) :
    ∃ R : Fin N → ℝ, (∀ i, 0 < R i) ∧
      complexPolydisc (fun i => (a i : ℂ)) R ⊆ U ∧
      (∀ x : Fin N → ℝ, (∀ i, |x i - a i| < R i) →
        ∀ i, lo i < x i ∧ x i < hi i) := by
  let r := fun i => min (a i - lo i) (hi i - a i)
  have hr : ∀ i, 0 < r i := fun i => lt_min (sub_pos.mpr (hlo i)) (sub_pos.mpr (hhi i))
  obtain ⟨R, hR, hRr, hRU⟩ := exists_small_polydisc U hU (fun i => (a i : ℂ)) ha r hr
  refine ⟨R, hR, hRU, ?_⟩
  intro x hx i
  exact mem_real_interval_of_abs_sub_lt
    ((hRr i).trans (min_le_left _ _)) ((hRr i).trans (min_le_right _ _)) (hx i)

/-- Equality on a real-centered polydisc gives an actual neighborhood of equality. -/
theorem eventuallyEq_of_real_box_polydisc {N : ℕ} (a : Fin N → ℝ) (R : Fin N → ℝ)
    (hR : ∀ i, 0 < R i) (f g : (Fin N → ℂ) → ℂ)
    (hf : DifferentiableOn ℂ f (complexPolydisc (fun i => (a i : ℂ)) R))
    (hg : DifferentiableOn ℂ g (complexPolydisc (fun i => (a i : ℂ)) R))
    (heq : ∀ x : Fin N → ℝ, (∀ i, |x i - a i| < R i) →
      f (fun i => (x i : ℂ)) = g (fun i => (x i : ℂ))) :
    f =ᶠ[𝓝 (fun i => (a i : ℂ))] g := by
  have hid := eqOn_polydisc_of_real_box a R hR f g hf hg heq
  exact Filter.eventually_of_mem
    ((isOpen_complexPolydisc _ R).mem_nhds (mem_complexPolydisc_center _ R hR))
    fun z hz => hid hz

/-- Proof of `DOZZ.eqOn_of_real_open_box`: the identity theorem from a real open box, including
dimension zero. -/
theorem eqOn_of_real_open_box {N : ℕ} (U : Set (Fin N → ℂ))
    (hU : IsOpen U) (hconn : IsPreconnected U) (f g : (Fin N → ℂ) → ℂ)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (lo hi : Fin N → ℝ) (hbox : ∀ i, lo i < hi i)
    (hinside : ∀ x : Fin N → ℝ, (∀ i, lo i < x i ∧ x i < hi i) →
      (fun i => (x i : ℂ)) ∈ U)
    (heq : ∀ x : Fin N → ℝ, (∀ i, lo i < x i ∧ x i < hi i) →
      f (fun i => (x i : ℂ)) = g (fun i => (x i : ℂ))) : EqOn f g U := by
  let a := fun i => (lo i + hi i) / 2
  have ha := midpoint_mem_real_box lo hi hbox
  have hain : (fun i => (a i : ℂ)) ∈ U := hinside a ha
  obtain ⟨R, hR, hRU, hreal⟩ := exists_polydisc_inside_real_box U hU a hain lo hi
    (fun i => (ha i).1) (fun i => (ha i).2)
  have hlocal := eventuallyEq_of_real_box_polydisc a R hR f g (hf.mono hRU) (hg.mono hRU)
    (fun x hx => heq x (hreal x hx))
  exact eqOn_of_preconnected_of_eventuallyEq U hU hconn f g hf hg _ hain hlocal

end DOZZ.Proofs
