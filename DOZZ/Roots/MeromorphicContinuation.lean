/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Topology.Instances.Complex
/-! # Continuing a local charge identity along a connected complex neighborhood -/
public section
open Filter Topology Set
namespace DOZZ.Proofs
/-- A local equality of meromorphic functions continues to every regular point of a connected domain. -/
theorem roots_eq_of_meromorphic_continuation (V : Set ℂ) (hV : IsPreconnected V)
    (f g : ℂ → ℂ) (hf : MeromorphicOn f V) (hg : MeromorphicOn g V)
    (a b : ℂ) (ha : a ∈ V) (hb : b ∈ V) (he : f =ᶠ[nhds a] g)
    (hfc : ContinuousAt f b) (hgc : ContinuousAt g b) : f b = g b := by
  have hfg : MeromorphicOn (fun z => f z - g z) V := hf.sub hg
  have hzero : ∀ᶠ z in nhdsWithin a {a}ᶜ, f z - g z = 0 :=
    (he.filter_mono nhdsWithin_le_nhds).mono fun z hz => sub_eq_zero.mpr hz
  have horder := meromorphicOrderAt_eq_top_iff.mpr hzero
  have horderb := hfg.meromorphicOrderAt_eq_top_of_isPreconnected hV ha hb horder
  have hzerob := meromorphicOrderAt_eq_top_iff.mp horderb
  have heqb : (fun z => f z - g z) =ᶠ[nhdsWithin b {b}ᶜ] (fun _ => (0 : ℂ)) := hzerob
  have hlim : Tendsto (fun z => f z - g z) (nhdsWithin b {b}ᶜ) (nhds 0) :=
    tendsto_const_nhds.congr' heqb.symm
  exact sub_eq_zero.mp (tendsto_nhds_unique
    ((hfc.sub hgc).tendsto.mono_left nhdsWithin_le_nhds) hlim)
end DOZZ.Proofs
