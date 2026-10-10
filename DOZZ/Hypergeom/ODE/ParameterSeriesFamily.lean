/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ParameterSeriesDerivativeBounds

/-! Parameter regularity of every characterized family on the ordinary-series disk. -/

@[expose] public section

open Filter
open scoped Topology

namespace DOZZ.Proofs

/-- On the open unit disk, every admissible family agrees locally in its parameters with the
ordinary Gauss series. This gives the parameter-holomorphic germ that continuation must propagate
to the full slit plane. -/
theorem IsGaussHypergeometricFamily.differentiableOn_params_unitDisk
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) {z : ℂ} (hz : ‖z‖ < 1) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => H p.1 p.2.1 p.2.2 z)
      gaussParameterPoleFreeDomain := by
  intro p hp
  have hseries := ordinaryHypergeometric_differentiableAt_params p z hp hz
  have hlocal : (fun q : ℂ × ℂ × ℂ => H q.1 q.2.1 q.2.2 z) =ᶠ[𝓝 p]
      (fun q => ordinaryHypergeometric q.1 q.2.1 q.2.2 z) := by
    filter_upwards [gaussParameterPoleFreeDomain_isOpen.mem_nhds hp] with q hq
    exact (hH q.1 q.2.1 q.2.2 hq).2 z hz
  exact (hseries.congr_of_eventuallyEq hlocal).differentiableWithinAt

end DOZZ.Proofs
