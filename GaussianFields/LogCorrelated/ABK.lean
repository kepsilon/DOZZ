/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.ScaleSpace
public import GaussianFields.LogCorrelated.ABK.Convolution
public import GaussianFields.LogCorrelated.ABK.ConvolutionBounds
public import GaussianFields.LogCorrelated.ABK.Kernel
public import GaussianFields.LogCorrelated.ABK.CanonicalField
public import GaussianFields.LogCorrelated.ABK.Annular
public import GaussianFields.LogCorrelated.ABK.Triadic

/-!
# ABK Physical-Space Log-Correlated Gaussian Field

This file starts the construction from Appendix `s.LGF` of ABK24.  The driving white noise is the
already-constructed scalar white noise on the scale-space `R^{1+d}`.  Product coordinates
`(r, y) ∈ R × R^d` are exposed through a measure-preserving equivalence with `Vec (d + 1)`, so
white-noise evaluation remains the concrete Haar/isonormal construction from
`GaussianFields.WhiteNoise.Isonormal`.

The ABK test kernel is
`(r, y) ↦ c r^{- (d+1)/2} (ζ_r * ψ)(y)` on `r > 0`, extended by zero to all of scale-space.
-/

public section

end
