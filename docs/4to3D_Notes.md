BesselFUnction.lean > line 22 has a 1/2 error:
* `besselK_properTime` - Alternative proper-time representation:
    K₁(z) = (z/2) ∫₀^∞ t^{-2} exp(-t - z²/(4t)) dt
should be 
* `besselK_properTime` - Alternative proper-time representation:
    K₁(z) = (z/4) ∫₀^∞ t^{-2} exp(-t - z²/(4t)) dt

This function besselK_properTime is not defined in this file, nor the relevant declared theorems are used.