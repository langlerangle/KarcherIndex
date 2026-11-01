module

/-
KsIndexLean — NullityNonresonant: Theorem A′'s non-resonant branch, k = 3.

For every nonzero natural period `m`, `nulSurface 3 m = 3` provided
`m * alphaStar` is not an integer. The proof supplies the zero-phase nullity
bound from `paperSlit_zeroPhase_nullity` to the fiber bound in `FiberEmbed`.

Non-resonance is an explicit hypothesis. The result does not require or establish
irrationality of `alphaStar`, and makes no conclusion for resonant periods.
-/
public import KsIndexLean.FiberEmbed
public import KsIndexLean.ZeroPhaseNullity

@[expose] public section


noncomputable section
namespace KsIndex.NullityDecomp
open KsIndex.Surface KsIndex.SurfaceSym KsIndex.FormIndex KsIndex.WeakH1
  KsIndex.FaithfulInjection KsIndex.Trace

/-- **Theorem A′, non-resonant branch (k = 3, every nonzero natural m)**: if `m·α*` is not
an integer then `nul(Ξ_{3,m}) = 3`. -/
theorem nulSurface_eq_three_offResonance {m : ℕ} [NeZero m]
    (hmα : ∀ n : ℤ, (m : ℝ) * KsIndex.Staircase.alphaStar ≠ (n : ℝ)) :
    nulSurface 3 m = 3 :=
  nulSurface_eq_three_of_mAlphaStar_not_int_of_zeroPhase
    (fun r => (KsIndex.Spectral.paperSlit_zeroPhase_nullity r.isLt).le) hmα

end KsIndex.NullityDecomp
