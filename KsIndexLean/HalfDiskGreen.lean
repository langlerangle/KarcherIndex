module

public import KsIndexLean.HalfDiskBoundaryFlux
public import KsIndexLean.MixedHalfDiskGreen

@[expose] public section


/-! The truncated Green identity for bounded classical half-period fields.
Only one-sided boundary germs are used; finite energy is not an input. -/
noncomputable section
open Set MeasureTheory Filter Topology Complex
namespace KsIndex.Trace.ClassicalHalfDiskJacobi
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.PunctureCutoff KsIndex.FaithfulInjection
variable {k : ℕ} {b : Bool} (u : ClassicalHalfDiskJacobi k b)

/-- The cross term is integrable for each positive puncture cutoff. -/
lemma cutoff_cross_integrable (hk : 2 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    IntegrableOn (crossDens k ε u.value) disk := by
  exact (ClassicalMixedHalfDiskJacobi.ofPure u).cutoff_cross_integrable hk h0 h1

/-- The potential term is integrable independently of the derivative energy. -/
lemma cutoff_potential_integrable (hk : 2 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    IntegrableOn (fun w => potV k w * (cutP k ε w)^(2 : ℕ) * ‖u.value w‖^(2 : ℕ)) disk := by
  exact (ClassicalMixedHalfDiskJacobi.ofPure u).cutoff_potential_integrable hk h0 h1

/-- Green's formula tested against the squared puncture cutoff times the field.
The Dirichlet or Neumann condition cancels the entire circle flux. -/
theorem cutoff_green_identity (hk : 2 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    ((∫ w in disk, (cutP k ε w)^(2 : ℕ) * gradSq u.value w : ℝ) : ℂ) =
      -(∫ w in disk, crossDens k ε u.value w) +
      ((∫ w in disk, potV k w * (cutP k ε w)^(2 : ℕ) * ‖u.value w‖^(2 : ℕ) : ℝ) : ℂ) := by
  exact (ClassicalMixedHalfDiskJacobi.ofPure u).cutoff_green_identity hk h0 h1

end KsIndex.Trace.ClassicalHalfDiskJacobi
