module

public import KsIndexLean.MixedHalfDiskWeakTests
public import KsIndexLean.HemisphereMixedPunctureRemoval

@[expose] public section


/-! Bounded mixed classical disk fields define weak Jacobi fields on the
actual lower hemisphere, with its canonical spherical-area integral. -/
noncomputable section
namespace KsIndex.Trace.ClassicalMixedHalfDiskJacobi
open KsIndex.Spherical KsIndex.WeakH1
variable {k : ℕ} {b1 b0 : Bool} (u : ClassicalMixedHalfDiskJacobi k b1 b0)

/-- The actual hemisphere weak field associated with classical disk data. -/
def toHemisphere (hk : 2 ≤ k) : HemisphereChartSpace :=
  hemisphereCoordinates.symm (u.toH1 hk)

@[simp] lemma toHemisphere_coordinates (hk : 2 ≤ k) :
    hemisphereCoordinates (u.toHemisphere hk) = u.toH1 hk :=
  hemisphereCoordinates.apply_symm_apply _

lemma toHemisphere_mem_character (hk : 2 ≤ k) (j : ℕ)
    (hc : ∀ w ∈ Surface.disk,
      u.value (planeRotation (-(2 * Real.pi) / k) w) = FormIndex.zeta k ^ j * u.value w) :
    u.toHemisphere hk ∈ hemisphereMixedCharacterDomain k j b1 b0 := by
  change hemisphereCoordinates (u.toHemisphere hk) ∈ mixedCharacterDomain k j b1 b0
  rw [u.toHemisphere_coordinates hk]
  exact u.toH1_mem_mixedCharacter hk j hc

/-- The equation holds against every admissible weak spherical test, not
only those with a chosen smooth representative or vanishing puncture germ. -/
theorem toHemisphere_tests_zero (hk : 2 ≤ k) (j : ℕ)
    (v : hemisphereMixedCharacterDomain k j b1 b0) :
    hemisphereJacobi (surfacePotential k) (u.toHemisphere hk) v.val = 0 := by
  rw [hemisphereJacobi_eq, u.toHemisphere_coordinates hk]
  exact u.character_tests_zero hk j ⟨hemisphereCoordinates v.val, v.property⟩

end KsIndex.Trace.ClassicalMixedHalfDiskJacobi
