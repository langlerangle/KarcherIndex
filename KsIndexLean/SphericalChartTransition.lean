module

public import KsIndexLean.SphericalInversion
public import KsIndexLean.Bracket

@[expose] public section


noncomputable section
namespace KsIndex.Spherical

/-- The geometric transition is the exact inversion used by the weak gluing development. -/
lemma southChart_eq_sigma {z : ℂ} (hz : z ≠ 0) :
    southChart z = sphereChart (KsIndex.Bracket.σ z) := by
  simpa only [KsIndex.Bracket.σ, one_div] using southChart_inverse_conj hz

lemma stereoCoord_southChart {z : ℂ} (hz : z ≠ 0) :
    stereoCoord (southChart z : Ambient) = KsIndex.Bracket.σ z := by
  rw [southChart_eq_sigma hz]
  exact stereoCoord_stereoPoint _

end KsIndex.Spherical
