module

public import KsIndexLean.SphericalChartTransition
public import KsIndexLean.SlitPlanarDomain

@[expose] public section


open Set Metric TopologicalSpace

noncomputable section
namespace KsIndex.Spherical

/-- The closed equatorial slits, in the actual sphere and the paper's coordinate. -/
def sphericalSlit (k : ℕ) : Set Sphere := sphereChart '' KsIndex.Bracket.slit k

lemma isClosed_sphericalSlit (k : ℕ) : IsClosed (sphericalSlit k) := by
  have hc : IsCompact (KsIndex.Bracket.slit k) :=
    (isCompact_sphere (0 : ℂ) 1).of_isClosed_subset
      (KsIndex.Trace.isClosed_planarSlit k) (fun z hz => mem_sphere_zero_iff_norm.mpr hz.1)
  exact (hc.image continuous_sphereChart).isClosed

def slitSphere (k : ℕ) : Opens Sphere :=
  ⟨(sphericalSlit k)ᶜ, (isClosed_sphericalSlit k).isOpen_compl⟩

lemma sphereChart_mem_sphericalSlit (k : ℕ) (z : ℂ) :
    sphereChart z ∈ sphericalSlit k ↔ z ∈ KsIndex.Bracket.slit k := by
  constructor
  · rintro ⟨w, hw, he⟩
    exact sphereChart_injective he ▸ hw
  · intro h
    exact ⟨z, h, rfl⟩

lemma reflectSphere_eq_of_equator (p : Sphere) (hp : p.val 2 = 0) : reflectSphere p = p := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [reflectSphere, reflectAmbient, hp]

lemma reflectSphere_fixes_slit (k : ℕ) {p : Sphere} (hp : p ∈ sphericalSlit k) :
    reflectSphere p = p := by
  obtain ⟨z, hz, rfl⟩ := hp
  apply reflectSphere_eq_of_equator
  exact (stereoPoint_equator_iff z).mpr hz.1

lemma reflectSphere_mem_sphericalSlit (k : ℕ) (p : Sphere) :
    reflectSphere p ∈ sphericalSlit k ↔ p ∈ sphericalSlit k := by
  constructor
  · intro h
    have he := reflectSphere_fixes_slit k h
    rw [reflectSphere_involutive] at he
    exact he ▸ h
  · intro h
    rw [reflectSphere_fixes_slit k h]
    exact h

lemma sphereChart_mem_slitSphere (k : ℕ) (z : ℂ) :
    sphereChart z ∈ slitSphere k ↔ z ∉ KsIndex.Bracket.slit k := by
  change (sphereChart z ∉ sphericalSlit k) ↔ _
  rw [sphereChart_mem_sphericalSlit]

lemma southChart_mem_slitSphere (k : ℕ) (z : ℂ) :
    southChart z ∈ slitSphere k ↔ z ∉ KsIndex.Bracket.slit k := by
  change (reflectSphere (sphereChart z) ∉ sphericalSlit k) ↔ _
  rw [reflectSphere_mem_sphericalSlit, sphereChart_mem_sphericalSlit]

end KsIndex.Spherical
