module

public import KsIndexLean.SphericalSlitDomain
public import KsIndexLean.ExtendedSeamChart

@[expose] public section


open Set Metric

noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace

lemma unmatched_boundary_eq_planarSlit (k : ℕ) :
    Subtype.val '' (boundaryArc k 1)ᶜ = KsIndex.Bracket.slit k := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨mem_sphere_zero_iff_norm.mp w.property, ?_⟩
    have h : ¬ (-(w.val ^ k).re < 0) := by
      simpa only [mem_compl_iff, mem_boundaryArc, pow_one, neg_one_mul] using hw
    linarith
  · rintro ⟨hn, hr⟩
    let w : Circle₁ := ⟨z, mem_sphere_zero_iff_norm.mpr hn⟩
    refine ⟨w, ?_, rfl⟩
    change w ∉ boundaryArc k 1
    simp only [mem_boundaryArc, pow_one, neg_one_mul]
    change ¬ -(z ^ k).re < 0
    linarith

/-- The actual weak-gluing domain is precisely the radius-two spherical slit chart. -/
lemma extendedSeamDomain_eq_slit_chart (k : ℕ) :
    (extendedSeamDomain (boundaryArc k 1) (isOpen_boundaryArc k 1) : Set ℂ) =
      Metric.ball 0 2 ∩ sphereChart ⁻¹' (slitSphere k : Set Sphere) := by
  ext z
  change (z ∈ Metric.ball 0 2 ∧ z ∉ Subtype.val '' (boundaryArc k 1)ᶜ) ↔ _
  rw [unmatched_boundary_eq_planarSlit]
  exact and_congr Iff.rfl (sphereChart_mem_slitSphere k z).symm

end KsIndex.Spherical
