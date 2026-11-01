module

public import KsIndexLean.PaperSlitSmoothDensity
public import KsIndexLean.PhaseGermInteriorSmooth
public import KsIndexLean.SphericalSmoothJoin

@[expose] public section


open scoped ContDiff
open MeasureTheory
noncomputable section
namespace KsIndex.Spectral
open KsIndex.Spherical KsIndex.Trace KsIndex.WeakH1

/-- The character restriction retains the isometry of the upper/lower
spherical correspondence, including its reciprocal phase convention. -/
def paperSlitCharacterSphereIsometry (α : ℝ) (j : ℕ) :
    paperSlitCharacterDomain α j ≃ₗᵢ[ℂ] paperSphericalPhaseCharacter α j where
  toLinearEquiv := paperSlitCharacterSphereEquiv α j
  norm_map' u := (paperSlitSphereLinearIsometryEquiv α).norm_map ⟨u.val, u.property.1⟩

/-- The image of the proved smooth disk representatives is dense in the
actual spherical phase-character carrier. Smoothness on spherical charts is
an additional representative-level assertion. -/
theorem paperSlit_spherical_image_dense (α : ℝ) (j : ℕ) :
    Dense ((paperSlitCharacterSphereIsometry α j) ''
      {u : paperSlitCharacterDomain α j | PaperSlitSmoothRepresentative α j u}) := by
  exact (paperSlitCharacterSphereIsometry α j).toHomeomorph.isDenseEmbedding.dense_image.mpr
    (paperSlit_smooth_dense α j)

/-- Every smooth approximant has smooth ordinary gluing germs on both
planar charts of the slit sphere. Phase matching across the removed slits
remains part of the original representative predicate. -/
theorem paperSlit_smooth_chart_germs (α : ℝ) (j : ℕ)
    (u : paperSlitCharacterDomain α j) (hu : PaperSlitSmoothRepresentative α j u) :
    ∃ f g : ℂ → ℂ,
      ContDiffOn ℝ ∞ (phaseGerm 1 (closedDiskRestriction f)
        (closedDiskRestriction g)) (KsIndex.Bracket.slit 3)ᶜ ∧
      ContDiffOn ℝ ∞ (phaseGerm 1 (closedDiskRestriction g)
        (closedDiskRestriction f)) (KsIndex.Bracket.slit 3)ᶜ ∧
      (valueCLM u.val.1 : ℂ → ℂ) =ᵐ[MeasureTheory.volume.restrict (disk : Set ℂ)] f ∧
      (valueCLM u.val.2 : ℂ → ℂ) =ᵐ[MeasureTheory.volume.restrict (disk : Set ℂ)] g := by
  obtain ⟨f, g, hf, hg, hvf, hvg, hs, _⟩ := hu
  refine ⟨f, g, phaseGerm_contDiffOn_slit_compl 3 hf hg ?_,
    phaseGerm_contDiffOn_slit_compl 3 hg hf ?_, hvf, hvg⟩
  · intro z hz
    simpa using (hs 1 (Or.inr rfl) z hz).1
  · intro z hz
    simpa using (hs 1 (Or.inr rfl) z hz).2

/-- Smooth density representatives give an actual spherical function in
lower/upper chart order, with the correct canonical AE class and smoothness
on both slit charts. -/
theorem paperSlit_exists_smooth_sphere_representative (α : ℝ) (j : ℕ)
    (u : paperSlitCharacterDomain α j) (hu : PaperSlitSmoothRepresentative α j u) :
    ∃ F : Sphere → ℂ,
      F =ᵐ[(volume : Measure Ambient).toSphere] sphereJoinedValue u.val.2 u.val.1 ∧
      ContDiffOn ℝ ∞ (fun z => F (sphereChart z)) (KsIndex.Bracket.slit 3)ᶜ ∧
      ContDiffOn ℝ ∞ (fun z => F (southChart z)) (KsIndex.Bracket.slit 3)ᶜ := by
  obtain ⟨f, g, hf, hg, hvf, hvg⟩ := paperSlit_smooth_chart_germs α j u hu
  have hr (v : ComplexH1) (h : ℂ → ℂ)
      (hv : (valueCLM v : ℂ → ℂ) =ᵐ[volume.restrict disk] h) :
      (valueCLM v : ℂ → ℂ) =ᵐ[volume.restrict disk] closedDiskRestriction h := by
    filter_upwards [hv, ae_restrict_mem disk.isOpen.measurableSet] with z hz hzd
    simp only [closedDiskRestriction, ite_eq_left (KsIndex.SurfaceForm.mem_disk_iff.mp hzd).le]
    exact hz
  refine ⟨sphereRepresentativeJoin (closedDiskRestriction g) (closedDiskRestriction f),
    sphereRepresentativeJoin_ae u.val.2 u.val.1 _ _ (hr _ _ hvg) (hr _ _ hvf), ?_⟩
  exact sphereRepresentativeJoin_smooth_charts 3 _ _ hg hf

end KsIndex.Spectral
