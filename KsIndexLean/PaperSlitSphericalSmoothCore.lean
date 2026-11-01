module

public import KsIndexLean.PaperSlitSphericalDensity

@[expose] public section


open Set MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

/-- A single spherical representative, with smooth extensions of both
hemisphere restrictions and actual neighborhoods of vanishing at the ends. -/
def PaperSlitSphericalSmoothCore (α : ℝ) (j : ℕ)
    (u : paperSlitCharacterDomain α j) : Prop :=
  ∃ (f g : ℂ → ℂ) (F : Sphere → ℂ),
    ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ g ∧
    F =ᵐ[(volume : Measure Ambient).toSphere] sphereJoinedValue u.val.2 u.val.1 ∧
    ContDiffOn ℝ ∞ (fun z => F (sphereChart z)) (KsIndex.Bracket.slit 3)ᶜ ∧
    ContDiffOn ℝ ∞ (fun z => F (southChart z)) (KsIndex.Bracket.slit 3)ᶜ ∧
    (∀ z, ‖z‖ < 1 → F (sphereChart z) = g z ∧ F (southChart z) = f z) ∧
    ∀ q ∈ KsIndex.Surface.punctures 3, F =ᶠ[𝓝 (sphereChart q)] 0

/-- The chartwise smooth approximants realize every clause on the same
spherical function, retaining the paper's upper/lower convention. -/
theorem paperSlit_smooth_core_realization (α : ℝ) (j : ℕ)
    (u : paperSlitCharacterDomain α j) (hu : PaperSlitSmoothRepresentative α j u) :
    PaperSlitSphericalSmoothCore α j u := by
  obtain ⟨f, g, hf, hg, hvf, hvg, hs, δ, hδ, hh⟩ := hu
  have hfg := phaseGerm_contDiffOn_slit_compl 3 hf hg
    (fun z hz => by simpa using (hs 1 (Or.inr rfl) z hz).1)
  have hgf := phaseGerm_contDiffOn_slit_compl 3 hg hf
    (fun z hz => by simpa using (hs 1 (Or.inr rfl) z hz).2)
  have hr (v : ComplexH1) (h : ℂ → ℂ)
      (hv : (valueCLM v : ℂ → ℂ) =ᵐ[volume.restrict disk] h) :
      (valueCLM v : ℂ → ℂ) =ᵐ[volume.restrict disk] closedDiskRestriction h := by
    filter_upwards [hv, ae_restrict_mem disk.isOpen.measurableSet] with z hz hzd
    simp only [closedDiskRestriction, ite_eq_left (KsIndex.SurfaceForm.mem_disk_iff.mp hzd).le]
    exact hz
  let F := sphereRepresentativeJoin (closedDiskRestriction g) (closedDiskRestriction f)
  have hc := sphereRepresentativeJoin_smooth_charts 3 _ _ hgf hfg
  refine ⟨f, g, F, hf, hg,
    sphereRepresentativeJoin_ae u.val.2 u.val.1 _ _ (hr _ _ hvg) (hr _ _ hvf),
    hc.1, hc.2, ?_, ?_⟩
  · intro z hz
    have he := sphereRepresentativeJoin_hemisphere_values
      (closedDiskRestriction g) (closedDiskRestriction f) hz
    simpa only [closedDiskRestriction, ite_eq_left hz.le] using he
  · intro q hq
    have hqnorm := KsIndex.JacobiFamily.punctures_norm_eq_one (by decide : 1 ≤ 3) hq
    have hf0 : closedDiskRestriction f =ᶠ[𝓝 q] 0 := by
      filter_upwards [Metric.ball_mem_nhds q hδ] with z hz
      have hh0 := (hh q hq z (by simpa only [Metric.mem_ball, dist_eq_norm] using hz)).1
      simp [closedDiskRestriction, hh0]
    have hg0 : closedDiskRestriction g =ᶠ[𝓝 q] 0 := by
      filter_upwards [Metric.ball_mem_nhds q hδ] with z hz
      have hh0 := (hh q hq z (by simpa only [Metric.mem_ball, dist_eq_norm] using hz)).2
      simp [closedDiskRestriction, hh0]
    exact sphereRepresentativeJoin_zero_near hqnorm hg0 hf0

/-- Smooth spherical representatives with hemisphere extensions and puncture
holes form a dense core of the paper's weak phase-character space. -/
theorem paperSlit_spherical_smooth_core_dense (α : ℝ) (j : ℕ) :
    Dense {u : paperSlitCharacterDomain α j | PaperSlitSphericalSmoothCore α j u} :=
  (paperSlit_smooth_dense α j).mono (fun u hu => paperSlit_smooth_core_realization α j u hu)

/-- The same core is dense in the actual spherical phase-character carrier. -/
theorem paperSpherical_smooth_core_image_dense (α : ℝ) (j : ℕ) :
    Dense ((paperSlitCharacterSphereIsometry α j) ''
      {u : paperSlitCharacterDomain α j | PaperSlitSphericalSmoothCore α j u}) :=
  (paperSlitCharacterSphereIsometry α j).toHomeomorph.isDenseEmbedding.dense_image.mpr
    (paperSlit_spherical_smooth_core_dense α j)

end KsIndex.Spectral
