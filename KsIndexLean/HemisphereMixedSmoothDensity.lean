module

public import KsIndexLean.HemisphereMixedPunctureRemoval
public import KsIndexLean.D5DensityAssembly
public import KsIndexLean.NaturalCoreClosedRepresentative
public import KsIndexLean.KarcherNeumannCoreCharacter

@[expose] public section


/-! Smooth stereographic representatives are dense in every mixed hemisphere
character domain. Smoothness at the equator is stated by closed-side germs;
the raw boundary values of a natural disk core are not used. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ContDiff
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1 KsIndex.SingleDisk

/-- Approximation in the complete hemisphere Sobolev norm by fields with
smooth closed-side stereographic representatives, vanishing near all punctures.
Every approximant retains the mixed weak trace and rotation conditions. -/
theorem hemisphereMixed_smooth_approx {k : ℕ} (hk : 1 ≤ k)
    (j : ℕ) (b1 b0 : Bool) (u : hemisphereMixedCharacterDomain k j b1 b0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : hemisphereMixedCharacterDomain k j b1 b0, ∃ G : ℂ → ℂ,
      dist u.val v.val < ε ∧ Continuous G ∧ ContDiffOn ℝ ∞ G disk ∧
      (hemisphereValue v.val =ᵐ[
        (volume : Measure Ambient).toSphere.restrict {p : Sphere | p.val 2 < 0}]
        fun p => G (stereoCoord p.val)) ∧
      (∀ w : ℂ, ‖w‖ = 1 → ∃ F : ℂ → ℂ, ContDiffAt ℝ ∞ F w ∧
        ∀ᶠ z in 𝓝 w, ‖z‖ ≤ 1 → G z = F z) ∧
      (∃ δ > 0, ∀ z : ℂ, ‖z‖ ≤ 1 →
        (∃ p ∈ Surface.punctures k, ‖z - p‖ < δ) → G z = 0) ∧
      (b1 = false → ∀ z ∈ Surface.arc k 1, G z = 0) ∧
      (b0 = false → ∀ z ∈ Surface.arc k 0, G z = 0) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 →
        G (planeRotation (-(2 * Real.pi) / k) z) = FormIndex.zeta k ^ j * G z) := by
  let ud : mixedCharacterDomain k j b1 b0 := ⟨hemisphereCoordinates u.val, u.property⟩
  obtain ⟨f, hf⟩ := (Metric.denseRange_iff.mp
    (naturalCharacterToMixed_denseRange hk j b1 b0)) ud ε hε
  let w := naturalCharacterToMixed hk j b1 b0 f
  let v := hemisphereDomainEquiv (mixedCharacterDomain k j b1 b0) w
  have hv : hemisphereCoordinates v.val = w.val :=
    hemisphereCoordinates.apply_symm_apply w.val
  obtain ⟨G, hG, hsm, he, hb, hp⟩ := exists_closed_representative hk f.property.1
  refine ⟨v, G, ?_, hG, hsm, ?_, hb, hp, ?_, ?_, ?_⟩
  · rw [← hemisphereCoordinates.dist_map, hv]
    exact hf
  · rw [hemisphere_ae_eq_iff]
    simp only [hemisphereValue, sphereWeakValue_pullback, hv]
    have ha := naturalCoreH1_value_ae hk ⟨f.val, f.property.1⟩
    filter_upwards [ha, ae_restrict_mem disk.isOpen.measurableSet] with z hz hd
    change valueCLM (naturalCoreH1 hk ⟨f.val, f.property.1⟩) z = _
    simpa only [sphereChart, stereoCoord_stereoPoint] using hz.trans (he hd)
  · intro hflag z hz
    have hh := (mem_NatCc.mp f.property.1).2.1
    simp only [hflag, ArcCond] at hh
    obtain ⟨δ, hδ, hh⟩ := hh
    exact NullityDecomp.C1rep_vanishes_near hδ hG (fun _ hx => he hx) hh hz.1.le
      ⟨z, arc_one_subset_slitC hz, by simpa using half_pos hδ⟩
  · intro hflag z hz
    have hh := (mem_NatCc.mp f.property.1).2.2.1
    simp only [hflag, ArcCond] at hh
    obtain ⟨δ, hδ, hh⟩ := hh
    exact NullityDecomp.C1rep_vanishes_near hδ hG (fun _ hx => he hx) hh hz.1.le
      ⟨z, Bracket.arc_zero_subset_slit hz, by simpa using half_pos hδ⟩
  · have hc : ∀ z ∈ Surface.disk,
        G (planeRotation (-(2 * Real.pi) / k) z) = FormIndex.zeta k ^ j * G z := by
      intro z hz
      have hr : planeRotation (-(2 * Real.pi) / k) z ∈ Surface.disk := by
        rw [SurfaceForm.mem_disk_iff, (planeRotation _).norm_map]
        exact SurfaceForm.mem_disk_iff.mp hz
      rw [← he hr, ← he hz]
      have hh := congrFun (Module.End.mem_eigenspace_iff.mp f.property.2) z
      simpa only [SingleDiskBridge.rot1_apply, Pi.smul_apply, smul_eq_mul,
        planeRotation_apply, SurfaceSym.rotUnit, Circle.coe_exp] using hh
    intro z hz
    exact KarcherData.PaperHalfPeriodRealization.continuous_disk_character_closed
      _ _ hG hc z (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)

end KsIndex.Spherical
