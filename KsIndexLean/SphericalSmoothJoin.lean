module

public import KsIndexLean.PhaseGermOverlap
public import KsIndexLean.SphericalJoinedValue
public import KsIndexLean.SphericalCanonicalQuotient
public import KsIndexLean.SingleCcSlitClearance

@[expose] public section


open Set MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Bracket

/-- Join chosen hemisphere representatives as an actual function on the
sphere. Smoothness requires their agreement along the uncut equator. -/
def sphereRepresentativeJoin (f g : ℂ → ℂ) (p : Sphere) : ℂ :=
  if p.val 2 ≤ 0 then f (stereoCoord p.val)
  else g (stereoCoord (reflectSphere p).val)

lemma sphereRepresentativeJoin_north (f g : ℂ → ℂ) (z : ℂ) :
    sphereRepresentativeJoin f g (sphereChart z) = phaseGerm 1 f g z := by
  rw [sphereRepresentativeJoin, phaseGerm]
  change (if stereoPoint z 2 ≤ 0 then f (stereoCoord (stereoPoint z))
    else g (stereoCoord (southChart z).val)) = _
  simp only [stereoPoint_nonpos_iff, stereoCoord_stereoPoint, one_mul]
  by_cases h : ‖z‖ ≤ 1
  · simp only [h, ite_true]
  · have hz : z ≠ 0 := by intro hz; simp [hz] at h
    simp only [h, ite_false, stereoCoord_southChart hz]

lemma sphereRepresentativeJoin_south (f g : ℂ → ℂ) {z : ℂ} (hn : ‖z‖ ≠ 1) :
    sphereRepresentativeJoin f g (southChart z) = phaseGerm 1 g f z := by
  rw [sphereRepresentativeJoin, phaseGerm]
  change (if -stereoPoint z 2 ≤ 0 then f (stereoCoord (southChart z).val)
    else g (stereoCoord (reflectSphere (reflectSphere (sphereChart z))).val)) = _
  rw [reflectSphere_involutive]
  change (if -stereoPoint z 2 ≤ 0 then f (stereoCoord (southChart z).val)
    else g (stereoCoord (stereoPoint z))) = _
  rw [stereoCoord_stereoPoint]
  rcases lt_or_gt_of_ne hn with h | h
  · have ht := (stereoPoint_lower_iff z).mpr h
    rw [ite_eq_right (by linarith), ite_eq_left h.le]
  · have ht : ¬ stereoPoint z 2 ≤ 0 := by
      rw [stereoPoint_nonpos_iff]
      exact not_le.mpr h
    have hz : z ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans h)
    rw [ite_eq_left (by linarith), ite_eq_right (not_le.mpr h),
      stereoCoord_southChart hz, one_mul]

/-- On the circle the overlap theorem supplies exactly the extra equality
needed to remove the exceptional seam from the south-chart formula. -/
lemma sphereRepresentativeJoin_south_of_germs (f g : ℂ → ℂ) {z : ℂ}
    (hf : ContDiffAt ℝ ∞ (phaseGerm 1 f g) z)
    (hg : ContDiffAt ℝ ∞ (phaseGerm 1 g f) z) :
    sphereRepresentativeJoin f g (southChart z) = phaseGerm 1 g f z := by
  by_cases hn : ‖z‖ = 1
  · have hz : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; norm_num)
    rw [southChart_eq_sigma hz, sphereRepresentativeJoin_north, σ_self hn]
    simpa [phaseGerm, hn] using phaseGerm_one_boundary_eq f g hn hf hg
  · exact sphereRepresentativeJoin_south f g hn

/-- Choosing smooth hemisphere representatives does not change the actual
spherical almost-everywhere class of the joined weak values. -/
theorem sphereRepresentativeJoin_ae (u v : ComplexH1) (f g : ℂ → ℂ)
    (hf : (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict disk] f)
    (hg : (valueCLM v : ℂ → ℂ) =ᵐ[volume.restrict disk] g) :
    sphereRepresentativeJoin f g =ᵐ[(volume : Measure Ambient).toSphere]
      sphereJoinedValue u v := by
  apply (sphere_ae_eq_iff_north _ _).mpr
  have hu := (ae_restrict_iff' disk.isOpen.measurableSet).mp hf
  have hv := (ae_restrict_iff' disk.isOpen.measurableSet).mp hg
  filter_upwards [hu, ae_comp_sigma hv, ae_norm_ne_one] with z hz hi hn
  rw [sphereRepresentativeJoin_north, sphereJoinedValue_north,
    joinedDiskValue_sigma_formula]
  simp only [phaseGerm, one_mul, one_smul]
  by_cases h : ‖z‖ ≤ 1
  · rw [ite_eq_left h, ite_eq_left h]
    exact (hz (KsIndex.SurfaceForm.mem_disk_iff.mpr (lt_of_le_of_ne h hn))).symm
  · rw [ite_eq_right h, ite_eq_right h]
    apply (hi _).symm
    apply KsIndex.SurfaceForm.mem_disk_iff.mpr
    rw [norm_σ]
    exact (inv_lt_one₀ (zero_lt_one.trans (lt_of_not_ge h))).mpr (lt_of_not_ge h)

/-- The chosen spherical join is smooth in both slit charts when its two
ordinary planar germs are smooth. This includes the chart centers. -/
theorem sphereRepresentativeJoin_smooth_charts (k : ℕ) (f g : ℂ → ℂ)
    (hf : ContDiffOn ℝ ∞ (phaseGerm 1 f g) (slit k)ᶜ)
    (hg : ContDiffOn ℝ ∞ (phaseGerm 1 g f) (slit k)ᶜ) :
    ContDiffOn ℝ ∞ (fun z => sphereRepresentativeJoin f g (sphereChart z)) (slit k)ᶜ ∧
    ContDiffOn ℝ ∞ (fun z => sphereRepresentativeJoin f g (southChart z)) (slit k)ᶜ := by
  constructor
  · simpa only [sphereRepresentativeJoin_north] using hf
  · apply hg.congr
    intro z hz
    exact sphereRepresentativeJoin_south_of_germs f g
      ((hf z hz).contDiffAt ((isClosed_slit k).isOpen_compl.mem_nhds hz))
      ((hg z hz).contDiffAt ((isClosed_slit k).isOpen_compl.mem_nhds hz))

/-- The two open hemisphere restrictions recover the chosen functions;
globally smooth choices therefore supply closed-hemisphere extensions. -/
lemma sphereRepresentativeJoin_hemisphere_values (f g : ℂ → ℂ) {z : ℂ}
    (hz : ‖z‖ < 1) :
    sphereRepresentativeJoin f g (sphereChart z) = f z ∧
    sphereRepresentativeJoin f g (southChart z) = g z := by
  rw [sphereRepresentativeJoin_north,
    sphereRepresentativeJoin_south f g (ne_of_lt hz)]
  simp [phaseGerm, hz.le]

/-- The stereographic coordinate is an open embedding into the actual sphere. -/
lemma sphereChart_openEmbedding : Topology.IsOpenEmbedding sphereChart := by
  have ho : IsOpen {p : Sphere | p.val 2 ≠ 1} :=
    isClosed_eq (by fun_prop) continuous_const |>.isOpen_compl
  exact ho.isOpenEmbedding_subtypeVal.comp sphereChartHomeomorph.isOpenEmbedding

/-- Common hemisphere holes give a genuine spherical neighborhood of
vanishing, rather than only a planar AE support statement. -/
theorem sphereRepresentativeJoin_zero_near {f g : ℂ → ℂ} {q : ℂ}
    (hq : ‖q‖ = 1) (hf : f =ᶠ[𝓝 q] 0) (hg : g =ᶠ[𝓝 q] 0) :
    sphereRepresentativeJoin f g =ᶠ[𝓝 (sphereChart q)] 0 := by
  rw [← sphereChart_openEmbedding.map_nhds_eq q]
  change (fun z => sphereRepresentativeJoin f g (sphereChart z)) =ᶠ[𝓝 q] 0
  simpa only [sphereRepresentativeJoin_north] using phaseGerm_zero_near 1 hq hf hg

end KsIndex.Spherical
