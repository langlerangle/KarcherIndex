module

public import KsIndexLean.PhasePairCollarConvergence
public import KsIndexLean.ReflectionLocalization
public import KsIndexLean.InversionJetTransition
public import KsIndexLean.SphericalJoinedJet
public import KsIndexLean.FiniteWeakPartition

@[expose] public section


open Set MeasureTheory
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket KsIndex.WeakH1

/-- The inverse-phase pullback of a two-disk join is the join with its disks
swapped. The seam and origin exclusions are null sets. -/
lemma joined_value_inverse_phase (u v : ComplexH1) {c : ℂ} (hc : c ≠ 0) :
    (fun z => c⁻¹ • joinedDiskValue u v c (σ z)) =ᵐ[volume]
      joinedDiskValue v u c⁻¹ := by
  filter_upwards [volume.ae_ne (0 : ℂ), ae_norm_ne_one] with z hz hn
  simp only [joinedDiskValue_sigma_formula, σ_σ]
  rcases lt_or_gt_of_ne hn with h | h
  · rw [ite_eq_right (not_norm_σ_le hz h), ite_eq_left h.le,
      smul_smul, inv_mul_cancel₀ hc, one_smul]
  · have hi : ‖σ z‖ ≤ 1 := by
      rw [norm_σ]
      exact (inv_le_one₀ (norm_pos_iff.mpr hz)).mpr h.le
    rw [ite_eq_left hi, ite_eq_right (not_le.mpr h)]

lemma joined_jet_inverse_phase (u v : ComplexH1) {c : ℂ} (hc : c ≠ 0) :
    (fun z => c⁻¹ • (joinedDiskJet u v c (σ z)).comp (fderiv ℝ σ z)) =ᵐ[volume]
      joinedDiskJet v u c⁻¹ := by
  filter_upwards [joinedDiskJet_reflection_ae u v hc] with z hz
  rw [hz, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- Symmetric localization identifies the inverse-side value limit with the
localized swapped join, for the actual phase c, without a sign assumption. -/
lemma localized_pair_value_inverse_phase (u v : ComplexH1) {c : ℂ} (hc : c ≠ 0)
    {χ : ℂ → ℝ} (hi : ∀ z, χ (σ z) = χ z) :
    (fun z => c⁻¹ • (χ (σ z) • joinedDiskValue u v c (σ z))) =ᵐ[volume]
      (fun z => χ z • joinedDiskValue v u c⁻¹ z) := by
  filter_upwards [joined_value_inverse_phase u v hc] with z hz
  rw [hi, smul_comm, hz]

/-- The corresponding full product jet also agrees, including the derivative
of the cutoff and the derivative of inversion. -/
lemma localized_pair_jet_inverse_phase (u v : ComplexH1) {c : ℂ} (hc : c ≠ 0)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hi : ∀ z, χ (σ z) = χ z) :
    (fun z => c⁻¹ •
      (χ (σ z) • joinedDiskJet u v c (σ z) +
        (fderiv ℝ χ (σ z)).smulRight (joinedDiskValue u v c (σ z))).comp
          (fderiv ℝ σ z)) =ᵐ[volume]
      (fun z => χ z • joinedDiskJet v u c⁻¹ z +
        (fderiv ℝ χ z).smulRight (joinedDiskValue v u c⁻¹ z)) := by
  filter_upwards [joined_value_inverse_phase u v hc, joined_jet_inverse_phase u v hc,
    volume.ae_ne (0 : ℂ)] with z hu hJ hz
  ext d
  have hd := congrArg (fun L : ℂ →L[ℝ] ℝ => L d) (invariant_cutoff_derivative hχ hi hz)
  have hj := congrArg (fun L : ℂ →L[ℝ] ℂ => L d) hJ
  change fderiv ℝ χ (σ z) (fderiv ℝ σ z d) = fderiv ℝ χ z d at hd
  change c⁻¹ • joinedDiskJet u v c (σ z) (fderiv ℝ σ z d) =
    joinedDiskJet v u c⁻¹ z d at hj
  change c⁻¹ • (χ (σ z) • joinedDiskJet u v c (σ z) (fderiv ℝ σ z d) +
      fderiv ℝ χ (σ z) (fderiv ℝ σ z d) • joinedDiskValue u v c (σ z)) =
    χ z • joinedDiskJet v u c⁻¹ z d + fderiv ℝ χ z d • joinedDiskValue v u c⁻¹ z
  rw [smul_add, hi, hd, smul_comm c⁻¹ (χ z),
    smul_comm c⁻¹ (fderiv ℝ χ z d), hj, hu]

/-- On the lower disk the inverse-side limit is exactly its localized original
H1 value, not an unrelated representative of the reflected join. -/
lemma localized_pair_lower_value (u v : ComplexH1) {c : ℂ} (hc : c ≠ 0)
    {χ : ℂ → ℝ} (hi : ∀ z, χ (σ z) = χ z) :
    (fun z => c⁻¹ • (χ (σ z) • joinedDiskValue u v c (σ z)))
      =ᵐ[volume.restrict (disk : Set ℂ)] (fun z => χ z • valueCLM v z) := by
  filter_upwards [(localized_pair_value_inverse_phase u v hc hi).filter_mono
    (ae_mono Measure.restrict_le_self),
    ae_restrict_mem KsIndex.SurfaceForm.measurableSet_disk] with z hz hzd
  rw [hz, joined_value_on_disk v u c⁻¹ hzd]

/-- The lower-disk limit jet is the actual product-rule jet of its original
H1 carrier. The exceptional origin is discarded only as a null set. -/
lemma localized_pair_lower_jet (u v : ComplexH1) {c : ℂ} (hc : c ≠ 0)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hi : ∀ z, χ (σ z) = χ z) :
    (fun z => c⁻¹ •
      (χ (σ z) • joinedDiskJet u v c (σ z) +
        (fderiv ℝ χ (σ z)).smulRight (joinedDiskValue u v c (σ z))).comp
          (fderiv ℝ σ z)) =ᵐ[volume.restrict (disk : Set ℂ)]
      (fun z => χ z • Dxy (dxLp v) (dyLp v) z +
        (fderiv ℝ χ z).smulRight (valueCLM v z)) := by
  filter_upwards [(localized_pair_jet_inverse_phase u v hc hχ hi).filter_mono
    (ae_mono Measure.restrict_le_self),
    (volume.ae_ne (0 : ℂ)).filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem KsIndex.SurfaceForm.measurableSet_disk] with z hz h0 hzd
  rw [hz, joined_value_on_disk v u c⁻¹ hzd,
    KsIndex.Spherical.joinedDiskJet_eq_coordinates v u c⁻¹ h0
      (KsIndex.SurfaceForm.mem_disk_iff.mp hzd).le]

end KsIndex.Trace
