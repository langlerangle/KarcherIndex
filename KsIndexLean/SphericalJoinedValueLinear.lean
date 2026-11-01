module

public import KsIndexLean.SphericalCarrierH1Comparison

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

lemma sphereJoinedValue_add_ae (u v a b : ComplexH1) :
    sphereJoinedValue (u + a) (v + b) =ᵐ[(volume : Measure Ambient).toSphere]
      (fun p => sphereJoinedValue u v p + sphereJoinedValue a b p) := by
  apply (sphere_ae_eq_iff_north _ _).mpr
  have hu := (ae_restrict_iff' disk.isOpen.measurableSet).mp
    (Lp.coeFn_add (valueCLM u) (valueCLM a))
  have hv := (ae_restrict_iff' disk.isOpen.measurableSet).mp
    (Lp.coeFn_add (valueCLM v) (valueCLM b))
  filter_upwards [hu, ae_comp_sigma hv, ae_norm_ne_one] with z hz hi hn
  simp only [sphereJoinedValue_north, joinedDiskValue_sigma_formula, one_smul]
  by_cases h : ‖z‖ ≤ 1
  · have hd : z ∈ disk := SurfaceForm.mem_disk_iff.mpr (lt_of_le_of_ne h hn)
    simp only [ite_eq_left h, map_add]
    exact hz hd
  · have hpos : 0 < ‖z‖ := lt_trans zero_lt_one (lt_of_not_ge h)
    have hd : Bracket.σ z ∈ disk := by
      apply SurfaceForm.mem_disk_iff.mpr
      rw [Bracket.norm_σ]
      exact (inv_lt_one₀ hpos).mpr (lt_of_not_ge h)
    simp only [ite_eq_right h, map_add]
    exact hi hd

lemma sphereJoinedValue_smul_ae (c : ℂ) (u v : ComplexH1) :
    sphereJoinedValue (c • u) (c • v) =ᵐ[(volume : Measure Ambient).toSphere]
      (fun p => c • sphereJoinedValue u v p) := by
  apply (sphere_ae_eq_iff_north _ _).mpr
  have hu := (ae_restrict_iff' disk.isOpen.measurableSet).mp (Lp.coeFn_smul c (valueCLM u))
  have hv := (ae_restrict_iff' disk.isOpen.measurableSet).mp (Lp.coeFn_smul c (valueCLM v))
  filter_upwards [hu, ae_comp_sigma hv, ae_norm_ne_one] with z hz hi hn
  simp only [sphereJoinedValue_north, joinedDiskValue_sigma_formula, one_smul]
  by_cases h : ‖z‖ ≤ 1
  · have hd : z ∈ disk := SurfaceForm.mem_disk_iff.mpr (lt_of_le_of_ne h hn)
    simp only [ite_eq_left h, map_smul]
    exact hz hd
  · have hpos : 0 < ‖z‖ := lt_trans zero_lt_one (lt_of_not_ge h)
    have hd : Bracket.σ z ∈ disk := by
      apply SurfaceForm.mem_disk_iff.mpr
      rw [Bracket.norm_σ]
      exact (inv_lt_one₀ hpos).mpr (lt_of_not_ge h)
    simp only [ite_eq_right h, map_smul]
    exact hi hd

/-- A canonical representative, constructed from the uniquely recovered disk pair. -/
def sphereChartValue {A : Set Circle₁} (hA : IsOpen A) (q : SphereChartSpace A hA) : Sphere → ℂ :=
  sphereJoinedValue (chartDiskPair hA q).val.1 (chartDiskPair hA q).val.2

lemma sphereChartValue_add_ae {A : Set Circle₁} (hA : IsOpen A) (q r : SphereChartSpace A hA) :
    sphereChartValue hA (q + r) =ᵐ[(volume : Measure Ambient).toSphere]
      (fun p => sphereChartValue hA q p + sphereChartValue hA r p) := by
  unfold sphereChartValue
  rw [chartDiskPair_val_add]
  exact sphereJoinedValue_add_ae _ _ _ _

lemma sphereChartValue_smul_ae {A : Set Circle₁} (hA : IsOpen A) (c : ℂ)
    (q : SphereChartSpace A hA) :
    sphereChartValue hA (c • q) =ᵐ[(volume : Measure Ambient).toSphere]
      (fun p => c • sphereChartValue hA q p) := by
  unfold sphereChartValue
  rw [chartDiskPair_val_smul]
  exact sphereJoinedValue_smul_ae c _ _

lemma sphereChartValue_memL2 {A : Set Circle₁} (hA : IsOpen A) (q : SphereChartSpace A hA) :
    MemLp (sphereChartValue hA q) 2 (volume : Measure Ambient).toSphere :=
  memL2_sphereJoinedValue _ _

lemma matchingPairClass_chartDiskPair {A : Set Circle₁} (hA : IsOpen A)
    (q : SphereChartSpace A hA) : matchingPairClass hA (chartDiskPair hA q) = q :=
  (matchingDiskPairEquiv A hA).apply_symm_apply q

lemma sphereChartValue_mk_ae {A : Set Circle₁} (hA : IsOpen A) (F : SphereChartFunctions A hA) :
    sphereChartValue hA (Quotient.mk (sphereChartSetoid A hA) F) =ᵐ[
      (volume : Measure Ambient).toSphere] F.val := by
  apply (sphereChartSetoid_iff_canonical hA
    (matchingPairFunction hA (chartDiskPair hA (Quotient.mk (sphereChartSetoid A hA) F))) F).mp
  exact Quotient.exact (matchingPairClass_chartDiskPair hA _)

end KsIndex.Spherical
