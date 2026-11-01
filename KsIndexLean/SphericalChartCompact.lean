module

public import KsIndexLean.CompactDomination
public import KsIndexLean.SphericalQuotientForms
public import KsIndexLean.SphericalSlitLinear
public import KsIndexLean.FiniteDiskBulkCompact

@[expose] public section


/-! Compactness of the canonical spherical-area realization of the weak chart space. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

/-- Flat disk-pair values control the canonical spherical L2 norm. -/
theorem sphereChartL2_norm_le_bulk {A : Set Circle₁} (hA : IsOpen A)
    (q : SphereChartSpace A hA) :
    ‖sphereChartL2CLM hA q‖ ≤ 3 * ‖pairDiskValueCLM (sphereDiskCoordinatesCLM hA q)‖ := by
  have hm := (sphereJoinedValue_mass_real_comparison
    (chartDiskPair hA q).val.1 (chartDiskPair hA q).val.2).2
  have hn := sphereChartL2_norm_sq_mass hA q
  change ‖sphereChartL2CLM hA q‖ ^ 2 = _ at hn
  unfold sphereChartValue at hn
  rw [← hn] at hm
  have h1 := norm_fst_le (pairDiskValueCLM (sphereDiskCoordinatesCLM hA q))
  have h2 := norm_snd_le (pairDiskValueCLM (sphereDiskCoordinatesCLM hA q))
  change ‖valueCLM (chartDiskPair hA q).val.1‖ ≤ _ at h1
  change ‖valueCLM (chartDiskPair hA q).val.2‖ ≤ _ at h2
  have h1sq := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr h1
  have h2sq := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr h2
  nlinarith [norm_nonneg (sphereChartL2CLM hA q),
    norm_nonneg (pairDiskValueCLM (sphereDiskCoordinatesCLM hA q))]

/-- Rellich compactness for the actual spherical-area L2 realization. -/
theorem sphereChartL2CLM_compact {A : Set Circle₁} (hA : IsOpen A) :
    IsCompactOperator (sphereChartL2CLM hA) :=
  KsIndex.compact_of_norm_le_compact
    (pairDiskValueCLM.comp (sphereDiskCoordinatesCLM hA)) (sphereChartL2CLM hA) 3
    (pairDiskValueCLM_compact.comp_clm (sphereDiskCoordinatesCLM hA))
    (sphereChartL2_norm_le_bulk hA)

/-- The slit-sphere realization is compact, without a phase or character restriction. -/
theorem sphericalSlitL2CLM_compact (k : ℕ) :
    IsCompactOperator (sphereChartL2CLM (isOpen_boundaryArc k 1)) :=
  sphereChartL2CLM_compact _

/-- Every linear subdomain inherits the canonical spherical compact inclusion. -/
theorem sphereChart_subdomain_L2_compact {A : Set Circle₁} (hA : IsOpen A)
    (D : Submodule ℂ (SphereChartSpace A hA)) :
    IsCompactOperator ((sphereChartL2CLM hA).comp D.subtypeL) :=
  (sphereChartL2CLM_compact hA).comp_clm D.subtypeL
end KsIndex.Spherical
