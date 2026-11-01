module

public import KsIndexLean.MixedPhysicalSpace
public import KsIndexLean.MixedHalfDiskWeakTests

@[expose] public section


/-! Exact range of the physical mixed-field map in each rotation character. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace KsIndex.Trace
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.WeakH1 KsIndex.FormIndex

lemma mixed_toH1_eq_of_eqOn {k : ℕ} (hk : 2 ≤ k) {b1 b0 : Bool}
    (U V : ClassicalMixedHalfDiskJacobi k b1 b0)
    (he : EqOn U.value V.value (Metric.closedBall (0 : ℂ) 1 \ punctures k)) :
    U.toH1 hk = V.toH1 hk := by
  apply valueCLM_injective
  apply Lp.ext
  filter_upwards [U.toH1_value_ae hk, V.toH1_value_ae hk,
    ae_restrict_mem measurableSet_disk] with z hu hv hz
  rw [hu, hv]
  exact he ⟨Metric.ball_subset_closedBall hz, punctures_notMem_disk (by omega) hz⟩

/-- The rotation sector of physical mixed classical fields, pulled back along
the injective weak map. Its pointwise character is proved below. -/
def classicalMixedSector {k : ℕ} (hk : 2 ≤ k) (j : ℕ) :
    Submodule ℂ (classicalMixedDiskSpace k true false) :=
  (weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j)).comap
    (classicalMixedDiskToH1 hk true false)

def classicalMixedSectorToH1 {k : ℕ} (hk : 2 ≤ k) (j : ℕ) :
    classicalMixedSector hk j →ₗ[ℂ] ComplexH1 :=
  (classicalMixedDiskToH1 hk true false).comp (classicalMixedSector hk j).subtype

/-- Exact range equality with the full-test weak radical; this is not just
an injection or a comparison of dimensions. -/
theorem classicalMixedSectorToH1_range {k : ℕ} (hk : 2 ≤ k) (j : ℕ) (u : ComplexH1) :
    u ∈ LinearMap.range (classicalMixedSectorToH1 hk j) ↔
      u ∈ mixedCharacterDomain k j true false ∧
      ∀ v ∈ mixedCharacterDomain k j true false, weakJacobi (surfacePotential k) u v = 0 := by
  constructor
  · rintro ⟨f, rfl⟩
    let U := classicalMixedDiskData f.val
    refine ⟨⟨U.toH1_mem_mixed hk, f.property⟩, ?_⟩
    intro v hv
    exact U.character_tests_zero hk j ⟨v, hv⟩
  · rintro ⟨hu, hQ⟩
    obtain ⟨U, he⟩ := dn_radical_toH1_surjective hk j u hu hQ
    let f : classicalMixedDiskSpace k true false :=
      ⟨(fun z => U.value z.val), U, fun _ => rfl⟩
    have hf : classicalMixedDiskToH1 hk true false f = u := by
      apply Eq.trans _ he
      apply mixed_toH1_eq_of_eqOn hk (classicalMixedDiskData f) U
      intro z hz
      exact classicalMixedDiskData_value f ⟨z, hz⟩
    have hs : f ∈ classicalMixedSector hk j := by
      change classicalMixedDiskToH1 hk true false f ∈
        weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j)
      rw [hf]
      exact hu.2
    exact ⟨⟨f, hs⟩, hf⟩

/-- The sector definition uses the actual paper character on every physical point. -/
theorem classicalMixedSector_pointwise {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (f : classicalMixedSector hk j) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1 \ punctures k,
      (classicalMixedDiskData f.val).value (planeRotation (-(2 * Real.pi) / k) z) =
        zeta k ^ j * (classicalMixedDiskData f.val).value z := by
  let U := classicalMixedDiskData f.val
  apply mixed_character_on_puncturedClosedDisk hk U j
  exact continuous_representative_character (U.toH1 hk) _ _ f.property
    U.smooth.continuousOn (U.toH1_value_ae hk)

end KsIndex.Trace

#print axioms KsIndex.Trace.classicalMixedSector
#print axioms KsIndex.Trace.classicalMixedSectorToH1
