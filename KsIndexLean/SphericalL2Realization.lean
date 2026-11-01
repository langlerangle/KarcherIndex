module

public import KsIndexLean.SphericalJoinedValueLinear

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

def sphereChartToL2 {A : Set Circle₁} (hA : IsOpen A) (q : SphereChartSpace A hA) :
    Lp ℂ 2 (volume : Measure Ambient).toSphere :=
  (sphereChartValue_memL2 hA q).toLp (sphereChartValue hA q)

lemma sphereChartToL2_coe_ae {A : Set Circle₁} (hA : IsOpen A) (q : SphereChartSpace A hA) :
    (sphereChartToL2 hA q : Sphere → ℂ) =ᵐ[(volume : Measure Ambient).toSphere]
      sphereChartValue hA q :=
  MemLp.coeFn_toLp (sphereChartValue_memL2 hA q)

/-- Actual canonical L2 realization of the spherical weak carrier. -/
def sphereChartL2LinearMap {A : Set Circle₁} (hA : IsOpen A) :
    SphereChartSpace A hA →ₗ[ℂ] Lp ℂ 2 (volume : Measure Ambient).toSphere where
  toFun := sphereChartToL2 hA
  map_add' q r := by
    apply Lp.ext
    filter_upwards [sphereChartToL2_coe_ae hA (q + r), sphereChartToL2_coe_ae hA q,
      sphereChartToL2_coe_ae hA r, sphereChartValue_add_ae hA q r,
      Lp.coeFn_add (sphereChartToL2 hA q) (sphereChartToL2 hA r)] with p hs hq hr ha hl
    simp only [Pi.add_apply] at hl
    rw [hs, hl, hq, hr]
    exact ha
  map_smul' c q := by
    apply Lp.ext
    filter_upwards [sphereChartToL2_coe_ae hA (c • q), sphereChartToL2_coe_ae hA q,
      sphereChartValue_smul_ae hA c q, Lp.coeFn_smul c (sphereChartToL2 hA q)] with p hs hq ha hl
    simp only [Pi.smul_apply] at hl
    simp only [RingHom.id_apply]
    rw [hs, hl, hq]
    exact ha

lemma sphereChartValue_eq_ae_iff {A : Set Circle₁} (hA : IsOpen A)
    (q r : SphereChartSpace A hA) :
    sphereChartValue hA q =ᵐ[(volume : Measure Ambient).toSphere] sphereChartValue hA r ↔
      q = r := by
  constructor
  · intro h
    have he : matchingPairClass hA (chartDiskPair hA q) =
        matchingPairClass hA (chartDiskPair hA r) := by
      apply Quotient.sound
      exact (sphereChartSetoid_iff_canonical hA
        (matchingPairFunction hA (chartDiskPair hA q))
        (matchingPairFunction hA (chartDiskPair hA r))).mpr h
    simpa only [matchingPairClass_chartDiskPair] using he
  · rintro rfl
    exact Filter.EventuallyEq.rfl

lemma sphereChartL2LinearMap_injective {A : Set Circle₁} (hA : IsOpen A) :
    Function.Injective (sphereChartL2LinearMap hA) := by
  intro q r h
  have he : (sphereChartToL2 hA q : Sphere → ℂ) =ᵐ[(volume : Measure Ambient).toSphere]
      (sphereChartToL2 hA r : Sphere → ℂ) := by
    exact Lp.ext_iff.mp h
  exact (sphereChartValue_eq_ae_iff hA q r).mp
    ((sphereChartToL2_coe_ae hA q).symm.trans (he.trans (sphereChartToL2_coe_ae hA r)))

lemma sphereChartL2LinearMap_enorm {A : Set Circle₁} (hA : IsOpen A)
    (q : SphereChartSpace A hA) : ‖sphereChartL2LinearMap hA q‖ₑ = sphereChartL2 hA q := by
  change ‖(sphereChartValue_memL2 hA q).toLp (sphereChartValue hA q)‖ₑ = _
  rw [Lp.enorm_toLp]
  obtain ⟨p, rfl⟩ := matchingPairClass_surjective hA q
  rw [sphereChartL2_matchingPair, sphereChartValue, chartDiskPair_join]

lemma sphereChartL2LinearMap_mk_ae {A : Set Circle₁} (hA : IsOpen A)
    (F : SphereChartFunctions A hA) :
    (sphereChartL2LinearMap hA (Quotient.mk (sphereChartSetoid A hA) F) : Sphere → ℂ)
      =ᵐ[(volume : Measure Ambient).toSphere] F.val :=
  (sphereChartToL2_coe_ae hA _).trans (sphereChartValue_mk_ae hA F)

end KsIndex.Spherical
