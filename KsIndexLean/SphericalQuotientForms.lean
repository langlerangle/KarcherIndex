module

public import KsIndexLean.SphericalL2Continuous

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

/-- Continuous recovery of the two ordered disk carriers. -/
def sphereDiskCoordinatesCLM {A : Set Circle₁} (hA : IsOpen A) :
    SphereChartSpace A hA →L[ℂ] ComplexH1 × ComplexH1 :=
  (transmissionDomain A 1).subtypeL.comp
    (sphereTransmissionLinearIsometryEquiv A hA).toContinuousLinearEquiv.toContinuousLinearMap

lemma sphereDiskCoordinatesCLM_apply {A : Set Circle₁} (hA : IsOpen A)
    (q : SphereChartSpace A hA) : sphereDiskCoordinatesCLM hA q = (chartDiskPair hA q).val := rfl

def sphereChartDirichlet {A : Set Circle₁} (hA : IsOpen A)
    (q r : SphereChartSpace A hA) : ℂ :=
  dirichlet (sphereDiskCoordinatesCLM hA q).1 (sphereDiskCoordinatesCLM hA r).1 +
    dirichlet (sphereDiskCoordinatesCLM hA q).2 (sphereDiskCoordinatesCLM hA r).2

def sphereChartJacobi {A : Set Circle₁} (hA : IsOpen A) (V : BoundedRealPotential)
    (q r : SphereChartSpace A hA) : ℂ :=
  weakJacobi V (sphereDiskCoordinatesCLM hA q).1 (sphereDiskCoordinatesCLM hA r).1 +
    weakJacobi V (sphereDiskCoordinatesCLM hA q).2 (sphereDiskCoordinatesCLM hA r).2

/-- Continuity of a two-copy form pullback along a continuous map from any topological space. -/
lemma continuous_diskPairForm_pullback {E : Type*} [TopologicalSpace E]
    (T : E → ComplexH1 × ComplexH1) (hT : Continuous T)
    (B : ComplexH1 → ComplexH1 → ℂ)
    (hB : Continuous (fun p : ComplexH1 × ComplexH1 => B p.1 p.2)) :
    Continuous (fun p : E × E => B (T p.1).1 (T p.2).1 + B (T p.1).2 (T p.2).2) :=
  (hB.comp ((hT.fst.comp continuous_fst).prodMk (hT.fst.comp continuous_snd))).add
    (hB.comp ((hT.snd.comp continuous_fst).prodMk (hT.snd.comp continuous_snd)))

lemma continuous_sphereChartDirichlet {A : Set Circle₁} (hA : IsOpen A) :
    Continuous (fun p : SphereChartSpace A hA × SphereChartSpace A hA =>
      sphereChartDirichlet hA p.1 p.2) :=
  continuous_diskPairForm_pullback (sphereDiskCoordinatesCLM hA)
    (sphereDiskCoordinatesCLM hA).continuous dirichlet continuous_dirichlet

lemma continuous_sphereChartJacobi {A : Set Circle₁} (hA : IsOpen A) (V : BoundedRealPotential) :
    Continuous (fun p : SphereChartSpace A hA × SphereChartSpace A hA =>
      sphereChartJacobi hA V p.1 p.2) :=
  continuous_diskPairForm_pullback (sphereDiskCoordinatesCLM hA)
    (sphereDiskCoordinatesCLM hA).continuous (weakJacobi V) (continuous_weakJacobi V)

/-- The quotient Dirichlet form is the actual canonical tangent pairing integral. -/
theorem sphereChartDirichlet_integral {A : Set Circle₁} (hA : IsOpen A)
    (q r : SphereChartSpace A hA) :
    sphereChartDirichlet hA q r =
      ∫ p, tangentPair
        (sphereJoinedGradient (chartDiskPair hA q).val.1 (chartDiskPair hA q).val.2 p)
        (sphereJoinedGradient (chartDiskPair hA r).val.1 (chartDiskPair hA r).val.2 p)
        ∂(volume : Measure Ambient).toSphere :=
  sum_dirichlet_eq_joined_integral _ _ _ _

theorem sphereChartJacobi_integral {A : Set Circle₁} (hA : IsOpen A) (V : BoundedRealPotential)
    (k : ℕ) (q r : SphereChartSpace A hA) :
    sphereChartJacobi hA V q r =
      ∫ p in slitSphere k, joinedJacobiDensity V
        (chartDiskPair hA q).val.1 (chartDiskPair hA q).val.2
        (chartDiskPair hA r).val.1 (chartDiskPair hA r).val.2 p
        ∂(volume : Measure Ambient).toSphere :=
  sum_weakJacobi_eq_joined_integral k V _ _ _ _

lemma sphereChartDirichlet_matchingPair {A : Set Circle₁} (hA : IsOpen A)
    (p r : MatchingDiskPair A) :
    sphereChartDirichlet hA (matchingPairClass hA p) (matchingPairClass hA r) =
      dirichlet p.val.1 r.val.1 + dirichlet p.val.2 r.val.2 := by
  simp only [sphereChartDirichlet, sphereDiskCoordinatesCLM_apply, chartDiskPair_join]

lemma sphereChartJacobi_matchingPair {A : Set Circle₁} (hA : IsOpen A) (V : BoundedRealPotential)
    (p r : MatchingDiskPair A) :
    sphereChartJacobi hA V (matchingPairClass hA p) (matchingPairClass hA r) =
      weakJacobi V p.val.1 r.val.1 + weakJacobi V p.val.2 r.val.2 := by
  simp only [sphereChartJacobi, sphereDiskCoordinatesCLM_apply, chartDiskPair_join]

lemma sphereChartDirichlet_add_left {A : Set Circle₁} (hA : IsOpen A)
    (q r s : SphereChartSpace A hA) :
    sphereChartDirichlet hA (q + r) s =
      sphereChartDirichlet hA q s + sphereChartDirichlet hA r s := by
  simp [sphereChartDirichlet, dirichlet_add_left]
  ring

lemma sphereChartDirichlet_add_right {A : Set Circle₁} (hA : IsOpen A)
    (q r s : SphereChartSpace A hA) :
    sphereChartDirichlet hA q (r + s) =
      sphereChartDirichlet hA q r + sphereChartDirichlet hA q s := by
  simp [sphereChartDirichlet, dirichlet_add_right]
  ring

lemma sphereChartDirichlet_smul_left {A : Set Circle₁} (hA : IsOpen A)
    (c : ℂ) (q r : SphereChartSpace A hA) :
    sphereChartDirichlet hA (c • q) r = (starRingEnd ℂ) c * sphereChartDirichlet hA q r := by
  simp [sphereChartDirichlet, dirichlet_smul_left]
  ring

lemma sphereChartDirichlet_smul_right {A : Set Circle₁} (hA : IsOpen A)
    (c : ℂ) (q r : SphereChartSpace A hA) :
    sphereChartDirichlet hA q (c • r) = c * sphereChartDirichlet hA q r := by
  simp [sphereChartDirichlet, dirichlet_smul_right]
  ring

lemma sphereChartDirichlet_conj {A : Set Circle₁} (hA : IsOpen A)
    (q r : SphereChartSpace A hA) :
    (starRingEnd ℂ) (sphereChartDirichlet hA r q) = sphereChartDirichlet hA q r := by
  simp only [sphereChartDirichlet, map_add, dirichlet_conj]

lemma sphereChartJacobi_add_left {A : Set Circle₁} (hA : IsOpen A) (V : BoundedRealPotential)
    (q r s : SphereChartSpace A hA) :
    sphereChartJacobi hA V (q + r) s = sphereChartJacobi hA V q s + sphereChartJacobi hA V r s := by
  simp [sphereChartJacobi, weakJacobi_add_left]
  ring

lemma sphereChartJacobi_add_right {A : Set Circle₁} (hA : IsOpen A) (V : BoundedRealPotential)
    (q r s : SphereChartSpace A hA) :
    sphereChartJacobi hA V q (r + s) = sphereChartJacobi hA V q r + sphereChartJacobi hA V q s := by
  simp [sphereChartJacobi, weakJacobi_add_right]
  ring

lemma sphereChartJacobi_smul_left {A : Set Circle₁} (hA : IsOpen A) (V : BoundedRealPotential)
    (c : ℂ) (q r : SphereChartSpace A hA) :
    sphereChartJacobi hA V (c • q) r = (starRingEnd ℂ) c * sphereChartJacobi hA V q r := by
  simp [sphereChartJacobi, weakJacobi_smul_left]
  ring

lemma sphereChartJacobi_smul_right {A : Set Circle₁} (hA : IsOpen A) (V : BoundedRealPotential)
    (c : ℂ) (q r : SphereChartSpace A hA) :
    sphereChartJacobi hA V q (c • r) = c * sphereChartJacobi hA V q r := by
  simp [sphereChartJacobi, weakJacobi_smul_right]
  ring

lemma sphereChartJacobi_conj {A : Set Circle₁} (hA : IsOpen A) (V : BoundedRealPotential)
    (q r : SphereChartSpace A hA) :
    (starRingEnd ℂ) (sphereChartJacobi hA V r q) = sphereChartJacobi hA V q r := by
  simp only [sphereChartJacobi, map_add, weakJacobi_conj]

end KsIndex.Spherical
