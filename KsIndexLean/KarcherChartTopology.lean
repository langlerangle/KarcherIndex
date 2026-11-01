module

public import KsIndexLean.KarcherGlobalMap

@[expose] public section


/-! Open chart embeddings for the punctured EW parameter sphere. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData

lemma isOpenEmbedding_sphereChart : IsOpenEmbedding Spherical.sphereChart := by
  have ho : IsOpen {p : Spherical.Sphere | p.val 2 ≠ 1} := by
    exact (isClosed_eq (by fun_prop : Continuous (fun p : Spherical.Sphere => p.val 2))
      continuous_const).isOpen_compl
  exact ho.isOpenEmbedding_subtypeVal.comp Spherical.sphereChartHomeomorph.isOpenEmbedding

lemma isOpenEmbedding_finiteParameter (k : ℕ) : IsOpenEmbedding (finiteParameter (k := k)) := by
  have ho : IsOpen (Surface.punctures k)ᶜ :=
    (isClosed_eq (continuous_id.pow (2 * k)) continuous_const).isOpen_compl
  have hm : MapsTo Spherical.sphereChart (Surface.punctures k)ᶜ
      (Spherical.sphereChart '' Surface.punctures k)ᶜ := by
    intro z hz
    exact (finiteParameter ⟨z, hz⟩).property
  exact isOpenEmbedding_sphereChart.restrict hm ho

/-- Complex conjugation as a topological coordinate change. -/
def conjugationHomeomorph : ℂ ≃ₜ ℂ where
  toFun := starRingEnd ℂ
  invFun := starRingEnd ℂ
  left_inv := star_star
  right_inv := star_star
  continuous_toFun := Complex.continuous_conj
  continuous_invFun := Complex.continuous_conj

lemma isOpenEmbedding_infinitySphereChart : IsOpenEmbedding infinitySphereChart :=
  Spherical.reflectSphereHomeomorph.isOpenEmbedding.comp
    (isOpenEmbedding_sphereChart.comp conjugationHomeomorph.isOpenEmbedding)

lemma isOpenEmbedding_infinityParameterChart {k : ℕ} (hk : 2 ≤ k)
    {r : ℝ} (hr : r ≤ 1) : IsOpenEmbedding (infinityParameterChart hk hr) := by
  have hm : MapsTo infinitySphereChart (Metric.ball (0 : ℂ) r)
      (Spherical.sphereChart '' Surface.punctures k)ᶜ := by
    intro z hz
    exact (infinityParameterChart hk hr ⟨z, hz⟩).property
  exact isOpenEmbedding_infinitySphereChart.restrict hm Metric.isOpen_ball

/-- The finite chart is a homeomorphism onto its open image. -/
def finiteParameterHomeomorph (k : ℕ) : PuncturedPlane k ≃ₜ Set.range (finiteParameter (k := k)) :=
  (isOpenEmbedding_finiteParameter k).isEmbedding.toHomeomorph

/-- The infinity disk is a homeomorphism onto its open image. -/
def infinityParameterHomeomorph {k : ℕ} (hk : 2 ≤ k) {r : ℝ} (hr : r ≤ 1) :
    Metric.ball (0 : ℂ) r ≃ₜ Set.range (infinityParameterChart hk hr) :=
  (isOpenEmbedding_infinityParameterChart hk hr).isEmbedding.toHomeomorph

end KsIndex.KarcherData
