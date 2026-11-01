module

public import KsIndexLean.ChainChartRotation
public import KsIndexLean.WeakH1Integration

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma diskRotation_value (θ : ℝ) (u : ComplexH1) :
    valueCLM (diskRotation θ u) = diskLpRotation θ (valueCLM u) :=
  diskH1Rotation_value θ u

lemma mass_diskRotation (θ : ℝ) (u v : ComplexH1) :
    mass (diskRotation θ u) (diskRotation θ v) = mass u v := by
  simp only [mass, diskRotation_value, LinearIsometry.inner_map_map]

lemma dirichlet_diskRotation (θ : ℝ) (u v : ComplexH1) :
    dirichlet (diskRotation θ u) (diskRotation θ v) = dirichlet u v := by
  have h := (diskRotation θ).inner_map_map u v
  change mass (diskRotation θ u) (diskRotation θ v) +
    dirichlet (diskRotation θ u) (diskRotation θ v) = mass u v + dirichlet u v at h
  rw [mass_diskRotation] at h
  exact add_left_cancel h

/-- Potential invariance requires only the stated AE symmetry of its actual coefficient. -/
lemma potential_diskRotation (θ : ℝ) (V : BoundedRealPotential)
    (hV : (fun z => V.V (planeRotation θ z)) =ᵐ[volume.restrict (disk : Set ℂ)] V.V)
    (u v : ComplexH1) :
    potential V (diskRotation θ u) (diskRotation θ v) = potential V u v := by
  rw [potential_integral, potential_integral]
  calc
    _ = ∫ z, (V.V (planeRotation θ z) : ℂ) *
        (starRingEnd ℂ) (valueCLM u (planeRotation θ z)) * valueCLM v (planeRotation θ z)
        ∂volume.restrict (disk : Set ℂ) := by
      apply integral_congr_ae
      filter_upwards [diskRotation_value_ae θ u, diskRotation_value_ae θ v, hV]
        with z hu hv hz
      simp only [Function.comp_apply] at hu hv
      rw [hu, hv, hz]
    _ = _ := (measurePreserving_planeRotation_disk θ).integral_comp
      (planeRotation θ).toHomeomorph.measurableEmbedding
      (fun z => (V.V z : ℂ) * (starRingEnd ℂ) (valueCLM u z) * valueCLM v z)

lemma weakJacobi_diskRotation (θ : ℝ) (V : BoundedRealPotential)
    (hV : (fun z => V.V (planeRotation θ z)) =ᵐ[volume.restrict (disk : Set ℂ)] V.V)
    (u v : ComplexH1) :
    weakJacobi V (diskRotation θ u) (diskRotation θ v) = weakJacobi V u v := by
  rw [weakJacobi, weakJacobi, dirichlet_diskRotation, potential_diskRotation θ V hV]

lemma surfacePotential_rotation (k : ℕ) (θ : ℝ) (z : ℂ) :
    (surfacePotential k).V (planeRotation θ z) = (surfacePotential k).V z := by
  exact KsIndex.ThetaOrtho.potV_rotation k (Complex.norm_exp_ofReal_mul_I θ) z

lemma surfaceJacobi_diskRotation (k : ℕ) (θ : ℝ) (u v : ComplexH1) :
    weakJacobi (surfacePotential k) (diskRotation θ u) (diskRotation θ v) =
      weakJacobi (surfacePotential k) u v :=
  weakJacobi_diskRotation θ (surfacePotential k)
    (Filter.Eventually.of_forall (surfacePotential_rotation k θ)) u v

end KsIndex.Trace
