module

public import KsIndexLean.RadialL2Approximation

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

def radialValueLp (t : ℝ) (ht : 0 ≤ t) (u : ComplexH1) : L2C :=
  (radial_value_memLp ht (Lp.memLp (valueCLM u))).toLp (radialTruncate t ∘ valueCLM u)

def radialDxLp (t : ℝ) (ht : 0 ≤ t) (u : ComplexH1) : L2C :=
  (radial_jet_memLp ht (Lp.memLp (valueCLM u)) (Lp.memLp (dxLp u))).toLp
    (fun z => radialJet t (valueCLM u z) (dxLp u z))

def radialDyLp (t : ℝ) (ht : 0 ≤ t) (u : ComplexH1) : L2C :=
  (radial_jet_memLp ht (Lp.memLp (valueCLM u)) (Lp.memLp (dyLp u))).toLp
    (fun z => radialJet t (valueCLM u z) (dyLp u z))

lemma radial_hasJet (t : ℝ) (ht : 0 ≤ t) (u : ComplexH1) :
    HasComplexH1Jet (radialValueLp t ht u) (radialDxLp t ht u) (radialDyLp t ht u) := by
  have hU (d : ℂ) : MemLp (fun z => Dxy (dxLp u) (dyLp u) z d) 2
      (volume.restrict (disk : Set ℂ)) :=
    ((Lp.memLp (dxLp u)).const_smul d.re).add ((Lp.memLp (dyLp u)).const_smul d.im)
  have hw := weakH1_radialTruncate ht (Lp.memLp (valueCLM u)) hU (carrier_hasJet u)
  apply (hw.congr_ae (radial_value_memLp ht (Lp.memLp (valueCLM u))).coeFn_toLp.symm).congr_ae_deriv
  filter_upwards [(radial_jet_memLp ht (Lp.memLp (valueCLM u)) (Lp.memLp (dxLp u))).coeFn_toLp,
    (radial_jet_memLp ht (Lp.memLp (valueCLM u)) (Lp.memLp (dyLp u))).coeFn_toLp] with z hx hy
  ext d
  change radialJet t (valueCLM u z) (d.re • dxLp u z + d.im • dyLp u z) =
    d.re • radialDxLp t ht u z + d.im • radialDyLp t ht u z
  rw [show radialDxLp t ht u z = radialJet t (valueCLM u z) (dxLp u z) from hx,
    show radialDyLp t ht u z = radialJet t (valueCLM u z) (dyLp u z) from hy,
    map_add, map_smul, map_smul]

/-- The actual adopted H1 carrier of the nonlinear radial value and weak jet. -/
def diskRadial (t : ℝ) (ht : 0 ≤ t) (u : ComplexH1) : ComplexH1 :=
  Classical.choose (exists_unique_carrier_of_jet _ _ _ (radial_hasJet t ht u)).exists

lemma diskRadial_coordinates (t : ℝ) (ht : 0 ≤ t) (u : ComplexH1) :
    valueCLM (diskRadial t ht u) = radialValueLp t ht u ∧
      dxLp (diskRadial t ht u) = radialDxLp t ht u ∧
      dyLp (diskRadial t ht u) = radialDyLp t ht u :=
  Classical.choose_spec (exists_unique_carrier_of_jet _ _ _ (radial_hasJet t ht u)).exists

lemma diskRadial_value_ae (t : ℝ) (ht : 0 ≤ t) (u : ComplexH1) :
    (valueCLM (diskRadial t ht u) : ℂ → ℂ) =ᵐ[volume.restrict disk]
      (radialTruncate t ∘ valueCLM u) := by
  rw [(diskRadial_coordinates t ht u).1]
  exact (radial_value_memLp ht (Lp.memLp (valueCLM u))).coeFn_toLp

lemma diskRadial_bounded {t : ℝ} (ht : 0 < t) (u : ComplexH1) :
    ∀ᵐ z ∂volume.restrict disk, ‖valueCLM (diskRadial t ht.le u) z‖ ≤ (Real.sqrt t)⁻¹ := by
  filter_upwards [diskRadial_value_ae t ht.le u] with z hz
  rw [hz]
  exact radialTruncate_bounded ht (valueCLM u z)

end KsIndex.Trace
