module

public import KsIndexLean.SphericalQuotientForms
public import KsIndexLean.SphericalSlitBoundary

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

/-- The first one-sided trace is continuous on the actual chart quotient. -/
def firstChartTraceCLM {A : Set Circle₁} (hA : IsOpen A) (B : Set Circle₁) :
    SphereChartSpace A hA →L[ℂ] Lp ℂ 2 (circleMeasure.restrict B) :=
  (arcTrace B).comp ((ContinuousLinearMap.fst ℂ ComplexH1 ComplexH1).comp
    (sphereDiskCoordinatesCLM hA))

def secondChartTraceCLM {A : Set Circle₁} (hA : IsOpen A) (B : Set Circle₁) :
    SphereChartSpace A hA →L[ℂ] Lp ℂ 2 (circleMeasure.restrict B) :=
  (arcTrace B).comp ((ContinuousLinearMap.snd ℂ ComplexH1 ComplexH1).comp
    (sphereDiskCoordinatesCLM hA))

lemma firstChartTraceCLM_apply {A : Set Circle₁} (hA : IsOpen A) (B : Set Circle₁)
    (q : SphereChartSpace A hA) : firstChartTraceCLM hA B q = firstChartTrace hA B q := rfl

lemma secondChartTraceCLM_apply {A : Set Circle₁} (hA : IsOpen A) (B : Set Circle₁)
    (q : SphereChartSpace A hA) : secondChartTraceCLM hA B q = secondChartTrace hA B q := rfl

/-- Same carrier predicate as the previously constructed phase space. -/
def sphericalPhaseDomain (k : ℕ) (c : ℂ) : Submodule ℂ (SphericalSlitNeumannSpace k) where
  carrier := {q | firstChartTraceCLM (isOpen_boundaryArc k 1) (boundaryArc k 0) q =
    c • secondChartTraceCLM (isOpen_boundaryArc k 1) (boundaryArc k 0) q}
  zero_mem' := by simp
  add_mem' := by
    intro q r hq hr; change _ = _ at hq hr ⊢; simp only [map_add, hq, hr, smul_add]
  smul_mem' := by
    intro a q hq; change _ = _ at hq ⊢; simp only [map_smul, hq, smul_comm a c]

lemma isClosed_sphericalPhaseDomain (k : ℕ) (c : ℂ) :
    IsClosed (sphericalPhaseDomain k c : Set (SphericalSlitNeumannSpace k)) :=
  isClosed_eq (firstChartTraceCLM (isOpen_boundaryArc k 1) (boundaryArc k 0)).continuous
    ((secondChartTraceCLM (isOpen_boundaryArc k 1) (boundaryArc k 0)).continuous.const_smul c)

instance sphericalPhaseNormedAddCommGroup (k : ℕ) (c : ℂ) :
    NormedAddCommGroup (SphericalSlitPhaseSpace k c) :=
  inferInstanceAs (NormedAddCommGroup (sphericalPhaseDomain k c))
instance sphericalPhaseModule (k : ℕ) (c : ℂ) : Module ℂ (SphericalSlitPhaseSpace k c) :=
  inferInstanceAs (Module ℂ (sphericalPhaseDomain k c))
instance sphericalPhaseNormedSpace (k : ℕ) (c : ℂ) : NormedSpace ℂ (SphericalSlitPhaseSpace k c) :=
  inferInstanceAs (NormedSpace ℂ (sphericalPhaseDomain k c))
instance sphericalPhaseCompleteSpace (k : ℕ) (c : ℂ) :
    CompleteSpace (SphericalSlitPhaseSpace k c) :=
  (isClosed_sphericalPhaseDomain k c).completeSpace_coe

/-- Recovery of the existing disk phase domain preserves linear operations and norm. -/
def slitPhaseLinearIsometryEquiv (k : ℕ) (c : ℂ) :
    SphericalSlitPhaseSpace k c ≃ₗᵢ[ℂ] slitTraceDomain k c where
  toEquiv := (slitPhaseEquiv k c).symm
  map_add' q r := by
    apply Subtype.ext
    exact (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1)).map_add q.val r.val
  map_smul' a q := by
    apply Subtype.ext
    exact (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1)).map_smul a q.val
  norm_map' _ := rfl

/-- Both one-sided traces vanish, with the inherited quotient norm. -/
def sphericalDirichletDomain (k : ℕ) : Submodule ℂ (SphericalSlitNeumannSpace k) where
  carrier := {q | firstChartTraceCLM (isOpen_boundaryArc k 1) (boundaryArc k 0) q = 0 ∧
    secondChartTraceCLM (isOpen_boundaryArc k 1) (boundaryArc k 0) q = 0}
  zero_mem' := by simp
  add_mem' := by
    intro q r hq hr
    change _ = 0 ∧ _ = 0 at hq hr ⊢
    simp only [map_add, hq.1, hq.2, hr.1, hr.2, add_zero, and_self]
  smul_mem' := by
    intro a q hq
    change _ = 0 ∧ _ = 0 at hq ⊢
    simp only [map_smul, hq.1, hq.2, smul_zero, and_self]

lemma isClosed_sphericalDirichletDomain (k : ℕ) :
    IsClosed (sphericalDirichletDomain k : Set (SphericalSlitNeumannSpace k)) :=
  (isClosed_eq (firstChartTraceCLM (isOpen_boundaryArc k 1) (boundaryArc k 0)).continuous
    continuous_const).inter
  (isClosed_eq (secondChartTraceCLM (isOpen_boundaryArc k 1) (boundaryArc k 0)).continuous
    continuous_const)

instance sphericalDirichletNormedAddCommGroup (k : ℕ) :
    NormedAddCommGroup (SphericalSlitDirichletSpace k) :=
  inferInstanceAs (NormedAddCommGroup (sphericalDirichletDomain k))
instance sphericalDirichletModule (k : ℕ) : Module ℂ (SphericalSlitDirichletSpace k) :=
  inferInstanceAs (Module ℂ (sphericalDirichletDomain k))
instance sphericalDirichletNormedSpace (k : ℕ) : NormedSpace ℂ (SphericalSlitDirichletSpace k) :=
  inferInstanceAs (NormedSpace ℂ (sphericalDirichletDomain k))
instance sphericalDirichletCompleteSpace (k : ℕ) : CompleteSpace (SphericalSlitDirichletSpace k) :=
  (isClosed_sphericalDirichletDomain k).completeSpace_coe

def slitDirichletLinearIsometryEquiv (k : ℕ) :
    SphericalSlitDirichletSpace k ≃ₗᵢ[ℂ] slitDirichletDomain k where
  toEquiv := (slitDirichletEquiv k).symm
  map_add' q r := by
    apply Subtype.ext
    exact (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1)).map_add q.val r.val
  map_smul' a q := by
    apply Subtype.ext
    exact (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1)).map_smul a q.val
  norm_map' _ := rfl

/-- Neumann imposes no additional slit trace condition. -/
def slitNeumannLinearIsometryEquiv (k : ℕ) :
    SphericalSlitNeumannSpace k ≃ₗᵢ[ℂ] slitNeumannDomain k :=
  sphereTransmissionLinearIsometryEquiv (boundaryArc k 1) (isOpen_boundaryArc k 1)

end KsIndex.Spherical
