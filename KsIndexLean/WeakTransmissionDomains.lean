module

public import KsIndexLean.WeakBoundaryDomains

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- The pair is ordered (upper, lower), as in the paper's slit trace equation. -/
abbrev DiskPairH1 := ComplexH1 × ComplexH1

def transmissionOperator (A : Set Circle₁) (phase : ℂ) :
    DiskPairH1 →L[ℂ] Lp ℂ 2 (circleMeasure.restrict A) :=
  (arcTrace A).comp (ContinuousLinearMap.fst ℂ ComplexH1 ComplexH1) -
    phase • (arcTrace A).comp (ContinuousLinearMap.snd ℂ ComplexH1 ComplexH1)

def transmissionDomain (A : Set Circle₁) (phase : ℂ) : Submodule ℂ DiskPairH1 :=
  LinearMap.ker (transmissionOperator A phase).toLinearMap

lemma mem_transmissionDomain (A : Set Circle₁) (phase : ℂ) (u : DiskPairH1) :
    u ∈ transmissionDomain A phase ↔ arcTrace A u.1 = phase • arcTrace A u.2 := by
  change arcTrace A u.1 - phase • arcTrace A u.2 = 0 ↔ _
  exact sub_eq_zero

lemma isClosed_transmissionDomain (A : Set Circle₁) (phase : ℂ) :
    IsClosed (transmissionDomain A phase : Set DiskPairH1) :=
  (transmissionOperator A phase).isClosed_ker

/-- Disk pairs with matching traces on arc1 and the prescribed phase relation on arc0. -/
def slitTraceDomain (k : ℕ) (phase : ℂ) : Submodule ℂ DiskPairH1 :=
  transmissionDomain (boundaryArc k 1) 1 ⊓ transmissionDomain (boundaryArc k 0) phase

lemma mem_slitTraceDomain (k : ℕ) (phase : ℂ) (u : DiskPairH1) :
    u ∈ slitTraceDomain k phase ↔
      arcTrace (boundaryArc k 1) u.1 = arcTrace (boundaryArc k 1) u.2 ∧
      arcTrace (boundaryArc k 0) u.1 = phase • arcTrace (boundaryArc k 0) u.2 := by
  simp [slitTraceDomain, mem_transmissionDomain]

lemma isClosed_slitTraceDomain (k : ℕ) (phase : ℂ) :
    IsClosed (slitTraceDomain k phase : Set DiskPairH1) :=
  (isClosed_transmissionDomain _ _).inter (isClosed_transmissionDomain _ _)

/-- The paper's upper = exp(2παi) * lower phase, on the three arc0 slits. -/
def paperSlitDomain (α : ℝ) : Submodule ℂ DiskPairH1 :=
  slitTraceDomain 3 (Complex.exp ((2 * Real.pi * α) * Complex.I))

lemma isClosed_paperSlitDomain (α : ℝ) : IsClosed (paperSlitDomain α : Set DiskPairH1) :=
  isClosed_slitTraceDomain _ _

/-- Zero trace on both sides implies every phase relation on that boundary set. -/
lemma mem_transmission_of_zero {A : Set Circle₁} (phase : ℂ) {u : DiskPairH1}
    (h1 : u.1 ∈ zeroTraceDomain A) (h2 : u.2 ∈ zeroTraceDomain A) :
    u ∈ transmissionDomain A phase := by
  rw [mem_transmissionDomain]
  have h1' : arcTrace A u.1 = 0 := h1
  have h2' : arcTrace A u.2 = 0 := h2
  rw [h1', h2', smul_zero]

/-- No phase is imposed on the slit in the natural Neumann comparison model. -/
def slitNeumannDomain (k : ℕ) : Submodule ℂ DiskPairH1 := transmissionDomain (boundaryArc k 1) 1

def slitDirichletDomain (k : ℕ) : Submodule ℂ DiskPairH1 :=
  slitNeumannDomain k ⊓
    (zeroTraceDomain (boundaryArc k 0)).comap
      (ContinuousLinearMap.fst ℂ ComplexH1 ComplexH1).toLinearMap ⊓
    (zeroTraceDomain (boundaryArc k 0)).comap
      (ContinuousLinearMap.snd ℂ ComplexH1 ComplexH1).toLinearMap

lemma slitDirichlet_le_phase (k : ℕ) (phase : ℂ) :
    slitDirichletDomain k ≤ slitTraceDomain k phase := by
  intro u hu
  exact ⟨hu.1.1, mem_transmission_of_zero phase hu.1.2 hu.2⟩

lemma slitPhase_le_Neumann (k : ℕ) (phase : ℂ) :
    slitTraceDomain k phase ≤ slitNeumannDomain k := inf_le_left

lemma isClosed_slitNeumannDomain (k : ℕ) :
    IsClosed (slitNeumannDomain k : Set DiskPairH1) := isClosed_transmissionDomain _ _

lemma isClosed_slitDirichletDomain (k : ℕ) :
    IsClosed (slitDirichletDomain k : Set DiskPairH1) :=
  ((isClosed_slitNeumannDomain k).inter
    ((isClosed_zeroTraceDomain _).preimage continuous_fst)).inter
      ((isClosed_zeroTraceDomain _).preimage continuous_snd)

/-- The same rotation character on both ordered disk components. -/
def pairCharacterDomain (θ : ℝ) (c : ℂ) : Submodule ℂ DiskPairH1 :=
  (weakCharacterDomain θ c).comap (ContinuousLinearMap.fst ℂ ComplexH1 ComplexH1).toLinearMap ⊓
    (weakCharacterDomain θ c).comap (ContinuousLinearMap.snd ℂ ComplexH1 ComplexH1).toLinearMap

lemma isClosed_pairCharacterDomain (θ : ℝ) (c : ℂ) :
    IsClosed (pairCharacterDomain θ c : Set DiskPairH1) :=
  ((isClosed_weakCharacterDomain θ c).preimage continuous_fst).inter
    ((isClosed_weakCharacterDomain θ c).preimage continuous_snd)

def paperSlitCharacterDomain (α : ℝ) (j : ℕ) : Submodule ℂ DiskPairH1 :=
  paperSlitDomain α ⊓ pairCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j)

lemma isClosed_paperSlitCharacterDomain (α : ℝ) (j : ℕ) :
    IsClosed (paperSlitCharacterDomain α j : Set DiskPairH1) :=
  (isClosed_paperSlitDomain α).inter (isClosed_pairCharacterDomain _ _)

/-- Inversion gluing fixes each circle point: value matching carries no orientation sign. -/
lemma seam_inversion_circle (w : Circle₁) : 1 / (starRingEnd ℂ) (w : ℂ) = (w : ℂ) := by
  have hw : ‖(w : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
  have hz : (w : ℂ) ≠ 0 := by intro h; simp [h] at hw
  apply (div_eq_iff ((map_ne_zero (starRingEnd ℂ)).mpr hz)).mpr
  simp [Complex.mul_conj, ← Complex.sq_norm, hw]

end KsIndex.Trace
