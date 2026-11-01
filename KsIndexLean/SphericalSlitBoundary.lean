module

public import KsIndexLean.SphericalSlitPhase

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

/-- No additional trace condition on the removed slit. -/
abbrev SphericalSlitNeumannSpace (k : ℕ) :=
  SphereChartSpace (boundaryArc k 1) (isOpen_boundaryArc k 1)

/-- Both one-sided slit traces vanish. -/
def SphericalSlitDirichletSpace (k : ℕ) :=
  {q : SphericalSlitNeumannSpace k //
    firstChartTrace (isOpen_boundaryArc k 1) (boundaryArc k 0) q = 0 ∧
    secondChartTrace (isOpen_boundaryArc k 1) (boundaryArc k 0) q = 0}

def neumannMatchingEquiv (k : ℕ) : slitNeumannDomain k ≃ MatchingDiskPair (boundaryArc k 1) where
  toFun p := ⟨p.val, by
    have h := (mem_transmissionDomain (boundaryArc k 1) 1 p.val).mp p.property
    simpa using h⟩
  invFun p := ⟨p.val, (mem_transmissionDomain (boundaryArc k 1) 1 p.val).mpr
    (by simpa using p.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def slitNeumannEquiv (k : ℕ) : slitNeumannDomain k ≃ SphericalSlitNeumannSpace k :=
  (neumannMatchingEquiv k).trans (matchingDiskPairEquiv _ (isOpen_boundaryArc k 1))

def dirichletMatchingPair (k : ℕ) (p : slitDirichletDomain k) :
    MatchingDiskPair (boundaryArc k 1) :=
  neumannMatchingEquiv k ⟨p.val, p.property.1.1⟩

lemma dirichletMatchingPair_zero (k : ℕ) (p : slitDirichletDomain k) :
    firstChartTrace (isOpen_boundaryArc k 1) (boundaryArc k 0)
        (matchingPairClass (isOpen_boundaryArc k 1) (dirichletMatchingPair k p)) = 0 ∧
    secondChartTrace (isOpen_boundaryArc k 1) (boundaryArc k 0)
        (matchingPairClass (isOpen_boundaryArc k 1) (dirichletMatchingPair k p)) = 0 := by
  unfold firstChartTrace secondChartTrace
  rw [chartDiskPair_join]
  exact ⟨p.property.1.2, p.property.2⟩

def slitDirichletEquiv (k : ℕ) : slitDirichletDomain k ≃ SphericalSlitDirichletSpace k where
  toFun p := ⟨matchingPairClass (isOpen_boundaryArc k 1) (dirichletMatchingPair k p),
    dirichletMatchingPair_zero k p⟩
  invFun q := ⟨(chartDiskPair (isOpen_boundaryArc k 1) q.val).val, by
    refine ⟨⟨?_, q.property.1⟩, q.property.2⟩
    apply (mem_transmissionDomain (boundaryArc k 1) 1 _).mpr
    simpa using (chartDiskPair (isOpen_boundaryArc k 1) q.val).property⟩
  left_inv p := by
    dsimp only
    apply Subtype.ext
    change (chartDiskPair (isOpen_boundaryArc k 1)
      (matchingPairClass (isOpen_boundaryArc k 1) (dirichletMatchingPair k p))).val = p.val
    exact congrArg Subtype.val (chartDiskPair_join (isOpen_boundaryArc k 1)
      (dirichletMatchingPair k p))
  right_inv q := by
    dsimp only
    apply Subtype.ext
    exact (matchingDiskPairEquiv (boundaryArc k 1) (isOpen_boundaryArc k 1)).apply_symm_apply q.val

/-- Zero traces satisfy every phase relation. -/
def sphericalDirichletToPhase (k : ℕ) (c : ℂ) (q : SphericalSlitDirichletSpace k) :
    SphericalSlitPhaseSpace k c :=
  ⟨q.val, by rw [q.property.1, q.property.2, smul_zero]⟩

def sphericalPhaseToNeumann (k : ℕ) (c : ℂ) (q : SphericalSlitPhaseSpace k c) :
    SphericalSlitNeumannSpace k := q.val

lemma slitDirichlet_phase_commutes (k : ℕ) (c : ℂ) (p : slitDirichletDomain k) :
    sphericalDirichletToPhase k c (slitDirichletEquiv k p) =
      slitPhaseEquiv k c ⟨p.val, slitDirichlet_le_phase k c p.property⟩ := by
  apply Subtype.ext
  rfl

lemma slitPhase_neumann_commutes (k : ℕ) (c : ℂ) (p : slitTraceDomain k c) :
    sphericalPhaseToNeumann k c (slitPhaseEquiv k c p) =
      slitNeumannEquiv k ⟨p.val, slitPhase_le_Neumann k c p.property⟩ := rfl

end KsIndex.Spherical
