module

public import KsIndexLean.SphericalChartQuotient

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

/-- Canonical disk carriers recovered from a chartwise equivalence class. -/
def chartDiskPair {A : Set Circle₁} (hA : IsOpen A) (q : SphereChartSpace A hA) :
    MatchingDiskPair A := (matchingDiskPairEquiv A hA).symm q

lemma chartDiskPair_join {A : Set Circle₁} (hA : IsOpen A) (p : MatchingDiskPair A) :
    chartDiskPair hA (matchingPairClass hA p) = p :=
  (matchingDiskPairEquiv A hA).symm_apply_apply p

/-- Trace from the first disk chart; defined on the quotient, not on raw seam values. -/
def firstChartTrace {A : Set Circle₁} (hA : IsOpen A) (B : Set Circle₁)
    (q : SphereChartSpace A hA) : Lp ℂ 2 (circleMeasure.restrict B) :=
  arcTrace B (chartDiskPair hA q).val.1

def secondChartTrace {A : Set Circle₁} (hA : IsOpen A) (B : Set Circle₁)
    (q : SphereChartSpace A hA) : Lp ℂ 2 (circleMeasure.restrict B) :=
  arcTrace B (chartDiskPair hA q).val.2

lemma chartTrace_ordinary {A : Set Circle₁} (hA : IsOpen A) (q : SphereChartSpace A hA) :
    firstChartTrace hA A q = secondChartTrace hA A q := (chartDiskPair hA q).property

/-- The slit phase equation on the two recovered one-sided traces. -/
def SphericalSlitPhaseSpace (k : ℕ) (c : ℂ) :=
  {q : SphereChartSpace (boundaryArc k 1) (isOpen_boundaryArc k 1) //
    firstChartTrace (isOpen_boundaryArc k 1) (boundaryArc k 0) q =
      c • secondChartTrace (isOpen_boundaryArc k 1) (boundaryArc k 0) q}

def slitMatchingPair (k : ℕ) (c : ℂ) (p : slitTraceDomain k c) :
    MatchingDiskPair (boundaryArc k 1) :=
  ⟨p.val, ((mem_slitTraceDomain k c p.val).mp p.property).1⟩

lemma slitMatchingPair_phase (k : ℕ) (c : ℂ) (p : slitTraceDomain k c) :
    firstChartTrace (isOpen_boundaryArc k 1) (boundaryArc k 0)
        (matchingPairClass (isOpen_boundaryArc k 1) (slitMatchingPair k c p)) =
      c • secondChartTrace (isOpen_boundaryArc k 1) (boundaryArc k 0)
        (matchingPairClass (isOpen_boundaryArc k 1) (slitMatchingPair k c p)) := by
  unfold firstChartTrace secondChartTrace
  rw [chartDiskPair_join]
  exact ((mem_slitTraceDomain k c p.val).mp p.property).2

/-- Set equivalence retaining the existing disk-pair order and phase convention. -/
def slitPhaseEquiv (k : ℕ) (c : ℂ) : slitTraceDomain k c ≃ SphericalSlitPhaseSpace k c where
  toFun p := ⟨matchingPairClass (isOpen_boundaryArc k 1) (slitMatchingPair k c p),
    slitMatchingPair_phase k c p⟩
  invFun q := ⟨(chartDiskPair (isOpen_boundaryArc k 1) q.val).val, by
    rw [mem_slitTraceDomain]
    exact ⟨(chartDiskPair (isOpen_boundaryArc k 1) q.val).property, q.property⟩⟩
  left_inv p := by
    dsimp only
    apply Subtype.ext
    change (chartDiskPair (isOpen_boundaryArc k 1)
      (matchingPairClass (isOpen_boundaryArc k 1) (slitMatchingPair k c p))).val = p.val
    exact congrArg Subtype.val (chartDiskPair_join (isOpen_boundaryArc k 1)
      (slitMatchingPair k c p))
  right_inv q := by
    dsimp only
    apply Subtype.ext
    exact (matchingDiskPairEquiv (boundaryArc k 1) (isOpen_boundaryArc k 1)).apply_symm_apply q.val

end KsIndex.Spherical
