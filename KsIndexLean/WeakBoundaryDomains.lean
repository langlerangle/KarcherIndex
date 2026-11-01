module

public import KsIndexLean.BoundaryRestriction
public import KsIndexLean.CharDecomp

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- The surface arc family, viewed on the boundary-circle subtype. -/
def boundaryArc (k n : ℕ) : Set Circle₁ := {w | (w : ℂ) ∈ KsIndex.Surface.arc k n}

lemma mem_boundaryArc (k n : ℕ) (w : Circle₁) :
    w ∈ boundaryArc k n ↔ (-1 : ℝ) ^ n * ((w : ℂ) ^ k).re < 0 := by
  change (‖(w : ℂ)‖ = 1 ∧ _) ↔ _
  rw [mem_sphere_zero_iff_norm.mp w.property]
  simp

lemma measurableSet_boundaryArc (k n : ℕ) : MeasurableSet (boundaryArc k n) := by
  have h : boundaryArc k n = {w : Circle₁ | (-1 : ℝ) ^ n * ((w : ℂ) ^ k).re < 0} :=
    Set.ext (mem_boundaryArc k n)
  rw [h]
  exact (isOpen_lt (by fun_prop) continuous_const).measurableSet

/-- True is natural Neumann (unrestricted); false imposes zero trace. -/
def naturalArcDomain (k n : ℕ) (neumann : Bool) : Submodule ℂ ComplexH1 :=
  if neumann then ⊤ else zeroTraceDomain (boundaryArc k n)

def mixedTraceDomain (k : ℕ) (b1 b0 : Bool) : Submodule ℂ ComplexH1 :=
  naturalArcDomain k 1 b1 ⊓ naturalArcDomain k 0 b0

lemma mem_naturalArcDomain (k n : ℕ) (b : Bool) (u : ComplexH1) :
    u ∈ naturalArcDomain k n b ↔
      b = false →
        (diskTraceCLM u : Circle₁ → ℂ) =ᵐ[circleMeasure.restrict (boundaryArc k n)] 0 := by
  cases b <;> simp [naturalArcDomain, mem_zeroTraceDomain]

lemma isClosed_naturalArcDomain (k n : ℕ) (b : Bool) :
    IsClosed (naturalArcDomain k n b : Set ComplexH1) := by
  cases b
  · exact isClosed_zeroTraceDomain _
  · exact isClosed_univ

lemma isClosed_mixedTraceDomain (k : ℕ) (b1 b0 : Bool) :
    IsClosed (mixedTraceDomain k b1 b0 : Set ComplexH1) :=
  (isClosed_naturalArcDomain k 1 b1).inter (isClosed_naturalArcDomain k 0 b0)

@[simp] lemma mixedTraceDomain_NN (k : ℕ) : mixedTraceDomain k true true = ⊤ := by
  simp [mixedTraceDomain, naturalArcDomain]

/-- Character constraint with an explicit angle and eigenvalue. -/
def weakCharacterOperator (θ : ℝ) (c : ℂ) : ComplexH1 →L[ℂ] ComplexH1 :=
  (diskRotation θ).toContinuousLinearMap - c • ContinuousLinearMap.id ℂ ComplexH1

def weakCharacterDomain (θ : ℝ) (c : ℂ) : Submodule ℂ ComplexH1 :=
  LinearMap.ker (weakCharacterOperator θ c).toLinearMap

lemma mem_weakCharacterDomain (θ : ℝ) (c : ℂ) (u : ComplexH1) :
    u ∈ weakCharacterDomain θ c ↔ diskRotation θ u = c • u := by
  change diskRotation θ u - c • u = 0 ↔ _
  exact sub_eq_zero

lemma isClosed_weakCharacterDomain (θ : ℝ) (c : ℂ) :
    IsClosed (weakCharacterDomain θ c : Set ComplexH1) := (weakCharacterOperator θ c).isClosed_ker

/-- Paper sector: negative-angle pullback with character eigenvalue `KsIndex.FormIndex.zeta k ^ r`. -/
def mixedCharacterDomain (k r : ℕ) (b1 b0 : Bool) : Submodule ℂ ComplexH1 :=
  mixedTraceDomain k b1 b0 ⊓ weakCharacterDomain (-(2 * Real.pi) / k) (KsIndex.FormIndex.zeta k ^ r)

lemma isClosed_mixedCharacterDomain (k r : ℕ) (b1 b0 : Bool) :
    IsClosed (mixedCharacterDomain k r b1 b0 : Set ComplexH1) :=
  (isClosed_mixedTraceDomain k b1 b0).inter (isClosed_weakCharacterDomain _ _)

lemma trace_character {θ : ℝ} {c : ℂ} {u : ComplexH1}
    (hu : u ∈ weakCharacterDomain θ c) :
    boundaryRotation θ (diskTraceCLM u) = c • diskTraceCLM u := by
  rw [← diskTrace_rotation, (mem_weakCharacterDomain θ c u).mp hu, map_smul]

end KsIndex.Trace
