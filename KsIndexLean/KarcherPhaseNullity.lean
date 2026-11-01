module

public import KsIndexLean.KarcherSlitNullity
public import KsIndexLean.SurfacePhaseNullity
public import KsIndexLean.PaperResonantSectorNullity

@[expose] public section


/-! Bounded complex geometric Jacobi fields of the six-ended tower at a fixed
translation phase. The endpoint nullity formula is for interior phases `0 < n < m`. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open KsIndex.Surface KsIndex.SurfaceSym KsIndex.NullityDecomp KsIndex.FormIndex
variable {m : ℕ} [Fact (2 ≤ 3)] [NeZero m] (R : PaperHalfPeriodRealization 3)

/-- The actual bounded geometric Jacobi fields with one translation character. -/
def geometricPhaseFiber (n : ℕ) : Submodule ℂ (R.boundedGeometricJacobi (m := m)) :=
  (boundedJacobiPhase 3 m n).comap (R.geometricFiberEncoding (m := m))

lemma mem_geometricPhaseFiber (n : ℕ) (G : R.boundedGeometricJacobi (m := m)) :
    G ∈ R.geometricPhaseFiber (m := m) n ↔
      ∀ q, G.val (HeightLift.periodDeck m 1 q) = zeta m ^ n * G.val q := by
  rw [R.geometricJacobiEquiv_translation_character]
  change (R.geometricFiberEncoding G ∈ BoundedJacobiE 3 m ∧
    R.geometricFiberEncoding G ∈ Module.End.eigenspace (shiftE m) (zeta m ^ n)) ↔ _
  have hb : R.geometricFiberEncoding G ∈ BoundedJacobiE 3 m := by
    rw [mem_boundedJacobiE]
    exact (R.geometricJacobiEquiv G).property
  simp only [hb, true_and, Module.End.mem_eigenspace_iff]
  constructor
  · intro ht a z
    exact congrFun ht (a,z)
  · intro ht
    exact funext (fun p => ht p.1 p.2)

def geometricPhaseFiberToModel (n : ℕ) :
    R.geometricPhaseFiber (m := m) n →ₗ[ℂ] boundedJacobiPhase 3 m n :=
  (R.geometricFiberEncoding (m := m).comp
    (R.geometricPhaseFiber (m := m) n).subtype).codRestrict _ (fun u => u.property)

lemma geometricPhaseFiberToModel_bijective (n : ℕ) :
    Function.Bijective (R.geometricPhaseFiberToModel (m := m) n) := by
  constructor
  · intro u v he
    apply Subtype.ext
    apply R.geometricJacobiEquiv.injective
    apply Subtype.ext
    apply (uncurryE m).injective
    exact congrArg Subtype.val he
  · intro w
    let v : BoundedJacobi 3 m := ⟨(uncurryE m).symm w.val,
      mem_boundedJacobiE.mp w.property.1⟩
    let g := R.geometricJacobiEquiv.symm v
    have he : R.geometricFiberEncoding (m := m) g = w.val := by
      change uncurryE m (R.geometricJacobiEquiv (R.geometricJacobiEquiv.symm v)).val = _
      rw [LinearEquiv.apply_symm_apply]
      exact (uncurryE m).apply_symm_apply w.val
    refine ⟨⟨g, ?_⟩, Subtype.ext he⟩
    change R.geometricFiberEncoding (m := m) g ∈ boundedJacobiPhase 3 m n
    rw [he]
    exact w.property

/-- At an interior translation phase, the complex dimension of bounded geometric
Jacobi fields is two at either threshold and zero otherwise. -/
theorem geometricPhaseFiber_nullity_eq_endpoint (n : ℕ) (hn : 0 < n) (hnm : n < m) :
    Cardinal.toENat (Module.rank ℂ (R.geometricPhaseFiber (m := m) n)) =
      if (n : ℝ) / m = KsIndex.Staircase.alphaStar ∨
          (n : ℝ) / m = 1 - KsIndex.Staircase.alphaStar then 2 else 0 := by
  have he := (LinearEquiv.ofBijective (R.geometricPhaseFiberToModel (m := m) n)
    (R.geometricPhaseFiberToModel_bijective (m := m) n)).rank_eq
  rw [he, boundedJacobiPhase_rank_eq_sum 3 m n (by omega)]
  exact KsIndex.PaperSlitTransport.interiorPhase_total_eq_endpoint hn hnm

end KsIndex.KarcherData.PaperHalfPeriodRealization
