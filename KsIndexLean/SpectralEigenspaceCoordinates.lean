module

public import KsIndexLean.SolutionEigenbasis

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open Module.End

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma spectral_inner_apply (T : H →L[ℂ] H) (hT : T.toLinearMap.IsSymmetric)
    (b : HilbertBasis ι ℂ H) (μ : ι → ℝ)
    (hb : ∀ i, T (b i) = (μ i : ℂ) • b i) (i : ι) (x : H) :
    inner ℂ (b i) (T x) = (μ i : ℂ) * inner ℂ (b i) x := by
  have h := hT (b i) x
  change inner ℂ (T (b i)) x = inner ℂ (b i) (T x) at h
  rw [← h, hb, inner_smul_left, Complex.conj_ofReal]

/-- Eigenspace membership is exactly support on the matching spectral entries. -/
lemma mem_eigenspace_iff_spectral_support (T : H →L[ℂ] H) (hT : T.toLinearMap.IsSymmetric)
    (b : HilbertBasis ι ℂ H) (μ : ι → ℝ)
    (hb : ∀ i, T (b i) = (μ i : ℂ) • b i) (t : ℝ) (x : H) :
    x ∈ eigenspace T.toLinearMap (t : ℂ) ↔
      ∀ i, μ i ≠ t → inner ℂ (b i) x = 0 := by
  rw [mem_eigenspace_iff]
  constructor
  · intro hx i hi
    have he := congrArg (fun y => inner ℂ (b i) y) hx
    change inner ℂ (b i) (T x) = inner ℂ (b i) ((t : ℂ) • x) at he
    rw [spectral_inner_apply T hT b μ hb, inner_smul_right] at he
    have hz : ((μ i : ℂ) - (t : ℂ)) * inner ℂ (b i) x = 0 := by
      rw [sub_mul, he, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Complex.ofReal_injective.ne hi))
  · intro hx
    apply b.repr.injective
    ext i
    simp only [HilbertBasis.repr_apply_apply]
    change inner ℂ (b i) (T x) = inner ℂ (b i) ((t : ℂ) • x)
    rw [spectral_inner_apply T hT b μ hb, inner_smul_right]
    by_cases hi : μ i = t
    · rw [hi]
    · rw [hx i hi, mul_zero, mul_zero]

/-- Coordinates on a finite equality block give an exact complex eigenspace equivalence. -/
def eigenspaceCoordinatesEquiv [DecidableEq ι]
    (T : H →L[ℂ] H) (hT : T.toLinearMap.IsSymmetric)
    (b : HilbertBasis ι ℂ H) (μ : ι → ℝ)
    (hb : ∀ i, T (b i) = (μ i : ℂ) • b i) (t : ℝ)
    (s : Finset ι) (hs : ∀ i, i ∈ s ↔ μ i = t) :
    eigenspace T.toLinearMap (t : ℂ) ≃ₗ[ℂ] (s → ℂ) := by
  let L : eigenspace T.toLinearMap (t : ℂ) →ₗ[ℂ] (s → ℂ) :=
    { toFun := fun x i => inner ℂ (b i.val) x
      map_add' := fun x y => by ext i; simp
      map_smul' := fun a x => by ext i; simp }
  apply LinearEquiv.ofBijective L
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply b.repr.injective
    ext i
    simp only [HilbertBasis.repr_apply_apply]
    by_cases hi : i ∈ s
    · exact congrFun hxy ⟨i, hi⟩
    · have hne : μ i ≠ t := fun h => hi ((hs i).mpr h)
      rw [(mem_eigenspace_iff_spectral_support T hT b μ hb t x).mp x.property i hne,
        (mem_eigenspace_iff_spectral_support T hT b μ hb t y).mp y.property i hne]
  · intro c
    let x := ∑ i : s, c i • b i.val
    have hx : x ∈ eigenspace T.toLinearMap (t : ℂ) := by
      apply Submodule.sum_mem
      intro i _
      apply Submodule.smul_mem
      rw [mem_eigenspace_iff]
      change T (b i.val) = (t : ℂ) • b i.val
      rw [hb, (hs i.val).mp i.property]
    refine ⟨⟨x, hx⟩, ?_⟩
    ext i
    exact (b.orthonormal.comp (fun i : s => i.val) Subtype.val_injective).inner_right_fintype c i

lemma eigenspace_finrank_eq_block_card [DecidableEq ι]
    (T : H →L[ℂ] H) (hT : T.toLinearMap.IsSymmetric)
    (b : HilbertBasis ι ℂ H) (μ : ι → ℝ)
    (hb : ∀ i, T (b i) = (μ i : ℂ) • b i) (t : ℝ)
    (s : Finset ι) (hs : ∀ i, i ∈ s ↔ μ i = t) :
    Module.finrank ℂ (eigenspace T.toLinearMap (t : ℂ)) = s.card := by
  have h := (eigenspaceCoordinatesEquiv T hT b μ hb t s hs).finrank_eq
  simpa using h

end KsIndex.Spectral
