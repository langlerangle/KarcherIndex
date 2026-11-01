module

public import KsIndexLean.SolutionEigenbasis

@[expose] public section


noncomputable section
namespace KsIndex.Spectral.PositiveCompactSolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : KsIndex.Spectral.PositiveCompactSolution H)

lemma basisEigenvalue_le_dist {i j : S.eigenbasisIndex} (hij : i ≠ j) :
    S.basisEigenvalue i ≤ dist (S.operator (S.eigenbasis i)) (S.operator (S.eigenbasis j)) := by
  have hi : inner ℂ (S.eigenbasis i)
      (S.operator (S.eigenbasis i) - S.operator (S.eigenbasis j)) =
      (S.basisEigenvalue i : ℂ) := by
    rw [S.eigenbasis_equation, S.eigenbasis_equation, inner_sub_right,
      inner_smul_right, inner_smul_right, S.eigenbasis.orthonormal.inner_eq_zero hij]
    simp [inner_self_eq_norm_sq_to_K, S.eigenbasis.orthonormal.norm_eq_one]
  have hn := norm_inner_le_norm (𝕜 := ℂ) (S.eigenbasis i)
    (S.operator (S.eigenbasis i) - S.operator (S.eigenbasis j))
  rw [hi, S.eigenbasis.orthonormal.norm_eq_one, one_mul] at hn
  simpa [dist_eq_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (S.basisEigenvalue_pos i)] using hn

/-- Compactness excludes infinitely many orthonormal eigenvectors above a
positive spectral threshold, including repetitions within an eigenspace. -/
lemma finite_basisEigenvalue_ge (ε : ℝ) (hε : 0 < ε) :
    {i : S.eigenbasisIndex | ε ≤ S.basisEigenvalue i}.Finite := by
  by_contra hf
  let A := {i : S.eigenbasisIndex | ε ≤ S.basisEigenvalue i}
  have hA : A.Infinite := hf
  let f : ℕ ↪ A := hA.natEmbedding A
  obtain ⟨K, hK, hsub⟩ := S.compact.image_closedBall_subset_compact 1
  have hmem (n : ℕ) : S.operator (S.eigenbasis (f n).val) ∈ K := by
    apply hsub
    refine ⟨S.eigenbasis (f n).val, ?_, rfl⟩
    simp [Metric.mem_closedBall, dist_zero_right, S.eigenbasis.orthonormal.norm_eq_one]
  obtain ⟨x, _, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hc := hlim.cauchySeq
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc ε hε
  have hdist := hN N (le_refl N) (N + 1) (by omega)
  have hne : (f (φ N)).val ≠ (f (φ (N + 1))).val := by
    intro he
    have he' := f.injective (Subtype.ext he)
    have := hφ.injective he'
    omega
  have hl := S.basisEigenvalue_le_dist hne
  have heps : ε ≤ S.basisEigenvalue (f (φ N)).val := (f (φ N)).property
  exact (not_lt_of_ge (heps.trans hl)) hdist

/-- Eigenvalues vanish along the cofinite filter on the basis index; no
infinite-sector enumeration has been assumed. -/
lemma basisEigenvalue_tendsto_zero :
    Filter.Tendsto S.basisEigenvalue Filter.cofinite (nhds 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  apply Filter.eventually_cofinite.mpr
  convert S.finite_basisEigenvalue_ge ε hε using 1
  ext i
  simp [dist_zero_right, Real.norm_eq_abs, abs_of_pos (S.basisEigenvalue_pos i)]

/-- Separability of the spectral index is a consequence, not an assumption. -/
lemma eigenbasisIndex_countable : Countable S.eigenbasisIndex := by
  have h := S.basisEigenvalue_tendsto_zero.countable_compl_preimage_ker
  have hn (i : S.eigenbasisIndex) : S.basisEigenvalue i ≠ 0 :=
    ne_of_gt (S.basisEigenvalue_pos i)
  simpa [ker_nhds, Set.preimage, hn, Set.countable_univ_iff] using h

/-- Every nonempty selection of basis indices has a largest eigenvalue.
This supplies the successive choices needed for ordering, with repetitions. -/
lemma exists_max_basisEigenvalue (A : Set S.eigenbasisIndex) (hA : A.Nonempty) :
    ∃ i ∈ A, ∀ j ∈ A, S.basisEigenvalue j ≤ S.basisEigenvalue i := by
  classical
  obtain ⟨k, hk⟩ := hA
  let F := {i | i ∈ A ∧ S.basisEigenvalue k ≤ S.basisEigenvalue i}
  have hF : F.Finite := (S.finite_basisEigenvalue_ge _ (S.basisEigenvalue_pos k)).subset
    (fun i hi => hi.2)
  have hkF : k ∈ hF.toFinset := by simp [F, hk]
  obtain ⟨i, hi, hmax⟩ := hF.toFinset.exists_max_image S.basisEigenvalue ⟨k, hkF⟩
  have hiF : i ∈ F := hF.mem_toFinset.mp hi
  refine ⟨i, hiF.1, fun j hj => ?_⟩
  by_cases hkj : S.basisEigenvalue k ≤ S.basisEigenvalue j
  · exact hmax j (hF.mem_toFinset.mpr ⟨hj, hkj⟩)
  · exact (le_of_not_ge hkj).trans hiF.2

end KsIndex.Spectral.PositiveCompactSolution
