module

public import KsIndexLean.InvariantHermitianHull

@[expose] public section


noncomputable section
namespace KsIndex.InvariantHermitian
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

lemma negativeSpectralSpace_coordinate_zero (T : Module.End ℂ H) (hT : T.IsSymmetric)
    (i : Fin (Module.finrank ℂ H)) (hi : 0 ≤ hT.eigenvalues rfl i)
    {u : H} (hu : u ∈ negativeSpectralSpace T) :
    (hT.eigenvectorBasis rfl).repr u i = 0 := by
  have hle : negativeSpectralSpace T ≤ ((hT.eigenvectorBasis rfl).toBasis.coord i).ker := by
    apply iSup_le
    intro μ v hv
    change (hT.eigenvectorBasis rfl).repr v i = 0
    have he := hT.eigenvectorBasis_apply_self_apply rfl v i
    rw [Module.End.mem_eigenspace_iff.mp hv, map_smul] at he
    change (μ.val : ℂ) * (hT.eigenvectorBasis rfl).repr v i =
      (hT.eigenvalues rfl i : ℂ) * (hT.eigenvectorBasis rfl).repr v i at he
    by_contra hn
    have heq := mul_right_cancel₀ hn he
    have hr : μ.val = hT.eigenvalues rfl i := Complex.ofReal_injective heq
    exact (not_lt_of_ge (hr ▸ hi)) μ.property
  exact hle hu

lemma negativeSpectralSpace_negative (T : Module.End ℂ H) (hT : T.IsSymmetric)
    {u : H} (hu : u ∈ negativeSpectralSpace T) (hne : u ≠ 0) :
    (inner ℂ u (T u)).re < 0 := by
  classical
  let b := hT.eigenvectorBasis rfl
  have hex : ∃ i, b.repr u i ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hne
    apply b.repr.injective
    ext i
    simpa using hn i
  obtain ⟨i, hi⟩ := hex
  have hneg : hT.eigenvalues rfl i < 0 := by
    by_contra hn
    exact hi (negativeSpectralSpace_coordinate_zero T hT i (le_of_not_gt hn) hu)
  rw [symmetric_energy_spectral_sum T hT]
  apply Finset.sum_neg'
  · intro j hj
    by_cases h : hT.eigenvalues rfl j < 0
    · exact mul_nonpos_of_nonpos_of_nonneg h.le (sq_nonneg _)
    · rw [negativeSpectralSpace_coordinate_zero T hT j (le_of_not_gt h) hu]
      simp
  · exact ⟨i, Finset.mem_univ _, mul_neg_of_neg_of_pos hneg (sq_pos_of_pos (norm_pos_iff.mpr hi))⟩

lemma negative_eigenvector_mem (T : Module.End ℂ H) (hT : T.IsSymmetric)
    (i : Fin (Module.finrank ℂ H)) (hi : hT.eigenvalues rfl i < 0) :
    hT.eigenvectorBasis rfl i ∈ negativeSpectralSpace T := by
  apply (le_iSup (fun μ : {r : ℝ // r < 0} => Module.End.eigenspace T (μ.val : ℂ))
    ⟨hT.eigenvalues rfl i, hi⟩)
  exact Module.End.mem_eigenspace_iff.mpr (hT.apply_eigenvectorBasis rfl i)

lemma spectral_count_le_negativeSpectralSpace_finrank (T : Module.End ℂ H)
    (hT : T.IsSymmetric) :
    Fintype.card {i : Fin (Module.finrank ℂ H) // hT.eigenvalues rfl i < 0} ≤
      Module.finrank ℂ (negativeSpectralSpace T) := by
  classical
  let v : {i : Fin (Module.finrank ℂ H) // hT.eigenvalues rfl i < 0} →
      negativeSpectralSpace T := fun i =>
    ⟨hT.eigenvectorBasis rfl i.val, negative_eigenvector_mem T hT i.val i.property⟩
  have hbase : LinearIndependent ℂ (hT.eigenvectorBasis rfl) :=
    (hT.eigenvectorBasis rfl).orthonormal.linearIndependent
  have hb : LinearIndependent ℂ (fun i : {i : Fin (Module.finrank ℂ H) //
      hT.eigenvalues rfl i < 0} => hT.eigenvectorBasis rfl i.val) :=
    hbase.comp (Subtype.val : {i : Fin (Module.finrank ℂ H) //
      hT.eigenvalues rfl i < 0} → Fin (Module.finrank ℂ H)) Subtype.val_injective
  have h : LinearIndependent ℂ v :=
    LinearIndependent.of_comp (negativeSpectralSpace T).subtype hb
  exact h.fintype_card_le_finrank

lemma negative_trial_finrank_le_negativeSpectralSpace (T : Module.End ℂ H)
    (hT : T.IsSymmetric) (X : Submodule ℂ H)
    (hX : ∀ u : X, u ≠ 0 → (inner ℂ u.val (T u.val)).re < 0) :
    Module.finrank ℂ X ≤ Module.finrank ℂ (negativeSpectralSpace T) :=
  (negative_trial_finrank_le_spectral_count T hT X hX).trans
    (spectral_count_le_negativeSpectralSpace_finrank T hT)

end KsIndex.InvariantHermitian
