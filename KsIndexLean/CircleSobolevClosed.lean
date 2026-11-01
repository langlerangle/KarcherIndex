module

public import KsIndexLean.DNHalfTraceSpace

@[expose] public section


/-! Closed subspaces defined by Fourier support conditions.

At every real Sobolev order, physical Fourier coefficient evaluations are
continuous. Their kernels show that zero constant coefficient and support in
`-j+kℤ` define closed subspaces. The zero constant coefficient condition agrees
with mean zero whenever an integrable function realization is available.
-/
noncomputable section
namespace KsIndex.CircleSobolev

/-- Physical coefficient evaluation is continuous at every real order. -/
def coeffCLM (s : ℝ) (n : ℤ) : Space s →L[ℂ] ℂ :=
  (weight s n : ℂ)⁻¹ • lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n

@[simp] theorem coeffCLM_apply (s : ℝ) (n : ℤ) (u : Space s) :
    coeffCLM s n u = coeff s u n := rfl

theorem isClosed_dotted (s : ℝ) : IsClosed (dotted s : Set (Space s)) :=
  (coeffCLM s 0).isClosed_ker

theorem isClosed_character (s : ℝ) (j k : ℤ) :
    IsClosed (character s j k : Set (Space s)) := by
  have he : (character s j k : Set (Space s)) =
      ⋂ (n : ℤ) (_ : ¬ ∃ m : ℤ, n = -j + k * m),
        {u : Space s | coeff s u n = 0} := by
    ext u
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact mem_character s j k u
  rw [he]
  exact isClosed_iInter (fun n => isClosed_iInter (fun _ => (coeffCLM s n).isClosed_ker))

theorem isClosed_dnCharacterSpace (k : ℕ) (j : ℤ) :
    IsClosed (dnCharacterSpace k j : Set (Space (1 / 2 : ℝ))) :=
  (isClosed_dnSpace k).inter (isClosed_character _ _ _)

end KsIndex.CircleSobolev
