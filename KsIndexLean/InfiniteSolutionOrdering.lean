module

public import KsIndexLean.SolutionSpectralThreshold

@[expose] public section


noncomputable section
namespace KsIndex.Spectral.PositiveCompactSolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : KsIndex.Spectral.PositiveCompactSolution H) [Infinite S.eigenbasisIndex]

/-- A largest remaining eigenvalue exists outside any finite set of basis indices. -/
lemma exists_next (F : Finset S.eigenbasisIndex) :
    ∃ i, i ∉ F ∧ ∀ j, j ∉ F → S.basisEigenvalue j ≤ S.basisEigenvalue i := by
  apply S.exists_max_basisEigenvalue {i | i ∉ F}
  exact F.exists_notMem

/-- Choose an index of a largest eigenvalue outside the finite set. -/
def nextIndex (F : Finset S.eigenbasisIndex) : S.eigenbasisIndex :=
  (S.exists_next F).choose

private lemma nextIndex_spec (F : Finset S.eigenbasisIndex) :
    S.nextIndex F ∉ F ∧ ∀ j, j ∉ F → S.basisEigenvalue j ≤ S.basisEigenvalue (S.nextIndex F) :=
  (S.exists_next F).choose_spec

/-- The finite set of indices selected during the first n ordering steps. -/
def usedIndices : ℕ → Finset S.eigenbasisIndex
  | 0 => ∅
  | n + 1 => by classical exact insert (S.nextIndex (usedIndices n)) (usedIndices n)

/-- Successive largest remaining eigenvalue, retaining each basis vector once. -/
def orderedIndex (n : ℕ) : S.eigenbasisIndex := S.nextIndex (S.usedIndices n)

private lemma mem_usedIndices (i : S.eigenbasisIndex) (n : ℕ) :
    i ∈ S.usedIndices n ↔ ∃ m < n, S.orderedIndex m = i := by
  classical
  induction n with
  | zero => simp [usedIndices]
  | succ n ih =>
    simp only [usedIndices, Finset.mem_insert, ih]
    constructor
    · intro h
      rcases h with h | ⟨m, hm, he⟩
      · exact ⟨n, by omega, h.symm⟩
      · exact ⟨m, by omega, he⟩
    · rintro ⟨m, hm, he⟩
      by_cases hmn : m = n
      · left
        subst m
        exact he.symm
      · right
        exact ⟨m, by omega, he⟩

lemma orderedIndex_injective : Function.Injective S.orderedIndex := by
  intro m n he
  have hne (a b : ℕ) (hab : a < b) : S.orderedIndex a ≠ S.orderedIndex b := by
    intro h
    exact (S.nextIndex_spec (S.usedIndices b)).1
      ((S.mem_usedIndices _ b).mpr ⟨a, hab, h⟩)
  rcases lt_trichotomy m n with h | h | h
  · exact False.elim (hne m n h he)
  · exact h
  · exact False.elim (hne n m h he.symm)

lemma orderedIndex_eigenvalue_antitone : Antitone (fun n => S.basisEigenvalue (S.orderedIndex n)) := by
  intro m n hmn
  rcases eq_or_lt_of_le hmn with h | h
  · subst n
    exact le_refl _
  · apply (S.nextIndex_spec (S.usedIndices m)).2
    intro hn
    obtain ⟨k, hk, he⟩ := (S.mem_usedIndices _ m).mp hn
    have := S.orderedIndex_injective he
    omega

lemma orderedIndex_surjective : Function.Surjective S.orderedIndex := by
  intro i
  by_contra hi
  have hout (n : ℕ) : i ∉ S.usedIndices n := by
    intro hn
    obtain ⟨m, _, he⟩ := (S.mem_usedIndices i n).mp hn
    exact hi ⟨m, he⟩
  have hle (n : ℕ) : S.basisEigenvalue i ≤ S.basisEigenvalue (S.orderedIndex n) :=
    (S.nextIndex_spec (S.usedIndices n)).2 i (hout n)
  have hfin := S.finite_basisEigenvalue_ge _ (S.basisEigenvalue_pos i)
  have hr : Set.range S.orderedIndex ⊆ {j | S.basisEigenvalue i ≤ S.basisEigenvalue j} := by
    rintro j ⟨n, rfl⟩
    exact hle n
  exact (Set.infinite_range_of_injective S.orderedIndex_injective) (hfin.subset hr)

/-- Ordered enumeration is a bijection, so no eigenspace multiplicity is lost. -/
def orderedIndexEquiv : ℕ ≃ S.eigenbasisIndex :=
  Equiv.ofBijective S.orderedIndex ⟨S.orderedIndex_injective, S.orderedIndex_surjective⟩

/-- Decreasing infinite solution spectrum, one entry per complex basis vector. -/
def infiniteEigenvalues (n : ℕ) : ℝ := S.basisEigenvalue (S.orderedIndex n)

lemma infiniteEigenvalues_pos (n : ℕ) : 0 < S.infiniteEigenvalues n :=
  S.basisEigenvalue_pos _

lemma infiniteEigenvalues_antitone : Antitone S.infiniteEigenvalues :=
  S.orderedIndex_eigenvalue_antitone

lemma infiniteEigenvalues_tendsto_zero :
    Filter.Tendsto S.infiniteEigenvalues Filter.atTop (nhds 0) := by
  change Filter.Tendsto (fun n => S.basisEigenvalue (S.orderedIndex n)) Filter.atTop (nhds 0)
  have h := S.basisEigenvalue_tendsto_zero.comp S.orderedIndex_injective.tendsto_cofinite
  simpa only [Nat.cofinite_eq_atTop, infiniteEigenvalues, Function.comp_def] using h

/-- Increasing reciprocal-shift spectrum on an infinite sector. -/
def infiniteReciprocalShift (c : ℝ) (n : ℕ) : ℝ := (S.infiniteEigenvalues n)⁻¹ - c

lemma infiniteReciprocalShift_monotone (c : ℝ) : Monotone (S.infiniteReciprocalShift c) := by
  intro i j hij
  apply sub_le_sub_right
  exact (inv_le_inv₀ (S.infiniteEigenvalues_pos i) (S.infiniteEigenvalues_pos j)).mpr
    (S.infiniteEigenvalues_antitone hij)

lemma infiniteReciprocalShift_tendsto_atTop (c : ℝ) :
    Filter.Tendsto (S.infiniteReciprocalShift c) Filter.atTop Filter.atTop := by
  change Filter.Tendsto (fun n => (S.infiniteEigenvalues n)⁻¹ - c) Filter.atTop Filter.atTop
  have hpos : Filter.Tendsto S.infiniteEigenvalues Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨S.infiniteEigenvalues_tendsto_zero,
      Filter.Eventually.of_forall S.infiniteEigenvalues_pos⟩
  have h := Filter.tendsto_atTop_add_const_right Filter.atTop (-c)
    hpos.inv_tendsto_nhdsGT_zero
  simpa only [infiniteReciprocalShift, sub_eq_add_neg, Pi.inv_apply] using h

/-- Reordering all eigenbasis indices preserves density of their linear span. -/
lemma orderedBasis_dense :
    ⊤ ≤ (Submodule.span ℂ (Set.range (fun n => S.eigenbasis (S.orderedIndex n)))).topologicalClosure := by
  have hr : Set.range (fun n => S.eigenbasis (S.orderedIndex n)) = Set.range S.eigenbasis :=
    S.orderedIndex_surjective.range_comp S.eigenbasis
  rw [hr, S.eigenbasis.dense_span]

/-- Orthonormal Hilbert basis in spectral order, indexed by all natural numbers. -/
def infiniteEigenbasis : HilbertBasis ℕ ℂ H :=
  HilbertBasis.mk (S.eigenbasis.orthonormal.comp S.orderedIndex S.orderedIndex_injective)
    S.orderedBasis_dense

lemma infiniteEigenbasis_apply (n : ℕ) :
    S.infiniteEigenbasis n = S.eigenbasis (S.orderedIndex n) :=
  congrFun (HilbertBasis.coe_mk _ _) n

lemma infiniteEigenbasis_equation (n : ℕ) :
    S.operator (S.infiniteEigenbasis n) = (S.infiniteEigenvalues n : ℂ) • S.infiniteEigenbasis n := by
  rw [S.infiniteEigenbasis_apply]
  exact S.eigenbasis_equation _

omit [Infinite S.eigenbasisIndex] in
/-- An infinite-dimensional ambient sector has an infinite eigenbasis index.
Finite-dimensional sectors use the separate finite-list construction. -/
lemma eigenbasisIndex_infinite (hH : ¬ FiniteDimensional ℂ H) : Infinite S.eigenbasisIndex := by
  classical
  cases finite_or_infinite S.eigenbasisIndex with
  | inl hf =>
    let := hf
    let := Fintype.ofFinite S.eigenbasisIndex
    exact False.elim (hH S.eigenbasis.toOrthonormalBasis.toBasis.finiteDimensional_of_finite)
  | inr hi => exact hi

end KsIndex.Spectral.PositiveCompactSolution
