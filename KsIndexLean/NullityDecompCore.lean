module

public import KsIndexLean.Surface
public import KsIndexLean.SurfaceSym
public import KsIndexLean.CharDecomp

@[expose] public section


/-!
# Rank, zero-form nullity, and copy reflections

`formNullity_zero_eq_rank` identifies the nullity of the zero form on a submodule
`D` with `Cardinal.toENat (Module.rank ℂ D)`. For this form, `NullOn` reduces to
subspace containment. The proof treats both finite-dimensional and infinite-rank
spaces; in the latter case finite-dimensional subspaces have arbitrarily large
rank. This algebraic identity allows rank decompositions to use the form-nullity
character decomposition theorem.

`reflE m c` acts on functions by precomposition with `(n, w) ↦ (c - n, w)`.
It is an involution, leaves the complex coordinate unchanged, and commutes with
`rotE`, which acts on that coordinate. The lemma `reflE_comm` proves commutation
of two copy reflections under the hypothesis `2 * (c - c') = 0` in `ZMod (2 * m)`.
For `m = 2` and `c, c' ∈ {1, -1}` this hypothesis holds. An even difference alone
is not the required condition for general `m`.

The composition `reflE m 1 (reflE m (-1) U)` evaluates `U` at copy `n - 2`.
For four copies this agrees with `n + 2`. Preservation of bounded Jacobi fields
and the resulting sector decomposition are established in separate modules.
-/

noncomputable section
namespace KsIndex.NullityDecomp
open KsIndex.Surface KsIndex.SurfaceSym KsIndex.FormIndex Complex

/-! ### The zero form -/

/-- The zero form is a `Sesq` on any domain. -/
lemma sesq_zero {ι : Type*} (D : Submodule ℂ (ι → ℂ)) :
    Sesq (fun _ => (0 : ℝ)) (fun _ _ => (0 : ℂ)) D := by
  constructor <;> intros <;> simp

/-- With the zero form, `NullOn` is just containment. -/
lemma nullOn_zero_iff {ι : Type*} (D V : Submodule ℂ (ι → ℂ)) :
    NullOn (fun _ _ => (0 : ℂ)) D V ↔ V ≤ D :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ _ _ _ => rfl⟩⟩

/-- **The zero-form bridge**: `formNullity` of the zero form is the rank, as an `ℕ∞`. -/
lemma formNullity_zero_eq_rank {ι : Type*} (D : Submodule ℂ (ι → ℂ)) :
    formNullity (fun _ _ => (0 : ℂ)) D = Cardinal.toENat (Module.rank ℂ D) := by
  classical
  apply le_antisymm
  · refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfin => ?_
    have hle : Module.rank ℂ ↥V ≤ Module.rank ℂ ↥D := Submodule.rank_mono hV.1
    have hV' : (Module.finrank ℂ ↥V : Cardinal) = Module.rank ℂ ↥V :=
      Module.finrank_eq_rank ℂ ↥V
    have h1 : (Module.finrank ℂ ↥V : ℕ∞) = Cardinal.toENat (Module.rank ℂ ↥V) := by
      rw [← hV']; simp
    rw [h1]
    exact Cardinal.toENat.monotone' hle
  · by_cases hfd : FiniteDimensional ℂ ↥D
    · have hD : (Module.finrank ℂ ↥D : Cardinal) = Module.rank ℂ ↥D :=
        Module.finrank_eq_rank ℂ ↥D
      have h1 : Cardinal.toENat (Module.rank ℂ ↥D) = (Module.finrank ℂ ↥D : ℕ∞) := by
        rw [← hD]; simp
      rw [h1]
      exact le_iSup_of_le D (le_iSup_of_le ((nullOn_zero_iff D D).mpr le_rfl)
        (le_iSup (fun _ : FiniteDimensional ℂ ↥D => (Module.finrank ℂ ↥D : ℕ∞)) hfd))
    · -- infinite rank: the right side is `⊤`, and the supremum dominates every `n : ℕ`
      have hrank : Cardinal.aleph0 ≤ Module.rank ℂ ↥D := by
        by_contra hlt
        exact hfd (Module.rank_lt_aleph0_iff.mp (lt_of_not_ge hlt))
      have hsup : ∀ n : ℕ, (n : ℕ∞) ≤ formNullity (fun _ _ => (0 : ℂ)) D := by
        intro n
        have hn : (n : Cardinal) ≤ Module.rank ℂ ↥D :=
          le_trans Cardinal.natCast_lt_aleph0.le hrank
        obtain ⟨s, hcard, hs⟩ := le_rank_iff_exists_linearIndependent_finset.mp hn
        -- span inside `↥D`, then push into the ambient space by `D.subtype`
        have hV₀rank : Module.finrank ℂ ↥(Submodule.span ℂ (s : Set ↥D)) = n := by
          rw [finrank_span_finset_eq_card hs, hcard]
        have hV₀fin : FiniteDimensional ℂ ↥(Submodule.span ℂ (s : Set ↥D)) :=
          FiniteDimensional.span_finset ℂ s
        set V : Submodule ℂ (ι → ℂ) :=
          (Submodule.span ℂ (s : Set ↥D)).map D.subtype with hVdef
        have hVle : V ≤ D := Submodule.map_subtype_le D _
        have hVfin : FiniteDimensional ℂ ↥V := by
          rw [hVdef]
          exact Module.Finite.map _ _
        have hVrank : Module.finrank ℂ ↥V = n := by
          rw [hVdef, Submodule.finrank_map_subtype_eq, hV₀rank]
        calc (n : ℕ∞) = (Module.finrank ℂ ↥V : ℕ∞) := by rw [hVrank]
          _ ≤ _ := le_iSup_of_le V (le_iSup_of_le ((nullOn_zero_iff D V).mpr hVle)
              (le_iSup (fun _ : FiniteDimensional ℂ ↥V => (Module.finrank ℂ ↥V : ℕ∞)) hVfin))
      have htop : formNullity (fun _ _ => (0 : ℂ)) D = ⊤ := by
        by_contra hne
        lift formNullity (fun _ _ => (0 : ℂ)) D to ℕ using hne with M hM
        have h1 := hsup (M + 1)
        have h2 : (M + 1 : ℕ) ≤ M := by exact_mod_cast h1
        omega
      rw [htop]
      exact le_top

/-! ### The seam reflections -/

/-- Copy reflection by precomposition with `(n, w) ↦ (c - n, w)`, with no change
to the complex coordinate and no scalar factor. -/
def reflE (m : ℕ) (c : ZMod (2 * m)) : Module.End ℂ (ZMod (2 * m) × ℂ → ℂ) where
  toFun U := fun p => U (c - p.1, p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma reflE_apply (m : ℕ) (c : ZMod (2 * m)) (U : ZMod (2 * m) × ℂ → ℂ)
    (p : ZMod (2 * m) × ℂ) : reflE m c U p = U (c - p.1, p.2) := rfl

/-- `reflE` is an involution. -/
lemma reflE_reflE (m : ℕ) (c : ZMod (2 * m)) (U : ZMod (2 * m) × ℂ → ℂ) :
    reflE m c (reflE m c U) = U := by
  funext p
  simp only [reflE_apply, sub_sub_cancel]

/-- `(reflE m c)^2 = 1` pointwise — the shape the decomposition engine consumes. -/
lemma reflE_sq (m : ℕ) (c : ZMod (2 * m)) (U : ZMod (2 * m) × ℂ → ℂ) :
    ((reflE m c) ^ 2) U = U := by
  rw [pow_two, Module.End.mul_apply, reflE_reflE]

/-- Two copy reflections commute if `2(c − c') = 0`: for `c, c' ∈ {±1}` we have `c − c' ∈ {0, ±2}` and `2·(±2) = ±4 = 0`
in `ZMod 4`. -/
lemma reflE_comm (m : ℕ) (c c' : ZMod (2 * m)) (h : 2 * (c - c') = 0)
    (U : ZMod (2 * m) × ℂ → ℂ) :
    reflE m c (reflE m c' U) = reflE m c' (reflE m c U) := by
  funext p
  simp only [reflE_apply]
  have hx : c' - (c - p.1) = c - (c' - p.1) := by linear_combination -h
  rw [hx]

/-- Composition in this order evaluates the field at `n - 2`. On `ZMod 4`, this
also equals evaluation at `n + 2`. -/
lemma reflE_one_comp_reflE_neg_one (m : ℕ) (U : ZMod (2 * m) × ℂ → ℂ)
    (p : ZMod (2 * m) × ℂ) :
    reflE m 1 (reflE m (-1) U) p = U (p.1 - 2, p.2) := by
  simp only [reflE_apply]
  have hx : (-1 : ZMod (2 * m)) - (1 - p.1) = p.1 - 2 := by ring
  rw [hx]

/-- The reflections commute with the rotation — they act on disjoint coordinates. -/
lemma reflE_rotE_comm (m : ℕ) (c : ZMod (2 * m)) (a : ℂ) (U : ZMod (2 * m) × ℂ → ℂ) :
    reflE m c (rotE m a U) = rotE m a (reflE m c U) := rfl

end KsIndex.NullityDecomp
