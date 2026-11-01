module

/-
Named propositions for the paper's two index/nullity formulas on the disk-chain
model of `Surface.lean`. These definitions specify statements; they are not
axioms or proofs. The corresponding formulas are proved downstream in
`D5Discharge`, `GeneralCapstone`, `K3IndexComplete`, and `PaperChainNullityExact`.

The model invariants are distinct from the geometric invariants on the EW
quotient. `KarcherGeometricInvariants` proves their equality, and
`KarcherGeometricCapstone` gives the resulting geometric theorems, including
existence of a realization from the EW data. No surface-uniqueness claim is
made by these model propositions or those realization theorems.

For k >= 3 the two-period formulas are index 4k - 3 and nullity 3. For the
six-ended family, the positive-period index is 6m - 4 floor(m alphaStar) - 3,
and nullity is 7 at integral m alphaStar and 3 otherwise.
`Theorem_k3_model` names the concrete `Staircase.alphaStar`;
`Theorem_k3_paper` retains the paper's existential threshold in (1/3, 1/2),
while still using the model carrier. The final lemma converts the concrete
statement to that existential form using the proved threshold bracket.
-/
public import KsIndexLean.Surface
public import KsIndexLean.Staircase

@[expose] public section


noncomputable section

namespace KsIndex.SurfaceTargets

open KsIndex.Surface KsIndex.Staircase

/-- **Theorem m=2, model-level statement.** -/
def Theorem_m2 : Prop :=
  ∀ k : ℕ, 3 ≤ k → indSurface k 2 = ((4 * k - 3 : ℕ) : ℕ∞) ∧ nulSurface k 2 = 3

open Classical in
/-- **Theorem k=3, model-level statement with the concrete threshold** `Staircase.alphaStar`
(stronger than the paper's ∃-form: it names the threshold). -/
def Theorem_k3_model : Prop :=
  ∀ m : ℕ, ∀ [NeZero m],
    indSurface 3 m = ((6 * m - 4 * ⌊(m : ℝ) * alphaStar⌋₊ - 3 : ℕ) : ℕ∞)
      ∧ nulSurface 3 m = (if ∃ n : ℤ, (m : ℝ) * alphaStar = n then 7 else 3)

@[deprecated Theorem_k3_model (since := "2026-09-07")] alias Theorem_k3 := Theorem_k3_model

open Classical in
/-- The existential threshold formulation of "Quotients with six ends", over the model:
there exists a threshold `α* ∈ (1/3, 1/2)` governing the staircase and the nullity
dichotomy. -/
def Theorem_k3_paper : Prop :=
  ∃ a : ℝ, a ∈ Set.Ioo (1/3 : ℝ) (1/2 : ℝ) ∧
    ∀ m : ℕ, ∀ [NeZero m],
      indSurface 3 m = ((6 * m - 4 * ⌊(m : ℝ) * a⌋₊ - 3 : ℕ) : ℕ∞)
        ∧ nulSurface 3 m = (if ∃ n : ℤ, (m : ℝ) * a = n then 7 else 3)

/-- The concrete model statement delivers the paper's ∃-form: witness `alphaStar`, whose
bracket `alphaStar ∈ (1/3, 1/2)` is proved (`alphaStar_mem_Ioo`). -/
theorem Theorem_k3_paper_of_model (h : Theorem_k3_model) : Theorem_k3_paper :=
  ⟨alphaStar, alphaStar_mem_Ioo, h⟩

end KsIndex.SurfaceTargets
