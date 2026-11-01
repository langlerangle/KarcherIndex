module

/-
Single-disk Jacobi forms, rotation classes and a bundled counting interface.

`Qd k` is the disk Dirichlet energy minus the curvature potential energy.
`rot1 a` acts by precomposition with multiplication by `a`. The diagonal count
`neumannCount k c` restricts the nonzero DtN modes to one residue class by
assigning positive symbol values to all other modes.

`SeamBridge` packages four index identities for a supplied family of test
spaces and a supplied rotation subspace. Its pure-Neumann field includes the
additional zero-mode contribution in class zero. The pure-Dirichlet and common
mixed counts are parameters. Constructing this structure requires proofs of
all four identities; its declaration alone does not establish them or identify
the supplied test spaces with a geometric boundary-value problem.
-/
public import KsIndexLean.Bracket
public import KsIndexLean.DtNCircle
public import KsIndexLean.ArcMain

@[expose] public section


noncomputable section

open Complex KsIndex.Surface KsIndex.FormIndex KsIndex.DiagForm KsIndex.DtNCircle
  KsIndex.SurfaceSym KsIndex.ArcForm

namespace KsIndex.SingleDiskBridge

/-! ### The one-disk Jacobi form and the single-disk rotation -/

/-- The one-disk Jacobi form `‖∇_g f‖² − ‖|A|f‖²` on the single half period (index type `ι = ℂ`).
For symmetric or antisymmetric disk pairs, the corresponding two-copy energy
is twice this one-disk energy. -/
def Qd (k : ℕ) (f : ℂ → ℂ) : ℝ := dirichletG k f - potentialG k f

/-- The single-disk rotation `f ↦ f(a·)`, as a `ℂ`-linear endomorphism of `ℂ → ℂ`.  Its
`ζ_k^j`-eigenspace under `a = rotUnit k` is the class-`j` subspace of the single-disk problem. -/
def rot1 (a : ℂ) : Module.End ℂ (ℂ → ℂ) where
  toFun f := fun w => f (a * w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma rot1_apply (a : ℂ) (f : ℂ → ℂ) (w : ℂ) : rot1 a f w = f (a * w) := rfl

/-! ### The class-refined Neumann count -/

/-- The `dtnSymbol`, restricted to a residue class `c mod k`: off-class modes are given the value
`1 > 0` so they never enter the index.  (`NZ` = nonzero integers, the `Ḣ^{1/2}` mode index.) -/
def dtnSymbolClass (k : ℕ) (c : ZMod k) (ℓ : NZ) : ℝ :=
  if (ℓ.val : ZMod k) = c then dtnSymbol k ℓ else 1

/-- The diagonal DtN index restricted to the nonzero modes in residue class `c`.
Class-count identities and their hypotheses are supplied separately. -/
def neumannCount (k : ℕ) (c : ZMod k) : ℕ∞ :=
  formIndex (Qdiag (dtnSymbolClass k c)) (DomDiag (dtnSymbolClass k c))

/-! ### The four seam-bridge identities -/

/-- Four index identities for the supplied single-disk spaces and subspace `E`.

The Boolean arguments label the two arc conditions. In the geometric
application, `E` is a rotation eigenspace, `dCount` is the pure-Dirichlet count,
and `dnCount` is the common mixed count. Equality of the mixed indices is an
obligation encoded by the last two fields, not a consequence of the structure
declaration. The residue convention in `pureN` is explicitly `(j : ZMod k)`. -/
structure SeamBridge (k j : ℕ) (SingleCc : Bool → Bool → Submodule ℂ (ℂ → ℂ))
    (E : Submodule ℂ (ℂ → ℂ)) (dCount dnCount : ℕ∞) : Prop where
  /-- Pure Neumann (even across `arc_1`, Neumann on `arc_0`) = `ind_{N,j}(Ξ^{(0,π)})`. -/
  pureN : formIndex (Qd k) (SingleCc true true ⊓ E)
    = neumannCount k (j : ZMod k) + (if (j : ZMod k) = 0 then 1 else 0)
  /-- Pure Dirichlet (odd across `arc_1`, Dirichlet on `arc_0`) = `ind_{D,j}(Ξ^{(0,π)})`. -/
  pureD : formIndex (Qd k) (SingleCc false false ⊓ E) = dCount
  /-- Mixed `ind_{DN,j}` (odd across `arc_1`, Neumann on `arc_0`). -/
  mixedDN : formIndex (Qd k) (SingleCc false true ⊓ E) = dnCount
  /-- Mixed `ind_{DN',j}` (even across `arc_1`, Dirichlet on `arc_0`), with the same count as `mixedDN`. -/
  mixedDN' : formIndex (Qd k) (SingleCc true false ⊓ E) = dnCount

end KsIndex.SingleDiskBridge
