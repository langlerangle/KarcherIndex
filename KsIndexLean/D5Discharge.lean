module

public import KsIndexLean.D5DensityAssembly
public import KsIndexLean.D5CapstoneRefl
public import KsIndexLean.NaturalCoreForm
public import KsIndexLean.FormIndexDensity
public import KsIndexLean.D5IndexTransport

@[expose] public section


/-!
# Equality of encoding indices and the m = 2 surface index

For each sector `(b₁, b₀, r)`, the natural and reflected compact cores have form
index equal to the negative index of `weakJacobi (surfacePotential k)` on the
same space `mixedCharacterDomain k r b₁ b₀`. The proof applies
`formIndex_eq_of_dense_form_map` to the two dense maps from `D5DensityAssembly`,
using their form identities.

These equalities prove `ReflEncodingDensity k` for `k ≥ 2`. Consequently,
`indSurface k 2 = 4k − 3` for `k ≥ 3` without an encoding-density assumption.
This module supplies the index formula, not a nullity formula.
-/

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.SingleDisk KsIndex.SingleDiskBridge KsIndex.FormIndex

variable {k : ℕ}



/-! ### Equality of encoding indices -/

/-- `ReflEncodingDensity` holds for `k ≥ 2`: both core form indices equal
the negative index of the same mixed weak sector. -/
theorem reflEncodingDensity_holds (hk : 2 ≤ k) :
    KsIndex.TwistSwap.ReflEncodingDensity k := fun b₁ b₀ r =>
  (reflSeam_eq_negativeIndex hk r b₁ b₀).trans
    (seamNat_eq_negativeIndex hk r b₁ b₀).symm

/-! ### The unconditional capstone -/

/-- The m=2 surface index: `ind(Ξ_{k,2}) = 4k − 3` for
every `k ≥ 3` — no encoding hypothesis.  [ksindexi] §1/§5, index half. -/
theorem indSurface_two_val_final (hk : 3 ≤ k) :
    KsIndex.Surface.indSurface k 2 = ((4 * k - 3 : ℕ) : ℕ∞) :=
  KsIndex.Capstone.indSurface_two_val_refl hk
    (reflEncodingDensity_holds (by omega))

/-- The ∀-`k` packaging of the unconditional m=2 index theorem. -/
theorem theorem_m2_index_final :
    ∀ k, 3 ≤ k → KsIndex.Surface.indSurface k 2 = ((4 * k - 3 : ℕ) : ℕ∞) :=
  fun _ hk => indSurface_two_val_final hk

end KsIndex.Trace
