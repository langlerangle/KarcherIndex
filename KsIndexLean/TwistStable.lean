module

/-
Boundary-continuous twisted domains and index-preserving linear maps.

`DomTw k ζ` does not by itself fix the raw values of each copy on the seam
circle. A swap can move such a value into a glued expression whose smoothness
depends on its boundary value. `DomTw_c := DomTw ⊓ BdyCont` adds continuity
of every copy on the closed disk, tying those circle values to interior limits.

This file defines that subdomain and proves an abstract index-comparison lemma.
A linear map from `D` into `D' ≤ D` that preserves `Q`, with `Q 0 = 0`, gives
equal form indices. No identity-on-`D'` or global injectivity hypothesis is
needed: preservation of `Q` forces injectivity on negative subspaces.
Constructing a boundary-limit map and proving swap stability are separate
applications of these definitions and the comparison lemma.
-/
public import KsIndexLean.TwistSwap

@[expose] public section


noncomputable section

open Complex MeasureTheory Metric
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SurfaceSym KsIndex.Bracket KsIndex.Twisted
  KsIndex.FormIndex KsIndex.GradOrtho

namespace KsIndex.TwistSwap

/-! ### The abstract retraction lemma -/

/-- **Index is preserved by a form-preserving linear map into a subdomain.**  If `T : ↥D →ₗ[ℂ] (ι→ℂ)` maps `D` into
a subdomain `D' ≤ D`, and preserves `Q`, then `formIndex Q D = formIndex Q D'`.

`T` need only be linear on `D` (as a type), and it is used injectively only on `Q`-negative
subspaces — where injectivity follows from `Q`-preservation (`T x = 0 ⟹ Q x = Q(T x) = Q 0 = 0`,
impossible for a nonzero vector of a negative-definite subspace).  So a boundary-limit retraction
that is NOT injective on all of `D` (it collapses differing unpinned circle values) still works. -/
theorem formIndex_eq_of_retraction {ι : Type*} {Q : (ι → ℂ) → ℝ} (hQ0 : Q 0 = 0)
    {D D' : Submodule ℂ (ι → ℂ)} (hD'D : D' ≤ D) (T : ↥D →ₗ[ℂ] (ι → ℂ))
    (hTmem : ∀ u : ↥D, T u ∈ D') (hTQ : ∀ u : ↥D, Q (T u) = Q (u : ι → ℂ)) :
    formIndex Q D = formIndex Q D' := by
  refine le_antisymm ?_ (formIndex_mono hD'D)
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfd => ?_
  have := hfd
  have hVD : V ≤ D := hV.1
  set φ : ↥V →ₗ[ℂ] (ι → ℂ) := T.comp (Submodule.inclusion hVD) with hφ
  have hφapp : ∀ x : ↥V, φ x = T (Submodule.inclusion hVD x) := fun _ => rfl
  have hQφ : ∀ x : ↥V, Q (φ x) = Q (x : ι → ℂ) := fun x => by rw [hφapp, hTQ]; rfl
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    have hx0 : φ x = 0 := LinearMap.mem_ker.mp hx
    have hQx : Q (x : ι → ℂ) = 0 := by rw [← hQφ x, hx0, hQ0]
    by_contra hxne
    have hxc : (x : ι → ℂ) ≠ 0 := fun h => hxne (Submodule.coe_eq_zero.mp h)
    exact absurd hQx (ne_of_lt (hV.2 (x : ι → ℂ) x.2 hxc))
  have hequiv : ↥V ≃ₗ[ℂ] ↥(LinearMap.range φ) := LinearEquiv.ofInjective φ hφinj
  have : FiniteDimensional ℂ ↥(LinearMap.range φ) := Module.Finite.equiv hequiv
  have hWD' : LinearMap.range φ ≤ D' := by
    rintro w ⟨x, rfl⟩; rw [hφapp]; exact hTmem _
  have hWneg : ∀ w ∈ LinearMap.range φ, w ≠ 0 → Q w < 0 := by
    rintro w ⟨x, rfl⟩ hwne
    rw [hQφ x]
    have hxne : (x : ι → ℂ) ≠ 0 := fun h => hwne (by rw [Submodule.coe_eq_zero.mp h, map_zero])
    exact hV.2 (x : ι → ℂ) x.2 hxne
  have hfr : (Module.finrank ℂ V : ℕ∞) = Module.finrank ℂ ↥(LinearMap.range φ) := by
    rw [hequiv.finrank_eq]
  rw [hfr]
  unfold formIndex
  exact le_iSup₂_of_le (LinearMap.range φ) ⟨hWD', hWneg⟩ (le_iSup_of_le ‹_› le_rfl)

/-! ### The boundary-continuous twisted subdomain -/

/-- Uncurried families whose copies are continuous up to the closed disk (boundary circle). -/
def BdyCont : Submodule ℂ (ZMod (2 * 1) × ℂ → ℂ) where
  carrier := {U | ∀ n : ZMod (2 * 1), ContinuousOn (fun w => U (n, w)) (closedBall 0 1)}
  zero_mem' := fun _ => continuousOn_const
  add_mem' := fun hU hV n => (hU n).add (hV n)
  smul_mem' := fun c _ hU n => (hU n).const_smul c

lemma mem_BdyCont {U : ZMod (2 * 1) × ℂ → ℂ} :
    U ∈ BdyCont ↔ ∀ n : ZMod (2 * 1), ContinuousOn (fun w => U (n, w)) (closedBall 0 1) :=
  Iff.rfl

/-- The twisted domain with every copy continuous on the closed disk.
The additional condition ties raw circle values to their interior limits. -/
def DomTw_c (k : ℕ) (ζ : ℂ) : Submodule ℂ (ZMod (2 * 1) × ℂ → ℂ) := DomTw k ζ ⊓ BdyCont

lemma DomTw_c_le_DomTw (k : ℕ) (ζ : ℂ) : DomTw_c k ζ ≤ DomTw k ζ := inf_le_left

end KsIndex.TwistSwap
