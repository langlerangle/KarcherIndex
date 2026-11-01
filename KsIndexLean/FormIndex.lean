module

/-
# Variational index and radical nullity on a function space

For a domain submodule `D ≤ (ι → ℂ)`, `formIndex Q D` is the supremum of the
dimensions of finite-dimensional subspaces on which `Q` is strictly negative
away from zero. `formNullity B D` is the analogous supremum for subspaces in
the radical: each vector pairs to zero under `B` with every vector of `D`.
Both counts take values in `ℕ∞`; the definitions do not require an operator
realization or a spectral theorem.

Finite-coordinate bounds follow by restricting a nonpositive subspace to a
finite set of coordinates. If a vector vanishing there has positive energy
unless it is zero, restriction is injective on the subspace. The more general
`formIndex_le_of_domMap` allows arbitrary finite families of linear functionals,
including boundary-trace Fourier coefficients, and needs only nonnegativity
on the map's kernel to bound the negative index.

The joint index-plus-nullity bound additionally uses a Hermitian pairing whose
diagonal is `Q` and which is additive in both slots on the domain. Scaling a
real form by a positive constant preserves its index; scaling the pairing by
a nonzero constant preserves its radical nullity.

`formIndex_le_of_negMap` compares indices across different coordinate spaces.
Its hypotheses control the target domain, negative vectors and the kernel.
It is an index comparison, not a nullity-transport theorem. Applications to
circle and surface forms supply their own domain and form identities.
-/
public import Mathlib

@[expose] public section


noncomputable section

namespace KsIndex.FormIndex

open Classical

variable {ι : Type*}

/-! ### Negative and radical subspaces and their dimension counts -/

/-- A subspace of the domain `D` on which the real form `Q` is negative
definite (strictly negative away from `0`). -/
def NegOn (Q : (ι → ℂ) → ℝ) (D V : Submodule ℂ (ι → ℂ)) : Prop :=
  V ≤ D ∧ ∀ u ∈ V, u ≠ 0 → Q u < 0

/-- A subspace of the domain `D` lying in the radical of the Hermitian form
`B`: every vector pairs to `0` with every domain element. -/
def NullOn (B : (ι → ℂ) → (ι → ℂ) → ℂ) (D V : Submodule ℂ (ι → ℂ)) : Prop :=
  V ≤ D ∧ ∀ u ∈ V, ∀ v : ι → ℂ, v ∈ D → B u v = 0

/-- The Morse index of `Q` on `D`: the supremum of `finrank` over
finite-dimensional `Q`-negative subspaces of `D`. -/
def formIndex (Q : (ι → ℂ) → ℝ) (D : Submodule ℂ (ι → ℂ)) : ℕ∞ :=
  ⨆ (V : Submodule ℂ (ι → ℂ)) (_ : NegOn Q D V) (_ : FiniteDimensional ℂ V),
    (Module.finrank ℂ V : ℕ∞)

/-- The nullity of `B` on `D`: the supremum of `finrank` over
finite-dimensional radical subspaces of `D`. -/
def formNullity (B : (ι → ℂ) → (ι → ℂ) → ℂ) (D : Submodule ℂ (ι → ℂ)) : ℕ∞ :=
  ⨆ (V : Submodule ℂ (ι → ℂ)) (_ : NullOn B D V) (_ : FiniteDimensional ℂ V),
    (Module.finrank ℂ V : ℕ∞)

/-! ### The head-coordinate engine -/

/-- **The generic head-coordinate bound.**  If every nonzero domain vector
that vanishes on a finite coordinate set `F` has strictly positive `Q`-energy,
then any `Q`-nonpositive subspace of the domain has dimension at most `F.card`.

Mechanism: the restriction-to-`F` map `V → (F → ℂ)` has trivial kernel (a
nonzero kernel vector would be a nonzero domain vector vanishing on `F`, hence
`Q`-positive, contradicting nonpositivity), so `finrank V ≤ finrank (F → ℂ) =
F.card`. -/
lemma finrank_le_card_of_nonpos
    {Q : (ι → ℂ) → ℝ} {D : Submodule ℂ (ι → ℂ)} {F : Finset ι}
    (hpos : ∀ u ∈ D, (∀ i ∈ F, u i = 0) → (∃ i, u i ≠ 0) → 0 < Q u)
    {W : Submodule ℂ (ι → ℂ)} [FiniteDimensional ℂ W]
    (hle : W ≤ D) (hW : ∀ u ∈ W, Q u ≤ 0) :
    Module.finrank ℂ W ≤ F.card := by
  classical
  set φ : ↥W →ₗ[ℂ] (↥F → ℂ) :=
    (LinearMap.pi fun i : ↥F => LinearMap.proj (i : ι)).comp W.subtype with hφ
  have hker : LinearMap.ker φ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    by_contra hxne
    have hzero : φ x = 0 := LinearMap.mem_ker.mp hx
    have hcoord : ∀ i ∈ F, (x : ι → ℂ) i = 0 := by
      intro i hi
      have hj := congrFun hzero ⟨i, hi⟩
      simpa [hφ, LinearMap.pi_apply, LinearMap.proj_apply] using hj
    have hxc : (x : ι → ℂ) ≠ 0 := fun h => hxne (Submodule.coe_eq_zero.mp h)
    have hex : ∃ i, (x : ι → ℂ) i ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hxc
      exact ⟨i, by simpa using hi⟩
    have hpos' := hpos (x : ι → ℂ) (hle x.2) hcoord hex
    have hnp := hW (x : ι → ℂ) x.2
    linarith
  have hinj : Function.Injective φ := LinearMap.ker_eq_bot.mp hker
  have hcard : Module.finrank ℂ (↥F → ℂ) = F.card := by
    rw [Module.finrank_pi, Fintype.card_coe]
  calc Module.finrank ℂ W
      ≤ Module.finrank ℂ (↥F → ℂ) := LinearMap.finrank_le_finrank_of_injective hinj
    _ = F.card := hcard

/-- The index is bounded by the head-set cardinality. -/
theorem formIndex_le_card {Q : (ι → ℂ) → ℝ} {D : Submodule ℂ (ι → ℂ)}
    {F : Finset ι} (hQ0 : Q 0 = 0)
    (hpos : ∀ u ∈ D, (∀ i ∈ F, u i = 0) → (∃ i, u i ≠ 0) → 0 < Q u) :
    formIndex Q D ≤ F.card := by
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfd => ?_
  have := hfd
  have hnp : ∀ u ∈ V, Q u ≤ 0 := by
    intro u hu
    rcases eq_or_ne u 0 with rfl | hne
    · exact le_of_eq hQ0
    · exact le_of_lt (hV.2 u hu hne)
  exact_mod_cast finrank_le_card_of_nonpos hpos hV.1 hnp

/-- **Index bound via a coordinate-trace map.**  If there is a `ℂ`-linear map `T` from the domain
`D` (as a type) to a finite coordinate space `idx → ℂ` such that `Q` is nonnegative on every
domain vector killed by `T`, then the index is at most `card idx`.

Mechanism: on a `Q`-negative subspace `V ≤ D`, the composite `T ∘ (V ↪ D)` is injective — a
nonzero kernel vector would be `Q`-negative (from `V`) yet `Q`-nonnegative (from `hnn`) — so
`finrank V ≤ finrank (idx → ℂ) = card idx`.  This generalizes `formIndex_le_card` (there `T` is
restriction to the head coordinates `F`), the flexibility being that `T` may read any linear
functionals of the domain vector, not just its coordinates — e.g. boundary-trace Fourier
coefficients. -/
theorem formIndex_le_of_domMap {Q : (ι → ℂ) → ℝ} {D : Submodule ℂ (ι → ℂ)}
    {idx : Type*} [Fintype idx] (T : ↥D →ₗ[ℂ] (idx → ℂ))
    (hnn : ∀ u : ↥D, T u = 0 → 0 ≤ Q (u : ι → ℂ)) :
    formIndex Q D ≤ (Fintype.card idx : ℕ∞) := by
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfd => ?_
  have := hfd
  set ψ : ↥V →ₗ[ℂ] (idx → ℂ) := T.comp (Submodule.inclusion hV.1) with hψ
  have hker : LinearMap.ker ψ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    by_contra hxne
    have hT0 : T (Submodule.inclusion hV.1 x) = 0 := LinearMap.mem_ker.mp hx
    have hnn' : 0 ≤ Q ((x : ι → ℂ)) := by
      have h := hnn (Submodule.inclusion hV.1 x) hT0
      simpa using h
    have hxc : (x : ι → ℂ) ≠ 0 := fun h => hxne (Submodule.coe_eq_zero.mp h)
    have hneg := hV.2 (x : ι → ℂ) x.2 hxc
    linarith
  have hinj : Function.Injective ψ := LinearMap.ker_eq_bot.mp hker
  have hcard : Module.finrank ℂ (idx → ℂ) = Fintype.card idx := by
    rw [Module.finrank_pi]
  calc (Module.finrank ℂ V : ℕ∞)
      ≤ (Module.finrank ℂ (idx → ℂ) : ℕ∞) := by
        exact_mod_cast LinearMap.finrank_le_finrank_of_injective hinj
    _ = Fintype.card idx := by rw [hcard]

/-- The nullity is bounded by the head-set cardinality (a radical vector
`B`-pairs to `0` with itself, so `Q = B(·,·) = 0` on the subspace). -/
theorem formNullity_le_card {Q : (ι → ℂ) → ℝ} {B : (ι → ℂ) → (ι → ℂ) → ℂ}
    {D : Submodule ℂ (ι → ℂ)} {F : Finset ι}
    (hBself : ∀ u : ι → ℂ, B u u = (Q u : ℂ))
    (hpos : ∀ u ∈ D, (∀ i ∈ F, u i = 0) → (∃ i, u i ≠ 0) → 0 < Q u) :
    formNullity B D ≤ F.card := by
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfd => ?_
  have := hfd
  have hnp : ∀ u ∈ V, Q u ≤ 0 := by
    intro u hu
    have h0 : B u u = 0 := hV.2 u hu u (hV.1 hu)
    have : (Q u : ℂ) = 0 := by rw [← hBself u, h0]
    exact le_of_eq (Complex.ofReal_eq_zero.mp this)
  exact_mod_cast finrank_le_card_of_nonpos hpos hV.1 hnp

/-! ### Scaling invariance

The `R_α` reduction presents each eigenspace block as a POSITIVE scalar multiple
(`× 2`) of a transported `𝒬_s`; the Morse index and nullity are blind to that
factor.  These two lemmas record that (independent of any form model). -/

/-- Scaling the real form by a positive constant preserves the index. -/
theorem formIndex_smul_pos {Q : (ι → ℂ) → ℝ} {D : Submodule ℂ (ι → ℂ)} {c : ℝ}
    (hc : 0 < c) : formIndex (fun u => c * Q u) D = formIndex Q D := by
  have key : ∀ V, NegOn (fun u => c * Q u) D V ↔ NegOn Q D V := by
    intro V
    refine and_congr_right fun _ => forall₂_congr fun u _ => forall_congr' fun _ => ?_
    constructor <;> intro h <;> nlinarith [h]
  refine iSup_congr fun V => ?_
  rw [propext (key V)]

/-- Scaling the Hermitian form by a nonzero constant preserves the nullity. -/
theorem formNullity_smul_ne_zero {B : (ι → ℂ) → (ι → ℂ) → ℂ}
    {D : Submodule ℂ (ι → ℂ)} {c : ℂ} (hc : c ≠ 0) :
    formNullity (fun u v => c * B u v) D = formNullity B D := by
  have key : ∀ V, NullOn (fun u v => c * B u v) D V ↔ NullOn B D V := by
    intro V
    refine and_congr_right fun _ =>
      forall₂_congr fun u _ => forall₂_congr fun v _ => ?_
    rw [mul_eq_zero]
    exact or_iff_right hc
  refine iSup_congr fun V => ?_
  rw [propext (key V)]

/-! ### The joint bound `ind + nul ≤ card F` -/

/-- On the sum of a `Q`-negative subspace and a radical subspace, `Q` is
nonpositive: the radical component drops out of the energy.  Needs exactly the
sesquilinear structure of `B` (diagonal `= Q`, additive in both slots on `D`,
Hermitian). -/
lemma form_nonpos_on_sup {Q : (ι → ℂ) → ℝ} {B : (ι → ℂ) → (ι → ℂ) → ℂ}
    {D V₁ V₂ : Submodule ℂ (ι → ℂ)} (hQ0 : Q 0 = 0)
    (hBself : ∀ u : ι → ℂ, B u u = (Q u : ℂ))
    (hBaddL : ∀ {a b v : ι → ℂ}, a ∈ D → b ∈ D → v ∈ D →
      B (a + b) v = B a v + B b v)
    (hBaddR : ∀ {a v w : ι → ℂ}, a ∈ D → v ∈ D → w ∈ D →
      B a (v + w) = B a v + B a w)
    (hBconj : ∀ u v : ι → ℂ, B v u = (starRingEnd ℂ) (B u v))
    (h₁ : NegOn Q D V₁) (h₂ : NullOn B D V₂) :
    ∀ u ∈ V₁ ⊔ V₂, Q u ≤ 0 := by
  intro u hu
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
  have hd₁ : u₁ ∈ D := h₁.1 hu₁
  have hd₂ : u₂ ∈ D := h₂.1 hu₂
  have hd12 : u₁ + u₂ ∈ D := D.add_mem hd₁ hd₂
  have hnull := h₂.2 u₂ hu₂
  have h12 : B u₁ u₂ = 0 := by
    rw [hBconj u₂ u₁, hnull u₁ hd₁, map_zero]
  have key : (Q (u₁ + u₂) : ℂ) = (Q u₁ : ℂ) := by
    rw [← hBself, hBaddL hd₁ hd₂ hd12, hnull _ hd12, add_zero,
      hBaddR hd₁ hd₁ hd₂, h12, add_zero, hBself]
  have keyR : Q (u₁ + u₂) = Q u₁ := by exact_mod_cast key
  rw [keyR]
  rcases eq_or_ne u₁ 0 with rfl | hne
  · exact le_of_eq hQ0
  · exact le_of_lt (h₁.2 u₁ hu₁ hne)

/-- The joint bound at the finrank level: a `Q`-negative subspace and a radical
subspace intersect trivially (a shared nonzero vector would have `Q < 0` and
`Q = 0` at once), so their dimensions add along the sum, where `Q` is
nonpositive and the head bound applies. -/
lemma finrank_add_finrank_le_card {Q : (ι → ℂ) → ℝ} {B : (ι → ℂ) → (ι → ℂ) → ℂ}
    {D V₁ V₂ : Submodule ℂ (ι → ℂ)} {F : Finset ι} (hQ0 : Q 0 = 0)
    (hBself : ∀ u : ι → ℂ, B u u = (Q u : ℂ))
    (hBaddL : ∀ {a b v : ι → ℂ}, a ∈ D → b ∈ D → v ∈ D →
      B (a + b) v = B a v + B b v)
    (hBaddR : ∀ {a v w : ι → ℂ}, a ∈ D → v ∈ D → w ∈ D →
      B a (v + w) = B a v + B a w)
    (hBconj : ∀ u v : ι → ℂ, B v u = (starRingEnd ℂ) (B u v))
    (hpos : ∀ u ∈ D, (∀ i ∈ F, u i = 0) → (∃ i, u i ≠ 0) → 0 < Q u)
    (h₁ : NegOn Q D V₁) (h₂ : NullOn B D V₂)
    [FiniteDimensional ℂ V₁] [FiniteDimensional ℂ V₂] :
    Module.finrank ℂ V₁ + Module.finrank ℂ V₂ ≤ F.card := by
  have hdisj : V₁ ⊓ V₂ = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨hu₁, hu₂⟩ := Submodule.mem_inf.mp hu
    rw [Submodule.mem_bot]
    by_contra hne
    have hneg := h₁.2 u hu₁ hne
    have h0 : B u u = 0 := h₂.2 u hu₂ u (h₁.1 hu₁)
    have hcast : (Q u : ℂ) = 0 := by rw [← hBself, h0]
    have := Complex.ofReal_eq_zero.mp hcast
    linarith
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq V₁ V₂
  rw [hdisj, finrank_bot] at hsum
  have hW : Module.finrank ℂ ↥(V₁ ⊔ V₂) ≤ F.card :=
    finrank_le_card_of_nonpos hpos (sup_le h₁.1 h₂.1)
      (form_nonpos_on_sup hQ0 hBself hBaddL hBaddR hBconj h₁ h₂)
  omega

/-- Rewrite of `formIndex` collapsing the finite-dimensionality condition into
the predicate, ready for `biSup_add_biSup_le'`. -/
lemma formIndex_eq_biSup (Q : (ι → ℂ) → ℝ) (D : Submodule ℂ (ι → ℂ)) :
    formIndex Q D
      = ⨆ (V : Submodule ℂ (ι → ℂ))
          (_ : NegOn Q D V ∧ FiniteDimensional ℂ V), (Module.finrank ℂ V : ℕ∞) := by
  refine iSup_congr fun _ => ?_
  rw [iSup_and]

lemma formNullity_eq_biSup (B : (ι → ℂ) → (ι → ℂ) → ℂ) (D : Submodule ℂ (ι → ℂ)) :
    formNullity B D
      = ⨆ (V : Submodule ℂ (ι → ℂ))
          (_ : NullOn B D V ∧ FiniteDimensional ℂ V), (Module.finrank ℂ V : ℕ∞) := by
  refine iSup_congr fun _ => ?_
  rw [iSup_and]

/-- **The generic `ind + nul ≤ card F` theorem.**  Specializes to the paper's
`qop_ind_plus_nul_above` at `F = {0}` and gives `ind(𝓝_α)+nul(𝓝_α) ≤ 2`
at the two-element sector-head set. -/
theorem formIndex_add_formNullity_le_card {Q : (ι → ℂ) → ℝ}
    {B : (ι → ℂ) → (ι → ℂ) → ℂ} {D : Submodule ℂ (ι → ℂ)} {F : Finset ι}
    (hQ0 : Q 0 = 0) (hBself : ∀ u : ι → ℂ, B u u = (Q u : ℂ))
    (hBaddL : ∀ {a b v : ι → ℂ}, a ∈ D → b ∈ D → v ∈ D →
      B (a + b) v = B a v + B b v)
    (hBaddR : ∀ {a v w : ι → ℂ}, a ∈ D → v ∈ D → w ∈ D →
      B a (v + w) = B a v + B a w)
    (hBconj : ∀ u v : ι → ℂ, B v u = (starRingEnd ℂ) (B u v))
    (hpos : ∀ u ∈ D, (∀ i ∈ F, u i = 0) → (∃ i, u i ≠ 0) → 0 < Q u) :
    formIndex Q D + formNullity B D ≤ F.card := by
  have hbot_neg : NegOn Q D ⊥ :=
    ⟨bot_le, fun u hu hune => absurd ((Submodule.mem_bot ℂ).mp hu) hune⟩
  have hbot_null : NullOn B D ⊥ := by
    refine ⟨bot_le, fun u hu v hv => ?_⟩
    rw [(Submodule.mem_bot ℂ).mp hu]
    have h := hBaddL D.zero_mem D.zero_mem hv
    rw [add_zero] at h
    linear_combination -h
  rw [formIndex_eq_biSup, formNullity_eq_biSup]
  refine ENat.biSup_add_biSup_le'
    ⟨⊥, hbot_neg, inferInstance⟩ ⟨⊥, hbot_null, inferInstance⟩ ?_
  rintro V₁ ⟨hV₁, hfd₁⟩ V₂ ⟨hV₂, hfd₂⟩
  have := hfd₁
  have := hfd₂
  exact_mod_cast finrank_add_finrank_le_card hQ0 hBself hBaddL hBaddR hBconj hpos
    hV₁ hV₂


/-- **Cross-index Morse-index comparison.**  A `ℂ`-linear map `T` from the domain `D` (as a type)
into another coordinate space `ι₂ → ℂ` that (i) lands in a second domain `D₂` (`hmem`), (ii) sends
`Q`-negative domain vectors to `Q₂`-negative images (`hneg`), and (iii) has a `Q`-nonnegative
kernel (`hker`) forces `formIndex Q D ≤ formIndex Q₂ D₂`.

Mechanism: on a `Q`-negative subspace `V ≤ D`, the composite `ψ = T ∘ (V ↪ D)` is injective (a
kernel vector is `Q`-nonnegative by `hker` yet `Q`-negative from `V`), so its image `range ψ` is a
`Q₂`-negative subspace of `D₂` of the same finite dimension as `V` — hence `finrank V ≤
formIndex Q₂ D₂`.  This is the ≤-half of `formIndex_eq_of_retraction`, freed from the requirement
that the two coordinate types agree (as needed for a boundary-trace map disk ⟶ circle). -/
theorem formIndex_le_of_negMap {ι ι₂ : Type*}
    {Q : (ι → ℂ) → ℝ} {D : Submodule ℂ (ι → ℂ)}
    {Q₂ : (ι₂ → ℂ) → ℝ} {D₂ : Submodule ℂ (ι₂ → ℂ)}
    (T : ↥D →ₗ[ℂ] (ι₂ → ℂ))
    (hmem : ∀ u : ↥D, T u ∈ D₂)
    (hneg : ∀ u : ↥D, Q (u : ι → ℂ) < 0 → Q₂ (T u) < 0)
    (hker : ∀ u : ↥D, T u = 0 → 0 ≤ Q (u : ι → ℂ)) :
    formIndex Q D ≤ formIndex Q₂ D₂ := by
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfd => ?_
  have : FiniteDimensional ℂ ↥V := hfd
  set ψ : ↥V →ₗ[ℂ] (ι₂ → ℂ) := T.comp (Submodule.inclusion hV.1) with hψ
  -- ψ is injective: a kernel vector is `Q`-nonnegative yet, if nonzero, `Q`-negative
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    by_contra hxne
    have hT0 : T (Submodule.inclusion hV.1 x) = 0 := LinearMap.mem_ker.mp hx
    have hnn : 0 ≤ Q ((x : ι → ℂ)) := by
      have h := hker (Submodule.inclusion hV.1 x) hT0
      simpa using h
    have hxc : (x : ι → ℂ) ≠ 0 := fun h => hxne (Submodule.coe_eq_zero.mp h)
    have hlt := hV.2 (x : ι → ℂ) x.2 hxc
    linarith
  -- the image is a `Q₂`-negative subspace of `D₂`, finite-dimensional, same rank as `V`
  set W : Submodule ℂ (ι₂ → ℂ) := LinearMap.range ψ with hW
  have hWle : W ≤ D₂ := by
    rintro y hy
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    exact hmem (Submodule.inclusion hV.1 x)
  have hWneg : NegOn Q₂ D₂ W := by
    refine ⟨hWle, ?_⟩
    intro w hw hwne
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hw
    have hxne : x ≠ 0 := by
      intro h; apply hwne; rw [h, map_zero]
    have hxc : (x : ι → ℂ) ≠ 0 := fun h => hxne (Submodule.coe_eq_zero.mp h)
    have hlt := hV.2 (x : ι → ℂ) x.2 hxc
    have := hneg (Submodule.inclusion hV.1 x) (by simpa using hlt)
    simpa [hψ] using this
  have hequiv := LinearEquiv.ofInjective ψ hinj
  have hWfd : FiniteDimensional ℂ ↥W := hequiv.finiteDimensional
  have heq : Module.finrank ℂ ↥V = Module.finrank ℂ ↥W := hequiv.finrank_eq
  calc (Module.finrank ℂ ↥V : ℕ∞)
      = (Module.finrank ℂ ↥W : ℕ∞) := by rw [heq]
    _ ≤ formIndex Q₂ D₂ :=
        le_iSup_of_le W (le_iSup_of_le hWneg (le_iSup_of_le hWfd le_rfl))

end KsIndex.FormIndex
