module

/-
KsIndexLean — ComplexH1ConjugationSlit: complex conjugation on `DiskPairH1` and its
action on the arc trace, the slit domain, and the paper-slit character domain.

Lifts `conjH1` (ComplexH1Conjugation) to `conjPairH1` on `DiskPairH1 = ComplexH1 × ComplexH1`
and threads it through the boundary structures of the `k = 3` slit adapter:

* `arcTrace_conjH1` : conjugation is `star` on each arc trace (via `diskTraceCLM_conjH1`).
* `conjPairH1_mem_slitTrace` / `conjPairH1_mem_paperSlitDomain` : conjugation maps the slit domain
  to its conjugate phase, `exp(2πiα) ↦ exp(-2πiα)`, i.e. `paperSlitDomain α ↦ paperSlitDomain (-α)`.
* `conjPairH1_mem_pairCharacter` : conjugation maps the character eigenvalue `c ↦ conj c`.

These assemble with `conj_zeta_three` into `conjSlitEquiv`, which exchanges
characters 1 and 2 while sending the phase `α` to `-α`.
-/
public import KsIndexLean.ComplexH1ConjugationCovariance

@[expose] public section


noncomputable section
open scoped Real
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 TauCeti KsIndex.FormIndex

/-- `star` is conjugate-linear on any complex `L²` (proven pointwise; `StarModule` is not a
registered instance for `Lp`). -/
lemma star_smul_Lp {α : Type*} {m : MeasurableSpace α} {μ : Measure α} (c : ℂ) (f : Lp ℂ 2 μ) :
    star (c • f) = (starRingEnd ℂ) c • star f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (c • f), Lp.coeFn_smul c f,
    Lp.coeFn_smul ((starRingEnd ℂ) c) (star f), Lp.coeFn_star f] with x h1 h2 h3 h4
  simp only [h1, h2, h3, h4, Pi.star_apply, Pi.smul_apply, smul_eq_mul, map_mul,
    Complex.star_def]

/-- **`boundaryRestrict` commutes with `star`.** -/
lemma boundaryRestrict_star (A : Set Circle₁) (f : Lp ℂ 2 circleMeasure) :
    boundaryRestrict A (star f) = star (boundaryRestrict A f) := by
  apply Lp.ext
  filter_upwards [boundaryRestrict_coe_ae A (star f),
    (Lp.coeFn_star f).filter_mono (ae_mono (Measure.restrict_le_self (s := A))),
    Lp.coeFn_star (boundaryRestrict A f), boundaryRestrict_coe_ae A f] with w h1 h2 h3 h4
  simp only [h1, h2, h3, h4, Pi.star_apply]

/-- **`arcTrace` covariance:** conjugation on `ComplexH1` is `star` on the arc trace. -/
lemma arcTrace_conjH1 (A : Set Circle₁) (u : ComplexH1) :
    arcTrace A (conjH1 u) = star (arcTrace A u) := by
  change boundaryRestrict A (diskTraceCLM (conjH1 u)) = star (boundaryRestrict A (diskTraceCLM u))
  rw [diskTraceCLM_conjH1, boundaryRestrict_star]

/-- **Complex conjugation on `DiskPairH1`, componentwise.** -/
def conjPairH1 : DiskPairH1 ≃ₛₗ[starRingEnd ℂ] DiskPairH1 where
  toFun u := (conjH1 u.1, conjH1 u.2)
  invFun u := (conjH1 u.1, conjH1 u.2)
  left_inv u := Prod.ext (conjMap_involutive u.1) (conjMap_involutive u.2)
  right_inv u := Prod.ext (conjMap_involutive u.1) (conjMap_involutive u.2)
  map_add' u v := by
    refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add, map_add]
  map_smul' c u := by
    refine Prod.ext ?_ ?_ <;> simp only [Prod.smul_fst, Prod.smul_snd, map_smulₛₗ]

@[simp] lemma conjPairH1_fst (u : DiskPairH1) : (conjPairH1 u).1 = conjH1 u.1 := rfl
@[simp] lemma conjPairH1_snd (u : DiskPairH1) : (conjPairH1 u).2 = conjH1 u.2 := rfl

/-- **Conjugation maps the pair character domain to its conjugate eigenvalue.** -/
lemma conjPairH1_mem_pairCharacter (θ : ℝ) (c : ℂ) {u : DiskPairH1}
    (hu : u ∈ pairCharacterDomain θ c) :
    conjPairH1 u ∈ pairCharacterDomain θ ((starRingEnd ℂ) c) := by
  rw [pairCharacterDomain, Submodule.mem_inf, Submodule.mem_comap, Submodule.mem_comap] at hu ⊢
  exact ⟨conjH1_mem_weakCharacter θ c hu.1, conjH1_mem_weakCharacter θ c hu.2⟩

/-- **Conjugation maps the slit domain to its conjugate phase.** -/
lemma conjPairH1_mem_slitTrace (k : ℕ) (phase : ℂ) {u : DiskPairH1}
    (hu : u ∈ slitTraceDomain k phase) :
    conjPairH1 u ∈ slitTraceDomain k ((starRingEnd ℂ) phase) := by
  rw [mem_slitTraceDomain] at hu ⊢
  obtain ⟨h1, h2⟩ := hu
  refine ⟨?_, ?_⟩
  · change arcTrace (boundaryArc k 1) (conjH1 u.1) = arcTrace (boundaryArc k 1) (conjH1 u.2)
    rw [arcTrace_conjH1, arcTrace_conjH1, h1]
  · change arcTrace (boundaryArc k 0) (conjH1 u.1)
        = (starRingEnd ℂ) phase • arcTrace (boundaryArc k 0) (conjH1 u.2)
    rw [arcTrace_conjH1, arcTrace_conjH1, h2, star_smul_Lp]

/-- The paper slit phase, in the exact form used by `paperSlitDomain`. -/
def paperSlitPhase (α : ℝ) : ℂ := Complex.exp ((2 * Real.pi * α) * Complex.I)

lemma paperSlitDomain_eq (α : ℝ) : paperSlitDomain α = slitTraceDomain 3 (paperSlitPhase α) := rfl

/-- The slit phase `exp((2πα)i)` conjugates to `exp((2π(-α))i)`. -/
lemma conj_paperSlitPhase (α : ℝ) :
    (starRingEnd ℂ) (paperSlitPhase α) = paperSlitPhase (-α) := by
  unfold paperSlitPhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- **Conjugation maps `paperSlitDomain α` to `paperSlitDomain (-α)`.** -/
lemma conjPairH1_mem_paperSlitDomain (α : ℝ) {u : DiskPairH1} (hu : u ∈ paperSlitDomain α) :
    conjPairH1 u ∈ paperSlitDomain (-α) := by
  rw [paperSlitDomain_eq] at hu ⊢
  have h := conjPairH1_mem_slitTrace 3 (paperSlitPhase α) hu
  rwa [conj_paperSlitPhase] at h

/-! ### The `j ≡ 1 ↔ j ≡ 2` domain equivalence -/

/-- `conj (zeta 3 ^ 2) = zeta 3` (via `xi 3 ^ 2 = zeta 3`). -/
lemma conj_zeta_three_sq : (starRingEnd ℂ) (zeta 3 ^ 2) = zeta 3 := by
  rw [map_pow]; exact xi_three_sq

lemma conjPairH1_involutive (u : DiskPairH1) : conjPairH1 (conjPairH1 u) = u :=
  Prod.ext (conjMap_involutive u.1) (conjMap_involutive u.2)

/-- **Conjugation maps the `j ≡ 1` character domain onto the `j ≡ 2` one** (`α ↦ -α`,
`zeta 3 ↦ zeta 3 ^ 2`). -/
lemma conjPairH1_mem_paperSlitCharacter (α : ℝ) {u : DiskPairH1}
    (hu : u ∈ paperSlitCharacterDomain α 1) :
    conjPairH1 u ∈ paperSlitCharacterDomain (-α) 2 := by
  rw [paperSlitCharacterDomain, Submodule.mem_inf] at hu ⊢
  refine ⟨conjPairH1_mem_paperSlitDomain α hu.1, ?_⟩
  have hc := conjPairH1_mem_pairCharacter (-(2 * Real.pi) / 3) (zeta 3 ^ 1) hu.2
  rwa [pow_one, conj_zeta_three] at hc

/-- **Reverse:** conjugation maps the `j ≡ 2` character domain onto the `j ≡ 1` one. -/
lemma conjPairH1_mem_paperSlitCharacter_rev (α : ℝ) {u : DiskPairH1}
    (hu : u ∈ paperSlitCharacterDomain α 2) :
    conjPairH1 u ∈ paperSlitCharacterDomain (-α) 1 := by
  rw [paperSlitCharacterDomain, Submodule.mem_inf] at hu ⊢
  refine ⟨conjPairH1_mem_paperSlitDomain α hu.1, ?_⟩
  have hc := conjPairH1_mem_pairCharacter (-(2 * Real.pi) / 3) (zeta 3 ^ 2) hu.2
  rwa [conj_zeta_three_sq, ← pow_one (zeta 3)] at hc

/-- **The conjugation equivalence:** complex conjugation as a conjugate-linear equivalence
`paperSlitCharacterDomain α 1 ≃ₛₗ paperSlitCharacterDomain (-α) 2`. -/
def conjSlitEquiv (α : ℝ) :
    paperSlitCharacterDomain α 1 ≃ₛₗ[starRingEnd ℂ] paperSlitCharacterDomain (-α) 2 where
  toFun u := ⟨conjPairH1 u.val, conjPairH1_mem_paperSlitCharacter α u.property⟩
  invFun v := ⟨conjPairH1 v.val, by
    have h := conjPairH1_mem_paperSlitCharacter_rev (-α) v.property
    rwa [neg_neg] at h⟩
  left_inv u := Subtype.ext (conjPairH1_involutive u.val)
  right_inv v := Subtype.ext (conjPairH1_involutive v.val)
  map_add' u v := Subtype.ext (map_add conjPairH1 u.val v.val)
  map_smul' c u := Subtype.ext (map_smulₛₗ conjPairH1 c u.val)

@[simp] lemma conjSlitEquiv_apply_val (α : ℝ) (u : paperSlitCharacterDomain α 1) :
    ((conjSlitEquiv α u : paperSlitCharacterDomain (-α) 2) : DiskPairH1) = conjPairH1 u.val := rfl

end KsIndex.Trace
