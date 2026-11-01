module

/-
Index and nullity of a diagonal form on its absolute-convergence domain.

For a real symbol `d : ι → ℝ`, `DomDiag d` consists of complex sequences
satisfying `Summable (fun i => |d i| * ‖u i‖ ^ 2)`. On this domain,
`Qdiag d` is the diagonal real form and `Bdiag d` its Hermitian pairing,
conjugate-linear in the first slot. Pairing summability follows from the
weighted arithmetic-geometric mean inequality.

If `{i | d i ≤ 0}` is finite, `formIndex_Qdiag` counts its strictly negative
entries and `formNullity_Bdiag` counts its zero entries. The proof combines
coordinate-subspace lower bounds with the joint index-plus-nullity upper
bound obtained from positivity outside that finite set.

The forms are defined using total `tsum` expressions on all sequences, but
the count theorems concern `DomDiag d`. No identification with a Sobolev,
Fourier, or geometric domain is automatic; applications must supply that
identification and the corresponding form equality separately.
-/
public import KsIndexLean.FormIndexDiag

@[expose] public section


noncomputable section

namespace KsIndex.DiagForm

open Classical KsIndex.FormIndex

variable {ι : Type*} [DecidableEq ι]

/-- Absolute-convergence membership: `∑ |d i| ‖u i‖² < ∞`. -/
def MemDiag (d : ι → ℝ) (u : ι → ℂ) : Prop :=
  Summable (fun i => |d i| * ‖u i‖ ^ 2)

/-- The diagonal real quadratic form `∑' d i ‖u i‖²`. -/
def Qdiag (d : ι → ℝ) (u : ι → ℂ) : ℝ := ∑' i, d i * ‖u i‖ ^ 2

/-- The polarized Hermitian form (conjugate-linear in the first slot). -/
def Bdiag (d : ι → ℝ) (u v : ι → ℂ) : ℂ := ∑' i, (d i : ℂ) * (starRingEnd ℂ) (u i) * v i

lemma memDiag_summable_signed {d : ι → ℝ} {u : ι → ℂ} (hu : MemDiag d u) :
    Summable (fun i => d i * ‖u i‖ ^ 2) := by
  rw [← summable_abs_iff]
  refine hu.congr fun i => ?_
  rw [abs_mul, abs_of_nonneg (sq_nonneg (‖u i‖))]

/-! ### The domain is a submodule -/

lemma memDiag_zero (d : ι → ℝ) : MemDiag d 0 :=
  summable_zero.congr fun i => by simp

lemma memDiag_smul (d : ι → ℝ) (c : ℂ) {u : ι → ℂ} (hu : MemDiag d u) : MemDiag d (c • u) := by
  refine (hu.mul_left (‖c‖ ^ 2)).congr fun i => ?_
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  ring

lemma memDiag_add (d : ι → ℝ) {u v : ι → ℂ} (hu : MemDiag d u) (hv : MemDiag d v) :
    MemDiag d (u + v) := by
  refine ((hu.add hv).mul_left 2).of_nonneg_of_le (fun i => by positivity) fun i => ?_
  have hX : ‖(u + v) i‖ ^ 2 ≤ 2 * ‖u i‖ ^ 2 + 2 * ‖v i‖ ^ 2 := by
    have h1 : ‖(u + v) i‖ ≤ ‖u i‖ + ‖v i‖ := by simpa only [Pi.add_apply] using norm_add_le _ _
    nlinarith [norm_nonneg ((u + v) i), norm_nonneg (u i), norm_nonneg (v i),
      sq_nonneg (‖u i‖ - ‖v i‖)]
  calc |d i| * ‖(u + v) i‖ ^ 2
      ≤ |d i| * (2 * ‖u i‖ ^ 2 + 2 * ‖v i‖ ^ 2) := mul_le_mul_of_nonneg_left hX (abs_nonneg _)
    _ = 2 * (|d i| * ‖u i‖ ^ 2 + |d i| * ‖v i‖ ^ 2) := by ring

/-- The absolute-convergence domain as a complex subspace of the full sequence space. -/
def DomDiag (d : ι → ℝ) : Submodule ℂ (ι → ℂ) where
  carrier := {u | MemDiag d u}
  zero_mem' := memDiag_zero d
  add_mem' hu hv := memDiag_add d hu hv
  smul_mem' c _ hu := memDiag_smul d c hu

lemma mem_DomDiag {d : ι → ℝ} {u : ι → ℂ} : u ∈ DomDiag d ↔ MemDiag d u := Iff.rfl

/-! ### The diagonal identity and sesquilinear structure -/

lemma Bdiag_self (d : ι → ℝ) (u : ι → ℂ) : Bdiag d u u = (Qdiag d u : ℂ) := by
  rw [Bdiag, Qdiag, Complex.ofReal_tsum]
  refine tsum_congr fun i => ?_
  rw [mul_assoc, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- Pairing summability from AM–GM. -/
lemma summable_pair {d : ι → ℝ} {u v : ι → ℂ} (hu : MemDiag d u) (hv : MemDiag d v) :
    Summable (fun i => (d i : ℂ) * (starRingEnd ℂ) (u i) * v i) := by
  apply Summable.of_norm
  refine ((hu.add hv).mul_left (1 / 2 : ℝ)).of_nonneg_of_le (fun i => by positivity) fun i => ?_
  rw [norm_mul, norm_mul, Complex.norm_real, RCLike.norm_conj, Real.norm_eq_abs]
  calc |d i| * ‖u i‖ * ‖v i‖
      ≤ |d i| * ((‖u i‖ ^ 2 + ‖v i‖ ^ 2) / 2) := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        nlinarith [sq_nonneg (‖u i‖ - ‖v i‖), norm_nonneg (u i), norm_nonneg (v i)]
    _ = 1 / 2 * (|d i| * ‖u i‖ ^ 2 + |d i| * ‖v i‖ ^ 2) := by ring

lemma Bdiag_add_left {d : ι → ℝ} {a b v : ι → ℂ} (ha : MemDiag d a) (hb : MemDiag d b)
    (hv : MemDiag d v) : Bdiag d (a + b) v = Bdiag d a v + Bdiag d b v := by
  rw [Bdiag, Bdiag, Bdiag, ← (summable_pair ha hv).tsum_add (summable_pair hb hv)]
  refine tsum_congr fun i => ?_
  simp only [Pi.add_apply, map_add]
  ring

lemma Bdiag_add_right {d : ι → ℝ} {a v w : ι → ℂ} (ha : MemDiag d a) (hv : MemDiag d v)
    (hw : MemDiag d w) : Bdiag d a (v + w) = Bdiag d a v + Bdiag d a w := by
  rw [Bdiag, Bdiag, Bdiag, ← (summable_pair ha hv).tsum_add (summable_pair ha hw)]
  refine tsum_congr fun i => ?_
  simp only [Pi.add_apply]
  ring

lemma Bdiag_conj (d : ι → ℝ) (u v : ι → ℂ) :
    Bdiag d v u = (starRingEnd ℂ) (Bdiag d u v) := by
  rw [Bdiag, Bdiag]
  show (∑' i, (d i : ℂ) * (starRingEnd ℂ) (v i) * u i)
      = star (∑' i, (d i : ℂ) * (starRingEnd ℂ) (u i) * v i)
  rw [tsum_star]
  refine tsum_congr fun i => ?_
  simp only [star_mul', Complex.star_def, Complex.conj_conj, Complex.conj_ofReal]
  ring

/-! ### The signature count -/

variable {d : ι → ℝ} (hfin : {i | d i ≤ 0}.Finite)

/-- The finite head set `{d ≤ 0}`. -/
def headFinset (hfin : {i | d i ≤ 0}.Finite) : Finset ι := hfin.toFinset

lemma mem_headFinset {hfin : {i | d i ≤ 0}.Finite} {i : ι} :
    i ∈ headFinset hfin ↔ d i ≤ 0 := by
  rw [headFinset, Set.Finite.mem_toFinset]; rfl

lemma negFinite (hfin : {i | d i ≤ 0}.Finite) : {i | d i < 0}.Finite :=
  hfin.subset fun i (hi : d i < 0) => (le_of_lt hi : d i ≤ 0)

lemma zeroFinite (hfin : {i | d i ≤ 0}.Finite) : {i | d i = 0}.Finite :=
  hfin.subset fun i (hi : d i = 0) => (le_of_eq hi : d i ≤ 0)

/-- `{d ≤ 0}` splits as the disjoint union of `{d < 0}` and `{d = 0}`. -/
lemma head_card_eq (hfin : {i | d i ≤ 0}.Finite) :
    (headFinset hfin).card = (negFinite hfin).toFinset.card + (zeroFinite hfin).toFinset.card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext i
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, mem_headFinset]
    constructor
    · intro h; rcases lt_or_eq_of_le h with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    · rintro (h | h)
      · exact le_of_lt h
      · exact le_of_eq h
  · rw [Finset.disjoint_left]
    intro i hi hj
    rw [Set.Finite.mem_toFinset] at hi hj
    exact absurd hj (ne_of_lt hi)

/-! Coordinate subspaces on `{d<0}` and `{d=0}` sit inside the domain. -/

lemma coordSpace_le_DomDiag (S : Finset ι) : coordSpace S ≤ DomDiag d := by
  intro u hu
  rw [mem_DomDiag]
  refine summable_of_ne_finset_zero (s := S) fun i hi => ?_
  rw [coordSpace_apply_eq_zero hu hi, norm_zero]
  simp

/-- `Qdiag` collapses to a finite sum on a coordinate subspace. -/
lemma Qdiag_eq_sum {S : Finset ι} {u : ι → ℂ} (hu : u ∈ coordSpace S) :
    Qdiag d u = ∑ i ∈ S, d i * ‖u i‖ ^ 2 := by
  rw [Qdiag]
  refine (hasSum_sum_of_ne_finset_zero (s := S) fun i hi => ?_).tsum_eq
  rw [coordSpace_apply_eq_zero hu hi, norm_zero]; simp

/-- On `coordSpace {d<0}` the form is negative definite. -/
lemma neg_on_neg_coord (hfin : {i | d i ≤ 0}.Finite) :
    ∀ u ∈ coordSpace (negFinite hfin).toFinset, u ≠ 0 → Qdiag d u < 0 := by
  intro u hu hune
  rw [Qdiag_eq_sum hu]
  have hmem : ∀ i ∈ (negFinite hfin).toFinset, d i < 0 := by
    intro i hi; rwa [Set.Finite.mem_toFinset] at hi
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hune
  have hi₀mem : i₀ ∈ (negFinite hfin).toFinset := by
    by_contra h
    exact hi₀ (by simpa using coordSpace_apply_eq_zero hu h)
  have hlt : ∑ i ∈ (negFinite hfin).toFinset, d i * ‖u i‖ ^ 2
      < ∑ _i ∈ (negFinite hfin).toFinset, (0 : ℝ) := by
    refine Finset.sum_lt_sum (fun i hi => ?_) ⟨i₀, hi₀mem, ?_⟩
    · exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt (hmem i hi)) (sq_nonneg _)
    · have : ‖u i₀‖ ^ 2 > 0 := by positivity
      exact mul_neg_of_neg_of_pos (hmem i₀ hi₀mem) this
  simpa using hlt

/-- On `coordSpace {d=0}` every vector is in the radical of `Bdiag`. -/
lemma null_on_zero_coord (hfin : {i | d i ≤ 0}.Finite) :
    ∀ u ∈ coordSpace (zeroFinite hfin).toFinset, ∀ v : ι → ℂ, v ∈ DomDiag d →
      Bdiag d u v = 0 := by
  intro u hu v _
  rw [Bdiag]
  have hzero : ∀ i, (d i : ℂ) * (starRingEnd ℂ) (u i) * v i = 0 := by
    intro i
    by_cases hi : i ∈ (zeroFinite hfin).toFinset
    · rw [Set.Finite.mem_toFinset] at hi
      rw [hi]; simp
    · rw [coordSpace_apply_eq_zero hu hi]; simp
  simp only [hzero, tsum_zero]

/-- Positivity off the head set: `Qdiag > 0` on nonzero domain vectors vanishing on `{d≤0}`. -/
lemma pos_off_head (hfin : {i | d i ≤ 0}.Finite) :
    ∀ u ∈ DomDiag d, (∀ i ∈ headFinset hfin, u i = 0) → (∃ i, u i ≠ 0) → 0 < Qdiag d u := by
  intro u hu hhead ⟨i₀, hi₀⟩
  have hi₀head : i₀ ∉ headFinset hfin := fun h => hi₀ (hhead i₀ h)
  have hi₀pos : 0 < d i₀ := by
    rw [mem_headFinset] at hi₀head; linarith [not_le.mp hi₀head]
  rw [Qdiag]
  refine (memDiag_summable_signed hu).tsum_pos (fun i => ?_) i₀ ?_
  · by_cases hi : i ∈ headFinset hfin
    · rw [hhead i hi, norm_zero]; simp
    · rw [mem_headFinset, not_le] at hi
      exact mul_nonneg (le_of_lt hi) (sq_nonneg _)
  · have : ‖u i₀‖ ^ 2 > 0 := by positivity
    exact mul_pos hi₀pos this

/-- **The diagonal index count**: `formIndex (Qdiag d) (DomDiag d) = #{d < 0}`. -/
theorem formIndex_Qdiag (hfin : {i | d i ≤ 0}.Finite) :
    formIndex (Qdiag d) (DomDiag d) = (negFinite hfin).toFinset.card := by
  have hlow : ((negFinite hfin).toFinset.card : ℕ∞) ≤ formIndex (Qdiag d) (DomDiag d) :=
    card_le_formIndex (coordSpace_le_DomDiag _) (neg_on_neg_coord hfin)
  have hup : formIndex (Qdiag d) (DomDiag d) + formNullity (Bdiag d) (DomDiag d)
      ≤ (headFinset hfin).card :=
    formIndex_add_formNullity_le_card (by simp [Qdiag]) (Bdiag_self d)
      (fun ha hb hv => Bdiag_add_left ha hb hv) (fun ha hv hw => Bdiag_add_right ha hv hw)
      (Bdiag_conj d) (pos_off_head hfin)
  have hznull : ((zeroFinite hfin).toFinset.card : ℕ∞) ≤ formNullity (Bdiag d) (DomDiag d) :=
    card_le_formNullity (coordSpace_le_DomDiag _) (null_on_zero_coord hfin)
  have hcard := head_card_eq hfin
  refine le_antisymm ?_ hlow
  have hzne : ((zeroFinite hfin).toFinset.card : ℕ∞) ≠ ⊤ := by simp
  have hchain : ((zeroFinite hfin).toFinset.card : ℕ∞) + formIndex (Qdiag d) (DomDiag d)
      ≤ (zeroFinite hfin).toFinset.card + (negFinite hfin).toFinset.card := by
    calc ((zeroFinite hfin).toFinset.card : ℕ∞) + formIndex (Qdiag d) (DomDiag d)
        = formIndex (Qdiag d) (DomDiag d) + (zeroFinite hfin).toFinset.card := by rw [add_comm]
      _ ≤ formIndex (Qdiag d) (DomDiag d) + formNullity (Bdiag d) (DomDiag d) :=
          add_le_add le_rfl hznull
      _ ≤ (headFinset hfin).card := hup
      _ = (negFinite hfin).toFinset.card + (zeroFinite hfin).toFinset.card := by
          rw [hcard]; push_cast; ring
      _ = (zeroFinite hfin).toFinset.card + (negFinite hfin).toFinset.card := by rw [add_comm]
  exact (ENat.add_le_add_iff_left hzne).mp hchain

/-- **The diagonal nullity count**: `formNullity (Bdiag d) (DomDiag d) = #{d = 0}`. -/
theorem formNullity_Bdiag (hfin : {i | d i ≤ 0}.Finite) :
    formNullity (Bdiag d) (DomDiag d) = (zeroFinite hfin).toFinset.card := by
  have hlow : ((zeroFinite hfin).toFinset.card : ℕ∞) ≤ formNullity (Bdiag d) (DomDiag d) :=
    card_le_formNullity (coordSpace_le_DomDiag _) (null_on_zero_coord hfin)
  have hup : formIndex (Qdiag d) (DomDiag d) + formNullity (Bdiag d) (DomDiag d)
      ≤ (headFinset hfin).card :=
    formIndex_add_formNullity_le_card (by simp [Qdiag]) (Bdiag_self d)
      (fun ha hb hv => Bdiag_add_left ha hb hv) (fun ha hv hw => Bdiag_add_right ha hv hw)
      (Bdiag_conj d) (pos_off_head hfin)
  have hineg : ((negFinite hfin).toFinset.card : ℕ∞) ≤ formIndex (Qdiag d) (DomDiag d) :=
    card_le_formIndex (coordSpace_le_DomDiag _) (neg_on_neg_coord hfin)
  have hcard := head_card_eq hfin
  refine le_antisymm ?_ hlow
  have hnne : ((negFinite hfin).toFinset.card : ℕ∞) ≠ ⊤ := by simp
  have hchain : ((negFinite hfin).toFinset.card : ℕ∞) + formNullity (Bdiag d) (DomDiag d)
      ≤ (negFinite hfin).toFinset.card + (zeroFinite hfin).toFinset.card := by
    calc ((negFinite hfin).toFinset.card : ℕ∞) + formNullity (Bdiag d) (DomDiag d)
        ≤ formIndex (Qdiag d) (DomDiag d) + formNullity (Bdiag d) (DomDiag d) :=
          add_le_add hineg le_rfl
      _ ≤ (headFinset hfin).card := hup
      _ = (negFinite hfin).toFinset.card + (zeroFinite hfin).toFinset.card := by
          rw [hcard]; push_cast; ring
  exact (ENat.add_le_add_iff_left hnne).mp hchain

end KsIndex.DiagForm
