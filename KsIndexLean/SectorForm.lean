module

/-
KsIndexLean — SectorForm: the coefficient form for the α-shifted DtN operator.

On the `(2;3)` sector, represented by `Idx = ℤ ⊕ ℤ`, the diagonal DtN
symbol is `σ₃(ℓ) = (ℓ²-4)/|ℓ|`. The two half-lattices use `sigP` and
`sigM`. The pairing `bN3` is conjugate-linear in its first slot and
polarizes `Ndiag`; composing with `M_α` (`mulA`) gives `NBform` and its
real diagonal `NQform`.

These are coefficient-normalized forms: the paper's unnormalized circle
arclength pairing has the additional factor `2π`. The form here corresponds
to the sum of the DtN pairings of `u,v` and of `M_α u,M_α v`.

The module proves the Hermitian and sesquilinear identities on the indicated
domains, together with invariance under `R_α`. This invariance supplies the
orthogonality of the two eigenspaces used in `SectorReduce` and `SectorIndex`.
-/
public import KsIndexLean.Sector

@[expose] public section


noncomputable section

namespace KsIndex.SectorForm

open KsIndex.CircleQ KsIndex.SIsometry KsIndex.Sector

/-- Pointwise conjugation of a Hermitian pairing summand (local copy of the
`Statements` helper, to keep this file independent of the circle track). -/
lemma star_pair (σ : ℝ) (a b : ℂ) :
    star ((σ : ℂ) * ((starRingEnd ℂ) a * b))
      = (σ : ℂ) * ((starRingEnd ℂ) b * a) := by
  have h : star ((σ : ℂ) * ((starRingEnd ℂ) a * b))
      = (starRingEnd ℂ) ((σ : ℂ) * ((starRingEnd ℂ) a * b)) := rfl
  rw [h, map_mul, map_mul, Complex.conj_ofReal, starRingEnd_self_apply]
  ring

/-! ### The base pairing `⟨N₃ u, v⟩` -/

/-- The coefficient-normalized DtN pairing, conjugate-linear in the first
slot. On the diagonal it is `Ndiag`; the arclength pairing has a factor `2π`. -/
def bN3 (u v : Idx → ℂ) : ℂ :=
  (∑' n : ℤ, (sigP n : ℂ) * ((starRingEnd ℂ) (u (Sum.inl n)) * v (Sum.inl n)))
    + (∑' m : ℤ, (sigM m : ℂ) * ((starRingEnd ℂ) (u (Sum.inr m)) * v (Sum.inr m)))

/-- Absolute summability of the `+`-lattice pairing sum for two `H^{1/2}`
half-sequences (AM–GM against `|σ₃| ≤ 3|ℓ|`). -/
lemma summable_bN3P {u v : Idx → ℂ}
    (hu : Summable fun n : ℤ => |6 * (n : ℝ) + 1| * ‖u (Sum.inl n)‖ ^ 2)
    (hv : Summable fun n : ℤ => |6 * (n : ℝ) + 1| * ‖v (Sum.inl n)‖ ^ 2) :
    Summable fun n : ℤ =>
      (sigP n : ℂ) * ((starRingEnd ℂ) (u (Sum.inl n)) * v (Sum.inl n)) := by
  refine Summable.of_norm ?_
  refine ((hu.add hv).mul_left (3 / 2)).of_nonneg_of_le (fun n => norm_nonneg _)
    fun n => ?_
  have hσ := abs_sigP_le n
  have hn : ‖(sigP n : ℂ) * ((starRingEnd ℂ) (u (Sum.inl n)) * v (Sum.inl n))‖
      = |sigP n| * (‖u (Sum.inl n)‖ * ‖v (Sum.inl n)‖) := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, starRingEnd_apply,
      norm_star]
  rw [hn]
  nlinarith [sq_nonneg (‖u (Sum.inl n)‖ - ‖v (Sum.inl n)‖), norm_nonneg (u (Sum.inl n)),
    norm_nonneg (v (Sum.inl n)), abs_nonneg (6 * (n : ℝ) + 1), abs_nonneg (sigP n),
    mul_le_mul_of_nonneg_right hσ
      (mul_nonneg (norm_nonneg (u (Sum.inl n))) (norm_nonneg (v (Sum.inl n))))]

/-- Absolute summability of the `-`-lattice pairing sum. -/
lemma summable_bN3M {u v : Idx → ℂ}
    (hu : Summable fun m : ℤ => |6 * (m : ℝ) + 4| * ‖u (Sum.inr m)‖ ^ 2)
    (hv : Summable fun m : ℤ => |6 * (m : ℝ) + 4| * ‖v (Sum.inr m)‖ ^ 2) :
    Summable fun m : ℤ =>
      (sigM m : ℂ) * ((starRingEnd ℂ) (u (Sum.inr m)) * v (Sum.inr m)) := by
  refine Summable.of_norm ?_
  refine ((hu.add hv).mul_left (3 / 2)).of_nonneg_of_le (fun m => norm_nonneg _)
    fun m => ?_
  have hσ := abs_sigM_le m
  have hn : ‖(sigM m : ℂ) * ((starRingEnd ℂ) (u (Sum.inr m)) * v (Sum.inr m))‖
      = |sigM m| * (‖u (Sum.inr m)‖ * ‖v (Sum.inr m)‖) := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, starRingEnd_apply,
      norm_star]
  rw [hn]
  nlinarith [sq_nonneg (‖u (Sum.inr m)‖ - ‖v (Sum.inr m)‖), norm_nonneg (u (Sum.inr m)),
    norm_nonneg (v (Sum.inr m)), abs_nonneg (6 * (m : ℝ) + 4), abs_nonneg (sigM m),
    mul_le_mul_of_nonneg_right hσ
      (mul_nonneg (norm_nonneg (u (Sum.inr m))) (norm_nonneg (v (Sum.inr m))))]

/-- On the diagonal `⟨N₃ u, u⟩ = Ndiag u`: `bN3` polarizes `Ndiag`. -/
lemma bN3_self (u : Idx → ℂ) : bN3 u u = (Ndiag u : ℂ) := by
  have h1 : ∀ z : ℂ, (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [bN3, Ndiag, h1]
  push_cast [Complex.ofReal_tsum]
  ring

/-- Hermitian symmetry of `bN3` (unconditional; conjugation commutes with the
`tsum`s). -/
lemma bN3_conj_symm (u v : Idx → ℂ) : bN3 v u = (starRingEnd ℂ) (bN3 u v) := by
  rw [bN3, bN3, starRingEnd_apply, star_add, tsum_star, tsum_star]
  congr 1
  · exact tsum_congr fun n => (star_pair (sigP n) (u (Sum.inl n)) (v (Sum.inl n))).symm
  · exact tsum_congr fun m => (star_pair (sigM m) (u (Sum.inr m)) (v (Sum.inr m))).symm

/-- Additivity of `bN3` in the first slot, on the sector `H^{1/2}` domain. -/
lemma bN3_add_left {a b v : Idx → ℂ} (ha : MemSector a) (hb : MemSector b)
    (hv : MemSector v) : bN3 (a + b) v = bN3 a v + bN3 b v := by
  have e₁ := (summable_bN3P ha.1 hv.1).tsum_add (summable_bN3P hb.1 hv.1)
  have e₂ := (summable_bN3M ha.2 hv.2).tsum_add (summable_bN3M hb.2 hv.2)
  have hA : (∑' n : ℤ,
        (sigP n : ℂ) * ((starRingEnd ℂ) ((a + b) (Sum.inl n)) * v (Sum.inl n)))
      = (∑' n : ℤ, (sigP n : ℂ) * ((starRingEnd ℂ) (a (Sum.inl n)) * v (Sum.inl n)))
        + ∑' n : ℤ, (sigP n : ℂ) * ((starRingEnd ℂ) (b (Sum.inl n)) * v (Sum.inl n)) := by
    rw [← e₁]; exact tsum_congr fun n => by simp only [Pi.add_apply, map_add]; ring
  have hB : (∑' m : ℤ,
        (sigM m : ℂ) * ((starRingEnd ℂ) ((a + b) (Sum.inr m)) * v (Sum.inr m)))
      = (∑' m : ℤ, (sigM m : ℂ) * ((starRingEnd ℂ) (a (Sum.inr m)) * v (Sum.inr m)))
        + ∑' m : ℤ, (sigM m : ℂ) * ((starRingEnd ℂ) (b (Sum.inr m)) * v (Sum.inr m)) := by
    rw [← e₂]; exact tsum_congr fun m => by simp only [Pi.add_apply, map_add]; ring
  rw [bN3, bN3, bN3, hA, hB]; ring

/-! ### The α-shifted form `𝓝_{3,α}` -/

/-- The real quadratic form `𝓝_{3,α}(u,u) = ⟨N₃u,u⟩ + ⟨N₃ M_α u, M_α u⟩`
([ksindexi] l. 4073). -/
def NQform (α : ℝ) (u : Idx → ℂ) : ℝ := Ndiag u + Ndiag (mulA α u)

/-- The polarized Hermitian form `𝓝_{3,α}(u,v)`, by composition with `M_α`. -/
def NBform (α : ℝ) (u v : Idx → ℂ) : ℂ := bN3 u v + bN3 (mulA α u) (mulA α v)

lemma NQform_zero (α : ℝ) : NQform α (0 : Idx → ℂ) = 0 := by
  have hm : mulA α (0 : Idx → ℂ) = 0 := by simp [mulA, sgn_zero]
  have hN : Ndiag (0 : Idx → ℂ) = 0 := by simp [Ndiag]
  simp only [NQform, hm, hN, add_zero]

/-- On the diagonal the polarized form recovers `NQform`. -/
lemma NBform_self (α : ℝ) (u : Idx → ℂ) : NBform α u u = (NQform α u : ℂ) := by
  simp only [NBform, NQform, bN3_self, Complex.ofReal_add]

/-- Hermitian symmetry of `𝓝_{3,α}` (unconditional). -/
lemma NBform_conj_symm (α : ℝ) (u v : Idx → ℂ) :
    NBform α v u = (starRingEnd ℂ) (NBform α u v) := by
  simp only [NBform, map_add]
  rw [bN3_conj_symm u v, bN3_conj_symm (mulA α u) (mulA α v)]

/-- Additivity of `𝓝_{3,α}` in the first slot, on the domain `Domς`. -/
lemma NBform_add_left (α : ℝ) {a b v : Idx → ℂ}
    (ha : MemSectorς a) (hb : MemSectorς b) (hv : MemSectorς v) :
    NBform α (a + b) v = NBform α a v + NBform α b v := by
  have hMa : MemSectorς (mulA α a) := mulA_mem_Domς α ha
  have hMb : MemSectorς (mulA α b) := mulA_mem_Domς α hb
  have hMv : MemSectorς (mulA α v) := mulA_mem_Domς α hv
  simp only [NBform]
  rw [mulA_add α (memSector_sectorL2 ha.1) (memSector_sectorL2 hb.1),
    bN3_add_left ha.1 hb.1 hv.1, bN3_add_left hMa.1 hMb.1 hMv.1]
  ring

/-- Additivity of `𝓝_{3,α}` in the second slot (from the first via Hermitian
symmetry). -/
lemma NBform_add_right (α : ℝ) {a v w : Idx → ℂ}
    (ha : MemSectorς a) (hv : MemSectorς v) (hw : MemSectorς w) :
    NBform α a (v + w) = NBform α a v + NBform α a w := by
  rw [NBform_conj_symm α (v + w) a, NBform_add_left α hv hw ha, map_add,
    ← NBform_conj_symm α v a, ← NBform_conj_symm α w a]

/-! ### `R_α`-invariance of the form (the block-diagonality engine) -/

/-- `⟨N₃ Pu, Pv⟩ = ⟨N₃ u, v⟩`: the parity is a unitary of `bN3` (the `inr`
sign flips cancel in the conjugate-product; `N₃` is diagonal). -/
lemma bN3_parity (u v : Idx → ℂ) : bN3 (parity u) (parity v) = bN3 u v := by
  simp only [bN3, parity_inl, parity_inr, map_neg, neg_mul, mul_neg, neg_neg]

/-- `bN3` is invariant under simultaneous negation of both slots. -/
lemma bN3_neg_neg (a b : Idx → ℂ) : bN3 (-a) (-b) = bN3 a b := by
  simp only [bN3, Pi.neg_apply, map_neg, neg_mul, mul_neg, neg_neg]

/-- **`𝓝_α(R_α u, R_α v) = 𝓝_α(u,v)`** ([ksindexi] `rop_props`, l. 4463) — the
form-symmetry that makes `𝓝_α` block-diagonal on the `R_α`-eigenspaces.  Pure
algebra: `M_α† P = P M_α`, `M_α M_α† = I`, and the parity/negation invariance
of `bN3`; no self-adjointness. -/
lemma NBform_rop (α : ℝ) {u v : Idx → ℂ} (hu : SectorL2 u) (hv : SectorL2 v) :
    NBform α (rop α u) (rop α v) = NBform α u v := by
  have hru : rop α u = -parity (mulA α u) := by rw [rop, mulAdag_parity]
  have hrv : rop α v = -parity (mulA α v) := by rw [rop, mulAdag_parity]
  have hmru : mulA α (rop α u) = -parity u := by
    rw [rop, mulA_neg, mulA_mulAdag α (sectorL2_parity hu)]
  have hmrv : mulA α (rop α v) = -parity v := by
    rw [rop, mulA_neg, mulA_mulAdag α (sectorL2_parity hv)]
  rw [NBform, hmru, hmrv, hru, hrv, bN3_neg_neg, bN3_neg_neg, bN3_parity, bN3_parity,
    NBform]
  ring

/-- `bN3` is conjugate-linear in the first slot: negation pulls out (unconditional,
via `tsum_neg`). -/
lemma bN3_neg_left (u v : Idx → ℂ) : bN3 (-u) v = -(bN3 u v) := by
  simp only [bN3, Pi.neg_apply, map_neg, neg_mul, mul_neg, tsum_neg, neg_add]

/-- Negation in the first slot of `𝓝_α` (unconditional). -/
lemma NBform_neg_left (α : ℝ) (u v : Idx → ℂ) :
    NBform α (-u) v = -(NBform α u v) := by
  rw [NBform, mulA_neg, bN3_neg_left, bN3_neg_left, NBform, neg_add]

/-- `bN3` is conjugate-linear in the first slot: scalars pull out conjugated. -/
lemma bN3_smul_left (c : ℂ) (u v : Idx → ℂ) :
    bN3 (c • u) v = (starRingEnd ℂ) c * bN3 u v := by
  rw [bN3, bN3, mul_add, ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  · exact tsum_congr fun n => by simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring
  · exact tsum_congr fun m => by simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring

/-- `bN3` is linear in the second slot. -/
lemma bN3_smul_right (c : ℂ) (u v : Idx → ℂ) :
    bN3 u (c • v) = c * bN3 u v := by
  rw [bN3, bN3, mul_add, ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  · exact tsum_congr fun n => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  · exact tsum_congr fun m => by simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- Conjugate-linearity of `𝓝_α` in the first slot (unconditional). -/
lemma NBform_smul_left (α : ℝ) (c : ℂ) (u v : Idx → ℂ) :
    NBform α (c • u) v = (starRingEnd ℂ) c * NBform α u v := by
  rw [NBform, mulA_smul, bN3_smul_left, bN3_smul_left, NBform, mul_add]

/-- Linearity of `𝓝_α` in the second slot (unconditional). -/
lemma NBform_smul_right (α : ℝ) (c : ℂ) (u v : Idx → ℂ) :
    NBform α u (c • v) = c * NBform α u v := by
  rw [NBform, mulA_smul, bN3_smul_right, bN3_smul_right, NBform, mul_add]

/-- **B-orthogonality of the two `R_α`-eigenspaces** — the block-diagonality of
`𝓝_α`.  If `R_α u = −u` (a `tan`-block vector) and `R_α v = v` (a `cot`-block
vector), then `𝓝_α(u,v) = 0`.  Pure consequence of the form-symmetry
`NBform_rop` and conjugate-linearity: `𝓝_α(u,v) = 𝓝_α(R_α u, R_α v) =
𝓝_α(−u, v) = −𝓝_α(u,v)`, so `𝓝_α(u,v) = 0`.  (This is what item 1's parity
orthogonality gives at the form level, and it makes the index/nullity additive.) -/
lemma NBform_eigen_orthogonal (α : ℝ) {u v : Idx → ℂ} (hu : SectorL2 u)
    (hv : SectorL2 v) (heu : rop α u = -u) (hev : rop α v = v) :
    NBform α u v = 0 := by
  have key : NBform α u v = -(NBform α u v) := by
    conv_lhs => rw [← NBform_rop α hu hv, heu, hev]
    rw [NBform_neg_left]
  have h0 : (2 : ℂ) * NBform α u v = 0 := by linear_combination key
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h two_ne_zero
  · exact h

/-- **Energy block-diagonality**: for `u` in the `tan` block (`R_α u = −u`) and
`v` in the `cot` block (`R_α v = v`), the `𝓝_α`-energy is additive,
`𝓝_α(u+v) = 𝓝_α(u) + 𝓝_α(v)` — the cross terms `𝓝_α(u,v) = 𝓝_α(v,u) = 0`
drop out (`NBform_eigen_orthogonal`).  This is what makes the direct sum of a
`tan`-block negative subspace and a `cot`-block negative subspace itself
`𝓝_α`-negative (the superadditivity `≥` half of the index additivity). -/
lemma NQform_add_block (α : ℝ) {u v : Idx → ℂ}
    (hu : MemSectorς u) (hv : MemSectorς v)
    (heu : rop α u = -u) (hev : rop α v = v) :
    NQform α (u + v) = NQform α u + NQform α v := by
  have hUV : MemSectorς (u + v) := memSectorς_add hu hv
  have ho : NBform α u v = 0 :=
    NBform_eigen_orthogonal α (memSector_sectorL2 hu.1) (memSector_sectorL2 hv.1) heu hev
  have ho' : NBform α v u = 0 := by rw [NBform_conj_symm, ho, map_zero]
  have hcast : (NQform α (u + v) : ℂ) = (NQform α u : ℂ) + (NQform α v : ℂ) := by
    rw [← NBform_self, NBform_add_left α hu hv hUV, NBform_add_right α hu hu hv,
      NBform_add_right α hv hu hv, NBform_self α u, NBform_self α v, ho, ho']
    ring
  exact_mod_cast hcast

end KsIndex.SectorForm
