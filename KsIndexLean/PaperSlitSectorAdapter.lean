module

/-
KsIndexLean — Circle trace reindexing for the k = 3 slit-to-sector correspondence.

The Dirichlet-to-Neumann symbol at k = 3 agrees with `sigP` on `6n+1` and
with `sigM` on `6m+4`. These two residue classes partition the Fourier class
`ℓ ≡ 1 (mod 3)`. Both progressions contain positive and negative frequencies.

`sectorOfTrace` restricts the Fourier coefficients of a mean-zero half-order
trace to these progressions. It belongs to `MemSector` by weighted summability.
When the second argument has support in that Fourier class,
`bN3_sectorOfTrace_eq_faithfulDtnB` identifies the sector pairing with the
circle Dirichlet-to-Neumann pairing by reindexing the two summable series.

The final two lemmas identify the sector's domain-based index and nullity
with the corresponding invariants of its subtype. The disk-pair seam identity,
reconstruction, and form/count transports are supplied by the companion slit
adapter modules listed below.
-/
public import KsIndexLean.CircleQ
public import KsIndexLean.DtNCircle
public import KsIndexLean.SectorForm
public import KsIndexLean.DtnBridge

@[expose] public section


noncomputable section
open KsIndex.CircleQ KsIndex.DtNCircle KsIndex.CircleSobolev KsIndex.Sector
  KsIndex.SectorForm KsIndex.DtnBridge KsIndex.FormIndex KsIndex.NegativeDensity

namespace KsIndex.PaperSlitAdapter

/-! ### the DtN symbol on the two mod-6 residue progressions of `ℓ ≡ 1 (mod 3)` -/

/-- `σ₃` on the residue class `6n+1`: `sigP n = dtnSymbol 3 ⟨6n+1⟩` (since `(3−1)² = 4`). -/
lemma sigP_eq_dtnSymbol (n : ℤ) : sigP n = dtnSymbol 3 ⟨6 * n + 1, by omega⟩ := by
  unfold sigP dtnSymbol
  push_cast
  norm_num

/-- `σ₃` on the residue class `6m+4`: `sigM m = dtnSymbol 3 ⟨6m+4⟩`. -/
lemma sigM_eq_dtnSymbol (m : ℤ) : sigM m = dtnSymbol 3 ⟨6 * m + 4, by omega⟩ := by
  unfold sigM dtnSymbol
  push_cast
  norm_num

/-! ### the core `NZ ↔ Idx` reindex: `bN3 ∘ sectorOfTrace = faithfulDtnB 3` -/

/-- The two mod-6 residue progressions of the class `ℓ ≡ 1 (mod 3)`, as an
injection `Idx → NZ`: `inl n ↦ 6n+1`, `inr m ↦ 6m+4`. -/
def idxToNZ : Idx → NZ :=
  Sum.elim (fun n => ⟨6 * n + 1, by omega⟩) (fun m => ⟨6 * m + 4, by omega⟩)

@[simp] lemma idxToNZ_inl_val (n : ℤ) : (idxToNZ (Sum.inl n)).val = 6 * n + 1 := rfl
@[simp] lemma idxToNZ_inr_val (m : ℤ) : (idxToNZ (Sum.inr m)).val = 6 * m + 4 := rfl

lemma dtnSymbol_idxToNZ_inl (n : ℤ) : dtnSymbol 3 (idxToNZ (Sum.inl n)) = sigP n :=
  (sigP_eq_dtnSymbol n).symm

lemma dtnSymbol_idxToNZ_inr (m : ℤ) : dtnSymbol 3 (idxToNZ (Sum.inr m)) = sigM m :=
  (sigM_eq_dtnSymbol m).symm

lemma idxToNZ_injective : Function.Injective idxToNZ := by
  rintro a b hab
  have hv : (idxToNZ a).val = (idxToNZ b).val := congrArg Subtype.val hab
  rcases a with n | n <;> rcases b with m | m <;>
    simp only [idxToNZ_inl_val, idxToNZ_inr_val] at hv
  · have : n = m := by omega
    subst this; rfl
  · exact absurd hv (by omega)
  · exact absurd hv (by omega)
  · have : n = m := by omega
    subst this; rfl

/-- The class `ℓ ≡ 1 (mod 3)` is exactly the range of `idxToNZ`: the two mod-6
progressions `{6n+1}` (even quotient) and `{6m+4}` (odd quotient) cover it. -/
lemma mem_range_idxToNZ_of_mod (ℓ : NZ) (h : ℓ.val % 3 = 1) :
    ℓ ∈ Set.range idxToNZ := by
  obtain ⟨q, hq⟩ : ∃ q : ℤ, ℓ.val = 3 * q + 1 := ⟨ℓ.val / 3, by omega⟩
  rcases Int.even_or_odd q with ⟨n, hn⟩ | ⟨k, hk⟩
  · exact ⟨Sum.inl n, Subtype.ext (by simp only [idxToNZ_inl_val]; omega)⟩
  · exact ⟨Sum.inr k, Subtype.ext (by simp only [idxToNZ_inr_val]; omega)⟩

/-- The sector trace of a dotted `H^{1/2}` function: its physical Fourier
coefficients read on the two progressions. -/
def sectorOfTrace (f : dotted (1 / 2 : ℝ)) : Idx → ℂ :=
  fun i => i.elim (fun n => coeff (1 / 2 : ℝ) f.val (6 * n + 1))
                  (fun m => coeff (1 / 2 : ℝ) f.val (6 * m + 4))

@[simp] lemma sectorOfTrace_inl (f : dotted (1 / 2 : ℝ)) (n : ℤ) :
    sectorOfTrace f (Sum.inl n) = coeff (1 / 2 : ℝ) f.val (6 * n + 1) := rfl

@[simp] lemma sectorOfTrace_inr (f : dotted (1 / 2 : ℝ)) (m : ℤ) :
    sectorOfTrace f (Sum.inr m) = coeff (1 / 2 : ℝ) f.val (6 * m + 4) := rfl

/-- The sector trace lands in `H^{1/2}_{(2;3)}`: the `(1+|ℓ|)`-weighted square
summability of `f`'s coefficients restricts to both progressions. -/
lemma memSector_sectorOfTrace (f : dotted (1 / 2 : ℝ)) :
    MemSector (sectorOfTrace f) := by
  have hsum : Summable
      (fun ℓ : ℤ => (1 + |(ℓ : ℝ)|) * ‖coeff (1 / 2 : ℝ) f.val ℓ‖ ^ 2) := by
    refine ((hasSum_weighted_sq (1 / 2 : ℝ) f.val).summable).congr (fun ℓ => ?_)
    rw [weight_sq, show (2 * (1 / 2 : ℝ)) = 1 by norm_num, Real.rpow_one]
  constructor
  · have hinj : Function.Injective (fun n : ℤ => 6 * n + 1) := by
      intro a b h; simp only at h; omega
    refine (hsum.comp_injective hinj).of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    simp only [Function.comp, sectorOfTrace_inl]
    rw [show ((6 * n + 1 : ℤ) : ℝ) = 6 * (n : ℝ) + 1 by push_cast; ring]
    exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg (6 * (n : ℝ) + 1)]) (sq_nonneg _)
  · have hinj : Function.Injective (fun m : ℤ => 6 * m + 4) := by
      intro a b h; simp only at h; omega
    refine (hsum.comp_injective hinj).of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    simp only [Function.comp, sectorOfTrace_inr]
    rw [show ((6 * m + 4 : ℤ) : ℝ) = 6 * (m : ℝ) + 4 by push_cast; ring]
    exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg (6 * (m : ℝ) + 4)]) (sq_nonneg _)

/-- The `faithfulDtnB 3` summand over `NZ`, as a function of the trace pair. -/
def dtnSummand (f g : dotted (1 / 2 : ℝ)) (ℓ : NZ) : ℂ :=
  (dtnSymbol 3 ℓ : ℂ) * (starRingEnd ℂ) (coeff (1 / 2 : ℝ) f.val ℓ.val)
    * coeff (1 / 2 : ℝ) g.val ℓ.val

lemma faithfulDtnB_eq_tsum (f g : dotted (1 / 2 : ℝ)) :
    faithfulDtnB 3 f g = ∑' ℓ : NZ, dtnSummand f g ℓ := rfl

/-- For dotted `H^{1/2}` traces `f` and `g`, with only `g` required to have Fourier
support in `ℓ ≡ 1 (mod 3)`, reindexing identifies the sector base pairing
`bN3` with the faithful DtN form on the circle. -/
lemma bN3_sectorOfTrace_eq_faithfulDtnB (f g : dotted (1 / 2 : ℝ))
    (hg : ∀ ℓ : ℤ, ℓ % 3 ≠ 1 → coeff (1 / 2 : ℝ) g.val ℓ = 0) :
    bN3 (sectorOfTrace f) (sectorOfTrace g) = faithfulDtnB 3 f g := by
  have hMf := memSector_sectorOfTrace f
  have hMg := memSector_sectorOfTrace g
  -- Summability of the two composed half-sums (= the bN3 P/M summands, reindexed).
  have hSP : Summable (fun n : ℤ => dtnSummand f g (idxToNZ (Sum.inl n))) :=
    (summable_bN3P hMf.1 hMg.1).congr (fun n => by
      simp only [dtnSummand, idxToNZ_inl_val, dtnSymbol_idxToNZ_inl, sectorOfTrace_inl]
      ring)
  have hSM : Summable (fun m : ℤ => dtnSummand f g (idxToNZ (Sum.inr m))) :=
    (summable_bN3M hMf.2 hMg.2).congr (fun m => by
      simp only [dtnSummand, idxToNZ_inr_val, dtnSymbol_idxToNZ_inr, sectorOfTrace_inr]
      ring)
  -- `bN3` splits as the two reindexed half-sums.
  have hbN3 : bN3 (sectorOfTrace f) (sectorOfTrace g)
      = (∑' n : ℤ, dtnSummand f g (idxToNZ (Sum.inl n)))
        + (∑' m : ℤ, dtnSummand f g (idxToNZ (Sum.inr m))) := by
    unfold bN3
    congr 1
    · exact tsum_congr (fun n => by
        simp only [dtnSummand, idxToNZ_inl_val, dtnSymbol_idxToNZ_inl, sectorOfTrace_inl]
        ring)
    · exact tsum_congr (fun m => by
        simp only [dtnSummand, idxToNZ_inr_val, dtnSymbol_idxToNZ_inr, sectorOfTrace_inr]
        ring)
  -- Recombine over `Idx`, then reindex `Idx → NZ` (support in the class ⊆ range).
  rw [hbN3, ← Summable.tsum_sum (f := fun i : Idx => dtnSummand f g (idxToNZ i)) hSP hSM,
    idxToNZ_injective.tsum_eq, faithfulDtnB_eq_tsum]
  intro ℓ hℓ
  rw [Function.mem_support] at hℓ
  by_contra hcon
  exact hℓ (by
    have hmod : ℓ.val % 3 ≠ 1 := fun h => hcon (mem_range_idxToNZ_of_mod ℓ h)
    rw [dtnSummand, hg ℓ.val hmod, mul_zero])

/-! ### The sector index and nullity as subtype invariants

Apply `formIndex_eq_negativeIndex` and `formNullity_eq_sesqNullity` to the
sector graph domain. These identities allow the slit-domain equivalences to
transport the domain-based counts via forms on the subtype `Domς`. -/

/-- The sector target `formIndex (NQform α) Domς` is the `negativeIndex` of the
`NQform`-diagonal restricted to the subtype `Domς`. -/
lemma formIndex_NQform_Domς (α : ℝ) :
    formIndex (NQform α) Domς = negativeIndex (fun x : Domς => NQform α x.val) :=
  formIndex_eq_negativeIndex (NQform α) Domς

/-- The sector target `formNullity (NBform α) Domς` is the `sesqNullity` of the
`NBform`-pairing restricted to `Domς`. -/
lemma formNullity_NBform_Domς (α : ℝ) :
    formNullity (NBform α) Domς = sesqNullity (fun u v : Domς => NBform α u.val v.val) :=
  formNullity_eq_sesqNullity (NBform α) Domς

/-! ### Companion modules

`PaperSlitAdapterAssembly` identifies the slit seam on sector coefficients.
`PaperSlitIndexTransport` constructs the splitting into graph-domain trace data
and zero-trace remainders for the nonintegral direct character case.
`PaperSlitBoundaryForm` gives the polarized form decomposition, and
`PaperSlitIndexPIN` transports index and nullity after removing the positive
remainder and the positive factor `2π`. `PaperSlitIndexPINConj` handles the
conjugate character, retaining the phase transformation `α ↦ -α`. -/

end KsIndex.PaperSlitAdapter
