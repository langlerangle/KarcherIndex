module

/-
KsIndexLean — Pure-Neumann index and nullity correspondence in nonzero characters.

For `k ≥ 3` and `0 < j < k`, the index and nullity on
`mixedCharacterDomain k j true true` equal those of the boundary DtN form
`pnBoundaryForm`. These are the nonzero-character correspondences in the
paper's lemma `nop-sphop`.

The linear equivalence `pnJacobiSplit`, defined for `k ≥ 2`, decomposes a
pure-Neumann element into its boundary trace and the zero-trace remainder
after subtracting the Jacobi extension. The trace right-inverse identity
proves that the split and join maps are inverse. In these coordinates,
`pnJacobiSplit_symm_form` expresses the weak Jacobi form as `2*π` times
the boundary form plus the zero-trace form. For `k ≥ 3` and `0 < j < k`,
strict positivity of the zero-trace block yields the index and radical
nullity correspondences. The final theorem transfers the known disk
nullity values to the boundary form through this correspondence.
-/
public import KsIndexLean.JacobiExtensionCounts
public import KsIndexLean.JacobiExtensionCharacter
public import KsIndexLean.CircleSobolevRotation
public import KsIndexLean.GeneralNeumannValues
public import KsIndexLean.PaperSlitHemisphereSplit

@[expose] public section


noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.CircleSobolev KsIndex.DtnBridge KsIndex.NegativeDensity
open KsIndex.Spectral KsIndex.FormIndex

variable {k j : ℕ}

/-! ### The class-j boundary space and the decomposition maps -/

/-- The class-j boundary space embeds in the full mean-zero space. -/
def pnCharacterDotted (hj0 : 0 < j) (hjk : j < k) :
    character (1 / 2 : ℝ) (j : ℤ) (k : ℤ) →ₗ[ℂ] dotted (1 / 2 : ℝ) where
  toFun f := ⟨f.val, character_mem_dotted hj0 hjk f.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def pnJacobiExtension (hk : 2 ≤ k) (hj0 : 0 < j) (hjk : j < k) :
    character (1 / 2 : ℝ) (j : ℤ) (k : ℤ) →ₗ[ℂ] ComplexH1 :=
  (jacobiExtensionCLM hk).toLinearMap.comp (pnCharacterDotted hj0 hjk)

lemma pnJacobiExtension_mem (hk : 2 ≤ k) (hj0 : 0 < j) (hjk : j < k)
    (f : character (1 / 2 : ℝ) (j : ℤ) (k : ℤ)) :
    pnJacobiExtension hk hj0 hjk f ∈ mixedCharacterDomain k j true true :=
  ⟨by rw [mixedTraceDomain_NN]; exact Submodule.mem_top,
    jacobiExtensionH1_mem_character hk j f f.property⟩

lemma pnJacobiExtension_trace (hk : 2 ≤ k) (hj0 : 0 < j) (hjk : j < k)
    (f : character (1 / 2 : ℝ) (j : ℤ) (k : ℤ)) :
    halfDiskTraceCLM (pnJacobiExtension hk hj0 hjk f) = f.val :=
  jacobiExtensionCLM_halfTrace hk (pnCharacterDotted hj0 hjk f)

/-- The boundary trace of a pure-Neumann class-j element. -/
def pnCharacterTrace (hk : 2 ≤ k) :
    mixedCharacterDomain k j true true →ₗ[ℂ]
      character (1 / 2 : ℝ) (j : ℤ) (k : ℤ) where
  toFun u := ⟨halfDiskTraceCLM u.val,
    halfDiskTrace_mem_character (by omega) u.property.2⟩
  map_add' u v := Subtype.ext (map_add halfDiskTraceCLM u.val v.val)
  map_smul' c u := Subtype.ext (map_smul halfDiskTraceCLM c u.val)

lemma pnJacobiRemainder_mem (hk : 2 ≤ k) (hj0 : 0 < j) (hjk : j < k)
    (u : mixedCharacterDomain k j true true) :
    u.val - pnJacobiExtension hk hj0 hjk (pnCharacterTrace (j := j) hk u) ∈
      mixedCharacterDomain k j false false := by
  rw [mixedDD_eq_fullDirichletCharacter (by omega)]
  constructor
  · apply (mem_fullZeroTrace_iff _).mpr
    have h : halfDiskTraceCLM
        (u.val - pnJacobiExtension hk hj0 hjk (pnCharacterTrace (j := j) hk u)) = 0 := by
      rw [map_sub, pnJacobiExtension_trace]
      exact sub_self _
    have he := congrArg (toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2)) h
    simpa only [halfDiskTraceCLM_apply, toL2_halfDiskTrace, map_zero] using he
  · exact (weakCharacterDomain _ _).sub_mem u.property.2
      (pnJacobiExtension_mem hk hj0 hjk (pnCharacterTrace (j := j) hk u)).2

def pnJacobiJoin (hk : 2 ≤ k) (hj0 : 0 < j) (hjk : j < k)
    (p : character (1 / 2 : ℝ) (j : ℤ) (k : ℤ) ×
      mixedCharacterDomain k j false false) :
    mixedCharacterDomain k j true true :=
  ⟨pnJacobiExtension hk hj0 hjk p.1 + p.2.val,
    (mixedCharacterDomain k j true true).add_mem
      (pnJacobiExtension_mem hk hj0 hjk p.1) (by
      have h : p.2.val ∈ zeroTraceDomain Set.univ ⊓
          weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) := by
        simpa only [mixedDD_eq_fullDirichletCharacter (by omega : 1 ≤ k)]
          using p.2.property
      exact ⟨fullZeroTrace_le_mixed k true true h.1, h.2⟩)⟩

/-! ### The linear decomposition (the paper's `dirichlet_decomp`, j ≠ 0) -/

def pnJacobiSplit (hk : 2 ≤ k) (hj0 : 0 < j) (hjk : j < k) :
    mixedCharacterDomain k j true true ≃ₗ[ℂ]
      character (1 / 2 : ℝ) (j : ℤ) (k : ℤ) ×
        mixedCharacterDomain k j false false where
  toFun u := (pnCharacterTrace (j := j) hk u,
    ⟨u.val - pnJacobiExtension hk hj0 hjk (pnCharacterTrace (j := j) hk u),
      pnJacobiRemainder_mem hk hj0 hjk u⟩)
  invFun := pnJacobiJoin hk hj0 hjk
  left_inv u := by
    apply Subtype.ext
    simp only [pnJacobiJoin]
    abel
  right_inv p := by
    have hz : halfDiskTraceCLM p.2.val = 0 := by
      apply toL2_injective (by norm_num : (0 : ℝ) ≤ 1 / 2)
      rw [map_zero]
      rw [halfDiskTraceCLM_apply, toL2_halfDiskTrace]
      apply (mem_fullZeroTrace_iff _).mp
      have h : p.2.val ∈ zeroTraceDomain Set.univ ⊓
          weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) := by
        simpa only [mixedDD_eq_fullDirichletCharacter (by omega : 1 ≤ k)]
          using p.2.property
      exact h.1
    have ht : pnCharacterTrace (j := j) hk (pnJacobiJoin hk hj0 hjk p) = p.1 := by
      apply Subtype.ext
      change halfDiskTraceCLM (pnJacobiExtension hk hj0 hjk p.1 + p.2.val) = p.1.val
      rw [map_add, pnJacobiExtension_trace, hz, add_zero]
    apply Prod.ext
    · exact ht
    · apply Subtype.ext
      change (pnJacobiJoin hk hj0 hjk p).val - pnJacobiExtension hk hj0 hjk
        (pnCharacterTrace (j := j) hk (pnJacobiJoin hk hj0 hjk p)) = p.2.val
      rw [ht]
      change (pnJacobiExtension hk hj0 hjk p.1 + p.2.val) -
        pnJacobiExtension hk hj0 hjk p.1 = p.2.val
      abel
  map_add' u v := by
    apply Prod.ext
    · exact (pnCharacterTrace (j := j) hk).map_add u v
    · apply Subtype.ext
      change u.val + v.val - pnJacobiExtension hk hj0 hjk
          (pnCharacterTrace (j := j) hk (u + v)) =
        (u.val - pnJacobiExtension hk hj0 hjk (pnCharacterTrace (j := j) hk u)) +
        (v.val - pnJacobiExtension hk hj0 hjk (pnCharacterTrace (j := j) hk v))
      rw [map_add, map_add]
      abel
  map_smul' c u := by
    apply Prod.ext
    · exact (pnCharacterTrace (j := j) hk).map_smul c u
    · apply Subtype.ext
      simp only [Prod.smul_snd, Submodule.coe_smul, RingHom.id_apply, map_smul, smul_sub]

/-- The explicit inverse realizes the paper's `first_block` identity. -/
lemma pnJacobiSplit_symm_form (hk : 2 ≤ k) (hj0 : 0 < j) (hjk : j < k)
    (p q : character (1 / 2 : ℝ) (j : ℤ) (k : ℤ) ×
      mixedCharacterDomain k j false false) :
    weakJacobi (surfacePotential k) ((pnJacobiSplit hk hj0 hjk).symm p)
      ((pnJacobiSplit hk hj0 hjk).symm q) =
      (2 * Real.pi : ℂ) * faithfulDtnB k (pnCharacterDotted hj0 hjk p.1)
        (pnCharacterDotted hj0 hjk q.1) +
      weakJacobi (surfacePotential k) p.2.val q.2.val := by
  have hz (w : mixedCharacterDomain k j false false) :
      w.val ∈ zeroTraceDomain Set.univ := by
    have h : w.val ∈ zeroTraceDomain Set.univ ⊓
        weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) := by
      simpa only [mixedDD_eq_fullDirichletCharacter (by omega : 1 ≤ k)]
        using w.property
    exact h.1
  exact jacobiExtensionCLM_block_form hk (pnCharacterDotted hj0 hjk p.1)
    (pnCharacterDotted hj0 hjk q.1) p.2.val q.2.val (hz p.2) (hz q.2)

/-! ### The index and nullity correspondences (the lemma's j ≠ 0 claims) -/

/-- The pure-Neumann class-j boundary (DtN) block — the `nop` side. -/
def pnBoundaryForm (hj0 : 0 < j) (hjk : j < k)
    (f g : character (1 / 2 : ℝ) (j : ℤ) (k : ℤ)) : ℂ :=
  faithfulDtnB k (pnCharacterDotted hj0 hjk f) (pnCharacterDotted hj0 hjk g)

lemma pnBoundaryForm_zero_left (hj0 : 0 < j) (hjk : j < k)
    (f : character (1 / 2 : ℝ) (j : ℤ) (k : ℤ)) :
    pnBoundaryForm hj0 hjk 0 f = 0 := by
  simp [pnBoundaryForm, faithfulDtnB, pnCharacterDotted, coeff]

lemma pnBoundaryForm_zero_right (hj0 : 0 < j) (hjk : j < k)
    (f : character (1 / 2 : ℝ) (j : ℤ) (k : ℤ)) :
    pnBoundaryForm hj0 hjk f 0 = 0 := by
  simp [pnBoundaryForm, faithfulDtnB, pnCharacterDotted, coeff]

lemma pnWeakJacobi_zero_left (V : BoundedRealPotential) (v : ComplexH1) :
    weakJacobi V 0 v = 0 := by
  have h := weakJacobi_add_left V 0 0 v
  rw [add_zero] at h
  have h2 : weakJacobi V 0 v + 0 = weakJacobi V 0 v + weakJacobi V 0 v := by
    rw [add_zero]
    exact h
  exact (add_left_cancel h2).symm

/-- **`ind_{N,j}(sphop) = ind_{N,j}(nop)` for `0 < j < k`** ([ksindexi]
Lemma `nop-sphop`), via the Jacobi-extension decomposition. -/
theorem pureNeumann_index_eq_boundary (hk : 3 ≤ k) (hj0 : 0 < j) (hjk : j < k) :
    diskWeakIndex (mixedCharacterDomain k j true true) (surfacePotential k) =
      negativeIndex (fun f : character (1 / 2 : ℝ) (j : ℤ) (k : ℤ) =>
        (pnBoundaryForm hj0 hjk f f).re) := by
  let B := pnBoundaryForm hj0 hjk
  let R := fun w : mixedCharacterDomain k j false false =>
    (weakJacobi (surfacePotential k) w w).re
  have hR0 : R 0 = 0 := by simp [R, pnWeakJacobi_zero_left]
  have hRp (w : mixedCharacterDomain k j false false) : 0 ≤ R w := by
    by_cases hw : w = 0
    · rw [hw, hR0]
    · exact (generalDirichlet_character_positive_of_range hk hj0 hjk w hw).le
  have he := negativeIndex_congr (pnJacobiSplit (by omega : 2 ≤ k) hj0 hjk).symm
    (fun p : character (1 / 2 : ℝ) (j : ℤ) (k : ℤ) ×
        mixedCharacterDomain k j false false =>
      2 * Real.pi * (B p.1 p.1).re + R p.2)
    (fun u : mixedCharacterDomain k j true true =>
      (weakJacobi (surfacePotential k) u u).re)
    (by
      intro p
      rw [pnJacobiSplit_symm_form]
      simp [B, R, pnBoundaryForm, Complex.mul_re])
  change negativeIndex (fun u : mixedCharacterDomain k j true true =>
    (weakJacobi (surfacePotential k) u u).re) = _
  rw [he]
  exact (negativeIndex_nonnegative_product
    (fun f : character (1 / 2 : ℝ) (j : ℤ) (k : ℤ) => 2 * Real.pi * (B f f).re) R
    (by simp [B, pnBoundaryForm_zero_left]) hR0 hRp).trans
    (negativeIndex_pos_mul _ _ Real.two_pi_pos)

/-- `nul_{N,j}(sphop) = nul_{N,j}(nop)` for `0 < j < k`, radical form. -/
theorem pureNeumann_sesqNullity_eq_boundary (hk : 3 ≤ k) (hj0 : 0 < j) (hjk : j < k) :
    sesqNullity (fun u v : mixedCharacterDomain k j true true =>
      weakJacobi (surfacePotential k) u v) =
      sesqNullity (pnBoundaryForm hj0 hjk) := by
  have he := sesqNullity_congr (pnJacobiSplit (by omega : 2 ≤ k) hj0 hjk).symm
    (fun p q : character (1 / 2 : ℝ) (j : ℤ) (k : ℤ) ×
        mixedCharacterDomain k j false false =>
      (2 * Real.pi : ℂ) * pnBoundaryForm hj0 hjk p.1 q.1 +
        weakJacobi (surfacePotential k) p.2.val q.2.val)
    (fun u v : mixedCharacterDomain k j true true =>
      weakJacobi (surfacePotential k) u v)
    (fun p q => pnJacobiSplit_symm_form (by omega) hj0 hjk p q)
  rw [he]
  have hp := sesqNullity_positive_product
    (fun f g : character (1 / 2 : ℝ) (j : ℤ) (k : ℤ) =>
      (2 * Real.pi : ℂ) * pnBoundaryForm hj0 hjk f g)
    (fun u v : mixedCharacterDomain k j false false =>
      weakJacobi (surfacePotential k) u v)
    (fun x => by rw [pnBoundaryForm_zero_right, mul_zero])
    (fun y => pnWeakJacobi_zero_left _ _)
    (fun y hy => generalDirichlet_character_positive_of_range hk hj0 hjk y hy)
  exact hp.trans (sesqNullity_nonzero_mul _ _
    (by exact_mod_cast Real.two_pi_pos.ne'))

/-- The nullity correspondence against the finite-dimensional disk nullity. -/
theorem pureNeumann_nullity_eq_boundary (hk : 3 ≤ k) (hj0 : 0 < j) (hjk : j < k) :
    (diskWeakNullity (mixedCharacterDomain k j true true) (surfacePotential k) : ℕ∞) =
      sesqNullity (pnBoundaryForm hj0 hjk) := by
  let : CompleteSpace (mixedCharacterDomain k j true true) :=
    (isClosed_mixedCharacterDomain k j true true).completeSpace_coe
  rw [← disk_sesqNullity_eq_weakNullity]
  exact pureNeumann_sesqNullity_eq_boundary hk hj0 hjk

/-- Consistency of the correspondence with the evaluated sphop-side nullity
values (`neumann_class_nullity`), transferred through the correspondence. -/
theorem pnBoundary_sesqNullity_value (hk : 3 ≤ k) (hj0 : 0 < j) (hjk : j < k) :
    sesqNullity (pnBoundaryForm hj0 hjk) =
      (if j = 1 ∨ j = k - 1 then 1 else 0 : ℕ∞) := by
  rw [← pureNeumann_nullity_eq_boundary hk hj0 hjk]
  have h := neumann_class_nullity k hk ⟨j, hjk⟩
  rw [show ((⟨j, hjk⟩ : Fin k) : ℕ) = j from rfl] at h
  rw [h]
  split_ifs <;> simp

end KsIndex.Trace
