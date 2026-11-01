module

/-
KsIndexLean — ZeroMeanBlock: the zero-angular-mean half of [ksindexi]
Lemma `nop-sphop` (tex 2199–2290, the `j = 0` zero-mean claims).

Mirrors the verified `j ≠ 0` assembly (`JacobiExtensionSplitting` /
`JacobiExtensionCounts`) on the zero-mean domain: the paper's Dirichlet
decomposition `u = jext(trace u) + (zero-trace remainder)` is an honest
linear equivalence (`zeroMeanSplit`) that block-diagonalizes the weak form
(`zeroMeanSplit_symm_form` = the paper's `first_block`); the remainder block
is positive definite (directness: a zero-trace weak solution is a multiple
of the radial `c·tanh((k−1)t)`, which is `S¹`-invariant and therefore
vanishes under zero angular mean); hence index and nullity transport to the
boundary block (`zeroMean_index_eq_boundary`, `zeroMean_nullity_eq_boundary`
— the lemma's `ind/nul_{N,0,⊥}(sphop) = ind/nul_{N,0,⊥}(nop)`), where the
class-zero mean-zero count is `neumannCount k 0` — WITHOUT the radial `+1`
of `pureNeumann_weak_index`.
-/
public import KsIndexLean.ZeroMeanBoundaryBlock
public import KsIndexLean.JacobiExtensionCounts
public import KsIndexLean.WeakHemisphereIndex
public import KsIndexLean.GeneralCharacterTestExtension

@[expose] public section


noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.CircleSobolev KsIndex.DtnBridge KsIndex.NegativeDensity
open KsIndex.Spectral KsIndex.SingleDisk KsIndex.SingleDiskBridge

variable {k : ℕ}

/-! ### The decomposition maps -/

/-- Class-zero carrier membership of zero-mean elements, with the trivial
character spelled out. -/
lemma zeroMeanDomain_mem_characterOne {u : ComplexH1} (hu : u ∈ zeroMeanDomain k) :
    u ∈ weakCharacterDomain (-(2 * Real.pi) / k) 1 := by
  have h := (Submodule.mem_inf.mp ((mem_zeroMeanDomain u).mp hu).2).2
  rwa [pow_zero] at h

/-- The Jacobi extension on the zero-mean boundary space. -/
def zeroMeanJacobiExtension (hk : 2 ≤ k) :
    zeroMeanBoundarySpace k →ₗ[ℂ] ComplexH1 :=
  (jacobiExtensionCLM hk).toLinearMap.comp (zeroMeanBoundaryDotted k)

lemma zeroMeanJacobiExtension_mem (hk : 2 ≤ k) (f : zeroMeanBoundarySpace k) :
    zeroMeanJacobiExtension hk f ∈ zeroMeanDomain k :=
  jacobiExtensionCLM_mem_zeroMeanDomain hk (zeroMeanBoundaryDotted k f) f.property.2

lemma zeroMeanJacobiExtension_trace (hk : 2 ≤ k) (f : zeroMeanBoundarySpace k) :
    halfDiskTraceCLM (zeroMeanJacobiExtension hk f) = f.val :=
  jacobiExtensionCLM_halfTrace hk (zeroMeanBoundaryDotted k f)

/-- The boundary trace of a zero-mean element, with its memberships
(ZeroMeanTrace, ZeroMeanExtension). -/
def zeroMeanCharacterTrace (hk : 2 ≤ k) :
    zeroMeanDomain k →ₗ[ℂ] zeroMeanBoundarySpace k where
  toFun u := ⟨halfDiskTraceCLM u.val,
    ⟨halfDiskTrace_mem_dotted_of_angularAverage_eq_zero
        ((mem_zeroMeanDomain u.val).mp u.property).1,
      halfDiskTrace_mem_character_zero (by omega)
        (zeroMeanDomain_mem_characterOne u.property)⟩⟩
  map_add' u v := Subtype.ext (map_add halfDiskTraceCLM u.val v.val)
  map_smul' c u := Subtype.ext (map_smul halfDiskTraceCLM c u.val)

/-- The zero-trace remainder space of the zero-mean block. -/
def zeroMeanDirichlet (k : ℕ) : Submodule ℂ ComplexH1 :=
  zeroMeanDomain k ⊓ zeroTraceDomain Set.univ

lemma zeroMeanDirichlet_le_pureDirichlet (hk : 1 ≤ k) :
    zeroMeanDirichlet k ≤ mixedCharacterDomain k 0 false false := by
  intro w hw
  obtain ⟨hwm, hwt⟩ := Submodule.mem_inf.mp hw
  rw [mixedDD_eq_fullDirichletCharacter hk]
  exact Submodule.mem_inf.mpr ⟨hwt,
    (Submodule.mem_inf.mp ((mem_zeroMeanDomain w).mp hwm).2).2⟩

lemma zeroMeanRemainder_mem (hk : 2 ≤ k) (u : zeroMeanDomain k) :
    u.val - zeroMeanJacobiExtension hk (zeroMeanCharacterTrace hk u) ∈
      zeroMeanDirichlet k :=
  Submodule.mem_inf.mpr
    ⟨sub_jacobiExtension_mem_zeroMeanDomain hk u.val u.property,
      sub_jacobiExtension_mem_fullZeroTrace hk u.val u.property⟩

def zeroMeanJoin (hk : 2 ≤ k)
    (p : zeroMeanBoundarySpace k × zeroMeanDirichlet k) : zeroMeanDomain k :=
  ⟨zeroMeanJacobiExtension hk p.1 + p.2.val,
    (zeroMeanDomain k).add_mem (zeroMeanJacobiExtension_mem hk p.1)
      (Submodule.mem_inf.mp p.2.property).1⟩

lemma zeroMeanDirichlet_halfTrace_zero (w : zeroMeanDirichlet k) :
    halfDiskTraceCLM w.val = 0 := by
  apply toL2_injective (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [map_zero, halfDiskTraceCLM_apply, toL2_halfDiskTrace]
  exact (mem_fullZeroTrace_iff _).mp (Submodule.mem_inf.mp w.property).2

/-! ### The honest decomposition (the paper's `dirichlet_decomp` at j = 0,⊥) -/

def zeroMeanSplit (hk : 2 ≤ k) :
    zeroMeanDomain k ≃ₗ[ℂ] zeroMeanBoundarySpace k × zeroMeanDirichlet k where
  toFun u := (zeroMeanCharacterTrace hk u,
    ⟨u.val - zeroMeanJacobiExtension hk (zeroMeanCharacterTrace hk u),
      zeroMeanRemainder_mem hk u⟩)
  invFun := zeroMeanJoin hk
  left_inv u := by
    apply Subtype.ext
    simp only [zeroMeanJoin]
    abel
  right_inv p := by
    have hz : halfDiskTraceCLM p.2.val = 0 := zeroMeanDirichlet_halfTrace_zero p.2
    have ht : zeroMeanCharacterTrace hk (zeroMeanJoin hk p) = p.1 := by
      apply Subtype.ext
      change halfDiskTraceCLM (zeroMeanJacobiExtension hk p.1 + p.2.val) = p.1.val
      rw [map_add, zeroMeanJacobiExtension_trace, hz, add_zero]
    apply Prod.ext
    · exact ht
    · apply Subtype.ext
      change (zeroMeanJoin hk p).val - zeroMeanJacobiExtension hk
        (zeroMeanCharacterTrace hk (zeroMeanJoin hk p)) = p.2.val
      rw [ht]
      change (zeroMeanJacobiExtension hk p.1 + p.2.val) -
        zeroMeanJacobiExtension hk p.1 = p.2.val
      abel
  map_add' u v := by
    apply Prod.ext
    · exact (zeroMeanCharacterTrace hk).map_add u v
    · apply Subtype.ext
      change u.val + v.val - zeroMeanJacobiExtension hk
          (zeroMeanCharacterTrace hk (u + v)) =
        (u.val - zeroMeanJacobiExtension hk (zeroMeanCharacterTrace hk u)) +
        (v.val - zeroMeanJacobiExtension hk (zeroMeanCharacterTrace hk v))
      rw [map_add, map_add]
      abel
  map_smul' c u := by
    apply Prod.ext
    · exact (zeroMeanCharacterTrace hk).map_smul c u
    · apply Subtype.ext
      simp only [Prod.smul_snd, Submodule.coe_smul, RingHom.id_apply, map_smul, smul_sub]

/-- The explicit inverse realizes the paper's `first_block` identity. -/
lemma zeroMeanSplit_symm_form (hk : 2 ≤ k)
    (p q : zeroMeanBoundarySpace k × zeroMeanDirichlet k) :
    weakJacobi (surfacePotential k) ((zeroMeanSplit hk).symm p)
      ((zeroMeanSplit hk).symm q) =
      (2 * Real.pi : ℂ) * zeroMeanBoundaryForm k p.1 q.1 +
        weakJacobi (surfacePotential k) p.2.val q.2.val :=
  jacobiExtensionCLM_block_form hk (zeroMeanBoundaryDotted k p.1)
    (zeroMeanBoundaryDotted k q.1) p.2.val q.2.val
    (Submodule.mem_inf.mp p.2.property).2 (Submodule.mem_inf.mp q.2.property).2

/-! ### Positivity of the remainder block -/

lemma weakJacobi_left_zero (V : BoundedRealPotential) (v : ComplexH1) :
    weakJacobi V 0 v = 0 := by
  have h := weakJacobi_add_left V 0 0 v
  rw [add_zero] at h
  have h2 : weakJacobi V 0 v + 0 = weakJacobi V 0 v + weakJacobi V 0 v := by
    rw [add_zero]
    exact h
  exact (add_left_cancel h2).symm

set_option maxHeartbeats 1600000 in
-- unifying `diskWeakIndex` with the bundled `domainJacobiForm` index is a
-- heavy (but true) definitional reduction through `mapPairing`
lemma zeroMeanDirichlet_nonneg (hk : 3 ≤ k) {w : ComplexH1}
    (hw : w ∈ mixedCharacterDomain k 0 false false) :
    0 ≤ (weakJacobi (surfacePotential k) w w).re := by
  have h : ∀ u : mixedCharacterDomain k 0 false false,
      0 ≤ ((domainJacobiForm (mixedCharacterDomain k 0 false false)
        (surfacePotential k)) u u).re := by
    apply form_nonnegative_of_index_zero
    exact pureDirichlet_weak_index_zero hk 0
  have h2 := h ⟨w, hw⟩
  rwa [domainJacobiForm_apply] at h2

/-- The remainder block is positive definite — the paper's directness: a
zero-energy element pairs to zero with the whole pure-Dirichlet class-zero
block, hence is a multiple of the radial Dirichlet solution `c·tanh((k−1)t)`,
which is `S¹`-invariant and therefore vanishes under zero angular mean. -/
lemma zeroMeanDirichlet_definite (hk : 3 ≤ k) (w : zeroMeanDirichlet k)
    (hz : (weakJacobi (surfacePotential k) w.val w.val).re = 0) : w = 0 := by
  obtain ⟨hwm, hwt⟩ := Submodule.mem_inf.mp w.property
  have hwd : w.val ∈ mixedCharacterDomain k 0 false false :=
    zeroMeanDirichlet_le_pureDirichlet (by omega) w.property
  have hperp : ∀ v ∈ mixedCharacterDomain k 0 false false,
      weakJacobi (surfacePotential k) w.val v = 0 :=
    KsIndex.hermitian_orthogonal_of_nonneg_diag
      (weakJacobi (surfacePotential k)) (mixedCharacterDomain k 0 false false)
      (fun x _ y _ z _ => weakJacobi_add_left _ x y z)
      (fun x _ y _ z _ => weakJacobi_add_right _ x y z)
      (fun c x _ y _ => weakJacobi_smul_right _ c x y)
      (fun x _ y _ => (weakJacobi_conj _ y x).symm)
      (fun x hx => zeroMeanDirichlet_nonneg hk hx) hwd hz
  have hall : ∀ v ∈ zeroTraceDomain Set.univ,
      weakJacobi (surfacePotential k) w.val v = 0 := by
    apply generalDirichlet_character_tests_extend (by omega : 0 < k) 0 w.val
      ((Submodule.mem_inf.mp ((mem_zeroMeanDomain w.val).mp hwm).2).2)
    intro v hv
    exact hperp v (by
      rw [mixedDD_eq_fullDirichletCharacter (by omega : 1 ≤ k) 0]
      exact hv)
  obtain ⟨c, hc⟩ := generalDirichlet_kernel_span (by omega : 2 ≤ k) w.val hwt hall
  have hP0 : angularAverage w.val = 0 := ((mem_zeroMeanDomain w.val).mp hwm).1
  have hinv : angularAverage w.val = w.val := by
    rw [hc, angularAverage_smul,
      angularAverage_of_invariant (fun θ => radialDirichletH1_rotation _ θ)]
  exact Subtype.ext (by rw [← hinv]; exact hP0)

lemma zeroMeanDirichlet_pos (hk : 3 ≤ k) (w : zeroMeanDirichlet k) (hw : w ≠ 0) :
    0 < (weakJacobi (surfacePotential k) w.val w.val).re := by
  rcases (zeroMeanDirichlet_nonneg hk
      (zeroMeanDirichlet_le_pureDirichlet (by omega) w.property)).lt_or_eq with h | h
  · exact h
  · exact absurd (zeroMeanDirichlet_definite hk w h.symm) hw

/-! ### The index and nullity correspondences (the lemma's j = 0,⊥ claims) -/

/-- `ind_{N,0,⊥}(sphop) = ind_{N,0,⊥}(nop)`: the zero-mean disk index equals
the boundary DtN index on mean-zero class-zero data. -/
theorem zeroMean_index_eq_boundary (hk : 3 ≤ k) :
    diskWeakIndex (zeroMeanDomain k) (surfacePotential k) =
      negativeIndex (fun f : zeroMeanBoundarySpace k =>
        (zeroMeanBoundaryForm k f f).re) := by
  let B := zeroMeanBoundaryForm k
  let R := fun w : zeroMeanDirichlet k =>
    (weakJacobi (surfacePotential k) w.val w.val).re
  have hR0 : R 0 = 0 := by simp [R, weakJacobi_left_zero]
  have hRp : ∀ w : zeroMeanDirichlet k, 0 ≤ R w := fun w =>
    zeroMeanDirichlet_nonneg hk
      (zeroMeanDirichlet_le_pureDirichlet (by omega) w.property)
  have he := negativeIndex_congr (zeroMeanSplit (by omega : 2 ≤ k)).symm
    (fun p : zeroMeanBoundarySpace k × zeroMeanDirichlet k =>
      2 * Real.pi * (B p.1 p.1).re + R p.2)
    (fun u : zeroMeanDomain k => (weakJacobi (surfacePotential k) u u).re)
    (by
      intro p
      rw [zeroMeanSplit_symm_form]
      simp [B, R, Complex.mul_re])
  change negativeIndex (fun u : zeroMeanDomain k =>
    (weakJacobi (surfacePotential k) u u).re) = _
  rw [he]
  exact (negativeIndex_nonnegative_product
    (fun f : zeroMeanBoundarySpace k => 2 * Real.pi * (B f f).re) R
    (by simp [B, zeroMeanBoundaryForm_zero_left]) hR0 hRp).trans
    (negativeIndex_pos_mul _ _ Real.two_pi_pos)

/-- `nul_{N,0,⊥}(sphop) = nul_{N,0,⊥}(nop)`, radical form. -/
theorem zeroMean_sesqNullity_eq_boundary (hk : 3 ≤ k) :
    sesqNullity (fun u v : zeroMeanDomain k =>
      weakJacobi (surfacePotential k) u v) =
      sesqNullity (zeroMeanBoundaryForm k) := by
  have he := sesqNullity_congr (zeroMeanSplit (by omega : 2 ≤ k)).symm
    (fun p q : zeroMeanBoundarySpace k × zeroMeanDirichlet k =>
      (2 * Real.pi : ℂ) * zeroMeanBoundaryForm k p.1 q.1 +
        weakJacobi (surfacePotential k) p.2.val q.2.val)
    (fun u v : zeroMeanDomain k => weakJacobi (surfacePotential k) u v)
    (fun p q => zeroMeanSplit_symm_form (by omega) p q)
  rw [he]
  have hp := sesqNullity_positive_product
    (fun f g : zeroMeanBoundarySpace k =>
      (2 * Real.pi : ℂ) * zeroMeanBoundaryForm k f g)
    (fun u v : zeroMeanDirichlet k => weakJacobi (surfacePotential k) u v)
    (fun x => by rw [zeroMeanBoundaryForm_zero_right, mul_zero])
    (fun y => weakJacobi_left_zero _ _)
    (fun y hy => zeroMeanDirichlet_pos hk y hy)
  exact hp.trans (sesqNullity_nonzero_mul _ _
    (by exact_mod_cast Real.two_pi_pos.ne'))

/-- The nullity correspondence against the finite-dimensional disk nullity. -/
theorem zeroMean_nullity_eq_boundary (hk : 3 ≤ k) :
    (diskWeakNullity (zeroMeanDomain k) (surfacePotential k) : ℕ∞) =
      sesqNullity (zeroMeanBoundaryForm k) := by
  let : CompleteSpace (zeroMeanDomain k) := (isClosed_zeroMeanDomain k).completeSpace_coe
  rw [← disk_sesqNullity_eq_weakNullity]
  exact zeroMean_sesqNullity_eq_boundary hk

/-! ### Evaluating the boundary counts -/

/-- A nonnegative quadratic function has no negative subspaces. -/
lemma negativeIndex_eq_zero_of_nonneg {E : Type*} [AddCommGroup E] [Module ℂ E]
    (Q : E → ℝ) (h : ∀ x, 0 ≤ Q x) : negativeIndex Q = 0 := by
  unfold KsIndex.NegativeDensity.negativeIndex
  refine le_antisymm (iSup_le fun V => iSup_le fun hV => iSup_le fun _ => ?_)
    zero_le
  have hbot : V = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hx0
    exact absurd (hV x hx hx0) (not_lt.mpr (h x))
  rw [hbot]
  simp

/-- A definite sesquilinear form has no radical. -/
lemma sesqNullity_eq_zero_of_definite {E : Type*} [AddCommGroup E] [Module ℂ E]
    (B : E → E → ℂ) (h : ∀ x, x ≠ 0 → B x x ≠ 0) : sesqNullity B = 0 := by
  unfold KsIndex.DtnBridge.sesqNullity
  refine le_antisymm (iSup_le fun V => iSup_le fun hV => iSup_le fun _ => ?_)
    zero_le
  have hbot : V = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hx0
    exact h x hx0 (hV x hx x)
  rw [hbot]
  simp

/-! ### Capstones -/

/-- **Capstone (index), [ksindexi] Lemma `nop-sphop` at j = 0,⊥**: the weak
index of the zero-angular-mean pure-Neumann class-zero block equals the
class-zero Neumann boundary count — WITHOUT the radial `+1` of
`pureNeumann_weak_index`, which belongs to the `S¹`-invariant block. -/
theorem zeroMean_weak_index (hk : 3 ≤ k) :
    diskWeakIndex (zeroMeanDomain k) (surfacePotential k) =
      neumannCount k (0 : ZMod k) := by
  rw [zeroMean_index_eq_boundary hk, neumannCount_zero hk]
  exact negativeIndex_eq_zero_of_nonneg _
    (fun f => zeroMeanBoundaryForm_self_nonneg (by omega) f)

/-- The zero-mean block contributes no negative directions (numeric form). -/
theorem zeroMean_weak_index_eq_zero (hk : 3 ≤ k) :
    diskWeakIndex (zeroMeanDomain k) (surfacePotential k) = 0 := by
  rw [zeroMean_weak_index hk]
  exact neumannCount_zero hk

/-- **Capstone (nullity)**: the zero-mean block has no radical — the
boundary block is positive definite on the mean-zero class-zero modes. -/
theorem zeroMean_weak_nullity (hk : 3 ≤ k) :
    diskWeakNullity (zeroMeanDomain k) (surfacePotential k) = 0 := by
  have hdef : ∀ f : zeroMeanBoundarySpace k, f ≠ 0 → zeroMeanBoundaryForm k f f ≠ 0 := by
    intro f hf hz
    have hp := zeroMeanBoundaryForm_self_pos (show 1 ≤ k by omega) f hf
    rw [hz] at hp
    simp at hp
  have h := zeroMean_nullity_eq_boundary hk
  rw [sesqNullity_eq_zero_of_definite (zeroMeanBoundaryForm k) hdef] at h
  exact_mod_cast h

end KsIndex.Trace
