module

public import KsIndexLean.JacobiExtensionForm
public import KsIndexLean.GeneralDirichletPositivity
public import KsIndexLean.MixedCharacterUniqueness

@[expose] public section


noncomputable section
open Set
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.CircleSobolev KsIndex.FormIndex

/-- The boundary character space embeds in the full mean-zero space. -/
def dnCharacterDotted {k j : ℕ} (hj0 : 0 < j) (hjk : j < k) :
    dnCharacterSpace k (j : ℤ) →ₗ[ℂ] dotted (1 / 2 : ℝ) where
  toFun f := ⟨f.val, dnCharacterSpace_mem_dotted hj0 hjk f.val f.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def dnJacobiExtension {k j : ℕ} (hk : 2 ≤ k) (hj0 : 0 < j) (hjk : j < k) :
    dnCharacterSpace k (j : ℤ) →ₗ[ℂ] ComplexH1 :=
  (jacobiExtensionCLM hk).toLinearMap.comp (dnCharacterDotted hj0 hjk)

lemma dnJacobiExtension_mem {k j : ℕ} (hk : 2 ≤ k) (hj0 : 0 < j) (hjk : j < k)
    (f : dnCharacterSpace k (j : ℤ)) :
    dnJacobiExtension hk hj0 hjk f ∈ mixedCharacterDomain k j true false :=
  jacobiExtensionCLM_mem_DN hk j (dnCharacterDotted hj0 hjk f) f.property

lemma dnJacobiExtension_trace {k j : ℕ} (hk : 2 ≤ k) (hj0 : 0 < j) (hjk : j < k)
    (f : dnCharacterSpace k (j : ℤ)) :
    halfDiskTraceCLM (dnJacobiExtension hk hj0 hjk f) = f.val :=
  jacobiExtensionCLM_halfTrace hk (dnCharacterDotted hj0 hjk f)

def dnCharacterTrace {k j : ℕ} (hk : 2 ≤ k) :
    mixedCharacterDomain k j true false →ₗ[ℂ] dnCharacterSpace k (j : ℤ) where
  toFun u := ⟨halfDiskTraceCLM u, halfDiskTrace_mem_dnCharacterSpace (by omega) u.property⟩
  map_add' u v := Subtype.ext (map_add halfDiskTraceCLM u.val v.val)
  map_smul' c u := Subtype.ext (map_smul halfDiskTraceCLM c u.val)

lemma dnJacobiRemainder_mem {k j : ℕ} (hk : 2 ≤ k) (hj0 : 0 < j) (hjk : j < k)
    (u : mixedCharacterDomain k j true false) :
    u.val - dnJacobiExtension hk hj0 hjk (dnCharacterTrace (j := j) hk u) ∈
      mixedCharacterDomain k j false false := by
  rw [mixedDD_eq_fullDirichletCharacter (by omega)]
  constructor
  · apply (mem_fullZeroTrace_iff _).mpr
    have h : halfDiskTraceCLM
        (u.val - dnJacobiExtension hk hj0 hjk (dnCharacterTrace (j := j) hk u)) = 0 := by
      rw [map_sub, dnJacobiExtension_trace]
      exact sub_self _
    have he := congrArg (toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2)) h
    simpa only [halfDiskTraceCLM_apply, toL2_halfDiskTrace, map_zero] using he
  · exact (weakCharacterDomain _ _).sub_mem u.property.2
      (dnJacobiExtension_mem hk hj0 hjk (dnCharacterTrace (j := j) hk u)).2

def dnJacobiJoin {k j : ℕ} (hk : 2 ≤ k) (hj0 : 0 < j) (hjk : j < k)
    (p : dnCharacterSpace k (j : ℤ) × mixedCharacterDomain k j false false) :
    mixedCharacterDomain k j true false :=
  ⟨dnJacobiExtension hk hj0 hjk p.1 + p.2.val,
    (mixedCharacterDomain k j true false).add_mem (dnJacobiExtension_mem hk hj0 hjk p.1) (by
      have h : p.2.val ∈ zeroTraceDomain Set.univ ⊓
          weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) := by
        simpa only [mixedDD_eq_fullDirichletCharacter (by omega : 1 ≤ k)] using p.2.property
      exact ⟨fullZeroTrace_le_mixed k true false h.1, h.2⟩)⟩

/-- Honest DN-domain decomposition, with explicit inverses. No completion-density transport. -/
def dnJacobiSplit {k j : ℕ} (hk : 2 ≤ k) (hj0 : 0 < j) (hjk : j < k) :
    mixedCharacterDomain k j true false ≃ₗ[ℂ]
      dnCharacterSpace k (j : ℤ) × mixedCharacterDomain k j false false where
  toFun u := (dnCharacterTrace (j := j) hk u,
    ⟨u.val - dnJacobiExtension hk hj0 hjk (dnCharacterTrace (j := j) hk u),
      dnJacobiRemainder_mem hk hj0 hjk u⟩)
  invFun := dnJacobiJoin hk hj0 hjk
  left_inv u := by
    apply Subtype.ext
    simp only [dnJacobiJoin]
    abel
  right_inv p := by
    have hz : halfDiskTraceCLM p.2.val = 0 := by
      apply toL2_injective (by norm_num : (0 : ℝ) ≤ 1 / 2)
      rw [map_zero]
      rw [halfDiskTraceCLM_apply, toL2_halfDiskTrace]
      apply (mem_fullZeroTrace_iff _).mp
      have h : p.2.val ∈ zeroTraceDomain Set.univ ⊓
          weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) := by
        simpa only [mixedDD_eq_fullDirichletCharacter (by omega : 1 ≤ k)] using p.2.property
      exact h.1
    have ht : dnCharacterTrace (j := j) hk
        (dnJacobiJoin hk hj0 hjk p) = p.1 := by
      apply Subtype.ext
      change halfDiskTraceCLM (dnJacobiExtension hk hj0 hjk p.1 + p.2.val) = p.1.val
      rw [map_add, dnJacobiExtension_trace, hz, add_zero]
    apply Prod.ext
    · exact ht
    · apply Subtype.ext
      change (dnJacobiJoin hk hj0 hjk p).val - dnJacobiExtension hk hj0 hjk
        (dnCharacterTrace (j := j) hk (dnJacobiJoin hk hj0 hjk p)) = p.2.val
      rw [ht]
      change (dnJacobiExtension hk hj0 hjk p.1 + p.2.val) -
        dnJacobiExtension hk hj0 hjk p.1 = p.2.val
      abel
  map_add' u v := by
    apply Prod.ext
    · exact (dnCharacterTrace (j := j) hk).map_add u v
    · apply Subtype.ext
      change u.val + v.val - dnJacobiExtension hk hj0 hjk (dnCharacterTrace (j := j) hk (u + v)) =
        (u.val - dnJacobiExtension hk hj0 hjk (dnCharacterTrace (j := j) hk u)) +
        (v.val - dnJacobiExtension hk hj0 hjk (dnCharacterTrace (j := j) hk v))
      rw [map_add, map_add]
      abel
  map_smul' c u := by
    apply Prod.ext
    · exact (dnCharacterTrace (j := j) hk).map_smul c u
    · apply Subtype.ext
      simp only [Prod.smul_snd, Submodule.coe_smul, RingHom.id_apply, map_smul, smul_sub]


/-- The explicit inverse realizes the exact block-diagonal form identity. -/
lemma dnJacobiSplit_symm_form {k j : ℕ} (hk : 2 ≤ k) (hj0 : 0 < j) (hjk : j < k)
    (p q : dnCharacterSpace k (j : ℤ) × mixedCharacterDomain k j false false) :
    weakJacobi (surfacePotential k) ((dnJacobiSplit hk hj0 hjk).symm p)
      ((dnJacobiSplit hk hj0 hjk).symm q) =
      (2 * Real.pi : ℂ) * KsIndex.DtnBridge.faithfulDtnB k
        (dnCharacterDotted hj0 hjk p.1) (dnCharacterDotted hj0 hjk q.1) +
      weakJacobi (surfacePotential k) p.2.val q.2.val := by
  have hz (w : mixedCharacterDomain k j false false) : w.val ∈ zeroTraceDomain Set.univ := by
    have h : w.val ∈ zeroTraceDomain Set.univ ⊓
        weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) := by
      simpa only [mixedDD_eq_fullDirichletCharacter (by omega : 1 ≤ k)] using w.property
    exact h.1
  exact jacobiExtensionCLM_block_form hk (dnCharacterDotted hj0 hjk p.1)
    (dnCharacterDotted hj0 hjk q.1) p.2.val q.2.val (hz p.2) (hz q.2)

end KsIndex.Trace
