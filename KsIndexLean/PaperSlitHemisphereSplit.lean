module

/-
Character-preserving hemisphere decomposition and its Jacobi form.

A weak rotation character has a boundary trace in the corresponding circle
character space. For `0 < r < k`, that trace has mean zero. At `k = 3` and
`0 < j < 3`, subtracting the Jacobi extension of the trace leaves an element
of the full zero-trace domain with the same character. No additional mixed
Dirichlet-Neumann boundary restriction is imposed on the source.

The hemisphere self-pairing splits into `2π · faithfulDtnB` of its trace
and the Jacobi self-pairing of the zero-trace remainder. This supplies the
per-hemisphere identity used in the pair decomposition.
-/
public import KsIndexLean.JacobiExtensionSplitting
public import KsIndexLean.DNHalfTraceSpace

@[expose] public section


noncomputable section
open Set
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.CircleSobolev KsIndex.FormIndex KsIndex.DtnBridge
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Character-only trace membership: the boundary trace of a `weakCharacterDomain` hemisphere is a
circle character (the character component of `halfDiskTrace_mem_dnCharacterSpace`, without DN). -/
lemma halfDiskTrace_mem_character {k r : ℕ} (hk : 0 < k) {u : ComplexH1}
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (KsIndex.FormIndex.zeta k ^ r)) :
    halfDiskTraceCLM u ∈ character (1 / 2 : ℝ) (r : ℤ) (k : ℤ) := by
  apply (mem_character_iff_boundaryRotation (show (0 : ℝ) ≤ 1 / 2 by norm_num) k hk (r : ℤ)
    (halfDiskTraceCLM u)).mpr
  simp only [halfDiskTraceCLM_apply, toL2_halfDiskTrace, zpow_natCast]
  exact trace_character hu

/-- A nontrivial circle character (`0 < r < k`) is mean-zero: `0 ∉ -r+kℤ`. -/
lemma character_mem_dotted {k r : ℕ} (hr0 : 0 < r) (hrk : r < k) {f : Space (1 / 2 : ℝ)}
    (hf : f ∈ character (1 / 2 : ℝ) (r : ℤ) (k : ℤ)) : f ∈ dotted (1 / 2 : ℝ) := by
  rw [mem_dotted]
  apply (mem_character _ _ _ f).mp hf 0
  rintro ⟨m, hm⟩
  have he : (r : ℤ) = (k : ℤ) * m := by linarith
  have hd : k ∣ r := by exact_mod_cast (show (k : ℤ) ∣ (r : ℤ) from ⟨m, he⟩)
  exact (not_le_of_gt hrk) (Nat.le_of_dvd hr0 hd)

/-- **Character hemisphere decomposition.**  A `weakCharacterDomain` hemisphere
`u` (`0<j<3`) splits as `jacobiExtensionCLM (trace) + remainder`, with the remainder in the full
zero-trace domain AND still in the character (trace recovery + character preservation) — the
character-only analogue of `dnJacobiRemainder_mem`, no DN restriction imposed. -/
lemma charHemi_remainder_mem {j : ℕ} (hj0 : 0 < j) (hjk : j < 3) {u : ComplexH1}
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j)) :
    u - jacobiExtensionCLM (show 2 ≤ 3 by norm_num)
        ⟨halfDiskTraceCLM u,
          character_mem_dotted hj0 hjk (halfDiskTrace_mem_character (by norm_num) hu)⟩
      ∈ zeroTraceDomain Set.univ
        ⊓ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j) := by
  refine ⟨?_, ?_⟩
  · apply (mem_fullZeroTrace_iff _).mpr
    have h : halfDiskTraceCLM (u - jacobiExtensionCLM (show 2 ≤ 3 by norm_num)
        ⟨halfDiskTraceCLM u, character_mem_dotted hj0 hjk
          (halfDiskTrace_mem_character (by norm_num) hu)⟩) = 0 := by
      rw [map_sub, jacobiExtensionCLM_halfTrace]
      exact sub_self _
    have he := congrArg (toL2 (show (0 : ℝ) ≤ 1 / 2 by norm_num)) h
    simpa only [halfDiskTraceCLM_apply, toL2_halfDiskTrace, map_zero] using he
  · refine (weakCharacterDomain _ _).sub_mem hu ?_
    change jacobiExtensionH1 (show 2 ≤ 3 by norm_num) _ ∈ _
    exact jacobiExtensionH1_mem_character (show 2 ≤ 3 by norm_num) j _
      (halfDiskTrace_mem_character (by norm_num) hu)

/-- The dotted boundary trace of a character hemisphere (`0<j<3`). -/
def charTrace {j : ℕ} (hj0 : 0 < j) (hjk : j < 3) {u : ComplexH1}
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j)) :
    dotted (1 / 2 : ℝ) :=
  ⟨halfDiskTraceCLM u,
    character_mem_dotted hj0 hjk (halfDiskTrace_mem_character (by norm_num) hu)⟩

/-- **Per-hemisphere block form.**  A character hemisphere's weak Jacobi self-energy splits into
`2π·faithfulDtnB` on its trace plus the zero-trace remainder's self-energy — the per-hemisphere
input to the pair block form. -/
lemma charHemi_block {j : ℕ} (hj0 : 0 < j) (hjk : j < 3) {u : ComplexH1}
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j)) :
    weakJacobi (surfacePotential 3) u u
      = (2 * Real.pi : ℂ) * faithfulDtnB 3 (charTrace hj0 hjk hu) (charTrace hj0 hjk hu)
        + weakJacobi (surfacePotential 3)
            (u - jacobiExtensionCLM (show 2 ≤ 3 by norm_num) (charTrace hj0 hjk hu))
            (u - jacobiExtensionCLM (show 2 ≤ 3 by norm_num) (charTrace hj0 hjk hu)) := by
  have hrem := charHemi_remainder_mem hj0 hjk hu
  have hz : (u - jacobiExtensionCLM (show 2 ≤ 3 by norm_num) (charTrace hj0 hjk hu))
      ∈ zeroTraceDomain Set.univ := (Submodule.mem_inf.mp hrem).1
  have hb := jacobiExtensionCLM_block_form (show 2 ≤ 3 by norm_num)
    (charTrace hj0 hjk hu) (charTrace hj0 hjk hu)
    (u - jacobiExtensionCLM (show 2 ≤ 3 by norm_num) (charTrace hj0 hjk hu))
    (u - jacobiExtensionCLM (show 2 ≤ 3 by norm_num) (charTrace hj0 hjk hu)) hz hz
  rwa [show jacobiExtensionCLM (show 2 ≤ 3 by norm_num) (charTrace hj0 hjk hu)
      + (u - jacobiExtensionCLM (show 2 ≤ 3 by norm_num) (charTrace hj0 hjk hu)) = u from by abel]
    at hb

end KsIndex.Trace
