module

public import KsIndexLean.JacobiExtensionOperator

@[expose] public section


noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.DtNCircle KsIndex.CircleSobolev
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

lemma jacobiExtensionH1_rotation {k : ℕ} (hk : 2 ≤ k) (θ : ℝ)
    (f : Space (1 / 2 : ℝ)) :
    diskRotation θ (jacobiExtensionH1 hk f) =
      jacobiExtensionH1 hk (rotationCLM (1 / 2 : ℝ) θ f) := by
  have h := (diskRotation θ).toContinuousLinearMap.map_tsum (jacobiExtension_summable hk f)
  change diskRotation θ (jacobiExtensionH1 hk f) = _ at h
  rw [h]
  unfold jacobiExtensionH1
  apply tsum_congr
  intro n
  simp only [LinearIsometry.coe_toContinuousLinearMap, map_smul,
    normalizedJacobiMode_rotation, coeff_rotationCLM, smul_smul]
  have he : fourier n.val (θ : AddCircle (2 * Real.pi)) =
      Complex.exp ((n.val : ℂ) * θ * Complex.I) := by
    rw [fourier_coe_apply]
    congr 1
    have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp
  rw [he, mul_comm]

lemma jacobiExtensionH1_mem_character {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (f : Space (1 / 2 : ℝ)) (hf : f ∈ character (1 / 2 : ℝ) (j : ℤ) (k : ℤ)) :
    jacobiExtensionH1 hk f ∈
      weakCharacterDomain (-(2 * Real.pi) / k) (KsIndex.FormIndex.zeta k ^ j) := by
  rw [mem_weakCharacterDomain, jacobiExtensionH1_rotation]
  have he := (mem_character_iff_rotationCLM (1 / 2 : ℝ) k (by omega) (j : ℤ) f).mp hf
  rw [he, jacobiExtensionH1_smul, zpow_natCast]

/-- Nontrivial character support excludes the zero Fourier coefficient. -/
lemma dnCharacterSpace_mem_dotted {k j : ℕ} (hj0 : 0 < j) (hjk : j < k)
    (f : Space (1 / 2 : ℝ)) (hf : f ∈ dnCharacterSpace k (j : ℤ)) :
    f ∈ dotted (1 / 2 : ℝ) := by
  rw [mem_dotted]
  apply (mem_character _ _ _ f).mp hf.2 0
  rintro ⟨m, hm⟩
  have he : (j : ℤ) = (k : ℤ) * m := by linarith
  have hd : k ∣ j := by
    exact_mod_cast (show (k : ℤ) ∣ (j : ℤ) from ⟨m, he⟩)
  exact (not_le_of_gt hjk) (Nat.le_of_dvd hj0 hd)

/-- Once the trace is identified, DN membership is imposed
without truncating inside the arc space. -/
lemma jacobiExtensionCLM_mem_DN {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (f : dotted (1 / 2 : ℝ)) (hf : f.val ∈ dnCharacterSpace k (j : ℤ)) :
    jacobiExtensionCLM hk f ∈ mixedCharacterDomain k j true false := by
  constructor
  · apply (halfDiskTrace_mem_dnSpace_iff_mixed k _).mp
    rw [jacobiExtensionCLM_halfTrace]
    exact hf.1
  · exact jacobiExtensionH1_mem_character hk j f hf.2

end KsIndex.Trace
