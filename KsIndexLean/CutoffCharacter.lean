module

public import KsIndexLean.CutoffBoundaryDomains
public import KsIndexLean.WeakPunctureApproximation

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.PunctureCutoff KsIndex.FaithfulInjection

lemma diskCutoff_rotation_of_invariant (k j : ℕ) (θ : ℝ)
    (hi : ∀ z, cutP k (cutoffEps j) (planeRotation θ z) = cutP k (cutoffEps j) z)
    (u : ComplexH1) :
    diskRotation θ (diskCutoff k j u) = diskCutoff k j (diskRotation θ u) := by
  have hr (v : ComplexH1) : (valueCLM (diskRotation θ v) : ℂ → ℂ)
      =ᵐ[volume.restrict disk] (fun z => valueCLM v (planeRotation θ z)) := by
    change (valueCLM (diskH1Rotation θ v) : ℂ → ℂ) =ᵐ[_] _
    rw [diskH1Rotation_value]
    exact diskLpRotation_coe_ae θ (valueCLM v)
  have hp := (diskCutoff_value_ae k j u).comp_tendsto
    (measurePreserving_planeRotation_disk θ).quasiMeasurePreserving.tendsto_ae
  apply valueCLM_injective
  apply Lp.ext
  filter_upwards [hr (diskCutoff k j u), diskCutoff_value_ae k j (diskRotation θ u),
    hr u, hp] with z hl hh hr hp
  simp only [Function.comp_apply] at hp
  rw [hl, hh, hr, hp, hi]

lemma diskCutoff_rotation {k : ℕ} (hk : 1 ≤ k) (j : ℕ) (θ : ℝ)
    (hθ : Complex.exp ((θ : ℂ) * Complex.I) ^ (2 * k) = 1) (u : ComplexH1) :
    diskRotation θ (diskCutoff k j u) = diskCutoff k j (diskRotation θ u) := by
  apply diskCutoff_rotation_of_invariant
  intro z
  rw [planeRotation_apply]
  exact cutP_rot hk _ (Complex.norm_exp_ofReal_mul_I θ) hθ z

lemma diskCutoff_mem_weakCharacterDomain {k : ℕ} (hk : 1 ≤ k) (j : ℕ) (θ : ℝ) (c : ℂ)
    (hθ : Complex.exp ((θ : ℂ) * Complex.I) ^ (2 * k) = 1) {u : ComplexH1}
    (hu : u ∈ weakCharacterDomain θ c) : diskCutoff k j u ∈ weakCharacterDomain θ c := by
  rw [mem_weakCharacterDomain, diskCutoff_rotation hk j θ hθ,
    (mem_weakCharacterDomain θ c u).mp hu, map_smul]

lemma paperRotation_puncture_root {k : ℕ} (hk : 1 ≤ k) :
    Complex.exp (((-(2 * Real.pi) / (k : ℝ) : ℝ) : ℂ) * Complex.I) ^ (2 * k) = 1 := by
  have he : Complex.exp (((-(2 * Real.pi) / (k : ℝ) : ℝ) : ℂ) * Complex.I) =
      (KsIndex.FormIndex.zeta k)⁻¹ := by
    rw [KsIndex.FormIndex.zeta, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  rw [he, inv_pow, Nat.mul_comm 2 k, pow_mul, KsIndex.FormIndex.zeta_pow_N hk,
    one_pow, inv_one]

lemma diskCutoff_mem_mixedTraceDomain (k j : ℕ) (b1 b0 : Bool) {u : ComplexH1}
    (hu : u ∈ mixedTraceDomain k b1 b0) : diskCutoff k j u ∈ mixedTraceDomain k b1 b0 := by
  have hn (n : ℕ) (b : Bool) (h : u ∈ naturalArcDomain k n b) :
      diskCutoff k j u ∈ naturalArcDomain k n b := by
    cases b with
    | false => exact diskCutoff_mem_zeroTraceDomain k j (boundaryArc k n) h
    | true => trivial
  exact ⟨hn 1 b1 hu.1, hn 0 b0 hu.2⟩

lemma diskCutoff_mem_mixedCharacterDomain {k : ℕ} (hk : 1 ≤ k) (j r : ℕ)
    (b1 b0 : Bool) {u : ComplexH1} (hu : u ∈ mixedCharacterDomain k r b1 b0) :
    diskCutoff k j u ∈ mixedCharacterDomain k r b1 b0 :=
  ⟨diskCutoff_mem_mixedTraceDomain k j b1 b0 hu.1,
    diskCutoff_mem_weakCharacterDomain hk j _ _ (paperRotation_puncture_root hk) hu.2⟩

end KsIndex.Trace
