module

public import KsIndexLean.RadialBoundaryDomains
public import KsIndexLean.CutoffCharacter

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma diskRadial_rotation (t : ℝ) (ht : 0 ≤ t) (θ : ℝ) (u : ComplexH1) :
    diskRotation θ (diskRadial t ht u) = diskRadial t ht (diskRotation θ u) := by
  have hr (v : ComplexH1) : (valueCLM (diskRotation θ v) : ℂ → ℂ)
      =ᵐ[volume.restrict disk] (fun z => valueCLM v (planeRotation θ z)) := by
    change (valueCLM (diskH1Rotation θ v) : ℂ → ℂ) =ᵐ[_] _
    rw [diskH1Rotation_value]
    exact diskLpRotation_coe_ae θ (valueCLM v)
  have hp := (diskRadial_value_ae t ht u).comp_tendsto
    (measurePreserving_planeRotation_disk θ).quasiMeasurePreserving.tendsto_ae
  apply valueCLM_injective
  apply Lp.ext
  filter_upwards [hr (diskRadial t ht u), diskRadial_value_ae t ht (diskRotation θ u),
    hr u, hp] with z hl hh hr hp
  simp only [Function.comp_apply] at hp hh
  rw [hl, hh, hr, hp]

lemma diskRadial_phase (t : ℝ) (ht : 0 ≤ t) (c : ℂ) (hc : ‖c‖ = 1) (u : ComplexH1) :
    diskRadial t ht (c • u) = c • diskRadial t ht u := by
  have hs : (valueCLM (c • u) : ℂ → ℂ) =ᵐ[volume.restrict disk]
      (fun z => c • valueCLM u z) := by
    rw [map_smul]
    exact Lp.coeFn_smul c (valueCLM u)
  apply valueCLM_injective
  rw [map_smul]
  apply Lp.ext
  filter_upwards [diskRadial_value_ae t ht (c • u), diskRadial_value_ae t ht u, hs,
    Lp.coeFn_smul c (valueCLM (diskRadial t ht u))] with z hl hu hs hr
  simp only [Function.comp_apply] at hl hu
  rw [hl, hr]
  change radialTruncate t (valueCLM (c • u) z) = c • valueCLM (diskRadial t ht u) z
  rw [hs, hu]
  exact radialTruncate_phase t c (valueCLM u z) hc

lemma diskRadial_mem_weakCharacterDomain (t : ℝ) (ht : 0 ≤ t) (θ : ℝ) (c : ℂ)
    (hc : ‖c‖ = 1) {u : ComplexH1} (hu : u ∈ weakCharacterDomain θ c) :
    diskRadial t ht u ∈ weakCharacterDomain θ c := by
  rw [mem_weakCharacterDomain, diskRadial_rotation,
    (mem_weakCharacterDomain θ c u).mp hu, diskRadial_phase t ht c hc]

lemma diskRadial_mem_mixedTraceDomain (t : ℝ) (ht : 0 ≤ t) (k : ℕ) (b1 b0 : Bool)
    {u : ComplexH1} (hu : u ∈ mixedTraceDomain k b1 b0) :
    diskRadial t ht u ∈ mixedTraceDomain k b1 b0 := by
  have hn (n : ℕ) (b : Bool) (h : u ∈ naturalArcDomain k n b) :
      diskRadial t ht u ∈ naturalArcDomain k n b := by
    cases b with
    | false => exact diskRadial_mem_zeroTraceDomain t ht (boundaryArc k n) h
    | true => trivial
  exact ⟨hn 1 b1 hu.1, hn 0 b0 hu.2⟩

lemma diskRadial_mem_mixedCharacterDomain (t : ℝ) (ht : 0 ≤ t) (k r : ℕ)
    (b1 b0 : Bool) {u : ComplexH1} (hu : u ∈ mixedCharacterDomain k r b1 b0) :
    diskRadial t ht u ∈ mixedCharacterDomain k r b1 b0 := by
  have hc : ‖KsIndex.FormIndex.zeta k ^ r‖ = 1 := by
    have he : KsIndex.FormIndex.zeta k = Complex.exp (((2 * Real.pi / (k : ℝ) : ℝ) : ℂ) *
        Complex.I) := by
      unfold KsIndex.FormIndex.zeta
      congr 1
      push_cast
      ring
    rw [norm_pow, he, Complex.norm_exp_ofReal_mul_I, one_pow]
  exact ⟨diskRadial_mem_mixedTraceDomain t ht k b1 b0 hu.1,
    diskRadial_mem_weakCharacterDomain t ht _ _ hc hu.2⟩

end KsIndex.Trace
