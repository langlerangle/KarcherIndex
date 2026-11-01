module

public import KsIndexLean.WeakMultiplierTrace
public import KsIndexLean.WeakTransmissionDomains
public import KsIndexLean.WeakDiskChain

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.FaithfulInjection

lemma boundaryRestrict_circleMul_congr (A : Set Circle₁) (η : C(Circle₁, ℝ))
    {F G : Lp ℂ 2 circleMeasure} (h : boundaryRestrict A F = boundaryRestrict A G) :
    boundaryRestrict A (circleMul η F) = boundaryRestrict A (circleMul η G) := by
  have he : (F : Circle₁ → ℂ) =ᵐ[circleMeasure.restrict A] G := by
    have hf := boundaryRestrict_coe_ae A F
    rw [h] at hf
    exact hf.symm.trans (boundaryRestrict_coe_ae A G)
  apply Lp.ext
  filter_upwards [boundaryRestrict_coe_ae A (circleMul η F),
    boundaryRestrict_coe_ae A (circleMul η G), he,
    (circleMul_coe η F).filter_mono (ae_mono (Measure.restrict_le_self (s := A))),
    (circleMul_coe η G).filter_mono (ae_mono (Measure.restrict_le_self (s := A)))]
    with w hf hg he hF hG
  rw [hf, hg, hF, hG, he]

lemma diskCutoff_arcTrace_eq (k j : ℕ) (A : Set Circle₁) (c : ℂ) {u v : ComplexH1}
    (h : arcTrace A u = c • arcTrace A v) :
    arcTrace A (diskCutoff k j u) = c • arcTrace A (diskCutoff k j v) := by
  change boundaryRestrict A (diskTraceCLM (diskCutoff k j u)) =
    c • boundaryRestrict A (diskTraceCLM (diskCutoff k j v))
  rw [diskCutoff_trace, diskCutoff_trace, ← boundaryRestrict_smul, ← circleMul_smul]
  apply boundaryRestrict_circleMul_congr
  rw [boundaryRestrict_smul]
  exact h

lemma diskCutoff_mem_zeroTraceDomain (k j : ℕ) (A : Set Circle₁) {u : ComplexH1}
    (h : u ∈ zeroTraceDomain A) : diskCutoff k j u ∈ zeroTraceDomain A := by
  have hz : arcTrace A u = (0 : ℂ) • arcTrace A (0 : ComplexH1) := by
    simpa only [zero_smul] using (show arcTrace A u = 0 from h)
  have he := diskCutoff_arcTrace_eq k j A 0 hz
  change arcTrace A (diskCutoff k j u) = 0
  simpa only [zero_smul] using he

lemma diskCutoff_mem_slitTraceDomain (k j : ℕ) (c : ℂ) {u : DiskPairH1}
    (h : u ∈ slitTraceDomain k c) :
    (diskCutoff k j u.1, diskCutoff k j u.2) ∈ slitTraceDomain k c := by
  obtain ⟨h1, h0⟩ := (mem_slitTraceDomain k c u).mp h
  apply (mem_slitTraceDomain k c _).mpr
  constructor
  · simpa only [one_smul] using diskCutoff_arcTrace_eq k j (boundaryArc k 1) 1
      (by simpa only [one_smul] using h1)
  · exact diskCutoff_arcTrace_eq k j (boundaryArc k 0) c h0

lemma diskCutoff_mem_weakDiskChain (k m j : ℕ) [NeZero m]
    {u : ZMod (2 * m) → ComplexH1} (h : u ∈ weakDiskChain k m) :
    (fun n => diskCutoff k j (u n)) ∈ weakDiskChain k m := by
  apply (mem_weakDiskChain k m _).mpr
  intro n
  simpa only [one_smul] using diskCutoff_arcTrace_eq k j (seamBoundary k m n) 1
    (by simpa only [one_smul] using (mem_weakDiskChain k m u).mp h n)

end KsIndex.Trace
