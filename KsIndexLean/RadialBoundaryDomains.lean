module

public import KsIndexLean.NonlinearWeakTrace
public import KsIndexLean.CutoffBoundaryDomains

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma boundaryRestrict_compLp (A : Set Circle₁) {F : ℂ → ℂ} {C : NNReal}
    (hF : LipschitzWith C F) (h0 : F 0 = 0) (f : Lp ℂ 2 circleMeasure) :
    boundaryRestrict A (hF.compLp h0 f) = hF.compLp h0 (boundaryRestrict A f) := by
  apply Lp.ext
  filter_upwards [boundaryRestrict_coe_ae A (hF.compLp h0 f),
    hF.coeFn_compLp h0 (boundaryRestrict A f), boundaryRestrict_coe_ae A f,
    (hF.coeFn_compLp h0 f).filter_mono (ae_mono (Measure.restrict_le_self (s := A)))]
    with w hl hr hf hc
  simp only [hl, hr, Function.comp_apply, hf, hc]

lemma radial_compLp_phase {μ : Measure Circle₁} (t : ℝ) (ht : 0 ≤ t)
    (c : ℂ) (hc : ‖c‖ = 1) (f : Lp ℂ 2 μ) :
    (radialTruncate_lipschitz ht).compLp (radialTruncate_zero t) (c • f) =
      c • (radialTruncate_lipschitz ht).compLp (radialTruncate_zero t) f := by
  let hF := radialTruncate_lipschitz ht
  let h0 := radialTruncate_zero t
  apply Lp.ext
  filter_upwards [hF.coeFn_compLp h0 (c • f), hF.coeFn_compLp h0 f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (hF.compLp h0 f)] with w hl hf hs hr
  rw [hl, hr]
  change radialTruncate t ((c • f) w) = c • (hF.compLp h0 f) w
  rw [hs, hf]
  exact radialTruncate_phase t c (f w) hc

lemma diskRadial_arcTrace (t : ℝ) (ht : 0 ≤ t) (A : Set Circle₁) (u : ComplexH1) :
    arcTrace A (diskRadial t ht u) =
      (radialTruncate_lipschitz ht).compLp (radialTruncate_zero t) (arcTrace A u) := by
  change boundaryRestrict A (diskTraceCLM (diskRadial t ht u)) = _
  rw [diskRadial_trace, boundaryRestrict_compLp]
  rfl

lemma diskRadial_arcTrace_phase (t : ℝ) (ht : 0 ≤ t) (A : Set Circle₁)
    (c : ℂ) (hc : ‖c‖ = 1) {u v : ComplexH1} (h : arcTrace A u = c • arcTrace A v) :
    arcTrace A (diskRadial t ht u) = c • arcTrace A (diskRadial t ht v) := by
  rw [diskRadial_arcTrace, diskRadial_arcTrace, h, radial_compLp_phase t ht c hc]

lemma diskRadial_mem_zeroTraceDomain (t : ℝ) (ht : 0 ≤ t) (A : Set Circle₁)
    {u : ComplexH1} (hu : u ∈ zeroTraceDomain A) : diskRadial t ht u ∈ zeroTraceDomain A := by
  change arcTrace A (diskRadial t ht u) = 0
  rw [diskRadial_arcTrace, show arcTrace A u = 0 from hu]
  exact LipschitzWith.compLp_zero _ _

lemma diskRadial_mem_slitTraceDomain (t : ℝ) (ht : 0 ≤ t) (k : ℕ) (c : ℂ)
    (hc : ‖c‖ = 1) {u : DiskPairH1} (hu : u ∈ slitTraceDomain k c) :
    (diskRadial t ht u.1, diskRadial t ht u.2) ∈ slitTraceDomain k c := by
  obtain ⟨h1, h0⟩ := (mem_slitTraceDomain k c u).mp hu
  apply (mem_slitTraceDomain k c _).mpr
  constructor
  · simpa only [one_smul] using diskRadial_arcTrace_phase t ht (boundaryArc k 1) 1
      (by norm_num) (by simpa only [one_smul] using h1)
  · exact diskRadial_arcTrace_phase t ht (boundaryArc k 0) c hc h0

lemma diskRadial_mem_weakDiskChain (t : ℝ) (ht : 0 ≤ t) (k m : ℕ) [NeZero m]
    {u : ZMod (2 * m) → ComplexH1} (hu : u ∈ weakDiskChain k m) :
    (fun n => diskRadial t ht (u n)) ∈ weakDiskChain k m := by
  apply (mem_weakDiskChain k m _).mpr
  intro n
  simpa only [one_smul] using diskRadial_arcTrace_phase t ht (seamBoundary k m n) 1
    (by norm_num) (by simpa only [one_smul] using (mem_weakDiskChain k m u).mp hu n)

end KsIndex.Trace
