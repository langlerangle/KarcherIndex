module

public import KsIndexLean.PhasePairPunctureSupport

@[expose] public section


open Set MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Restricting a representative to the closed disk leaves its weak interior
value unchanged. -/
lemma RepresentsDiskJet.value_closedDiskRestriction {f : ℂ → ℂ} {u : ComplexH1}
    (h : RepresentsDiskJet f u) :
    (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] closedDiskRestriction f := by
  filter_upwards [h.1, ae_restrict_mem disk.isOpen.measurableSet] with z hz hzD
  rw [hz, closedDiskRestriction, ite_eq_left (KsIndex.SurfaceForm.mem_disk_iff.mp hzD).le]

/-- Smooth phase germs of representatives enforce membership in the actual
weak slit trace domain. -/
lemma slitTraceDomain_of_represented_phase_germs {k : ℕ} {c : ℂ}
    {f g : ℂ → ℂ} {u v : ComplexH1}
    (hu : RepresentsDiskJet f u) (hv : RepresentsDiskJet g v)
    (hs : ∀ b, b = 0 ∨ b = 1 → ∀ z ∈ KsIndex.Surface.arc k b,
      ContDiffAt ℝ ∞ (phaseGerm (if b = 0 then c else 1)
        (closedDiskRestriction f) (closedDiskRestriction g)) z) :
    (u, v) ∈ slitTraceDomain k c := by
  have h b (hb : b = 0 ∨ b = 1) := arcTrace_phaseGerm
    (A := boundaryArc k b) u v (if b = 0 then c else 1)
    hu.value_closedDiskRestriction hv.value_closedDiskRestriction
    (fun w hw => hs b hb w hw)
  apply (mem_slitTraceDomain k c (u, v)).mpr
  constructor
  · simpa only [show ¬(1 : ℕ) = 0 by decide, ite_false, one_smul] using h 1 (Or.inr rfl)
  · simpa only [ite_true] using h 0 (Or.inl rfl)

/-- Smooth approximation of a puncture-avoiding slit pair for any nonzero
phase. Both oriented seam germs and a common puncture hole are retained;
no finite cyclic extension of the phase is required. -/
theorem punctured_slit_pair_approximation {k : ℕ} (hk : 1 ≤ k)
    (c : ℂ) (hc : c ≠ 0) (p : slitTraceDomain k c)
    {H : Set ℂ} (hH : IsOpen H) (hpH : KsIndex.Surface.punctures k ⊆ H)
    (hu : ∀ᵐ z ∂volume.restrict (disk : Set ℂ), z ∈ H → valueCLM p.val.1 z = 0)
    (hv : ∀ᵐ z ∂volume.restrict (disk : Set ℂ), z ∈ H → valueCLM p.val.2 z = 0) :
    ∃ (f g : ℕ → ℂ → ℂ) (U V : ℕ → ComplexH1),
      Tendsto (fun n => (U n, V n)) atTop (𝓝 p.val) ∧
      ∀ᶠ n in atTop,
        ContDiff ℝ ∞ (f n) ∧ RepresentsDiskJet (f n) (U n) ∧
        ContDiff ℝ ∞ (g n) ∧ RepresentsDiskJet (g n) (V n) ∧
        (∀ b, b = 0 ∨ b = 1 → ∀ z ∈ KsIndex.Surface.arc k b,
          ContDiffAt ℝ ∞ (phaseGerm (if b = 0 then c else 1)
            (closedDiskRestriction (f n)) (closedDiskRestriction (g n))) z ∧
          ContDiffAt ℝ ∞ (phaseGerm (if b = 0 then c⁻¹ else 1)
            (closedDiskRestriction (g n)) (closedDiskRestriction (f n))) z) ∧
        (U n, V n) ∈ slitTraceDomain k c ∧
        ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ KsIndex.Surface.punctures k, ∀ z,
          ‖z - q‖ < δ → f n z = 0 ∧ g n z = 0 := by
  classical
  let phase := fun a : ℕ => if a = 0 then c else 1
  have hnon a (_ha : a = 0 ∨ a = 1) : phase a ≠ 0 := by
    dsimp [phase]
    split_ifs
    · exact hc
    · exact one_ne_zero
  obtain ⟨h1, h0⟩ := (mem_slitTraceDomain k c p.val).mp p.property
  have htrace a (ha : a = 0 ∨ a = 1) :
      arcTrace (boundaryArc k a) p.val.1 = phase a • arcTrace (boundaryArc k a) p.val.2 := by
    rcases ha with rfl | rfl
    · simpa only [phase, ite_true] using h0
    · simpa only [phase, show ¬(1 : ℕ) = 0 by decide, ite_false, one_smul] using h1
  obtain ⟨ι, t, a, F, G, F₀, G₀, U, V, ht, ha, hpiece, hint, hrep⟩ :=
    slit_pair_partition_approximation k p.val.1 p.val.2 phase hnon htrace hH hpH hu hv
  refine ⟨(fun n z => F₀ n z + ∑ i ∈ t, F i n z),
    (fun n z => G₀ n z + ∑ i ∈ t, G i n z), U, V, ht, ?_⟩
  have hall := (eventually_all_finset t).mpr hpiece
  filter_upwards [hall, hint, hrep] with n hn hi hr
  refine ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ?_, ?_⟩
  · intro b hb z hz
    constructor
    · exact finite_phase_pair_global_seams t k a phase
        (fun i => F i n) (fun i => G i n) (F₀ n) (G₀ n) ha hn
        hi.2.2.1 hi.2.2.2.2.2 hb hz
    · have h := finite_phase_pair_global_seams t k a (fun b => (phase b)⁻¹)
        (fun i => G i n) (fun i => F i n) (G₀ n) (F₀ n) ha
        (fun i h => (hn i h).swap) hi.2.2.2.2.2 hi.2.2.1 hb hz
      simpa only [phase, apply_ite, inv_one] using h
  · constructor
    · apply slitTraceDomain_of_represented_phase_germs hr.2.1 hr.2.2.2
      intro b hb z hz
      exact finite_phase_pair_global_seams t k a phase
        (fun i => F i n) (fun i => G i n) (F₀ n) (G₀ n) ha hn
        hi.2.2.1 hi.2.2.2.2.2 hb hz
    · exact finite_phase_pair_puncture_holes t hk a phase
        (fun i => F i n) (fun i => G i n) (F₀ n) (G₀ n) hn
        hi.2.2.1 hi.2.2.2.2.2

end KsIndex.Trace
