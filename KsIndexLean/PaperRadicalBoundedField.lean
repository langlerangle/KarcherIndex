module

public import KsIndexLean.PaperCyclicEnergySmooth
public import KsIndexLean.GammaEndProducer
public import KsIndexLean.PaperSectorParameters
public import KsIndexLean.WeakSmoothCharacter

@[expose] public section


/-! Actual bounded Jacobi fields from the paper radical, with the original
lower-first copy identification. Rotation-character identification is separate. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.PaperSlitTransport
open KsIndex.Trace KsIndex.Surface KsIndex.Twisted KsIndex.WeakH1 KsIndex.PaperSlitAdapter

lemma SmoothSlitPair.cyclic_zero {c : ℂ} (p : SmoothSlitPair c)
    {m : ℕ} [NeZero m] : p.cyclic m 0 = p.lower := by
  funext z
  simp [SmoothSlitPair.cyclic, extF, p.copies_eq]

lemma SmoothSlitPair.cyclic_one {c : ℂ} (p : SmoothSlitPair c)
    {m : ℕ} [NeZero m] : p.cyclic m 1 = p.upper := by
  have : Fact (1 < 2 * m) := ⟨by have := NeZero.ne m; omega⟩
  have h10 : (1 : ZMod (2 * 1)) ≠ 0 := by decide
  funext z
  simp [SmoothSlitPair.cyclic, extF, ZMod.val_one, p.copies_eq, h10]

lemma SmoothSlitPair.cyclic_shift {c : ℂ} (p : SmoothSlitPair c)
    {m : ℕ} [NeZero m] (hc : c ^ m = 1) (n : ZMod (2 * m)) (z : ℂ) :
    p.cyclic m (n + 2) z = c * p.cyclic m n z := by
  exact (mem_shift_iff.mp (extE_mem_shift hc
    (fun a => smoothPairCopies p.upper p.lower a.1 a.2))) n z

lemma SmoothSlitPair.cyclic_disk_character {c d : ℂ} (p : SmoothSlitPair c)
    (θ : ℝ) (hu : ∀ z ∈ (WeakH1.disk : Set ℂ),
      p.upper (planeRotation θ z) = d * p.upper z)
    (hl : ∀ z ∈ (WeakH1.disk : Set ℂ),
      p.lower (planeRotation θ z) = d * p.lower z)
    (m : ℕ) (n : ZMod (2 * m)) {z : ℂ} (hz : z ∈ (WeakH1.disk : Set ℂ)) :
    p.cyclic m n (planeRotation θ z) = d * p.cyclic m n z := by
  simp only [SmoothSlitPair.cyclic, extF, p.copies_eq]
  split_ifs
  · rw [hl z hz]; ring
  · rw [hu z hz]; ring

theorem SmoothSlitPair.cyclic_bounded {c : ℂ} (p : SmoothSlitPair c)
    {m : ℕ} [NeZero m] (hc : c ^ m = 1) : IsBounded (p.cyclic m) :=
  KsIndex.GammaProducer.bounded_of_jacobi_energySmooth
    (p.cyclic_mem_energySmooth hc) (p.cyclic_isJacobiField m)

/-- Every actual paper radical element produces a bounded smooth finite-energy
Jacobi field on the cyclic chain when its phase closes after m pairs. The weak
upper component is recovered on copy one, the lower on copy zero. -/
theorem pair_radical_bounded_field {α : ℝ} {j m : ℕ} [NeZero m]
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0)
    (hc : Complex.exp ((2 * Real.pi * α) * Complex.I) ^ m = 1) :
    ∃ U : ZMod (2 * m) → ℂ → ℂ,
      U ∈ KsIndex.FaithfulInjection.EnergySmooth 3 m ∧ IsJacobiField 3 m U ∧
      IsBounded U ∧
      (∀ a z, z ∈ (WeakH1.disk : Set ℂ) →
        U a (planeRotation (-(2 * Real.pi) / 3) z) = FormIndex.zeta 3 ^ j * U a z) ∧
      (∀ n z, U (n + 2) z = Complex.exp ((2 * Real.pi * α) * Complex.I) * U n z) ∧
      valueCLM u.val.1 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] U 1 ∧
      valueCLM u.val.2 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] U 0 := by
  obtain ⟨p, hp, hq⟩ := pair_radical_smooth_pair u hrad
  obtain ⟨hpu, hpl⟩ := pair_smooth_representatives_character u
    p.upper_smooth.continuousOn p.lower_smooth.continuousOn hp hq
  refine ⟨p.cyclic m, p.cyclic_mem_energySmooth hc, p.cyclic_isJacobiField m,
    p.cyclic_bounded hc, (fun a z hz => p.cyclic_disk_character _ hpu hpl m a hz),
    p.cyclic_shift hc, ?_, ?_⟩
  · simpa only [p.cyclic_one] using hp
  · simpa only [p.cyclic_zero] using hq

/-- The paper's rational Fourier phases satisfy the closing condition; no
extra monodromy hypothesis is required in this specialization. -/
theorem rational_pair_radical_bounded_field {n j m : ℕ} [NeZero m]
    (u : paperSlitCharacterDomain ((n : ℝ) / m) j) (hrad : ∀ w, Bpair u w = 0) :
    ∃ U : ZMod (2 * m) → ℂ → ℂ,
      U ∈ KsIndex.FaithfulInjection.EnergySmooth 3 m ∧ IsJacobiField 3 m U ∧
      IsBounded U ∧
      (∀ a z, z ∈ (WeakH1.disk : Set ℂ) →
        U a (planeRotation (-(2 * Real.pi) / 3) z) = FormIndex.zeta 3 ^ j * U a z) ∧
      (∀ a z, U (a + 2) z = Spherical.paperPhase ((n : ℝ) / m) * U a z) ∧
      valueCLM u.val.1 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] U 1 ∧
      valueCLM u.val.2 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] U 0 :=
  pair_radical_bounded_field u hrad (Spherical.paperRationalPhase_root m n)

end KsIndex.PaperSlitTransport
