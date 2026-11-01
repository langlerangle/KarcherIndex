module

public import KsIndexLean.PaperPairTwistedSmooth
public import KsIndexLean.TwistedSmoothExtension
public import KsIndexLean.EnergySmooth

@[expose] public section


/-! The normalized paper pair extended in lower-first cyclic order. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.PaperSlitTransport
open KsIndex.Trace KsIndex.Surface KsIndex.Twisted

/-- Cyclic extension by `extF`; the phase on copy n is c^(n.val/2). -/
def SmoothSlitPair.cyclic {c : ℂ} (p : SmoothSlitPair c) (m : ℕ) : ZMod (2 * m) → ℂ → ℂ :=
  extF m c (smoothPairCopies p.upper p.lower)

lemma SmoothSlitPair.copies_eq {c : ℂ} (p : SmoothSlitPair c) (n : ZMod (2 * 1)) :
    smoothPairCopies p.upper p.lower n = if n = 0 then p.lower else p.upper := by
  simp only [smoothPairCopies, closedDiskRestriction_eq_of_exterior p.lower_exterior,
    closedDiskRestriction_eq_of_exterior p.upper_exterior]

lemma SmoothSlitPair.cyclic_smooth {c : ℂ} (p : SmoothSlitPair c)
    {m : ℕ} [NeZero m] (hc : c ^ m = 1) : IsSmooth 3 m (p.cyclic m) :=
  extF_isSmooth hc p.isSmoothTw

lemma SmoothSlitPair.cyclic_energy {c : ℂ} (p : SmoothSlitPair c) (m : ℕ)
    (n : ZMod (2 * m)) : IntegrableOn (gradSq (p.cyclic m n)) Surface.disk := by
  have hp : ∀ a, IntegrableOn (gradSq (smoothPairCopies p.upper p.lower a)) Surface.disk := by
    intro a
    rw [p.copies_eq a]
    split_ifs
    · exact p.lower_energy
    · exact p.upper_energy
  change IntegrableOn (gradSq (fun z => c ^ (n.val / 2) *
    smoothPairCopies p.upper p.lower _ z)) Surface.disk
  have he : gradSq (fun z => c ^ (n.val / 2) * smoothPairCopies p.upper p.lower
      ((n.val % 2 : ℕ) : ZMod (2 * 1)) z) =
      (fun z => ‖c ^ (n.val / 2)‖ ^ 2 * gradSq (smoothPairCopies p.upper p.lower
        ((n.val % 2 : ℕ) : ZMod (2 * 1))) z) := by
    funext z
    exact gradSq_const_mul _ _ _
  rw [he]
  exact (hp _).const_mul _

lemma SmoothSlitPair.cyclic_mass {c : ℂ} (p : SmoothSlitPair c) (m : ℕ)
    (n : ZMod (2 * m)) : IntegrableOn (fun z => ‖p.cyclic m n z‖ ^ 2) Surface.disk := by
  have hp : ∀ a, IntegrableOn (fun z => ‖smoothPairCopies p.upper p.lower a z‖ ^ 2)
      Surface.disk := by
    intro a
    rw [p.copies_eq a]
    split_ifs
    · exact p.lower_mass
    · exact p.upper_mass
  change IntegrableOn (fun z => ‖c ^ (n.val / 2) *
    smoothPairCopies p.upper p.lower _ z‖ ^ 2) Surface.disk
  simp_rw [norm_mul, mul_pow]
  exact (hp _).const_mul _

lemma SmoothSlitPair.cyclic_punctureZero {c : ℂ} (p : SmoothSlitPair c) (m : ℕ) :
    PunctureZero 3 (p.cyclic m) := by
  intro n z hz
  simp only [SmoothSlitPair.cyclic, extF, p.copies_eq]
  split_ifs <;> simp only [p.lower_puncture z hz, p.upper_puncture z hz, mul_zero]

lemma SmoothSlitPair.cyclic_flat_pde {c : ℂ} (p : SmoothSlitPair c) (m : ℕ)
    (n : ZMod (2 * m)) {z : ℂ} (hz : z ∈ Surface.disk) :
    laplacian (p.cyclic m n) z + (potV 3 z : ℂ) * p.cyclic m n z = 0 := by
  let f := smoothPairCopies p.upper p.lower ((n.val % 2 : ℕ) : ZMod (2 * 1))
  have hf : ContDiffAt ℝ ∞ f z := (p.isSmoothTw.1 _).contDiffAt (Metric.isOpen_ball.mem_nhds hz)
  have hp : laplacian f z + (potV 3 z : ℂ) * f z = 0 := by
    dsimp only [f]
    rw [p.copies_eq]
    split_ifs
    · exact p.lower_pde z hz
    · exact p.upper_pde z hz
  change laplacian ((c ^ (n.val / 2)) • f) z + (potV 3 z : ℂ) * (c ^ (n.val / 2) * f z) = 0
  rw [laplacian_smul _ hf]
  linear_combination c ^ (n.val / 2) * hp

end KsIndex.PaperSlitTransport
