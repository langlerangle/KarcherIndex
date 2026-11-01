module

public import KsIndexLean.GeneralDiskClassical
public import KsIndexLean.PaperSlitLocalTests
public import KsIndexLean.WeakDirichletModeSelection

@[expose] public section


/-! # Interior regularity from weak Dirichlet tests

Vanishing of the weak Jacobi pairing against every full zero-trace test gives the
real and imaginary weak equations on the open disk. For `2 ≤ k`, interior elliptic
regularity then supplies a smooth representative satisfying the classical equation
there. The argument uses compactly supported real tests from `PaperSlitLocalTests`.

The zero-trace condition is imposed on the test functions, not on `u`. The smooth
representative agrees with `u` almost everywhere on the disk; no boundary regularity
is asserted here. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Weq
open KsIndex.Trace KsIndex.WeakH1 KsIndex.PaperSlitTransport KsIndex.FormIndex

lemma fullDirichlet_tests_real_weak (k : ℕ) (u : ComplexH1)
    (hQ : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v = 0) :
    PunctureRemoval.IsWeakSolOn (Surface.potV k) disk (rePart u) ∧
      PunctureRemoval.IsWeakSolOn (Surface.potV k) disk (imPart u) := by
  have hpair (φ : ℂ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ (disk : Set ℂ)) :=
    realTest_pairing_zero_components k u φ hφ hc
      (hQ (realTestH1 φ hφ hc)
        ((mem_fullZeroTrace_iff _).mpr (diskTrace_realTestH1 φ hφ hc hs)))
  exact ⟨fun φ hφ hc hs => (hpair φ hφ hc hs).1,
    fun φ hφ hc hs => (hpair φ hφ hc hs).2⟩

/-- The input consists only of actual weak Jacobi tests, not assumed PDE regularity. -/
theorem fullDirichlet_tests_classical {k : ℕ} (hk : 2 ≤ k) (u : ComplexH1)
    (hQ : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v = 0) :
    ∃ f : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) f (disk : Set ℂ) ∧
      valueCLM u =ᵐ[volume.restrict (disk : Set ℂ)] f ∧
      ∀ z ∈ (disk : Set ℂ), Surface.laplacian f z + (Surface.potV k z : ℂ) * f z = 0 := by
  obtain ⟨hr, hi⟩ := fullDirichlet_tests_real_weak k u hQ
  exact general_disk_weakSol_classical hk u hr hi

end KsIndex.Weq
