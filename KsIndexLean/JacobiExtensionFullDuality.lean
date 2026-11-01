module

public import KsIndexLean.JacobiExtensionForm

@[expose] public section


/-! The DtN duality identity against every weak H¹ test, without a
mean-zero restriction on the test's trace. -/
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.DtNCircle KsIndex.CircleSobolev KsIndex.DtnBridge

/-- Full-test Green duality; the zero mode of the test is allowed. -/
theorem jacobiExtensionCLM_full_duality {k : ℕ} (hk : 2 ≤ k)
    (f : dotted (1 / 2 : ℝ)) (v : ComplexH1) :
    weakJacobi (surfacePotential k) (jacobiExtensionCLM hk f) v =
      duality (1 / 2 : ℝ) (dottedDtnCLM k f).val (halfDiskTraceCLM v) := by
  change weakJacobi (surfacePotential k) (jacobiExtensionH1 hk f.val) v = _
  rw [jacobiExtensionH1_weak_pairing, duality_eq_tsum]
  congr 1
  have h0 : (starRingEnd ℂ)
      (coeff (-(1 / 2 : ℝ)) (dottedDtnCLM k f).val 0) *
      coeff (1 / 2 : ℝ) (halfDiskTraceCLM v) 0 = 0 := by
    rw [(mem_dotted _ _).mp (dottedDtnCLM k f).property, map_zero, zero_mul]
  rw [tsum_int_eq_nz _ h0]
  apply tsum_congr
  intro n
  rw [coeff_dottedDtnCLM, map_mul, Complex.conj_ofReal]
  congr 1
  exact (coeff_halfDiskTrace v n).symm

end KsIndex.Trace
