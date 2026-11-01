module

public import KsIndexLean.AlphaFourModeCertificate

@[expose] public section


/-! Rational finite Gram matrix and certified entrywise enclosure. -/
namespace KsIndex.AlphaFourMode

def mode (i : Fin 4) : ℤ := (i : ℕ) - 2

def rationalWeight (n : ℤ) : ℚ :=
  (((6*n+1 : ℤ) : ℚ)^2-4) / |((6*n+1 : ℤ) : ℚ)| + 363/16

def rationalKernel (m n : ℤ) : ℚ := (-1)^(m-n) / ((2*(m-n)+1 : ℤ) : ℚ)

def finiteGram (i j : Fin 4) : ℚ :=
  ∑ n ∈ Finset.range 129,
    rationalKernel (mode i) ((n:ℤ)-64) * rationalKernel (mode j) ((n:ℤ)-64) /
      rationalWeight ((n:ℤ)-64)

def roundedGram : Matrix (Fin 4) (Fin 4) ℚ :=
  !![805223/10000000,14067/5000000,-112247/10000000,76169/10000000;
     14067/5000000,499151/5000000,98179/5000000,-25047/2500000;
     -112247/10000000,98179/5000000,971379/10000000,251/625000;
     76169/10000000,-25047/2500000,251/625000,151817/2000000]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- Exact rational computation; no native evaluator or floating-point premise. -/
lemma finiteGram_enclosure : ∀ i j, |finiteGram i j - roundedGram i j| ≤ (1/10000000:ℚ) := by
  decide +kernel

end KsIndex.AlphaFourMode
