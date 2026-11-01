module

public import KsIndexLean.D5Discharge
public import KsIndexLean.NamedDomainSpectrum

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical KsIndex.SingleDisk
open KsIndex.FormIndex KsIndex.SingleDiskBridge

/-- For `k ≥ 2`, the natural smooth-core index equals the weak mixed-sector
negative spectral count in the infinite eigenbasis case. Density and
quadratic-form identification compare the core index with the weak form index;
the spectral index theorem then identifies that index with the count. -/
lemma seamNat_eq_infinite_spectral_count {k : ℕ} (hk : 2 ≤ k)
    (r : ℕ) (b1 b0 : Bool)
    [Infinite (diskSpectralData (mixedCharacterDomain k r b1 b0) (surfacePotential k)).eigenbasisIndex] :
    seamNat k b1 b0 r =
      (diskNegativeCount (mixedCharacterDomain k r b1 b0) (surfacePotential k) : ℕ∞) := by
  calc
    _ = KsIndex.NegativeDensity.negativeIndex
        (fun u : mixedCharacterDomain k r b1 b0 =>
          (weakJacobi (surfacePotential k) u.val u.val).re) :=
      seamNat_eq_negativeIndex hk r b1 b0
    _ = _ := disk_negativeIndex_eq_count
      (mixedCharacterDomain k r b1 b0) (surfacePotential k)

/-- For `k ≥ 2`, the reflected smooth-core index equals the weak mixed-sector
negative spectral count in the infinite eigenbasis case. Density and
quadratic-form identification compare the core index with the weak form index;
the spectral index theorem then identifies that index with the count. -/
lemma reflSeam_eq_infinite_spectral_count {k : ℕ} (hk : 2 ≤ k)
    (r : ℕ) (b1 b0 : Bool)
    [Infinite (diskSpectralData (mixedCharacterDomain k r b1 b0) (surfacePotential k)).eigenbasisIndex] :
    formIndex (Qd k) (KsIndex.TwistSwap.ReflCc k (sgn b1) (sgn b0) ⊓ Erot1 k r) =
      (diskNegativeCount (mixedCharacterDomain k r b1 b0) (surfacePotential k) : ℕ∞) := by
  calc
    _ = KsIndex.NegativeDensity.negativeIndex
        (fun u : mixedCharacterDomain k r b1 b0 =>
          (weakJacobi (surfacePotential k) u.val u.val).re) :=
      reflSeam_eq_negativeIndex hk r b1 b0
    _ = _ := disk_negativeIndex_eq_count
      (mixedCharacterDomain k r b1 b0) (surfacePotential k)

/-- For `k ≥ 2`, the natural smooth-core index equals the weak mixed-sector
negative spectral count in the finite-dimensional weighted ambient space case. Density and
quadratic-form identification compare the core index with the weak form index;
the spectral index theorem then identifies that index with the count. -/
lemma seamNat_eq_finite_spectral_count {k : ℕ} (hk : 2 ≤ k)
    (r : ℕ) (b1 b0 : Bool)
    [FiniteDimensional ℂ (WeightedDiskAmbient (mixedCharacterDomain k r b1 b0))] :
    seamNat k b1 b0 r =
      ((diskSpectralData (mixedCharacterDomain k r b1 b0) (surfacePotential k)).finiteStrictCount ((surfacePotential k).C + 1) 0 : ℕ∞) := by
  calc
    _ = KsIndex.NegativeDensity.negativeIndex
        (fun u : mixedCharacterDomain k r b1 b0 =>
          (weakJacobi (surfacePotential k) u.val u.val).re) :=
      seamNat_eq_negativeIndex hk r b1 b0
    _ = _ := disk_negativeIndex_eq_finite_count
      (mixedCharacterDomain k r b1 b0) (surfacePotential k)

/-- For `k ≥ 2`, the reflected smooth-core index equals the weak mixed-sector
negative spectral count in the finite-dimensional weighted ambient space case. Density and
quadratic-form identification compare the core index with the weak form index;
the spectral index theorem then identifies that index with the count. -/
lemma reflSeam_eq_finite_spectral_count {k : ℕ} (hk : 2 ≤ k)
    (r : ℕ) (b1 b0 : Bool)
    [FiniteDimensional ℂ (WeightedDiskAmbient (mixedCharacterDomain k r b1 b0))] :
    formIndex (Qd k) (KsIndex.TwistSwap.ReflCc k (sgn b1) (sgn b0) ⊓ Erot1 k r) =
      ((diskSpectralData (mixedCharacterDomain k r b1 b0) (surfacePotential k)).finiteStrictCount ((surfacePotential k).C + 1) 0 : ℕ∞) := by
  calc
    _ = KsIndex.NegativeDensity.negativeIndex
        (fun u : mixedCharacterDomain k r b1 b0 =>
          (weakJacobi (surfacePotential k) u.val u.val).re) :=
      reflSeam_eq_negativeIndex hk r b1 b0
    _ = _ := disk_negativeIndex_eq_finite_count
      (mixedCharacterDomain k r b1 b0) (surfacePotential k)

end KsIndex.Spectral
