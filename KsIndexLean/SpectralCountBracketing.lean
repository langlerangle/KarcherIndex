module

public import KsIndexLean.SlitCharacterBracketing
public import KsIndexLean.OrderedSpectralCounts

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open Filter KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

/-- Lowering each ordered eigenvalue can only increase strict sublevel counts. -/
lemma strictSpectralCount_antitone {ν μ : ℕ → ℝ}
    (hν : Tendsto ν atTop atTop) (hμ : Tendsto μ atTop atTop)
    (h : ∀ n, μ n ≤ ν n) (L : ℝ) :
    strictSpectralCount ν hν L ≤ strictSpectralCount μ hμ L :=
  Nat.find_min' _ ((strictSpectralCount_spec μ hμ L).trans (h _))

/-- The weak inequality retains eigenvalues at the threshold, hence nullity at zero. -/
lemma weakSpectralCount_antitone {ν μ : ℕ → ℝ}
    (hν : Tendsto ν atTop atTop) (hμ : Tendsto μ atTop atTop)
    (h : ∀ n, μ n ≤ ν n) (L : ℝ) :
    weakSpectralCount ν hν L ≤ weakSpectralCount μ hμ L :=
  Nat.find_min' _ ((weakSpectralCount_spec μ hμ L).trans_le (h _))

def finiteCopyStrictCountAt {ι : Type*} [Fintype ι]
    (D : Submodule ℂ (ι → ComplexH1)) [CompleteSpace (finiteH1Domain D)]
    (V : BoundedRealPotential) [Infinite (finiteSpectralData D V).eigenbasisIndex]
    (L : ℝ) : ℕ :=
  strictSpectralCount ((finiteSpectralData D V).infiniteReciprocalShift (V.C + 1))
    ((finiteSpectralData D V).infiniteReciprocalShift_tendsto_atTop (V.C + 1)) L

def finiteCopyWeakCountAt {ι : Type*} [Fintype ι]
    (D : Submodule ℂ (ι → ComplexH1)) [CompleteSpace (finiteH1Domain D)]
    (V : BoundedRealPotential) [Infinite (finiteSpectralData D V).eigenbasisIndex]
    (L : ℝ) : ℕ :=
  weakSpectralCount ((finiteSpectralData D V).infiniteReciprocalShift (V.C + 1))
    ((finiteSpectralData D V).infiniteReciprocalShift_tendsto_atTop (V.C + 1)) L

lemma finiteCopy_infinite_count_le {ι : Type*} [Fintype ι]
    (D F : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] [CompleteSpace (finiteH1Domain F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [Infinite (finiteSpectralData D V).eigenbasisIndex]
    [Infinite (finiteSpectralData F V).eigenbasisIndex] (L : ℝ) :
    strictSpectralCount ((finiteSpectralData D V).infiniteReciprocalShift (V.C + 1))
      ((finiteSpectralData D V).infiniteReciprocalShift_tendsto_atTop (V.C + 1)) L ≤
    strictSpectralCount ((finiteSpectralData F V).infiniteReciprocalShift (V.C + 1))
      ((finiteSpectralData F V).infiniteReciprocalShift_tendsto_atTop (V.C + 1)) L ∧
    weakSpectralCount ((finiteSpectralData D V).infiniteReciprocalShift (V.C + 1))
      ((finiteSpectralData D V).infiniteReciprocalShift_tendsto_atTop (V.C + 1)) L ≤
    weakSpectralCount ((finiteSpectralData F V).infiniteReciprocalShift (V.C + 1))
      ((finiteSpectralData F V).infiniteReciprocalShift_tendsto_atTop (V.C + 1)) L :=
  ⟨strictSpectralCount_antitone _ _ (finiteCopy_infinite_eigenvalue_le D F V h) L,
   weakSpectralCount_antitone _ _ (finiteCopy_infinite_eigenvalue_le D F V h) L⟩


/-- Both threshold counts for the paper's character slit brackets. At L = 0
these are negative and nonpositive spectral multiplicities, respectively. -/
lemma paperSlitCharacter_infinite_count_bracket (α : ℝ) (j : ℕ)
    (V : BoundedRealPotential)
    [Infinite (finiteSpectralData (pairFiniteDomain (paperSlitDirichletCharacterDomain j)) V).eigenbasisIndex]
    [Infinite (finiteSpectralData (pairFiniteDomain (paperSlitCharacterDomain α j)) V).eigenbasisIndex]
    [Infinite (finiteSpectralData (pairFiniteDomain (paperSlitNeumannCharacterDomain j)) V).eigenbasisIndex]
    (L : ℝ) :
    finiteCopyStrictCountAt (pairFiniteDomain (paperSlitDirichletCharacterDomain j)) V L ≤
    finiteCopyStrictCountAt (pairFiniteDomain (paperSlitCharacterDomain α j)) V L ∧
    finiteCopyStrictCountAt (pairFiniteDomain (paperSlitCharacterDomain α j)) V L ≤
    finiteCopyStrictCountAt (pairFiniteDomain (paperSlitNeumannCharacterDomain j)) V L ∧
    finiteCopyWeakCountAt (pairFiniteDomain (paperSlitDirichletCharacterDomain j)) V L ≤
    finiteCopyWeakCountAt (pairFiniteDomain (paperSlitCharacterDomain α j)) V L ∧
    finiteCopyWeakCountAt (pairFiniteDomain (paperSlitCharacterDomain α j)) V L ≤
    finiteCopyWeakCountAt (pairFiniteDomain (paperSlitNeumannCharacterDomain j)) V L := by
  have hDP := finiteCopy_infinite_count_le _ _ V
    (pairFiniteDomain_mono (paperSlitDirichletCharacter_le_phase α j)) L
  have hPN := finiteCopy_infinite_count_le _ _ V
    (pairFiniteDomain_mono (paperSlitCharacter_le_Neumann α j)) L
  exact ⟨hDP.1, hPN.1, hDP.2, hPN.2⟩

end KsIndex.Spectral
