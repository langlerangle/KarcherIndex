module

public import KsIndexLean.FiniteCopyBracketing
public import KsIndexLean.FiniteCopySpectralEquality

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

set_option maxHeartbeats 800000 in
/-- An `(n+1)`-dimensional trial subspace in the smaller domain, with Rayleigh
quotients bounded above by the larger domain's `n`th eigenvalue, contains a
nonzero weak eigenfunction. Its weak equation holds against every test in the
larger domain, and hence also every test in the smaller domain. -/
lemma finiteCopy_common_eigenfunction_of_infinite_trial
    {ι : Type*} [Fintype ι] (D F : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] [CompleteSpace (finiteH1Domain F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [Infinite (finiteSpectralData F V).eigenbasisIndex] (n : ℕ)
    (htrial : ∃ W : Submodule ℂ (finiteH1Domain D), FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = n + 1 ∧ ∀ u : W,
      (finiteH1Jacobi D V u u).re ≤
        (finiteSpectralData F V).infiniteReciprocalShift (V.C + 1) n *
          ‖finiteH1WeightedValue D u‖ ^ 2) :
    ∃ u : finiteH1Domain D, u ≠ 0 ∧
      (∀ w : finiteH1Domain F,
        finiteH1Jacobi F V (finiteH1Inclusion h u) w =
          ((finiteSpectralData F V).infiniteReciprocalShift (V.C + 1) n : ℂ) *
            inner ℂ (finiteH1WeightedValue F (finiteH1Inclusion h u))
              (finiteH1WeightedValue F w)) ∧
      (∀ w : finiteH1Domain D, finiteH1Jacobi D V u w =
          ((finiteSpectralData F V).infiniteReciprocalShift (V.C + 1) n : ℂ) *
            inner ℂ (finiteH1WeightedValue D u) (finiteH1WeightedValue D w)) := by
  let := finiteH1Domain_innerProductSpace F
  obtain ⟨W, hfd, hd, hb⟩ := htrial
  let := hfd
  let T := finiteH1Inclusion h
  let e := Submodule.equivMapOfInjective T (finiteH1Inclusion_injective h) W
  let : FiniteDimensional ℂ (W.map T) := e.finiteDimensional
  have hdim : n < Module.finrank ℂ (W.map T) := by
    rw [← e.finrank_eq, hd]
    omega
  obtain ⟨v, hv, horth⟩ := exists_nonzero_orthogonal_before
    (finiteH1WeightedValue F) (finiteSpectralData F V).infiniteEigenbasis
    (W.map T) n hdim
  obtain ⟨u, hu, he⟩ := v.property
  have hne : u ≠ 0 := by
    intro hz
    apply hv
    apply Subtype.ext
    exact he.symm.trans ((congrArg T hz).trans T.map_zero)
  have hlo := finiteCopyJacobi_spectral_tail F V n v horth
  have hhi := hb ⟨u, hu⟩
  have hhi' : (finiteH1Jacobi F V v v).re ≤
      (finiteSpectralData F V).infiniteReciprocalShift (V.C + 1) n *
        ‖finiteH1WeightedValue F v‖ ^ 2 := by
    rw [← he]
    exact hhi
  have hev := finiteCopyJacobi_infinite_tail_equality F V n v horth
    (le_antisymm hhi' hlo)
  have hev' : ∀ w : finiteH1Domain F, finiteH1Jacobi F V (T u) w =
      ((finiteSpectralData F V).infiniteReciprocalShift (V.C + 1) n : ℂ) *
        inner ℂ (finiteH1WeightedValue F (T u)) (finiteH1WeightedValue F w) := by
    intro w
    rw [he]
    exact hev w
  exact ⟨u, hne, hev', fun w => hev' (T w)⟩

/-- Same-index equality in infinite-sector bracketing has a common nonzero
weak eigenfunction satisfying the equation against all larger-domain tests. -/
lemma finiteCopy_infinite_common_eigenfunction
    {ι : Type*} [Fintype ι] (D F : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] [CompleteSpace (finiteH1Domain F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [Infinite (finiteSpectralData D V).eigenbasisIndex]
    [Infinite (finiteSpectralData F V).eigenbasisIndex] (n : ℕ)
    (heq : (finiteSpectralData D V).infiniteReciprocalShift (V.C + 1) n =
      (finiteSpectralData F V).infiniteReciprocalShift (V.C + 1) n) :
    ∃ u : finiteH1Domain D, u ≠ 0 ∧
      (∀ w : finiteH1Domain F, finiteH1Jacobi F V (finiteH1Inclusion h u) w =
        ((finiteSpectralData F V).infiniteReciprocalShift (V.C + 1) n : ℂ) *
          inner ℂ (finiteH1WeightedValue F (finiteH1Inclusion h u))
            (finiteH1WeightedValue F w)) ∧
      (∀ w : finiteH1Domain D, finiteH1Jacobi D V u w =
        ((finiteSpectralData F V).infiniteReciprocalShift (V.C + 1) n : ℂ) *
          inner ℂ (finiteH1WeightedValue D u) (finiteH1WeightedValue D w)) := by
  apply finiteCopy_common_eigenfunction_of_infinite_trial D F V h n
  exact (finiteCopyJacobi_infinite_minmax D V n _).mp heq.le

set_option maxHeartbeats 800000 in
/-- An `(n+1)`-dimensional trial subspace in the smaller domain, with Rayleigh
quotients bounded above by the larger domain's `n`th eigenvalue, contains a
nonzero weak eigenfunction. Its weak equation holds against every test in the
larger domain, and hence also every test in the smaller domain. -/
lemma finiteCopy_common_eigenfunction_of_finite_trial
    {ι : Type*} [Fintype ι] (D F : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] [CompleteSpace (finiteH1Domain F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [FiniteDimensional ℂ (WeightedFiniteAmbient F)]
    (n : Fin (Module.finrank ℂ (WeightedFiniteAmbient F)))
    (htrial : ∃ W : Submodule ℂ (finiteH1Domain D), FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = n.val + 1 ∧ ∀ u : W,
      (finiteH1Jacobi D V u u).re ≤
        (finiteSpectralData F V).finiteReciprocalShift (V.C + 1) n *
          ‖finiteH1WeightedValue D u‖ ^ 2) :
    ∃ u : finiteH1Domain D, u ≠ 0 ∧
      (∀ w : finiteH1Domain F,
        finiteH1Jacobi F V (finiteH1Inclusion h u) w =
          ((finiteSpectralData F V).finiteReciprocalShift (V.C + 1) n : ℂ) *
            inner ℂ (finiteH1WeightedValue F (finiteH1Inclusion h u))
              (finiteH1WeightedValue F w)) ∧
      (∀ w : finiteH1Domain D, finiteH1Jacobi D V u w =
          ((finiteSpectralData F V).finiteReciprocalShift (V.C + 1) n : ℂ) *
            inner ℂ (finiteH1WeightedValue D u) (finiteH1WeightedValue D w)) := by
  let := finiteH1Domain_innerProductSpace F
  obtain ⟨W, hfd, hd, hb⟩ := htrial
  let := hfd
  let T := finiteH1Inclusion h
  let e := Submodule.equivMapOfInjective T (finiteH1Inclusion_injective h) W
  let : FiniteDimensional ℂ (W.map T) := e.finiteDimensional
  have hdim : n.val < Module.finrank ℂ (W.map T) := by
    rw [← e.finrank_eq, hd]
    omega
  obtain ⟨v, hv, hcoeff⟩ := exists_nonzero_orthogonal_in_trial
    (finiteH1WeightedValue F)
    (fun i : Fin n.val => (finiteSpectralData F V).finiteEigenbasis.toHilbertBasis
      ⟨i.val, Nat.lt_trans i.isLt n.isLt⟩) (W.map T) (by simpa using hdim)
  have horth : ∀ i < n, inner ℂ
      ((finiteSpectralData F V).finiteEigenbasis.toHilbertBasis i)
      (finiteH1WeightedValue F v) = 0 := by
    intro i hi
    exact hcoeff ⟨i.val, hi⟩
  obtain ⟨u, hu, he⟩ := v.property
  have hne : u ≠ 0 := by
    intro hz
    apply hv
    apply Subtype.ext
    exact he.symm.trans ((congrArg T hz).trans T.map_zero)
  have hlo := finiteCopyJacobi_finite_spectral_tail F V n v horth
  have hhi := hb ⟨u, hu⟩
  have hhi' : (finiteH1Jacobi F V v v).re ≤
      (finiteSpectralData F V).finiteReciprocalShift (V.C + 1) n *
        ‖finiteH1WeightedValue F v‖ ^ 2 := by
    rw [← he]
    exact hhi
  have hev := finiteCopyJacobi_finite_tail_equality F V n v horth
    (le_antisymm hhi' hlo)
  have hev' : ∀ w : finiteH1Domain F, finiteH1Jacobi F V (T u) w =
      ((finiteSpectralData F V).finiteReciprocalShift (V.C + 1) n : ℂ) *
        inner ℂ (finiteH1WeightedValue F (T u)) (finiteH1WeightedValue F w) := by
    intro w
    rw [he]
    exact hev w
  exact ⟨u, hne, hev', fun w => hev' (T w)⟩


/-- Same-index equality in bracketing has a common nonzero
weak eigenfunction satisfying the equation against all larger-domain tests. -/
lemma finiteCopy_finite_to_infinite_common_eigenfunction
    {ι : Type*} [Fintype ι] (D F : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] [CompleteSpace (finiteH1Domain F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [FiniteDimensional ℂ (WeightedFiniteAmbient D)]
    [Infinite (finiteSpectralData F V).eigenbasisIndex] (n : ℕ)
    (hD : n < Module.finrank ℂ (WeightedFiniteAmbient D))
    (heq : (finiteSpectralData D V).finiteReciprocalShift (V.C + 1) ⟨n, hD⟩ =
      (finiteSpectralData F V).infiniteReciprocalShift (V.C + 1) n) :
    ∃ u : finiteH1Domain D, u ≠ 0 ∧
      (∀ w : finiteH1Domain F, finiteH1Jacobi F V (finiteH1Inclusion h u) w =
        ((finiteSpectralData F V).infiniteReciprocalShift (V.C + 1) n : ℂ) *
          inner ℂ (finiteH1WeightedValue F (finiteH1Inclusion h u))
            (finiteH1WeightedValue F w)) ∧
      (∀ w : finiteH1Domain D, finiteH1Jacobi D V u w =
        ((finiteSpectralData F V).infiniteReciprocalShift (V.C + 1) n : ℂ) *
          inner ℂ (finiteH1WeightedValue D u) (finiteH1WeightedValue D w)) := by
  apply finiteCopy_common_eigenfunction_of_infinite_trial D F V h n
  exact (finiteCopyJacobi_finite_minmax D V ⟨n, hD⟩ _).mp heq.le


/-- Same-index equality in bracketing has a common nonzero
weak eigenfunction satisfying the equation against all larger-domain tests. -/
lemma finiteCopy_infinite_to_finite_common_eigenfunction
    {ι : Type*} [Fintype ι] (D F : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] [CompleteSpace (finiteH1Domain F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [Infinite (finiteSpectralData D V).eigenbasisIndex]
    [FiniteDimensional ℂ (WeightedFiniteAmbient F)] (n : ℕ)
    (hF : n < Module.finrank ℂ (WeightedFiniteAmbient F))
    (heq : (finiteSpectralData D V).infiniteReciprocalShift (V.C + 1) n =
      (finiteSpectralData F V).finiteReciprocalShift (V.C + 1) ⟨n, hF⟩) :
    ∃ u : finiteH1Domain D, u ≠ 0 ∧
      (∀ w : finiteH1Domain F, finiteH1Jacobi F V (finiteH1Inclusion h u) w =
        ((finiteSpectralData F V).finiteReciprocalShift (V.C + 1) ⟨n, hF⟩ : ℂ) *
          inner ℂ (finiteH1WeightedValue F (finiteH1Inclusion h u))
            (finiteH1WeightedValue F w)) ∧
      (∀ w : finiteH1Domain D, finiteH1Jacobi D V u w =
        ((finiteSpectralData F V).finiteReciprocalShift (V.C + 1) ⟨n, hF⟩ : ℂ) *
          inner ℂ (finiteH1WeightedValue D u) (finiteH1WeightedValue D w)) := by
  apply finiteCopy_common_eigenfunction_of_finite_trial D F V h ⟨n, hF⟩
  exact (finiteCopyJacobi_infinite_minmax D V n _).mp heq.le


/-- Same-index equality in bracketing has a common nonzero
weak eigenfunction satisfying the equation against all larger-domain tests. -/
lemma finiteCopy_finite_common_eigenfunction
    {ι : Type*} [Fintype ι] (D F : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] [CompleteSpace (finiteH1Domain F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [FiniteDimensional ℂ (WeightedFiniteAmbient D)]
    [FiniteDimensional ℂ (WeightedFiniteAmbient F)] (n : ℕ)
    (hF : n < Module.finrank ℂ (WeightedFiniteAmbient F))
    (hD : n < Module.finrank ℂ (WeightedFiniteAmbient D))
    (heq : (finiteSpectralData D V).finiteReciprocalShift (V.C + 1) ⟨n, hD⟩ =
      (finiteSpectralData F V).finiteReciprocalShift (V.C + 1) ⟨n, hF⟩) :
    ∃ u : finiteH1Domain D, u ≠ 0 ∧
      (∀ w : finiteH1Domain F, finiteH1Jacobi F V (finiteH1Inclusion h u) w =
        ((finiteSpectralData F V).finiteReciprocalShift (V.C + 1) ⟨n, hF⟩ : ℂ) *
          inner ℂ (finiteH1WeightedValue F (finiteH1Inclusion h u))
            (finiteH1WeightedValue F w)) ∧
      (∀ w : finiteH1Domain D, finiteH1Jacobi D V u w =
        ((finiteSpectralData F V).finiteReciprocalShift (V.C + 1) ⟨n, hF⟩ : ℂ) *
          inner ℂ (finiteH1WeightedValue D u) (finiteH1WeightedValue D w)) := by
  apply finiteCopy_common_eigenfunction_of_finite_trial D F V h ⟨n, hF⟩
  exact (finiteCopyJacobi_finite_minmax D V ⟨n, hD⟩ _).mp heq.le


end KsIndex.Spectral
