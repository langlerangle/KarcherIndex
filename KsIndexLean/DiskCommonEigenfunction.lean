module

public import KsIndexLean.DiskBracketing
public import KsIndexLean.DiskSpectralEquality

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

/-- Only linear algebra in the trial domain is needed for orthogonality. -/
lemma linear_trial_orthogonal {E H ι : Type*} [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι]
    (J : E →ₗ[ℂ] H) (b : ι → H) (W : Submodule ℂ E)
    [FiniteDimensional ℂ W] (hdim : Fintype.card ι < Module.finrank ℂ W) :
    ∃ u : W, u ≠ 0 ∧ ∀ i, inner ℂ (b i) (J u) = 0 := by
  let L : W →ₗ[ℂ] (ι → ℂ) :=
    { toFun := fun u i => inner ℂ (b i) (J u)
      map_add' := fun u v => by ext i; simp
      map_smul' := fun a u => by ext i; simp }
  have hker : L.ker ≠ ⊥ := by
    intro he
    have hd := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp he)
    have heq : Module.finrank ℂ (ι → ℂ) = Fintype.card ι := by simp
    rw [heq] at hd
    omega
  obtain ⟨u, hu, hne⟩ := L.ker.ne_bot_iff.mp hker
  exact ⟨u, hne, fun i => congrFun (LinearMap.mem_ker.mp hu) i⟩

lemma disk_trial_orthogonal_before (F : Submodule ℂ ComplexH1)
    [CompleteSpace F] (V : BoundedRealPotential)
    [Infinite (diskSpectralData F V).eigenbasisIndex]
    (W : Submodule ℂ F) [FiniteDimensional ℂ W] (n : ℕ)
    (hdim : n < Module.finrank ℂ W) :
    ∃ v : W, v ≠ 0 ∧ ∀ i < n, inner ℂ
      ((diskSpectralData F V).infiniteEigenbasis i)
      (weightedDiskAmbientEmbedding F v) = 0 := by
  obtain ⟨v, hv, hc⟩ := linear_trial_orthogonal (weightedDiskAmbientEmbedding F).toLinearMap
    (fun i : Fin n => (diskSpectralData F V).infiniteEigenbasis i.val) W (by simpa using hdim)
  exact ⟨v, hv, fun i hi => hc ⟨i, hi⟩⟩

lemma disk_trial_orthogonal_finite (F : Submodule ℂ ComplexH1)
    [CompleteSpace F] (V : BoundedRealPotential)
    [FiniteDimensional ℂ (WeightedDiskAmbient F)]
    (W : Submodule ℂ F) [FiniteDimensional ℂ W]
    (n : Fin (Module.finrank ℂ (WeightedDiskAmbient F)))
    (hdim : n.val < Module.finrank ℂ W) :
    ∃ v : W, v ≠ 0 ∧ ∀ i < n, inner ℂ
      ((diskSpectralData F V).finiteEigenbasis.toHilbertBasis i)
      (weightedDiskAmbientEmbedding F v) = 0 := by
  obtain ⟨v, hv, hc⟩ := linear_trial_orthogonal
    (weightedDiskAmbientEmbedding F).toLinearMap
    (fun i : Fin n.val => (diskSpectralData F V).finiteEigenbasis.toHilbertBasis
      ⟨i.val, Nat.lt_trans i.isLt n.isLt⟩) W (by simpa using hdim)
  exact ⟨v, hv, fun i hi => hc ⟨i.val, hi⟩⟩

set_option maxHeartbeats 800000 in
/-- Equality at an attained trial bound produces a nonzero eigenfunction in the
smaller domain which satisfies the weak equation against *all* larger-domain
tests. This is stronger than membership in both value-trace domains. -/
lemma disk_common_eigenfunction_of_infinite_trial
     (D F : Submodule ℂ ComplexH1)
    [CompleteSpace (D)] [CompleteSpace (F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [Infinite (diskSpectralData F V).eigenbasisIndex] (n : ℕ)
    (htrial : ∃ W : Submodule ℂ (D), FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = n + 1 ∧ ∀ u : W,
      (weakJacobi V u u).re ≤
        (diskSpectralData F V).infiniteReciprocalShift (V.C + 1) n *
          ‖weightedDiskAmbientEmbedding D u‖ ^ 2) :
    ∃ u : D, u ≠ 0 ∧
      (∀ w : F,
        weakJacobi V (Submodule.inclusion h u) w =
          ((diskSpectralData F V).infiniteReciprocalShift (V.C + 1) n : ℂ) *
            inner ℂ (weightedDiskAmbientEmbedding F (Submodule.inclusion h u))
              (weightedDiskAmbientEmbedding F w)) ∧
      (∀ w : D, weakJacobi V u w =
          ((diskSpectralData F V).infiniteReciprocalShift (V.C + 1) n : ℂ) *
            inner ℂ (weightedDiskAmbientEmbedding D u) (weightedDiskAmbientEmbedding D w)) := by
  obtain ⟨W, hfd, hd, hb⟩ := htrial
  let := hfd
  let T := Submodule.inclusion h
  let e := Submodule.equivMapOfInjective T (Submodule.inclusion_injective h) W
  let : FiniteDimensional ℂ (W.map T) := e.finiteDimensional
  have hdim : n < Module.finrank ℂ (W.map T) := by
    rw [← e.finrank_eq, hd]
    omega
  have ho := disk_trial_orthogonal_before F V (W.map T) n hdim
  let v := Classical.choose ho
  have hv := (Classical.choose_spec ho).1
  have horth := (Classical.choose_spec ho).2
  let u : D := (e.symm v).val
  have hu : u ∈ W := (e.symm v).property
  have he : T u = v.val := congrArg Subtype.val (e.apply_symm_apply v)
  have hne : u ≠ 0 := by
    intro hz
    apply hv
    apply Subtype.ext
    exact he.symm.trans ((congrArg T hz).trans T.map_zero)
  have hlo := diskJacobi_spectral_tail F V n v horth
  have hhi := hb ⟨u, hu⟩
  have hhi' : (weakJacobi V v v).re ≤
      (diskSpectralData F V).infiniteReciprocalShift (V.C + 1) n *
        ‖weightedDiskAmbientEmbedding F v‖ ^ 2 := by
    rw [← he]
    exact hhi
  have hev := diskJacobi_infinite_tail_equality F V n v horth
    (le_antisymm hhi' hlo)
  have hev' : ∀ w : F, weakJacobi V (T u) w =
      ((diskSpectralData F V).infiniteReciprocalShift (V.C + 1) n : ℂ) *
        inner ℂ (weightedDiskAmbientEmbedding F (T u)) (weightedDiskAmbientEmbedding F w) := by
    intro w
    calc
      weakJacobi V (T u) w = weakJacobi V v.val w :=
        congrArg (fun x : F => weakJacobi V x w) he
      _ = ((diskSpectralData F V).infiniteReciprocalShift (V.C + 1) n : ℂ) *
          inner ℂ (weightedDiskAmbientEmbedding F v.val) (weightedDiskAmbientEmbedding F w) := hev w
      _ = _ := congrArg (fun x : F =>
        ((diskSpectralData F V).infiniteReciprocalShift (V.C + 1) n : ℂ) *
          inner ℂ (weightedDiskAmbientEmbedding F x) (weightedDiskAmbientEmbedding F w)) he.symm
  exact ⟨u, hne, hev', fun w => hev' (T w)⟩

/-- Same-index equality in infinite-sector bracketing has a common nonzero
weak eigenfunction, including the larger test space's natural conditions. -/
lemma disk_infinite_common_eigenfunction
     (D F : Submodule ℂ ComplexH1)
    [CompleteSpace (D)] [CompleteSpace (F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [Infinite (diskSpectralData D V).eigenbasisIndex]
    [Infinite (diskSpectralData F V).eigenbasisIndex] (n : ℕ)
    (heq : (diskSpectralData D V).infiniteReciprocalShift (V.C + 1) n =
      (diskSpectralData F V).infiniteReciprocalShift (V.C + 1) n) :
    ∃ u : D, u ≠ 0 ∧
      (∀ w : F, weakJacobi V (Submodule.inclusion h u) w =
        ((diskSpectralData F V).infiniteReciprocalShift (V.C + 1) n : ℂ) *
          inner ℂ (weightedDiskAmbientEmbedding F (Submodule.inclusion h u))
            (weightedDiskAmbientEmbedding F w)) ∧
      (∀ w : D, weakJacobi V u w =
        ((diskSpectralData F V).infiniteReciprocalShift (V.C + 1) n : ℂ) *
          inner ℂ (weightedDiskAmbientEmbedding D u) (weightedDiskAmbientEmbedding D w)) := by
  apply disk_common_eigenfunction_of_infinite_trial D F V h n
  exact (diskJacobi_infinite_minmax D V n _).mp heq.le

set_option maxHeartbeats 800000 in
/-- Equality at an attained trial bound produces a nonzero eigenfunction in the
smaller domain which satisfies the weak equation against *all* larger-domain
tests. This is stronger than membership in both value-trace domains. -/
lemma disk_common_eigenfunction_of_finite_trial
     (D F : Submodule ℂ ComplexH1)
    [CompleteSpace (D)] [CompleteSpace (F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [FiniteDimensional ℂ (WeightedDiskAmbient F)]
    (n : Fin (Module.finrank ℂ (WeightedDiskAmbient F)))
    (htrial : ∃ W : Submodule ℂ (D), FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = n.val + 1 ∧ ∀ u : W,
      (weakJacobi V u u).re ≤
        (diskSpectralData F V).finiteReciprocalShift (V.C + 1) n *
          ‖weightedDiskAmbientEmbedding D u‖ ^ 2) :
    ∃ u : D, u ≠ 0 ∧
      (∀ w : F,
        weakJacobi V (Submodule.inclusion h u) w =
          ((diskSpectralData F V).finiteReciprocalShift (V.C + 1) n : ℂ) *
            inner ℂ (weightedDiskAmbientEmbedding F (Submodule.inclusion h u))
              (weightedDiskAmbientEmbedding F w)) ∧
      (∀ w : D, weakJacobi V u w =
          ((diskSpectralData F V).finiteReciprocalShift (V.C + 1) n : ℂ) *
            inner ℂ (weightedDiskAmbientEmbedding D u) (weightedDiskAmbientEmbedding D w)) := by
  obtain ⟨W, hfd, hd, hb⟩ := htrial
  let := hfd
  let T := Submodule.inclusion h
  let e := Submodule.equivMapOfInjective T (Submodule.inclusion_injective h) W
  let : FiniteDimensional ℂ (W.map T) := e.finiteDimensional
  have hdim : n.val < Module.finrank ℂ (W.map T) := by
    rw [← e.finrank_eq, hd]
    omega
  have ho := disk_trial_orthogonal_finite F V (W.map T) n hdim
  let v := Classical.choose ho
  have hv := (Classical.choose_spec ho).1
  have horth := (Classical.choose_spec ho).2
  let u : D := (e.symm v).val
  have hu : u ∈ W := (e.symm v).property
  have he : T u = v.val := congrArg Subtype.val (e.apply_symm_apply v)
  have hne : u ≠ 0 := by
    intro hz
    apply hv
    apply Subtype.ext
    exact he.symm.trans ((congrArg T hz).trans T.map_zero)
  have hlo := diskJacobi_finite_spectral_tail F V n v horth
  have hhi := hb ⟨u, hu⟩
  have hhi' : (weakJacobi V v v).re ≤
      (diskSpectralData F V).finiteReciprocalShift (V.C + 1) n *
        ‖weightedDiskAmbientEmbedding F v‖ ^ 2 := by
    rw [← he]
    exact hhi
  have hev := diskJacobi_finite_tail_equality F V n v horth
    (le_antisymm hhi' hlo)
  have hev' : ∀ w : F, weakJacobi V (T u) w =
      ((diskSpectralData F V).finiteReciprocalShift (V.C + 1) n : ℂ) *
        inner ℂ (weightedDiskAmbientEmbedding F (T u)) (weightedDiskAmbientEmbedding F w) := by
    intro w
    calc
      weakJacobi V (T u) w = weakJacobi V v.val w :=
        congrArg (fun x : F => weakJacobi V x w) he
      _ = ((diskSpectralData F V).finiteReciprocalShift (V.C + 1) n : ℂ) *
          inner ℂ (weightedDiskAmbientEmbedding F v.val) (weightedDiskAmbientEmbedding F w) := hev w
      _ = _ := congrArg (fun x : F =>
        ((diskSpectralData F V).finiteReciprocalShift (V.C + 1) n : ℂ) *
          inner ℂ (weightedDiskAmbientEmbedding F x) (weightedDiskAmbientEmbedding F w)) he.symm
  exact ⟨u, hne, hev', fun w => hev' (T w)⟩


/-- Same-index equality in bracketing has a common nonzero
weak eigenfunction, including the larger test space's natural conditions. -/
lemma disk_finite_to_infinite_common_eigenfunction
     (D F : Submodule ℂ ComplexH1)
    [CompleteSpace (D)] [CompleteSpace (F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [FiniteDimensional ℂ (WeightedDiskAmbient D)]
    [Infinite (diskSpectralData F V).eigenbasisIndex] (n : ℕ)
    (hD : n < Module.finrank ℂ (WeightedDiskAmbient D))
    (heq : (diskSpectralData D V).finiteReciprocalShift (V.C + 1) ⟨n, hD⟩ =
      (diskSpectralData F V).infiniteReciprocalShift (V.C + 1) n) :
    ∃ u : D, u ≠ 0 ∧
      (∀ w : F, weakJacobi V (Submodule.inclusion h u) w =
        ((diskSpectralData F V).infiniteReciprocalShift (V.C + 1) n : ℂ) *
          inner ℂ (weightedDiskAmbientEmbedding F (Submodule.inclusion h u))
            (weightedDiskAmbientEmbedding F w)) ∧
      (∀ w : D, weakJacobi V u w =
        ((diskSpectralData F V).infiniteReciprocalShift (V.C + 1) n : ℂ) *
          inner ℂ (weightedDiskAmbientEmbedding D u) (weightedDiskAmbientEmbedding D w)) := by
  apply disk_common_eigenfunction_of_infinite_trial D F V h n
  exact (diskJacobi_finite_minmax D V ⟨n, hD⟩ _).mp heq.le


/-- Same-index equality in bracketing has a common nonzero
weak eigenfunction, including the larger test space's natural conditions. -/
lemma disk_infinite_to_finite_common_eigenfunction
     (D F : Submodule ℂ ComplexH1)
    [CompleteSpace (D)] [CompleteSpace (F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [Infinite (diskSpectralData D V).eigenbasisIndex]
    [FiniteDimensional ℂ (WeightedDiskAmbient F)] (n : ℕ)
    (hF : n < Module.finrank ℂ (WeightedDiskAmbient F))
    (heq : (diskSpectralData D V).infiniteReciprocalShift (V.C + 1) n =
      (diskSpectralData F V).finiteReciprocalShift (V.C + 1) ⟨n, hF⟩) :
    ∃ u : D, u ≠ 0 ∧
      (∀ w : F, weakJacobi V (Submodule.inclusion h u) w =
        ((diskSpectralData F V).finiteReciprocalShift (V.C + 1) ⟨n, hF⟩ : ℂ) *
          inner ℂ (weightedDiskAmbientEmbedding F (Submodule.inclusion h u))
            (weightedDiskAmbientEmbedding F w)) ∧
      (∀ w : D, weakJacobi V u w =
        ((diskSpectralData F V).finiteReciprocalShift (V.C + 1) ⟨n, hF⟩ : ℂ) *
          inner ℂ (weightedDiskAmbientEmbedding D u) (weightedDiskAmbientEmbedding D w)) := by
  apply disk_common_eigenfunction_of_finite_trial D F V h ⟨n, hF⟩
  exact (diskJacobi_infinite_minmax D V n _).mp heq.le


/-- Same-index equality in bracketing has a common nonzero
weak eigenfunction, including the larger test space's natural conditions. -/
lemma disk_finite_common_eigenfunction
     (D F : Submodule ℂ ComplexH1)
    [CompleteSpace (D)] [CompleteSpace (F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [FiniteDimensional ℂ (WeightedDiskAmbient D)]
    [FiniteDimensional ℂ (WeightedDiskAmbient F)] (n : ℕ)
    (hF : n < Module.finrank ℂ (WeightedDiskAmbient F))
    (hD : n < Module.finrank ℂ (WeightedDiskAmbient D))
    (heq : (diskSpectralData D V).finiteReciprocalShift (V.C + 1) ⟨n, hD⟩ =
      (diskSpectralData F V).finiteReciprocalShift (V.C + 1) ⟨n, hF⟩) :
    ∃ u : D, u ≠ 0 ∧
      (∀ w : F, weakJacobi V (Submodule.inclusion h u) w =
        ((diskSpectralData F V).finiteReciprocalShift (V.C + 1) ⟨n, hF⟩ : ℂ) *
          inner ℂ (weightedDiskAmbientEmbedding F (Submodule.inclusion h u))
            (weightedDiskAmbientEmbedding F w)) ∧
      (∀ w : D, weakJacobi V u w =
        ((diskSpectralData F V).finiteReciprocalShift (V.C + 1) ⟨n, hF⟩ : ℂ) *
          inner ℂ (weightedDiskAmbientEmbedding D u) (weightedDiskAmbientEmbedding D w)) := by
  apply disk_common_eigenfunction_of_finite_trial D F V h ⟨n, hF⟩
  exact (diskJacobi_finite_minmax D V ⟨n, hD⟩ _).mp heq.le


end KsIndex.Spectral
