module

public import KsIndexLean.SectorL2Realization

@[expose] public section


noncomputable section
namespace KsIndex.SectorIndex
open KsIndex.CircleQ KsIndex.Sector KsIndex.SectorForm KsIndex.SIsometry KsIndex.InvariantHermitian

lemma sectorL2_of_hilbert (u : SectorHilbert) : SectorL2 u := by
  have h : Summable (fun i : Idx => ‖u i‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp u).summable (show (0 : ℝ) < (2 : ENNReal).toReal by norm_num)
  exact ⟨h.comp_injective Sum.inl_injective, h.comp_injective Sum.inr_injective⟩

lemma hilbert_norm_sq (u : SectorHilbert) : ‖u‖ ^ 2 = normSqS u := by
  have h := lp.hasSum_norm (show (0 : ℝ) < (2 : ENNReal).toReal by norm_num) u
  have hu := sectorL2_of_hilbert u
  have he : ‖u‖ ^ 2 = ∑' i : Idx, ‖u i‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h.tsum_eq.symm
  exact he.trans (Summable.tsum_sum (f := fun i : Idx => ‖u i‖ ^ 2) hu.1 hu.2)

lemma normSqS_sgn {u : Idx → ℂ} (hu : SectorL2 u) : normSqS (sgn u) = normSqS u := by
  have ht := summable_convK_sq Tker_mul Tker_orth Tker_row Tker_row1 hu.2
  have hT := tsum_convS_sq ht
  have hid : convS (convK Tker (fun m => u (.inr m))) = fun m => u (.inr m) := by
    funext m
    rw [← convK_Sker, convK_ST_eq hu.2]
  rw [hid] at hT
  simp only [normSqS, sgn_inl, sgn_inr]
  rw [← hT, tsum_convS_sq hu.1, add_comm]

def hilbertSgn : SectorHilbert →ₗ[ℂ] SectorHilbert where
  toFun u := ⟨sgn u, sector_mem_lp (sectorL2_sgn (sectorL2_of_hilbert u))⟩
  map_add' u v := by
    apply Subtype.ext
    exact sgn_add (sectorL2_of_hilbert u) (sectorL2_of_hilbert v)
  map_smul' c u := by apply Subtype.ext; exact sgn_smul c u

lemma hilbertSgn_involutive : Function.Involutive hilbertSgn := by
  intro u
  apply Subtype.ext
  exact sgn_involutive (sectorL2_of_hilbert u)

lemma hilbertSgn_norm (u : SectorHilbert) : ‖hilbertSgn u‖ = ‖u‖ := by
  have h : ‖hilbertSgn u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [hilbert_norm_sq, hilbert_norm_sq]
    exact normSqS_sgn (sectorL2_of_hilbert u)
  nlinarith [norm_nonneg (hilbertSgn u), norm_nonneg u]

lemma hilbertSgn_inner (u v : SectorHilbert) :
    inner ℂ (hilbertSgn u) (hilbertSgn v) = inner ℂ u v :=
  (LinearMap.norm_map_iff_inner_map_map hilbertSgn).mp hilbertSgn_norm u v

lemma hilbertSgn_symmetric : hilbertSgn.IsSymmetric := by
  intro u v
  have h := hilbertSgn_inner u (hilbertSgn v)
  rwa [hilbertSgn_involutive] at h

/-- The paper's adjoint phase multiplier, now on actual coefficient L². -/
def hilbertMulAdag (α : ℝ) : SectorHilbert →ₗ[ℂ] SectorHilbert :=
  (Real.cos (α * Real.pi) : ℂ) • LinearMap.id +
    (Complex.I * (Real.sin (α * Real.pi) : ℂ)) • hilbertSgn

lemma hilbertMulAdag_inner (α : ℝ) (u v : SectorHilbert) :
    inner ℂ (hilbertMulAdag α u) (hilbertMulAdag α v) = inner ℂ u v := by
  have htrig : (Real.cos (α * Real.pi) : ℂ)^2 +
      (Real.sin (α * Real.pi) : ℂ)^2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq (α * Real.pi)
  simp only [hilbertMulAdag, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    map_mul, Complex.conj_I, Complex.conj_ofReal, hilbertSgn_inner,
    hilbertSgn_symmetric u v]
  linear_combination (inner ℂ u v) * htrig -
    (inner ℂ u v) * (Real.sin (α * Real.pi) : ℂ)^2 * Complex.I_sq

def hilbertParity : SectorHilbert →ₗ[ℂ] SectorHilbert where
  toFun u := ⟨parity u, sector_mem_lp (sectorL2_parity (sectorL2_of_hilbert u))⟩
  map_add' u v := by apply Subtype.ext; exact parity_add u v
  map_smul' c u := by apply Subtype.ext; exact parity_smul c u

lemma hilbertParity_inner (u v : SectorHilbert) :
    inner ℂ (hilbertParity u) (hilbertParity v) = inner ℂ u v := by
  apply (LinearMap.norm_map_iff_inner_map_map hilbertParity).mp _ u v
  intro w
  have h : ‖hilbertParity w‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [hilbert_norm_sq, hilbert_norm_sq]
    exact normSqS_parity w
  nlinarith [norm_nonneg (hilbertParity w), norm_nonneg w]

def hilbertRop (α : ℝ) : SectorHilbert →ₗ[ℂ] SectorHilbert :=
  -(hilbertMulAdag α).comp hilbertParity

@[simp] lemma hilbertRop_apply (α : ℝ) (u : SectorHilbert) (i : Idx) :
    hilbertRop α u i = rop α u i := rfl

lemma hilbertRop_inner (α : ℝ) (u v : SectorHilbert) :
    inner ℂ (hilbertRop α u) (hilbertRop α v) = inner ℂ u v := by
  change inner ℂ (-(hilbertMulAdag α (hilbertParity u)))
    (-(hilbertMulAdag α (hilbertParity v))) = _
  rw [inner_neg_left, inner_neg_right, neg_neg, hilbertMulAdag_inner, hilbertParity_inner]

/-- Transport the restricted involution to the actual L² hull. -/
def sectorL2HullInvolution (α : ℝ) (X : Submodule ℂ Domς) :
    Module.End ℂ (sectorL2Hull α X) :=
  (sectorHullL2Equiv α X).toLinearMap.comp
    ((sectorHullInvolution α X).comp (sectorHullL2Equiv α X).symm.toLinearMap)

lemma sectorL2HullInvolution_involutive (α : ℝ) (X : Submodule ℂ Domς) :
    Function.Involutive (sectorL2HullInvolution α X) := by
  intro u
  simp only [sectorL2HullInvolution, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rw [sectorHullInvolution_involutive α X, LinearEquiv.apply_symm_apply]

lemma sectorHullL2Equiv_coeff (α : ℝ) (X : Submodule ℂ Domς)
    (u : sectorInvariantHull α X) (i : Idx) :
    (sectorHullL2Equiv α X u).val i = u.val.val i := rfl

lemma sectorL2HullInvolution_coe (α : ℝ) (X : Submodule ℂ Domς)
    (u : sectorL2Hull α X) :
    (sectorL2HullInvolution α X u).val = hilbertRop α u.val := by
  have h : u.val = sectorL2Embedding ((sectorHullL2Equiv α X).symm u).val := by
    exact congrArg Subtype.val ((sectorHullL2Equiv α X).apply_symm_apply u).symm
  rw [h]
  rfl

lemma sectorL2HullInvolution_unitary (α : ℝ) (X : Submodule ℂ Domς)
    (u v : sectorL2Hull α X) :
    inner ℂ (sectorL2HullInvolution α X u) (sectorL2HullInvolution α X v) =
      inner ℂ u v := by
  change inner ℂ (sectorL2HullInvolution α X u).val
    (sectorL2HullInvolution α X v).val = inner ℂ u.val v.val
  rw [sectorL2HullInvolution_coe, sectorL2HullInvolution_coe, hilbertRop_inner]

lemma sectorL2HullForm_invariant (α : ℝ) (X : Submodule ℂ Domς)
    (u v : sectorL2Hull α X) :
    sectorL2HullForm α X (sectorL2HullInvolution α X u) (sectorL2HullInvolution α X v) =
      sectorL2HullForm α X u v := by
  change NBform α
    ((sectorHullL2Equiv α X).symm (sectorHullL2Equiv α X
      (sectorHullInvolution α X ((sectorHullL2Equiv α X).symm u)))).val.val
    ((sectorHullL2Equiv α X).symm (sectorHullL2Equiv α X
      (sectorHullInvolution α X ((sectorHullL2Equiv α X).symm v)))).val.val = _
  simp only [LinearEquiv.symm_apply_apply]
  exact sectorHull_form_invariant α X _ _

/-- The exact commutation input required by the paper's spectral proof. -/
lemma sectorL2HullOperator_commutes (α : ℝ) (X : Submodule ℂ Domς)
    [FiniteDimensional ℂ X] :
    Function.Commute (sectorL2HullOperator α X) (sectorL2HullInvolution α X) := by
  apply representingOperator_commutes _ _ (sectorL2HullInvolution_involutive α X)
    (sectorL2HullInvolution_unitary α X)
  intro u v
  rw [sectorL2HullOperator_represents, sectorL2HullOperator_represents]
  exact sectorL2HullForm_invariant α X u v

lemma sectorL2Hull_negativeSpectralSpace_stable (α : ℝ) (X : Submodule ℂ Domς)
    [FiniteDimensional ℂ X] :
    ∀ u ∈ negativeSpectralSpace (sectorL2HullOperator α X),
      sectorL2HullInvolution α X u ∈ negativeSpectralSpace (sectorL2HullOperator α X) :=
  negativeSpectralSpace_stable _ _ (sectorL2HullOperator_commutes α X)

end KsIndex.SectorIndex
