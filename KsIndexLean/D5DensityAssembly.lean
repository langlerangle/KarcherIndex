module

public import KsIndexLean.D5MembershipRouting
public import KsIndexLean.D5CarrierBridge
public import KsIndexLean.D5CharProjAlgebra
public import KsIndexLean.D5CoreEquivariance
public import KsIndexLean.D5TwistedCoreTrace
public import KsIndexLean.NaturalCoreCharacter
public import KsIndexLean.GeneralConstrainedApproximation
public import KsIndexLean.DiskRotationForms

@[expose] public section


/-!
# Density of natural and reflected cores in mixed character domains

For every positive `k`, rotation character, and pair of boundary flags,
`naturalCharacterToMixed` and `twistedCharacterToMixed` have dense range in
the mixed weak domain.

The construction first approximates within the character domain by a function
vanishing near the punctures, then assembles smooth boundary and interior
pieces. Character projection preserves core membership. Its weak carrier agrees
with the continuous carrier-side projection, which fixes the target and
preserves convergence.
-/

open Set MeasureTheory Filter Topology Metric
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket KsIndex.SingleDisk KsIndex.SingleDiskBridge
open KsIndex.SurfaceSym KsIndex.FormIndex

/-! ### Rotation-power and transport helpers -/

/-- Applying a power of the single-disk rotation is rotation by the power. -/
lemma rot1_pow_apply (a : ℂ) : ∀ (j : ℕ) (f : ℂ → ℂ) (w : ℂ),
    ((rot1 a) ^ j) f w = f (a ^ j * w)
  | 0, f, w => by simp
  | (j + 1), f, w => by
      rw [pow_succ, Module.End.mul_apply, rot1_pow_apply a j (rot1 a f) w,
        rot1_apply, ← mul_assoc, ← pow_succ']

/-- Disk-a.e. identities transport along plane rotations. -/
lemma ae_disk_comp_planeRotation (θ : ℝ) {f g : ℂ → ℂ}
    (h : f =ᵐ[volume.restrict (disk : Set ℂ)] g) :
    (fun z => f (planeRotation θ z)) =ᵐ[volume.restrict (disk : Set ℂ)]
      (fun z => g (planeRotation θ z)) :=
  (measurePreserving_planeRotation_disk θ).quasiMeasurePreserving.ae h

/-- The rotation unit is unimodular (as a complex number). -/
lemma rotUnit_norm_one (k : ℕ) : ‖(rotUnit k : ℂ)‖ = 1 := by
  simp

/-! ### The common projection step

For `fc` in a `rot1`-stable core `D` (with the a.e. value identification
against the weak carrier `Un`), the function-side character projection's
natural carrier equals the carrier-side projection of `Un`. -/

section ProjectionStep

variable {k : ℕ}

/-- The pointwise formula of the function-side projection. -/
lemma charProj_rot1_apply (_hk : 1 ≤ k) (D : Submodule ℂ (ℂ → ℂ)) (r : ℕ)
    (v : ↥D) (z : ℂ) :
    charProj (rot1 (rotUnit k : ℂ)) k D r v z =
      (k : ℂ)⁻¹ * ∑ j ∈ Finset.range k, xi k ^ (r * j) *
        (v : ℂ → ℂ) ((rotUnit k : ℂ) ^ j * z) := by
  rw [charProj_apply]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [rot1_pow_apply]

/-- The k-th power of the canonical rotation acts as the identity on every function. -/
lemma rot1_pow_k_eq_id (hk : 1 ≤ k) (u : ℂ → ℂ) :
    ((rot1 (rotUnit k : ℂ)) ^ k) u = u := by
  funext w
  rw [rot1_pow_apply, rotUnit_pow hk, one_mul]

end ProjectionStep

/-! ### The two density theorems -/

variable {k : ℕ}

/-- The natural-core class-`r` sector maps densely into the
mixed weak sector, for every flag pair. -/
theorem naturalCharacterToMixed_denseRange (hk : 1 ≤ k) (r : ℕ) (b₁ b₀ : Bool) :
    DenseRange (naturalCharacterToMixed hk r b₁ b₀) := by
  rw [Metric.denseRange_iff]
  intro w ε hε
  -- Approximate within the character domain while opening puncture holes, at ε/2.
  obtain ⟨v, M, ρ, hvmem, _hM, hρ, hvw, _hbd, hhole⟩ :=
    exists_general_mixed_character_puncture_approx hk r b₁ b₀ w.val w.property
      (half_pos hε)
  obtain ⟨hvtrace, hvchar⟩ := Submodule.mem_inf.mp hvmem
  -- Assemble boundary and interior approximants for `v`.
  obtain ⟨ι, t, a, gB, g₀, U, hconv, hB, hC, ha01, hD⟩ :=
    sIII_boundary_assembly hk b₁ b₀ v hvtrace ⟨ρ, hρ, hhole⟩
  -- The restricted family eventually belongs to the core.
  have hmem := assembly_family_mem_cores hk b₁ b₀ ha01 hC hD
  -- Carrier-side projection preserves convergence and fixes `v`.
  have hfix : carrierCharProj k r v = v :=
    carrierCharProj_eq_self (Nat.lt_of_lt_of_le Nat.zero_lt_one hk) hvchar
  have hproj := carrierCharProj_tendsto k r hconv
  rw [hfix] at hproj
  have hev : ∀ᶠ n in atTop, dist (carrierCharProj k r (U n)) v < ε / 2 :=
    Metric.tendsto_nhds.mp hproj (ε / 2) (half_pos hε)
  obtain ⟨n, ⟨hmemn, hBn⟩, hevn⟩ := ((hmem.and hB).and hev).exists
  set F : ℂ → ℂ := fun z => g₀ n z + ∑ i ∈ t, gB i n z with hFdef
  set fc : ℂ → ℂ := closedDiskRestriction F with hfcdef
  have hfcmem : fc ∈ NatCc k b₁ b₀ := hmemn.1
  -- the function-side projection
  have ha1 := rotUnit_norm_one k
  have hak : (rotUnit k : ℂ) ^ k = 1 := rotUnit_pow hk
  have hgD : ∀ u ∈ NatCc k b₁ b₀,
      rot1 (rotUnit k : ℂ) u ∈ NatCc k b₁ b₀ :=
    fun u hu => rot1_mem_natCc_same ha1 hak hu
  have hgN : ∀ u ∈ NatCc k b₁ b₀,
      ((rot1 (rotUnit k : ℂ)) ^ k) u = u :=
    fun u _ => rot1_pow_k_eq_id hk u
  set P : ℂ → ℂ :=
    charProj (rot1 (rotUnit k : ℂ)) k (NatCc k b₁ b₀) r ⟨fc, hfcmem⟩
    with hPdef
  have hPmem : P ∈ NatCc k b₁ b₀ :=
    charProj_mem _ k r hgD ⟨fc, hfcmem⟩
  have hPeig : P ∈ Erot1 k r :=
    charProj_mem_eigenspace _ r (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
      hgN hgD ⟨fc, hfcmem⟩
  refine ⟨⟨P, Submodule.mem_inf.mpr ⟨hPmem, hPeig⟩⟩, ?_⟩
  -- the key identification: the projected carrier equals carrierCharProj (U n)
  have hkey : (naturalCharacterToMixed hk r b₁ b₀
      ⟨P, Submodule.mem_inf.mpr ⟨hPmem, hPeig⟩⟩).val
      = carrierCharProj k r (U n) := by
    apply valueCLM_injective
    apply Lp.ext
    -- the per-rotation transported value identifications
    have htrans : ∀ᵐ z ∂volume.restrict (disk : Set ℂ), ∀ j ∈ Finset.range k,
        (valueCLM (U n) : ℂ → ℂ) (planeRotation ((j : ℝ) * rotAngle k) z)
          = F (planeRotation ((j : ℝ) * rotAngle k) z) := by
      rw [Filter.eventually_all_finset]
      intro j _
      exact ae_disk_comp_planeRotation _ hBn.1
    filter_upwards [naturalCoreH1_value_ae hk ⟨P, hPmem⟩,
      carrierCharProj_value_ae k r (U n), htrans,
      ae_restrict_mem KsIndex.SurfaceForm.measurableSet_disk]
      with z h1 h2 h3 hzd
    show (valueCLM (naturalCoreH1 hk ⟨P, hPmem⟩) : ℂ → ℂ) z
        = (valueCLM (carrierCharProj k r (U n)) : ℂ → ℂ) z
    rw [h1, h2]
    show P z = _
    rw [hPdef, charProj_rot1_apply hk]
    simp only [smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    congr 1
    -- `fc = F` at the rotated point (it stays in the open disk), and the
    -- carrier value agrees with `F` there by the transported identification
    have hzn : ‖(rotUnit k : ℂ) ^ j * z‖ < 1 := by
      rw [norm_mul, norm_pow, rotUnit_norm_one, one_pow, one_mul]
      exact KsIndex.SurfaceForm.mem_disk_iff.mp hzd
    have hfcF : fc ((rotUnit k : ℂ) ^ j * z)
        = F ((rotUnit k : ℂ) ^ j * z) := by
      rw [hfcdef]
      exact ite_eq_left hzn.le
    rw [hfcF]
    have h3j := h3 j hj
    rw [planeRotation_rotAngle_pow] at h3j
    exact h3j.symm
  rw [Subtype.dist_eq, hkey]
  calc dist w.val (carrierCharProj k r (U n))
      ≤ dist w.val v + dist v (carrierCharProj k r (U n)) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
        refine add_lt_add ?_ (dist_comm (carrierCharProj k r (U n)) v ▸ hevn)
        rw [dist_eq_norm, norm_sub_rev]
        exact hvw
    _ = ε := add_halves ε

/-- The twisted-core class-`r` sector maps densely into the
mixed weak sector, for every flag pair. -/
theorem twistedCharacterToMixed_denseRange (hk : 1 ≤ k) (r : ℕ) (b₁ b₀ : Bool) :
    DenseRange (twistedCharacterToMixed hk r b₁ b₀) := by
  rw [Metric.denseRange_iff]
  intro w ε hε
  obtain ⟨v, M, ρ, hvmem, _hM, hρ, hvw, _hbd, hhole⟩ :=
    exists_general_mixed_character_puncture_approx hk r b₁ b₀ w.val w.property
      (half_pos hε)
  obtain ⟨hvtrace, hvchar⟩ := Submodule.mem_inf.mp hvmem
  obtain ⟨ι, t, a, gB, g₀, U, hconv, hB, hC, ha01, hD⟩ :=
    sIII_boundary_assembly hk b₁ b₀ v hvtrace ⟨ρ, hρ, hhole⟩
  have hmem := assembly_family_mem_cores hk b₁ b₀ ha01 hC hD
  have hfix : carrierCharProj k r v = v :=
    carrierCharProj_eq_self (Nat.lt_of_lt_of_le Nat.zero_lt_one hk) hvchar
  have hproj := carrierCharProj_tendsto k r hconv
  rw [hfix] at hproj
  have hev : ∀ᶠ n in atTop, dist (carrierCharProj k r (U n)) v < ε / 2 :=
    Metric.tendsto_nhds.mp hproj (ε / 2) (half_pos hε)
  obtain ⟨n, ⟨hmemn, hBn⟩, hevn⟩ := ((hmem.and hB).and hev).exists
  set F : ℂ → ℂ := fun z => g₀ n z + ∑ i ∈ t, gB i n z with hFdef
  set fc : ℂ → ℂ := closedDiskRestriction F with hfcdef
  have hfcmem : fc ∈ KsIndex.TwistSwap.ReflCc k (sgn b₁) (sgn b₀) := hmemn.2
  have ha1 := rotUnit_norm_one k
  have hak : (rotUnit k : ℂ) ^ k = 1 := rotUnit_pow hk
  have hgD : ∀ u ∈ KsIndex.TwistSwap.ReflCc k (sgn b₁) (sgn b₀),
      rot1 (rotUnit k : ℂ) u
        ∈ KsIndex.TwistSwap.ReflCc k (sgn b₁) (sgn b₀) :=
    fun u hu => rot1_mem_reflCc_same ha1 hak _ _ hu
  have hgN : ∀ u ∈ KsIndex.TwistSwap.ReflCc k (sgn b₁) (sgn b₀),
      ((rot1 (rotUnit k : ℂ)) ^ k) u = u :=
    fun u _ => rot1_pow_k_eq_id hk u
  set P : ℂ → ℂ := charProj (rot1 (rotUnit k : ℂ)) k
    (KsIndex.TwistSwap.ReflCc k (sgn b₁) (sgn b₀)) r ⟨fc, hfcmem⟩ with hPdef
  have hPmem : P ∈ KsIndex.TwistSwap.ReflCc k (sgn b₁) (sgn b₀) :=
    charProj_mem _ k r hgD ⟨fc, hfcmem⟩
  have hPeig : P ∈ Erot1 k r :=
    charProj_mem_eigenspace _ r (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
      hgN hgD ⟨fc, hfcmem⟩
  refine ⟨⟨P, Submodule.mem_inf.mpr ⟨hPmem, hPeig⟩⟩, ?_⟩
  have hkey : (twistedCharacterToMixed hk r b₁ b₀
      ⟨P, Submodule.mem_inf.mpr ⟨hPmem, hPeig⟩⟩).val
      = carrierCharProj k r (U n) := by
    apply valueCLM_injective
    apply Lp.ext
    have htrans : ∀ᵐ z ∂volume.restrict (disk : Set ℂ), ∀ j ∈ Finset.range k,
        (valueCLM (U n) : ℂ → ℂ) (planeRotation ((j : ℝ) * rotAngle k) z)
          = F (planeRotation ((j : ℝ) * rotAngle k) z) := by
      rw [Filter.eventually_all_finset]
      intro j _
      exact ae_disk_comp_planeRotation _ hBn.1
    filter_upwards [twistedCoreH1_value_ae hk ⟨P, hPmem⟩,
      carrierCharProj_value_ae k r (U n), htrans,
      ae_restrict_mem KsIndex.SurfaceForm.measurableSet_disk]
      with z h1 h2 h3 hzd
    show (valueCLM (twistedCoreH1 hk ⟨P, hPmem⟩) : ℂ → ℂ) z
        = (valueCLM (carrierCharProj k r (U n)) : ℂ → ℂ) z
    rw [h1, h2]
    show P z = _
    rw [hPdef, charProj_rot1_apply hk]
    simp only [smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    congr 1
    have hzn : ‖(rotUnit k : ℂ) ^ j * z‖ < 1 := by
      rw [norm_mul, norm_pow, rotUnit_norm_one, one_pow, one_mul]
      exact KsIndex.SurfaceForm.mem_disk_iff.mp hzd
    have hfcF : fc ((rotUnit k : ℂ) ^ j * z)
        = F ((rotUnit k : ℂ) ^ j * z) := by
      rw [hfcdef]
      exact ite_eq_left hzn.le
    rw [hfcF]
    have h3j := h3 j hj
    rw [planeRotation_rotAngle_pow] at h3j
    exact h3j.symm
  rw [Subtype.dist_eq, hkey]
  calc dist w.val (carrierCharProj k r (U n))
      ≤ dist w.val v + dist v (carrierCharProj k r (U n)) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
        refine add_lt_add ?_ (dist_comm (carrierCharProj k r (U n)) v ▸ hevn)
        rw [dist_eq_norm, norm_sub_rev]
        exact hvw
    _ = ε := add_halves ε

end KsIndex.Trace
