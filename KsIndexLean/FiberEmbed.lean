module

/-
# Isotypic fibers and nullity bounds

For positive `k` and `m`, the commuting rotation and two-copy shift decompose
`BoundedJacobi k m` into rotation/shift eigenspaces. Their ranks sum to
`nulSurface k m`. The shift acts by copy-index reindexing without changing the
complex coordinate, and preserves seam conditions by `seamArc_add_two`.

For `k = 3` and nonzero `m`, Caccioppoli estimates realize each fiber in the
chain Sobolev space. An injective linear map carries it into the spherical
character radical at phase `a/m`, bounding its dimension by the corresponding
weak sector nullity. Translation fields supply nonzero vectors in the three
zero-phase fibers. Interior phases away from `α*` and `1 − α*` contribute zero.

The final nonresonant equality and resonant upper bound retain an explicit
zero-phase dimension bound as a hypothesis. The injection alone does not
supply equality of dimensions or threshold witnesses.
-/
public import KsIndexLean.NullitySectors
public import KsIndexLean.Caccioppoli
public import KsIndexLean.WeakH1Integration
public import KsIndexLean.EnergySmoothWeakCopy
public import KsIndexLean.ChainChartNormed
public import KsIndexLean.ChainChartShift
public import KsIndexLean.ChainChartRotation
public import KsIndexLean.ChainPhaseCharacter
public import KsIndexLean.DiskH1RotationIsometry
public import KsIndexLean.PaperSectorParameters
public import KsIndexLean.PaperSmoothChainSector
public import KsIndexLean.ChainPairingCore
public import KsIndexLean.WitnessFibers
public import KsIndexLean.NullityInjection
public import KsIndexLean.PaperSlitCharacterInvariants
public import KsIndexLean.PositiveBlockCounts
public import KsIndexLean.PaperSlitIndexAssembly
public import KsIndexLean.SectorPhase
public import KsIndexLean.Staircase
public import KsIndexLean.BandArithmetic
public import KsIndexLean.StaircaseArithmetic

@[expose] public section


namespace KsIndex.NullityDecomp
open KsIndex.Surface KsIndex.SurfaceSym KsIndex.FormIndex KsIndex.WeakH1
  KsIndex.FaithfulInjection KsIndex.Trace Complex MeasureTheory

variable {k m : ℕ}

/-- **The shift stabilizes `BoundedJacobi`** (curried).  Each clause is the `n+2`
reindex of the original, with the seam arcs matched by `seamArc_add_two`. -/
lemma shiftF_mem_boundedJacobi {u : ZMod (2 * m) → ℂ → ℂ}
    (hu : u ∈ BoundedJacobi k m) : shiftF u ∈ BoundedJacobi k m := by
  obtain ⟨⟨hsm1, hsm2, hsm3⟩, hbd, hjac, hpz, hsv⟩ := hu
  refine ⟨⟨fun n => hsm1 (n + 2), fun n w hw => ?_, fun n w hw => hsm3 (n + 2) w hw⟩,
    ?_, fun n w hw => hjac (n + 2) w hw, fun n p hp => hpz (n + 2) p hp,
    fun n w hw => ?_⟩
  · -- glue smoothness across the seam
    have hglue : glue (shiftF u) n = glue u (n + 2) := by
      funext z
      simp only [glue, shiftF, add_right_comm n 1 2]
    rw [hglue]
    exact hsm2 (n + 2) w (by rwa [seamArc_add_two])
  · -- boundedness
    obtain ⟨C, hC⟩ := hbd
    exact ⟨C, fun n w => hC (n + 2) w⟩
  · -- seam single-valuedness: `(shiftF u)(n+1) w = (shiftF u) n w`
    change u (n + 1 + 2) w = u (n + 2) w
    rw [show n + 1 + 2 = (n + 2) + 1 from by ring]
    exact hsv (n + 2) w (by rwa [seamArc_add_two])

/-- **The shift stabilizes `BoundedJacobiE`** (uncurried), via `uncurry_symm_shiftE`. -/
lemma shiftE_mem_boundedJacobiE {U : ZMod (2 * m) × ℂ → ℂ}
    (hU : U ∈ BoundedJacobiE k m) : shiftE m U ∈ BoundedJacobiE k m := by
  rw [mem_boundedJacobiE] at hU ⊢
  rw [uncurry_symm_shiftE]
  exact shiftF_mem_boundedJacobi hU

/-! ### The arbitrary-m isotypic decomposition -/

/-- The `(r, a)`-isotypic fiber of `BoundedJacobi k m`: rotation character `r`
(the ℤ_k factor) and shift character `a` (the ℤ/m factor). -/
noncomputable def isotypicFiber (k m r a : ℕ) : Submodule ℂ (ZMod (2 * m) × ℂ → ℂ) :=
  (BoundedJacobiE k m ⊓
      Module.End.eigenspace (rotE m ((rotUnit k : Circle) : ℂ)) (zeta k ^ r)) ⊓
    Module.End.eigenspace (shiftE m) (zeta m ^ a)

/-- **`nulSurface k m` splits over the `ℤ_k × ℤ/m` isotypic fibers** (rotation ×
shift) — two applications of the character decomposition theorem with the zero form (nothing
transported; density-free).  The arbitrary-m analogue of `nulSurface_eq_sum_sectors`,
with the shift generator in place of the m=2 reflections. -/
theorem nulSurface_eq_sum_isotypic (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    nulSurface k m = ∑ r : Fin k, ∑ a : Fin m,
      Cardinal.toENat (Module.rank ℂ (isotypicFiber k m (r : ℕ) (a : ℕ))) := by
  rw [nulSurface_eq_formNullity_zero]
  -- first split: the rotation (order k)
  rw [formNullity_eq_sum_eigen (g := rotE m ((rotUnit k : Circle) : ℂ)) (sesq_zero _) hk
    (fun u _ => rot_pow_id hk u)
    (fun u hu => rotE_mem_boundedJacobiE hk hu) (fun _ _ _ _ => rfl)]
  refine Finset.sum_congr rfl fun r _ => ?_
  -- second split: the shift (order m), preserving the rotation eigenspace
  rw [formNullity_eq_sum_eigen (g := shiftE m) (sesq_zero _) hm
    (fun u _ => shift_pow_id u)
    (fun u hu => by
      obtain ⟨hD, hE⟩ := Submodule.mem_inf.mp hu
      rw [Module.End.mem_eigenspace_iff] at hE
      refine Submodule.mem_inf.mpr ⟨shiftE_mem_boundedJacobiE hD, ?_⟩
      rw [Module.End.mem_eigenspace_iff, ← Module.End.mul_apply, rotE_mul_shiftE,
        Module.End.mul_apply, hE, map_smul])
    (fun _ _ _ _ => rfl)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [formNullity_zero_eq_rank]
  rfl

/-! ### The Caccioppoli bridge for a fiber element

A fiber element is a `BoundedJacobi` field; the Caccioppoli inclusion
(`bddJacobi_le_energySmooth`) realizes it as an `EnergySmooth` field — the input to
`energySmoothToChainChart` for the forward map into the chain carrier
(`ChainChartSpace`), where the phase/character/radical membership all live. -/

/-- A fiber element as an `EnergySmooth` field, via the Caccioppoli
inclusion `BoundedJacobi ⊆ EnergySmooth` (k = 3). -/
noncomputable def fiberES {m r a : ℕ} [NeZero m] (U : isotypicFiber 3 m r a) :
    EnergySmooth 3 m :=
  ⟨(uncurryE m).symm U.val,
    bddJacobi_le_energySmooth (by norm_num)
      (mem_boundedJacobiE.mp
        ((Submodule.mem_inf.mp (Submodule.mem_inf.mp U.property).1).1))⟩

/-! ### the per-copy intertwining of the two symmetries

Under `energySmoothToChainChart` the copies of `fiberES U` are `energySmoothCopy (fiberES U)`
(`energySmoothToChainChart_coordinates`).  The shift eigenvalue `ζ_m^a` becomes the
copy-shift, and the rotation eigenvalue `ζ₃^r` becomes the per-copy `diskRotation` character —
the two inputs that `mem_chainChartPhaseDomain_iff_coordinates` /
`mem_chainChartCharacterDomain_iff_coordinates` consume. -/

/-- **Copy-shift from the shift eigenvector.**  `U ∈ eigenspace shiftE (ζ_m^a)` pushes to the
`ComplexH1` copies: `copy (n+2) = ζ_m^a · copy n`.  This is the coordinate input to the
phase-domain membership (`mem_chainChartPhaseDomain_iff_coordinates` consumes it, does not
supply it). -/
lemma fiberCopy_shift {m r a : ℕ} [NeZero m] (U : isotypicFiber 3 m r a) (n : ZMod (2 * m)) :
    energySmoothCopy (fiberES U) (n + 2) = (zeta m ^ a) • energySmoothCopy (fiberES U) n := by
  have hev : shiftE m U.val = (zeta m ^ a) • U.val :=
    Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp U.property).2
  have hshiftF : shiftF (fiberES U).val = (zeta m ^ a) • (fiberES U).val := by
    have h := congrArg (uncurryE m).symm hev
    rwa [map_smul, uncurry_symm_shiftE] at h
  have hvpt : ∀ w, (fiberES U).val (n + 2) w = (zeta m ^ a) * (fiberES U).val n w := by
    intro w
    have h := congrFun (congrFun hshiftF n) w
    simpa only [shiftF, Pi.smul_apply, smul_eq_mul] using h
  apply valueCLM_injective
  rw [map_smul]
  apply MeasureTheory.Lp.ext
  filter_upwards [energySmoothCopy_value_ae (fiberES U) (n + 2),
    energySmoothCopy_value_ae (fiberES U) n,
    Lp.coeFn_smul (zeta m ^ a) (valueCLM (energySmoothCopy (fiberES U) n))] with z h1 h2 hc
  simp only [h1, h2, hc, hvpt, Pi.smul_apply, smul_eq_mul]

/-- **Rotation-character transfer from the rotation eigenvector**.  `U ∈ eigenspace rotE (ζ₃^r)` pushes to the per-copy `diskRotation` character:
`diskRotation (-2π/3) (copy n) = ζ₃^r · copy n` — the coordinate input to the
character-domain membership.  Same a.e. template as `fiberCopy_shift`
(`ccSmoothCopy_rotation`), with the plane rotation on the disk handled by
`measurePreserving_planeRotation_disk`. -/
lemma fiberCopy_rotation {m r a : ℕ} [NeZero m] (U : isotypicFiber 3 m r a) (n : ZMod (2 * m)) :
    diskRotation (-(2 * Real.pi) / 3) (energySmoothCopy (fiberES U) n)
      = (zeta 3 ^ r) • energySmoothCopy (fiberES U) n := by
  have hev : rotE m ((rotUnit 3 : Circle) : ℂ) U.val = (zeta 3 ^ r) • U.val :=
    Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp U.property).1).2
  have hrotF : rotF ((rotUnit 3 : Circle) : ℂ) (fiberES U).val
      = (zeta 3 ^ r) • (fiberES U).val := by
    have h := congrArg (uncurryE m).symm hev
    rwa [map_smul, uncurry_symm_rotE] at h
  have hvpt : ∀ z, (fiberES U).val n (((rotUnit 3 : Circle) : ℂ) * z)
      = (zeta 3 ^ r) * (fiberES U).val n z := by
    intro z
    have h := congrFun (congrFun hrotF n) z
    simpa only [rotF, Pi.smul_apply, smul_eq_mul] using h
  have hpr : ∀ z : ℂ, planeRotation (-(2 * Real.pi) / 3) z = ((rotUnit 3 : Circle) : ℂ) * z := by
    intro z
    rw [planeRotation_apply, rotUnit, Circle.coe_exp]
    push_cast
    ring_nf
  apply valueCLM_injective
  rw [map_smul]
  apply MeasureTheory.Lp.ext
  have hcomp := (measurePreserving_planeRotation_disk
    (-(2 * Real.pi) / 3)).quasiMeasurePreserving.ae_eq_comp
    (energySmoothCopy_value_ae (fiberES U) n)
  filter_upwards [diskRotation_value_ae (-(2 * Real.pi) / 3) (energySmoothCopy (fiberES U) n),
    hcomp, energySmoothCopy_value_ae (fiberES U) n,
    Lp.coeFn_smul (zeta 3 ^ r) (valueCLM (energySmoothCopy (fiberES U) n))] with z hr hc h2 hs
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at hr hc hs ⊢
  rw [hr, hc, hpr z, hvpt z, hs, h2]

/-! ### the fiber element lands in the sampled phase-character sector

The two per-copy transfers feed the coordinate-membership criteria, placing the
chain realization of a fiber element in `chainChartPhaseDomain (paperPhase (a/m))` (via
`fiberCopy_shift` + `paperRationalPhase_eq_zeta`) and `chainChartCharacterDomain (ζ₃^r)` (via
`fiberCopy_rotation`) — the two factors of `PaperChainSector m a r`. -/

/-- The chain-carrier realization of a fiber element (through `fiberES` + Caccioppoli). -/
noncomputable def fiberToChain {m r a : ℕ} [NeZero m] (U : isotypicFiber 3 m r a) :
    ChainChartSpace 3 m := energySmoothToChainChart 3 m (fiberES U)

lemma fiberToChain_coord {m r a : ℕ} [NeZero m] (U : isotypicFiber 3 m r a) :
    chainChartCoordinatesCLM 3 m (fiberToChain U) = energySmoothCopy (fiberES U) :=
  energySmoothToChainChart_coordinates 3 m (fiberES U)

/-- **Phase membership**: `fiberToChain U ∈ chainChartPhaseDomain (paperPhase (a/m))`, from the
copy-shift + the `paperPhase (a/m) = ζ_m^a` bridge. -/
lemma fiberToChain_mem_phase {m r a : ℕ} [NeZero m] (U : isotypicFiber 3 m r a) :
    fiberToChain U ∈ chainChartPhaseDomain 3 m (KsIndex.Spherical.paperPhase ((a : ℝ) / m)) := by
  rw [mem_chainChartPhaseDomain_iff_coordinates]
  intro n
  simp only [fiberToChain_coord, KsIndex.Spectral.paperRationalPhase_eq_zeta]
  exact fiberCopy_shift U n

/-- **Character membership**: `fiberToChain U ∈ chainChartCharacterDomain (ζ₃^r)`, from the
rotation transfer.  Uses the paper's root proof so it matches `PaperChainSector`'s factor. -/
lemma fiberToChain_mem_char {m r a : ℕ} [NeZero m] (U : isotypicFiber 3 m r a) :
    fiberToChain U ∈ chainChartCharacterDomain 3 m (-(2 * Real.pi) / 3)
      (paperRotation_root 3 (by norm_num)) (zeta 3 ^ r) := by
  rw [mem_chainChartCharacterDomain_iff_coordinates]
  intro n
  simp only [fiberToChain_coord]
  exact fiberCopy_rotation U n

/-- The fiber element as an element of the phase-domain subtype (the carrier of
`PaperChainSector`). -/
noncomputable def fiberToPhase {m r a : ℕ} [NeZero m] (U : isotypicFiber 3 m r a) :
    chainChartPhaseDomain 3 m (KsIndex.Spherical.paperPhase ((a : ℝ) / m)) :=
  ⟨fiberToChain U, fiberToChain_mem_phase U⟩

/-- **The fiber element lands in the sampled phase-character sector.**  The two factor
memberships, assembled through the `comap` that defines `PaperChainSector`.  The `comap` is
stripped with the `mem_comap` lemma (not raw defeq, which the kernel cannot reduce in time). -/
theorem fiberToPhase_mem_sector {m r a : ℕ} [NeZero m] (U : isotypicFiber 3 m r a) :
    fiberToPhase U ∈ KsIndex.Spherical.PaperChainSector m a r := by
  simp only [KsIndex.Spherical.PaperChainSector, chainPhaseCharacterDomain, Submodule.mem_comap]
  exact fiberToChain_mem_char U

/-! ### the image lies in the sector's weak radical

A fiber element is a bounded Jacobi field, so (`chainChart_sector_pairing_zero`)
its chain realization pairs to zero under `chainChartJacobi` against every element of the sector
— the `mem_formRadical` characterization of radical membership, for the injection below. -/

/-- The underlying field of `fiberES U` is a bounded Jacobi field (the `isotypicFiber` carrier). -/
lemma fiberES_mem_boundedJacobi {m r a : ℕ} [NeZero m] (U : isotypicFiber 3 m r a) :
    (fiberES U).val ∈ BoundedJacobi 3 m :=
  mem_boundedJacobiE.mp ((Submodule.mem_inf.mp (Submodule.mem_inf.mp U.property).1).1)

/-- **The fiber image pairs to zero against the whole sector** — the ≤-side image-in-radical
fact, via `chainChart_sector_pairing_zero` at `u := fiberES U`. -/
lemma fiberToPhase_pairing_zero {m r a : ℕ} [NeZero m] (U : isotypicFiber 3 m r a)
    (v : KsIndex.Spherical.PaperChainSector m a r) :
    chainChartJacobi 3 m (surfacePotential 3) (fiberToChain U) v.val.val = 0 :=
  chainChart_sector_pairing_zero a r (fiberES U) (fiberES_mem_boundedJacobi U) v

/-! ### The ≥ base rows: the three translation witnesses sit in the a = 0 fibers

Astra/`WitnessFibers` gives, for each of the three translation Jacobi fields, its
`shiftE`/`rotE` eigenspace memberships (phase `a = 0`, rotation characters `r = 0,1,2`) and
nonvanishing.  Intersecting with the `BoundedJacobiE` carrier places a nonzero element in each
`isotypicFiber 3 m r 0` — so each of those three fibers is nontrivial (the base nullity 3). -/
section Witnesses
open KsIndex.JacobiFamily KsIndex.JacobiFields

/-- A bounded Jacobi field with the two eigenspace memberships lands in the `a = 0` fiber. -/
lemma witness_mem_isotypicFiber {m : ℕ} [NeZero m] {r : ℕ} {J : BoundedJacobi 3 m}
    (hrot : uncurryE m J.val ∈
      Module.End.eigenspace (rotE m ((rotUnit 3 : Circle) : ℂ)) (zeta 3 ^ r))
    (hshift : uncurryE m J.val ∈ Module.End.eigenspace (shiftE m) (zeta m ^ (0 : ℕ))) :
    uncurryE m J.val ∈ isotypicFiber 3 m r 0 := by
  refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, hrot⟩, hshift⟩
  rw [mem_boundedJacobiE, LinearEquiv.symm_apply_apply]
  exact J.property

/-- `uncurryE` of a nonzero bounded Jacobi field is nonzero. -/
lemma witness_ne_zero {m : ℕ} [NeZero m] {J : BoundedJacobi 3 m} (hJ : J ≠ 0) :
    uncurryE m J.val ≠ 0 := by
  intro h
  exact hJ (Submodule.coe_eq_zero.mp ((uncurryE m).injective (by rw [h, map_zero])))

lemma uncurry_J3_mem_fiber {m : ℕ} [NeZero m] :
    uncurryE m (J3 3 m (by norm_num)).val ∈ isotypicFiber 3 m 0 0 :=
  witness_mem_isotypicFiber uncurry_J3_mem_rot uncurry_J3_mem_shift

lemma uncurry_Jplus_mem_fiber {m : ℕ} [NeZero m] :
    uncurryE m (Jplus m).val ∈ isotypicFiber 3 m 1 0 :=
  witness_mem_isotypicFiber uncurry_Jplus_mem_rot uncurry_Jplus_mem_shift

lemma uncurry_Jminus_mem_fiber {m : ℕ} [NeZero m] :
    uncurryE m (Jminus m).val ∈ isotypicFiber 3 m 2 0 :=
  witness_mem_isotypicFiber uncurry_Jminus_mem_rot uncurry_Jminus_mem_shift

/-- **The three `a = 0` fibers are nontrivial** — the squeeze's ≥ base rows (nullity ≥ 3). -/
theorem isotypicFiber_a0_ne_bot {m : ℕ} [NeZero m] :
    isotypicFiber 3 m 0 0 ≠ ⊥ ∧ isotypicFiber 3 m 1 0 ≠ ⊥ ∧ isotypicFiber 3 m 2 0 ≠ ⊥ := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact witness_ne_zero J3_ne_zero ((Submodule.mem_bot ℂ).mp (h ▸ uncurry_J3_mem_fiber))
  · exact witness_ne_zero Jplus_ne_zero ((Submodule.mem_bot ℂ).mp (h ▸ uncurry_Jplus_mem_fiber))
  · exact witness_ne_zero Jminus_ne_zero ((Submodule.mem_bot ℂ).mp (h ▸ uncurry_Jminus_mem_fiber))

end Witnesses

/-! ### The ≤ injection: isotypicFiber ↪ ChainChartSpace (linear, injective)

The forward map bundled as a ℂ-linear map (via `LinearMap.codRestrict`, since `EnergySmooth` is a
submodule), and injective: a fiber element is determined by its chain realization.  The injectivity
reuses the Q1b-α faithfulness (`boundedJacobi_zero_of_disk_zero`, general m) — if the realization
vanishes, every copy's disk values vanish a.e., hence pointwise (smoothness, `eqOn_open_of_ae_eq`),
so the bounded Jacobi field is zero. -/

/-- `fiberES` bundled as a ℂ-linear map. -/
noncomputable def fiberES_lin {m r a : ℕ} [NeZero m] :
    isotypicFiber 3 m r a →ₗ[ℂ] EnergySmooth 3 m :=
  LinearMap.codRestrict (EnergySmooth 3 m)
    ((uncurryE m).symm.toLinearMap.comp (isotypicFiber 3 m r a).subtype)
    (fun U => bddJacobi_le_energySmooth (by norm_num) (fiberES_mem_boundedJacobi U))

/-- **The ≤ injection**, bundled: `isotypicFiber 3 m r a →ₗ ChainChartSpace 3 m`. -/
noncomputable def fiberLin {m r a : ℕ} [NeZero m] :
    isotypicFiber 3 m r a →ₗ[ℂ] ChainChartSpace 3 m :=
  (energySmoothToChainChart 3 m).comp fiberES_lin

lemma fiberLin_apply {m r a : ℕ} [NeZero m] (U : isotypicFiber 3 m r a) :
    fiberLin U = fiberToChain U := rfl

/-- **The injection is injective** — a fiber element is determined by its chain realization. -/
lemma fiberLin_injective {m r a : ℕ} [NeZero m] :
    Function.Injective (fiberLin (m := m) (r := r) (a := a)) := by
  refine (injective_iff_map_eq_zero _).mpr fun U hU => ?_
  have hcoord : energySmoothCopy (fiberES U) = 0 := by
    have key : chainChartCoordinatesCLM 3 m (fiberLin U) = 0 :=
      (congrArg (fun x => chainChartCoordinatesCLM 3 m x) hU).trans (map_zero _)
    exact (energySmoothToChainChart_coordinates 3 m (fiberES U)).symm.trans key
  have hae : ∀ n, ((fiberES U).val n : ℂ → ℂ)
      =ᵐ[volume.restrict (Surface.disk : Set ℂ)] 0 := by
    intro n
    have h1 := energySmoothCopy_value_ae (fiberES U) n
    rw [show energySmoothCopy (fiberES U) n = 0 from congrFun hcoord n, map_zero] at h1
    exact h1.symm.trans (Lp.coeFn_zero ℂ 2 _)
  have heqon : ∀ n, Set.EqOn ((fiberES U).val n) 0 Surface.disk := fun n =>
    Measure.eqOn_open_of_ae_eq (hae n) Metric.isOpen_ball
      ((fiberES U).property.1.1 n).continuousOn continuousOn_const
  have hu0 : (fiberES U).val = 0 :=
    boundedJacobi_zero_of_disk_zero (fiberES_mem_boundedJacobi U)
      (fun n z hz => heqon n hz)
  have hUval : U.val = 0 := by
    have hu0' : (uncurryE m).symm U.val = 0 := hu0
    have h := congrArg (uncurryE m) hu0'
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h
  exact Subtype.ext hUval

/-- **The injection into the sampled sector**, bundled: `isotypicFiber 3 m r a →ₗ PaperChainSector
m a r` (corestrict `fiberLin` through the phase-domain and the sector memberships).  The first leg
of the transport; injective. -/
noncomputable def fiberToSectorLin {m r a : ℕ} [NeZero m] :
    isotypicFiber 3 m r a →ₗ[ℂ] KsIndex.Spherical.PaperChainSector m a r :=
  LinearMap.codRestrict (KsIndex.Spherical.PaperChainSector m a r)
    (LinearMap.codRestrict
      (chainChartPhaseDomain 3 m (KsIndex.Spherical.paperPhase ((a : ℝ) / m)))
      fiberLin (fun U => fiberToChain_mem_phase U))
    (fun U => fiberToPhase_mem_sector U)

lemma fiberToSectorLin_injective {m r a : ℕ} [NeZero m] :
    Function.Injective (fiberToSectorLin (m := m) (r := r) (a := a)) := fun _ _ h =>
  fiberLin_injective
    (congrArg (fun w : KsIndex.Spherical.PaperChainSector m a r => w.val.val) h)

/-! ### the injection into the sphere character domain

Compose `fiberToSectorLin` with the `paperChainSlitEquiv` (chain sector ≃ slit character
domain) and `paperSlitCharacterSphereEquiv` (slit ≃ sphere character).  The composite is injective; its image lands in `paperSphericalCharacterRadical` below,
whose finrank is the per-character weak count. -/

/-- The fiber element carried all the way to the sphere character domain. -/
noncomputable def fiberToSphere {m r a : ℕ} [NeZero m] :
    isotypicFiber 3 m r a →ₗ[ℂ]
      KsIndex.Spectral.paperSphericalPhaseCharacter ((a : ℝ) / m) r :=
  ((KsIndex.Spectral.paperSlitCharacterSphereEquiv ((a : ℝ) / m) r).toLinearMap).comp
    (((KsIndex.Spectral.paperChainSlitEquiv m a r).toLinearMap).comp fiberToSectorLin)

lemma fiberToSphere_injective {m r a : ℕ} [NeZero m] :
    Function.Injective (fiberToSphere (m := m) (r := r) (a := a)) := by
  intro U U' h
  apply fiberToSectorLin_injective
  apply (KsIndex.Spectral.paperChainSlitEquiv m a r).injective
  apply (KsIndex.Spectral.paperSlitCharacterSphereEquiv ((a : ℝ) / m) r).injective
  exact h

/-- **The fiber image lands in the spherical character radical** — the ≤-side form-transfer crux.
Transport the sector pairing-zero fact (`fiberToPhase_pairing_zero`) through the two on-trunk
form-preserving equivalences: `paperChainSlitEquiv_jacobi` carries the chain pairing to the slit
weak-pair sum (up to the factor `m`), and `paperSlitCharacterSphere_jacobi` identifies that sum with
the sphere `sphereChartJacobi`.  Since every sphere test vector is `paperSlitCharacterSphereEquiv`
of a slit vector, and `m ≠ 0`, the sphere pairing vanishes against everything — i.e.
`fiberToSphere U ∈ paperSphericalCharacterRadical`. -/
lemma fiberToSphere_mem_radical {m r a : ℕ} [NeZero m] (U : isotypicFiber 3 m r a) :
    fiberToSphere U ∈
      KsIndex.Spectral.paperSphericalCharacterRadical ((a : ℝ) / m) r (surfacePotential 3) := by
  rw [KsIndex.Spectral.mem_paperSphericalCharacterRadical]
  intro w
  obtain ⟨sW, rfl⟩ :=
    (KsIndex.Spectral.paperSlitCharacterSphereEquiv ((a : ℝ) / m) r).surjective w
  have hFT : fiberToSphere U =
      KsIndex.Spectral.paperSlitCharacterSphereEquiv ((a : ℝ) / m) r
        (KsIndex.Spectral.paperChainSlitEquiv m a r (fiberToSectorLin U)) := rfl
  rw [hFT, KsIndex.Spectral.paperSlitCharacterSphere_jacobi]
  have hjac := KsIndex.Spectral.paperChainSlitEquiv_jacobi m a r (surfacePotential 3)
    (fiberToSectorLin U) ((KsIndex.Spectral.paperChainSlitEquiv m a r).symm sW)
  rw [LinearEquiv.apply_symm_apply] at hjac
  have hpair : chainChartJacobi 3 m (surfacePotential 3) (fiberToChain U)
      ((KsIndex.Spectral.paperChainSlitEquiv m a r).symm sW).val.val = 0 :=
    fiberToPhase_pairing_zero U ((KsIndex.Spectral.paperChainSlitEquiv m a r).symm sW)
  have hm := hjac.symm.trans hpair
  have hmne : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  exact (mul_eq_zero.mp hm).resolve_left hmne

/-! ### The rank bound: `rank(isotypicFiber) ≤ dim(spherical radical)`

Corestrict the injection to the radical (it lands there by `fiberToSphere_mem_radical`), then the
injective linear map into the finite-dimensional radical bounds the source rank.  This is the
per-character ≤ half of the squeeze: each isotypic fiber's rank is at most the per-character weak
nullity (`= finrank(paperSphericalCharacterRadical)`). -/

/-- The injection `fiberToSphere`, corestricted to the spherical character radical. -/
noncomputable def fiberToSphereRadical {m r a : ℕ} [NeZero m] :
    isotypicFiber 3 m r a →ₗ[ℂ]
      KsIndex.Spectral.paperSphericalCharacterRadical ((a : ℝ) / m) r (surfacePotential 3) :=
  LinearMap.codRestrict _ fiberToSphere (fun U => fiberToSphere_mem_radical U)

lemma fiberToSphereRadical_injective {m r a : ℕ} [NeZero m] :
    Function.Injective (fiberToSphereRadical (m := m) (r := r) (a := a)) := fun _ _ h =>
  fiberToSphere_injective (congrArg Subtype.val h)

/-- **The per-character ≤ bound.** The isotypic fiber's rank is at most the dimension of the
spherical character radical — the weak per-character nullity count. -/
lemma isotypicFiber_finrank_le {m r a : ℕ} [NeZero m] :
    Module.finrank ℂ (isotypicFiber 3 m r a) ≤
      Module.finrank ℂ
        (KsIndex.Spectral.paperSphericalCharacterRadical ((a : ℝ) / m) r (surfacePotential 3)) := by
  have := KsIndex.Spectral.paperSphericalCharacterRadical_finiteDimensional
    ((a : ℝ) / m) r (surfacePotential 3)
  exact LinearMap.finrank_le_finrank_of_injective fiberToSphereRadical_injective

/-! ### The interior per-character counts

Composing the rank bound with the spherical-sector facts (`three_paperSpherical_*`) pins
the interior per-character contribution: at an interior phase `a/m ∈ (0,1)` the sphere index is
`≥ 1` and `index + nullity ≤ 2`, so each fiber's rank is `≤ 1`; and the trivial rotation class
`r = 0` has nullity `0`.  These are the numeric inputs the per-class capstone sums (interior `a`,
`r = 1,2` contribute at most one each; `r = 0` contributes nothing). -/

/-- Arithmetic: `index + nullity ≤ 2` with `index ≥ 1` forces `nullity ≤ 1` (in `ℕ`). -/
private lemma enat_null_le_one {N : ℕ} {I : ℕ∞} (hsum : I + (N : ℕ∞) ≤ 2) (hidx : 1 ≤ I) :
    N ≤ 1 := by
  have h1 : (1 : ℕ∞) + (N : ℕ∞) ≤ 2 :=
    le_trans (add_le_add hidx (le_refl (N : ℕ∞))) hsum
  rw [← Nat.cast_one, ← Nat.cast_add, show (2 : ℕ∞) = ((2 : ℕ) : ℕ∞) by norm_cast,
    Nat.cast_le] at h1
  omega

/-- For `0 < a < m`, the rational phase `a/m` sits in the physical interior `(0,1)`. -/
private lemma interior_phase_bounds {m a : ℕ} [NeZero m] (ha0 : 0 < a) (ham : a < m) :
    0 < (a : ℝ) / m ∧ (a : ℝ) / m < 1 := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  refine ⟨div_pos ?_ hm, ?_⟩
  · exact_mod_cast ha0
  · rw [div_lt_one hm]; exact_mod_cast ham

/-- **Interior per-character bound.** At an interior phase (`0 < a < m`) each isotypic fiber of a
nontrivial-or-trivial rotation class `r < 3` has rank at most one. -/
lemma isotypicFiber_interior_finrank_le_one {m r a : ℕ} [NeZero m]
    (ha0 : 0 < a) (ham : a < m) (hr : r < 3) :
    Module.finrank ℂ (isotypicFiber 3 m r a) ≤ 1 := by
  obtain ⟨h0, h1⟩ := interior_phase_bounds ha0 ham
  refine le_trans isotypicFiber_finrank_le ?_
  exact enat_null_le_one
    (KsIndex.Spectral.three_paperSpherical_index_add_nullity_le_two h0 h1 hr)
    (KsIndex.Spectral.three_paperSpherical_index_ge_one ((a : ℝ) / m) hr)

/-- **Interior trivial class vanishes.** At an interior phase the trivial rotation class `r = 0`
(Dirichlet sector) contributes nothing to the nullity. -/
lemma isotypicFiber_interior_r0_finrank_zero {m a : ℕ} [NeZero m]
    (ha0 : 0 < a) (ham : a < m) :
    Module.finrank ℂ (isotypicFiber 3 m 0 a) = 0 := by
  obtain ⟨h0, h1⟩ := interior_phase_bounds ha0 ham
  have hle := isotypicFiber_finrank_le (m := m) (r := 0) (a := a)
  rw [KsIndex.Spectral.three_paperSpherical_zero_nullity_zero h0 h1] at hle
  exact Nat.le_zero.mp hle

/-! ### Plugging into the decomposition sum

`nulSurface_eq_sum_isotypic` sums `Cardinal.toENat (Module.rank ℂ (isotypicFiber …))`.  The
injection into the finite-dimensional radical makes each fiber finite-dimensional, so that
`ℕ∞`-rank is the cast of the `ℕ`-valued `finrank`, and the per-character bounds above apply term by
term.  The per-interior-phase total is then `≤ 2` (`r = 0` vanishes, `r = 1,2` give `≤ 1` each). -/

/-- Each isotypic fiber is finite-dimensional (it injects into the finite-dimensional radical). -/
lemma isotypicFiber_finiteDimensional {m r a : ℕ} [NeZero m] :
    FiniteDimensional ℂ (isotypicFiber 3 m r a) := by
  have := KsIndex.Spectral.paperSphericalCharacterRadical_finiteDimensional
    ((a : ℝ) / m) r (surfacePotential 3)
  exact FiniteDimensional.of_injective fiberToSphereRadical fiberToSphereRadical_injective

/-- The `ℕ∞`-rank of a fiber is the cast of its `ℕ`-valued `finrank` (it is finite-dimensional). -/
lemma isotypicFiber_rank_toENat {m r a : ℕ} [NeZero m] :
    Cardinal.toENat (Module.rank ℂ (isotypicFiber 3 m r a)) =
      (Module.finrank ℂ (isotypicFiber 3 m r a) : ℕ∞) := by
  have := isotypicFiber_finiteDimensional (m := m) (r := r) (a := a)
  rw [← Module.finrank_eq_rank ℂ (isotypicFiber 3 m r a)]
  simp

/-- **Per-interior-phase total `≤ 2`.** At an interior phase, the three rotation classes together
contribute at most two to the nullity (`r = 0` gives `0`, `r = 1,2` give `≤ 1` each). -/
lemma interiorPhase_total_le_two {m a : ℕ} [NeZero m] (ha0 : 0 < a) (ham : a < m) :
    ∑ r : Fin 3, Cardinal.toENat (Module.rank ℂ (isotypicFiber 3 m (r : ℕ) a)) ≤ 2 := by
  have key : ∑ r : Fin 3, Cardinal.toENat (Module.rank ℂ (isotypicFiber 3 m (r : ℕ) a))
      = ((∑ r : Fin 3, Module.finrank ℂ (isotypicFiber 3 m (r : ℕ) a) : ℕ) : ℕ∞) := by
    push_cast
    exact Finset.sum_congr rfl (fun r _ => isotypicFiber_rank_toENat)
  rw [key]
  have hnat : ∑ r : Fin 3, Module.finrank ℂ (isotypicFiber 3 m (r : ℕ) a) ≤ 2 := by
    rw [Fin.sum_univ_three]
    have h0 := isotypicFiber_interior_r0_finrank_zero (m := m) (a := a) ha0 ham
    have h1 := isotypicFiber_interior_finrank_le_one (m := m) (r := ((1 : Fin 3) : ℕ)) (a := a)
      ha0 ham (by decide)
    have h2 := isotypicFiber_interior_finrank_le_one (m := m) (r := ((2 : Fin 3) : ℕ)) (a := a)
      ha0 ham (by decide)
    simp only [Fin.val_zero] at h0 ⊢
    omega
  exact_mod_cast hnat

/-! ### Bridge to the sector nullity

`mem_paperSphericalCharacterRadical` exhibits `paperSphericalCharacterRadical` as the radical of the
sphere Jacobi form, and `paperSlitCharacterSphere_jacobi` identifies that form — through
`paperSlitCharacterSphereEquiv` — with the pair weak-Jacobi form on the slit character domain.  So
the radical's `finrank` equals the sector `sesqNullity`.  This is the hinge to the sector
count theorems (`paperSlit_nullity_eq_sectorClass`): no `finiteCopyWeakNullity` transport needed. -/

/-- **The radical dimension is the pair-weak sector nullity** (general `α, j`, unconditional). -/
lemma radical_finrank_eq_pair_sesqNullity (α : ℝ) (j : ℕ) (V : BoundedRealPotential) :
    (Module.finrank ℂ (KsIndex.Spectral.paperSphericalCharacterRadical α j V) : ℕ∞) =
      KsIndex.DtnBridge.sesqNullity (fun u v : KsIndex.Trace.paperSlitCharacterDomain α j =>
        weakJacobi V u.val.1 v.val.1 + weakJacobi V u.val.2 v.val.2) := by
  have := KsIndex.Spectral.paperSphericalCharacterRadical_finiteDimensional α j V
  have h2 := KsIndex.DtnBridge.sesqNullity_eq_finrank_radical
    (fun u v : KsIndex.Spectral.paperSphericalPhaseCharacter α j =>
      KsIndex.Spherical.sphereChartJacobi (KsIndex.Trace.isOpen_boundaryArc 3 1) V
        u.val.val v.val.val)
    (KsIndex.Spectral.paperSphericalCharacterRadical α j V)
    (KsIndex.Spectral.mem_paperSphericalCharacterRadical α j V)
  have h3 := KsIndex.DtnBridge.sesqNullity_congr
    (KsIndex.Spectral.paperSlitCharacterSphereEquiv α j)
    (fun u v : KsIndex.Trace.paperSlitCharacterDomain α j =>
      weakJacobi V u.val.1 v.val.1 + weakJacobi V u.val.2 v.val.2)
    (fun u v : KsIndex.Spectral.paperSphericalPhaseCharacter α j =>
      KsIndex.Spherical.sphereChartJacobi (KsIndex.Trace.isOpen_boundaryArc 3 1) V
        u.val.val v.val.val)
    (fun u v => KsIndex.Spectral.paperSlitCharacterSphere_jacobi α j V u v)
  rw [← h2, h3]

/-- Each fiber for `k = 3` and nonzero `m` has dimension bounded by the pair-weak
sector nullity at phase `a/m` and character `r`. This is an upper bound, not a
surjectivity or equal-dimension assertion. -/
lemma isotypicFiber_finrank_le_pair_sesqNullity {m r a : ℕ} [NeZero m] :
    (Module.finrank ℂ (isotypicFiber 3 m r a) : ℕ∞) ≤
      KsIndex.DtnBridge.sesqNullity
        (fun u v : KsIndex.Trace.paperSlitCharacterDomain ((a : ℝ) / m) r =>
          weakJacobi (surfacePotential 3) u.val.1 v.val.1
        + weakJacobi (surfacePotential 3) u.val.2 v.val.2) := by
  rw [← radical_finrank_eq_pair_sesqNullity ((a : ℝ) / m) r (surfacePotential 3)]
  exact_mod_cast isotypicFiber_finrank_le

/-! ### Sharp off-threshold vanishing (unconditional)

The weak sector nullity vanishes phase-wise whenever the phase avoids both thresholds `α*` and
`1 − α*` (this needs no irrationality assumption — it is the circle threshold
characterization `nul s = [s = s*]`).  Composed with the capstone ≤ consumable and the interior
sector theorem, every interior non-threshold phase contributes nothing to the nullity. -/

/-- Off the threshold `s*`, the circle nullity vanishes (the `= 0` face of `circle_main`'s
nullity clause, isolated at `Staircase.sstar`). -/
lemma nul_eq_zero_of_ne {s : ℝ} (hs : 0 < s) (hne : s ≠ KsIndex.Staircase.sstar) :
    KsIndex.Statements.nul s = 0 := by
  obtain ⟨_, _, hbelow, habove⟩ := KsIndex.Staircase.sstar_spec
  have hne0 : KsIndex.CircleQ.gam s ≠ 0 := by
    rcases lt_trichotomy s KsIndex.Staircase.sstar with hlt | he | hgt
    · exact ne_of_lt (hbelow s hs hlt)
    · exact absurd he hne
    · exact ne_of_gt (habove s hgt)
  have hne1 : KsIndex.Statements.nul s ≠ 1 :=
    fun h => hne0 ((KsIndex.Statements.nul_eq_one_iff hs).mp h)
  exact Order.lt_one_iff.mp (lt_of_le_of_ne (KsIndex.Statements.nul_le_one s) hne1)

/-- `tan(βπ/2) = s*` exactly at the threshold phase `β = 1 − α*` (the `=` analogue of
`tan_half_lt_sstar_iff`, via injectivity of `arctan`). -/
lemma tan_half_eq_sstar_iff {β : ℝ} (h0 : 0 < β) (h1 : β < 1) :
    Real.tan (β * Real.pi / 2) = KsIndex.Staircase.sstar ↔ β = 1 - KsIndex.Staircase.alphaStar := by
  have hπ := Real.pi_pos
  have hb0 : 0 < β * Real.pi / 2 := by positivity
  have hb1 : β * Real.pi / 2 < Real.pi / 2 := by
    nlinarith [mul_pos (show (0 : ℝ) < 1 - β by linarith) hπ]
  rw [← Real.arctan_strictMono.injective.eq_iff, Real.arctan_tan (by linarith) hb1,
    KsIndex.Staircase.arctan_sstar_eq, KsIndex.Staircase.alphaStar]
  have key : (1 : ℝ) - 2 / Real.pi * Real.arctan (1 / KsIndex.Staircase.sstar)
      = (Real.pi / 2 - Real.arctan (1 / KsIndex.Staircase.sstar)) / (Real.pi / 2) := by
    field_simp [Real.pi_ne_zero]
  rw [key, eq_div_iff (by positivity : (Real.pi / 2 : ℝ) ≠ 0), mul_div_assoc]

/-- **The weak sector nullity vanishes off threshold** (`α ∉ {α*, 1 − α*}`, interior). -/
lemma sector_nullity_zero_of_off_threshold {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (hα : α ≠ KsIndex.Staircase.alphaStar) (hα' : α ≠ 1 - KsIndex.Staircase.alphaStar) :
    KsIndex.FormIndex.formNullity (KsIndex.SectorForm.NBform α) KsIndex.Sector.Domς = 0 := by
  rw [KsIndex.SectorPhase.sector_nullity_eq α h0 h1]
  have hπ := Real.pi_pos
  have hx0 : 0 < α * Real.pi / 2 := by positivity
  have hx1 : α * Real.pi / 2 < Real.pi / 2 := by
    nlinarith [mul_pos (show (0 : ℝ) < 1 - α by linarith) hπ]
  have ht1pos : 0 < Real.tan (α * Real.pi / 2) := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith))
      (Real.cos_pos_of_mem_Ioo ⟨by linarith, hx1⟩)
  have ht2eq : Real.tan ((1 - α) * Real.pi / 2) = (Real.tan (α * Real.pi / 2))⁻¹ := by
    rw [show (1 - α) * Real.pi / 2 = Real.pi / 2 - α * Real.pi / 2 by ring,
      Real.tan_pi_div_two_sub]
  have ht2pos : 0 < Real.tan ((1 - α) * Real.pi / 2) := by rw [ht2eq]; exact inv_pos.mpr ht1pos
  have hne1 : Real.tan (α * Real.pi / 2) ≠ KsIndex.Staircase.sstar :=
    mt (tan_half_eq_sstar_iff h0 h1).mp hα'
  have hne2 : Real.tan ((1 - α) * Real.pi / 2) ≠ KsIndex.Staircase.sstar := by
    intro h
    have hh : (1 : ℝ) - α = 1 - KsIndex.Staircase.alphaStar :=
      (tan_half_eq_sstar_iff (by linarith) (by linarith)).mp h
    exact hα (by linarith)
  rw [nul_eq_zero_of_ne ht1pos hne1, nul_eq_zero_of_ne ht2pos hne2, add_zero]

/-- **Interior non-threshold fibers vanish** (unconditional).  For an interior phase `a/m` that
avoids both thresholds and a nontrivial rotation class `r` (`3 ∤ r`), the isotypic fiber is trivial:
`finrank = 0`.  This is the ≤-side heart of `nulSurface 3 m = 3` — every interior phase other than
`α*`, `1 − α*` contributes nothing. -/
lemma isotypicFiber_offThreshold_finrank_zero {m r a : ℕ} [NeZero m]
    (ha0 : 0 < a) (ham : a < m) (hr : ¬ (3 ∣ r))
    (hα : (a : ℝ) / m ≠ KsIndex.Staircase.alphaStar)
    (hα' : (a : ℝ) / m ≠ 1 - KsIndex.Staircase.alphaStar) :
    Module.finrank ℂ (isotypicFiber 3 m r a) = 0 := by
  obtain ⟨h0, h1⟩ := interior_phase_bounds ha0 ham
  have hle := isotypicFiber_finrank_le_pair_sesqNullity (m := m) (r := r) (a := a)
  rw [KsIndex.PaperSlitAdapter.paperSlit_nullity_eq_sectorClass ((a : ℝ) / m) h0 h1 hr,
    sector_nullity_zero_of_off_threshold h0 h1 hα hα'] at hle
  exact_mod_cast nonpos_iff_eq_zero.mp hle

/-- **Interior non-threshold phases contribute nothing to the decomposition sum.**  For `a ≠ 0`
with `a/m ∉ {α*, 1 − α*}`, the whole rotation-class sum of `toENat`-ranks vanishes (`r = 0` by
`interior_r0`, `r = 1,2` by the off-threshold vanishing).  This is the per-phase form the capstone
sum consumes: only the threshold phases (and `a = 0`) survive. -/
lemma interiorPhase_total_zero_of_offThreshold {m a : ℕ} [NeZero m]
    (ha0 : 0 < a) (ham : a < m)
    (hα : (a : ℝ) / m ≠ KsIndex.Staircase.alphaStar)
    (hα' : (a : ℝ) / m ≠ 1 - KsIndex.Staircase.alphaStar) :
    ∑ r : Fin 3, Cardinal.toENat (Module.rank ℂ (isotypicFiber 3 m (r : ℕ) a)) = 0 := by
  have key : ∑ r : Fin 3, Cardinal.toENat (Module.rank ℂ (isotypicFiber 3 m (r : ℕ) a))
      = ((∑ r : Fin 3, Module.finrank ℂ (isotypicFiber 3 m (r : ℕ) a) : ℕ) : ℕ∞) := by
    push_cast
    exact Finset.sum_congr rfl (fun r _ => isotypicFiber_rank_toENat)
  rw [key]
  have hnat : ∑ r : Fin 3, Module.finrank ℂ (isotypicFiber 3 m (r : ℕ) a) = 0 := by
    rw [Fin.sum_univ_three]
    have h0 := isotypicFiber_interior_r0_finrank_zero (m := m) (a := a) ha0 ham
    have h1 := isotypicFiber_offThreshold_finrank_zero (m := m) (r := ((1 : Fin 3) : ℕ)) (a := a)
      ha0 ham (by decide) hα hα'
    have h2 := isotypicFiber_offThreshold_finrank_zero (m := m) (r := ((2 : Fin 3) : ℕ)) (a := a)
      ha0 ham (by decide) hα hα'
    simp only [Fin.val_zero] at h0 ⊢
    omega
  exact_mod_cast hnat

/-! ### The conditional general-m nullity equality (`k = 3`)

The decomposition, interior off-threshold vanishing, and translation lower
bound give `nulSurface 3 m = 3` when no interior sampled phase is a threshold
and each zero-phase fiber has dimension at most one. The latter condition is
the explicit hypothesis `hzero`. -/
theorem nulSurface_eq_three_of_no_interior_threshold {m : ℕ} [NeZero m]
    (hthresh : ∀ a : Fin m, (a : ℕ) ≠ 0 →
      ((a : ℕ) : ℝ) / m ≠ KsIndex.Staircase.alphaStar ∧
      ((a : ℕ) : ℝ) / m ≠ 1 - KsIndex.Staircase.alphaStar)
    (hzero : ∀ r : Fin 3, Module.finrank ℂ (isotypicFiber 3 m (r : ℕ) 0) ≤ 1) :
    nulSurface 3 m = 3 := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  refine le_antisymm ?_ (KsIndex.JacobiFamily.three_le_nulSurface 3 m (by norm_num))
  rw [nulSurface_eq_sum_isotypic 3 m (by norm_num) hm, Finset.sum_comm]
  have hsingle : ∀ b ∈ Finset.univ, b ≠ (0 : Fin m) →
      (∑ r : Fin 3, Cardinal.toENat (Module.rank ℂ (isotypicFiber 3 m (r : ℕ) (b : ℕ)))) = 0 := by
    intro b _ hb0
    have hb0' : (b : ℕ) ≠ 0 := fun h => hb0 (Fin.ext (by simpa using h))
    obtain ⟨hα, hα'⟩ := hthresh b hb0'
    exact interiorPhase_total_zero_of_offThreshold (Nat.pos_of_ne_zero hb0') b.isLt hα hα'
  rw [Finset.sum_eq_single (0 : Fin m) hsingle (fun h => absurd (Finset.mem_univ _) h)]
  simp only [Fin.val_zero]
  calc ∑ r : Fin 3, Cardinal.toENat (Module.rank ℂ (isotypicFiber 3 m (r : ℕ) 0))
      ≤ ∑ _r : Fin 3, (1 : ℕ∞) := by
        refine Finset.sum_le_sum fun r _ => ?_
        rw [isotypicFiber_rank_toENat]
        exact_mod_cast hzero r
    _ = 3 := by simp

/-- If `m·α*` is not an integer, no interior sampled phase equals either threshold.
Together with the zero-phase bound `hzero`, this gives `nulSurface 3 m = 3`. -/
theorem nulSurface_eq_three_of_mAlphaStar_not_int {m : ℕ} [NeZero m]
    (hzero : ∀ r : Fin 3, Module.finrank ℂ (isotypicFiber 3 m (r : ℕ) 0) ≤ 1)
    (hmα : ∀ n : ℤ, (m : ℝ) * KsIndex.Staircase.alphaStar ≠ (n : ℝ)) :
    nulSurface 3 m = 3 := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  refine nulSurface_eq_three_of_no_interior_threshold ?_ hzero
  intro a _
  refine ⟨fun h => hmα ((a : ℕ) : ℤ) ?_, fun h => hmα ((m : ℤ) - ((a : ℕ) : ℤ)) ?_⟩
  · rw [div_eq_iff hm0] at h; push_cast; linear_combination -h
  · rw [div_eq_iff hm0] at h; push_cast; linear_combination h

/-! ### The zero-phase interface

At `a = 0`, the fiber-to-sector bound has phase `0/m = 0`. A bound of one
on that sector's `sesqNullity` therefore supplies the zero-phase fiber bound. -/

/-- The zero-phase slot: `sesqNullity ≤ 1` at phase `0` ⇒ the `a = 0` fiber rank is `≤ 1`. -/
lemma isotypicFiber_zeroPhase_finrank_le_one {m : ℕ} [NeZero m] {r : ℕ}
    (hs : KsIndex.DtnBridge.sesqNullity
      (fun u v : KsIndex.Trace.paperSlitCharacterDomain 0 r =>
        weakJacobi (surfacePotential 3) u.val.1 v.val.1
      + weakJacobi (surfacePotential 3) u.val.2 v.val.2) ≤ 1) :
    Module.finrank ℂ (isotypicFiber 3 m r 0) ≤ 1 := by
  have hle := isotypicFiber_finrank_le_pair_sesqNullity (m := m) (r := r) (a := 0)
  have hp : ((0 : ℕ) : ℝ) / (m : ℝ) = 0 := by simp
  rw [hp] at hle
  exact_mod_cast le_trans hle hs

/-- The nonresonant nullity equality with the zero-phase hypothesis expressed
as a bound on the pair-weak sector's `sesqNullity`. -/
theorem nulSurface_eq_three_of_mAlphaStar_not_int_of_zeroPhase {m : ℕ} [NeZero m]
    (hz : ∀ r : Fin 3, KsIndex.DtnBridge.sesqNullity
      (fun u v : KsIndex.Trace.paperSlitCharacterDomain 0 (r : ℕ) =>
        weakJacobi (surfacePotential 3) u.val.1 v.val.1
      + weakJacobi (surfacePotential 3) u.val.2 v.val.2) ≤ 1)
    (hmα : ∀ n : ℤ, (m : ℝ) * KsIndex.Staircase.alphaStar ≠ (n : ℝ)) :
    nulSurface 3 m = 3 :=
  nulSurface_eq_three_of_mAlphaStar_not_int
    (fun r => isotypicFiber_zeroPhase_finrank_le_one (hz r)) hmα

/-! ### The resonant upper bound (reusing the endpoint count)

`KsIndex.BandArithmetic.endpoints α* m` (`Ico 1 m` filtered by `n/m ∈ {α*, 1−α*}`) is the
already-defined endpoint set, with `resonant_endpoints_card` (`= 2` or `0`) and
`resonance_bookkeeping` (`3 + 2·card = if m·α* ∈ ℤ then 7 else 3`).  Working the decomposition sum
over `ℕ` (via `Fin.sum_univ_eq_sum_range`) aligns the interior phases directly with that set — no
bijection needed: each nonzero phase contributes `0` off the endpoints and `≤ 2` on them. -/
theorem nulSurface_le_three_add_two_endpoints {m : ℕ} [NeZero m]
    (hzero : ∀ r : Fin 3, Module.finrank ℂ (isotypicFiber 3 m (r : ℕ) 0) ≤ 1) :
    nulSurface 3 m ≤
      3 + 2 * (KsIndex.BandArithmetic.endpoints KsIndex.Staircase.alphaStar m).card := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [nulSurface_eq_sum_isotypic 3 m (by norm_num) hm, Finset.sum_comm,
    Fin.sum_univ_eq_sum_range
      (fun n => ∑ r : Fin 3, Cardinal.toENat (Module.rank ℂ (isotypicFiber 3 m (r : ℕ) n))) m,
    ← Finset.add_sum_erase (Finset.range m) _ (Finset.mem_range.mpr hm)]
  have hEsub : KsIndex.BandArithmetic.endpoints KsIndex.Staircase.alphaStar m ⊆
      (Finset.range m).erase 0 := by
    intro n hn
    rw [KsIndex.BandArithmetic.endpoints, Finset.mem_filter, Finset.mem_Ico] at hn
    exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr hn.1.2⟩
  refine add_le_add ?_ ?_
  · calc (∑ r : Fin 3, Cardinal.toENat (Module.rank ℂ (isotypicFiber 3 m (r : ℕ) 0)))
        ≤ ∑ _r : Fin 3, (1 : ℕ∞) := by
          refine Finset.sum_le_sum fun r _ => ?_
          rw [isotypicFiber_rank_toENat]; exact_mod_cast hzero r
      _ = 3 := by simp
  · calc (∑ n ∈ (Finset.range m).erase 0,
            ∑ r : Fin 3, Cardinal.toENat (Module.rank ℂ (isotypicFiber 3 m (r : ℕ) n)))
        ≤ ∑ n ∈ (Finset.range m).erase 0,
            (if n ∈ KsIndex.BandArithmetic.endpoints KsIndex.Staircase.alphaStar m then (2 : ℕ∞)
              else 0) := by
          refine Finset.sum_le_sum fun n hn => ?_
          obtain ⟨hn0, hnm⟩ := Finset.mem_erase.mp hn
          have hnlt : n < m := Finset.mem_range.mp hnm
          split_ifs with hE
          · exact interiorPhase_total_le_two (Nat.pos_of_ne_zero hn0) hnlt
          · have hmemIco : n ∈ Finset.Ico 1 m := Finset.mem_Ico.mpr ⟨by omega, hnlt⟩
            have hnp : ¬ (((n : ℝ) / m = KsIndex.Staircase.alphaStar) ∨
                ((n : ℝ) / m = 1 - KsIndex.Staircase.alphaStar)) := fun hp =>
              hE (by rw [KsIndex.BandArithmetic.endpoints, Finset.mem_filter]; exact ⟨hmemIco, hp⟩)
            exact le_of_eq (interiorPhase_total_zero_of_offThreshold (Nat.pos_of_ne_zero hn0) hnlt
              (fun h => hnp (Or.inl h)) (fun h => hnp (Or.inr h)))
      _ = ∑ _n ∈ (Finset.range m).erase 0 ∩
            KsIndex.BandArithmetic.endpoints KsIndex.Staircase.alphaStar m, (2 : ℕ∞) :=
          Finset.sum_ite_mem _ _ _
      _ = ∑ _n ∈ KsIndex.BandArithmetic.endpoints KsIndex.Staircase.alphaStar m, (2 : ℕ∞) := by
          rw [Finset.inter_eq_right.mpr hEsub]
      _ = 2 * (KsIndex.BandArithmetic.endpoints KsIndex.Staircase.alphaStar m).card := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

open Classical in
/-- **The resonant dichotomy upper bound.**  Composed with `resonance_bookkeeping`:
`nul(Ξ_{3,m}) ≤ if m·α* ∈ ℤ then 7 else 3` (still carrying the `a = 0` slot `hzero`).  Together with
`three_le_nulSurface`, the nonresonant branch is exactly `3`; the resonant branch is pinned to the
window `[3,7]`; this upper-bound theorem does not construct threshold witnesses. -/
theorem nulSurface_le_seven_or_three {m : ℕ} [NeZero m]
    (hzero : ∀ r : Fin 3, Module.finrank ℂ (isotypicFiber 3 m (r : ℕ) 0) ≤ 1) :
    nulSurface 3 m ≤ if ∃ z : ℤ, (m : ℝ) * KsIndex.Staircase.alphaStar = (z : ℝ) then 7 else 3 := by
  have hbound := nulSurface_le_three_add_two_endpoints hzero
  have hb := KsIndex.Staircase.resonance_bookkeeping m (Nat.one_le_iff_ne_zero.mpr (NeZero.ne m))
  have hcast : (3 : ℕ∞) +
        2 * ((KsIndex.BandArithmetic.endpoints KsIndex.Staircase.alphaStar m).card : ℕ∞)
      = ((3 + 2 * (KsIndex.BandArithmetic.endpoints KsIndex.Staircase.alphaStar m).card : ℕ) :
          ℕ∞) := by
    push_cast; ring
  rw [hcast, hb] at hbound
  simpa only [Nat.cast_ite, Nat.cast_ofNat] using hbound

end KsIndex.NullityDecomp
