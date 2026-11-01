module

public import KsIndexLean.PureSectorSurjectivity

@[expose] public section


/-! The pure reflected bounded-field sectors are linearly equivalent to the
actual weak Jacobi radicals, via disk restriction. -/
noncomputable section
namespace KsIndex.NullityDecomp
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Surface KsIndex.Spectral

/-- The weak Jacobi form radical on a pure-boundary character domain. -/
abbrev pureSectorRadical (k r s : ℕ) :=
  @formRadical (mixedCharacterDomain k r (decide (s = 0)) (decide (s = 0)))
    inferInstance (diskDomain_innerProductSpace _)
    (domainJacobiForm (mixedCharacterDomain k r (decide (s = 0)) (decide (s = 0)))
      (surfacePotential k))

/-- Disk restriction with its actual weak-kernel codomain. -/
def pureSectorToRadical {k r s : ℕ} (hk : 2 ≤ k) (hs : s < 2) :
    boundedJacobiSector k r s s →ₗ[ℂ] pureSectorRadical k r s := by
  let D := mixedCharacterDomain k r (decide (s = 0)) (decide (s = 0))
  let L : boundedJacobiSector k r s s →ₗ[ℂ] D :=
    (sectorRestrict hk).codRestrict D (fun W => sectorRestrict_mem hk hs hs W)
  exact L.codRestrict _ (fun W => (mem_formRadical _ _).mpr
    (fun v => sector_weakJacobi_zero hk hs hs W v))

@[simp] lemma pureSectorToRadical_value {k r s : ℕ} (hk : 2 ≤ k) (hs : s < 2)
    (W : boundedJacobiSector k r s s) :
    (pureSectorToRadical hk hs W).val.val = sectorRestrictFun hk W := rfl

lemma pureSectorToRadical_bijective {k r s : ℕ} (hk : 2 ≤ k) (hs : s < 2) :
    Function.Bijective (pureSectorToRadical (r := r) hk hs) := by
  constructor
  · intro W V h
    apply sectorRestrict_injective hk
    exact congrArg (fun x : pureSectorRadical k r s => x.val.val) h
  · intro u
    have hQ : ∀ v : mixedCharacterDomain k r (decide (s = 0)) (decide (s = 0)),
        weakJacobi (surfacePotential k) u.val.val v.val = 0 :=
      (mem_formRadical _ _).mp u.property
    obtain ⟨W, hW, _⟩ := pure_sector_restriction_unique hk hs u.val hQ
    exact ⟨W, Subtype.ext (Subtype.ext hW)⟩

/-- Both directions are the actual restriction/lifting correspondence. -/
def pureSectorRadicalEquiv {k r s : ℕ} (hk : 2 ≤ k) (hs : s < 2) :
    boundedJacobiSector k r s s ≃ₗ[ℂ] pureSectorRadical k r s :=
  LinearEquiv.ofBijective (pureSectorToRadical hk hs) (pureSectorToRadical_bijective hk hs)

@[simp] theorem pureSectorRadicalEquiv_apply_value {k r s : ℕ}
    (hk : 2 ≤ k) (hs : s < 2) (W : boundedJacobiSector k r s s) :
    (pureSectorRadicalEquiv hk hs W).val.val = sectorRestrictFun hk W := rfl

@[simp] theorem pureSectorRadicalEquiv_inverse_restriction {k r s : ℕ}
    (hk : 2 ≤ k) (hs : s < 2) (u : pureSectorRadical k r s) :
    sectorRestrictFun hk ((pureSectorRadicalEquiv hk hs).symm u) = u.val.val := by
  exact congrArg (fun x : pureSectorRadical k r s => x.val.val)
    ((pureSectorRadicalEquiv hk hs).apply_symm_apply u)

/-- The bounded-field sector rank equals the pure-boundary weak nullity. -/
theorem pure_sector_rank_eq_nullity {k r s : ℕ} (hk : 2 ≤ k) (hs : s < 2) :
    Cardinal.toENat (Module.rank ℂ (boundedJacobiSector k r s s)) =
      (diskWeakNullity (mixedCharacterDomain k r (decide (s = 0)) (decide (s = 0)))
        (surfacePotential k) : ℕ∞) := by
  have hfin : FiniteDimensional ℂ (pureSectorRadical k r s) :=
    diskRadical_finiteDimensional _ _
  rw [(pureSectorRadicalEquiv (r := r) hk hs).rank_eq,
    ← Module.finrank_eq_rank ℂ (pureSectorRadical k r s)]
  simp [diskWeakNullity, pureSectorRadical]

end KsIndex.NullityDecomp
