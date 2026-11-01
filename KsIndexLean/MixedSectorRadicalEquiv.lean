module

public import KsIndexLean.MixedPhysicalRadical
public import KsIndexLean.DiskJacobiSesquilinear
public import KsIndexLean.JacobiRadicalSpectrum

@[expose] public section


/-!
# Mixed j-character sector ≃ full-test weak (form) radical

For `k ≥ 2`, the physical mixed classical sector `classicalMixedSector hk j` is
complex-linearly equivalent to the full-test weak radical
`Spectral.formRadical (domainJacobiForm (mixedCharacterDomain k j true false) (surfacePotential k))`.
This is the kernel of the Jacobi form on the mixed `(j;k)`-character domain:
Dirichlet on arc 0 and Neumann on arc 1. The radical condition tests against
every vector in that domain, rather than only the vector itself.

The forward map is `classicalMixedSectorToH1`, restricted first to the character
domain and then to its form radical. The final coercion theorem identifies this
map in `ComplexH1` by definitional equality. Eigenspace and dimension transport
are separate results.

-/
set_option autoImplicit false
noncomputable section
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.WeakH1 KsIndex.FormIndex KsIndex.Spectral
namespace KsIndex.Trace

variable {k : ℕ}

/-- The mixed `(j;k)`-character domain (reducible: defeq to the full name). -/
abbrev mcDomain (k j : ℕ) : Submodule ℂ ComplexH1 := mixedCharacterDomain k j true false

/-- The Jacobi form on the mixed character domain. -/
abbrev mcForm (k j : ℕ) : mcDomain k j →L⋆[ℂ] mcDomain k j →L[ℂ] ℂ :=
  domainJacobiForm (mcDomain k j) (surfacePotential k)

/-- The full-test weak radical of the Jacobi form on the mixed character domain. -/
abbrev mcRadical (k j : ℕ) : Submodule ℂ (mcDomain k j) :=
  @Spectral.formRadical (mcDomain k j) inferInstance (diskDomain_innerProductSpace _) (mcForm k j)

/-- Equality in nested submodules follows from equality of the underlying H1 fields. -/
theorem nested_submodule_ext (D : Submodule ℂ ComplexH1) (R : Submodule ℂ D)
    (a b : R) (h : a.1.1 = b.1.1) : a = b :=
  Subtype.ext (Subtype.ext h)

/-- The sector→H¹ map is injective (physical carrier injectivity composed with the subtype). -/
theorem classicalMixedSectorToH1_injective (hk : 2 ≤ k) (j : ℕ) :
    Function.Injective (classicalMixedSectorToH1 hk j) := fun _ _ hab =>
  Submodule.injective_subtype _ (classicalMixedDiskToH1_injective hk true false hab)

/-- Per-element range characterisation: the image of a sector field lies in the character domain
and is a full-test weak-Jacobi solution there. -/
theorem classicalMixedSectorToH1_mem (hk : 2 ≤ k) (j : ℕ) (x : classicalMixedSector hk j) :
    classicalMixedSectorToH1 hk j x ∈ mcDomain k j ∧
      ∀ v ∈ mcDomain k j,
        weakJacobi (surfacePotential k) (classicalMixedSectorToH1 hk j x) v = 0 :=
  (classicalMixedSectorToH1_range hk j (classicalMixedSectorToH1 hk j x)).mp ⟨x, rfl⟩

/-- Sector field map, restricted to the character domain `mcDomain`. -/
def mixedSectorToDomain (hk : 2 ≤ k) (j : ℕ) :
    classicalMixedSector hk j →ₗ[ℂ] mcDomain k j :=
  (classicalMixedSectorToH1 hk j).codRestrict (mcDomain k j)
    (fun x => (classicalMixedSectorToH1_mem hk j x).1)

/-- Sector field map, further restricted to the form radical `mcRadical`. -/
def mixedSectorToRadical (hk : 2 ≤ k) (j : ℕ) :
    classicalMixedSector hk j →ₗ[ℂ] mcRadical k j :=
  (mixedSectorToDomain hk j).codRestrict (mcRadical k j) (fun x => by
    rw [Spectral.mem_formRadical]
    intro v
    change weakJacobi (surfacePotential k) (classicalMixedSectorToH1 hk j x) v.val = 0
    exact (classicalMixedSectorToH1_mem hk j x).2 v.val v.property)

/-- The doubly-restricted map carries the actual field (definitional). -/
theorem mixedSectorToRadical_coe (hk : 2 ≤ k) (j : ℕ) (x : classicalMixedSector hk j) :
    ((mixedSectorToRadical hk j x).val : ComplexH1) = classicalMixedSectorToH1 hk j x := rfl

theorem mixedSectorToRadical_injective (hk : 2 ≤ k) (j : ℕ) :
    Function.Injective (mixedSectorToRadical hk j) := fun _ _ hab =>
  classicalMixedSectorToH1_injective hk j (congrArg (fun r => (r.val.val : ComplexH1)) hab)

theorem mixedSectorToRadical_surjective (hk : 2 ≤ k) (j : ℕ) :
    Function.Surjective (mixedSectorToRadical hk j) := by
  intro r
  have hfull : ∀ v ∈ mcDomain k j, weakJacobi (surfacePotential k) r.val.val v = 0 := by
    intro v hv
    -- Use the same inner product instance as the radical carrier, then identify
    -- the restricted form with the weak Jacobi pairing.
    have hh := (@Spectral.mem_formRadical (mcDomain k j) inferInstance
      (diskDomain_innerProductSpace (mcDomain k j)) (mcForm k j) r.val).mp r.property ⟨v, hv⟩
    exact (domainJacobiForm_apply (mcDomain k j) (surfacePotential k) r.val ⟨v, hv⟩).symm.trans hh
  obtain ⟨x, hx⟩ :=
    (classicalMixedSectorToH1_range hk j r.val.val).mpr ⟨r.val.property, hfull⟩
  have hfield : (mixedSectorToRadical hk j x).val.val = r.val.val := by
    rw [mixedSectorToRadical_coe]
    exact hx
  exact ⟨x, nested_submodule_ext (mcDomain k j) (mcRadical k j)
    (mixedSectorToRadical hk j x) r hfield⟩

/-- The physical mixed classical `(j;k)`-character sector is linearly equivalent to
the full-test weak radical of the Jacobi form on the mixed character domain. -/
def classicalMixedSectorRadicalEquiv (hk : 2 ≤ k) (j : ℕ) :
    classicalMixedSector hk j ≃ₗ[ℂ] mcRadical k j :=
  LinearEquiv.ofBijective (mixedSectorToRadical hk j)
    ⟨mixedSectorToRadical_injective hk j, mixedSectorToRadical_surjective hk j⟩

/-- The radical equivalence, read back to
`ComplexH1`, is exactly the sector→H¹ map. -/
@[simp] theorem classicalMixedSectorRadicalEquiv_coe (hk : 2 ≤ k) (j : ℕ)
    (x : classicalMixedSector hk j) :
    ((classicalMixedSectorRadicalEquiv hk j x).val : ComplexH1)
      = classicalMixedSectorToH1 hk j x :=
  rfl

end KsIndex.Trace
