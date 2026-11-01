module

public import KsIndexLean.KarcherGlobalFirstGeometry

@[expose] public section


/-! The algebraic normalization step for a comparison of covering maps.
The analytic descent and constant-ratio reduction are NOT assumed proved here. -/
noncomputable section
namespace KsIndex.KarcherData

/-- A nonzero rotation mapping the puncture complement into itself must
preserve the puncture polynomial. One puncture suffices for the argument. -/
lemma rotation_puncture_power {k : ℕ} {ζ a : ℂ} (hζ : ζ ≠ 0)
    (ha : a ∈ Surface.punctures k)
    (havoid : ∀ w : ℂ, w ∉ Surface.punctures k → ζ * w ∉ Surface.punctures k) :
    ζ ^ (2 * k) = 1 := by
  have he : ζ * (a / ζ) = a := by field_simp
  have hw : a / ζ ∈ Surface.punctures k := by
    by_contra hn
    have hn' := havoid (a / ζ) hn
    rw [he] at hn'
    exact hn' ha
  change a ^ (2 * k) = -1 at ha
  change (a / ζ) ^ (2 * k) = -1 at hw
  rw [div_pow, ha] at hw
  have hh := (div_eq_iff (pow_ne_zero (2 * k) hζ)).mp hw
  simpa only [neg_mul, one_mul, neg_inj] using hh.symm

/-- Once comparison of normals has reduced two coverings to a constant
(k-1)-st root of unity, puncture avoidance and the labeled upper boundary
arc remove the remaining ambiguity. This is a conditional algebraic lemma,
not a covering-map uniqueness theorem. -/
theorem cover_rotation_normalization {k : ℕ} (hk : 2 ≤ k) {ζ a : ℂ}
    (hroot : ζ ^ (k - 1) = 1) (ha : a ∈ Surface.punctures k)
    (havoid : ∀ w : ℂ, w ∉ Surface.punctures k → ζ * w ∉ Surface.punctures k)
    (harc : ζ ∈ Surface.arc k 1) : ζ = 1 := by
  have hζ : ζ ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by omega : k - 1 ≠ 0)] at hroot
    exact zero_ne_one hroot
  have hp := rotation_puncture_power hζ ha havoid
  rw [show 2 * k = (k - 1) * 2 + 2 by omega, pow_add, pow_mul,
    hroot, one_pow, one_mul] at hp
  rcases sq_eq_one_iff.mp hp with hz | hz
  · exact hz
  · have hkpow : ζ ^ k = ζ := by
      rw [show k = (k - 1) + 1 by omega, pow_add, hroot, pow_one, one_mul]
    have hb := harc.2
    rw [hkpow, hz] at hb
    norm_num at hb

end KsIndex.KarcherData
