module

/-
# Kernel orthonormality, inversion and the coefficient isometry

The multiplier by `ς` is represented in `CircleQ` by `convS`, with real
kernel `chat`. For square-summable complex sequences, this file proves
that `convS` preserves the sum of squared norms. Its transpose kernel
`Tker a n = chat (n - a)` supplies an inverse: `convK_TS_eq` and
`convK_ST_eq` prove both compositions pointwise on `ℓ²` inputs.
These identities describe the two coefficient directions of `ς² = 1`.

The first step is orthonormality of the shifted kernels:

`∑' m, chat (m - n) * chat (m - n') = if n = n' then 1 else 0`.

With `oddInv j = 1/(2j+1)`, partial fractions turn the off-diagonal
products into scaled differences of shifted profiles. Those differences
are absolutely summable. The unit-shift difference sums to zero by
splitting into two natural-number telescopes, with sums `-1` and `1`;
finite induction and reindexing handle all integer shifts. The diagonal
uses the odd-integer reciprocal-square sum from `CircleQ`.

For a general real kernel, column orthonormality gives isometry on
finite-support inputs. Square-summable rows with squared mass at most
one give convergence of truncated convolutions. Bounds on finite output
sums then prove the `ℓ²` contraction. Applying these results to `Sker`
and `Tker`, and passing their finite-support inverse identities to the
limit, proves inversion in both directions. The two contraction bounds
then give `tsum_convS_sq`; `tsum_convS_sq_eq_normSq` specializes it to
`MemDom` inputs.
-/
public import KsIndexLean.CircleQ

@[expose] public section


noncomputable section

namespace KsIndex.SIsometry

open KsIndex.CircleQ Real Filter Topology

/-- `oddInv j = 1/(2j+1)`, the unsigned kernel profile. -/
def oddInv (j : ℤ) : ℝ := 1 / (2 * (j : ℝ) + 1)

lemma oddInv_reflect (j : ℤ) : oddInv (-j - 1) = -oddInv j := by
  rw [oddInv, oddInv]
  push_cast
  rw [show 2 * (-(j : ℝ) - 1) + 1 = -(2 * (j : ℝ) + 1) from by ring, div_neg]

/-- Partial fractions: the product of two shifted profiles is a scaled
difference. -/
lemma oddInv_mul_oddInv {k : ℤ} (hk : k ≠ 0) (j : ℤ) :
    oddInv j * oddInv (j - k)
      = 1 / (2 * (k : ℝ)) * (oddInv (j - k) - oddInv j) := by
  have h1 := two_mul_add_one_ne_zero j
  have h2 := two_mul_add_one_ne_zero (j - k)
  have hk' : ((k : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hk
  rw [oddInv, oddInv]
  push_cast at h2 ⊢
  field_simp
  ring

/-- Square-summability of a shifted profile. -/
lemma summable_oddInv_shift_sq (c : ℤ) :
    Summable fun j : ℤ => oddInv (j - c) ^ 2 := by
  have hinj : Function.Injective (fun j : ℤ => j - c) := fun a b hab => by
    have : a - c = b - c := hab
    omega
  have h := hasSum_int_odd_sq_inv.summable.comp_injective hinj
  have hfun : ((fun d : ℤ => (1 : ℝ) / (2 * (d : ℝ) + 1) ^ 2) ∘
      fun j : ℤ => j - c) = fun j : ℤ => oddInv (j - c) ^ 2 := by
    funext j
    simp only [Function.comp_apply, oddInv, div_pow, one_pow]
  rwa [hfun] at h

/-- Absolute summability of a product of two shifted profiles (AM–GM). -/
lemma summable_oddInv_mul (c c' : ℤ) :
    Summable fun j : ℤ => oddInv (j - c) * oddInv (j - c') := by
  refine (((summable_oddInv_shift_sq c).add
    (summable_oddInv_shift_sq c')).mul_left (1 / 2)).of_norm_bounded ?_
  intro j
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|oddInv (j - c)| - |oddInv (j - c')|),
    abs_nonneg (oddInv (j - c)), abs_nonneg (oddInv (j - c')),
    sq_abs (oddInv (j - c)), sq_abs (oddInv (j - c'))]

/-- Summability of the telescope differences. -/
lemma summable_oddInv_sub_shift (c : ℤ) :
    Summable fun j : ℤ => oddInv (j - c) - oddInv j := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have h := (summable_oddInv_mul 0 c).mul_left (2 * (c : ℝ))
    refine h.congr fun j => ?_
    have hpf := oddInv_mul_oddInv hc j
    have hc' : ((c : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hc
    rw [show j - (0 : ℤ) = j from by ring] at *
    rw [hpf]
    field_simp

/-- Decay of a shifted profile along `ℕ`. -/
lemma tendsto_oddInv_shift (c : ℤ) :
    Tendsto (fun N : ℕ => oddInv ((N : ℤ) + c)) atTop (𝓝 0) := by
  have hgrow : Tendsto (fun N : ℕ => 2 * (N : ℝ) + (2 * (c : ℝ) + 1))
      atTop atTop :=
    tendsto_atTop_add_const_right _ _
      (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
  have h := tendsto_inv_atTop_zero.comp hgrow
  refine h.congr fun N => ?_
  simp only [Function.comp_apply, oddInv, one_div]
  push_cast
  ring_nf

/-- The unit telescope over `ℤ` vanishes. -/
lemma tsum_oddInv_sub_one : ∑' j : ℤ, (oddInv (j - 1) - oddInv j) = 0 := by
  have hodd0 : oddInv 0 = 1 := by norm_num [oddInv]
  have hoddneg : oddInv (-1) = -1 := by norm_num [oddInv]
  -- ℕ side: `∑_{n<N} (oddInv (n-1) - oddInv n) = oddInv (-1) - oddInv (N-1) → -1`
  have hnat : HasSum (fun n : ℕ => oddInv ((n : ℤ) - 1) - oddInv (n : ℤ))
      (-1) := by
    have hsummable : Summable fun n : ℕ =>
        oddInv ((n : ℤ) - 1) - oddInv (n : ℤ) := by
      have h : Summable ((fun j : ℤ => oddInv (j - 1) - oddInv j) ∘
          (Nat.cast : ℕ → ℤ)) :=
        (summable_oddInv_sub_shift 1).comp_injective Nat.cast_injective
      exact h.congr fun n => rfl
    have hnorm := hsummable.abs.congr fun n => (Real.norm_eq_abs _).symm
    rw [hasSum_iff_tendsto_nat_of_summable_norm hnorm]
    have htel : ∀ N : ℕ, (∑ n ∈ Finset.range N,
        (oddInv ((n : ℤ) - 1) - oddInv (n : ℤ)))
          = -1 - oddInv ((N : ℤ) - 1) := by
      intro N
      have hcast : ∀ i : ℕ, ((i + 1 : ℕ) : ℤ) - 1 = (i : ℤ) := fun i => by
        push_cast
        ring
      have h := Finset.sum_range_sub' (fun i : ℕ => oddInv ((i : ℤ) - 1)) N
      simp only [hcast] at h
      rw [h]
      norm_num [oddInv]
    have hlim : Tendsto (fun N : ℕ => -1 - oddInv ((N : ℤ) - 1))
        atTop (𝓝 (-1)) := by
      have h := (tendsto_const_nhds (x := (-1 : ℝ))
        (f := atTop (α := ℕ))).sub (tendsto_oddInv_shift (-1))
      rw [sub_zero] at h
      refine h.congr fun N => ?_
      rw [show ((N : ℕ) : ℤ) + (-1) = ((N : ℕ) : ℤ) - 1 from by ring]
    exact (tendsto_congr htel).mpr hlim
  -- negative side: reflection makes it the increasing telescope, → +1
  have hneg : HasSum (fun n : ℕ =>
      oddInv ((-((n : ℤ) + 1)) - 1) - oddInv (-((n : ℤ) + 1))) 1 := by
    have hfun : (fun n : ℕ =>
        oddInv ((-((n : ℤ) + 1)) - 1) - oddInv (-((n : ℤ) + 1)))
          = fun n : ℕ => oddInv (n : ℤ) - oddInv ((n : ℤ) + 1) := by
      funext n
      have h2 := oddInv_reflect ((n : ℤ) + 1)
      have h3 := oddInv_reflect (n : ℤ)
      rw [show (-(((n : ℕ) : ℤ) + 1)) - 1 = -(((n : ℤ) + 1)) - 1 from by ring,
        h2, show -(((n : ℕ) : ℤ) + 1) = -((n : ℤ)) - 1 from by ring, h3]
      ring
    rw [hfun]
    have hsummable : Summable fun n : ℕ =>
        oddInv (n : ℤ) - oddInv ((n : ℤ) + 1) := by
      have h : Summable ((fun j : ℤ => oddInv (j - (-1)) - oddInv j) ∘
          (Nat.cast : ℕ → ℤ)) :=
        (summable_oddInv_sub_shift (-1)).comp_injective Nat.cast_injective
      refine h.neg.congr fun n => ?_
      simp only [Function.comp_apply]
      rw [show ((n : ℕ) : ℤ) - (-1) = (n : ℤ) + 1 from by ring]
      ring
    have hnorm := hsummable.abs.congr fun n => (Real.norm_eq_abs _).symm
    rw [hasSum_iff_tendsto_nat_of_summable_norm hnorm]
    have htel : ∀ N : ℕ, (∑ n ∈ Finset.range N,
        (oddInv (n : ℤ) - oddInv ((n : ℤ) + 1)))
          = 1 - oddInv (N : ℤ) := by
      intro N
      have hcast : ∀ i : ℕ, ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 := fun i => by
        push_cast
        ring
      have h := Finset.sum_range_sub' (fun i : ℕ => oddInv (i : ℤ)) N
      simp only [hcast] at h
      rw [h]
      norm_num [oddInv]
    have hlim : Tendsto (fun N : ℕ => 1 - oddInv (N : ℤ))
        atTop (𝓝 1) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ))
        (f := atTop (α := ℕ))).sub (tendsto_oddInv_shift 0)
      rw [sub_zero] at h
      refine h.congr fun N => ?_
      rw [show ((N : ℕ) : ℤ) + (0 : ℤ) = ((N : ℕ) : ℤ) from by ring]
    exact (tendsto_congr htel).mpr hlim
  have h := HasSum.of_nat_of_neg_add_one
    (f := fun j : ℤ => oddInv (j - 1) - oddInv j) hnat hneg
  rw [h.tsum_eq]
  norm_num

/-- The unit telescope, shifted by any `c`, still vanishes. -/
lemma tsum_oddInv_sub_one_shift (c : ℤ) :
    ∑' j : ℤ, (oddInv ((j - c) - 1) - oddInv (j - c)) = 0 := by
  have h := Equiv.tsum_eq (Equiv.subRight c)
    (fun j : ℤ => oddInv (j - 1) - oddInv j)
  simp only [Equiv.subRight_apply] at h
  rw [h, tsum_oddInv_sub_one]

/-- Telescopes of nonnegative shift vanish (induction on the shift). -/
lemma tsum_oddInv_sub_ofNat (K : ℕ) :
    ∑' j : ℤ, (oddInv (j - (K : ℤ)) - oddInv j) = 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hsum : Summable fun j : ℤ =>
        oddInv ((j - (K : ℤ)) - 1) - oddInv (j - (K : ℤ)) := by
      have h : Summable ((fun j : ℤ => oddInv (j - 1) - oddInv j) ∘
          fun j : ℤ => j - (K : ℤ)) :=
        (summable_oddInv_sub_shift 1).comp_injective
          fun a b (hab : a - (K : ℤ) = b - (K : ℤ)) => by omega
      exact h.congr fun j => rfl
    have hsum2 : Summable fun j : ℤ => oddInv (j - (K : ℤ)) - oddInv j :=
      summable_oddInv_sub_shift _
    have hpt : ∀ j : ℤ,
        oddInv (j - ((K + 1 : ℕ) : ℤ)) - oddInv j
          = (oddInv ((j - (K : ℤ)) - 1) - oddInv (j - (K : ℤ)))
            + (oddInv (j - (K : ℤ)) - oddInv j) := by
      intro j
      rw [show j - ((K + 1 : ℕ) : ℤ) = (j - (K : ℤ)) - 1 from by push_cast; ring]
      ring
    calc ∑' j : ℤ, (oddInv (j - ((K + 1 : ℕ) : ℤ)) - oddInv j)
        = ∑' j : ℤ, ((oddInv ((j - (K : ℤ)) - 1) - oddInv (j - (K : ℤ)))
            + (oddInv (j - (K : ℤ)) - oddInv j)) := tsum_congr hpt
      _ = (∑' j : ℤ, (oddInv ((j - (K : ℤ)) - 1) - oddInv (j - (K : ℤ))))
            + ∑' j : ℤ, (oddInv (j - (K : ℤ)) - oddInv j) :=
          hsum.tsum_add hsum2
      _ = 0 := by rw [tsum_oddInv_sub_one_shift, ih, add_zero]

/-- Every telescope over `ℤ` vanishes. -/
lemma tsum_oddInv_sub_shift (k : ℤ) :
    ∑' j : ℤ, (oddInv (j - k) - oddInv j) = 0 := by
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨K, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    exact tsum_oddInv_sub_ofNat K
  · -- negative k: reindex by `+k` and negate, reducing to shift `-k ≥ 0`
    have h := Equiv.tsum_eq (Equiv.addRight k)
      (fun j : ℤ => oddInv (j - k) - oddInv j)
    have hfun : ∀ j : ℤ,
        (fun j : ℤ => oddInv (j - k) - oddInv j) ((Equiv.addRight k) j)
          = -(oddInv (j - (-k)) - oddInv j) := by
      intro j
      simp only [Equiv.coe_addRight]
      rw [show j + k - k = j from by ring, show j - -k = j + k from by ring]
      ring
    obtain ⟨K, hK⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ -k)
    calc ∑' j : ℤ, (oddInv (j - k) - oddInv j)
        = ∑' j : ℤ, (fun j : ℤ => oddInv (j - k) - oddInv j)
            ((Equiv.addRight k) j) := h.symm
      _ = ∑' j : ℤ, -(oddInv (j - (-k)) - oddInv j) := tsum_congr hfun
      _ = -∑' j : ℤ, (oddInv (j - (-k)) - oddInv j) := tsum_neg
      _ = 0 := by rw [hK, tsum_oddInv_sub_ofNat, neg_zero]

/-- Off-diagonal orthogonality of the shifted profiles. -/
lemma tsum_oddInv_mul_shift {k : ℤ} (hk : k ≠ 0) :
    ∑' j : ℤ, oddInv j * oddInv (j - k) = 0 := by
  calc ∑' j : ℤ, oddInv j * oddInv (j - k)
      = ∑' j : ℤ, 1 / (2 * (k : ℝ)) * (oddInv (j - k) - oddInv j) :=
        tsum_congr fun j => oddInv_mul_oddInv hk j
    _ = 1 / (2 * (k : ℝ)) * ∑' j : ℤ, (oddInv (j - k) - oddInv j) :=
        tsum_mul_left
    _ = 0 := by rw [tsum_oddInv_sub_shift, mul_zero]

/-- Sign bookkeeping: `(-1)^(2m - c) = (-1)^c` for integer exponents. -/
lemma neg_one_zpow_two_mul_sub (m c : ℤ) :
    ((-1 : ℝ)) ^ (2 * m - c) = (-1 : ℝ) ^ c := by
  rcases Int.even_or_odd c with ⟨t, ht⟩ | ⟨t, ht⟩
  · have h1 : Even (2 * m - c) := ⟨m - t, by omega⟩
    have h2 : Even c := ⟨t, by omega⟩
    rw [Even.neg_one_zpow h1, Even.neg_one_zpow h2]
  · have h1 : Odd (2 * m - c) := ⟨m - t - 1, by omega⟩
    have h2 : Odd c := ⟨t, by omega⟩
    rw [Odd.neg_one_zpow h1, Odd.neg_one_zpow h2]

/-- `chat` in factored form. -/
lemma chat_eq (d : ℤ) : chat d = 2 / π * (-1 : ℝ) ^ d * oddInv d := by
  rw [chat, oddInv]
  ring

/-- **Kernel orthonormality** — the coefficient-level content of `ς² = 1`:
the shifted kernels `chat (· - n)` form an orthonormal family in `ℓ²`. -/
theorem chat_orthonormal (n n' : ℤ) :
    ∑' m : ℤ, chat (m - n) * chat (m - n')
      = if n = n' then (1 : ℝ) else 0 := by
  rcases eq_or_ne n n' with rfl | hne
  · rw [if_pos rfl]
    have hbasel := hasSum_int_odd_sq_inv.mul_left (4 / π ^ 2)
    have hval : 4 / π ^ 2 * (π ^ 2 / 4) = 1 := by
      have hπ : π ≠ 0 := pi_ne_zero
      field_simp
    rw [hval] at hbasel
    have hre := Equiv.tsum_eq (Equiv.subRight n) (fun d : ℤ => chat d ^ 2)
    simp only [Equiv.subRight_apply] at hre
    calc ∑' m : ℤ, chat (m - n) * chat (m - n)
        = ∑' m : ℤ, chat (m - n) ^ 2 := tsum_congr fun m => (sq (chat (m - n))).symm
      _ = ∑' d : ℤ, chat d ^ 2 := hre
      _ = ∑' d : ℤ, 4 / π ^ 2 * ((1 : ℝ) / (2 * (d : ℝ) + 1) ^ 2) :=
          tsum_congr fun d => by rw [chat_sq]; ring
      _ = 1 := hbasel.tsum_eq
  · rw [if_neg hne]
    set k : ℤ := n' - n with hk
    have hkne : k ≠ 0 := by omega
    have hpt : ∀ m : ℤ, chat (m - n) * chat (m - n')
        = 4 / π ^ 2 * (-1 : ℝ) ^ (n + n')
          * (oddInv (m - n) * oddInv ((m - n) - k)) := by
      intro m
      rw [chat_eq, chat_eq, show m - n' = (m - n) - k from by omega]
      have hsign : (-1 : ℝ) ^ (m - n) * (-1 : ℝ) ^ ((m - n) - k)
          = (-1 : ℝ) ^ (n + n') := by
        rw [← zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0),
          show m - n + (m - n - k) = 2 * m - (n + n') from by omega,
          neg_one_zpow_two_mul_sub]
      calc 2 / π * (-1 : ℝ) ^ (m - n) * oddInv (m - n)
            * (2 / π * (-1 : ℝ) ^ ((m - n) - k) * oddInv ((m - n) - k))
          = (2 / π * (2 / π))
              * ((-1 : ℝ) ^ (m - n) * (-1 : ℝ) ^ ((m - n) - k))
              * (oddInv (m - n) * oddInv ((m - n) - k)) := by ring
        _ = 4 / π ^ 2 * (-1 : ℝ) ^ (n + n')
              * (oddInv (m - n) * oddInv ((m - n) - k)) := by
            rw [hsign]
            ring
    have hre := Equiv.tsum_eq (Equiv.subRight n)
      (fun j : ℤ => oddInv j * oddInv (j - k))
    simp only [Equiv.subRight_apply] at hre
    calc ∑' m : ℤ, chat (m - n) * chat (m - n')
        = ∑' m : ℤ, 4 / π ^ 2 * (-1 : ℝ) ^ (n + n')
            * (oddInv (m - n) * oddInv ((m - n) - k)) := tsum_congr hpt
      _ = 4 / π ^ 2 * (-1 : ℝ) ^ (n + n')
            * ∑' m : ℤ, oddInv (m - n) * oddInv ((m - n) - k) := tsum_mul_left
      _ = 4 / π ^ 2 * (-1 : ℝ) ^ (n + n')
            * ∑' j : ℤ, oddInv j * oddInv (j - k) := by rw [hre]
      _ = 0 := by rw [tsum_oddInv_mul_shift hkne, mul_zero]

/-! ### `chat` toolkit for the two instantiations -/

/-- The kernel reflection identity `ς̂(-d) = ς̂(d-1)`, the coefficient-level
statement that `S`'s adjoint is again a shifted `S`. -/
lemma chat_refl (d : ℤ) : chat (-d) = chat (d - 1) := by
  have ho : oddInv (-d) = -oddInv (d - 1) := by
    have h := oddInv_reflect (d - 1)
    rwa [show -(d - 1) - 1 = -d from by ring] at h
  rw [chat_eq, chat_eq, ho]
  rcases Int.even_or_odd d with ⟨t, ht⟩ | ⟨t, ht⟩
  · rw [Even.neg_one_zpow (⟨-t, by omega⟩ : Even (-d)),
        Odd.neg_one_zpow (⟨t - 1, by omega⟩ : Odd (d - 1))]
    ring
  · rw [Odd.neg_one_zpow (⟨-t - 1, by omega⟩ : Odd (-d)),
        Even.neg_one_zpow (⟨t, by omega⟩ : Even (d - 1))]
    ring

/-- `ς̂(b - m) = ς̂(m - (b+1))`, the reflection identity in shifted form. -/
lemma chat_refl_shift (b m : ℤ) : chat (b - m) = chat (m - (b + 1)) := by
  rw [show b - m = -(m - b) from by ring, chat_refl, show m - b - 1 = m - (b + 1) from by ring]

/-- The `ℤ`-Basel sum for the kernel: `∑_d ς̂(d)² = 1`. -/
theorem hasSum_chat_sq : HasSum (fun d : ℤ => chat d ^ 2) 1 := by
  have h := hasSum_int_odd_sq_inv.mul_left (4 / π ^ 2)
  have hval : 4 / π ^ 2 * (π ^ 2 / 4) = 1 := by
    have hπ : π ≠ 0 := pi_ne_zero
    field_simp
  rw [hval] at h
  have hfun : (fun d : ℤ => 4 / π ^ 2 * ((1 : ℝ) / (2 * (d : ℝ) + 1) ^ 2))
      = fun d : ℤ => chat d ^ 2 := by
    funext d; rw [chat_sq]; ring
  rwa [hfun] at h

lemma summable_chat_sq : Summable fun d : ℤ => chat d ^ 2 := hasSum_chat_sq.summable

/-- Square-summability with the shift on the FIRST index. -/
lemma summable_chat_fst_sq (n : ℤ) : Summable fun m : ℤ => chat (m - n) ^ 2 := by
  have hinj : Function.Injective (fun m : ℤ => m - n) := fun a b hab => by
    simp only at hab; omega
  exact (summable_chat_sq.comp_injective hinj).congr fun m => rfl

/-- Total kernel mass with the shift on the first index is `1`. -/
theorem tsum_chat_fst_sq (n : ℤ) : ∑' m : ℤ, chat (m - n) ^ 2 = 1 := by
  have hre := Equiv.tsum_eq (Equiv.subRight n) (fun d : ℤ => chat d ^ 2)
  simp only [Equiv.subRight_apply] at hre
  rw [hre, hasSum_chat_sq.tsum_eq]

/-- Total kernel mass with the shift on the SECOND index is `1`. -/
theorem tsum_chat_snd_sq (m : ℤ) : ∑' n : ℤ, chat (m - n) ^ 2 = 1 := by
  have hre := Equiv.tsum_eq (Equiv.subLeft m) (fun d : ℤ => chat d ^ 2)
  simp only [Equiv.subLeft_apply] at hre
  rw [hre, hasSum_chat_sq.tsum_eq]

/-- Summability of a product of two first-index shifts (AM–GM). -/
lemma summable_chat_shift_mul (n n' : ℤ) :
    Summable fun m : ℤ => chat (m - n) * chat (m - n') := by
  refine (((summable_chat_fst_sq n).add (summable_chat_fst_sq n')).mul_left
    (1 / 2)).of_norm_bounded ?_
  intro m
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|chat (m - n)| - |chat (m - n')|), sq_abs (chat (m - n)),
    sq_abs (chat (m - n'))]

/-! ### A `tsum`-level Cauchy–Schwarz -/

lemma summable_mul_of_sq {p q : ℤ → ℝ} (hp : Summable fun n => p n ^ 2)
    (hq : Summable fun n => q n ^ 2) : Summable fun n => p n * q n := by
  refine ((hp.add hq).mul_left (1 / 2)).of_norm_bounded ?_
  intro n
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|p n| - |q n|), sq_abs (p n), sq_abs (q n)]

theorem tsum_mul_sq_le {p q : ℤ → ℝ} (hp : Summable fun n => p n ^ 2)
    (hq : Summable fun n => q n ^ 2) :
    (∑' n : ℤ, p n * q n) ^ 2 ≤ (∑' n : ℤ, p n ^ 2) * ∑' n : ℤ, q n ^ 2 := by
  have hpq := summable_mul_of_sq hp hq
  have hfin : ∀ G : Finset ℤ,
      (∑ n ∈ G, p n * q n) ^ 2 ≤ (∑' n : ℤ, p n ^ 2) * ∑' n : ℤ, q n ^ 2 := by
    intro G
    calc (∑ n ∈ G, p n * q n) ^ 2
        ≤ (∑ n ∈ G, p n ^ 2) * ∑ n ∈ G, q n ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq G p q
      _ ≤ (∑' n : ℤ, p n ^ 2) * ∑' n : ℤ, q n ^ 2 :=
          mul_le_mul (hp.sum_le_tsum G fun _ _ => sq_nonneg _)
            (hq.sum_le_tsum G fun _ _ => sq_nonneg _)
            (Finset.sum_nonneg fun _ _ => sq_nonneg _)
            (tsum_nonneg fun _ => sq_nonneg _)
  have hts : Tendsto (fun G : Finset ℤ => ∑ n ∈ G, p n * q n) atTop
      (𝓝 (∑' n : ℤ, p n * q n)) := hpq.hasSum
  have htend : Tendsto (fun G : Finset ℤ => (∑ n ∈ G, p n * q n) ^ 2) atTop
      (𝓝 ((∑' n : ℤ, p n * q n) ^ 2)) := hts.pow 2
  exact le_of_tendsto htend (Eventually.of_forall hfin)

/-! ### Finite-support isometry and `ℓ²` contraction for a general
orthonormal kernel.

Everything is stated for an abstract kernel `K : ℤ → ℤ → ℝ` whose
columns are orthonormal, so that the two instantiations `K m n = chat (m-n)`
(the operator `S`) and `K n m = chat (m-n)` (its reflection `S̃`) share
all proofs. -/

section Kernel

variable {K : ℤ → ℤ → ℝ}

/-- The convolution operator attached to a kernel `K` (first index = output
variable). -/
def convK (K : ℤ → ℤ → ℝ) (u : ℤ → ℂ) (m : ℤ) : ℂ :=
  ∑' n : ℤ, (K m n : ℂ) * u n

/-- Interchange of a `tsum` with a finite sum, with the summability of the
pointwise sum as a bonus. -/
lemma summable_tsum_finset_sum {α : Type*} {M : Type*} [AddCommGroup M]
    [TopologicalSpace M] [ContinuousAdd M] [T2Space M]
    (s : Finset α) (f : α → ℤ → M)
    (hf : ∀ a ∈ s, Summable (f a)) :
    Summable (fun m : ℤ => ∑ a ∈ s, f a m) ∧
      ∑' m : ℤ, (∑ a ∈ s, f a m) = ∑ a ∈ s, ∑' m : ℤ, f a m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ihs, ihe⟩ := ih fun b hb => hf b (Finset.mem_insert_of_mem hb)
    have hfa : Summable (f a) := hf a (Finset.mem_insert_self a s)
    refine ⟨(hfa.add ihs).congr fun m => (Finset.sum_insert (f := fun b => f b m) ha).symm, ?_⟩
    calc ∑' m : ℤ, (∑ b ∈ insert a s, f b m)
        = ∑' m : ℤ, (f a m + ∑ b ∈ s, f b m) :=
          tsum_congr fun m => Finset.sum_insert (f := fun b => f b m) ha
      _ = (∑' m : ℤ, f a m) + ∑' m : ℤ, (∑ b ∈ s, f b m) := hfa.tsum_add ihs
      _ = ∑ b ∈ insert a s, ∑' m : ℤ, f b m := by
          rw [ihe, Finset.sum_insert (f := fun b => ∑' m : ℤ, f b m) ha]

/-- On finite-support input the convolution is a finite sum. -/
lemma convK_eq_sum {u : ℤ → ℂ} {F : Finset ℤ} (hF : ∀ n ∉ F, u n = 0)
    (m : ℤ) : convK K u m = ∑ n ∈ F, (K m n : ℂ) * u n :=
  tsum_eq_sum fun n hn => by rw [hF n hn, mul_zero]

/-- **Finite-support isometry**: for an orthonormal kernel, the convolution
preserves the `ℓ²` mass of finitely supported sequences.  Pure finite
interchange — no Fubini. -/
theorem finite_isometry
    (hKmul : ∀ n n' : ℤ, Summable fun m : ℤ => K m n * K m n')
    (hKorth : ∀ n n' : ℤ,
      ∑' m : ℤ, K m n * K m n' = if n = n' then (1 : ℝ) else 0)
    {u : ℤ → ℂ} {F : Finset ℤ} (hF : ∀ n ∉ F, u n = 0) :
    ∑' m : ℤ, ‖convK K u m‖ ^ 2 = ∑' n : ℤ, ‖u n‖ ^ 2 := by
  have hnormz : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  -- the square expands into a double finite sum
  have hpt : ∀ m : ℤ, ((‖convK K u m‖ ^ 2 : ℝ) : ℂ)
      = ∑ n ∈ F, ∑ n' ∈ F,
          ((K m n * K m n' : ℝ) : ℂ) * (u n * (starRingEnd ℂ) (u n')) := by
    intro m
    rw [hnormz, convK_eq_sum hF, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun n' _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  -- summability of each (n, n')-family in m
  have hsummul : ∀ n n' : ℤ, Summable fun m : ℤ =>
      ((K m n * K m n' : ℝ) : ℂ) * (u n * (starRingEnd ℂ) (u n')) :=
    fun n n' =>
      (Complex.summable_ofReal.mpr (hKmul n n')).mul_right _
  -- collapse the inner tsum via orthonormality
  have hval : ∀ n n' : ℤ,
      (∑' m : ℤ, ((K m n * K m n' : ℝ) : ℂ) * (u n * (starRingEnd ℂ) (u n')))
        = ((if n = n' then (1 : ℝ) else 0 : ℝ) : ℂ)
            * (u n * (starRingEnd ℂ) (u n')) := by
    intro n n'
    rw [tsum_mul_right, ← Complex.ofReal_tsum, hKorth]
  have hinner : ∀ n : ℤ, Summable (fun m : ℤ => ∑ n' ∈ F,
      ((K m n * K m n' : ℝ) : ℂ) * (u n * (starRingEnd ℂ) (u n'))) := fun n =>
    (summable_tsum_finset_sum F _ fun n' _ => hsummul n n').1
  have hmain : ((∑' m : ℤ, ‖convK K u m‖ ^ 2 : ℝ) : ℂ)
      = ((∑' n : ℤ, ‖u n‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    calc ∑' m : ℤ, ((‖convK K u m‖ ^ 2 : ℝ) : ℂ)
        = ∑' m : ℤ, ∑ n ∈ F, ∑ n' ∈ F,
            ((K m n * K m n' : ℝ) : ℂ) * (u n * (starRingEnd ℂ) (u n')) :=
          tsum_congr hpt
      _ = ∑ n ∈ F, ∑' m : ℤ, ∑ n' ∈ F,
            ((K m n * K m n' : ℝ) : ℂ) * (u n * (starRingEnd ℂ) (u n')) :=
          (summable_tsum_finset_sum F _ fun n _ => hinner n).2
      _ = ∑ n ∈ F, ∑ n' ∈ F, ∑' m : ℤ,
            ((K m n * K m n' : ℝ) : ℂ) * (u n * (starRingEnd ℂ) (u n')) :=
          Finset.sum_congr rfl fun n _ =>
            (summable_tsum_finset_sum F _ fun n' _ => hsummul n n').2
      _ = ∑ n ∈ F, ∑ n' ∈ F, ((if n = n' then (1 : ℝ) else 0 : ℝ) : ℂ)
            * (u n * (starRingEnd ℂ) (u n')) :=
          Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun n' _ =>
            hval n n'
      _ = ∑ n ∈ F, u n * (starRingEnd ℂ) (u n) := by
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [Finset.sum_congr rfl (fun n' _ => by
            rw [apply_ite (Complex.ofReal), Complex.ofReal_one,
              Complex.ofReal_zero, ite_mul, one_mul, zero_mul])]
          rw [Finset.sum_ite_eq, if_pos hn]
      _ = ∑ n ∈ F, ((‖u n‖ ^ 2 : ℝ) : ℂ) :=
          Finset.sum_congr rfl fun n _ => (hnormz (u n)).symm
      _ = ((∑ n ∈ F, ‖u n‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
      _ = ((∑' n : ℤ, ‖u n‖ ^ 2 : ℝ) : ℂ) := by
          rw [tsum_eq_sum (s := F) fun n hn => by rw [hF n hn]; simp]
  exact Complex.ofReal_injective hmain

/-! #### Truncations and the `ℓ²`-contraction bound -/

/-- Truncation of a sequence to the window `[-N, N]`. -/
def trunc (N : ℕ) (u : ℤ → ℂ) : ℤ → ℂ :=
  fun n => if n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then u n else 0

lemma trunc_support (N : ℕ) (u : ℤ → ℂ) :
    ∀ n ∉ Finset.Icc (-(N : ℤ)) (N : ℤ), trunc N u n = 0 :=
  fun _ hn => if_neg hn

lemma trunc_sq_le (N : ℕ) (u : ℤ → ℂ) (n : ℤ) :
    ‖trunc N u n‖ ^ 2 ≤ ‖u n‖ ^ 2 := by
  rw [trunc]
  split_ifs
  · exact le_rfl
  · simpa using sq_nonneg ‖u n‖

lemma summable_trunc_sq (N : ℕ) (u : ℤ → ℂ) :
    Summable fun n : ℤ => ‖trunc N u n‖ ^ 2 :=
  summable_of_ne_finset_zero (s := Finset.Icc (-(N : ℤ)) (N : ℤ))
    fun n hn => by rw [trunc_support N u n hn]; simp

/-- Absolute summability of the convolution integrand for `ℓ²` input, from
row square-summability of the kernel (AM–GM). -/
lemma summable_convK_term (hKrow : ∀ m : ℤ, Summable fun n : ℤ => K m n ^ 2)
    {u : ℤ → ℂ} (hu : Summable fun n : ℤ => ‖u n‖ ^ 2) (m : ℤ) :
    Summable fun n : ℤ => (K m n : ℂ) * u n := by
  refine Summable.of_norm ?_
  refine (((hKrow m).add hu).mul_left (1 / 2)).of_nonneg_of_le
    (fun n => norm_nonneg _) fun n => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  nlinarith [sq_nonneg (|K m n| - ‖u n‖), abs_nonneg (K m n),
    norm_nonneg (u n), sq_abs (K m n)]

/-- On finite-support input the square of the convolution is summable
(finite Cauchy–Schwarz against the shifted kernel squares). -/
lemma summable_convK_sq_of_support
    (hKmul : ∀ n n' : ℤ, Summable fun m : ℤ => K m n * K m n')
    {u : ℤ → ℂ} {F : Finset ℤ} (hF : ∀ n ∉ F, u n = 0) :
    Summable fun m : ℤ => ‖convK K u m‖ ^ 2 := by
  have hin : Summable fun m : ℤ => ∑ n ∈ F, K m n ^ 2 * ‖u n‖ ^ 2 :=
    (summable_tsum_finset_sum F (fun n => fun m : ℤ => K m n ^ 2 * ‖u n‖ ^ 2)
      fun n _ => by
        have h := (hKmul n n).mul_right (‖u n‖ ^ 2)
        exact h.congr fun m => by ring).1
  refine (hin.mul_left (F.card : ℝ)).of_nonneg_of_le
    (fun m => sq_nonneg _) fun m => ?_
  have h1 : ‖convK K u m‖ ≤ ∑ n ∈ F, |K m n| * ‖u n‖ := by
    rw [convK_eq_sum hF]
    refine (norm_sum_le F _).trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h2 : (∑ n ∈ F, |K m n| * ‖u n‖) ^ 2
      ≤ (F.card : ℝ) * ∑ n ∈ F, (|K m n| * ‖u n‖) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h3 : (∑ n ∈ F, (|K m n| * ‖u n‖) ^ 2)
      = ∑ n ∈ F, K m n ^ 2 * ‖u n‖ ^ 2 :=
    Finset.sum_congr rfl fun n _ => by rw [mul_pow, sq_abs]
  have h4 : ‖convK K u m‖ ^ 2 ≤ (∑ n ∈ F, |K m n| * ‖u n‖) ^ 2 := by
    have hnn : (0 : ℝ) ≤ ‖convK K u m‖ := norm_nonneg _
    nlinarith [h1]
  calc ‖convK K u m‖ ^ 2 ≤ (∑ n ∈ F, |K m n| * ‖u n‖) ^ 2 := h4
    _ ≤ (F.card : ℝ) * ∑ n ∈ F, (|K m n| * ‖u n‖) ^ 2 := h2
    _ = (F.card : ℝ) * ∑ n ∈ F, K m n ^ 2 * ‖u n‖ ^ 2 := by rw [h3]

/-- Pointwise convergence of the truncated convolutions, for `ℓ²` input:
the tail is controlled by AM–GM against the kernel row mass. -/
lemma tendsto_convK_trunc (hKrow : ∀ m : ℤ, Summable fun n : ℤ => K m n ^ 2)
    (hKrow1 : ∀ m : ℤ, (∑' n : ℤ, K m n ^ 2) ≤ 1)
    {u : ℤ → ℂ} (hu : Summable fun n : ℤ => ‖u n‖ ^ 2) (m : ℤ) :
    Tendsto (fun N : ℕ => convK K (trunc N u) m) atTop (𝓝 (convK K u m)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨F, hF⟩ := exists_finset_tsum_compl_lt hu
    (show (0 : ℝ) < ε ^ 2 / 4 by positivity)
  refine ⟨F.sup fun n => n.natAbs, fun N hN => ?_⟩
  have hFsub : F ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro n hn
    have h1 : n.natAbs ≤ F.sup fun n => n.natAbs :=
      Finset.le_sup (f := fun n : ℤ => n.natAbs) hn
    rw [Finset.mem_Icc]
    omega
  -- the difference is the tail sum
  have hsum_u := summable_convK_term hKrow hu m
  have hsum_t : Summable fun n : ℤ => (K m n : ℂ) * trunc N u n :=
    summable_of_ne_finset_zero (s := Finset.Icc (-(N : ℤ)) (N : ℤ))
      fun n hn => by rw [trunc_support N u n hn, mul_zero]
  have hdiff : convK K (trunc N u) m - convK K u m
      = -∑' n : ℤ, (if n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then 0
          else (K m n : ℂ) * u n) := by
    rw [convK, convK, ← hsum_t.tsum_sub hsum_u, ← tsum_neg]
    refine tsum_congr fun n => ?_
    rw [trunc]
    split_ifs <;> ring
  -- termwise AM–GM majorant
  set g : ℤ → ℂ := fun n =>
    if n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then 0 else (K m n : ℂ) * u n with hg
  set h : ℤ → ℝ := fun n => ε / 4 * K m n ^ 2
    + 1 / ε * (if n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then 0 else ‖u n‖ ^ 2)
    with hh
  have htail_summable : Summable fun n : ℤ =>
      (if n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then 0 else ‖u n‖ ^ 2) := by
    refine hu.of_nonneg_of_le (fun n => ?_) fun n => ?_
    · split_ifs
      · exact le_rfl
      · exact sq_nonneg _
    · split_ifs
      · exact sq_nonneg _
      · exact le_rfl
  have hh_summable : Summable h :=
    ((hKrow m).mul_left (ε / 4)).add (htail_summable.mul_left (1 / ε))
  have hgh : ∀ n : ℤ, ‖g n‖ ≤ h n := by
    intro n
    simp only [hg, hh]
    split_ifs with hmem
    · simp only [norm_zero, mul_zero, add_zero]
      positivity
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 : ε * (1 / ε * ‖u n‖ ^ 2) = ‖u n‖ ^ 2 := by field_simp
      refine le_of_mul_le_mul_left ?_ hε
      nlinarith [h1, sq_nonneg (ε * |K m n| - 2 * ‖u n‖), sq_abs (K m n),
        abs_nonneg (K m n), norm_nonneg (u n)]
  have hg_norm : Summable fun n : ℤ => ‖g n‖ :=
    hh_summable.of_nonneg_of_le (fun n => norm_nonneg _) hgh
  -- split off the head to control the tail sum
  have hhead_eq : (∑' n : ℤ,
      (if n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then ‖u n‖ ^ 2 else 0))
        = ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖u n‖ ^ 2 := by
    rw [tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) (N : ℤ))
      fun n hn => if_neg hn]
    exact Finset.sum_congr rfl fun n hn => if_pos hn
  have hhead_summable : Summable fun n : ℤ =>
      (if n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then ‖u n‖ ^ 2 else 0) :=
    summable_of_ne_finset_zero
      (s := Finset.Icc (-(N : ℤ)) (N : ℤ)) fun n hn => if_neg hn
  have htail_eq : (∑' n : ℤ,
      (if n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then 0 else ‖u n‖ ^ 2))
        = (∑' n : ℤ, ‖u n‖ ^ 2)
          - ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖u n‖ ^ 2 := by
    rw [← hhead_eq, ← hu.tsum_sub hhead_summable]
    refine tsum_congr fun n => ?_
    split_ifs <;> ring
  -- the tail is below ε²/4
  have hsplitF := hu.tsum_subtype_add_tsum_subtype_compl (↑F : Set ℤ)
  have hFin := Finset.tsum_subtype' F (fun n : ℤ => ‖u n‖ ^ 2)
  rw [hFin] at hsplitF
  have hFsum : (∑ n ∈ F, ‖u n‖ ^ 2)
      ≤ ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖u n‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hFsub fun n _ _ => sq_nonneg _
  have htail_lt : (∑' n : ℤ,
      (if n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then 0 else ‖u n‖ ^ 2))
        < ε ^ 2 / 4 := by
    rw [htail_eq]
    have : (∑' n : ℤ, ‖u n‖ ^ 2) - ∑ n ∈ F, ‖u n‖ ^ 2 < ε ^ 2 / 4 := by
      linarith [hF, hsplitF.symm]
    linarith [hFsum]
  -- assemble
  rw [dist_eq_norm, hdiff, norm_neg]
  have hb1 : ‖∑' n : ℤ, g n‖ ≤ ∑' n : ℤ, ‖g n‖ := norm_tsum_le_tsum_norm hg_norm
  have hb2 : (∑' n : ℤ, ‖g n‖) ≤ ∑' n : ℤ, h n :=
    hg_norm.tsum_le_tsum hgh hh_summable
  have hb3 : (∑' n : ℤ, h n) = ε / 4 * (∑' n : ℤ, K m n ^ 2)
      + 1 / ε * ∑' n : ℤ,
        (if n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then 0 else ‖u n‖ ^ 2) := by
    rw [hh, ((hKrow m).mul_left (ε / 4)).tsum_add (htail_summable.mul_left (1 / ε)),
      tsum_mul_left, tsum_mul_left]
  have hb4 : ε / 4 * (∑' n : ℤ, K m n ^ 2) ≤ ε / 4 * 1 :=
    mul_le_mul_of_nonneg_left (hKrow1 m) (by positivity)
  have hb5 : 1 / ε * (∑' n : ℤ,
      (if n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then 0 else ‖u n‖ ^ 2))
        ≤ 1 / ε * (ε ^ 2 / 4) :=
    mul_le_mul_of_nonneg_left (le_of_lt htail_lt) (by positivity)
  have hfinal : 1 / ε * (ε ^ 2 / 4) = ε / 4 := by field_simp
  calc ‖∑' n : ℤ, g n‖ ≤ ∑' n : ℤ, h n := hb1.trans hb2
    _ ≤ ε / 4 * 1 + ε / 4 := by rw [hb3]; rw [hfinal] at hb5; linarith
    _ < ε := by linarith

/-- **The contraction bound at the finset level**: for `ℓ²` input, every
finite piece of the output mass is dominated by the input mass.  Finite
isometry on the truncations plus a limit — no Fatou, no weak topology. -/
theorem sum_convK_sq_le
    (hKmul : ∀ n n' : ℤ, Summable fun m : ℤ => K m n * K m n')
    (hKorth : ∀ n n' : ℤ,
      ∑' m : ℤ, K m n * K m n' = if n = n' then (1 : ℝ) else 0)
    (hKrow : ∀ m : ℤ, Summable fun n : ℤ => K m n ^ 2)
    (hKrow1 : ∀ m : ℤ, (∑' n : ℤ, K m n ^ 2) ≤ 1)
    {u : ℤ → ℂ} (hu : Summable fun n : ℤ => ‖u n‖ ^ 2) (G : Finset ℤ) :
    (∑ m ∈ G, ‖convK K u m‖ ^ 2) ≤ ∑' n : ℤ, ‖u n‖ ^ 2 := by
  have hGlim : Tendsto (fun N : ℕ => ∑ m ∈ G, ‖convK K (trunc N u) m‖ ^ 2)
      atTop (𝓝 (∑ m ∈ G, ‖convK K u m‖ ^ 2)) :=
    tendsto_finsetSum G fun m _ =>
      ((tendsto_convK_trunc hKrow hKrow1 hu m).norm.pow 2)
  refine le_of_tendsto hGlim (Eventually.of_forall fun N => ?_)
  have hsq := summable_convK_sq_of_support hKmul (trunc_support N u)
  have h1 : (∑ m ∈ G, ‖convK K (trunc N u) m‖ ^ 2)
      ≤ ∑' m : ℤ, ‖convK K (trunc N u) m‖ ^ 2 :=
    hsq.sum_le_tsum G fun m _ => sq_nonneg _
  have h2 := finite_isometry hKmul hKorth (trunc_support N u)
  have h3 : (∑' n : ℤ, ‖trunc N u n‖ ^ 2) ≤ ∑' n : ℤ, ‖u n‖ ^ 2 :=
    (summable_trunc_sq N u).tsum_le_tsum (trunc_sq_le N u) hu
  linarith

/-- The output of the convolution of an `ℓ²` sequence is `ℓ²`. -/
theorem summable_convK_sq
    (hKmul : ∀ n n' : ℤ, Summable fun m : ℤ => K m n * K m n')
    (hKorth : ∀ n n' : ℤ,
      ∑' m : ℤ, K m n * K m n' = if n = n' then (1 : ℝ) else 0)
    (hKrow : ∀ m : ℤ, Summable fun n : ℤ => K m n ^ 2)
    (hKrow1 : ∀ m : ℤ, (∑' n : ℤ, K m n ^ 2) ≤ 1)
    {u : ℤ → ℂ} (hu : Summable fun n : ℤ => ‖u n‖ ^ 2) :
    Summable fun m : ℤ => ‖convK K u m‖ ^ 2 :=
  summable_of_sum_le (fun _ => sq_nonneg _)
    (sum_convK_sq_le hKmul hKorth hKrow hKrow1 hu)

/-- **The `ℓ²`-contraction**: `‖Ku‖₂² ≤ ‖u‖₂²`. -/
theorem tsum_convK_sq_le
    (hKmul : ∀ n n' : ℤ, Summable fun m : ℤ => K m n * K m n')
    (hKorth : ∀ n n' : ℤ,
      ∑' m : ℤ, K m n * K m n' = if n = n' then (1 : ℝ) else 0)
    (hKrow : ∀ m : ℤ, Summable fun n : ℤ => K m n ^ 2)
    (hKrow1 : ∀ m : ℤ, (∑' n : ℤ, K m n ^ 2) ≤ 1)
    {u : ℤ → ℂ} (hu : Summable fun n : ℤ => ‖u n‖ ^ 2) :
    (∑' m : ℤ, ‖convK K u m‖ ^ 2) ≤ ∑' n : ℤ, ‖u n‖ ^ 2 :=
  (summable_convK_sq hKmul hKorth hKrow hKrow1 hu).tsum_le_of_sum_le
    (sum_convK_sq_le hKmul hKorth hKrow hKrow1 hu)

/-! #### Adjoint continuity under `ℓ²`-convergence -/

/-- Linearity of `convK` in its argument (on `ℓ²` inputs). -/
lemma convK_sub (hKrow : ∀ m : ℤ, Summable fun n : ℤ => K m n ^ 2)
    {u v : ℤ → ℂ} (hu : Summable fun n : ℤ => ‖u n‖ ^ 2)
    (hv : Summable fun n : ℤ => ‖v n‖ ^ 2) (m : ℤ) :
    convK K (u - v) m = convK K u m - convK K v m := by
  rw [convK, convK, convK,
    ← (summable_convK_term hKrow hu m).tsum_sub (summable_convK_term hKrow hv m)]
  exact tsum_congr fun n => by simp only [Pi.sub_apply]; ring

/-- Additivity of `convK` in its argument (on `ℓ²` inputs). -/
lemma convK_add (hKrow : ∀ m : ℤ, Summable fun n : ℤ => K m n ^ 2)
    {u v : ℤ → ℂ} (hu : Summable fun n : ℤ => ‖u n‖ ^ 2)
    (hv : Summable fun n : ℤ => ‖v n‖ ^ 2) (m : ℤ) :
    convK K (u + v) m = convK K u m + convK K v m := by
  rw [convK, convK, convK,
    ← (summable_convK_term hKrow hu m).tsum_add (summable_convK_term hKrow hv m)]
  exact tsum_congr fun n => by simp only [Pi.add_apply]; ring

/-- `ℂ`-homogeneity of `convK` in its argument (no summability needed). -/
lemma convK_smul (c : ℂ) (u : ℤ → ℂ) (m : ℤ) :
    convK K (c • u) m = c • convK K u m := by
  simp only [convK, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by ring

/-- The pointwise Cauchy–Schwarz bound: `‖Kv(a)‖² ≤ ‖v‖₂²`. -/
lemma norm_convK_sq_le (hKrow : ∀ m : ℤ, Summable fun n : ℤ => K m n ^ 2)
    (hKrow1 : ∀ m : ℤ, (∑' n : ℤ, K m n ^ 2) ≤ 1)
    {v : ℤ → ℂ} (hv : Summable fun n : ℤ => ‖v n‖ ^ 2) (a : ℤ) :
    ‖convK K v a‖ ^ 2 ≤ ∑' n : ℤ, ‖v n‖ ^ 2 := by
  have hKsq : Summable fun n : ℤ => |K a n| ^ 2 :=
    (hKrow a).congr fun n => (sq_abs _).symm
  have hnorm_sum : Summable fun n : ℤ => ‖(K a n : ℂ) * v n‖ :=
    (summable_mul_of_sq hKsq hv).congr fun n => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hb1 : ‖convK K v a‖ ≤ ∑' n : ℤ, |K a n| * ‖v n‖ := by
    rw [convK]
    exact (norm_tsum_le_tsum_norm hnorm_sum).trans_eq
      (tsum_congr fun n => by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs])
  have hmass : (∑' n : ℤ, |K a n| ^ 2) ≤ 1 := by
    rw [show (∑' n : ℤ, |K a n| ^ 2) = ∑' n : ℤ, K a n ^ 2 from
      tsum_congr fun n => sq_abs _]
    exact hKrow1 a
  have hb1sq : ‖convK K v a‖ ^ 2 ≤ (∑' n : ℤ, |K a n| * ‖v n‖) ^ 2 := by
    have h0 : 0 ≤ ‖convK K v a‖ := norm_nonneg _
    have hs0 : 0 ≤ ∑' n : ℤ, |K a n| * ‖v n‖ :=
      tsum_nonneg fun n => mul_nonneg (abs_nonneg _) (norm_nonneg _)
    nlinarith [hb1, h0, hs0]
  calc ‖convK K v a‖ ^ 2 ≤ (∑' n : ℤ, |K a n| * ‖v n‖) ^ 2 := hb1sq
    _ ≤ (∑' n : ℤ, |K a n| ^ 2) * ∑' n : ℤ, ‖v n‖ ^ 2 := tsum_mul_sq_le hKsq hv
    _ ≤ 1 * ∑' n : ℤ, ‖v n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hmass (tsum_nonneg fun _ => sq_nonneg _)
    _ = ∑' n : ℤ, ‖v n‖ ^ 2 := one_mul _

/-- If a sequence of `ℓ²` inputs vanishes in `ℓ²`, the convolutions vanish
pointwise. -/
lemma tendsto_convK_of_tendsto_zero
    (hKrow : ∀ m : ℤ, Summable fun n : ℤ => K m n ^ 2)
    (hKrow1 : ∀ m : ℤ, (∑' n : ℤ, K m n ^ 2) ≤ 1)
    {w : ℕ → ℤ → ℂ} (hw : ∀ N, Summable fun n : ℤ => ‖w N n‖ ^ 2)
    (hlim : Tendsto (fun N => ∑' n : ℤ, ‖w N n‖ ^ 2) atTop (𝓝 0)) (a : ℤ) :
    Tendsto (fun N => convK K (w N) a) atTop (𝓝 0) := by
  have hsq : Tendsto (fun N => ‖convK K (w N) a‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun N => sq_nonneg _)
      (fun N => norm_convK_sq_le hKrow hKrow1 (hw N) a) hlim
  have hnorm : Tendsto (fun N => ‖convK K (w N) a‖) atTop (𝓝 0) := by
    have h := hsq.sqrt
    rw [Real.sqrt_zero] at h
    exact (tendsto_congr fun N => Real.sqrt_sq (norm_nonneg _)).mp h
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

end Kernel

/-! ### The full `ℓ²` isometry of `S = convS`

The forward kernel `Sker m n = ς̂(m-n)` reproduces `convS`; its adjoint
`Tker a n = ς̂(n-a)` is again a shifted kernel by `chat_refl`.  Both are
orthonormal, hence `ℓ²`-contractions; the finite-support inversion
`S̃ S = id` upgrades to `ℓ²` by truncation, and the two contractions pin
the isometry. -/

/-- The forward convolution kernel of `S`. -/
def Sker : ℤ → ℤ → ℝ := fun m n => chat (m - n)

/-- The adjoint kernel of `S`. -/
def Tker : ℤ → ℤ → ℝ := fun a n => chat (n - a)

@[simp] lemma convK_Sker (u : ℤ → ℂ) (m : ℤ) : convK Sker u m = convS u m := rfl

/-- Summability of a product of two reflected shifts. -/
lemma summable_chat_refl_mul (b b' : ℤ) :
    Summable fun m : ℤ => chat (b - m) * chat (b' - m) := by
  have hfun : (fun m : ℤ => chat (b - m) * chat (b' - m))
      = fun m : ℤ => chat (m - (b + 1)) * chat (m - (b' + 1)) := by
    funext m; rw [chat_refl_shift b m, chat_refl_shift b' m]
  rw [hfun]; exact summable_chat_shift_mul (b + 1) (b' + 1)

/-- Orthonormality of the reflected shifts. -/
lemma tsum_chat_refl_mul (b b' : ℤ) :
    ∑' m : ℤ, chat (b - m) * chat (b' - m) = if b = b' then (1 : ℝ) else 0 := by
  have hfun : (fun m : ℤ => chat (b - m) * chat (b' - m))
      = fun m : ℤ => chat (m - (b + 1)) * chat (m - (b' + 1)) := by
    funext m; rw [chat_refl_shift b m, chat_refl_shift b' m]
  rw [hfun, chat_orthonormal (b + 1) (b' + 1)]
  simp only [add_left_inj]

lemma Sker_mul (n n' : ℤ) : Summable fun m : ℤ => Sker m n * Sker m n' :=
  summable_chat_shift_mul n n'
lemma Sker_orth (n n' : ℤ) :
    ∑' m : ℤ, Sker m n * Sker m n' = if n = n' then (1 : ℝ) else 0 :=
  chat_orthonormal n n'
lemma Sker_row (m : ℤ) : Summable fun n : ℤ => Sker m n ^ 2 := summable_chat_shift_sq m
lemma Sker_row1 (m : ℤ) : (∑' n : ℤ, Sker m n ^ 2) ≤ 1 := le_of_eq (tsum_chat_snd_sq m)

lemma Tker_mul (b b' : ℤ) : Summable fun m : ℤ => Tker m b * Tker m b' :=
  summable_chat_refl_mul b b'
lemma Tker_orth (b b' : ℤ) :
    ∑' m : ℤ, Tker m b * Tker m b' = if b = b' then (1 : ℝ) else 0 :=
  tsum_chat_refl_mul b b'
lemma Tker_row (a : ℤ) : Summable fun n : ℤ => Tker a n ^ 2 := summable_chat_fst_sq a
lemma Tker_row1 (a : ℤ) : (∑' n : ℤ, Tker a n ^ 2) ≤ 1 := le_of_eq (tsum_chat_fst_sq a)

/-- `convS u` is `ℓ²` for `ℓ²` input. -/
lemma summable_convS_sq {u : ℤ → ℂ} (hu : Summable fun n : ℤ => ‖u n‖ ^ 2) :
    Summable fun m : ℤ => ‖convS u m‖ ^ 2 := by
  have h := summable_convK_sq Sker_mul Sker_orth Sker_row Sker_row1 hu
  exact h.congr fun m => by rw [convK_Sker]

/-- **Finite-support inversion** `S̃(S v) = v` for `v` of finite support. -/
theorem finite_inversion {v : ℤ → ℂ} {F : Finset ℤ} (hF : ∀ n ∉ F, v n = 0)
    (a : ℤ) : convK Tker (convK Sker v) a = v a := by
  have hinner : ∀ n : ℤ, convK Sker v n = ∑ m ∈ F, (chat (n - m) : ℂ) * v m := by
    intro n
    simp only [convK, Sker]
    exact tsum_eq_sum fun m hm => by rw [hF m hm, mul_zero]
  have hsummand : ∀ m ∈ F, Summable fun n : ℤ =>
      (chat (n - a) : ℂ) * ((chat (n - m) : ℂ) * v m) := by
    intro m _
    refine ((Complex.summable_ofReal.mpr (summable_chat_shift_mul a m)).mul_right
      (v m)).congr fun n => ?_
    push_cast; ring
  have hstep : convK Tker (convK Sker v) a
      = ∑' n : ℤ, ∑ m ∈ F, (chat (n - a) : ℂ) * ((chat (n - m) : ℂ) * v m) := by
    rw [convK]
    refine tsum_congr fun n => ?_
    simp only [Tker]
    rw [hinner n, Finset.mul_sum]
  rw [hstep, (summable_tsum_finset_sum F _ hsummand).2]
  have hval : ∀ m ∈ F,
      (∑' n : ℤ, (chat (n - a) : ℂ) * ((chat (n - m) : ℂ) * v m))
        = if a = m then v m else 0 := by
    intro m _
    have h1 : (fun n : ℤ => (chat (n - a) : ℂ) * ((chat (n - m) : ℂ) * v m))
        = fun n : ℤ => v m * ((chat (n - a) * chat (n - m) : ℝ) : ℂ) := by
      funext n; push_cast; ring
    rw [h1, tsum_mul_left, ← Complex.ofReal_tsum, chat_orthonormal a m,
      apply_ite (Complex.ofReal), Complex.ofReal_one, Complex.ofReal_zero,
      mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl hval, Finset.sum_ite_eq F a v]
  by_cases ha : a ∈ F
  · rw [if_pos ha]
  · rw [if_neg ha, hF a ha]

/-- **Finite-support inversion** `S(T v) = v` for `v` of finite support —
the mirror of `finite_inversion` with `Sker ↔ Tker` (reflected shifts in place
of shifts: `tsum_chat_refl_mul`/`summable_chat_refl_mul` for the orthonormality). -/
theorem finite_inversion_ST {v : ℤ → ℂ} {F : Finset ℤ} (hF : ∀ n ∉ F, v n = 0)
    (a : ℤ) : convK Sker (convK Tker v) a = v a := by
  have hinner : ∀ n : ℤ, convK Tker v n = ∑ m ∈ F, (chat (m - n) : ℂ) * v m := by
    intro n
    simp only [convK, Tker]
    exact tsum_eq_sum fun m hm => by rw [hF m hm, mul_zero]
  have hsummand : ∀ m ∈ F, Summable fun n : ℤ =>
      (chat (a - n) : ℂ) * ((chat (m - n) : ℂ) * v m) := by
    intro m _
    refine ((Complex.summable_ofReal.mpr (summable_chat_refl_mul a m)).mul_right
      (v m)).congr fun n => ?_
    push_cast; ring
  have hstep : convK Sker (convK Tker v) a
      = ∑' n : ℤ, ∑ m ∈ F, (chat (a - n) : ℂ) * ((chat (m - n) : ℂ) * v m) := by
    rw [convK]
    refine tsum_congr fun n => ?_
    simp only [Sker]
    rw [hinner n, Finset.mul_sum]
  rw [hstep, (summable_tsum_finset_sum F _ hsummand).2]
  have hval : ∀ m ∈ F,
      (∑' n : ℤ, (chat (a - n) : ℂ) * ((chat (m - n) : ℂ) * v m))
        = if a = m then v m else 0 := by
    intro m _
    have h1 : (fun n : ℤ => (chat (a - n) : ℂ) * ((chat (m - n) : ℂ) * v m))
        = fun n : ℤ => v m * ((chat (a - n) * chat (m - n) : ℝ) : ℂ) := by
      funext n; push_cast; ring
    rw [h1, tsum_mul_left, ← Complex.ofReal_tsum, tsum_chat_refl_mul a m,
      apply_ite (Complex.ofReal), Complex.ofReal_one, Complex.ofReal_zero,
      mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl hval, Finset.sum_ite_eq F a v]
  by_cases ha : a ∈ F
  · rw [if_pos ha]
  · rw [if_neg ha, hF a ha]

/-! #### `ℓ²`-tail limit -/

lemma tsum_ite_compl_eq {f : ℤ → ℝ} (hf : Summable f) (F : Finset ℤ) :
    (∑' n : ℤ, if n ∈ F then (0 : ℝ) else f n) = (∑' n : ℤ, f n) - ∑ n ∈ F, f n := by
  have hhead : (∑' n : ℤ, if n ∈ F then f n else 0) = ∑ n ∈ F, f n := by
    rw [tsum_eq_sum (s := F) fun n hn => if_neg hn]
    exact Finset.sum_congr rfl fun n hn => if_pos hn
  have hhead_sum : Summable fun n : ℤ => if n ∈ F then f n else 0 :=
    summable_of_ne_finset_zero (s := F) fun n hn => if_neg hn
  rw [← hhead, ← hf.tsum_sub hhead_sum]
  exact tsum_congr fun n => by split_ifs <;> ring

lemma tendsto_trunc_sub_sq {u : ℤ → ℂ} (hu : Summable fun n : ℤ => ‖u n‖ ^ 2) :
    Tendsto (fun N : ℕ => ∑' n : ℤ, ‖(trunc N u - u) n‖ ^ 2) atTop (𝓝 0) := by
  have hexh : Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) atTop atTop := by
    apply tendsto_atTop_finset_of_monotone
    · exact fun a b hab => Finset.Icc_subset_Icc (by omega) (by omega)
    · exact fun x => ⟨x.natAbs, by rw [Finset.mem_Icc]; omega⟩
  have hpart : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖u n‖ ^ 2) atTop
      (𝓝 (∑' n : ℤ, ‖u n‖ ^ 2)) := (hu.hasSum.comp hexh)
  have heq : ∀ N : ℕ, (∑' n : ℤ, ‖(trunc N u - u) n‖ ^ 2)
      = (∑' n : ℤ, ‖u n‖ ^ 2) - ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖u n‖ ^ 2 := by
    intro N
    have hpt : ∀ n : ℤ, ‖(trunc N u - u) n‖ ^ 2
        = if n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then (0 : ℝ) else ‖u n‖ ^ 2 := by
      intro n
      simp only [Pi.sub_apply, trunc]
      split_ifs with hn
      · simp
      · rw [zero_sub, norm_neg]
    rw [tsum_congr hpt, tsum_ite_compl_eq hu]
  rw [show (0 : ℝ) = (∑' n : ℤ, ‖u n‖ ^ 2) - (∑' n : ℤ, ‖u n‖ ^ 2) from by ring]
  exact (tendsto_congr heq).mpr (tendsto_const_nhds.sub hpart)

/-- **The inversion on `ℓ²`**: `S̃(S u) = u` pointwise for `ℓ²` `u`. -/
theorem convK_TS_eq {u : ℤ → ℂ} (hu : Summable fun n : ℤ => ‖u n‖ ^ 2) (a : ℤ) :
    convK Tker (convK Sker u) a = u a := by
  set w' : ℕ → ℤ → ℂ := fun N => trunc N u - u with hw'
  -- each `w' N` is `ℓ²`, with vanishing `ℓ²` mass
  have hw'sq : ∀ N, Summable fun n : ℤ => ‖w' N n‖ ^ 2 := by
    intro N
    refine hu.of_nonneg_of_le (fun n => sq_nonneg _) fun n => ?_
    simp only [hw', Pi.sub_apply, trunc]
    split_ifs with hn
    · simp
    · rw [zero_sub, norm_neg]
  -- the `S`-image of `w' N`
  have hSw'sq : ∀ N, Summable fun m : ℤ => ‖convK Sker (w' N) m‖ ^ 2 := fun N =>
    summable_convK_sq Sker_mul Sker_orth Sker_row Sker_row1 (hw'sq N)
  have hbound : ∀ N, (∑' m : ℤ, ‖convK Sker (w' N) m‖ ^ 2) ≤ ∑' n : ℤ, ‖w' N n‖ ^ 2 :=
    fun N => tsum_convK_sq_le Sker_mul Sker_orth Sker_row Sker_row1 (hw'sq N)
  have hSlim : Tendsto (fun N => ∑' m : ℤ, ‖convK Sker (w' N) m‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun N => tsum_nonneg fun _ => sq_nonneg _) hbound
      (tendsto_trunc_sub_sq hu)
  -- adjoint continuity: `S̃(S(w' N)) a → 0`
  have hTlim : Tendsto (fun N => convK Tker (convK Sker (w' N)) a) atTop (𝓝 0) :=
    tendsto_convK_of_tendsto_zero Tker_row Tker_row1 hSw'sq hSlim a
  -- rewrite that as the difference of the two compositions
  have husq : Summable fun m : ℤ => ‖convK Sker u m‖ ^ 2 :=
    summable_convK_sq Sker_mul Sker_orth Sker_row Sker_row1 hu
  have htruncsq : ∀ N, Summable fun m : ℤ => ‖convK Sker (trunc N u) m‖ ^ 2 := fun N =>
    summable_convK_sq Sker_mul Sker_orth Sker_row Sker_row1 (summable_trunc_sq N u)
  have hsplit : ∀ N, convK Tker (convK Sker (w' N)) a
      = convK Tker (convK Sker (trunc N u)) a - convK Tker (convK Sker u) a := by
    intro N
    have hfun : convK Sker (w' N)
        = convK Sker (trunc N u) - convK Sker u := by
      funext m
      rw [hw', convK_sub Sker_row (summable_trunc_sq N u) hu m, Pi.sub_apply]
    rw [hfun, convK_sub Tker_row (htruncsq N) husq a]
  -- so the shifted compositions converge to `S̃(S u) a`
  have hconv : Tendsto (fun N => convK Tker (convK Sker (trunc N u)) a) atTop
      (𝓝 (convK Tker (convK Sker u) a)) := by
    have := hTlim
    simp only [hsplit] at this
    have h2 := this.add_const (convK Tker (convK Sker u) a)
    simpa using h2
  -- but that sequence is eventually `u a` (finite-support inversion)
  have heventually : Tendsto (fun N : ℕ => convK Tker (convK Sker (trunc N u)) a) atTop
      (𝓝 (u a)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop a.natAbs] with N hN
    rw [finite_inversion (trunc_support N u) a]
    simp only [trunc]
    rw [if_pos (by rw [Finset.mem_Icc]; omega)]
  exact tendsto_nhds_unique hconv heventually

/-- **The inversion on `ℓ²`**: `S(T u) = u` pointwise for `ℓ²` `u` — the
counterpart of `convK_TS_eq` with `Sker` and `Tker` exchanged. Together
they give `T∘S = id` and `S∘T = id` on the two coefficient spaces.
This direction uses orthonormality of the reflected kernel columns,
finite-support inversion, and convergence of the truncated inputs. -/
theorem convK_ST_eq {u : ℤ → ℂ} (hu : Summable fun n : ℤ => ‖u n‖ ^ 2) (a : ℤ) :
    convK Sker (convK Tker u) a = u a := by
  set w' : ℕ → ℤ → ℂ := fun N => trunc N u - u with hw'
  have hw'sq : ∀ N, Summable fun n : ℤ => ‖w' N n‖ ^ 2 := by
    intro N
    refine hu.of_nonneg_of_le (fun n => sq_nonneg _) fun n => ?_
    simp only [hw', Pi.sub_apply, trunc]
    split_ifs with hn
    · simp
    · rw [zero_sub, norm_neg]
  have hTw'sq : ∀ N, Summable fun m : ℤ => ‖convK Tker (w' N) m‖ ^ 2 := fun N =>
    summable_convK_sq Tker_mul Tker_orth Tker_row Tker_row1 (hw'sq N)
  have hbound : ∀ N, (∑' m : ℤ, ‖convK Tker (w' N) m‖ ^ 2) ≤ ∑' n : ℤ, ‖w' N n‖ ^ 2 :=
    fun N => tsum_convK_sq_le Tker_mul Tker_orth Tker_row Tker_row1 (hw'sq N)
  have hTlim : Tendsto (fun N => ∑' m : ℤ, ‖convK Tker (w' N) m‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun N => tsum_nonneg fun _ => sq_nonneg _) hbound
      (tendsto_trunc_sub_sq hu)
  have hSlim : Tendsto (fun N => convK Sker (convK Tker (w' N)) a) atTop (𝓝 0) :=
    tendsto_convK_of_tendsto_zero Sker_row Sker_row1 hTw'sq hTlim a
  have husq : Summable fun m : ℤ => ‖convK Tker u m‖ ^ 2 :=
    summable_convK_sq Tker_mul Tker_orth Tker_row Tker_row1 hu
  have htruncsq : ∀ N, Summable fun m : ℤ => ‖convK Tker (trunc N u) m‖ ^ 2 := fun N =>
    summable_convK_sq Tker_mul Tker_orth Tker_row Tker_row1 (summable_trunc_sq N u)
  have hsplit : ∀ N, convK Sker (convK Tker (w' N)) a
      = convK Sker (convK Tker (trunc N u)) a - convK Sker (convK Tker u) a := by
    intro N
    have hfun : convK Tker (w' N)
        = convK Tker (trunc N u) - convK Tker u := by
      funext m
      rw [hw', convK_sub Tker_row (summable_trunc_sq N u) hu m, Pi.sub_apply]
    rw [hfun, convK_sub Sker_row (htruncsq N) husq a]
  have hconv : Tendsto (fun N => convK Sker (convK Tker (trunc N u)) a) atTop
      (𝓝 (convK Sker (convK Tker u) a)) := by
    have := hSlim
    simp only [hsplit] at this
    have h2 := this.add_const (convK Sker (convK Tker u) a)
    simpa using h2
  have heventually : Tendsto (fun N : ℕ => convK Sker (convK Tker (trunc N u)) a) atTop
      (𝓝 (u a)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop a.natAbs] with N hN
    rw [finite_inversion_ST (trunc_support N u) a]
    simp only [trunc]
    rw [if_pos (by rw [Finset.mem_Icc]; omega)]
  exact tendsto_nhds_unique hconv heventually

/-- For every square-summable complex sequence, `convS` preserves the
sum of squared norms. -/
theorem tsum_convS_sq {u : ℤ → ℂ} (hu : Summable fun n : ℤ => ‖u n‖ ^ 2) :
    ∑' m : ℤ, ‖convS u m‖ ^ 2 = ∑' n : ℤ, ‖u n‖ ^ 2 := by
  have hle : (∑' m : ℤ, ‖convS u m‖ ^ 2) ≤ ∑' n : ℤ, ‖u n‖ ^ 2 := by
    have h := tsum_convK_sq_le Sker_mul Sker_orth Sker_row Sker_row1 hu
    simpa only [convK_Sker] using h
  have husq : Summable fun m : ℤ => ‖convK Sker u m‖ ^ 2 :=
    summable_convK_sq Sker_mul Sker_orth Sker_row Sker_row1 hu
  have hge : (∑' n : ℤ, ‖u n‖ ^ 2) ≤ ∑' m : ℤ, ‖convS u m‖ ^ 2 := by
    calc (∑' n : ℤ, ‖u n‖ ^ 2)
        = ∑' n : ℤ, ‖convK Tker (convK Sker u) n‖ ^ 2 :=
          tsum_congr fun n => by rw [convK_TS_eq hu n]
      _ ≤ ∑' m : ℤ, ‖convK Sker u m‖ ^ 2 :=
          tsum_convK_sq_le Tker_mul Tker_orth Tker_row Tker_row1 husq
      _ = ∑' m : ℤ, ‖convS u m‖ ^ 2 := by simp only [convK_Sker]
  exact le_antisymm hle hge

/-- The isometry in the paper's notation: `∑ ‖ς·u‖² = ‖u‖²`. -/
theorem tsum_convS_sq_eq_normSq {u : ℤ → ℂ} (hu : MemDom u) :
    ∑' m : ℤ, ‖convS u m‖ ^ 2 = normSq u :=
  tsum_convS_sq (summable_normSq hu.1)

end KsIndex.SIsometry
