module

public import Mathlib

@[expose] public section


noncomputable section
open scoped BigOperators
namespace KsIndex.AlphaMatrixPacket

def mode (i : Fin 4) : ℤ := (i.val : ℤ) - 2

def sigP (n : ℤ) : ℝ := |6 * (n : ℝ) + 1| - 4 / |6 * (n : ℝ) + 1|

def kernel (i : Fin 4) (n : ℤ) : ℝ :=
  (-1 : ℝ) ^ (mode i - n) / (2 * ((mode i - n : ℤ) : ℝ) + 1)

def gram (i j : Fin 4) : ℝ :=
  ∑ n ∈ Finset.Icc (-64 : ℤ) 64,
    kernel i n * kernel j n / (sigP n + 2187 / 100)

def rounded : Fin 4 → Fin 4 → ℝ :=
![
  ![(82845571 / 1000000000 : ℝ), (566577 / 200000000 : ℝ), (-2379719 / 200000000 : ℝ), (8020801 /
    1000000000 : ℝ)],
  ![(566577 / 200000000 : ℝ), (103478601 / 1000000000 : ℝ), (1310269 / 62500000 : ℝ), (-10614759 /
    1000000000 : ℝ)],
  ![(-2379719 / 200000000 : ℝ), (1310269 / 62500000 : ℝ), (100623941 / 1000000000 : ℝ), (265213 /
    1000000000 : ℝ)],
  ![(8020801 / 1000000000 : ℝ), (-10614759 / 1000000000 : ℝ), (265213 / 1000000000 : ℝ), (77973481
    / 1000000000 : ℝ)]
]

def deficit : Fin 4 → ℝ := ![9/2, 12, 9, 12/5]

def certificate (i j : Fin 4) : ℝ :=
  (if i = j then 1 / ((729/400 : ℝ) * deficit i) else 0) -
    (10000/24649 : ℝ) * (rounded i j +
      if i = j then (1/23000 : ℝ) + 4/1000000000 else 0)


/-! ### Exact rational mirror of the Gram matrix -/

/-- Rational version of `kernel`. -/
def kernelQ (i : Fin 4) (n : ℤ) : ℚ :=
  (-1 : ℚ) ^ (mode i - n) / (2 * ((mode i - n : ℤ) : ℚ) + 1)

/-- Rational version of `sigP`. -/
def sigPQ (n : ℤ) : ℚ := |6 * (n : ℚ) + 1| - 4 / |6 * (n : ℚ) + 1|

/-- Rational version of `gram`. -/
def gramQ (i j : Fin 4) : ℚ :=
  ∑ n ∈ Finset.Icc (-64 : ℤ) 64,
    kernelQ i n * kernelQ j n / (sigPQ n + 2187 / 100)

/-- Rational version of `rounded`. -/
def roundedQ : Fin 4 → Fin 4 → ℚ :=
![
  ![(82845571 / 1000000000 : ℚ), (566577 / 200000000 : ℚ), (-2379719 / 200000000 : ℚ), (8020801 /
    1000000000 : ℚ)],
  ![(566577 / 200000000 : ℚ), (103478601 / 1000000000 : ℚ), (1310269 / 62500000 : ℚ), (-10614759 /
    1000000000 : ℚ)],
  ![(-2379719 / 200000000 : ℚ), (1310269 / 62500000 : ℚ), (100623941 / 1000000000 : ℚ), (265213 /
    1000000000 : ℚ)],
  ![(8020801 / 1000000000 : ℚ), (-10614759 / 1000000000 : ℚ), (265213 / 1000000000 : ℚ), (77973481
    / 1000000000 : ℚ)]
]

lemma gram_eq_cast (i j : Fin 4) : gram i j = ((gramQ i j : ℚ) : ℝ) := by
  simp [gram, gramQ, kernel, kernelQ, sigP, sigPQ]

lemma rounded_eq_cast (i j : Fin 4) : rounded i j = ((roundedQ i j : ℚ) : ℝ) := by
  fin_cases i <;> fin_cases j <;> norm_num [rounded, roundedQ]

/-- The exact rational check of all sixteen entries, by kernel evaluation
(`decide +kernel`, no `native_decide`). -/
lemma gramQ_enclosure : ∀ i j : Fin 4, |gramQ i j - roundedQ i j| ≤ (1/1000000000 : ℚ) := by
  decide +kernel

/-- The sixteen finite Gram entries have the specified rational enclosures. -/
theorem gram_entry_enclosure (i j : Fin 4) :
    |gram i j - rounded i j| ≤ (1/1000000000 : ℝ) := by
  rw [gram_eq_cast, rounded_eq_cast]
  have h : ((|gramQ i j - roundedQ i j| : ℚ) : ℝ) ≤ ((1/1000000000 : ℚ) : ℝ) :=
    Rat.cast_le.mpr (gramQ_enclosure i j)
  push_cast at h
  exact h

/-- A uniform positive margin for the real symmetric certificate matrix. -/
theorem certificate_margin (x : Fin 4 → ℝ) :
    (1/50000 : ℝ) * (∑ i, (x i)^2) ≤
      ∑ i, ∑ j, x i * certificate i j * x j := by
  have hSOS : 0 ≤
      (32838513979681/371960804700000 : ℝ) * ((1 : ℝ) * x 0 + (-427490845155/32838513979681 : ℝ) *
        x 1 + (1795533681285/32838513979681 : ℝ) * x 2 + (-1210362933303/32838513979681 : ℝ) * x
        3)^2 +
      (7514616615755890696651741/2035773347505724034883450000 : ℝ) * ((1 : ℝ) * x 1 +
        (-34373190842191980640139499/15029233231511781393303482 : ℝ) * x 2 +
        (8680546506321893331829962/7514616615755890696651741 : ℝ) * x 3)^2 +
      (2983721245837479582347531084839675609/5590285686817103604583650356031965400000 : ℝ) * ((1 :
        ℝ) * x 2 + (54910482425013514203102636965366727300/2983721245837479582347531084839675609 :
        ℝ) * x 3)^2 +
(2060646521096768003549950711394001867074234861417 /
        184971225933699238478301262895871618335100427050000
        : ℝ) * ((1 : ℝ) * x 3)^2 := by
    positivity
  simp [Fin.sum_univ_four, certificate, rounded, deficit]
  norm_num
  linarith [hSOS]

end KsIndex.AlphaMatrixPacket
