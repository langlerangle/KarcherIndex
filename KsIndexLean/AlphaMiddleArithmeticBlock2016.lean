module

public import KsIndexLean.AlphaSignedWindowBudget

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.MiddleBlock2016
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
def entries : Array (ℤ × ℤ × ℤ) := #[
  (-35551393, -33734197, 208324),
  (23051527, 24868143, 101967),
  (33700589, 35516853, 207714),
  (-24849387, -23033702, 101712),
  (-35482381, -33667047, 207107),
  (23015905, 24830661, 101459),
  (33633571, 35447976, 206502),
  (-24811964, -22998135, 101206),
  (-35413639, -33600161, 205899),
  (22980393, 24793295, 100954),
  (33566817, 35379369, 205298),
  (-24774656, -22962679, 100703),
  (-35345166, -33533538, 204700),
  (22944992, 24756045, 100453),
  (33500325, 35311030, 204104),
  (-24737464, -22927332, 100204),
  (-35276960, -33467176, 203511),
  (22909700, 24718911, 99955),
  (33434093, 35242957, 202919),
  (-24700387, -22892095, 99708),
  (-35209020, -33401075, 202330),
  (22874517, 24681891, 99461),
  (33368121, 35175148, 201744),
  (-24663424, -22856967, 99215),
  (-35141343, -33335232, 201159),
  (22839444, 24644985, 98970),
  (33302407, 35107603, 200577),
  (-24626575, -22821947, 98726),
  (-35073929, -33269646, 199997),
  (22804478, 24608194, 98482)
]
def mode (i : Fin 30) : ℤ :=
  let j := 2016+i.val
  if j % 2 = 0 then (j/2+3 : ℕ) else -((j/2+3 : ℕ) : ℤ)
def row (i : Fin 30) : ℤ × ℤ × ℤ := entries[i.val]?.getD (0,0,0)
def lo (i : Fin 30) : ℚ := (row i).1 / 1000000000000
def hi (i : Fin 30) : ℚ := (row i).2.1 / 1000000000000
def energy (i : Fin 30) : ℚ := (row i).2.2 / 1000000000000000000
theorem arithmetic : ∀ i : Fin 30, lo i ≤ hi i ∧
  signedIntervalRadius (lo i) (hi i)^2 / residualWeightRat (mode i) ≤ energy i := by
  decide +kernel
theorem total : (∑ i : Fin 30, energy i) = (4565060/1000000000000000000 : ℚ) := by
  decide +kernel
#print axioms arithmetic
#print axioms total
end KsIndex.AlphaRemarkTrial.MiddleBlock2016
