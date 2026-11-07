module
public import Mathlib.Data.List.Basic
@[expose] public section
namespace KsIndex.LookupTreePilot
inductive Tree : Nat → Type
  | leaf : Int → Tree 0
  | node {h : Nat} : Tree h → Tree h → Tree (h+1)
def flatten : {h : Nat} → Tree h → List Int
  | _, .leaf a => [a]
  | _, .node l r => flatten l ++ flatten r
def lookup : {h : Nat} → Tree h → Nat → Int
  | _, .leaf a, n => if n = 0 then a else 0
  | h+1, .node l r, n => if n < 2^h then lookup l n else lookup r (n-2^h)
lemma flatten_length {h : Nat} (t : Tree h) : (flatten t).length = 2^h := by
  induction t with
  | leaf a => simp [flatten]
  | node l r hl hr => simp [flatten, hl, hr, Nat.pow_succ, Nat.mul_two]
/-- Every index, including those outside the tree, has the original list default-zero meaning. -/
theorem lookup_eq {h : Nat} (t : Tree h) (n : Nat) :
    lookup t n = ((flatten t)[n]?).getD 0 := by
  induction t generalizing n with
  | leaf a => cases n <;> simp [lookup, flatten]
  | node l r hl hr =>
    simp only [lookup, flatten, List.getElem?_append, flatten_length]
    split <;> simp_all
#print axioms lookup_eq
end KsIndex.LookupTreePilot
