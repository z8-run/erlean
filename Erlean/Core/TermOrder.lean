import Erlean.Core.FiniteMap

/-!
# Erlang term order on supported map keys

`MapKey.before` is an internal canonical storage order. It is *not* Erlang's
observable term order: for example it places every negative integer after every
nonnegative integer, and it orders the key kinds differently. Operations whose
result order is specified by OTP, such as `maps:iterator(Map, ordered)`, must use
the relation below instead.

The comparison follows OTP's standard term order restricted to the key kinds of
the map profile:

`number < atom < reference < pid < tuple < nil < list < bitstring`

- integers compare numerically;
- atoms compare by their Unicode code points (equivalently by UTF-8 bytes);
- references and pids compare by their model identities;
- tuples compare by size first, then element by element;
- nonempty lists compare their heads, then their tails as terms, which also
  orders improper lists as OTP does;
- bitstrings compare bit by bit, with a proper prefix ordered first.
-/

namespace Erlean.Core.MapKey

/-- Kind rank in Erlang's standard term order. -/
def termRank : MapKey → Nat
  | .integer _ => 0
  | .atom _ => 1
  | .reference _ => 2
  | .pid _ => 3
  | .tuple _ => 4
  | .nil => 5
  | .cons _ _ => 6
  | .bitstring _ => 7

/-- Lexicographic comparison with a proper prefix ordered first. -/
def compareLex {α : Type} (cmp : α → α → Ordering) : List α → List α → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys =>
    match cmp x y with
    | .eq => compareLex cmp xs ys
    | result => result

mutual
/-- Erlang's standard term order restricted to supported map keys. -/
def termCompare (left right : MapKey) : Ordering :=
  match left, right with
  | .integer a, .integer b => Ord.compare a b
  | .atom a, .atom b =>
    compareLex (fun x y : Nat => Ord.compare x y) (a.toList.map Char.toNat) (b.toList.map Char.toNat)
  | .reference a, .reference b => Ord.compare a b
  | .pid a, .pid b => Ord.compare a b
  | .tuple xs, .tuple ys =>
    match Ord.compare xs.length ys.length with
    | .eq => termCompareList xs ys
    | result => result
  | .nil, .nil => .eq
  | .cons a b, .cons c d =>
    match termCompare a c with
    | .eq => termCompare b d
    | result => result
  | .bitstring a, .bitstring b =>
    compareLex (fun x y : Bool => Ord.compare (if x then 1 else 0 : Nat) (if y then 1 else 0)) a b
  | _, _ => Ord.compare (termRank left) (termRank right)
termination_by sizeOf left

/-- Element-wise comparison of equally sized tuple contents. -/
def termCompareList (left right : List MapKey) : Ordering :=
  match left, right with
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys =>
    match termCompare x y with
    | .eq => termCompareList xs ys
    | result => result
termination_by sizeOf left
end

/-- Strict Erlang term order on supported map keys. -/
def termBefore (left right : MapKey) : Bool := termCompare left right == .lt

end Erlean.Core.MapKey

namespace Erlean.Core.FiniteMap

/-- Insert one entry into a list already sorted by Erlang term order. -/
def insertByTermOrder {α : Type} (entry : MapKey × α) : Entries α → Entries α
  | [] => [entry]
  | head :: rest =>
    if MapKey.termBefore head.1 entry.1 then head :: insertByTermOrder entry rest
    else entry :: head :: rest

/-- Entries arranged in ascending Erlang term order of their keys. This is the
    order that OTP specifies for `maps:iterator(Map, ordered)`, and the order in
    which OTP stores (and therefore lists) the keys of small maps. -/
def termOrdered {α : Type} (entries : Entries α) : Entries α :=
  entries.foldr insertByTermOrder []

end Erlean.Core.FiniteMap

namespace Erlean.Core.MapKey

theorem compareLex_self {α : Type} (cmp : α → α → Ordering) (refl : ∀ x, cmp x x = .eq) :
    ∀ xs : List α, compareLex cmp xs xs = .eq
  | [] => rfl
  | x :: xs => by simp [compareLex, refl x, compareLex_self cmp refl xs]

mutual
/-- Every supported key is term-order equal to itself. -/
theorem termCompare_self (key : MapKey) : termCompare key key = .eq := by
  match key with
  | .integer a => simp [termCompare]
  | .atom a => simp [termCompare, compareLex_self _ (fun _ => Nat.compare_eq_eq.mpr rfl)]
  | .reference a => simp [termCompare]
  | .pid a => simp [termCompare]
  | .tuple xs => simp [termCompare, termCompareList_self xs]
  | .nil => simp [termCompare]
  | .cons a b => simp [termCompare, termCompare_self a, termCompare_self b]
  | .bitstring a =>
    simp only [termCompare]
    exact compareLex_self (α := Bool) _ (fun _ => Nat.compare_eq_eq.mpr rfl) a
termination_by sizeOf key

theorem termCompareList_self (keys : List MapKey) : termCompareList keys keys = .eq := by
  match keys with
  | [] => simp [termCompareList]
  | x :: xs => simp [termCompareList, termCompare_self x, termCompareList_self xs]
termination_by sizeOf keys
end

end Erlean.Core.MapKey

namespace Erlean.Core.FiniteMap

theorem insertByTermOrder_length {α : Type} (entry : MapKey × α) (entries : Entries α) :
    (insertByTermOrder entry entries).length = entries.length + 1 := by
  induction entries with
  | nil => rfl
  | cons head rest ih =>
    unfold insertByTermOrder
    split <;> simp [ih]

/-- Term-order sorting neither drops nor duplicates entries. -/
theorem termOrdered_length {α : Type} (entries : Entries α) :
    (termOrdered entries).length = entries.length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih => simp [termOrdered, insertByTermOrder_length] at ih ⊢; exact ih

end Erlean.Core.FiniteMap
