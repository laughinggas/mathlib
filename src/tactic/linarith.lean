/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/
import tactic.ring
import data.tree

/-!
# `linarith`

A tactic for discharging linear arithmetic goals using Fourier-Motzkin elimination.

`linarith` is (in principle) complete for ℚ and ℝ. It is not complete for non-dense orders, i.e. ℤ.

- @TODO: investigate storing comparisons in a list instead of a set, for possible efficiency gains
- @TODO: delay proofs of denominator normalization and nat casting until after contradiction is
  found
-/

meta def nat.to_pexpr : ℕ → pexpr
| 0 := ``(0)
| 1 := ``(1)
| n := if n % 2 = 0 then ``(bit0 %%(nat.to_pexpr (n/2))) else ``(bit1 %%(nat.to_pexpr (n/2)))


open native

namespace linarith

section lemmas

lemma int.coe_nat_bit0 (n : ℕ) : (↑(bit0 n : ℕ) : ℤ) = bit0 (↑n : ℤ) := by simp [bit0]
lemma int.coe_nat_bit1 (n : ℕ) : (↑(bit1 n : ℕ) : ℤ) = bit1 (↑n : ℤ) := by simp [bit1, bit0]
lemma int.coe_nat_bit0_mul (n : ℕ) (x : ℕ) : (↑(bit0 n * x) : ℤ) = (↑(bit0 n) : ℤ) * (↑x : ℤ) := by simp
lemma int.coe_nat_bit1_mul (n : ℕ) (x : ℕ) : (↑(bit1 n * x) : ℤ) = (↑(bit1 n) : ℤ) * (↑x : ℤ) := by simp
lemma int.coe_nat_one_mul (x : ℕ) : (↑(1 * x) : ℤ) = 1 * (↑x : ℤ) := by simp
lemma int.coe_nat_zero_mul (x : ℕ) : (↑(0 * x) : ℤ) = 0 * (↑x : ℤ) := by simp
lemma int.coe_nat_mul_bit0 (n : ℕ) (x : ℕ) : (↑(x * bit0 n) : ℤ) = (↑x : ℤ) * (↑(bit0 n) : ℤ) := by simp
lemma int.coe_nat_mul_bit1 (n : ℕ) (x : ℕ) : (↑(x * bit1 n) : ℤ) = (↑x : ℤ) * (↑(bit1 n) : ℤ) := by simp
lemma int.coe_nat_mul_one (x : ℕ) : (↑(x * 1) : ℤ) = (↑x : ℤ) * 1 := by simp
lemma int.coe_nat_mul_zero (x : ℕ) : (↑(x * 0) : ℤ) = (↑x : ℤ) * 0 := by simp

lemma nat_eq_subst {n1 n2 : ℕ} {z1 z2 : ℤ} (hn : n1 = n2) (h1 : ↑n1 = z1) (h2 : ↑n2 = z2) : z1 = z2 :=
by simpa [eq.symm h1, eq.symm h2, int.coe_nat_eq_coe_nat_iff]

lemma nat_le_subst {n1 n2 : ℕ} {z1 z2 : ℤ} (hn : n1 ≤ n2) (h1 : ↑n1 = z1) (h2 : ↑n2 = z2) : z1 ≤ z2 :=
by simpa [eq.symm h1, eq.symm h2, int.coe_nat_le]

lemma nat_lt_subst {n1 n2 : ℕ} {z1 z2 : ℤ} (hn : n1 < n2) (h1 : ↑n1 = z1) (h2 : ↑n2 = z2) : z1 < z2 :=
by simpa [eq.symm h1, eq.symm h2, int.coe_nat_lt]

lemma eq_of_eq_of_eq {α} [ordered_semiring α] {a b : α} (ha : a = 0) (hb : b = 0) : a + b = 0 :=
by simp *

lemma le_of_eq_of_le {α} [ordered_semiring α] {a b : α} (ha : a = 0) (hb : b ≤ 0) : a + b ≤ 0 :=
by simp *

lemma lt_of_eq_of_lt {α} [ordered_semiring α] {a b : α} (ha : a = 0) (hb : b < 0) : a + b < 0 :=
by simp *

lemma le_of_le_of_eq {α} [ordered_semiring α] {a b : α} (ha : a ≤ 0) (hb : b = 0) : a + b ≤ 0 :=
by simp *

lemma lt_of_lt_of_eq {α} [ordered_semiring α] {a b : α} (ha : a < 0) (hb : b = 0) : a + b < 0 :=
by simp *

lemma mul_neg {α} [ordered_ring α] {a b : α} (ha : a < 0) (hb : b > 0) : b * a < 0 :=
have (-b)*a > 0, from mul_pos_of_neg_of_neg (neg_neg_of_pos hb) ha,
neg_of_neg_pos (by simpa)

lemma mul_nonpos {α} [ordered_ring α] {a b : α} (ha : a ≤ 0) (hb : b > 0) : b * a ≤ 0 :=
have (-b)*a ≥ 0, from mul_nonneg_of_nonpos_of_nonpos (le_of_lt (neg_neg_of_pos hb)) ha,
(by simpa)

lemma mul_eq {α} [ordered_semiring α] {a b : α} (ha : a = 0) (hb : b > 0) : b * a = 0 :=
by simp *

lemma eq_of_not_lt_of_not_gt {α} [linear_order α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b :=
le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)

lemma add_subst {α} [ring α] {n e1 e2 t1 t2 : α} (h1 : n * e1 = t1) (h2 : n * e2 = t2) :
      n * (e1 + e2) = t1 + t2 := by simp [left_distrib, *]

lemma sub_subst {α} [ring α] {n e1 e2 t1 t2 : α} (h1 : n * e1 = t1) (h2 : n * e2 = t2) :
      n * (e1 - e2) = t1 - t2 := by simp [left_distrib, *, sub_eq_add_neg]

lemma neg_subst {α} [ring α] {n e t : α} (h1 : n * e = t) : n * (-e) = -t := by simp *

private meta def apnn : tactic unit := `[norm_num]

lemma mul_subst {α} [comm_ring α] {n1 n2 k e1 e2 t1 t2 : α} (h1 : n1 * e1 = t1) (h2 : n2 * e2 = t2)
     (h3 : n1*n2 = k . apnn) : k * (e1 * e2) = t1 * t2 :=
have h3 : n1 * n2 = k, from h3,
by rw [←h3, mul_comm n1, mul_assoc n2, ←mul_assoc n1, h1, ←mul_assoc n2, mul_comm n2, mul_assoc, h2] -- OUCH

lemma div_subst {α} [field α] {n1 n2 k e1 e2 t1 : α} (h1 : n1 * e1 = t1) (h2 : n2 / e2 = 1) (h3 : n1*n2 = k) :
      k * (e1 / e2) = t1 :=
by rw [←h3, mul_assoc, mul_div_comm, h2, ←mul_assoc, h1, mul_comm, one_mul]

end lemmas

/--
A linear expression is a list of pairs of variable indices and coefficients.

Some functions on `linexp` assume that `n : ℕ` occurs at most once as the first element of a pair,
and that the list is sorted in decreasing order of the first argument.
This is not enforced by the type but the operations here preserve it.
-/
@[reducible]
def linexp : Type := list (ℕ × ℤ)
end linarith

/--
A map `ℕ → ℤ` is converted to `list (ℕ × ℤ)` in the obvious way.
This list is sorted in decreasing order of the first argument.
-/
meta def native.rb_map.to_linexp (m : rb_map ℕ ℤ) : linarith.linexp :=
m.to_list

namespace linarith
namespace linexp

/--
Add two `linexp`s together componentwise.
Preserves sorting and uniqueness of the first argument.
-/
meta def add : linexp → linexp → linexp
| [] a := a
| a [] := a
| (a@(n1,z1)::t1) (b@(n2,z2)::t2) :=
  if n1 < n2 then b::add (a::t1) t2
  else if n2 < n1 then a::add t1 (b::t2)
  else let sum := z1 + z2 in if sum = 0 then add t1 t2 else (n1, sum)::add t1 t2

/-- `l.scale c` scales the values in `l` by `c` without modifying the order or keys. -/
def scale (c : ℤ) (l : linexp) : linexp :=
if c = 0 then []
else if c = 1 then l
else l.map $ λ ⟨n, z⟩, (n, z*c)

/--
`l.get n` returns the value in `l` associated with key `n`, if it exists, and `none` otherwise.
This function assumes that `l` is sorted in decreasing order of the first argument,
that is, it will return `none` as soon as it finds a key smaller than `n`.
-/
def get (n : ℕ) : linexp → option ℤ
| [] := none
| ((a, b)::t) :=
  if a < n then none
  else if a = n then some b
  else get t

/--
`l.contains n` is true iff `n` is the first element of a pair in `l`.
-/
def contains (n : ℕ) : linexp → bool := option.is_some ∘ get n

/--
`l.zfind n` returns the value associated with key `n` if there is one, and 0 otherwise.
-/
def zfind (n : ℕ) (l : linexp) : ℤ :=
match l.get n with
| none := 0
| some v := v
end

/--
Defines a lex ordering on `linexp`. This function is performance critical.
-/
def cmp : linexp → linexp → ordering
| [] [] := ordering.eq
| [] _ := ordering.lt
| _ [] := ordering.gt
| ((n1,z1)::t1) ((n2,z2)::t2) :=
  if n1 < n2 then ordering.lt
  else if n2 < n1 then ordering.gt
  else if z1 < z2 then ordering.lt
  else if z2 < z1 then ordering.gt
  else cmp t1 t2

/-- `l.vars` returns the list of variables that occur in `l`. -/
def vars (l : linexp) : list ℕ :=
l.map prod.fst

end linexp

section datatypes

@[derive decidable_eq, derive inhabited]
inductive ineq
| eq | le | lt

open ineq

def ineq.max : ineq → ineq → ineq
| eq a := a
| le a := a
| lt a := lt

/-- `ineq` is ordered `eq < le < lt`. -/
def ineq.cmp : ineq → ineq → ordering
| eq eq := ordering.eq
| eq _ := ordering.lt
| le le := ordering.eq
| le lt := ordering.lt
| lt lt := ordering.eq
| _ _ := ordering.gt

def ineq.to_string : ineq → string
| eq := "="
| le := "≤"
| lt := "<"

instance : has_to_string ineq := ⟨ineq.to_string⟩

/--
The main datatype for FM elimination.
Variables are represented by natural numbers, each of which has an integer coefficient.
Index 0 is reserved for constants, i.e. `coeffs.find 0` is the coefficient of 1.
The represented term is `coeffs.sum (λ ⟨k, v⟩, v * Var[k])`.
str determines the direction of the comparison -- is it < 0, ≤ 0, or = 0?
-/
@[derive inhabited]
structure comp : Type :=
(str : ineq)
(coeffs : linexp)

/-- `c.vars` returns the list of variables that appear in the linear expression contained in `c`. -/
def comp.vars : comp → list ℕ :=
linexp.vars ∘ comp.coeffs

@[derive inhabited]
inductive comp_source : Type
| assump : ℕ → comp_source
| add : comp_source → comp_source → comp_source
| scale : ℕ → comp_source → comp_source

meta def comp_source.flatten : comp_source → rb_map ℕ ℕ
| (comp_source.assump n) := mk_rb_map.insert n 1
| (comp_source.add c1 c2) := (comp_source.flatten c1).add (comp_source.flatten c2)
| (comp_source.scale n c) := (comp_source.flatten c).map (λ v, v * n)

def comp_source.to_string : comp_source → string
| (comp_source.assump e) := to_string e
| (comp_source.add c1 c2) := comp_source.to_string c1 ++ " + " ++ comp_source.to_string c2
| (comp_source.scale n c) := to_string n ++ " * " ++ comp_source.to_string c

meta instance comp_source.has_to_format : has_to_format comp_source :=
⟨λ a, comp_source.to_string a⟩

/--
A `pcomp` stores a linear comparison `Σ cᵢ*xᵢ R 0`,
along with information about how this comparison was derived.

The original expressions fed into `linarith` are each assigned a unique natural number label.
The *historical set* `pcomp.history` stores the labels of expressions
that were used in deriving the current `pcomp`.

Variables are also indexed by natural numbers. The sets `pcomp.effective`, `pcomp.implicit`,
and `pcomp.vars` contain variable indices.

* `pcomp.vars` contains the variables that appear in `pcomp.c`. We store them in `pcomp` to
  avoid recomputing the set, which requires folding over a list. (TODO: is this really needed?)
* `pcomp.effective` contains the variables that have been effectively eliminated from `pcomp`.
  A variable `n` is said to be *effectively eliminated* in `pcomp` if the elimination of `n`
  produced at least one of the ancestors of `pcomp`.
* `pcomp.implicit` contains the variables that have been implicitly eliminated from `pcomp`.
  A variable `n` is said to be *implicitly eliminated* in `pcomp` if it satisfies the following
  properties:
  - There is some `ancestor` of `pcomp` such that `n` appears in `ancestor.vars`.
  - `n` does not appear in `pcomp.vars`.
  - `n` was not effectively eliminated.

We track these sets in order to compute whether the history of a `pcomp` is *minimal*.
Checking this directly is expensive, but effective approximations can be defined in terms of these
sets. During the variable elimination process, a `pcomp` with non-minimal history can be discarded.
-/
meta structure pcomp : Type :=
(c : comp)
(src : comp_source)
(history : rb_set ℕ)
(effective : rb_set ℕ)
(implicit : rb_set ℕ)
(vars : rb_set ℕ)

/--
Any comparison whose history is not minimal is redundant,
and need not be included in the new set of comparisons.

`elimed_ge : ℕ` is a natural number such that all variables with index ≥ `elimed_ge` have been
removed from the system.

This test is an overapproximation to minimality. It gives necessary but not sufficient conditions.
If the history of `c` is minimal, then `c.maybe_minimal` is true,
but `c.maybe_minimal` may also be true for some `c` with minimal history.
Thus, if `c.maybe_minimal` is false, `c` is known not to be minimal and must be redundant.

See http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.51.493&rep=rep1&type=pdf p.13
(Theorem 7).

The condition described there considers only implicitly eliminated variables that have been
officially eliminated from the system. This is not the case for every implicitly eliminated variable.
Consider eliminating `z` from `{x + y + z < 0, x - y - z < 0}`. The result is the set
`{2*x < 0}`; `y` is implicitly but not officially eliminated.

This implementation of Fourier-Motzkin elimination processes variables in decreasing order of
indices. Immediately after a step that eliminates variable `k`, variable `k'` has been eliminated
iff `k' ≥ k`. Thus we can compute the intersection of officially and implicitly eliminated variables
by taking the set of implicitly eliminated variables with indices ≥ `elimed_ge`.
-/
meta def pcomp.maybe_minimal (c : pcomp) (elimed_ge : ℕ) : bool :=
c.history.size ≤ 1 + ((c.implicit.filter (≥ elimed_ge)).union c.effective).size

/-- `comp` has a lex order. First the `ineq`s are compared, then the `coeff`s. -/
meta def comp.cmp : comp → comp → ordering
| ⟨str1, coeffs1⟩ ⟨str2, coeffs2⟩ :=
  match str1.cmp str2 with
  | ordering.lt := ordering.lt
  | ordering.gt := ordering.gt
  | ordering.eq := coeffs1.cmp coeffs2
  end

/--
The `comp_source` field is ignored when comparing `pcomp`s. Two `pcomp`s proving the same
comparison, with different sources, are considered equivalent.
-/
meta def pcomp.cmp (p1 p2 : pcomp) : ordering :=
p1.c.cmp p2.c

meta def comp.coeff_of (c : comp) (a : ℕ) : ℤ :=
c.coeffs.zfind a

meta def comp.scale (c : comp) (n : ℕ) : comp :=
{ c with coeffs := c.coeffs.scale n }

meta def comp.add (c1 c2 : comp) : comp :=
⟨c1.str.max c2.str, c1.coeffs.add c2.coeffs⟩

meta def pcomp.scale (c : pcomp) (n : ℕ) : pcomp :=
{c with c := c.c.scale n, src := c.src.scale n}

/--
`pcomp.add c1 c2 elim_var` creates the result of summing the linear comparisons `c1` and `c2`,
during the process of eliminating the variable `elim_var`.
The computation assumes, but does not enforce, that `elim_var` appears in both `c1` and `c2`
and does not appear in the sum.

Computing the sum of the two comparisons is easy; the complicated details lie in tracking the
additional fields of `pcomp`.

* The historical set `pcomp.history` of `c1 + c2` is the union of the two historical sets.
* We recompute the variables that appear in `c1 + c2` from the newly created `linexp`,
  since some may have been implicitly eliminated.
* The effectively eliminated variables of `c1 + c2` are the union of the two effective sets,
  with `elim_var` inserted.
* The implicitly eliminated variables of `c1 + c2` are those that appear in at least one of
  `c1.vars` and `c2.vars` but not in `(c1 + c2).vars`, excluding `elim_var`.
-/
meta def pcomp.add (c1 c2 : pcomp) (elim_var : ℕ) : pcomp :=
let c := c1.c.add c2.c,
    src := c1.src.add c2.src,
    history := c1.history.union c2.history,
    vars := native.rb_set.of_list c.vars,
    effective := (c1.effective.union c2.effective).insert elim_var,
    implicit := ((c1.vars.union c2.vars).sdiff vars).erase elim_var in
⟨c, src, history, effective, implicit, vars⟩

/--
`pcomp.assump c n` creates a `pcomp` whose comparison is `c` and whose source is
`comp_source.assump n`, that is, `c` is derived from the `n`th hypothesis.
The history is the singleton set `{n}`.
No variables have been eliminated (effectively or implicitly).
-/
meta def pcomp.assump (c : comp) (n : ℕ) : pcomp :=
{ c := c,
  src := comp_source.assump n,
  history := mk_rb_set.insert n,
  effective := mk_rb_set,
  implicit := mk_rb_set,
  vars := rb_set.of_list c.vars }

meta instance pcomp.to_format : has_to_format pcomp :=
⟨λ p, to_fmt p.c.coeffs ++ to_string p.c.str ++ "0"⟩

meta instance comp.to_format : has_to_format comp :=
⟨λ p, to_fmt p.coeffs ++ to_string p.str ++ "0"⟩

/-- Creates an empty set of `pcomp`s, sorted using `pcomp.cmp`. -/
meta def mk_pcomp_set : rb_set pcomp :=
rb_map.mk_core unit pcomp.cmp

end datatypes

section fm_elim

/-- If `c1` and `c2` both contain variable `a` with opposite coefficients,
produces `v1`, `v2` such that `a` has been cancelled in `v1*c1 + v2*c2`. -/
meta def elim_var (c1 c2 : comp) (a : ℕ) : option (ℕ × ℕ) :=
let v1 := c1.coeff_of a,
    v2 := c2.coeff_of a in
if v1 * v2 < 0 then
  let vlcm :=  nat.lcm v1.nat_abs v2.nat_abs,
      v1' := vlcm / v1.nat_abs,
      v2' := vlcm / v2.nat_abs in
  some ⟨v1', v2'⟩
else none

meta def pelim_var (p1 p2 : pcomp) (a : ℕ) : option pcomp :=
do (n1, n2) ← elim_var p1.c p2.c a,
   return $ (p1.scale n1).add (p2.scale n2) a

meta def comp.is_contr (c : comp) : bool := c.coeffs.empty ∧ c.str = ineq.lt

meta def pcomp.is_contr (p : pcomp) : bool := p.c.is_contr

meta def elim_with_set (a : ℕ) (p : pcomp) (comps : rb_set pcomp) : rb_set pcomp :=
comps.fold mk_pcomp_set $ λ pc s,
match pelim_var p pc a with
| some pc := if pc.maybe_minimal a then s.insert pc else s
| none := s
end

/--
The state for the elimination monad.
* `vars`: the set of variables present in `comps`
* `comps`: a set of comparisons
-/
meta structure linarith_structure :=
(vars : rb_set ℕ)
(comps : rb_set pcomp)

@[reducible, derive [monad, monad_except pcomp]] meta def linarith_monad :=
state_t linarith_structure (except_t pcomp id)

meta def get_vars : linarith_monad (rb_set ℕ) :=
linarith_structure.vars <$> get

meta def get_var_list : linarith_monad (list ℕ) :=
rb_set.to_list <$> get_vars

meta def get_comps : linarith_monad (rb_set pcomp) :=
linarith_structure.comps <$> get

meta def validate : linarith_monad unit :=
do ⟨_, comps⟩ ← get,
match comps.to_list.find (λ p : pcomp, p.is_contr) with
| none := return ()
| some c := throw c
end

meta def update (vars : rb_set ℕ) (comps : rb_set pcomp) : linarith_monad unit :=
state_t.put ⟨vars, comps⟩ >> validate

/--
`split_set_by_var_sign a comps` partitions the set `comps` into three parts.
* `pos` contains the elements of `comps` in which `a` has a positive coefficient.
* `neg` contains the elements of `comps` in which `a` has a negative coefficient.
* `not_present` contains the elements of `comps` in which `a` has coefficient 0.

Returns `(pos, neg, not_present)`.
-/
meta def split_set_by_var_sign (a : ℕ) (comps : rb_set pcomp) :
  rb_set pcomp × rb_set pcomp × rb_set pcomp :=
comps.fold ⟨mk_pcomp_set, mk_pcomp_set, mk_pcomp_set⟩ $ λ pc ⟨pos, neg, not_present⟩,
  let n := pc.c.coeff_of a in
  if n > 0 then ⟨pos.insert pc, neg, not_present⟩
  else if n < 0 then ⟨pos, neg.insert pc, not_present⟩
  else ⟨pos, neg, not_present.insert pc⟩

/--
`monad.elim_var a` performs one round of Fourier-Motzkin elimination, eliminating the variable `a`
from the `linarith` state.
-/
meta def monad.elim_var (a : ℕ) : linarith_monad unit :=
do vs ← get_vars,
   when (vs.contains a) $
do ⟨pos, neg, not_present⟩ ← split_set_by_var_sign a <$> get_comps,
   let cs' := pos.fold not_present (λ p s, s.union (elim_with_set a p neg)),
   update (vs.erase a) cs'


meta def elim_all_vars : linarith_monad unit :=
get_var_list >>= list.mmap' monad.elim_var

end fm_elim

/-!
`linarith` computes the linear form of its input expressions,
assuming (without justification) that the type of these expressions
is a commutative semiring.

It identifies atoms up to ring-equivalence: that is, `(y*3)*x` will be identified `3*(x*y)`,
where the monomial `x*y` is the linear atom.

* Variables are represented by natural numbers.
* Monomials are represented by `monom := rb_map ℕ ℕ`. The monomial `1` is represented by the empty map.
* Linear combinations of monomials are represented by `sum := rb_map monom ℤ`.

All input expressions are converted to `sum`s, preserving the map from expressions to variables.
We then discard the monomial information, mapping each distinct monomial to a natural number.
The resulting `rb_map ℕ ℤ` represents the ring-normalized linear form of the expression.
-/

/-- Variables (represented by natural numbers) map to their power. -/
@[reducible] meta def monom : Type := rb_map ℕ ℕ

/-- Compare monomials by first comparing their keys and then their powers. -/
@[reducible] meta def monom.lt : monom → monom → Prop :=
λ a b, (a.keys < b.keys) || ((a.keys = b.keys) && (a.values < b.values))

/-- The `has_lt` instance for `monom` is only needed locally. -/
local attribute [instance]
meta def monom_has_lt : has_lt monom := ⟨monom.lt⟩

/-- Linear combinations of monomials are represented by mapping monomials to coefficients. -/
@[reducible] meta def sum : Type := rb_map monom ℤ

/-- `sum.scale_by_monom s m` multiplies every monomial in `s` by `m`. -/
meta def sum.scale_by_monom (s : sum) (m : monom) : sum :=
s.fold mk_rb_map $ λ m' coeff sm, sm.insert (m.add m') coeff

/-- `sum.mul s1 s2` distributes the multiplication of two sums.` -/
meta def sum.mul (s1 s2 : sum) : sum :=
s1.fold mk_rb_map $ λ mn coeff sm, sm.add $ (s2.scale_by_monom mn).scale coeff

/-- `sum_of_monom m` lifts `m` to a sum with coefficient `1`. -/
meta def sum_of_monom (m : monom) : sum :=
mk_rb_map.insert m 1

/-- The unit monomial `one` is represented by the empty rb map. -/
meta def one : monom := mk_rb_map

/-- A scalar `z` is represented by a `sum` with coefficient `z` and monomial `one` -/
meta def scalar (z : ℤ) : sum :=
mk_rb_map.insert one z

/-- A single variable `n` is represented by a sum with coefficient `1` and monomial `n`. -/
meta def var (n : ℕ) : sum :=
mk_rb_map.insert (mk_rb_map.insert n 1) 1

section parse

open ineq tactic

meta def map_of_expr_mul_aux (c1 c2 : rb_map ℕ ℤ) : option (rb_map ℕ ℤ) :=
match c1.keys, c2.keys with
| [0], _ := some $ c2.scale (c1.zfind 0)
| _, [0] := some $ c1.scale (c2.zfind 0)
| [], _ := some mk_rb_map
| _, [] := some mk_rb_map
| _, _ := none
end

meta def list.mfind {α} (tac : α → tactic unit) : list α → tactic α
| [] := failed
| (h::t) := tac h >> return h <|> list.mfind t

meta def rb_map.find_defeq (red : transparency) {v} (m : expr_map v) (e : expr) : tactic v :=
prod.snd <$> list.mfind (λ p, is_def_eq e p.1 red) m.to_list

/--
`map_of_expr red map e` computes the linear form of `e`.

`map` is a lookup map from atomic expressions to variable numbers.
If a new atomic expression is encountered, it is added to the map with a new number.
-/
meta def map_of_expr (red : transparency) : expr_map ℕ → expr → tactic (expr_map ℕ × sum)
| m e@`(%%e1 * %%e2) :=
   do (m', comp1) ← map_of_expr m e1,
      (m', comp2) ← map_of_expr m' e2,
      return (m', comp1.mul comp2)
| m `(%%e1 + %%e2) :=
   do (m', comp1) ← map_of_expr m e1,
      (m', comp2) ← map_of_expr m' e2,
      return (m', comp1.add comp2)
| m `(%%e1 - %%e2) :=
   do (m', comp1) ← map_of_expr m e1,
      (m', comp2) ← map_of_expr m' e2,
      return (m', comp1.add (comp2.scale (-1)))
| m `(-%%e) := do (m', comp) ← map_of_expr m e, return (m', comp.scale (-1))
| m e :=
  match e.to_int with
  | some 0 := return ⟨m, mk_rb_map⟩
  | some z := return ⟨m, scalar z⟩
  | none :=
    (do k ← rb_map.find_defeq red m e, return (m, var k)) <|>
    (let n := m.size + 1 in return (m.insert e n, var n))
  end

/--
`sum_to_lf s map` eliminates the monomial level of the `sum` `s`.

`map` is a lookup map from monomials to variable numbers.
The output `rb_map ℕ ℤ` has the same structure as `sum`,
but each monomial key is replaced with its index according to `map`.
If any new monomials are encountered, they are assigned variable numbers and `map` is updated.
 -/
meta def sum_to_lf (s : sum) (m : rb_map monom ℕ) : rb_map monom ℕ × rb_map ℕ ℤ :=
s.fold (m, mk_rb_map) $ λ mn coeff ⟨map, out⟩,
  match map.find mn with
  | some n := ⟨map, out.insert n coeff⟩
  | none := let n := map.size in ⟨map.insert mn n, out.insert n coeff⟩
  end

meta def parse_into_comp_and_expr : expr → option (ineq × expr)
| `(%%e < 0) := (ineq.lt, e)
| `(%%e ≤ 0) := (ineq.le, e)
| `(%%e = 0) := (ineq.eq, e)
| _ := none

meta def to_comp (red : transparency) (e : expr) (m : expr_map ℕ) (mm : rb_map monom ℕ) :
  tactic (comp × expr_map ℕ × rb_map monom ℕ) :=
do (iq, e) ← parse_into_comp_and_expr e,
   (m', comp') ← map_of_expr red m e,
   let ⟨nm, mm'⟩ := sum_to_lf comp' mm,
   return ⟨⟨iq, mm'.to_linexp⟩,m',nm⟩

meta def to_comp_fold (red : transparency) : expr_map ℕ → list expr → rb_map monom ℕ →
      tactic (list (option comp) × expr_map ℕ × rb_map monom ℕ )
| m [] mm := return ([], m, mm)
| m (h::t) mm :=
  (do (c, m', mm') ← to_comp red h m mm,
      (l, mp, mm') ← to_comp_fold m' t mm',
      return (c::l, mp, mm')) <|>
  (do (l, mp, mm') ← to_comp_fold m t mm,
      return (none::l, mp, mm'))

/--
Takes a list of proofs of props of the form `t {<, ≤, =} 0`, and creates a
`linarith_structure`.
-/
meta def mk_linarith_structure (red : transparency) (l : list expr) :
  tactic (linarith_structure × rb_map ℕ (expr × expr)) :=
do pftps ← l.mmap infer_type,
  (l', _, map) ← to_comp_fold red mk_rb_map pftps mk_rb_map,
  let lz := list.enum $ ((l.zip pftps).zip l').filter_map (λ ⟨a, b⟩, prod.mk a <$> b),
  let prmap := rb_map.of_list $ lz.map (λ ⟨n, x⟩, (n, x.1)),
  let vars : rb_set ℕ := rb_map.set_of_list $ list.range map.size,
  let pc : rb_set pcomp :=
    rb_set.of_list_core mk_pcomp_set $ lz.map (λ ⟨n, x⟩, pcomp.assump x.2 n),
  return ({vars := vars, comps := pc}, prmap)

meta def linarith_monad.run (red : transparency) {α} (tac : linarith_monad α) (l : list expr) :
  tactic ((pcomp ⊕ α) × rb_map ℕ (expr × expr)) :=
do (struct, inputs) ← mk_linarith_structure red l,
match (state_t.run (validate >> tac) struct).run with
| (except.ok (a, _)) := return (sum.inr a, inputs)
| (except.error contr) := return (sum.inl contr, inputs)
end

end parse

section prove
open ineq tactic

meta def get_rel_sides : expr → tactic (expr × expr)
| `(%%a < %%b) := return (a, b)
| `(%%a ≤ %%b) := return (a, b)
| `(%%a = %%b) := return (a, b)
| `(%%a ≥ %%b) := return (a, b)
| `(%%a > %%b) := return (a, b)
| _ := failed

meta def mul_expr (n : ℕ) (e : expr) : pexpr :=
if n = 1 then ``(%%e) else
``(%%(nat.to_pexpr n) * %%e)

meta def add_exprs_aux : pexpr → list pexpr → pexpr
| p [] := p
| p [a] := ``(%%p + %%a)
| p (h::t) := add_exprs_aux ``(%%p + %%h) t

meta def add_exprs : list pexpr → pexpr
| [] := ``(0)
| (h::t) := add_exprs_aux h t

meta def find_contr (m : rb_set pcomp) : option pcomp :=
m.keys.find (λ p, p.c.is_contr)

meta def ineq_const_mul_nm : ineq → name
| lt := ``mul_neg
| le := ``mul_nonpos
| eq := ``mul_eq

meta def ineq_const_nm : ineq → ineq → (name × ineq)
| eq eq := (``eq_of_eq_of_eq, eq)
| eq le := (``le_of_eq_of_le, le)
| eq lt := (``lt_of_eq_of_lt, lt)
| le eq := (``le_of_le_of_eq, le)
| le le := (`add_nonpos, le)
| le lt := (`add_neg_of_nonpos_of_neg, lt)
| lt eq := (``lt_of_lt_of_eq, lt)
| lt le := (`add_neg_of_neg_of_nonpos, lt)
| lt lt := (`add_neg, lt)

meta def mk_single_comp_zero_pf (c : ℕ) (h : expr) : tactic (ineq × expr) :=
do tp ← infer_type h,
  some (iq, e) ← return $ parse_into_comp_and_expr tp,
  if c = 0 then
    do e' ← mk_app ``zero_mul [e], return (eq, e')
  else if c = 1 then return (iq, h)
  else
    do nm ← resolve_name (ineq_const_mul_nm iq),
       tp ← (prod.snd <$> (infer_type h >>= get_rel_sides)) >>= infer_type,
       cpos ← to_expr ``((%%c.to_pexpr : %%tp) > 0),
       (_, ex) ← solve_aux cpos `[norm_num, done],
--       e' ← mk_app (ineq_const_mul_nm iq) [h, ex], -- this takes many seconds longer in some examples! why?
       e' ← to_expr ``(%%nm %%h %%ex) ff,
       return (iq, e')

meta def mk_lt_zero_pf_aux (c : ineq) (pf npf : expr) (coeff : ℕ) : tactic (ineq × expr) :=
do (iq, h') ← mk_single_comp_zero_pf coeff npf,
   let (nm, niq) := ineq_const_nm c iq,
   n ← resolve_name nm,
   e' ← to_expr ``(%%n %%pf %%h'),
   return (niq, e')

/--
Takes a list of coefficients `[c]` and list of expressions, of equal length.
Each expression is a proof of a prop of the form `t {<, ≤, =} 0`.
Produces a proof that the sum of `(c*t) {<, ≤, =} 0`,
where the `comp` is as strong as possible.
-/
meta def mk_lt_zero_pf : list ℕ → list expr → tactic expr
| _ [] := fail "no linear hypotheses found"
| [c] [h] := prod.snd <$> mk_single_comp_zero_pf c h
| (c::ct) (h::t) :=
  do (iq, h') ← mk_single_comp_zero_pf c h,
     prod.snd <$> (ct.zip t).mfoldl (λ pr ce, mk_lt_zero_pf_aux pr.1 pr.2 ce.2 ce.1) (iq, h')
| _ _ := fail "not enough args to mk_lt_zero_pf"

meta def term_of_ineq_prf (prf : expr) : tactic expr :=
do (lhs, _) ← infer_type prf >>= get_rel_sides,
   return lhs

meta structure linarith_config :=
(discharger : tactic unit := `[ring])
(restrict_type : option Type := none)
(restrict_type_reflect : reflected restrict_type . apply_instance)
(exfalso : bool := tt)
(transparency : transparency := reducible)
(split_hypotheses : bool := tt)

meta def ineq_pf_tp (pf : expr) : tactic expr :=
do (_, z) ← infer_type pf >>= get_rel_sides,
   infer_type z

meta def mk_neg_one_lt_zero_pf (tp : expr) : tactic expr :=
to_expr ``((neg_neg_of_pos zero_lt_one : -1 < (0 : %%tp)))

/--
Assumes `e` is a proof that `t = 0`. Creates a proof that `-t = 0`.
-/
meta def mk_neg_eq_zero_pf (e : expr) : tactic expr :=
to_expr ``(neg_eq_zero.mpr %%e)

meta def add_neg_eq_pfs : list expr → tactic (list expr)
| [] := return []
| (h::t) :=
  do some (iq, tp) ← parse_into_comp_and_expr <$> infer_type h,
  match iq with
  | ineq.eq := do nep ← mk_neg_eq_zero_pf h, tl ← add_neg_eq_pfs t, return $ h::nep::tl
  | _ := list.cons h <$> add_neg_eq_pfs t
  end

/--
Takes a list of proofs of propositions of the form `t {<, ≤, =} 0`,
and tries to prove the goal `false`.
-/
meta def prove_false_by_linarith1 (cfg : linarith_config) : list expr → tactic unit
| [] := fail "no args to linarith"
| l@(h::t) :=
  do l' ← add_neg_eq_pfs l,
     hz ← ineq_pf_tp h >>= mk_neg_one_lt_zero_pf,
     (sum.inl contr, inputs) ← elim_all_vars.run cfg.transparency (hz::l')
       | fail "linarith failed to find a contradiction",
     let coeffs := inputs.keys.map (λ k, (contr.src.flatten.ifind k)),
     let pfs : list expr := inputs.keys.map (λ k, (inputs.ifind k).1),
     let zip := (coeffs.zip pfs).filter (λ pr, pr.1 ≠ 0),
     let (coeffs, pfs) := zip.unzip,
     mls ← zip.mmap (λ pr, do e ← term_of_ineq_prf pr.2, return (mul_expr pr.1 e)),
     sm ← to_expr $ add_exprs mls,
     tgt ← to_expr ``(%%sm = 0),
     (a, b) ← solve_aux tgt (cfg.discharger >> done),
     pf ← mk_lt_zero_pf coeffs pfs,
     pftp ← infer_type pf,
     (_, nep, _) ← rewrite_core b pftp,
     pf' ← mk_eq_mp nep pf,
     mk_app `lt_irrefl [pf'] >>= exact

end prove

section normalize
open tactic

set_option eqn_compiler.max_steps 50000

meta def rem_neg (prf : expr) : expr → tactic expr
| `(_ ≤ _) := to_expr ``(lt_of_not_ge %%prf)
| `(_ < _) := to_expr ``(le_of_not_gt %%prf)
| `(_ > _) := to_expr ``(le_of_not_gt %%prf)
| `(_ ≥ _) := to_expr ``(lt_of_not_ge %%prf)
| e := failed

meta def rearr_comp : expr → expr → tactic expr
| prf `(%%a ≤ 0) := return prf
| prf  `(%%a < 0) := return prf
| prf  `(%%a = 0) := return prf
| prf  `(%%a ≥ 0) := to_expr ``(neg_nonpos.mpr %%prf)
| prf  `(%%a > 0) := to_expr ``(neg_neg_of_pos %%prf)
| prf  `(0 ≥ %%a) := to_expr ``(show %%a ≤ 0, from %%prf)
| prf  `(0 > %%a) := to_expr ``(show %%a < 0, from %%prf)
| prf  `(0 = %%a) := to_expr ``(eq.symm %%prf)
| prf  `(0 ≤ %%a) := to_expr ``(neg_nonpos.mpr %%prf)
| prf  `(0 < %%a) := to_expr ``(neg_neg_of_pos %%prf)
| prf  `(%%a ≤ %%b) := to_expr ``(sub_nonpos.mpr %%prf)
| prf  `(%%a < %%b) := to_expr ``(sub_neg_of_lt %%prf)
| prf  `(%%a = %%b) := to_expr ``(sub_eq_zero.mpr %%prf)
| prf  `(%%a > %%b) := to_expr ``(sub_neg_of_lt %%prf)
| prf  `(%%a ≥ %%b) := to_expr ``(sub_nonpos.mpr %%prf)
| prf  `(¬ %%t) := do nprf ← rem_neg prf t, tp ← infer_type nprf, rearr_comp nprf tp
| prf  _ := fail "couldn't rearrange comp"


meta def is_numeric : expr → option ℚ
| `(%%e1 + %%e2) := (+) <$> is_numeric e1 <*> is_numeric e2
| `(%%e1 - %%e2) := has_sub.sub <$> is_numeric e1 <*> is_numeric e2
| `(%%e1 * %%e2) := (*) <$> is_numeric e1 <*> is_numeric e2
| `(%%e1 / %%e2) := (/) <$> is_numeric e1 <*> is_numeric e2
| `(-%%e) := rat.neg <$> is_numeric e
| e := e.to_rat

meta def find_cancel_factor : expr → ℕ × tree ℕ
| `(%%e1 + %%e2) :=
  let (v1, t1) := find_cancel_factor e1, (v2, t2) := find_cancel_factor e2, lcm := v1.lcm v2 in
  (lcm, tree.node lcm t1 t2)
| `(%%e1 - %%e2) :=
  let (v1, t1) := find_cancel_factor e1, (v2, t2) := find_cancel_factor e2, lcm := v1.lcm v2 in
  (lcm, tree.node lcm t1 t2)
| `(%%e1 * %%e2) :=
  let (v1, t1) := find_cancel_factor e1, (v2, t2) := find_cancel_factor e2, pd := v1*v2 in
  (pd, tree.node pd t1 t2)
| `(%%e1 / %%e2) :=
  match is_numeric e2 with
  | some q := let (v1, t1) := find_cancel_factor e1, n := v1.lcm q.num.nat_abs in
    (n, tree.node n t1 (tree.node q.num.nat_abs tree.nil tree.nil))
  | none := (1, tree.node 1 tree.nil tree.nil)
  end
| `(-%%e) := find_cancel_factor e
| _ := (1, tree.node 1 tree.nil tree.nil)

open tree

meta def mk_prod_prf : ℕ → tree ℕ → expr → tactic expr
| v (node _ lhs rhs) `(%%e1 + %%e2) :=
  do v1 ← mk_prod_prf v lhs e1, v2 ← mk_prod_prf v rhs e2, mk_app ``add_subst [v1, v2]
| v (node _ lhs rhs) `(%%e1 - %%e2) :=
  do v1 ← mk_prod_prf v lhs e1, v2 ← mk_prod_prf v rhs e2, mk_app ``sub_subst [v1, v2]
| v (node n lhs@(node ln _ _) rhs) `(%%e1 * %%e2) :=
  do tp ← infer_type e1, v1 ← mk_prod_prf ln lhs e1, v2 ← mk_prod_prf (v/ln) rhs e2,
     ln' ← tp.of_nat ln, vln' ← tp.of_nat (v/ln), v' ← tp.of_nat v,
     ntp ← to_expr ``(%%ln' * %%vln' = %%v'),
     (_, npf) ← solve_aux ntp `[norm_num, done],
     mk_app ``mul_subst [v1, v2, npf]
| v (node n lhs rhs@(node rn _ _)) `(%%e1 / %%e2) :=
  do tp ← infer_type e1, v1 ← mk_prod_prf (v/rn) lhs e1,
     rn' ← tp.of_nat rn, vrn' ← tp.of_nat (v/rn), n' ← tp.of_nat n, v' ← tp.of_nat v,
     ntp ← to_expr ``(%%rn' / %%e2 = 1),
     (_, npf) ← solve_aux ntp `[norm_num, done],
     ntp2 ← to_expr ``(%%vrn' * %%n' = %%v'),
     (_, npf2) ← solve_aux ntp2 `[norm_num, done],
     mk_app ``div_subst [v1, npf, npf2]
| v t `(-%%e) := do v' ← mk_prod_prf v t e, mk_app ``neg_subst [v']
| v _ e :=
  do tp ← infer_type e,
     v' ← tp.of_nat v,
     e' ← to_expr ``(%%v' * %%e),
     mk_app `eq.refl [e']

/--
Given `e`, a term with rational division, produces a natural number `n` and a proof of `n*e = e'`,
where `e'` has no division.
-/
meta def kill_factors (e : expr) : tactic (ℕ × expr) :=
let (n, t) := find_cancel_factor e in
do e' ← mk_prod_prf n t e, return (n, e')

open expr
meta def expr_contains (n : name) : expr → bool
| (const nm _) := nm = n
| (lam _ _ _ bd) := expr_contains bd
| (pi _ _ _ bd) := expr_contains bd
| (app e1 e2) := expr_contains e1 || expr_contains e2
| _ := ff

lemma sub_into_lt {α} [ordered_semiring α] {a b : α} (he : a = b) (hl : a ≤ 0) : b ≤ 0 :=
by rwa he at hl

meta def norm_hyp_aux (h' lhs : expr) : tactic expr :=
do (v, lhs') ← kill_factors lhs,
   if v = 1 then return h' else do
   (ih, h'') ← mk_single_comp_zero_pf v h',
   (_, nep, _) ← infer_type h'' >>= rewrite_core lhs',
   mk_eq_mp nep h''

meta def norm_hyp (h : expr) : tactic expr :=
do htp ← infer_type h,
   h' ← rearr_comp h htp,
   some (c, lhs) ← parse_into_comp_and_expr <$> infer_type h',
   if expr_contains `has_div.div lhs then
     norm_hyp_aux h' lhs
   else return h'

meta def get_contr_lemma_name : expr → option name
| `(%%a < %%b) := return `lt_of_not_ge
| `(%%a ≤ %%b) := return `le_of_not_gt
| `(%%a = %%b) := return ``eq_of_not_lt_of_not_gt
| `(%%a ≠ %%b) := return `not.intro
| `(%%a ≥ %%b) := return `le_of_not_gt
| `(%%a > %%b) := return `lt_of_not_ge
| `(¬ %%a < %%b) := return `not.intro
| `(¬ %%a ≤ %%b) := return `not.intro
| `(¬ %%a = %%b) := return `not.intro
| `(¬ %%a ≥ %%b) := return `not.intro
| `(¬ %%a > %%b) := return `not.intro
| _ := none

/-- Assumes the input `t` is of type `ℕ`. Produces `t'` of type `ℤ` such that `↑t = t'` and
a proof of equality. -/
meta def cast_expr (e : expr) : tactic (expr × expr) :=
do s ← [`int.coe_nat_add, `int.coe_nat_zero, `int.coe_nat_one,
        ``int.coe_nat_bit0_mul, ``int.coe_nat_bit1_mul, ``int.coe_nat_zero_mul, ``int.coe_nat_one_mul,
        ``int.coe_nat_mul_bit0, ``int.coe_nat_mul_bit1, ``int.coe_nat_mul_zero, ``int.coe_nat_mul_one,
        ``int.coe_nat_bit0, ``int.coe_nat_bit1].mfoldl simp_lemmas.add_simp simp_lemmas.mk,
   ce ← to_expr ``(↑%%e : ℤ),
   simplify s [] ce {fail_if_unchanged := ff}

meta def is_nat_int_coe : expr → option expr
| `((↑(%%n : ℕ) : ℤ)) := some n
| _ := none

meta def mk_coe_nat_nonneg_prf (e : expr) : tactic expr :=
mk_app `int.coe_nat_nonneg [e]

meta def get_nat_comps : expr → list expr
| `(%%a + %%b) := (get_nat_comps a).append (get_nat_comps b)
| `(%%a * %%b) := (get_nat_comps a).append (get_nat_comps b)
| e := match is_nat_int_coe e with
  | some e' := [e']
  | none := []
  end

meta def mk_coe_nat_nonneg_prfs (e : expr) : tactic (list expr) :=
(get_nat_comps e).mmap mk_coe_nat_nonneg_prf

meta def mk_cast_eq_and_nonneg_prfs (pf a b : expr) (ln : name) : tactic (list expr) :=
do (a', prfa) ← cast_expr a,
   (b', prfb) ← cast_expr b,
   la ← mk_coe_nat_nonneg_prfs a',
   lb ← mk_coe_nat_nonneg_prfs b',
   pf' ← mk_app ln [pf, prfa, prfb],
   return $ pf'::(la.append lb)

meta def mk_int_pfs_of_nat_pf (pf : expr) : tactic (list expr) :=
do tp ← infer_type pf,
match tp with
| `(%%a = %%b) := mk_cast_eq_and_nonneg_prfs pf a b ``nat_eq_subst
| `(%%a ≤ %%b) := mk_cast_eq_and_nonneg_prfs pf a b ``nat_le_subst
| `(%%a < %%b) := mk_cast_eq_and_nonneg_prfs pf a b ``nat_lt_subst
| `(%%a ≥ %%b) := mk_cast_eq_and_nonneg_prfs pf b a ``nat_le_subst
| `(%%a > %%b) := mk_cast_eq_and_nonneg_prfs pf b a ``nat_lt_subst
| `(¬ %%a ≤ %%b) := do pf' ← mk_app ``lt_of_not_ge [pf], mk_cast_eq_and_nonneg_prfs pf' b a ``nat_lt_subst
| `(¬ %%a < %%b) := do pf' ← mk_app ``le_of_not_gt [pf], mk_cast_eq_and_nonneg_prfs pf' b a ``nat_le_subst
| `(¬ %%a ≥ %%b) := do pf' ← mk_app ``lt_of_not_ge [pf], mk_cast_eq_and_nonneg_prfs pf' a b ``nat_lt_subst
| `(¬ %%a > %%b) := do pf' ← mk_app ``le_of_not_gt [pf], mk_cast_eq_and_nonneg_prfs pf' a b ``nat_le_subst
| _ := fail "mk_int_pfs_of_nat_pf failed: proof is not an inequality"
end

meta def mk_non_strict_int_pf_of_strict_int_pf (pf : expr) : tactic expr :=
do tp ← infer_type pf,
match tp with
| `(%%a < %%b) := to_expr ``(@cast (%%a < %%b) (%%a + 1 ≤ %%b) (by refl) %%pf)
| `(%%a > %%b) := to_expr ``(@cast (%%a > %%b) (%%a ≥ %%b + 1) (by refl) %%pf)
| `(¬ %%a ≤ %%b) := to_expr ``(@cast (%%a > %%b) (%%a ≥ %%b + 1) (by refl) (lt_of_not_ge %%pf))
| `(¬ %%a ≥ %%b) := to_expr ``(@cast (%%a < %%b) (%%a + 1 ≤ %%b) (by refl) (lt_of_not_ge %%pf))
| _ := fail "mk_non_strict_int_pf_of_strict_int_pf failed: proof is not an inequality"
end

meta def guard_is_nat_prop : expr → tactic unit
| `(%%a = _) := infer_type a >>= unify `(ℕ)
| `(%%a ≤ _) := infer_type a >>= unify `(ℕ)
| `(%%a < _) := infer_type a >>= unify `(ℕ)
| `(%%a ≥ _) := infer_type a >>= unify `(ℕ)
| `(%%a > _) := infer_type a >>= unify `(ℕ)
| `(¬ %%p) := guard_is_nat_prop p
| _ := failed

meta def guard_is_strict_int_prop : expr → tactic unit
| `(%%a < _) := infer_type a >>= unify `(ℤ)
| `(%%a > _) := infer_type a >>= unify `(ℤ)
| `(¬ %%a ≤ _) := infer_type a >>= unify `(ℤ)
| `(¬ %%a ≥ _) := infer_type a >>= unify `(ℤ)
| _ := failed

meta def replace_nat_pfs : list expr → tactic (list expr)
| [] := return []
| (h::t) :=
  (do infer_type h >>= guard_is_nat_prop,
      ls ← mk_int_pfs_of_nat_pf h,
      list.append ls <$> replace_nat_pfs t) <|> list.cons h <$> replace_nat_pfs t

meta def replace_strict_int_pfs : list expr → tactic (list expr)
| [] := return []
| (h::t) :=
  (do infer_type h >>= guard_is_strict_int_prop,
      l ← mk_non_strict_int_pf_of_strict_int_pf h,
      list.cons l <$> replace_strict_int_pfs t) <|> list.cons h <$> replace_strict_int_pfs t

meta def partition_by_type_aux : rb_lmap expr expr → list expr → tactic (rb_lmap expr expr)
| m [] := return m
| m (h::t) := do tp ← ineq_pf_tp h, partition_by_type_aux (m.insert tp h) t

meta def partition_by_type (l : list expr) : tactic (rb_lmap expr expr) :=
partition_by_type_aux mk_rb_map l

private meta def try_linarith_on_lists (cfg : linarith_config) (ls : list (list expr)) : tactic unit :=
(first $ ls.map $ prove_false_by_linarith1 cfg) <|> fail "linarith failed"

/--
Takes a list of proofs of propositions.
Filters out the proofs of linear (in)equalities,
and tries to use them to prove `false`.
If `pref_type` is given, starts by working over this type.
-/
meta def prove_false_by_linarith (cfg : linarith_config) (pref_type : option expr) (l : list expr) : tactic unit :=
do l' ← replace_nat_pfs l,
   l'' ← replace_strict_int_pfs l',
   ls ← list.reduce_option <$> l''.mmap (λ h, (do s ← norm_hyp h, return (some s)) <|> return none)
          >>= partition_by_type,
   pref_type ← (unify pref_type.iget `(ℕ) >> return (some `(ℤ) : option expr)) <|> return pref_type,
   match cfg.restrict_type, rb_map.values ls, pref_type with
   | some rtp, _, _ :=
      do m ← mk_mvar, unify `(some %%m : option Type) cfg.restrict_type_reflect, m ← instantiate_mvars m,
         prove_false_by_linarith1 cfg (ls.ifind m)
   | none, [ls'], _ := prove_false_by_linarith1 cfg ls'
   | none, ls', none := try_linarith_on_lists cfg ls'
   | none, _, (some t) := prove_false_by_linarith1 cfg (ls.ifind t) <|>
      try_linarith_on_lists cfg (rb_map.values (ls.erase t))
   end

end normalize

/--
`find_squares m e` collects all terms of the form `a ^ 2` and `a * a` that appear in `e`
and adds them to the set `m`.
A pair `(a, tt)` is added to `m` when `a^2` appears in `e`, and `(a, ff)` is added to `m`
when `a*a` appears in `e`.  -/
meta def find_squares : rb_set (expr × bool) → expr → tactic (rb_set (expr × bool))
| s `(%%a ^ 2) := do s ← find_squares s a, return (s.insert (a, tt))
| s e@`(%%e1 * %%e2) := if e1 = e2 then do s ← find_squares s e1, return (s.insert (e1, ff)) else e.mfoldl find_squares s
| s e := e.mfoldl find_squares s

-- used in the `nlinarith` normalization steps. The `_` argument is for uniformity.
@[nolint unused_arguments]
lemma mul_zero_eq {α} {R : α → α → Prop} [semiring α] {a b : α} (_ : R a 0) (h : b = 0) : a * b = 0 :=
by simp [h]

-- used in the `nlinarith` normalization steps. The `_` argument is for uniformity.
@[nolint unused_arguments]
lemma zero_mul_eq {α} {R : α → α → Prop} [semiring α] {a b : α} (h : a = 0) (_ : R b 0) : a * b = 0 :=
by simp [h]


end linarith

section
open tactic linarith

open lean lean.parser interactive tactic interactive.types
local postfix `?`:9001 := optional
local postfix *:9001 := many

meta def linarith.elab_arg_list : option (list pexpr) → tactic (list expr)
| none := return []
| (some l) := l.mmap i_to_expr

meta def linarith.preferred_type_of_goal : option expr → tactic (option expr)
| none := return none
| (some e) := some <$> ineq_pf_tp e

/--
`linarith.interactive_aux cfg o_goal restrict_hyps args`:
* `cfg` is a `linarith_config` object
* `o_goal : option expr` is the local constant corresponding to the former goal, if there was one
* `restrict_hyps : bool` is `tt` if `linarith only [...]` was used
* `args : option (list pexpr)` is the optional list of arguments in `linarith [...]`
-/
meta def linarith.interactive_aux (cfg : linarith_config) :
  option expr → bool → option (list pexpr) → tactic unit
| none tt none := fail "linarith only called with no arguments"
| none tt (some l) := l.mmap i_to_expr >>= prove_false_by_linarith cfg none
| (some e) tt l :=
  do tp ← ineq_pf_tp e,
     list.cons e <$> linarith.elab_arg_list l >>= prove_false_by_linarith cfg (some tp)
| oe ff l :=
  do otp ← linarith.preferred_type_of_goal oe,
     list.append <$> local_context <*>
      (list.filter (λ a, bnot $ expr.is_local_constant a) <$> linarith.elab_arg_list l) >>=
     prove_false_by_linarith cfg otp

/--
Tries to prove a goal of `false` by linear arithmetic on hypotheses.
If the goal is a linear (in)equality, tries to prove it by contradiction.
If the goal is not `false` or an inequality, applies `exfalso` and tries linarith on the
hypotheses.

* `linarith` will use all relevant hypotheses in the local context.
* `linarith [t1, t2, t3]` will add proof terms t1, t2, t3 to the local context.
* `linarith only [h1, h2, h3, t1, t2, t3]` will use only the goal (if relevant), local hypotheses
  `h1`, `h2`, `h3`, and proofs `t1`, `t2`, `t3`. It will ignore the rest of the local context.
* `linarith!` will use a stronger reducibility setting to identify atoms.

Config options:
* `linarith {exfalso := ff}` will fail on a goal that is neither an inequality nor `false`
* `linarith {restrict_type := T}` will run only on hypotheses that are inequalities over `T`
* `linarith {discharger := tac}` will use `tac` instead of `ring` for normalization.
  Options: `ring2`, `ring SOP`, `simp`
-/
meta def tactic.interactive.linarith (red : parse ((tk "!")?))
  (restr : parse ((tk "only")?)) (hyps : parse pexpr_list?)
  (cfg : linarith_config := {}) : tactic unit :=
let cfg :=
  if red.is_some then {cfg with transparency := semireducible, discharger := `[ring!]}
  else cfg in
do t ← target,
   when cfg.split_hypotheses (try auto.split_hyps),
   match get_contr_lemma_name t with
   | some nm := seq' (applyc nm) $
     do t ← intro1, linarith.interactive_aux cfg (some t) restr.is_some hyps
   | none := if cfg.exfalso then exfalso >> linarith.interactive_aux cfg none restr.is_some hyps
             else fail "linarith failed: target type is not an inequality."
   end

add_hint_tactic "linarith"

/--
`linarith` attempts to find a contradiction between hypotheses that are linear (in)equalities.
Equivalently, it can prove a linear inequality by assuming its negation and proving `false`.

In theory, `linarith` should prove any goal that is true in the theory of linear arithmetic over
the rationals. While there is some special handling for non-dense orders like `nat` and `int`,
this tactic is not complete for these theories and will not prove every true goal.

An example:
```lean
example (x y z : ℚ) (h1 : 2*x  < 3*y) (h2 : -4*x + 2*z < 0)
        (h3 : 12*y - 4* z < 0)  : false :=
by linarith
```

`linarith` will use all appropriate hypotheses and the negation of the goal, if applicable.

`linarith [t1, t2, t3]` will additionally use proof terms `t1, t2, t3`.

`linarith only [h1, h2, h3, t1, t2, t3]` will use only the goal (if relevant), local hypotheses
`h1`, `h2`, `h3`, and proofs `t1`, `t2`, `t3`. It will ignore the rest of the local context.

`linarith!` will use a stronger reducibility setting to try to identify atoms. For example,
```lean
example (x : ℚ) : id x ≥ x :=
by linarith
```
will fail, because `linarith` will not identify `x` and `id x`. `linarith!` will.
This can sometimes be expensive.

`linarith {discharger := tac, restrict_type := tp, exfalso := ff}` takes a config object with five
optional arguments:
* `discharger` specifies a tactic to be used for reducing an algebraic equation in the
  proof stage. The default is `ring`. Other options currently include `ring SOP` or `simp` for basic
  problems.
* `restrict_type` will only use hypotheses that are inequalities over `tp`. This is useful
  if you have e.g. both integer and rational valued inequalities in the local context, which can
  sometimes confuse the tactic.
* `transparency` controls how hard `linarith` will try to match atoms to each other. By default
  it will only unfold `reducible` definitions.
* If `split_hypotheses` is true, `linarith` will split conjunctions in the context into separate
  hypotheses.
* If `exfalso` is false, `linarith` will fail when the goal is neither an inequality nor `false`.
  (True by default.)

A variant, `nlinarith`, does some basic preprocessing to handle some nonlinear goals.
-/
add_tactic_doc
{ name       := "linarith",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.linarith],
  tags       := ["arithmetic", "decision procedure", "finishing"] }

/--
An extension of `linarith` with some preprocessing to allow it to solve some nonlinear arithmetic
problems. (Based on Coq's `nra` tactic.) See `linarith` for the available syntax of options,
which are inherited by `nlinarith`; that is, `nlinarith!` and `nlinarith only [h1, h2]` all work as
in `linarith`. The preprocessing is as follows:

* For every subterm `a ^ 2` or `a * a` in a hypothesis or the goal,
  the assumption `0 ≤ a ^ 2` or `0 ≤ a * a` is added to the context.
* For every pair of hypotheses `a1 R1 b1`, `a2 R2 b2` in the context, `R1, R2 ∈ {<, ≤, =}`,
  the assumption `0 R' (b1 - a1) * (b2 - a2)` is added to the context (non-recursively),
  where `R ∈ {<, ≤, =}` is the appropriate comparison derived from `R1, R2`.
-/
meta def tactic.interactive.nlinarith (red : parse ((tk "!")?))
  (restr : parse ((tk "only")?)) (hyps : parse pexpr_list?)
  (cfg : linarith_config := {}) : tactic unit := do
  ls ← match hyps with
    | none := if restr.is_some then return [] else local_context
    | some hyps := do
      ls ← hyps.mmap i_to_expr,
      if restr.is_some then return ls else (++ ls) <$> local_context
    end,
  (s, ge0) ← (list.mfoldr (λ h ⟨s, l⟩, do
      h ← infer_type h >>= rearr_comp h <|> return h,
      t ← infer_type h,
      s ← find_squares s t,
      return (s, match t with
        | `(%%a ≤ 0) := (ineq.le, h) :: l
        | `(%%a < 0) := (ineq.lt, h) :: l
        | `(%%a = 0) := (ineq.eq, h) :: l
        | _ := l end))
    (mk_rb_set, []) ls : tactic (rb_set (expr × bool) × list (ineq × expr))),
  s ← target >>= find_squares s,
  (hyps, ge0) ← s.fold (return (hyps, ge0)) (λ ⟨e, is_sq⟩ tac, do
    (hyps, ge0) ← tac,
    (do
      t ← infer_type e,
      when cfg.restrict_type.is_some
        (is_def_eq `(some %%t : option Type) cfg.restrict_type_reflect),
      p ← mk_app (if is_sq then ``pow_two_nonneg else ``mul_self_nonneg) [e],
      p ← infer_type p >>= rearr_comp p <|> return p,
      t ← infer_type p,
      h ← assertv `h t p,
      return (hyps.map (λ l, pexpr.of_expr h :: l), (ineq.le, h) :: ge0)) <|>
    return (hyps, ge0)),
  ge0.mmap'_diag (λ ⟨posa, a⟩ ⟨posb, b⟩, try $ do
    p ←  match posa, posb with
      | ineq.eq, _ := mk_app ``zero_mul_eq [a, b]
      | _, ineq.eq := mk_app ``mul_zero_eq [a, b]
      | ineq.lt, ineq.lt := mk_app ``mul_pos_of_neg_of_neg [a, b]
      | ineq.lt, ineq.le := do a ← mk_app ``le_of_lt [a], mk_app ``mul_nonneg_of_nonpos_of_nonpos [a, b]
      | ineq.le, ineq.lt := do b ← mk_app ``le_of_lt [b], mk_app ``mul_nonneg_of_nonpos_of_nonpos [a, b]
      | ineq.le, ineq.le := mk_app ``mul_nonneg_of_nonpos_of_nonpos [a, b]
      end,
    t ← infer_type p,
    assertv `h t p, skip),
  tactic.interactive.linarith red restr hyps cfg

add_hint_tactic "nlinarith"

add_tactic_doc
{ name       := "nlinarith",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.nlinarith],
  tags       := ["arithmetic", "decision procedure", "finishing"] }

end
