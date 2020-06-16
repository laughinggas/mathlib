/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/

import order.filter.basic

/-!
# Germ of a function at a filter
-/

namespace filter

variables {α : Type*} {β : Type*} {l : filter α} {f g h : α → β}

def eventually_le [has_le β] (l : filter α) (f g : α → β) : Prop := ∀ᶠ x in l, f x ≤ g x

notation f ` ≤ᶠ[` l `] ` g := ∀ᶠ x in l, f x ≤ g x

section preorder

variables [preorder β]

lemma eventually_le_of_eq (h : f =ᶠ[l] g) : f ≤ᶠ[l] g := h.mono $ λ x, le_of_eq

@[trans] lemma eventually_le.trans (H₁ : f ≤ᶠ[l] g) (H₂ : g ≤ᶠ[l] h) : f ≤ᶠ[l] h :=
H₂.mp $ H₁.mono $ λ x, le_trans

end preorder
#check add_mul_self_eq

def eventually_lt (l : filter α) (f g : α → β) : Prop := ∀ᶠ x in l, f x = g x

lemma eventually_


def germ_setoid (l : filter α) (β : Type*) : setoid (α → β) :=
{ r := eventually_eq l,
  iseqv := ⟨eventually_eq.refl _, λ _ _, eventually_eq.symm, λ _ _ _, eventually_eq.trans⟩ }

def germ (l : filter α) (β : Type*) : Type* := quotient (germ_setoid l β)

namespace germ

def mk (l : filter α) (f : α → β) : germ l β := quotient.mk' f

@[simp] lemma quot_mk_eq_mk (l : filter α) (f : α → β) : quot.mk _ f = mk l f := rfl

@[simp] lemma mk'_eq_mk (l : filter α) (f : α → β) : quotient.mk' f = mk l f := rfl

@[elab_as_eliminator]
lemma induction_on (f : germ l β) {p : germ l β → Prop} (h : ∀ f : α → β, p (mk l f)) : p f :=
quotient.induction_on' f h

lemma sound (h : f =ᶠ[l] g) : mk l f = mk l g := quot.sound h

alias sound ← filter.eventually_eq.germ_eq

def const (l : filter α) (a : β) : germ l β := mk l (λ _, a)

section monoid

variables {M : Type*} {G : Type*}

@[to_additive]
instance [has_mul M] : has_mul (germ l M) :=
⟨quotient.map₂' (λ f g x, f x * g x) (λ f f' Hf g g' Hg, Hf.mul Hg)⟩

@[simp, to_additive]
lemma mk_mul_mk [has_mul M] (f g : α → M) : mk l f * mk l g = mk l (λ x, f x * g x) := rfl

@[to_additive]
instance [has_one M] : has_one (germ l M) := ⟨const l 1⟩

@[simp, to_additive]
lemma mk_one [has_one M] : mk l (λ _, (1:M)) = 1 := rfl

@[to_additive add_semigroup]
instance [semigroup M] : semigroup (germ l M) :=
{ mul := (*), mul_assoc := by { rintros ⟨f⟩ ⟨g⟩ ⟨h⟩, apply sound, simp only [mul_assoc] } }

@[to_additive add_comm_semigroup]
instance [comm_semigroup M] : comm_semigroup (germ l M) :=
{ mul := (*),
  mul_comm := by { rintros ⟨f⟩ ⟨g⟩, apply sound, simp only [mul_comm] },
  .. germ.semigroup }

@[to_additive add_monoid]
instance [monoid M] : monoid (germ l M) :=
{ mul := (*),
  one := 1,
  one_mul := λ f, induction_on f $ λ f, by simp only [← mk_one, mk_mul_mk, one_mul],
  mul_one := λ f, induction_on f $ λ f, by simp only [← mk_one, mk_mul_mk, mul_one],
  .. germ.semigroup }

@[to_additive add_comm_monoid]
instance [comm_monoid M] : comm_monoid (germ l M) :=
{ mul := (*),
  one := 1,
  .. germ.comm_semigroup, .. germ.monoid }

@[to_additive]
instance [has_inv G] : has_inv (germ l G) :=
⟨quotient.map' (λ f x, (f x)⁻¹) (λ f g H, H.inv)⟩

@[simp, to_additive]
lemma inv_mk [has_inv G] (f : α → G) : (mk l f)⁻¹ = mk l (λ x, (f x)⁻¹) := rfl

@[to_additive add_group]
instance [group G] : group (germ l G) :=
{ mul := (*),
  one := 1,
  inv := has_inv.inv,
  mul_left_inv := λ f, induction_on f $ λ f, by simp,
  .. germ.monoid }

@[to_additive add_comm_group]
instance [comm_group G] : comm_group (germ l G) :=
{ mul := (*),
  one := 1,
  inv := has_inv.inv,
  .. germ.group, .. germ.comm_monoid }

end monoid

section order

end germ

end filter
