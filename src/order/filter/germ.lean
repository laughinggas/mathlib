/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Abhimanyu Pallavi Sudhir
-/
import order.filter.basic
import algebra.pi_instances

/-!
# Germ of a function at a filter
-/

namespace filter

variables {α β γ δ : Type*} {l : filter α} {f g h : α → β}

lemma const_eventually_eq' (hl : l ≠ ⊥) {a b : β} : (∀ᶠ x in l, a = b) ↔ a = b :=
eventually_const hl

lemma const_eventually_eq (hl : l ≠ ⊥) {a b : β} : ((λ _, a) =ᶠ[l] (λ _, b)) ↔ a = b :=
@const_eventually_eq' _ _ _ hl a b

section has_le

variables [has_le β]

def eventually_le (l : filter α) (f g : α → β) : Prop := ∀ᶠ x in l, f x ≤ g x

notation f ` ≤ᶠ[`:50 l:50 `] `:0 g:50 := eventually_le l f g

lemma eventually_le.congr {f f' g g' : α → β} (H : f ≤ᶠ[l] g) (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g') :
  f' ≤ᶠ[l] g' :=
H.mp $ hg.mp $ hf.mono $ λ x hf hg H, by rwa [hf, hg] at H

lemma eventually_le_congr {f f' g g' : α → β} (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g') :
  f ≤ᶠ[l] g ↔ f' ≤ᶠ[l] g' :=
⟨λ H, H.congr hf hg, λ H, H.congr hf.symm hg.symm⟩

end has_le

section preorder

variables [preorder β]

lemma eventually_eq.le (h : f =ᶠ[l] g) : f ≤ᶠ[l] g := h.mono $ λ x, le_of_eq

@[refl] lemma eventually_le.refl (l : filter α) (f : α → β) :
  f ≤ᶠ[l] f :=
(eventually_eq.refl l f).le

@[trans] lemma eventually_le.trans (H₁ : f ≤ᶠ[l] g) (H₂ : g ≤ᶠ[l] h) : f ≤ᶠ[l] h :=
H₂.mp $ H₁.mono $ λ x, le_trans

@[trans] lemma eventually_eq.trans_le (H₁ : f =ᶠ[l] g) (H₂ : g ≤ᶠ[l] h) : f ≤ᶠ[l] h :=
H₁.le.trans H₂

@[trans] lemma eventually_le.trans_eq (H₁ : f ≤ᶠ[l] g) (H₂ : g =ᶠ[l] h) : f ≤ᶠ[l] h :=
H₁.trans H₂.le

end preorder

lemma eventually_le.antisymm [partial_order β] (h₁ : f ≤ᶠ[l] g) (h₂ : g ≤ᶠ[l] f) :
  f =ᶠ[l] g :=
h₂.mp $ h₁.mono $ λ x, le_antisymm

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

def map_right (op : β → γ) : germ l β → germ l γ :=
quotient.map' ((∘) op) $ λ f g H, H.mono $ λ x H, congr_arg op H

def map_right₂ (op : β → γ → δ) : germ l β → germ l γ → germ l δ :=
quotient.map₂' (λ f g x, op (f x) (g x)) $ λ f f' Hf g g' Hg,
Hg.mp $ Hf.mono $ λ x Hf Hg, by simp only [Hf, Hg]

def const (l : filter α) (a : β) : germ l β := mk l (λ _, a)

@[simp] lemma const_inj (hl : l ≠ ⊥) {a b : β} : const l a = const l b ↔ a = b :=
quotient.eq'.trans $ const_eventually_eq hl

section monoid

variables {M : Type*} {G : Type*}

@[to_additive]
instance [has_mul M] : has_mul (germ l M) := ⟨map_right₂ (*)⟩

@[simp, to_additive]
lemma mk_mul_mk [has_mul M] (f g : α → M) : mk l f * mk l g = mk l (f * g) := rfl

@[to_additive]
instance [has_one M] : has_one (germ l M) := ⟨const l 1⟩

@[simp, to_additive]
lemma mk_one [has_one M] : mk l (1 : α → M) = 1 := rfl

@[to_additive add_semigroup]
instance [semigroup M] : semigroup (germ l M) :=
{ mul := (*), mul_assoc := by { rintros ⟨f⟩ ⟨g⟩ ⟨h⟩, apply sound, simp only [mul_assoc] } }

@[to_additive add_comm_semigroup]
instance [comm_semigroup M] : comm_semigroup (germ l M) :=
{ mul := (*),
  mul_comm := by { rintros ⟨f⟩ ⟨g⟩, apply sound, simp only [mul_comm] },
  .. germ.semigroup }

@[to_additive left_cancel_add_semigroup]
instance [left_cancel_semigroup M] : left_cancel_semigroup (germ l M) :=
{ mul := (*),
  mul_left_cancel := λ f₁ f₂ f₃, quotient.induction_on₃' f₁ f₂ f₃ $ λ f₁ f₂ f₃ H,
    sound $ (quotient.exact' H).mono $ λ x, mul_left_cancel,
  .. germ.semigroup }

@[to_additive right_cancel_add_semigroup]
instance [right_cancel_semigroup M] : right_cancel_semigroup (germ l M) :=
{ mul := (*),
  mul_right_cancel := λ f₁ f₂ f₃, quotient.induction_on₃' f₁ f₂ f₃ $ λ f₁ f₂ f₃ H,
    sound $ (quotient.exact' H).mono $ λ x, mul_right_cancel,
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
instance [has_inv G] : has_inv (germ l G) := ⟨map_right has_inv.inv⟩

@[simp, to_additive]
lemma inv_mk [has_inv G] (f : α → G) : (mk l f)⁻¹ = mk l f⁻¹ := rfl

#print pi.group
@[to_additive add_group]
instance [group G] : group (germ l G) :=
{ mul := (*),
  one := 1,
  inv := has_inv.inv,
  mul_left_inv := λ f, induction_on f $ λ f, by simp,
  .. germ.monoid }

@[simp]
lemma mk_sub_mk [add_group G] (f  g : α → G) : mk l f - mk l g = mk l (λ x, f x - g x) := rfl

@[to_additive add_comm_group]
instance [comm_group G] : comm_group (germ l G) :=
{ mul := (*),
  one := 1,
  inv := has_inv.inv,
  .. germ.group, .. germ.comm_monoid }

end monoid

section ring

variables {R : Type*}

/-- If `0 ≠ 1` in the codomain and -/
protected def nonzero [has_zero R] [has_one R] [nonzero R] (hl : l ≠ ⊥) :
  nonzero (germ l R) :=
{ zero_ne_one := mt (const_inj hl).1 zero_ne_one }

instance [mul_zero_class R] : mul_zero_class (germ l R) :=
{ zero := 0,
  mul := (*),
  mul_zero := λ f, induction_on f $ λ f, sound $ eventually_of_forall _ $ λ x, mul_zero _,
  zero_mul := λ f, induction_on f $ λ f, sound $ eventually_of_forall _ $ λ x, zero_mul _ }

instance [distrib R] : distrib (germ l R) :=
{ mul := (*),
  add := (+),
  left_distrib := λ f g h, quotient.induction_on₃' f g h $ λ f g h, sound $
    eventually_of_forall _ $ λ x, left_distrib _ _ _,
  right_distrib := λ f g h, quotient.induction_on₃' f g h $ λ f g h, sound $
    eventually_of_forall _ $ λ x, right_distrib _ _ _ }

instance [semiring R] : semiring (germ l R) :=
{ .. germ.add_comm_monoid, .. germ.monoid, .. germ.distrib, .. germ.mul_zero_class }

instance [ring R] : ring (germ l R) :=
{ .. germ.add_comm_group, .. germ.monoid, .. germ.distrib, .. germ.mul_zero_class }

instance [comm_semiring R] : comm_semiring (germ l R) :=
{ .. germ.semiring, .. germ.comm_monoid }

instance [comm_ring R] : comm_ring (germ l R) :=
{ .. germ.ring, .. germ.comm_monoid }

end ring

instance [has_le β] : has_le (germ l β) :=
⟨λ f g, quotient.lift_on₂' f g l.eventually_le $
  λ f f' g g' h h', propext $ eventually_le_congr h h'⟩

@[simp] lemma mk_le_mk [has_le β] : mk l f ≤ mk l g = (f ≤ᶠ[l] g) := rfl

instance [preorder β] : preorder (germ l β) :=
{ le := (≤),
  le_refl := λ f, induction_on f $ eventually_le.refl l,
  le_trans := λ f₁ f₂ f₃, induction_on f₁ $ λ f₁, induction_on f₂ $ λ f₂, induction_on f₃ $ λ f₃,
    eventually_le.trans }

instance [partial_order β] : partial_order (germ l β) :=
{ le := (≤),
  le_antisymm := λ f g, induction_on f $ λ f, induction_on g $ λ g h₁ h₂, sound $ h₁.antisymm h₂,
  .. germ.preorder }

@[to_additive ordered_cancel_add_comm_monoid]
instance [ordered_cancel_comm_monoid β] : ordered_cancel_comm_monoid (germ l β) :=
{ mul_le_mul_left := λ f g, quotient.induction_on₂' f g $ λ f g H h, induction_on h $ λ h,
    H.mono $ λ x H, mul_le_mul_left'' H _,
  le_of_mul_le_mul_left := λ f g h, quotient.induction_on₃' f g h $ λ f g h H,
    H.mono $ λ x, le_of_mul_le_mul_left',
  .. germ.partial_order, .. germ.comm_monoid, .. germ.left_cancel_semigroup,
  .. germ.right_cancel_semigroup }

end germ

end filter
