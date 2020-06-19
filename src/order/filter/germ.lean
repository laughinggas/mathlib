/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Abhimanyu Pallavi Sudhir
-/
import order.filter.basic
import algebra.pi_instances

/-!
# Germ of a function at a filter

The germ of a function `f : α → β` at a filter `l : filter α` is the equivalence class of `f`
with respect to the equivalence relation `eventually_eq l`: `f ≈ g` means `∀ᶠ x in l, f x = g x`.

We define `mk l f` to be the germ of `f` at `l` and `const l c` to be the germ of the constant
function at `l`.

For each of the following structures we prove that if `β` has this structure, then so does `germ l β`:

* one-operation algebraic structures up to `comm_group`;
* `mul_zero_class`, `distrib`, `semiring`, `comm_semiring`, `ring`, `comm_ring`;
* `preorder` and `partial_order`; note that `mk l f
-/

namespace filter

variables {α β γ δ : Type*} {l : filter α} {f g h : α → β}

lemma const_eventually_eq' (hl : l ≠ ⊥) {a b : β} : (∀ᶠ x in l, a = b) ↔ a = b :=
eventually_const hl

lemma const_eventually_eq (hl : l ≠ ⊥) {a b : β} : ((λ _, a) =ᶠ[l] (λ _, b)) ↔ a = b :=
@const_eventually_eq' _ _ _ hl a b

lemma eventually_eq.comp_tendsto {f' : α → β} (H : f =ᶠ[l] f') {g : γ → α} {lc : filter γ}
  (hg : tendsto g lc l) :
  f ∘ g =ᶠ[lc] f' ∘ g :=
hg.eventually H

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

instance : has_coe_t (α → β) (germ l β) := ⟨quotient.mk'⟩

@[simp] lemma quot_mk_eq_coe (l : filter α) (f : α → β) : quot.mk _ f = (f : germ l β) := rfl

@[simp] lemma mk'_eq_coe (l : filter α) (f : α → β) : quotient.mk' f = (f : germ l β) := rfl

@[elab_as_eliminator]
lemma induction_on (f : germ l β) {p : germ l β → Prop} (h : ∀ f : α → β, p f) : p f :=
quotient.induction_on' f h

@[elab_as_eliminator]
lemma induction_on₂ (f : germ l β) (g : germ l γ) {p : germ l β → germ l γ → Prop}
  (h : ∀ (f : α → β) (g : α → γ), p f g) : p f g :=
quotient.induction_on₂' f g h

@[elab_as_eliminator]
lemma induction_on₃ (f : germ l β) (g : germ l γ) (h : germ l δ)
  {p : germ l β → germ l γ → germ l δ → Prop}
  (H : ∀ (f : α → β) (g : α → γ) (h : α → δ), p f g h) :
  p f g h :=
quotient.induction_on₃' f g h H

lemma coe_eq : (f : germ l β) = g ↔ (f =ᶠ[l] g) := quotient.eq'

alias coe_eq ↔ _ filter.eventually_eq.germ_eq

def map (op : β → γ) : germ l β → germ l γ :=
quotient.map' ((∘) op) $ λ f g H, H.mono $ λ x H, congr_arg op H

def map₂ (op : β → γ → δ) : germ l β → germ l γ → germ l δ :=
quotient.map₂' (λ f g x, op (f x) (g x)) $ λ f f' Hf g g' Hg,
Hg.mp $ Hf.mono $ λ x Hf Hg, by simp only [Hf, Hg]

def comp_tendsto (f : germ l β) {lc : filter γ} {g : γ → α} (hg : tendsto g lc l) :
  germ lc β :=
quotient.lift_on' f (λ f, ↑(f ∘ g)) $ λ f g H, coe_eq.2 $ H.comp_tendsto hg

@[simp] lemma coe_comp_tendsto (f : α → β) {lc : filter γ} {g : γ → α} (hg : tendsto g lc l) :
  (f : germ l β).comp_tendsto hg = f ∘ g :=
rfl

def const (l : filter α) (a : β) : germ l β := ↑(λ x : α, a)

@[simp] lemma const_inj (hl : l ≠ ⊥) {a b : β} : const l a = const l b ↔ a = b :=
coe_eq.trans $ const_eventually_eq hl

@[simp] lemma map_const (l : filter α) (a : β) (f : β → γ) :
  (const l a).map f = const l (f a) :=
rfl

@[simp] lemma map₂_const (l : filter α) (b : β) (c : γ) (f : β → γ → δ) :
  map₂ f (const l b) (const l c) = const l (f b c) :=
rfl

@[simp] lemma const_comp_tendsto {l : filter α} (b : β) {lc : filter γ} {g : γ → α}
  (hg : tendsto g lc l) :
  (const l b).comp_tendsto hg = const lc b :=
rfl

section monoid

variables {M : Type*} {G : Type*}

@[to_additive]
instance [has_mul M] : has_mul (germ l M) := ⟨map₂ (*)⟩

@[simp, to_additive]
lemma coe_mul [has_mul M] (f g : α → M) : ↑(f * g) = (f * g : germ l M) := rfl

attribute [norm_cast] coe_mul coe_add

@[to_additive]
instance [has_one M] : has_one (germ l M) := ⟨const l 1⟩

@[simp, to_additive]
lemma coe_one [has_one M] : ↑(1 : α → M) = (1 : germ l M) := rfl

attribute [norm_cast] coe_one coe_zero

@[to_additive add_semigroup]
instance [semigroup M] : semigroup (germ l M) :=
{ mul := (*), mul_assoc := by { rintros ⟨f⟩ ⟨g⟩ ⟨h⟩,
    simp only [mul_assoc, quot_mk_eq_coe, ← coe_mul] } }

@[to_additive add_comm_semigroup]
instance [comm_semigroup M] : comm_semigroup (germ l M) :=
{ mul := (*),
  mul_comm := by { rintros ⟨f⟩ ⟨g⟩, simp only [mul_comm, quot_mk_eq_coe, ← coe_mul] },
  .. germ.semigroup }

@[to_additive left_cancel_add_semigroup]
instance [left_cancel_semigroup M] : left_cancel_semigroup (germ l M) :=
{ mul := (*),
  mul_left_cancel := λ f₁ f₂ f₃, induction_on₃ f₁ f₂ f₃ $ λ f₁ f₂ f₃ H,
    coe_eq.2 ((coe_eq.1 H).mono $ λ x, mul_left_cancel),
  .. germ.semigroup }

@[to_additive right_cancel_add_semigroup]
instance [right_cancel_semigroup M] : right_cancel_semigroup (germ l M) :=
{ mul := (*),
  mul_right_cancel := λ f₁ f₂ f₃, induction_on₃ f₁ f₂ f₃ $ λ f₁ f₂ f₃ H,
    coe_eq.2 $ (coe_eq.1 H).mono $ λ x, mul_right_cancel,
  .. germ.semigroup }

@[to_additive add_monoid]
instance [monoid M] : monoid (germ l M) :=
{ mul := (*),
  one := 1,
  one_mul := λ f, induction_on f $ λ f, by { norm_cast, rw [one_mul] },
  mul_one := λ f, induction_on f $ λ f, by { norm_cast, rw [mul_one] },
  .. germ.semigroup }

/-- coercion from functions to germs as a monoid homomorphism. -/
@[to_additive]
def coe_mul_hom [monoid M] : (α → M) →* germ l M := ⟨coe, rfl, λ f g, rfl⟩

/-- coercion from functions to germs as an additive monoid homomorphism. -/
add_decl_doc coe_add_hom

@[to_additive add_comm_monoid]
instance [comm_monoid M] : comm_monoid (germ l M) :=
{ mul := (*),
  one := 1,
  .. germ.comm_semigroup, .. germ.monoid }

@[to_additive]
instance [has_inv G] : has_inv (germ l G) := ⟨map has_inv.inv⟩

@[simp, to_additive]
lemma coe_inv [has_inv G] (f : α → G) : ↑f⁻¹ = (f⁻¹ : germ l G) := rfl

attribute [norm_cast] coe_inv coe_neg

@[to_additive add_group]
instance [group G] : group (germ l G) :=
{ mul := (*),
  one := 1,
  inv := has_inv.inv,
  mul_left_inv := λ f, induction_on f $ λ f,
    -- TODO(pi_id): `pi.group.to_has_one` has `id` preventing `simp` from using `mk_one`
    by { norm_cast, rw [mul_left_inv], refl },
  .. germ.monoid }

@[simp, norm_cast]
lemma coe_sub [add_group G] (f  g : α → G) : ↑(f - g) = (f - g : germ l G) := rfl

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
  mul_zero := λ f, induction_on f $ λ f, by { norm_cast, rw [mul_zero], refl },
  zero_mul := λ f, induction_on f $ λ f, by { norm_cast, rw [zero_mul], refl } }

instance [distrib R] : distrib (germ l R) :=
{ mul := (*),
  add := (+),
  left_distrib := λ f g h, induction_on₃ f g h $ λ f g h, by { norm_cast, rw [left_distrib] },
  right_distrib := λ f g h, induction_on₃ f g h $ λ f g h, by { norm_cast, rw [right_distrib] } }

instance [semiring R] : semiring (germ l R) :=
{ .. germ.add_comm_monoid, .. germ.monoid, .. germ.distrib, .. germ.mul_zero_class }

instance [ring R] : ring (germ l R) :=
{ .. germ.add_comm_group, .. germ.monoid, .. germ.distrib, .. germ.mul_zero_class }

instance [comm_semiring R] : comm_semiring (germ l R) :=
{ .. germ.semiring, .. germ.comm_monoid }

instance [comm_ring R] : comm_ring (germ l R) :=
{ .. germ.ring, .. germ.comm_monoid }

end ring

section module

variables {M N R : Type*}

instance [monoid M] [has_scalar M β]  : has_scalar M (germ l β) :=
⟨λ c, map ((•) c)⟩

instance has_scalar' [monoid M] [has_scalar M β] : has_scalar (germ l M) (germ l β) :=
⟨map₂ (•)⟩

@[simp] lemma coe_smul [monoid M] [has_scalar M β] (c : M) (f : α → β) :
  ↑(c • f) = (c • f : germ l β) :=
rfl

@[simp] lemma coe_smul' [monoid M] [has_scalar M β] (c : α → M) (f : α → β) :
  ↑(c • f) = (c • f : germ l β) :=
rfl

instance {M : Type*} [monoid M] [mul_action M β]  : mul_action M (germ l β) :=
{ smul := (•),
  one_smul := λ f, induction_on f $ λ f, _,
}

instance {M N : Type*} [monoid M] [add_monoid N] [distrib_mul_action M N] :
  distrib_mul_action M (germ l N) :=
{ smul := (•),
}

end module

instance [has_le β] : has_le (germ l β) :=
⟨λ f g, quotient.lift_on₂' f g l.eventually_le $
  λ f f' g g' h h', propext $ eventually_le_congr h h'⟩

-- Should this be a `norm_cast`?
@[simp] lemma coe_le [has_le β] : (f : germ l β) ≤ g = (f ≤ᶠ[l] g) := rfl

instance [preorder β] : preorder (germ l β) :=
{ le := (≤),
  le_refl := λ f, induction_on f $ eventually_le.refl l,
  le_trans := λ f₁ f₂ f₃, induction_on₃ f₁ f₂ f₃ $ λ f₁ f₂ f₃, eventually_le.trans }

instance [partial_order β] : partial_order (germ l β) :=
{ le := (≤),
  le_antisymm := λ f g, induction_on₂ f g $ λ f g h₁ h₂, (h₁.antisymm h₂).germ_eq,
  .. germ.preorder }

instance [has_bot β] : has_bot (germ l β) := ⟨const l ⊥⟩

@[simp] lemma const_bot [has_bot β] : const l (⊥:β) = ⊥ := rfl

instance [order_bot β] : order_bot (germ l β) :=
{ bot := ⊥,
  le := (≤),
  bot_le := λ f, induction_on f $ λ f, eventually_of_forall _ $ λ x, bot_le,
  .. germ.partial_order }

instance [has_top β] : has_top (germ l β) := ⟨const l ⊤⟩

@[simp] lemma const_top [has_top β] : const l (⊤:β) = ⊤ := rfl

instance [order_top β] : order_top (germ l β) :=
{ top := ⊤,
  le := (≤),
  le_top := λ f, induction_on f $ λ f, eventually_of_forall _ $ λ x, le_top,
  .. germ.partial_order }

instance [has_sup β] : has_sup (germ l β) := ⟨map₂ (⊔)⟩

instance [has_inf β] : has_inf (germ l β) := ⟨map₂ (⊓)⟩

instance [semilattice_sup β] : semilattice_sup (germ l β) :=
{ sup := (⊔),
  le_sup_left := λ f g, induction_on₂ f g $ λ f g,
    eventually_of_forall _ $ λ x, le_sup_left,
  le_sup_right := λ f g, induction_on₂ f g $ λ f g,
    eventually_of_forall _ $ λ x, le_sup_right,
  sup_le := λ f₁ f₂ g, induction_on₃ f₁ f₂ g $ λ f₁ f₂ g h₁ h₂,
    h₂.mp $ h₁.mono $ λ x, sup_le,
  .. germ.partial_order }

instance [semilattice_inf β] : semilattice_inf (germ l β) :=
{ inf := (⊓),
  inf_le_left := λ f g, induction_on₂ f g $ λ f g,
    eventually_of_forall _ $ λ x, inf_le_left,
  inf_le_right := λ f g, induction_on₂ f g $ λ f g,
    eventually_of_forall _ $ λ x, inf_le_right,
  le_inf := λ f₁ f₂ g, induction_on₃ f₁ f₂ g $ λ f₁ f₂ g h₁ h₂,
    h₂.mp $ h₁.mono $ λ x, le_inf,
  .. germ.partial_order }

instance [semilattice_inf_bot β] : semilattice_inf_bot (germ l β) :=
{ .. germ.semilattice_inf, .. germ.order_bot }

instance [semilattice_sup_bot β] : semilattice_sup_bot (germ l β) :=
{ .. germ.semilattice_sup, .. germ.order_bot }

instance [semilattice_inf_top β] : semilattice_inf_top (germ l β) :=
{ .. germ.semilattice_inf, .. germ.order_top }

instance [semilattice_sup_top β] : semilattice_sup_top (germ l β) :=
{ .. germ.semilattice_sup, .. germ.order_top }

instance [lattice β] : lattice (germ l β) :=
{ .. germ.semilattice_sup, .. germ.semilattice_inf }

instance [bounded_lattice β] : bounded_lattice (germ l β) :=
{ .. germ.lattice, .. germ.order_bot, .. germ.order_top }

@[to_additive ordered_cancel_add_comm_monoid]
instance [ordered_cancel_comm_monoid β] : ordered_cancel_comm_monoid (germ l β) :=
{ mul_le_mul_left := λ f g, induction_on₂ f g $ λ f g H h, induction_on h $ λ h,
    H.mono $ λ x H, mul_le_mul_left'' H _,
  le_of_mul_le_mul_left := λ f g h, induction_on₃ f g h $ λ f g h H,
    H.mono $ λ x, le_of_mul_le_mul_left',
  .. germ.partial_order, .. germ.comm_monoid, .. germ.left_cancel_semigroup,
  .. germ.right_cancel_semigroup }

end germ

end filter
