/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.measure_space
import measure_theory.borel_space
import topology.opens
/-!
# Haar measure
-/
universe variables u v w
noncomputable theory

open topological_space set measurable_space has_inv

namespace nat

@[simp] lemma find_eq_zero {p : ℕ → Prop} [decidable_pred p] (h : ∃ (n : ℕ), p n) :
  nat.find h = 0 ↔ p 0 :=
begin
  split,
  { intro h0, rw [← h0], apply nat.find_spec },
  { intro hp, apply nat.eq_zero_of_le_zero, exact nat.find_min' _ hp }
end

@[simp] lemma find_pos {p : ℕ → Prop} [decidable_pred p] (h : ∃ (n : ℕ), p n) :
  0 < nat.find h ↔ ¬ p 0 :=
by rw [nat.pos_iff_ne_zero, not_iff_not, nat.find_eq_zero]

open_locale classical

/- redefine `Inf_nat_def` -/
protected lemma Inf_def {s : set ℕ} (h : s.nonempty) : Inf s = nat.find h :=
Inf_nat_def _

@[simp] lemma Inf_eq_zero {s : set ℕ} : Inf s = 0 ↔ 0 ∈ s ∨ s = ∅ :=
begin
  cases eq_empty_or_nonempty s,
  { subst h, simp only [or_true, eq_self_iff_true, iff_true, Inf, has_Inf.Inf,
      mem_empty_eq, exists_false, dif_neg, not_false_iff] },
  { have := ne_empty_iff_nonempty.mpr h,
    simp only [this, or_false, nat.Inf_def, h, nat.find_eq_zero] }
end

lemma Inf_spec {s : set ℕ} (h : s.nonempty) : Inf s ∈ s :=
by { rw [nat.Inf_def h], exact nat.find_spec h }

lemma not_mem_of_lt_Inf {s : set ℕ} {m : ℕ} (hm : m < Inf s) : m ∉ s :=
begin
  cases eq_empty_or_nonempty s,
  { subst h, apply not_mem_empty },
  { rw [nat.Inf_def h] at hm, exact nat.find_min h hm }
end

protected lemma Inf_le {s : set ℕ} {m : ℕ} (hm : m ∈ s) : Inf s ≤ m :=
by { rw [nat.Inf_def ⟨m, hm⟩], exact nat.find_min' ⟨m, hm⟩ hm }

end nat

@[simp] lemma bUnion_finset_image {α β γ} [decidable_eq α] {s : finset γ} {f : γ → α}
  {g : α → set β} : (⋃x ∈ s.image f, g x) = (⋃y ∈ s, g (f y)) :=
begin
  convert @bUnion_image _ _ _ (↑s) _ _, ext x y,
  simp only [mem_Union, exists_prop, ← finset.mem_coe, finset.coe_image]
end

@[simp] lemma bInter_finset_image {α β γ} [decidable_eq α] {s : finset γ} {f : γ → α}
  {g : α → set β} : (⋂ x ∈ s.image f, g x) = (⋂ y ∈ s, g (f y)) :=
begin
  convert @bInter_image _ _ _ (↑s) _ _, ext x y,
  simp only [mem_Inter, exists_prop, ← finset.mem_coe, finset.coe_image]
end

lemma mem_prop {α} {p : α → Prop} {x : α} : @has_mem.mem α (set α) _ x p ↔ p x := iff.rfl

lemma disjoint.preimage {α β} (f : α → β) {s t : set β} (h : disjoint s t) :
  disjoint (f ⁻¹' s) (f ⁻¹' t) :=
λ x hx, h hx

namespace function

lemma injective.surjective_preimage {α β : Type*} {f : α → β} (hf : injective f) :
  surjective (preimage f) :=
by { intro s, use f '' s, rw preimage_image_eq _ hf }

lemma surjective.surjective_image {α β : Type*} {f : α → β} (hf : surjective f) :
  surjective (image f) :=
by { intro s, use f ⁻¹' s, rw image_preimage_eq hf }

lemma injective.injective_image {α β : Type*} {f : α → β} (hf : injective f) :
  injective (image f) :=
by { intros s t h, rw [←preimage_image_eq s hf, ←preimage_image_eq t hf, h] }

lemma injective.ne_iff {α β : Type*} {f : α → β} (hf : injective f) {x y : α} :
  f x ≠ f y ↔ x ≠ y :=
⟨mt $ congr_arg f, hf.ne⟩

lemma injective.nonempty {α β : Type*} {f : set α → set β} (hf : injective f)
  (h2 : f ∅ = ∅) {s : set α} : (f s).nonempty ↔ s.nonempty :=
by rw [← ne_empty_iff_nonempty, ← h2, ← ne_empty_iff_nonempty, hf.ne_iff]

end function
open function

lemma infi_congr {α β γ : Type*} {f : α → γ} {g : β → γ} [complete_lattice γ] (h : α → β)
  (h1 : function.surjective h) (h2 : ∀ x, g (h x) = f x) : (⨅ x, f x) = ⨅ y, g y  :=
by { unfold infi, congr, convert h1.range_comp g, ext, rw ←h2 }

lemma supr_congr {α β γ : Type*} {f : α → γ} {g : β → γ} [complete_lattice γ] (h : α → β)
  (h1 : function.surjective h) (h2 : ∀ x, g (h x) = f x) : (⨆ x, f x) = ⨆ y, g y  :=
by { unfold supr, congr, convert h1.range_comp g, ext, rw ←h2 }


@[simp]
lemma injective_preimage {α β : Type*} {f : α → β} : injective (preimage f) ↔ surjective f :=
begin
  refine ⟨λ h y, _, surjective.injective_preimage⟩,
  obtain ⟨x, hx⟩ : (f ⁻¹' {y}).nonempty,
  { rw [h.nonempty preimage_empty], apply singleton_nonempty },
  exact ⟨x, hx⟩
end

@[simp]
lemma surjective_preimage {α β : Type*} {f : α → β} : surjective (preimage f) ↔ injective f :=
begin
  refine ⟨λ h x x' hx, _, injective.surjective_preimage⟩,
  cases h {x} with s hs, have := mem_singleton x,
  rwa [← hs, mem_preimage, hx, ← mem_preimage, hs, mem_singleton_iff, eq_comm] at this
end

@[simp] lemma surjective_image {α β : Type*} {f : α → β} : surjective (image f) ↔ surjective f :=
begin
  refine ⟨λ h y, _, surjective.surjective_image⟩,
  cases h {y} with s hs,
  have := mem_singleton y, rw [← hs] at this, rcases this with ⟨x, h1x, h2x⟩,
  exact ⟨x, h2x⟩
end

@[simp] lemma injective_image {α β : Type*} {f : α → β} : injective (image f) ↔ injective f :=
begin
  refine ⟨λ h x x' hx, _, injective.injective_image⟩,
  rw [← singleton_eq_singleton_iff], apply h,
  rw [image_singleton, image_singleton, hx]
end


namespace homeomorph
variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]
@[simp]
lemma is_open_preimage (f : α ≃ₜ β) {s : set β} : is_open (f ⁻¹' s) ↔ is_open s :=
begin
  refine ⟨λ h, _, f.continuous_to_fun s⟩,
  rw [← (image_preimage_eq f.to_equiv.surjective : _ = s)], exact f.is_open_map _ h
end

end homeomorph

section
variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]

/-- The compact sets of a topological space. See also `nonempty_compacts`. -/
def compacts (α : Type*) [topological_space α] : set (set α) := { s : set α | compact s }

/-- The compact sets with nonempty interior of a topological space. See also `compacts` and
  `nonempty_compacts`. -/
def nontrivial_compacts (α : Type*) [topological_space α] : set (set α) :=
{ s : set α | compact s ∧ (interior s).nonempty  }

/-- The open neighborhoods of a point. See also `opens`. -/
def open_nhds_of {α : Type*} [topological_space α] (x : α) : set (set α) :=
{ s : set α | is_open s ∧ x ∈ s }

variables {ι : Type*} {π : ι → Type*} [∀i, topological_space (π i)]

lemma compact_univ_pi {s : Πi:ι, set (π i)} (h : ∀i, compact (s i)) : compact (set.pi set.univ s) :=
by { convert compact_pi_infinite h, simp only [pi, forall_prop_of_true, mem_univ] }

end

variables {α : Type u} [measurable_space α]
          {β : Type v} [measurable_space β]

section
variables [topological_space α]  [borel_space α]
lemma compact.is_measurable [t2_space α] {s : set α} (h : compact s) : is_measurable s :=
(closed_of_compact _ h).is_measurable
end

namespace measure_theory

/-- A measure is nonzero if it is not 0 on the whole space. -/
def measure.nonzero (μ : measure α) : Prop :=
μ set.univ > 0

variable [topological_space α]

/-- A regular borel measure. -/
structure measure.regular (μ : measure α) : Prop :=
  (le_top_of_compact : ∀ {{K : set α}}, compact K → μ K < ⊤)
  (outer_regular : ∀ {{A : set α}}, is_measurable A →
    μ A = ⨅ (U : set α) (h : is_open U) (h2 : A ⊆ U), μ U)
  (inner_regular : ∀ {{U : set α}}, is_open U →
    μ U = ⨆ (K : set α) (h : compact K) (h2 : K ⊆ U), μ K)


variables {G : Type w} [measurable_space G] [group G] [topological_space G] [topological_group G]
  [borel_space G]

lemma measurable_inv : measurable (inv : G → G) :=
continuous.measurable continuous_inv

lemma measurable_mul [second_countable_topology G] : measurable (λ p : G × G, p.1 * p.2) :=
continuous.measurable continuous_mul

lemma measurable_mul_left (g : G) : measurable (λ h : G, g * h) :=
continuous.measurable $ continuous_const.mul continuous_id

lemma measurable_mul_right (g : G) : measurable (λ h : G, h * g) :=
continuous.measurable $ continuous_id.mul continuous_const

def is_left_invariant (μ : measure G) : Prop :=
∀ (g : G) {A : set G} (h : is_measurable A), μ ((λ h, g * h) ⁻¹' A) = μ A

def is_right_invariant (μ : measure G) : Prop :=
∀ (g : G) {A : set G} (h : is_measurable A), μ ((λ h, h * g) ⁻¹' A) = μ A

-- /-- A left Haar measure. -/
-- structure is_left_haar_measure (μ : measure G) : Prop :=
--   (measure_univ_pos : μ.nonzero)
--   (is_regular : μ.regular)
--   (left_invariant : is_left_invariant μ)

-- /-- A right Haar measure. -/
-- structure is_right_haar_measure (μ : measure G) : Prop :=
--   (measure_univ_pos : μ.nonzero)
--   (is_regular : μ.regular)
--   (right_invariant : is_right_invariant μ)

namespace measure

/-- The conjugate of a measure on a topological group. -/
@[nolint unused_arguments]
protected def conj (μ : measure G) : measure G :=
μ.map inv

lemma conj_apply (μ : measure G) {s : set G} (hs : is_measurable s) :
  μ.conj s = μ (inv ⁻¹' s) :=
by { unfold measure.conj, rw [measure.map_apply measurable_inv hs] }

@[simp] lemma conj_conj (μ : measure G) : μ.conj.conj = μ :=
begin
  ext1 s hs,
  rw [μ.conj.conj_apply hs, μ.conj_apply (measurable_inv.preimage hs), ←preimage_comp],
  congr, ext g, rw [function.comp_app, inv_inv],
end

variables {μ : measure G}

lemma nonzero.conj (h : μ.nonzero) : μ.conj.nonzero :=
by { dsimp [nonzero], rwa [μ.conj_apply is_measurable.univ, preimage_univ] }

lemma regular.conj [t2_space G] (h : μ.regular) : μ.conj.regular :=
begin
  split,
  { intros K hK, rw [μ.conj_apply hK.is_measurable], apply h.le_top_of_compact,
    exact (homeomorph.inv G).compact_preimage.mpr hK },
  { intros A hA, rw [μ.conj_apply hA, h.outer_regular (measurable_inv.preimage hA)],
    symmetry, apply infi_congr (preimage inv) (equiv.inv G).injective.surjective_preimage,
    intro U, apply infi_congr_Prop (homeomorph.inv G).is_open_preimage, intro hU,
    apply infi_congr_Prop,
    { apply preimage_subset_preimage_iff, rw [surjective.range_eq], apply subset_univ,
      exact (equiv.inv G).surjective },
    intro h2U, rw [μ.conj_apply hU.is_measurable] },
  { intros U hU, rw [μ.conj_apply hU.is_measurable, h.inner_regular (continuous_inv U hU)],
    symmetry,
    apply supr_congr (preimage inv) (equiv.inv G).injective.surjective_preimage,
    intro K, apply supr_congr_Prop (homeomorph.inv G).compact_preimage, intro hK,
    apply supr_congr_Prop,
    { apply preimage_subset_preimage_iff, rw [surjective.range_eq], apply subset_univ,
      exact (equiv.inv G).surjective },
    intro h2U, rw [μ.conj_apply hK.is_measurable] },
end

end measure

variables [t2_space G] {μ : measure G}

@[simp] lemma regular_conj_iff : μ.conj.regular ↔ μ.regular :=
by { refine ⟨λ h, _, measure.regular.conj⟩, rw ←μ.conj_conj, exact measure.regular.conj h }

lemma is_right_invariant_conj' (h : is_left_invariant μ) :
  is_right_invariant μ.conj :=
begin
  intros g A hA, rw [μ.conj_apply (measurable_mul_right g A hA), μ.conj_apply hA],
  convert h g⁻¹ (measurable_inv A hA) using 2,
  simp only [←preimage_comp], congr' 1, ext h, simp only [mul_inv_rev, comp_app, inv_inv]
end

lemma is_left_invariant_conj' (h : is_right_invariant μ) : is_left_invariant μ.conj :=
begin
  intros g A hA, rw [μ.conj_apply (measurable_mul_left g A hA), μ.conj_apply hA],
  convert h g⁻¹ (measurable_inv A hA) using 2,
  simp only [←preimage_comp], congr' 1, ext h, simp only [mul_inv_rev, comp_app, inv_inv]
end

@[simp] lemma is_right_invariant_conj : is_right_invariant μ.conj ↔ is_left_invariant μ :=
by { refine ⟨λ h, _, is_right_invariant_conj'⟩, rw ←μ.conj_conj, exact is_left_invariant_conj' h }

@[simp] lemma is_left_invariant_conj : is_left_invariant μ.conj ↔ is_right_invariant μ :=
by { refine ⟨λ h, _, is_left_invariant_conj'⟩, rw ←μ.conj_conj, exact is_right_invariant_conj' h }

/- we put the construction of the Haar measure in a namespace to partially hide it -/
namespace haar
/-- (K : V) -/
def index (K V : set G) : ℕ :=
Inf $ finset.card '' {t : finset G | K ⊆ ⋃ g ∈ t, (λ h, g * h) ⁻¹' V }

/-- If `K` is compact and `V` has nonempty interior, then the index `(K : V)` is well-defined,
  there is a finite set `t` satisfying the desired properties. -/
lemma index_defined {K V : set G} (hK : compact K) (hV : (interior V).nonempty) :
  ∃ n : ℕ, n ∈ finset.card '' {t : finset G | K ⊆ ⋃ g ∈ t, (λ h, g * h) ⁻¹' V } :=
begin
  cases hV with g₀ hg₀,
  rcases compact.elim_finite_subcover hK (λ g : G, interior $ (λ h, g * h) ⁻¹' V) _ _ with ⟨t, ht⟩,
  { refine ⟨t.card, t, subset.trans ht _, rfl⟩,
    apply Union_subset_Union, intro g, apply Union_subset_Union, intro hg, apply interior_subset },
  { intro g, apply is_open_interior },
  { intros g hg, rw [mem_Union], use g₀ * g⁻¹,
    apply preimage_interior_subset_interior_preimage, exact continuous_const.mul continuous_id,
    rwa [mem_preimage, inv_mul_cancel_right] }
end

lemma index_elim {K V : set G} (hK : compact K) (hV : (interior V).nonempty) :
  ∃ (t : finset G), K ⊆ (⋃ g ∈ t, (λ h, g * h) ⁻¹' V) ∧ finset.card t = index K V :=
by { have := nat.Inf_spec (index_defined hK hV), rwa [mem_image] at this }


lemma index_empty {V : set G} : index ∅ V = 0 :=
begin
  simp only [index, nat.Inf_eq_zero], left, use ∅,
  simp only [finset.card_empty, empty_subset, mem_set_of_eq, eq_self_iff_true, and_self],
end

lemma le_index_mul (K₀ : nontrivial_compacts G) {K V : set G}
  (hK : compact K) (hV : (interior V).nonempty) : index K V ≤ index K K₀.1 * index K₀.1 V :=
begin
  classical,
  rcases index_elim hK K₀.2.2 with ⟨s, h1s, h2s⟩,
  rcases index_elim K₀.2.1 hV with ⟨t, h1t, h2t⟩,
  rw [← h2s, ← h2t],
  refine le_trans (nat.Inf_le _) _,
  exact ((t.product s).image (λ p : G × G, p.1 * p.2)).card,
  { refine ⟨_, _, rfl⟩, rw [mem_set_of_eq], refine subset.trans h1s _,
    apply bUnion_subset, intros g₁ hg₁, rw preimage_subset_iff, intros g₂ hg₂,
    have := h1t hg₂,
    rcases this with ⟨_, ⟨g₃, rfl⟩, A, ⟨hg₃, rfl⟩, hV⟩, rw [mem_preimage] at hV,
    fapply mem_bUnion, exact g₃ * g₁,
    simp only [multiset.mem_erase_dup, finset.product_val, multiset.mem_product, multiset.mem_map,
      finset.image_val, prod.exists, mem_def],
    refine ⟨g₃, g₁, ⟨hg₃, hg₁⟩, rfl⟩, rw [mem_preimage], convert hV using 1, rw [mul_assoc] },
  { convert finset.card_image_le, rw [finset.card_product, mul_comm] },
end

lemma index_pos (K : nontrivial_compacts G) {V : set G} (hV : (interior V).nonempty) : 0 < index K.1 V :=
begin
  unfold index, rw [Inf_nat_def, nat.find_pos, mem_image],
  { rintro ⟨t, h1t, h2t⟩, rw [finset.card_eq_zero] at h2t, subst h2t,
    cases K.2.2 with g hg,
    show g ∈ (∅ : set G), convert h1t (interior_subset hg), symmetry, apply bUnion_empty },
  { exact index_defined K.2.1 hV }
end

lemma index_mono {K K' V : set G} (hK' : compact K') (h : K ⊆ K')
  (hV : (interior V).nonempty) : index K V ≤ index K' V :=
begin
  rcases index_elim hK' hV with ⟨s, h1s, h2s⟩,
  apply nat.Inf_le, rw [mem_image], refine ⟨s, subset.trans h h1s, h2s⟩
end

/-- prehaar -/
-- in notes: K₀ compact with non-empty interior, U open containing 1, K compact
def prehaar (K₀ U : set G) (K : compacts G) : ℝ := (index K.1 U : ℝ) / index K₀ U

lemma prehaar_nonneg (K₀ : nontrivial_compacts G) {U : set G} (K : compacts G)
  (hU : (interior U).nonempty) : 0 ≤ prehaar K₀.1 U K :=
by { apply div_nonneg; norm_cast, apply zero_le, exact index_pos K₀ hU }

lemma prehaar_le_index (K₀ : nontrivial_compacts G) {U : set G} (K : compacts G)
  (hU : (interior U).nonempty) : prehaar K₀.1 U K ≤ index K.1 K₀.1 :=
begin
  unfold prehaar, rw [div_le_iff]; norm_cast,
  { apply le_index_mul K₀ K.2 hU },
  { exact index_pos K₀ hU }
end

/-- haar_product X -/
def haar_product (K₀ : set G) : set (compacts G → ℝ) :=
set.pi set.univ (λ K, Icc 0 $ index K.1 K₀)

lemma prehaar_mem_haar_product (K₀ : nontrivial_compacts G) {U : set G}
  (hU : (interior U).nonempty) : prehaar K₀.1 U ∈ haar_product K₀.1 :=
by { rintro ⟨K, hK⟩ h2K, rw [mem_Icc],
     exact ⟨prehaar_nonneg K₀ _ hU, prehaar_le_index K₀ _ hU⟩ }

/-- C -/
def CC (K₀ : set G) (V : open_nhds_of (1 : G)) : set (compacts G → ℝ) :=
closure $ prehaar K₀ '' { U : set G | U ⊆ V ∧ is_open U ∧ (1 : G) ∈ U }

lemma nonempty_Inter_CC (K₀ : nontrivial_compacts G) :
  (haar_product K₀.1 ∩ ⋂ (V : open_nhds_of (1 : G)), CC K₀.1 V).nonempty :=
begin
  have : compact (haar_product K₀.1), { apply compact_univ_pi, intro K, apply compact_Icc },
  rw [← ne_empty_iff_nonempty],
  have := compact.elim_finite_subfamily_closed this (CC K₀) (λ s, is_closed_closure), apply mt this,
  rintro ⟨t, h1t⟩, rw [← not_nonempty_iff_eq_empty] at h1t, apply h1t,
  let V₀ := ⋂ (V ∈ t), (V : open_nhds_of 1).1,
  have h1V₀ : is_open V₀,
  { apply is_open_bInter, apply finite_mem_finset, rintro ⟨V, hV⟩ h2V, exact hV.1 },
  have h2V₀ : (1 : G) ∈ V₀, { rw mem_Inter, rintro ⟨V, hV⟩, rw mem_Inter, intro h2V, exact hV.2 },
  refine ⟨prehaar K₀ V₀, _⟩,
  split,
  { apply prehaar_mem_haar_product K₀, use 1, rwa interior_eq_of_open h1V₀ },
  { rw mem_Inter, rintro ⟨V, hV⟩, rw mem_Inter, intro h2V, apply subset_closure,
    apply mem_image_of_mem, rw [mem_set_of_eq],
    exact ⟨subset.trans (Inter_subset _ ⟨V, hV⟩) (Inter_subset _ h2V), h1V₀, h2V₀⟩ },
end

/-- the Haar measure on compact sets -/
def haar_measure' (K₀ : nontrivial_compacts G) (K : compacts G) : nnreal :=
⟨classical.some (nonempty_Inter_CC K₀) K, sorry⟩


end haar
open haar

/-- the Haar measure on `G` -/
def haar_measure (K₀ : nontrivial_compacts G) : measure G :=
sorry

lemma haar_measure_eq_haar_measure' (K₀ : nontrivial_compacts G) (K : compacts G) :
  haar_measure K₀ K = haar_measure' K₀ K :=
sorry

lemma is_left_invariant_haar_measure (K₀ : nontrivial_compacts G) (K : compacts G) :
  is_left_invariant (haar_measure K₀) :=
sorry

lemma nonzero_haar_measure (K₀ : nontrivial_compacts G) (K : compacts G) :
  (haar_measure K₀).nonzero :=
sorry

lemma regular_haar_measure (K₀ : nontrivial_compacts G) (K : compacts G) :
  (haar_measure K₀).regular :=
sorry



end measure_theory
-- #lint