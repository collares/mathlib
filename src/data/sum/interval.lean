/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.sum.order
import order.locally_finite

/-!
# Finite intervals in a disjoint union

This file provides the `locally_finite_order` instance for the disjoint sum and linear sum of two
orders and calculates the cardinality of their finite intervals.
-/

open function sum

lemma or_iff_left {a b : Prop} (hb : ¬ b) : a ∨ b ↔ a := ⟨λ h, h.resolve_right hb, or.inl⟩
lemma or_iff_right {a b : Prop} (ha : ¬ a) : a ∨ b ↔ b := ⟨λ h, h.resolve_left ha, or.inr⟩

namespace multiset
section disj_sum
variables {α β : Type*} (s : multiset α) (t : multiset β)

/-- Disjoint sum of multisets. -/
def disj_sum : multiset (α ⊕ β) := s.map inl + t.map inr

@[simp] lemma zero_disj_sum : (0 : multiset α).disj_sum t = t.map inr := zero_add _
@[simp] lemma disj_sum_zero : s.disj_sum (0 : multiset β) = s.map inl := add_zero _

variables {s t} {s₁ s₂ : multiset α} {t₁ t₂ : multiset β} {a : α} {b : β} {x : α ⊕ β}

@[simp] lemma card_disj_sum : (s.disj_sum t).card = s.card + t.card :=
by rw [disj_sum, card_add, card_map, card_map]

lemma mem_disj_sum : x ∈ s.disj_sum t ↔ (∃ a, a ∈ s ∧ inl a = x) ∨ ∃ b, b ∈ t ∧ inr b = x :=
by simp_rw [disj_sum, mem_add, mem_map]

@[simp] lemma inl_mem_disj_sum : inl a ∈ s.disj_sum t ↔ a ∈ s :=
begin
  rw [mem_disj_sum, or_iff_left],
  simp only [exists_eq_right],
  rintro ⟨b, _, hb⟩,
  exact inr_ne_inl hb,
end

@[simp] lemma inr_mem_disj_sum : inr b ∈ s.disj_sum t ↔ b ∈ t :=
begin
  rw [mem_disj_sum, or_iff_right],
  simp only [exists_eq_right],
  rintro ⟨a, _, ha⟩,
  exact inl_ne_inr ha,
end

@[simp] lemma map_lt_map {f : α → β} {s t : multiset α} (h : s < t) : s.map f < t.map f :=
begin
  refine (map_le_map h.le).lt_of_not_le (λ H, h.ne $ eq_of_le_of_card_le h.le _),
  rw [←s.card_map f, ←t.card_map f],
  exact card_le_of_le H,
end

lemma map_strict_mono (f : α → β) : strict_mono (map f) := λ _ _, map_lt_map

lemma disj_sum_mono (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) : s₁.disj_sum t₁ ≤ s₂.disj_sum t₂ :=
add_le_add (map_le_map hs) (map_le_map ht)

lemma disj_sum_strict_mono (hs : s₁ < s₂) (ht : t₁ < t₂) : s₁.disj_sum t₁ < s₂.disj_sum t₂ :=
add_lt_add (map_lt_map hs) (map_lt_map ht)

lemma disj_sum_mono_left (hs : s₁ ≤ s₂) (t : multiset β) : s₁.disj_sum t ≤ s₂.disj_sum t :=
add_le_add_right (map_le_map hs) _

lemma disj_sum_mono_right (s : multiset α) :
  monotone (s.disj_sum : multiset β → multiset (α ⊕ β)) :=
λ t₁ t₂ ht, add_le_add_left (map_le_map ht) _

protected lemma nodup.disj_sum (hs : s.nodup) (ht : t.nodup) : (s.disj_sum t).nodup :=
begin
  refine (multiset.nodup_add_of_nodup (multiset.nodup_map inl_injective hs) $
    multiset.nodup_map inr_injective ht).2 (λ x hs ht, _),
  rw multiset.mem_map at hs ht,
  obtain ⟨a, _, rfl⟩ := hs,
  obtain ⟨b, _, h⟩ := ht,
  exact inr_ne_inl h,
end

end disj_sum
end multiset

namespace finset
variables {α₁ α₂ β₁ β₂ γ₁ γ₂ : Type*}

section disj_sum
variables {α β : Type*} (s : finset α) (t : finset β)

/-- Disjoint sum of finsets. -/
def disj_sum : finset (α ⊕ β) := ⟨s.1.disj_sum t.1, s.2.disj_sum t.2⟩

@[simp] lemma val_disj_sum : (s.disj_sum t).1 = s.1.disj_sum t.1 := rfl

variables {s t} {a : α} {b : β} {x : α ⊕ β}

lemma mem_disj_sum : x ∈ s.disj_sum t ↔ (∃ a, a ∈ s ∧ inl a = x) ∨ ∃ b, b ∈ t ∧ inr b = x :=
multiset.mem_disj_sum

@[simp] lemma inl_mem_disj_sum : inl a ∈ s.disj_sum t ↔ a ∈ s := multiset.inl_mem_disj_sum
@[simp] lemma inr_mem_disj_sum : inr b ∈ s.disj_sum t ↔ b ∈ t := multiset.inr_mem_disj_sum

end disj_sum

section sum_lift₂
variables (f f₁ g₁ : α₁ → β₁ → finset γ₁) (g f₂ g₂ : α₂ → β₂ → finset γ₂)

/-- Lifts maps `α₁ → β₁ → finset γ₁` and `α₂ → β₂ → finset γ₂` to a map
`α₁ ⊕ α₂ → β₁ ⊕ β₂ → finset (γ₁ ⊕ γ₂)`. Could be generalized to alternative monads if we can make
sure to keep computability and universe polymorphism. -/
def sum_lift₂ : Π (a : α₁ ⊕ α₂) (b : β₁ ⊕ β₂), finset (γ₁ ⊕ γ₂)
| (inl a) (inl b) := (f a b).map ⟨_, inl_injective⟩
| (inl a) (inr b) := ∅
| (inr a) (inl b) := ∅
| (inr a) (inr b) := (g a b).map ⟨_, inr_injective⟩

@[simp] lemma sum_lift₂_inl_inl (a : α₁) (b : β₁) :
  sum_lift₂ f g (inl a) (inl b) = (f a b).map ⟨_, inl_injective⟩ := rfl

@[simp] lemma sum_lift₂_inl_inr (a : α₁) (b : β₂) : sum_lift₂ f g (inl a) (inr b) = ∅ := rfl
@[simp] lemma sum_lift₂_inr_inl (a : α₂) (b : β₁) : sum_lift₂ f g (inr a) (inl b) = ∅ := rfl

@[simp] lemma sum_lift₂_inr_inr (a : α₂) (b : β₂) :
  sum_lift₂ f g (inr a) (inr b) = (g a b).map ⟨_, inr_injective⟩ := rfl

variables {f f₁ g₁ g f₂ g₂} {a : α₁ ⊕ α₂} {b : β₁ ⊕ β₂} {c : γ₁ ⊕ γ₂}

lemma mem_sum_lift₂ :
  c ∈ sum_lift₂ f g a b ↔ (∃ a₁ b₁ c₁, a = inl a₁ ∧ b = inl b₁ ∧ c = inl c₁ ∧ c₁ ∈ f a₁ b₁)
    ∨ ∃ a₂ b₂ c₂, a = inr a₂ ∧ b = inr b₂ ∧ c = inr c₂ ∧ c₂ ∈ g a₂ b₂ :=
begin
  split,
  { cases a; cases b,
    { rw [sum_lift₂, mem_map],
      rintro ⟨c, hc, rfl⟩,
      exact or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩ },
    { refine λ h, (not_mem_empty _ h).elim },
    { refine λ h, (not_mem_empty _ h).elim },
    { rw [sum_lift₂, mem_map],
      rintro ⟨c, hc, rfl⟩,
      exact or.inr ⟨a, b, c, rfl, rfl, rfl, hc⟩ } },
  { rintro (⟨a, b, c, rfl, rfl, rfl, hc⟩ | ⟨a, b, c, rfl, rfl, rfl, hc⟩); exact mem_map_of_mem _ hc }
end

lemma inl_mem_sum_lift₂ {c₁ : γ₁} :
  inl c₁ ∈ sum_lift₂ f g a b ↔ ∃ a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ c₁ ∈ f a₁ b₁ :=
begin
  rw [mem_sum_lift₂, or_iff_left],
  simp only [exists_and_distrib_left, exists_eq_left'],
  rintro ⟨_, _, c₂, _, _, h, _⟩,
  exact inl_ne_inr h,
end

lemma inr_mem_sum_lift₂ {c₂ : γ₂} :
  inr c₂ ∈ sum_lift₂ f g a b ↔ ∃ a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ c₂ ∈ g a₂ b₂ :=
begin
  rw [mem_sum_lift₂, or_iff_right],
  simp only [exists_and_distrib_left, exists_eq_left'],
  rintro ⟨_, _, c₂, _, _, h, _⟩,
  exact inr_ne_inl h,
end

lemma sum_lift₂_nonempty :
  (sum_lift₂ f g a b).nonempty ↔ (∃ a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ (f a₁ b₁).nonempty)
    ∨ ∃ a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ (g a₂ b₂).nonempty :=
begin
  split,
  { rintro ⟨c | c, hc⟩,
    { rw inl_mem_sum_lift₂ at hc,
      obtain ⟨a, b, ha, hb, hc⟩ := hc,
      exact or.inl ⟨a, b, ha, hb, c, hc⟩ },
    { rw inr_mem_sum_lift₂ at hc,
      obtain ⟨a, b, ha, hb, hc⟩ := hc,
      exact or.inr ⟨a, b, ha, hb, c, hc⟩ } },
  { rintro (⟨a, b, rfl, rfl, h⟩ | ⟨a, b, rfl, rfl, h⟩); exact h.map }
end

lemma sum_lift₂_eq_empty :
  (sum_lift₂ f g a b) = ∅ ↔ (∀ a₁ b₁, a = inl a₁ → b = inl b₁ → f a₁ b₁ = ∅)
    ∧ ∀ a₂ b₂, a = inr a₂ → b = inr b₂ → g a₂ b₂ = ∅ :=
begin
  refine ⟨λ h, ⟨_, _⟩, λ h, _⟩,
  any_goals { rintro a b rfl rfl, exact map_eq_empty.1 h },
  cases a; cases b,
  { exact map_eq_empty.2 (h.1 _ _ rfl rfl) },
  { refl },
  { refl },
  { exact map_eq_empty.2 (h.2 _ _ rfl rfl) }
end

lemma sum_lift₂_mono (h₁ : ∀ a b, f₁ a b ⊆ g₁ a b) (h₂ : ∀ a b, f₂ a b ⊆ g₂ a b) (a : α₁ ⊕ α₂)
  (b : β₁ ⊕ β₂) :
  sum_lift₂ f₁ f₂ a b ⊆ sum_lift₂ g₁ g₂ a b :=
begin
  cases a; cases b,
  { exact map_subset_map.2 (h₁ _ _) },
  { exact subset.refl _},
  { exact subset.refl _},
  { exact map_subset_map.2 (h₂ _ _) }
end

end sum_lift₂

section sum_lex_lift
variables (f₁ : α₁ → β₁ → finset γ₁) (f₂ : α₂ → β₂ → finset γ₂)
          (g₁ : α₁ → β₂ → finset γ₁) (g₂ : α₁ → β₂ → finset γ₂)

/-- Lifts maps `α₁ → β₁ → finset γ₁`, `α₂ → β₂ → finset γ₂`, `α₁ → β₂ → finset γ₁`,
`α₂ → β₂ → finset γ₂`  to a map `α₁ ⊕ α₂ → β₁ ⊕ β₂ → finset (γ₁ ⊕ γ₂)`. Could be generalized to
alternative monads if we can make sure to keep computability and universe polymorphism. -/
def sum_lex_lift : Π (a : α₁ ⊕ α₂) (b : β₁ ⊕ β₂), finset (γ₁ ⊕ γ₂)
| (inl a) (inl b) := (f₁ a b).map ⟨_, inl_injective⟩
| (inl a) (inr b) := (g₁ a b).disj_sum (g₂ a b)
| (inr a) (inl b) := ∅
| (inr a) (inr b) := (f₂ a b).map ⟨_, inr_injective⟩

@[simp] lemma sum_lex_lift_inl_inl (a : α₁) (b : β₁) :
  sum_lex_lift f₁ f₂ g₁ g₂ (inl a) (inl b) = (f₁ a b).map ⟨_, inl_injective⟩ := rfl

@[simp] lemma sum_lex_lift_inl_inr (a : α₁) (b : β₂) :
  sum_lex_lift f₁ f₂ g₁ g₂ (inl a) (inr b) = (g₁ a b).disj_sum (g₂ a b) := rfl

@[simp] lemma sum_lex_lift_inr_inl (a : α₂) (b : β₁) :
  sum_lex_lift f₁ f₂ g₁ g₂ (inr a) (inl b) = ∅ := rfl

@[simp] lemma sum_lex_lift_inr_inr (a : α₂) (b : β₂) :
  sum_lex_lift f₁ f₂ g₁ g₂ (inr a) (inr b) = (f₂ a b).map ⟨_, inr_injective⟩ := rfl

variables {f₁ g₁ f₂ g₂} {a : α₁ ⊕ α₂} {b : β₁ ⊕ β₂} {c : γ₁ ⊕ γ₂}

lemma mem_sum_lex_lift :
  c ∈ sum_lex_lift f₁ f₂ g₁ g₂ a b ↔
    (∃ a₁ b₁ c₁, a = inl a₁ ∧ b = inl b₁ ∧ c = inl c₁ ∧ c₁ ∈ f₁ a₁ b₁) ∨
    (∃ a₁ b₂ c₁, a = inl a₁ ∧ b = inr b₂ ∧ c = inl c₁ ∧ c₁ ∈ g₁ a₁ b₂) ∨
    (∃ a₁ b₂ c₂, a = inl a₁ ∧ b = inr b₂ ∧ c = inr c₂ ∧ c₂ ∈ g₂ a₁ b₂) ∨
     ∃ a₂ b₂ c₂, a = inr a₂ ∧ b = inr b₂ ∧ c = inr c₂ ∧ c₂ ∈ f₂ a₂ b₂ :=
begin
  split,
  { cases a; cases b,
    { rw [sum_lex_lift, mem_map],
      rintro ⟨c, hc, rfl⟩,
      exact or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩ },
    { refine λ h, (mem_disj_sum.1 h).elim _ _,
      { rintro ⟨c, hc, rfl⟩,
        } },
    { refine λ h, (not_mem_empty _ h).elim },
    { rw [sum_lex_lift, mem_map],
      rintro ⟨c, hc, rfl⟩,
      exact or.inr ⟨a, b, c, rfl, rfl, rfl, hc⟩ } },
  { rintro (⟨a, b, c, rfl, rfl, rfl, hc⟩ | ⟨a, b, c, rfl, rfl, rfl, hc⟩); exact mem_map_of_mem _ hc }
end

lemma inl_mem_sum_lex_lift {c₁ : γ₁} :
  inl c₁ ∈ sum_lex_lift f₁ f₂ g₁ g₂ a b ↔ ∃ a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ c₁ ∈ f a₁ b₁ :=
begin
  rw [mem_sum_lex_lift, or_iff_left],
  simp only [exists_and_distrib_left, exists_eq_left'],
  rintro ⟨_, _, c₂, _, _, h, _⟩,
  exact inl_ne_inr h,
end

lemma inr_mem_sum_lex_lift {c₂ : γ₂} :
  inr c₂ ∈ sum_lex_lift f₁ f₂ g₁ g₂ a b ↔ ∃ a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ c₂ ∈ g a₂ b₂ :=
begin
  rw [mem_sum_lex_lift, or_iff_right],
  simp only [exists_and_distrib_left, exists_eq_left'],
  rintro ⟨_, _, c₂, _, _, h, _⟩,
  exact inr_ne_inl h,
end

lemma sum_lex_lift_nonempty :
  (sum_lex_lift f₁ f₂ g₁ g₂ a b).nonempty ↔ (∃ a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ (f a₁ b₁).nonempty)
    ∨ ∃ a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ (g a₂ b₂).nonempty :=
begin
  split,
  { rintro ⟨c | c, hc⟩,
    { rw inl_mem_sum_lex_lift at hc,
      obtain ⟨a, b, ha, hb, hc⟩ := hc,
      exact or.inl ⟨a, b, ha, hb, c, hc⟩ },
    { rw inr_mem_sum_lex_lift at hc,
      obtain ⟨a, b, ha, hb, hc⟩ := hc,
      exact or.inr ⟨a, b, ha, hb, c, hc⟩ } },
  { rintro (⟨a, b, rfl, rfl, h⟩ | ⟨a, b, rfl, rfl, h⟩); exact h.map }
end

lemma sum_lex_lift_eq_empty :
  (sum_lex_lift f₁ f₂ g₁ g₂ a b) = ∅ ↔ (∀ a₁ b₁, a = inl a₁ → b = inl b₁ → f a₁ b₁ = ∅)
    ∧ ∀ a₂ b₂, a = inr a₂ → b = inr b₂ → g a₂ b₂ = ∅ :=
begin
  refine ⟨λ h, ⟨_, _⟩, λ h, _⟩,
  any_goals { rintro a b rfl rfl, exact map_eq_empty.1 h },
  cases a; cases b,
  { exact map_eq_empty.2 (h.1 _ _ rfl rfl) },
  { refl },
  { refl },
  { exact map_eq_empty.2 (h.2 _ _ rfl rfl) }
end

lemma sum_lex_lift_mono (h₁ : ∀ a b, f₁ a b ⊆ g₁ a b) (h₂ : ∀ a b, f₂ a b ⊆ g₂ a b) (a : α₁ ⊕ α₂)
  (b : β₁ ⊕ β₂) :
  sum_lex_lift f₁ f₂ a b ⊆ sum_lex_lift g₁ g₂ a b :=
begin
  cases a; cases b,
  { exact map_subset_map.2 (h₁ _ _) },
  { exact subset.refl _},
  { exact subset.refl _},
  { exact map_subset_map.2 (h₂ _ _) }
end



end sum_lex_lift
end finset

open finset function

namespace sum
variables {α β : Type*}

/-! ### Disjoint sum of orders -/

section disjoint
variables [preorder α] [preorder β] [locally_finite_order α] [locally_finite_order β]

instance : locally_finite_order (α ⊕ β) :=
{ finset_Icc := sum_lift₂ Icc Icc,
  finset_Ico := sum_lift₂ Ico Ico,
  finset_Ioc := sum_lift₂ Ioc Ioc,
  finset_Ioo := sum_lift₂ Ioo Ioo,
  finset_mem_Icc := by rintro (a | a) (b | b) (x | x); simp,
  finset_mem_Ico := by rintro (a | a) (b | b) (x | x); simp,
  finset_mem_Ioc := by rintro (a | a) (b | b) (x | x); simp,
  finset_mem_Ioo := by rintro (a | a) (b | b) (x | x); simp }

variables (a₁ a₂ : α) (b₁ b₂ : β) (a b : α ⊕ β)

lemma Icc_inl_inl : Icc (inl a₁ : α ⊕ β) (inl a₂) = (Icc a₁ a₂).map ⟨_, inl_injective⟩ := rfl
lemma Ico_inl_inl : Ico (inl a₁ : α ⊕ β) (inl a₂) = (Ico a₁ a₂).map ⟨_, inl_injective⟩ := rfl
lemma Ioc_inl_inl : Ioc (inl a₁ : α ⊕ β) (inl a₂) = (Ioc a₁ a₂).map ⟨_, inl_injective⟩ := rfl
lemma Ioo_inl_inl : Ioo (inl a₁ : α ⊕ β) (inl a₂) = (Ioo a₁ a₂).map ⟨_, inl_injective⟩ := rfl
@[simp] lemma Icc_inl_inr : Icc (inl a₁) (inr b₂) = ∅ := rfl
@[simp] lemma Ico_inl_inr : Ico (inl a₁) (inr b₂) = ∅ := rfl
@[simp] lemma Ioc_inl_inr : Ioc (inl a₁) (inr b₂) = ∅ := rfl
@[simp] lemma Ioo_inl_inr : Ioo (inl a₁) (inr b₂) = ∅ := rfl
@[simp] lemma Icc_inr_inl : Icc (inr b₁) (inl a₂) = ∅ := rfl
@[simp] lemma Ico_inr_inl : Ico (inr b₁) (inl a₂) = ∅ := rfl
@[simp] lemma Ioc_inr_inl : Ioc (inr b₁) (inl a₂) = ∅ := rfl
@[simp] lemma Ioo_inr_inl : Ioo (inr b₁) (inl a₂) = ∅ := rfl
lemma Icc_inr_inr : Icc (inr b₁ : α ⊕ β) (inr b₂) = (Icc b₁ b₂).map ⟨_, inr_injective⟩ := rfl
lemma Ico_inr_inr : Ico (inr b₁ : α ⊕ β) (inr b₂) = (Ico b₁ b₂).map ⟨_, inr_injective⟩ := rfl
lemma Ioc_inr_inr : Ioc (inr b₁ : α ⊕ β) (inr b₂) = (Ioc b₁ b₂).map ⟨_, inr_injective⟩ := rfl
lemma Ioo_inr_inr : Ioo (inr b₁ : α ⊕ β) (inr b₂) = (Ioo b₁ b₂).map ⟨_, inr_injective⟩ := rfl

end disjoint

/-! ### Lexicographical sum of orders -/

namespace lex
variables [preorder α] [preorder β] [order_top α] [order_bot β] [locally_finite_order α]
  [locally_finite_order β]

instance locally_finite_order : locally_finite_order (α ⊕ₗ β) :=
{ finset_Icc := sum_lex_lift Icc Icc (λ a _, Ici a) (λ _, Iic),
  finset_Ico := sum_lex_lift Ico Ico (λ a _, Ici a) (λ _, Iio),
  finset_Ioc := sum_lex_lift Ioc Ioc (λ a _, Ioi a) (λ _, Iic),
  finset_Ioo := sum_lex_lift Ioo Ioo (λ a _, Ioi a) (λ _, Iio),
  finset_mem_Icc := _,
  finset_mem_Ico := _,
  finset_mem_Ioc := _,
  finset_mem_Ioo := _ }

variables (a a₁ a₂ : α) (b b₁ b₂ : β)

lemma Icc_inl_inl : Icc (inlₗ a₁ : α ⊕ₗ β) (inlₗ a₂) = (Icc a₁ a₂).map ⟨_, inl_injective⟩ := rfl
lemma Ico_inl_inl : Ico (inlₗ a₁ : α ⊕ₗ β) (inlₗ a₂) = (Ico a₁ a₂).map ⟨_, inl_injective⟩ := rfl
lemma Ioc_inl_inl : Ioc (inlₗ a₁ : α ⊕ₗ β) (inlₗ a₂) = (Ioc a₁ a₂).map ⟨_, inl_injective⟩ := rfl
lemma Ioo_inl_inl : Ioo (inlₗ a₁ : α ⊕ₗ β) (inlₗ a₂) = (Ioo a₁ a₂).map ⟨_, inl_injective⟩ := rfl
@[simp] lemma Icc_inl_inr : Icc (inlₗ a) (inrₗ b) = (Ici a).disj_sum (Iic b) := rfl
@[simp] lemma Ico_inl_inr : Ico (inlₗ a) (inrₗ b) = (Ici a).disj_sum (Iio b) := rfl
@[simp] lemma Ioc_inl_inr : Ioc (inlₗ a) (inrₗ b) = (Ioi a).disj_sum (Iic b) := rfl
@[simp] lemma Ioo_inl_inr : Ioo (inlₗ a) (inrₗ b) = (Ioi a).disj_sum (Iio b) := rfl
@[simp] lemma Icc_inr_inl : Icc (inrₗ b) (inlₗ a) = ∅ := rfl
@[simp] lemma Ico_inr_inl : Ico (inrₗ b) (inlₗ a) = ∅ := rfl
@[simp] lemma Ioc_inr_inl : Ioc (inrₗ b) (inlₗ a) = ∅ := rfl
@[simp] lemma Ioo_inr_inl : Ioo (inrₗ b) (inlₗ a) = ∅ := rfl
lemma Icc_inr_inr : Icc (inrₗ b₁ : α ⊕ₗ β) (inrₗ b₂) = (Icc b₁ b₂).map ⟨_, inr_injective⟩ := rfl
lemma Ico_inr_inr : Ico (inrₗ b₁ : α ⊕ₗ β) (inrₗ b₂) = (Ico b₁ b₂).map ⟨_, inr_injective⟩ := rfl
lemma Ioc_inr_inr : Ioc (inrₗ b₁ : α ⊕ₗ β) (inrₗ b₂) = (Ioc b₁ b₂).map ⟨_, inr_injective⟩ := rfl
lemma Ioo_inr_inr : Ioo (inrₗ b₁ : α ⊕ₗ β) (inrₗ b₂) = (Ioo b₁ b₂).map ⟨_, inr_injective⟩ := rfl

end lex
end sum
