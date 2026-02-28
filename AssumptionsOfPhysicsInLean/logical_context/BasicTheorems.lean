import AssumptionsOfPhysicsInLean.logical_context.Basic
import AssumptionsOfPhysicsInLean.logical_context.Order
import AssumptionsOfPhysicsInLean.logical_context.Equiv
import Mathlib.Data.Fintype.Order

variable {C : LogicalContext}
open LogicalContext
open Connectives


theorem narrower_antisymm {s₁ s₂ : C.Statement} :
  s₁ ≼ s₂ → s₂ ≼ s₁ → s₁ ≡ s₂ := by
  intro h1 h2 a ha
  specialize h1 a ha
  specialize h2 a ha
  by_cases hs1 : a s₁
  · simp_all only [forall_const]
  simp_all only [Bool.false_eq_true, IsEmpty.forall_iff, imp_false, Bool.not_eq_true]

theorem Equiv_to_narrower {s₁ s₂ : C.Statement} : s₁ ≡ s₂ → s₁ ≼ s₂ := by
simp_all

theorem pnarrower_iff_narrower_not_broader (s₁ s₂ : C.Statement) :
  s₁ ≺ s₂ ↔ (s₁ ≼ s₂) ∧ ¬(s₂ ≼ s₁) := by
constructor
· intro ⟨h1,h2⟩
  constructor
  · exact h1
  intro h3
  apply h2
  exact narrower_antisymm h1 h3
intro ⟨h1,h2⟩
constructor
· simp_all only [narrower, not_forall, Bool.not_eq_true, implies_true]
intro h3
unfold narrower at h2; push_neg at h2
obtain ⟨a, ha, h2⟩ := h2
simp_all only [narrower, equivalent, ne_eq, Bool.not_eq_true,
  Bool.eq_true_and_eq_false_self]

namespace CongreunceTheorems

theorem Narrower_congr {s₁ s₂ s₁' s₂' : C.Statement} :
(s₁ ≡ s₁') → (s₂ ≡ s₂') → (s₁ ≼ s₂) = (s₁' ≼ s₂') := by
simp_all
theorem Not_congr {s t : C.Statement} :
  s ≡ t → (¬s) ≡ (¬t) := by
intro hcongr a ha
rw [Not_spec a ha, Not_spec a ha, hcongr a ha]

theorem And_congr {s t s' t' : C.Statement} :
  s ≡ s' →
  t ≡ t' →
  s ∧ t ≡ s' ∧ t' := by
  intro h1 h2 a ha
  rw [And_spec a ha, And_spec a ha]
  specialize h1 a ha
  specialize h2 a ha
  rw [h1, h2]


theorem Or_congr {s t s' t' : C.Statement} :
  s ≡ s' →
  t ≡ t' →
  s ∨ t ≡ s' ∨ t' := by
  intro h1 h2 a ha
  simp_all only [equivalent, Connectives.Or_spec]

theorem Any_congr (S T : Set C.Statement) :
  (∀ s t, s ≡ t → (s ∈ S ↔ t ∈ T)) →
  Any S ≡ Any T := by
intro h
have hST : S = T := by
  apply Set.ext
  intro s
  exact h s s equiv_refl
subst hST
rfl

theorem All_congr (S T : Set C.Statement) :
  (∀ s t, s ≡ t → (s ∈ S ↔ t ∈ T)) →
  All S ≡ All T := by
intro h
have hST : S = T := by
  · apply Set.ext
    intro s
    apply h s s equiv_refl
subst hST
rfl

end CongreunceTheorems

namespace AlgebraicTheorems

theorem And_comm {a b : C.Statement} : a ∧ b ≡ b ∧ a := by
intro f hf
rw [And_spec f hf, And_spec f hf]
exact Bool.and_comm _ _

theorem and_assoc {a b c : C.Statement} : ((a ∧ b) ∧ c) ≡ (a ∧ (b ∧ c)) := by
intro f hf; repeat rw [And_spec f hf]
exact Bool.and_assoc _ _ _



theorem Or_comm {a b : C.Statement} : a ∨ b ≡ b ∨ a := by
intro f hf
rw [Or_spec f hf, Or_spec f hf]
exact Bool.or_comm _ _

theorem Or_assoc {a b c : C.Statement} : ((a ∨ b) ∨ c) ≡ (a ∨ (b ∨ c)) := by
intro f hf; repeat rw [Or_spec f hf]
exact Bool.or_assoc _ _ _

theorem narrower_Or_left {a b : C.Statement} : a ≼ a ∨ b := by
intro f hf ha
rw [Or_spec f hf]
exact Bool.or_inl ha

theorem narrower_Or_right {a b : C.Statement} : b ≼ a ∨ b := by
intro f hf hb
rw [Or_spec f hf]
exact Bool.or_inr hb

theorem Or_narrower {a b c : C.Statement} : a ≼ c → b ≼ c → a ∨ b ≼ c := by
intro h1 h2 f hf h3
specialize h1 f hf
specialize h2 f hf
rw [Or_spec f hf] at h3
simp only [Bool.or_eq_true] at h3
cases h3 with
| inl ha => exact h1 ha
| inr hb => exact h2 hb


theorem And_narrower_left {a b : C.Statement} : a ∧ b ≼ a := by
intro f hf h1
rw [And_spec f hf] at h1
exact Bool.and_elim_left h1

theorem And_narrower_right {a b : C.Statement} : a ∧ b ≼ b := by
intro f hf h1
rw [And_spec f hf] at h1
exact Bool.and_elim_right h1

theorem narrower_And (a b c : C.Statement) : a ≼ b → a ≼ c → a ≼ b ∧ c := by
intro h1 h2 f hf ha
specialize h1 f hf
specialize h2 f hf
rw [And_spec f hf]
simp only [Bool.and_eq_true]
exact ⟨h1 ha, h2 ha⟩

theorem equiv_And_Or {a b c : C.Statement} :
  (a ∨ b) ∧ (a ∨ c) ≡ a ∨ (b ∧ c) := by
intro f hf
rw [And_spec f hf, Or_spec f hf, Or_spec f hf, Or_spec f hf, And_spec f hf ]
exact Eq.symm (Bool.or_and_distrib_left (f a) (f b) (f c))

theorem And_Not_equiv_bottom {s : C.Statement} : s ∧ ¬s ≡ bottom := by
intro a ha
rw [And_spec a ha, Not_spec a ha, bottom_false a ha]
exact Bool.and_not_self (a s)



theorem top_equiv_Or_Not {s : C.Statement} : top ≡ s ∨ ¬s := by
intro a ha
rw [top_true a ha, Or_spec a ha, Not_spec a ha]
exact Eq.symm (Bool.or_not_self (a s))

theorem narrower_top {s : C.Statement} : s ≼ top := by
intro a ha _
rw [top_true a ha]

theorem bottom_narrower {s : C.Statement} : bottom ≼ s := by
intro a ha hbottom
rw [bottom_false a ha ] at hbottom
contradiction


end AlgebraicTheorems
