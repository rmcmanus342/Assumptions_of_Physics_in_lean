import AssumptionsOfPhysicsInLean.logical_context.Basic
import AssumptionsOfPhysicsInLean.logical_context.Equiv
import AssumptionsOfPhysicsInLean.logical_context.Connectives

variable {C : LogicalContext}
open LogicalContext
open Connectives

@[simp] def narrower (s₁ s₂ : C.Statement) := ∀a ∈ C.possible, a s₁ → a s₂
infix:25 " ≼ " => narrower
@[simp] def proper_narrower (s₁ s₂ : C.Statement) := (s₁ ≼ s₂) ∧ ¬(s₁ ≡ s₂)
infix:25 " ≺" => proper_narrower
@[simp] def broader (s₁ s₂ : C.Statement) := s₂ ≼ s₁
infix:25 " ≽ " => broader
@[simp] def proper_broader (s₁ s₂ : C.Statement) := (s₁ ≽ s₂) ∧ ¬(s₁ ≡ s₂)
infix:25 " ≻ " => proper_broader
@[simp] def compatible (s₁ s₂ : C.Statement) :=
  ∃a ∈ C.possible, a s₁ = true ∧ a s₂ = true --idk if this is right
infix:25 " ≍ " => compatible

def independent (s : C.Statement) (T : ι → C.Statement) : Prop := sorry


--and also some minimal theorems on this as well as the instances of these relations

@[refl, simp]
theorem narrower_refl {s : C.Statement} : s ≼ s := by
intro a ha
exact id

@[trans, simp]
theorem narrower_trans {a b c : C.Statement} :
  a ≼ b → b ≼ c → a ≼ c := by
intro h1 h2 f hf
specialize h1 f hf
specialize h2 f hf
trans
· exact h1
· exact h2


instance narrower_is_preorder : Preorder C.Statement where
  le := narrower
  le_refl := @narrower_refl C
  le_trans := @narrower_trans C


@[refl, simp]
theorem broader_refl {s : C.Statement} : s ≽ s := by
intro a ha
exact id


@[trans, simp]
theorem broader_trans {a b c : C.Statement} :
  a ≽ b → b ≽ c → a ≽ c := by
intro h1 h2 f hf
trans
· exact h2 f hf
· exact h1 f hf

theorem narrower_of_narrower_of_equiv {s₁ s₂ s₃ : C.Statement}
(h1 : s₁ ≼ s₂) (h2 : s₂ ≡ s₃) : s₁ ≼ s₃ := by simp_all

theorem narrower_iff_And_Not_equiv_bottom (s₁ s₂ : C.Statement) :
  s₁ ≼ s₂ ↔ s₁ ∧ ¬s₂≡ LogicalContext.Connectives.bottom := by simp_all



theorem narrower_iff_self_And_equiv_self (s₁ s₂ : C.Statement) :
  s₁ ≼ s₂ ↔ s₁ ∧ s₂ ≡ s₁ := by simp_all


theorem narrower_iff_Or_self_equiv_self (s₁ s₂ : C.Statement) :
  s₁ ≼ s₂ ↔ s₁ ∨ s₂ ≡ s₂ := by simp_all


theorem compatible_iff_And_not_equiv_bottom (s₁ s₂ : C.Statement) :
  compatible s₁ s₂ ↔ ¬(s₁ ∧ s₂ ≡ bottom):= by simp_all



theorem not_compatible_iff_self_And_Not_equiv_self (s₁ s₂ : C.Statement) :
  ¬(compatible s₁ s₂) ↔ (s₁ ∧ ¬s₂ ≡ s₁) := by simp_all


theorem self_narrower_self_Or {s₁ s₂ : C.Statement} : s₁ ≼ s₁ ∨ s₂ := by simp_all
theorem self_narrower_Or_self {s₁ s₂ : C.Statement} : s₂ ≼ s₁ ∨ s₂ := by simp_all
theorem self_And_narrower_self {s₁ s₂ : C.Statement} : s₁ ∧ s₂ ≼ s₁ := by simp_all
theorem And_narrower_right (a b : C.Statement) : a ∧ b ≼ b := by
simp_all
theorem narrower_iff_Not_Or_equiv_top (s₁ s₂ : C.Statement) :
  s₁ ≼ s₂ ↔ ¬s₁ ∨ s₂ ≡ top := by
constructor
· intro _ a _
  by_cases hs1 : a s₁ <;> simp_all
intro h a ha _
specialize h a ha
simp_all

instance : Trans (@narrower C) (narrower) (narrower) := {
  trans := @narrower_trans C
}

instance : Trans (@narrower C) (· ≡ · ) (· ≼ · ) := {
  trans := narrower_of_narrower_of_equiv
}
instance : Trans (· ≡ ·) (@narrower C) (· ≼ · ) := {
  trans := by
    intro a b c h1 h2
    simp_all only [equivalent, narrower, implies_true]
}

theorem narrower_top (x : C.Statement) : x ≼ Connectives.top := by simp_all

theorem bottom_narrower (x : C.Statement) : Connectives.bottom ≼ x := by simp_all
