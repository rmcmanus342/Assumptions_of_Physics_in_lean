import AssumptionsOfPhysicsInLean.logical_context.Basic


variable {C : LogicalContext}

@[simp] def equivalent {C : LogicalContext} (s₁ s₂ : C.Statement) := ∀a ∈ C.possible, a s₁ = a s₂
infix:25 " ≡ " => equivalent





variable {C : LogicalContext}
@[refl, simp]
theorem equiv_refl {s : C.Statement} : s ≡ s := by
simp_all only [equivalent, implies_true]

@[symm]
theorem equiv_symm {s₁ s₂ : C.Statement} :
  s₁ ≡ s₂ →
  s₂ ≡ s₁ := by
intro h a ha
symm
exact h a ha

@[trans]
theorem equiv_trans {s₁ s₂ s₃ : C.Statement} :
  s₁ ≡ s₂ →
  s₂ ≡ s₃ →
  s₁ ≡ s₃ := by
intro h₁ h₂ a ha
trans a s₂
· exact h₁ a ha
· exact h₂ a ha

instance statementSetoid (C : LogicalContext) :
  Setoid C.Statement where
  r := equivalent
  iseqv := {
    refl := @equiv_refl C,
    symm := @equiv_symm C,
    trans := @equiv_trans C
  }
