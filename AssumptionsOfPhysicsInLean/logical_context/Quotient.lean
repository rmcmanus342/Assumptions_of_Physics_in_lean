import AssumptionsOfPhysicsInLean.logical_context.Basic
import AssumptionsOfPhysicsInLean.logical_context.Order
import AssumptionsOfPhysicsInLean.logical_context.BasicTheorems
--most algebraic theorems that talk of logical operations and truth tables
--also all lifts happen here
namespace Quotient
open LogicalContext
open CongreunceTheorems
open AlgebraicTheorems





variable {C : LogicalContext}
def StatementQ (C : LogicalContext) :=
Quotient (statementSetoid C)

def qOp1 (f : C.Statement → C.Statement)
  (f_congr : ∀ {s s'}, s ≡ s' → f s ≡ f s') :
   StatementQ C → StatementQ C :=
Quotient.map _ (fun _ _ h ↦ f_congr h)

def qOp2 (f : C.Statement → C.Statement → C.Statement)
  (f_congr : ∀ {s₁ s₁' s₂ s₂'}, s₁ ≡ s₁' → s₂ ≡ s₂' → f s₁ s₂ ≡ f s₁' s₂') :
  StatementQ C → StatementQ C → StatementQ C :=
  Quotient.map₂
      (_)
      (fun _ _ ha _ _ hb ↦ f_congr ha hb)

def qRel2 (R : C.Statement → C.Statement → Prop)
    (R_congr : ∀ {s₁ s₂ s₁' s₂'}, s₁ ≡ s₁' → s₂ ≡ s₂' → (R s₁ s₂ = R s₁' s₂')) :
    StatementQ C → StatementQ C → Prop :=
    Quotient.lift₂
    (_)
    (fun _ _ _ _ ha hb ↦ R_congr ha hb)

def qNot : StatementQ C → StatementQ C := qOp1 _ Not_congr

def qAnd : StatementQ C → StatementQ C → StatementQ C := qOp2 _ And_congr

def qOr : StatementQ C → StatementQ C → StatementQ C := qOp2 _ Or_congr

def qNarrower : StatementQ C → StatementQ C → Prop := qRel2 _ Narrower_congr

def qAny (s : Set (StatementQ C)) : StatementQ C := sorry 

def qAll : Set (StatementQ C) → StatementQ C := sorry


def top :  StatementQ C := Quot.mk _ Connectives.top
def bottom : StatementQ C  := Quot.mk _ Connectives.bottom
infixl:35 " ∧ " => qAnd
infixl:30 " ∨ " => qOr
prefix:40 "¬" => qNot
infix:25 " ≼ " => qNarrower

theorem and_comm (p q : StatementQ C) : (p ∧ q) = (q ∧ p) := by
  induction p using Quot.ind
  induction q using Quot.ind
  apply Quot.sound
  apply And_comm

--instance : Preorder (StatementQ C) := Quotient.instPreorder

end Quotient
