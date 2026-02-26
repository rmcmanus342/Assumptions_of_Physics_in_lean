import AssumptionsOfPhysicsInLean.logical_context.Basic
import Mathlib.Data.Fintype.Order
namespace LogicalContext.Connectives
variable {C : LogicalContext}

def Not (s : C.Statement) : C.Statement :=
  C.apply (fun _ : Unit ↦ s)
  (fun x ↦ !x ())

def And (s₁ s₂ : C.Statement) :=
  C.apply
    (fun b : Bool => cond b s₁ s₂)
    (fun g => g true && g false)

def Or (s₁ s₂ : C.Statement) :=
  C.apply
    (fun b : Bool => cond b s₁ s₂)
    (fun g => g true || g false)

def top : C.Statement := C.apply
  (Empty.elim)
  (fun _ ↦ true)
def bottom : C.Statement := C.apply
  (Empty.elim)
  (fun _ ↦ false)

#check Bool.completeBooleanAlgebra.sSup
#check Bool.completeBooleanAlgebra.sInf

noncomputable def Any (S : Set C.Statement) : C.Statement := C.apply
  (fun s : S ↦ s.val)
  (fun g  ↦ sSup (Set.range g))

noncomputable def All (S : Set C.Statement) : C.Statement := C.apply
  (fun i : {s // s ∈ S} ↦ i.val)
  (fun g ↦ sInf (Set.range g))





-- Infix notation for And
infixl:35 " ∧ " => And

-- Infix notation for Or
infixl:30 " ∨ " => Or

-- Prefix notation for Not
prefix:40 "¬" => Not

@[simp] theorem top_true : ∀a ∈ C.possible, a top = true := by apply apply_spec
@[simp] theorem bottom_false : ∀a ∈ C.possible, a bottom = false := by apply apply_spec
@[simp] theorem Not_spec {s : C.Statement} : ∀a ∈ C.possible, a (¬s) = !a s := by apply apply_spec
@[simp] theorem And_spec {s₁ s₂ : C.Statement} :
  ∀a ∈ C.possible, a (s₁ ∧ s₂) = ((a s₁) && (a s₂)) := by apply apply_spec
@[simp] theorem Or_spec {s₁ s₂ : C.Statement} :
  ∀a ∈ C.possible, a (s₁ ∨ s₂) = ((a s₁) || (a s₂)) := by apply apply_spec

variable {S : Set C.Statement}
#check C.apply_spec (fun i : {s // s ∈ S } ↦ i.val) (Bool.completeBooleanAlgebra.sInf ∘ Set.range )

@[simp]
theorem Any_spec (S : Set C.Statement) :
  ∀ a ∈ C.possible,
    a (Any S) =
      sSup (a '' S) :=
by
  intro a ha
  classical
  simpa [Any, Set.image, Set.range, Function.comp]
    using
      C.apply_spec
        (T := fun i : {s // s ∈ S} => i.val)
        (f := fun g => sSup (Set.range g))
        a ha

@[simp]
theorem All_spec (S : Set C.Statement) :
  ∀ a ∈ C.possible,
    a (All S) =
      sInf (a '' S) :=
by
  intro a ha
  classical
  simpa [All, Set.image, Set.range, Function.comp]
    using
      C.apply_spec
        (T := fun i : {s // s ∈ S} => i.val)
        (f := fun g => sInf (Set.range g))
        a ha

end LogicalContext.Connectives
