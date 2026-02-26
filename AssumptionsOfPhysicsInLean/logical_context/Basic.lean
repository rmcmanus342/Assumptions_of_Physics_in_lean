import Mathlib.Data.Set.Basic

universe u v

structure LogicalContext where
  Statement : Type u
  truth : Statement → Bool
  possible : Set (Statement → Bool)
  truth_possible : truth ∈ possible
  /--
  You can combine an arbitrary possible :
  Set (Statement → Bool) number of statements with a boolean function.
  -/
  apply {ι: Type v} :
    (ι → Statement) →
    (f : (ι → Bool) → Bool) →
    Statement

  --axiom of closure
  apply_spec {ι: Type v}
   (T : ι → Statement)
   (f : (ι → Bool) → Bool) :
    ∀ a ∈ possible,
      a (apply T f) = f (a ∘ T)
