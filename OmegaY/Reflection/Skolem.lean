/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Reflection/Skolem.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Reflection.Stability
import Mathlib.Data.Set.Countable
import Mathlib.Data.Fintype.Pi

/-!
# Actual finite Skolem functions for the positive master

The selected functions are defined using choice from a fully specified finite
positive-graph witness predicate. Their closure implies `MasterClosed`; no
changed-endpoint reflection is put into the selected-witness predicate.
-/

namespace OmegaY.Reflection

universe u v w

variable {Label : Type u} {Key : Type v}
variable [LinearOrder Label] [LinearOrder Key]
variable [WellFoundedLT Label] [WellFoundedLT Key]
variable (S : KeySyntax.{u,v,w} Label Key)

/-- The first `n` parameters can fix selected vertices; the remaining `k`
parameters are anchors below every vertex which is not selected. -/
structure Query (n k : Nat) where
  internal : List (InternalAtom S n)
  needs : List (TopAtom S n)
  fixed : Fin n → Bool

def Query.Realizes {n k : Nat} (q : Query S n k) (top : Label)
    (params : Fin (n + k) → Label) (f : Fin n → Label) : Prop :=
  StrictMono f ∧ Bounded f top ∧ InternalHolds S (R S) q.internal f ∧
    TopHolds S (R S) q.needs f top ∧
    (∀ i, q.fixed i = true → f i = params (Fin.castAdd k i)) ∧
    (∀ i, q.fixed i = false → ∀ j : Fin k, params (Fin.natAdd n j) < f i)

variable [OrderBot Label]

/-- An actual selected finite tuple, with a fixed fallback when unrealizable. -/
noncomputable def skolemTuple {n k : Nat} (q : Query S n k) (top : Label)
    (params : Fin (n + k) → Label) : Fin n → Label := by
  classical
  exact if h : ∃ f, q.Realizes S top params f then Classical.choose h else fun _ => ⊥

theorem skolemTuple_spec {n k : Nat} (q : Query S n k) (top : Label)
    (params : Fin (n + k) → Label) (h : ∃ f, q.Realizes S top params f) :
    q.Realizes S top params (skolemTuple S q top params) := by
  classical
  rw [skolemTuple, dif_pos h]
  exact Classical.choose_spec h

theorem skolemTuple_bounded {n k : Nat} (q : Query S n k) {top : Label}
    (htop : ⊥ < top) (params : Fin (n + k) → Label) :
    Bounded (skolemTuple S q top params) top := by
  classical
  by_cases h : ∃ f, q.Realizes S top params f
  · exact (skolemTuple_spec S q top params h).2.1
  · simp only [skolemTuple, dif_neg h, Bounded]
    exact fun _ => htop

def SkolemClosed (a top : Label) : Prop :=
  ∀ (n k : Nat) (q : Query S n k) (params : Fin (n + k) → Label),
    Bounded params a → Bounded (skolemTuple S q top params) a

/-- The ordinary closure of the actual selected functions gives every finite
positive master compression, including fixed old parameters and anchors. -/
theorem masterClosed_of_skolemClosed {a top : Label} (hbot : ⊥ < a)
    (hclosed : SkolemClosed S a top) : MasterClosed S a top := by
  classical
  intro n G N f anchors hmono hbound hG hN hanchors
  let q : Query S n anchors.length := ⟨G, N, fun i => decide (f i < a)⟩
  let params : Fin (n + anchors.length) → Label :=
    Fin.addCases (fun i => if f i < a then f i else ⊥) (fun j => anchors.get j)
  have hparams : Bounded params a := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      simp only [params, Fin.addCases_left]
      split
      · assumption
      · exact hbot
    | right j =>
      simp only [params, Fin.addCases_right]
      exact hanchors _ (List.get_mem _ _)
  have hreal : q.Realizes S top params f := by
    refine ⟨hmono, hbound, hG, hN, ?_, ?_⟩
    · intro i hi
      have hia : f i < a := of_decide_eq_true hi
      simp [params, hia]
    · intro i hi j
      have hia : ¬f i < a := of_decide_eq_false hi
      simp only [params, Fin.addCases_right]
      exact lt_of_lt_of_le (hanchors _ (List.get_mem _ _)) (le_of_not_gt hia)
  let g := skolemTuple S q top params
  have hg : q.Realizes S top params g := skolemTuple_spec S q top params ⟨f, hreal⟩
  refine ⟨g, hg.1, hclosed n anchors.length q params hparams, ?_, ?_, hg.2.2.1,
    hg.2.2.2.1⟩
  · intro i hi
    have heq := hg.2.2.2.2.1 i (by exact decide_eq_true hi)
    simpa [params, hi] using heq
  · intro i hi p hp
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hp
    have hfalse : q.fixed i = false := by
      exact decide_eq_false (not_lt_of_ge hi)
    simpa [params] using hg.2.2.2.2.2 i hfalse j

/-- The functions being closed under have only countably many finite codes
when the key syntax has only countably many templates. -/
instance internalAtom_countable {n : Nat} [Countable (S.Template n)] :
    Countable (InternalAtom S n) :=
  Function.Injective.countable (f := fun e => (e.key, e.parent, e.child)) (by
    intro e d h
    cases e
    cases d
    simpa only [Prod.mk.injEq, InternalAtom.mk.injEq] using h)

instance topAtom_countable {n : Nat} [Countable (S.Template n)] :
    Countable (TopAtom S n) :=
  Function.Injective.countable (f := fun e => (e.key, e.parent)) (by
    intro e d h
    cases e
    cases d
    simpa only [Prod.mk.injEq, TopAtom.mk.injEq] using h)

instance query_countable {n k : Nat} [Countable (S.Template n)] :
    Countable (Query S n k) :=
  Function.Injective.countable (f := fun q => (q.internal, q.needs, q.fixed)) (by
    intro q r h
    cases q
    cases r
    simpa only [Prod.mk.injEq, Query.mk.injEq] using h)

def SkolemCode := Σ n : Nat, Σ k : Nat, Query S n k × Fin n

instance skolemCode_countable [∀ n, Countable (S.Template n)] :
    Countable (SkolemCode S) := by unfold SkolemCode; infer_instance

#print axioms skolemTuple_spec
#print axioms masterClosed_of_skolemClosed
#print axioms skolemCode_countable

end OmegaY.Reflection
