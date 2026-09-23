/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Reflection.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import Mathlib.Order.WellFounded
import Mathlib.Order.Fin.Basic

/-!
# Positive finite-graph reflection by an actual well-founded recursion

The endpoint is the primary recursion index and the control key the secondary
index. Internal atoms may use arbitrary keys. Only atoms at the current top
endpoint must have earlier keys. No reflection or existence axiom is assumed.

The finite key syntax is a parameter, rather than the type of all monotone
functions. This leaves room for a countable concrete vector-key syntax.
-/

namespace OmegaY.Reflection

universe u v w

variable {Label : Type u} {Key : Type v}

/-- A finite syntax with a pointwise-monotone interpretation in the key order. -/
structure KeySyntax (Label : Type u) (Key : Type v)
    [Preorder Label] [Preorder Key] where
  Template : Nat → Type w
  eval : {n : Nat} → Template n → (Fin n → Label) → Key
  monotone_eval : ∀ {n : Nat} (t : Template n) {f g : Fin n → Label},
    (∀ i, g i ≤ f i) → eval t g ≤ eval t f

variable [LinearOrder Label] [LinearOrder Key]

structure InternalAtom (S : KeySyntax.{u,v,w} Label Key) (n : Nat) where
  key : S.Template n
  parent : Fin n
  child : Fin n
  parent_lt_child : parent < child

structure TopAtom (S : KeySyntax.{u,v,w} Label Key) (n : Nat) where
  key : S.Template n
  parent : Fin n

variable (S : KeySyntax.{u,v,w} Label Key)

abbrev Relation := Key → Label → Label → Prop

def Bounded {n : Nat} (f : Fin n → Label) (b : Label) : Prop := ∀ i, f i < b

def FixesBelow {n : Nat} (a : Label) (f g : Fin n → Label) : Prop :=
  ∀ i, f i < a → g i = f i

def InternalHolds (R : Relation (Label := Label) (Key := Key))
    {n : Nat} (G : List (InternalAtom S n)) (f : Fin n → Label) : Prop :=
  ∀ e ∈ G, R (S.eval e.key f) (f e.parent) (f e.child)

def TopHolds (R : Relation (Label := Label) (Key := Key))
    {n : Nat} (N : List (TopAtom S n)) (f : Fin n → Label) (b : Label) : Prop :=
  ∀ e ∈ N, R (S.eval e.key f) (f e.parent) b

def KeysBelow {n : Nat} (N : List (TopAtom S n))
    (f : Fin n → Label) (theta : Key) : Prop :=
  ∀ e ∈ N, S.eval e.key f < theta

/-- The ordinary, nonrecursive description of the finite reflection clause. -/
def Reflects (R : Relation (Label := Label) (Key := Key))
    (theta : Key) (a b : Label) : Prop :=
  ∀ (n : Nat) (G : List (InternalAtom S n)) (N : List (TopAtom S n))
    (f : Fin n → Label),
    StrictMono f → Bounded f b → InternalHolds S R G f →
    KeysBelow S N f theta → TopHolds S R N f b →
    ∃ g : Fin n → Label, StrictMono g ∧ Bounded g a ∧ FixesBelow a f g ∧
      InternalHolds S R G g ∧ TopHolds S R N g a

def StageLT : (Label × Key) → (Label × Key) → Prop :=
  Prod.Lex (· < ·) (· < ·)

variable [WellFoundedLT Label] [WellFoundedLT Key]

theorem stage_wellFounded : WellFounded (StageLT (Label := Label) (Key := Key)) :=
  ⟨fun x => Prod.lexAccessible (wellFounded_lt.apply x.1)
    (fun k => wellFounded_lt.apply k) x.2⟩

/-- All four forms of recursive lookup carry an explicit earlier-stage proof. -/
def recursionStep (s : Label × Key)
    (previous : ∀ t, StageLT t s → Label → Prop) (a : Label) : Prop :=
  ∃ hab : a < s.1,
    ∀ (n : Nat) (G : List (InternalAtom S n)) (N : List (TopAtom S n))
      (f : Fin n → Label), StrictMono f →
      ∀ hf : Bounded f s.1,
      (∀ e ∈ G, previous (f e.child, S.eval e.key f)
        (Prod.Lex.left _ _ (hf e.child)) (f e.parent)) →
      ∀ hk : KeysBelow S N f s.2,
      (∀ e (he : e ∈ N), previous (s.1, S.eval e.key f)
        (Prod.Lex.right _ (hk e he)) (f e.parent)) →
      ∃ g : Fin n → Label, StrictMono g ∧
        ∃ hg : Bounded g a, FixesBelow a f g ∧
        (∀ e ∈ G, previous (g e.child, S.eval e.key g)
          (Prod.Lex.left _ _ (lt_trans (hg e.child) hab)) (g e.parent)) ∧
        (∀ e ∈ N, previous (a, S.eval e.key g)
          (Prod.Lex.left _ _ hab) (g e.parent))

/-- The relation is defined, not postulated, by endpoint/key recursion. -/
noncomputable def R (theta : Key) (a b : Label) : Prop :=
  stage_wellFounded.fix (recursionStep S) (b, theta) a

/-- The defining equation uses the same actual relation at every atom. -/
theorem equation (theta : Key) (a b : Label) :
    R S theta a b ↔ a < b ∧ Reflects S (R S) theta a b := by
  unfold R
  rw [WellFounded.fix_eq]
  simp only [recursionStep, Reflects, InternalHolds, TopHolds, exists_prop]

theorem lower_lt {theta : Key} {a b : Label} (h : R S theta a b) : a < b :=
  ((equation S theta a b).mp h).1

theorem reflects {theta : Key} {a b : Label} (h : R S theta a b) :
    Reflects S (R S) theta a b := ((equation S theta a b).mp h).2

omit [WellFoundedLT Label] in
theorem pointwise_le_of_compression {n : Nat} {a : Label} {f g : Fin n → Label}
    (hg : Bounded g a) (hfix : FixesBelow a f g) : ∀ i, g i ≤ f i := by
  intro i
  by_cases hi : f i < a
  · exact le_of_eq (hfix i hi)
  · exact le_trans (le_of_lt (hg i)) (le_of_not_gt hi)

/-- Lowering the control key only restricts which top demands are tested. -/
theorem key_weaken {theta Theta : Key} {a b : Label}
    (hle : theta ≤ Theta) (h : R S Theta a b) : R S theta a b := by
  apply (equation S theta a b).mpr
  refine ⟨lower_lt S h, ?_⟩
  intro n G N f hmono hbound hG hkeys hN
  apply reflects S h n G N f hmono hbound hG _ hN
  intro e he
  exact lt_of_lt_of_le (hkeys e he) hle

/-- Two finite compressions compose; moving the labels never raises a key. -/
theorem trans {theta : Key} {a b c : Label}
    (hab : R S theta a b) (hbc : R S theta b c) : R S theta a c := by
  apply (equation S theta a c).mpr
  refine ⟨lt_trans (lower_lt S hab) (lower_lt S hbc), ?_⟩
  intro n G N f hmono hbound hG hkeys hN
  obtain ⟨h, hmono', hbound', hfix', hG', hN'⟩ :=
    reflects S hbc n G N f hmono hbound hG hkeys hN
  have hle := pointwise_le_of_compression hbound' hfix'
  have hkeys' : KeysBelow S N h theta := by
    intro e he
    exact lt_of_le_of_lt (S.monotone_eval e.key hle) (hkeys e he)
  obtain ⟨g, hgmono, hgbound, hgfix, hgG, hgN⟩ :=
    reflects S hab n G N h hmono' hbound' hG' hkeys' hN'
  refine ⟨g, hgmono, hgbound, ?_, hgG, hgN⟩
  intro i hi
  have hhi : h i = f i := hfix' i (lt_trans hi (lower_lt S hab))
  rw [hgfix i (hhi ▸ hi), hhi]

/-- The retained prefix is fixed at a selected cut, while the cut label itself
is allowed to move. No root used in a key is required to be retained. -/
theorem finite_reflection {n : Nat} (G : List (InternalAtom S n))
    (N : List (TopAtom S n)) (f : Fin n → Label) (cut : Fin n)
    {theta : Key} {top : Label} (hmono : StrictMono f) (hbound : Bounded f top)
    (hG : InternalHolds S (R S) G f) (hkeys : KeysBelow S N f theta)
    (hN : TopHolds S (R S) N f top) (hcontrol : R S theta (f cut) top) :
    ∃ g : Fin n → Label, StrictMono g ∧ Bounded g (f cut) ∧
      (∀ i, i < cut → g i = f i) ∧ (∀ i, g i ≤ f i) ∧
      InternalHolds S (R S) G g ∧ TopHolds S (R S) N g (f cut) := by
  obtain ⟨g, hgmono, hgbound, hgfix, hgG, hgN⟩ :=
    reflects S hcontrol n G N f hmono hbound hG hkeys hN
  exact ⟨g, hgmono, hgbound, fun i hi => hgfix i (hmono hi),
    pointwise_le_of_compression hgbound hgfix, hgG, hgN⟩

#print axioms equation
#print axioms key_weaken
#print axioms trans
#print axioms finite_reflection

end OmegaY.Reflection
