/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Reflection/OrdinalSupply.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Reflection.Skolem
import Mathlib.SetTheory.Cardinal.Regular

/-!
# Actual cofinal reflection supply below omega-one

All labels belong to the set-bounded well-order `[0, omega-one]`. A countable
family of the previously defined finite Skolem functions is closed by taking
successive countable bounds and then a countable supremum. Thus the supply
condition is proved for actual ordinals, not introduced as a semantic axiom.
-/

namespace OmegaY.Reflection.OrdinalSupply

open Ordinal Cardinal
open scoped Cardinal Ordinal

universe v w

abbrev Label : Type 1 := {o : Ordinal.{0} // o ≤ ω₁}

instance : OrderBot Label where
  bot := ⟨0, zero_le⟩
  bot_le a := by
    change (0 : Ordinal) ≤ a.1
    exact zero_le

noncomputable def top : Label := ⟨ω₁, le_rfl⟩

theorem bot_lt_top : (⊥ : Label) < top := by
  change (0 : Ordinal) < ω₁
  exact lt_trans omega0_pos omega0_lt_omega_one

theorem countable_iio_ordinal {a : Ordinal.{0}} (ha : a < ω₁) :
    Countable (Set.Iio a) := by
  apply Cardinal.mk_le_aleph0_iff.mp
  rw [Cardinal.mk_Iio_ordinal, Cardinal.lift_le_aleph0]
  exact Cardinal.lt_aleph_one_iff.mp (lt_omega_iff_card_lt.mp ha)

theorem countable_iio {a : Label} (ha : a < top) : Countable (Set.Iio a) := by
  letI := countable_iio_ordinal ha
  exact Function.Injective.countable
    (f := fun x : Set.Iio a => (⟨x.1.1, x.2⟩ : Set.Iio a.1)) (by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : Set.Iio a.1 => z.1) h)

variable {Key : Type v} [LinearOrder Key] [WellFoundedLT Key]
variable (S : KeySyntax.{1,v,w} Label Key)
variable [∀ n, Countable (S.Template n)]

def arity (c : SkolemCode S) : Nat := c.1 + c.2.1

noncomputable def operation (c : SkolemCode S) (params : Fin (arity S c) → Label) :
    Label := skolemTuple S c.2.2.1 top params c.2.2.2

omit [∀ n, Countable (S.Template n)] in
theorem operation_lt_top (c : SkolemCode S) (params : Fin (arity S c) → Label) :
    operation S c params < top :=
  skolemTuple_bounded S c.2.2.1 bot_lt_top params c.2.2.2

def Input (a : Label) := Σ c : SkolemCode S, Fin (arity S c) → Set.Iio a

instance input_countable (a : Set.Iio top) : Countable (Input S a.1) := by
  letI := countable_iio a.2
  unfold Input
  infer_instance

/-- A simultaneous bound for every finite input below one countable cut. -/
noncomputable def operationBound (a : Set.Iio top) : Ordinal.{0} :=
  ⨆ input : Input S a.1, (operation S input.1 (fun i => (input.2 i).1)).1 + 1

theorem operationBound_lt (a : Set.Iio top) : operationBound S a < ω₁ := by
  apply Ordinal.iSup_lt_omega_one
  intro input
  exact (isSuccLimit_omega 1).add_one_lt (operation_lt_top S input.1 _)

theorem operation_lt_bound (a : Set.Iio top) (c : SkolemCode S)
    (params : Fin (arity S c) → Label) (hp : Bounded params a.1) :
    (operation S c params).1 < operationBound S a := by
  let input : Input S a.1 := ⟨c, fun i => ⟨params i, hp i⟩⟩
  exact Ordinal.lt_iSup_add_one
    (fun t : Input S a.1 => (operation S t.1 (fun i => (t.2 i).1)).1) input

noncomputable def next (a : Set.Iio top) : Set.Iio top :=
  ⟨⟨max (a.1.1 + 1) (operationBound S a) + 1,
    ((isSuccLimit_omega 1).add_one_lt
      (max_lt ((isSuccLimit_omega 1).add_one_lt a.2) (operationBound_lt S a))).le⟩,
    (isSuccLimit_omega 1).add_one_lt
      (max_lt ((isSuccLimit_omega 1).add_one_lt a.2) (operationBound_lt S a))⟩

theorem lt_next (a : Set.Iio top) : a.1 < (next S a).1 := by
  change a.1.1 < max (a.1.1 + 1) (operationBound S a) + 1
  exact lt_trans (lt_of_lt_of_le (lt_add_one _) (le_max_left _ _)) (lt_add_one _)

theorem operation_lt_next (a : Set.Iio top) (c : SkolemCode S)
    (params : Fin (arity S c) → Label) (hp : Bounded params a.1) :
    operation S c params < (next S a).1 := by
  change (operation S c params).1 < max (a.1.1 + 1) (operationBound S a) + 1
  exact lt_trans (lt_of_lt_of_le (operation_lt_bound S a c params hp)
    (le_max_right _ _)) (lt_add_one _)

noncomputable def chain (seed : Set.Iio top) : Nat → Set.Iio top
  | 0 => seed
  | n + 1 => next S (chain seed n)

theorem chain_step (seed : Set.Iio top) (n : Nat) :
    (chain S seed n).1 < (chain S seed (n + 1)).1 := lt_next S _

theorem chain_strictMono (seed : Set.Iio top) :
    StrictMono (fun n => (chain S seed n).1.1) :=
  strictMono_nat_of_lt_succ (chain_step S seed)

theorem finite_common_stage (c : Nat → Ordinal.{0}) (hc : Monotone c) :
    ∀ (n : Nat) (f : Fin n → Ordinal.{0}),
    (∀ i, f i < ⨆ j, c j) → ∃ j, ∀ i, f i < c j := by
  intro n
  induction n with
  | zero =>
    intro f _h
    exact ⟨0, fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro f h
    obtain ⟨j, hj⟩ := Ordinal.lt_iSup_iff.mp (h 0)
    obtain ⟨k, hk⟩ := ih (fun i => f i.succ) (fun i => h i.succ)
    refine ⟨max j k, ?_⟩
    intro i
    induction i using Fin.cases with
    | zero => exact lt_of_lt_of_le hj (hc (le_max_left _ _))
    | succ i => exact lt_of_lt_of_le (hk i) (hc (le_max_right _ _))

/-- Cofinal actual Skolem closure points, supplied within the fixed ordinal set. -/
theorem skolemClosed_cofinal (seed : Set.Iio top) :
    ∃ a : Label, seed.1 < a ∧ a < top ∧ SkolemClosed S a top := by
  let c : Nat → Ordinal.{0} := fun n => (chain S seed n).1.1
  let delta : Ordinal.{0} := ⨆ n, c n
  have hdelta : delta < ω₁ := Ordinal.iSup_lt_omega_one (fun n => (chain S seed n).2)
  let a : Label := ⟨delta, hdelta.le⟩
  have hstage : ∀ n, (chain S seed n).1 < a := by
    intro n
    exact lt_of_lt_of_le (chain_step S seed n) (Ordinal.le_iSup c (n + 1))
  refine ⟨a, hstage 0, hdelta, ?_⟩
  intro n k q params hp i
  obtain ⟨j, hj⟩ := finite_common_stage c (chain_strictMono S seed).monotone
    (n + k) (fun i => (params i).1) hp
  let code : SkolemCode S := ⟨n, k, q, i⟩
  have hnext := operation_lt_next S (chain S seed j) code params hj
  exact lt_trans hnext (hstage (j + 1))

/-- The master closure condition has now been supplied without reflection axioms. -/
theorem masterClosed_cofinal (seed : Set.Iio top) :
    ∃ a : Label, seed.1 < a ∧ a < top ∧ MasterClosed S a top := by
  obtain ⟨a, hsa, hat, hclosed⟩ := skolemClosed_cofinal S seed
  exact ⟨a, hsa, hat, masterClosed_of_skolemClosed S
    (lt_of_le_of_lt bot_le hsa) hclosed⟩

/-- Actual simultaneous supply at a cofinal family of countable ordinal labels. -/
theorem reflection_supply_cofinal (seed : Set.Iio top) :
    ∃ a : Label, seed.1 < a ∧ a < top ∧ ∀ theta : Key, R S theta a top := by
  obtain ⟨a, hsa, hat, hclosed⟩ := masterClosed_cofinal S seed
  exact ⟨a, hsa, hat, initial_supply S hat hclosed⟩

structure ClosedPoint where
  val : Label
  lt_top : val < top
  closed : MasterClosed S val top

noncomputable def pointAbove (seed : Set.Iio top) : ClosedPoint S :=
  ⟨Classical.choose (masterClosed_cofinal S seed),
    (Classical.choose_spec (masterClosed_cofinal S seed)).2.1,
    (Classical.choose_spec (masterClosed_cofinal S seed)).2.2⟩

theorem lt_pointAbove (seed : Set.Iio top) : seed.1 < (pointAbove S seed).val :=
  (Classical.choose_spec (masterClosed_cofinal S seed)).1

noncomputable def points : Nat → ClosedPoint S
  | 0 => pointAbove S ⟨⊥, bot_lt_top⟩
  | n + 1 => pointAbove S ⟨(points n).val, (points n).lt_top⟩

theorem points_strictMono : StrictMono (fun n => (points S n).val) :=
  strictMono_nat_of_lt_succ (fun _n => lt_pointAbove S _)

/-- Every finite positive graph and finite reservoir has an actual initial
representation, with its own top strictly below omega-one. -/
theorem initial_finite_graph {n : Nat} (G : List (InternalAtom S n))
    (N : List (TopAtom S n)) :
    ∃ beta : Label, beta < top ∧ ∃ f : Fin n → Label,
      StrictMono f ∧ Bounded f beta ∧
      InternalHolds S (R S) G f ∧ TopHolds S (R S) N f beta := by
  let f : Fin n → Label := fun i => (points S i.val).val
  refine ⟨(points S n).val, (points S n).lt_top, f, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact points_strictMono S hij
  · intro i
    exact points_strictMono S i.isLt
  · intro e _he
    exact between_closed_points S (points_strictMono S e.parent_lt_child)
      (points S e.child.val).lt_top (points S e.parent.val).closed
      (points S e.child.val).closed (S.eval e.key f)
  · intro e _he
    exact between_closed_points S (points_strictMono S e.parent.isLt)
      (points S n).lt_top (points S e.parent.val).closed (points S n).closed
      (S.eval e.key f)

#print axioms skolemClosed_cofinal
#print axioms masterClosed_cofinal
#print axioms reflection_supply_cofinal
#print axioms initial_finite_graph

end OmegaY.Reflection.OrdinalSupply
