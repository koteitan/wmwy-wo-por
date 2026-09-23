/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Reflection/Stability.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Reflection

/-!
# Endpoint stability from positive master-graph closure

`MasterClosed` describes ordinary finite positive-graph closure with its top
endpoint kept fixed. It does not assert reflection at a changed endpoint.
The latter is proved here by induction on the actual recursively defined key.
The existence of such closure points is a separate supply obligation.
-/

namespace OmegaY.Reflection

universe u v w

variable {Label : Type u} {Key : Type v}
variable [LinearOrder Label] [LinearOrder Key]
variable [WellFoundedLT Label] [WellFoundedLT Key]
variable (S : KeySyntax.{u,v,w} Label Key)

/-- Closure under finite positive master diagrams. The finite `anchors` allow
positive inequalities above parameters already below the closure point. -/
def MasterClosed (a top : Label) : Prop :=
  ∀ (n : Nat) (G : List (InternalAtom S n)) (N : List (TopAtom S n))
    (f : Fin n → Label) (anchors : List Label),
    StrictMono f → Bounded f top → InternalHolds S (R S) G f →
    TopHolds S (R S) N f top → (∀ p ∈ anchors, p < a) →
    ∃ g : Fin n → Label, StrictMono g ∧ Bounded g a ∧ FixesBelow a f g ∧
      (∀ i, a ≤ f i → ∀ p ∈ anchors, p < g i) ∧
      InternalHolds S (R S) G g ∧ TopHolds S (R S) N g top

/-- An actual stability theorem: only finite master closure is a hypothesis;
endpoint-changing reflection is obtained by induction on the key. -/
theorem endpoint_stability {a top : Label} (hatop : a < top)
    (hclosed : MasterClosed S a top) (theta : Key) :
    ∀ p, p < a → (R S theta p a ↔ R S theta p top) := by
  induction theta using (wellFounded_lt :
      WellFounded ((· < ·) : Key → Key → Prop)).induction with
  | h theta ih =>
    intro p hpa
    constructor
    · intro hpaR
      apply (equation S theta p top).mpr
      refine ⟨lt_trans hpa hatop, ?_⟩
      intro n G N f hmono hbound hG hkeys hN
      obtain ⟨h, hhmono, hhbound, hhfix, hhanchor, hhG, hhN⟩ :=
        hclosed n G N f [p] hmono hbound hG hN (by
          intro q hq
          have hqp : q = p := List.mem_singleton.mp hq
          exact hqp ▸ hpa)
      have hle : ∀ i, h i ≤ f i := pointwise_le_of_compression hhbound hhfix
      have hhkeys : KeysBelow S N h theta := by
        intro e he
        exact lt_of_le_of_lt (S.monotone_eval e.key hle) (hkeys e he)
      have hhN' : TopHolds S (R S) N h a := by
        intro e he
        exact (ih (S.eval e.key h) (hhkeys e he) (h e.parent)
          (hhbound e.parent)).mpr (hhN e he)
      obtain ⟨g, hgmono, hgbound, hgfix, hgG, hgN⟩ :=
        reflects S hpaR n G N h hhmono hhbound hhG hhkeys hhN'
      refine ⟨g, hgmono, hgbound, ?_, hgG, hgN⟩
      intro i hi
      have hhi : h i = f i := hhfix i (lt_trans hi hpa)
      exact (hgfix i (hhi ▸ hi)).trans hhi
    · intro hptopR
      apply (equation S theta p a).mpr
      refine ⟨hpa, ?_⟩
      intro n G N f hmono hbound hG hkeys hN
      have hN' : TopHolds S (R S) N f top := by
        intro e he
        exact (ih (S.eval e.key f) (hkeys e he) (f e.parent)
          (hbound e.parent)).mp (hN e he)
      exact reflects S hptopR n G N f hmono
        (fun i => lt_trans (hbound i) hatop) hG hkeys hN'

/-- Every key reflects from the fixed master top to a master closure point. -/
theorem initial_supply {a top : Label} (hatop : a < top)
    (hclosed : MasterClosed S a top) (theta : Key) : R S theta a top := by
  apply (equation S theta a top).mpr
  refine ⟨hatop, ?_⟩
  intro n G N f hmono hbound hG hkeys hN
  obtain ⟨g, hgmono, hgbound, hgfix, _hganchor, hgG, hgN⟩ :=
    hclosed n G N f [] hmono hbound hG hN (by simp)
  refine ⟨g, hgmono, hgbound, hgfix, hgG, ?_⟩
  intro e he
  exact (endpoint_stability S hatop hclosed (S.eval e.key g)
    (g e.parent) (hgbound e.parent)).mpr (hgN e he)

/-- Two closure points support every key, with no upper-endpoint monotonicity
assumption for arbitrary points. -/
theorem between_closed_points {a b top : Label} (hab : a < b) (hbtop : b < top)
    (ha : MasterClosed S a top) (hb : MasterClosed S b top)
    (theta : Key) : R S theta a b := by
  exact (endpoint_stability S hbtop hb theta a hab).mpr
    (initial_supply S (lt_trans hab hbtop) ha theta)

#print axioms endpoint_stability
#print axioms initial_supply
#print axioms between_closed_points

end OmegaY.Reflection
