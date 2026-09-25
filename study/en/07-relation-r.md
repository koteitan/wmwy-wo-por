[← Back](README.md) | [English](07-relation-r.md) | [Japanese](../07-relation-r.md)

# The relation R

Prerequisites

| Note | Terms used here |
|---|---|
| [02 Well-founded relations and recursion](02-well-founded.md) | lexicographic order, well-founded recursion, guarded recursion, keys, stage, top |
| [03 Structures and Σ₁-elementary substructures](03-sigma1-elementary.md) | height of a structure, witness, position, `Lit`, `Form`, `Sat`, `ElemL`, internal relation, top predicate, partial top predicates, `Lit.holds_of_le` |
| [04 Patterns of resemblance](04-patterns-of-resemblance.md) | the idea of making top predicates atomic symbols |
| [06 Phyrion's combinatorial layer for ω-Y](06-combinatorial-layer.md) | key syntax, templates, combinatorial layer, the role of `key_weaken` |

This note explains the definition of the label relation $`R`$ of this repository and the properties that follow directly from it. The Lean file is [Por/Relation.lean](../../Por/Relation.lean).

## 1. Notation

- $`\mathrm{Label}`$: the type of labels. Any well-ordered linear order works (the Lean assumptions are `LinearOrder` and `WellFoundedLT`). In the final theorems $`\mathrm{Label} = \{o \le \omega_1\}`$ ([01](01-ordinals.md) §6).
- $`\mathrm{Key}`$: the type of keys, also any well-ordered linear order. In the final theorems it is $`\mathrm{Key}_m`$ ([02](02-well-founded.md) §3; $`m`$ is the key length).
- $`S`$: the key syntax `KeySyntax Label Key` ([06](06-combinatorial-layer.md) §1).
- $`R(\theta, a, b)`$: key $`\theta`$, lower point $`a`$ (a label), upper point $`b`$ (a label). $`b`$ is the top ([02](02-well-founded.md) §3). In Lean, `Por.R S θ a b`.

## 2. The language

Here the symbols of the language of [03](03-sigma1-elementary.md) §7 get their meaning. There are three kinds of symbols. For each template $`t`$ over $`n`$ variables and positions $`i, j \lt n`$ there are the following.

| Symbol | Number of arguments | Meaning (in the structure of height $`c`$) |
|---|---|---|
| $`\lt`$ | 2 | the order of labels |
| $`\mathrm{Rel}_{t,i,j}`$ | $`n`$ | $`\mathrm{Rel}_{t,i,j}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ v_j)`$ |
| $`\mathrm{Top}_{t,i}`$ | $`n`$ | $`\mathrm{Top}_{t,i}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ c)`$ |

$`\vec v = (v_0, \ldots, v_{n-1})`$ is the tuple of values of the variables. $`\mathrm{Rel}`$ is a relation between points, and $`\mathrm{Top}`$ a relation from a point to the top $`c`$ (the height of the structure). $`c`$ itself is not in the domain. Both symbols compute their key from the $`n`$ points by the template.

In Lean the literals `Lit.rel t i j pos` and `Lit.top t i pos` read these symbols ([03](03-sigma1-elementary.md) §7). The true interpretations are:

```lean
def relR : Key → Label → Label → Prop := fun κ x y => R S κ x y
def topR (c : Label) : Key → Label → Prop := fun κ x => R S κ x c
```

## 3. The structure 𝔄^c_θ

**Definition.** For a key $`\theta`$ and a height $`c`$, the structure $`\mathfrak A^c_\theta`$ is:

- domain $`\{x \mid x \lt c\}`$, order $`\lt`$;
- $`\mathrm{Rel}_{t,i,j}`$ for every template;
- $`\mathrm{Top}_{t,i}(\vec v)`$, defined only when $`\mathrm{eval}\ t\ \vec v \lt \theta`$. Where it is not defined, top literals are false.

In Lean, truth in $`\mathfrak A^c_\theta`$ is `Sat (relR S) (topR S c) (· < θ) c φ p`.

**Example.** Let the key length be $`m = 1`$ and $`\theta = (\omega)`$. The templates are ω-Y templates ([06](06-combinatorial-layer.md) §1): $`\mathrm{some}\ 0`$ puts $`v_0`$ at the coordinate, and $`\mathrm{none}`$ puts $`\top`$.

- The top predicate of the template $`(\mathrm{some}\ 0)`$ is defined when $`v_0 \lt \omega`$, that is, when $`v_0`$ is a natural number.
- The top predicate of the template $`(\mathrm{none})`$ has key $`(\top)`$, so it is defined nowhere.
- If $`\theta = (\top)`$, the top predicate of the template $`(\mathrm{some}\ 0)`$ is defined everywhere.

## 4. Definition

**Definition (R).**

```math
R(\theta, a, b) \iff a \lt b \ \land\ \mathfrak A^{a}_{\theta} \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_{\theta}
```

Here $`\mathfrak A^{a}_{\theta} \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_{\theta}`$ means that for every formula $`\varphi`$ and all parameters $`\vec p`$ below $`a`$ the following holds. We write $`\vec p \lt a`$ when every entry of the tuple $`\vec p`$ is below $`a`$.

```math
\mathfrak A^{a}_{\theta} \models \varphi(\vec p) \iff \mathfrak A^{b}_{\theta} \models \varphi(\vec p)
```

In Lean this is `ElemL (relR S) (topR S a) (topR S b) θ a b` ([03](03-sigma1-elementary.md) §8). The two structures have different top predicates ($`R`$ to $`a`$ and $`R`$ to $`b`$).

## 5. Recursion

The right side reads $`R`$ itself. The definition uses well-founded recursion on the lexicographic order $`\lhd`$ of the stages $`(b, \theta)`$ (pairs of a top and a key, [02](02-well-founded.md) §3), for all $`a`$ at once.

**What the right side reads.** Only three kinds, all at smaller stages.

| Read | Stage | Why smaller |
|---|---|---|
| $`\mathrm{Rel}(\vec v)`$, that is $`R(\kappa, x, y)`$ | $`(y, \kappa)`$ | the points are below the height ($`a`$ or $`b`$), so $`y \lt b`$ |
| a top predicate of $`\mathfrak A^{a}_\theta`$, $`R(\kappa, x, a)`$ | $`(a, \kappa)`$ | $`a \lt b`$ |
| a top predicate of $`\mathfrak A^{b}_\theta`$, $`R(\kappa, x, b)`$ | $`(b, \kappa)`$ | it is defined only when $`\kappa \lt \theta`$ |

The third row is the main point. Because the top predicates of $`\mathfrak A^{b}_\theta`$ are defined only below the key $`\theta`$, the right side does not read the stage $`(b, \theta)`$ itself.

**The recursion in Lean (`stepF`).** At stage $`s = (b, \theta)`$ it returns the set of $`a`$ with $`R(\theta, \cdot, b)`$. Each of the three interpretations carries a proof that the stage is smaller, as a guard ([02](02-well-founded.md) §5).

| Interpretation at the stage | Expression |
|---|---|
| internal relation | $`\mathrm{rel}(\kappa, x, y) :\iff \exists h : y \lt b,\ R(\kappa, x, y)`$ |
| top at height $`a`$ | $`\mathrm{top}_A(\kappa, x) :\iff R(\kappa, x, a)`$ (the guard is $`a \lt b`$, required at the start of `stepF`) |
| top at height $`b`$ | $`\mathrm{top}_B(\kappa, x) :\iff \exists h : \kappa \lt \theta,\ R(\kappa, x, b)`$ |

```lean
noncomputable def stepF (s : Label × Key) (IH : ∀ t, StageLT t s → Label → Prop) :
    Label → Prop :=
  fun a => ∃ hab : a < s.1,
    ElemL (S := S)
      (fun κ x y => ∃ h : y < s.1, IH (y, κ) (Prod.Lex.left _ _ h) x)
      (fun κ x => IH (a, κ) (Prod.Lex.left _ _ hab) x)
      (fun κ x => ∃ h : κ < s.2, IH (s.1, κ) (Prod.Lex.right _ h) x)
      s.2 a s.1

noncomputable def R (θ : Key) (a b : Label) : Prop :=
  stage_wf.fix (stepF S) (b, θ) a
```

## 6. Removing the guards: R_iff

**Theorem (`R_iff`).**

```math
R(\theta, a, b) \iff a \lt b \land \mathrm{ElemL}(\mathrm{relR}, \mathrm{topR}(a), \mathrm{topR}(b), \theta, a, b)
```

**Proof.** Unfolding one step with `WellFounded.fix_eq`, the left side becomes "$`a \lt b`$ and `ElemL` with the stage interpretations". Under $`a \lt b`$, show that the stage interpretations agree with the true ones wherever a formula reads (`sat_congr`, [03](03-sigma1-elementary.md) §8).

1. Internal relation: only places where the second point is below the height are read. The height is $`a`$ or $`b`$, both at most $`b`$, so the guard $`y \lt b`$ is true.
2. Top at height $`a`$: the guard is $`a \lt b`$, which is the assumption.
3. Top at height $`b`$: only the defined keys $`\kappa \lt \theta`$ are read, and the guard $`\kappa \lt \theta`$ is exactly this.

So the truth values agree, and the equation without guards follows. $`\square`$

## 7. Properties that follow directly

**Theorem (`R_lt`).** If $`R(\theta, a, b)`$ then $`a \lt b`$. This is the first component of `R_iff`.

**Theorem (`key_weaken`, key weakening).** If $`\theta \le \Theta`$ and $`R(\Theta, a, b)`$, then $`R(\theta, a, b)`$.

**Proof.** `R_iff` gives $`a \lt b`$ and the elementarity $`E`$ at key $`\Theta`$. For a formula $`\varphi`$ and parameters $`\vec p \lt a`$, show both directions at key $`\theta`$.

- From height $`a`$ to height $`b`$: take a witness $`w`$ at height $`a`$. Make the formula $`\varphi'`$ in which every position is a parameter (the parameters are $`w`$, all below $`a`$). Since $`\theta \le \Theta`$, $`w`$ satisfies $`\varphi'`$ at key $`\Theta`$ too (`Lit.holds_allow_mono`). By $`E`$, $`\varphi'`$ is true at height $`b`$ at key $`\Theta`$. All variables are fixed, so the witness is $`w`$ itself. The key of a top literal depends only on $`w`$, and it was below $`\theta`$ at height $`a`$. So the literal holds at height $`b`$ at key $`\theta`$ (`Lit.holds_of_le` with $`w \le w`$).
- From height $`b`$ to height $`a`$: take a witness $`v`$ at height $`b`$. Make the formula $`\varphi'`$ whose parameters are the positions with $`v_i \lt a`$. Since $`\theta \le \Theta`$, $`v`$ satisfies $`\varphi'`$ at key $`\Theta`$. By $`E`$ there is a witness $`w`$ at height $`a`$ with $`w_i = v_i`$ at the positions where $`v_i \lt a`$. At the other positions $`w_i \lt a \le v_i`$. So $`w \le v`$ pointwise. The key of a top literal satisfies $`\mathrm{eval}\ t\ w \le \mathrm{eval}\ t\ v \lt \theta`$, so $`w`$ also works at key $`\theta`$ (`Lit.holds_of_le`). The original parameter positions have $`p_i \lt a`$, so $`w`$ agrees with $`p`$ there. $`\square`$

The second direction needs lowering the witnesses pointwise. That is why the monotonicity of `eval` (`monotone_eval` in [06](06-combinatorial-layer.md) §1) is used.

**Property (defined top predicates agree).** Let $`R(\theta, a, b)`$ and $`\vec v \lt a`$. If $`\mathrm{eval}\ t\ \vec v \lt \theta`$, then:

```math
R(\mathrm{eval}\ t\ \vec v,\ v_i,\ a) \iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ b)
```

**Reason.** Use the formula $`\mathrm{Top}_{t,i}(\vec v)`$ in which every variable is a parameter. At height $`a`$ it means the left side, at height $`b`$ the right side. This property is not stated as a Lean theorem. The proofs use the similar `top_abs` (agreement of top predicates between a Good point and $`\omega_1`$, [09](09-obligations.md) §3). Good is defined in [08](08-closure-chain.md) §1.

**Property (the lower point is a limit ordinal).** If the labels are ordinals and $`R(\theta, a, b)`$, then $`a`$ is a nonzero limit ordinal.

**Reason.** The same as the example of [03](03-sigma1-elementary.md) §5.

- If $`a = 0`$: the formula $`\exists v_0\ (\text{true})`$ with one variable, no parameters and no literals is true at height $`b`$ and false at height 0.
- If $`a = \gamma + 1`$: with parameter $`\gamma \lt a`$, $`\exists v_1\ (\gamma \lt v_1)`$ is true at height $`b`$ ($`v_1 = \gamma + 1 \lt b`$) and false at height $`a`$.

Both contradict elementarity. This property is not proved in Lean, and the combinatorial layer does not use it.

## 8. Properties not used

**Transitivity.** $`R(\theta, a, b) \land R(\theta, b, c) \implies R(\theta, a, c)`$. The middle structure $`\mathfrak A^b_\theta`$ is the same in both relations, so for formulas with parameters $`\vec p \lt a`$ the two equivalences can be chained. This property is not proved in Lean, and the combinatorial layer does not use it.

## 9. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "The relation R" | the defining formula and the stages |
| [README](../../README-en.md) "Proofs of the three theorems" | summary of the proof of key weakening |
| [notes/01-design.md](../../notes/01-design.md) §2, §3.1 | definition, recursion, key weakening |
| [Por/Relation.lean](../../Por/Relation.lean) | everything in this note |
| [OmegaY/Reflection.lean](../../OmegaY/Reflection.lean) | gives `Reflection.R` by `Por.R` and `Reflection.key_weaken` by `Por.key_weaken` |

## 10. Lean correspondence

| Concept | Lean | File |
|---|---|---|
| stages and their order | `StageLT`, `stage_wf` | [Por/Relation.lean](../../Por/Relation.lean) |
| one step of the recursion | `stepF` | same |
| the relation | `R` | same |
| true interpretations | `relR`, `topR` | same |
| defining equation | `R_iff` | same |
| strictly smaller | `R_lt` | same |
| key weakening | `key_weaken` | same |
| elementarity, truth | `ElemL`, `Sat` | [Por/Formula.lean](../../Por/Formula.lean) |
| only what is read matters | `sat_congr` | same |
| parts of key weakening | `Lit.holds_allow_mono`, `Lit.holds_of_le` | same |
