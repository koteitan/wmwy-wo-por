[← Back](README.md) | [English](02-well-founded.md) | [Japanese](../02-well-founded.md)

# Well-founded relations and recursion

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | ordinal, infinite descending sequence, labels $`\{o \le \omega_1\}`$ |

This note explains three things: well-founded relations, well-founded recursion, and termination by decreasing labels. The definition of the relation $`R`$ ([07](07-relation-r.md)) has the form of §4 and §5. The overall proof ([06](06-combinatorial-layer.md)) has the form of §6.

## 1. Well-founded relations

**Definition (well-founded).** A relation $`\prec`$ on a set $`X`$ is **well-founded** if every nonempty subset $`S`$ of $`X`$ has a $`\prec`$-minimal element, that is, an $`x \in S`$ with no $`y \in S`$ such that $`y \prec x`$.

A relation is well-founded if and only if there is no infinite descending sequence $`x_0 \succ x_1 \succ x_2 \succ \cdots`$. The direction "no infinite descending sequence implies well-founded" uses a weak form of the axiom of choice (dependent choice).

**Definition in Lean.** Lean uses `Acc` (accessibility).

- `Acc r x` holds when `Acc r y` holds for every $`y`$ with $`r\,y\,x`$. It is defined inductively.
- `WellFounded r` means `Acc r x` for every $`x`$.

`Acc r x` means "every sequence that follows $`r`$ backwards from $`x`$ stops".

| Relation | Well-founded? | Lean |
|---|---|---|
| $`\lt`$ on $`\mathbb N`$ | yes | `wellFounded_lt` |
| $`\lt`$ on ordinals, on labels | yes | `wellFounded_lt` |
| $`\lt`$ on keys (§3) | yes | `OmegaY.Keys.key_wellFounded` |
| $`\lt`$ on $`\mathbb Z`$ | no | |
| lexicographic order on all legal expressions | no | `OmegaY.Expansion.Dynamics.not_wellFounded_lex_all_legal` |

Example for the last row. In the lexicographic order on expressions a proper prefix is smaller, and otherwise the first differing entry decides. This gives the infinite descending sequence below (the sequence `onesThenTwo` inside the Lean proof).

```math
(1,2) \gt (1,1,2) \gt (1,1,1,2) \gt (1,1,1,1,2) \gt \cdots
```

Expansion in ω-Y decreases the lexicographic order (`Dynamics.next_lex`, [05](05-omegay-mountain.md) §7). Still, the lexicographic order alone does not give termination. So labels are used (§6).

## 2. Well-founded induction

**Theorem (well-founded induction).** Let $`\prec`$ be well-founded, and let a property $`P`$ satisfy:

```math
\forall x\ \Bigl(\bigl(\forall y \prec x\ \ P(y)\bigr) \implies P(x)\Bigr)
```

Then $`P(x)`$ holds for every $`x`$.

**Proof.** Suppose the set of $`x`$ where $`P`$ fails is nonempty. Take a minimal element $`x`$. For $`y \prec x`$, $`P(y)`$ holds. By the assumption $`P(x)`$ holds, a contradiction. $`\square`$

In Lean this is `WellFounded.induction` and `WellFoundedLT.induction`. The proof of `top_abs` in [09 Proofs of the three theorems](09-obligations.md) uses it on the order of keys.

## 3. Lexicographic products and the order of keys

**Definition (lexicographic product).** For $`(A, \lt_A)`$ and $`(B, \lt_B)`$, the **lexicographic order** on $`A \times B`$ is:

```math
(a, b) \prec (a', b') \iff a \lt_A a' \ \lor\ (a = a' \land b \lt_B b')
```

**Theorem.** If $`\lt_A`$ and $`\lt_B`$ are well-founded, so is the lexicographic order.

**Proof.** Do well-founded induction on $`b`$ inside well-founded induction on $`a`$. A pair below $`(a, b)`$ either has $`a' \lt_A a`$ (accessible by the outer induction hypothesis) or has the same $`a`$ and $`b' \lt_B b`$ (accessible by the inner induction hypothesis). $`\square`$

**Example.** In $`\mathbb N \times \mathbb N`$ there are infinitely many pairs below $`(1, 0)`$: $`(0, 0), (0, 1), (0, 2), \ldots`$. Still every descending sequence is finite. For example $`(1,0) \succ (0, 100) \succ (0, 99) \succ \cdots \succ (0, 0)`$ stops after 102 terms.

In Lean this is `Prod.Lex` and `WellFounded.prod_lex`. The stages of the recursion for $`R`$ are ordered in this way ([Por/Relation.lean](../../Por/Relation.lean)).

```math
(b', \kappa') \lhd (b, \theta) \iff b' \lt b\ \lor\ (b' = b \land \kappa' \lt \theta)
```

$`b`$ is a label (the top) and $`\kappa`$ is a key. In Lean these are `StageLT := Prod.Lex (· < ·) (· < ·)` and `stage_wf`.

**Definition (key).** A **key** of length $`m`$ is a sequence of $`m`$ entries, each a label or $`\top`$. $`\top`$ is greater than every label.

```math
\mathrm{Key}_m = \mathrm{Lex}\bigl(\mathrm{Fin}\ m \to \mathrm{Label} \cup \{\top\}\bigr)
```

The order is lexicographic: compare at the **first coordinate where they differ**. In Lean this is `OmegaY.Keys.Key m Label := Lex (Fin m → WithTop Label)`.

| Two keys ($`m = 2`$) | Result | Reason |
|---|---|---|
| $`(3, 5)`$ and $`(3, \top)`$ | $`(3, 5) \lt (3, \top)`$ | equal at coordinate 0, $`5 \lt \top`$ at coordinate 1 |
| $`(2, \top)`$ and $`(3, 0)`$ | $`(2, \top) \lt (3, 0)`$ | $`2 \lt 3`$ at coordinate 0 |
| $`(\omega, 0)`$ and $`(5, \top)`$ | $`(5, \top) \lt (\omega, 0)`$ | $`5 \lt \omega`$ at coordinate 0 |

**Theorem (`key_wellFounded`).** The order on $`\mathrm{Key}_m`$ is well-founded.

**Proof.** $`\mathrm{Label} \cup \{\top\}`$ is well-founded: a descending sequence contains $`\top`$ at most once, as its first term, and the rest is a descending sequence of labels. The lexicographic order on sequences of length $`m`$ is the same order as the lexicographic product above iterated $`m - 1`$ times. So it is well-founded. $`\square`$

In Lean it is obtained as `wellFounded_lt` from a Mathlib instance (the lexicographic order over a finite index type is well-founded).

## 4. Well-founded recursion

**Theorem (well-founded recursion).** Let $`\prec`$ be a well-founded relation on $`T`$. Suppose a rule $`G`$ takes $`t \in T`$ and "the values at keys smaller than $`t`$" and returns the value at $`t`$. Then there is exactly one function $`F`$ with:

```math
F(t) = G\bigl(t,\ F{\restriction}\{t' \mid t' \prec t\}\bigr)
```

**Example (the Ackermann function).** Take $`\mathbb N \times \mathbb N`$ with the lexicographic order as keys.

```math
\begin{aligned}
A(0, n) &= n + 1, \cr
A(m+1, 0) &= A(m, 1), \cr
A(m+1, n+1) &= A\bigl(m,\ A(m+1, n)\bigr).
\end{aligned}
```

The keys $`(m, 1)`$, $`(m+1, n)`$, $`(m, \cdot)`$ called on the right are all lexicographically smaller than the key on the left. So well-founded recursion defines $`A`$.

**The form in Lean.** `WellFounded.fix` takes the rule $`G`$ with this type:

```lean
G : (t : T) → ((t' : T) → r t' t → V) → V
```

The second argument (called `IH` below) takes a key `t'` together with a proof that `t'` is smaller. It cannot be called without the proof. The defining equation is `WellFounded.fix_eq`.

## 5. Guarded recursion

In the definition of $`R`$, "which stage is read" depends on the values of variables in a formula. We cannot say in advance that the stage read is smaller. So the definition takes this form:

1. Write the value to be read as $`\exists h : (\text{the stage is smaller}),\ \mathrm{IH}(\text{stage}, h)`$. This is a **guard**. Where the stage is not smaller, the expression is false.
2. Obtain the defining equation `fix_eq`. At this point the right side carries guards.
3. Show that the guards are always true where the right side actually reads. This gives the equation without guards.

In [07 The relation R](07-relation-r.md), step 1 is `stepF`, and steps 2 and 3 are the proof of `R_iff`.

**Small example.** On $`\mathbb N`$ consider a definition $`F(n) := 1 + \sum_{i \in S_n} F(i)`$, where $`S_n`$ is a given finite set for each $`n`$ that may contain numbers $`\ge n`$. As written this is not a well-founded recursion. With a guard, $`F(n) := 1 + \sum_{i \in S_n,\ i \lt n} F(i)`$ is defined by well-founded recursion. If $`S_n \subseteq \{0, \ldots, n-1\}`$ is shown separately, the unguarded equation $`F(n) = 1 + \sum_{i \in S_n} F(i)`$ holds.

## 6. Termination by a bound on labels

We show that a one-step relation $`\to`$ on a set of states $`X`$ is well-founded, using labels in a well-founded order $`(L, \lt)`$.

**Theorem.** Suppose a relation $`\mathrm{valid}(s, \alpha)`$ between states and labels satisfies:

- There is $`\alpha_0`$ with $`\mathrm{valid}(s, \alpha_0)`$ for every state $`s`$.
- If $`\mathrm{valid}(s, \alpha)`$ and $`s \to t`$, then $`\mathrm{valid}(t, \alpha')`$ for some $`\alpha' \lt \alpha`$.

Then $`\to`$ is well-founded: there is no infinite sequence $`s_0 \to s_1 \to s_2 \to \cdots`$.

**Proof.** By well-founded induction on $`\alpha`$, show "if $`\mathrm{valid}(s, \alpha)`$ then $`s`$ is accessible". If $`s \to t`$, then $`t`$ has some $`\alpha' \lt \alpha`$, so $`t`$ is accessible by the induction hypothesis. $`\square`$

The point is that a state need not have a unique label. We only use "there is some labelling" and "after one step there is a labelling with a smaller bound".

The ω-Y proof applies it as follows ([06](06-combinatorial-layer.md) §8).

| General form | ω-Y |
|---|---|
| state | expression $`s`$ (`Dynamics.Expr`) |
| $`s \to t`$ | one expansion step `Dynamics.Step t s` ($`s \ne ()`$ and $`t = s[N]`$) |
| label | `Model.Label` (ordinals at most $`\omega_1`$) |
| $`\mathrm{valid}(s, \alpha)`$ | the mountain of $`s`$ has a representation of dimension $`D`$ whose labels are all below $`\alpha`$ ($`D`$ is fixed by the starting expression) |
| $`\alpha_0`$ | $`\omega_1`$ (`keyRepresentation_exists` and `KeyRepresentation.bounded`) |
| $`\alpha'`$ | the last label of the old representation (the label of the last column) |

The Lean proof is `Dynamics.accessible_of_representation_below`, which writes the same induction directly ([OmegaY/Expansion/DynamicsRepresentationRank.lean](../../OmegaY/Expansion/DynamicsRepresentationRank.lean)). The 1-Y version did induction on the last label itself. The ω-Y version does induction on a bound $`\alpha`$ of all labels. So when the result of expansion is the empty expression, no last label is needed. There is no expansion step from the empty expression (the definition of `Step` requires $`s \ne ()`$; `Dynamics.empty_accessible`).

## 7. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "The relation R" | well-founded recursion on the lexicographic order of (top, key) |
| [notes/01-design.md](../../notes/01-design.md) §2.3 | the order of stages and the stages read on the right side |
| [Por/Relation.lean](../../Por/Relation.lean) | §3–§5 (`StageLT`, `stage_wf`, `stepF`, `R`, `R_iff`) |
| [Por/Supply.lean](../../Por/Supply.lean) | §2 (the induction on keys in `top_abs`) |
| [OmegaY/Keys.lean](../../OmegaY/Keys.lean) | §3 (the order of keys and `key_wellFounded`) |
| [OmegaY/Expansion/DynamicsRepresentationRank.lean](../../OmegaY/Expansion/DynamicsRepresentationRank.lean) | §6 (induction on a bound of labels) |

## 8. Lean correspondence

| Concept | Lean | File |
|---|---|---|
| accessibility | `Acc` | Lean core |
| well-founded | `WellFounded` | Lean core |
| well-founded induction | `WellFounded.induction`, `WellFoundedLT.induction` | Lean core, Mathlib |
| lexicographic product | `Prod.Lex`, `WellFounded.prod_lex` | same |
| well-founded recursion and its equation | `WellFounded.fix`, `WellFounded.fix_eq` | Lean core |
| stages and their order | `StageLT`, `stage_wf` | [Por/Relation.lean](../../Por/Relation.lean) |
| one guarded step | `stepF` | same |
| removing the guards | `R_iff` | same |
| keys and their order | `Keys.Key`, `Keys.key_wellFounded` | [OmegaY/Keys.lean](../../OmegaY/Keys.lean) |
| lexicographic order on expressions is not well-founded | `Dynamics.not_wellFounded_lex_all_legal` | [OmegaY/Expansion/LegalDomainBoundary.lean](../../OmegaY/Expansion/LegalDomainBoundary.lean) |
| termination by a bound on labels | `Dynamics.accessible_of_representation_below`, `Dynamics.empty_accessible` | [OmegaY/Expansion/DynamicsRepresentationRank.lean](../../OmegaY/Expansion/DynamicsRepresentationRank.lean) |
