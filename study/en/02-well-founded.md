[← Back](README.md) | [English](02-well-founded.md) | [Japanese](../02-well-founded.md)

# Well-founded relations and well-founded recursion

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | ordinal, $`\mathrm{Ord}`$, infinite descending sequence, $`\lt`$ is well-founded, labels $`\mathrm{Label}`$ (§6), $`\mathrm{Fin}\ m`$ (§7) |

This note explains well-founded relations and well-founded recursion. The definition of the relation $`R`$ ([07](07-relation-r.md)) has the form of §4 and §5. The proof that expansion terminates ([06](06-combinatorial-layer.md) §8) has the form of §6.

## 1. Well-founded relations

**Definition (well-founded).** A relation $`\prec`$ on a set $`X`$ is **well-founded** if every nonempty subset $`S`$ of $`X`$ has a $`\prec`$-minimal element, that is, some $`x \in S`$ such that no $`y \in S`$ has $`y \prec x`$.

Being well-founded is equivalent to having no infinite descending sequence $`x_0 \succ x_1 \succ x_2 \succ \cdots`$. The direction "no infinite descending sequence implies well-founded" uses a weak form of the axiom of choice (dependent choice).

**Definition (accessible).** $`x`$ is **accessible** if every $`y`$ with $`y \prec x`$ is accessible. This is an inductive definition: the set of accessible elements is the least set closed under this condition.

That $`x`$ is accessible means "every sequence that follows $`\prec`$ backwards from $`x`$ stops". $`\prec`$ is well-founded if and only if every $`x`$ is accessible.

| Relation | Well-founded? |
|---|---|
| $`\lt`$ on $`\mathbb N`$ | yes |
| $`\lt`$ on ordinals (also $`\lt`$ on labels) | yes |
| $`\lt`$ on $`\mathbb Z`$ | no |
| lexicographic order on ω-Y expressions | no |

The last row. An ω-Y expression is a finite sequence of positive integers, defined in [05](05-omegay-mountain.md) §1. In the lexicographic order of expressions a proper prefix is smaller, and otherwise the first differing entry decides. So there is an infinite descending sequence.

```math
(1,2) \gt (1,1,2) \gt (1,1,1,2) \gt (1,1,1,1,2) \gt \cdots
```

An ω-Y expansion lowers the lexicographic order ([05](05-omegay-mountain.md) §7). Still, the lexicographic order alone does not give termination. So labels ([01](01-ordinals.md) §6) are attached to the columns of expressions, and it is shown that expansion lowers them (§6, [06](06-combinatorial-layer.md) §8).

## 2. Well-founded induction

**Theorem (well-founded induction).** Let $`\prec`$ be well-founded and let a property $`P`$ satisfy

```math
\forall x\ \Bigl(\bigl(\forall y \prec x\ \ P(y)\bigr) \implies P(x)\Bigr)
```

Then $`P(x)`$ holds for every $`x`$.

**Proof.** Suppose the set of $`x`$ where $`P`$ fails is nonempty. Take a minimal element $`x`$. For $`y \prec x`$, $`P(y)`$ holds. By the assumption $`P(x)`$ holds, a contradiction. $`\square`$

The theorem (absoluteness of the top predicates) of [09 Proofs of the three theorems](09-obligations.md) §3.1 uses it with the order of keys (§3).

## 3. Lexicographic products

**Definition (lexicographic product).** For $`(A, \lt_A)`$ and $`(B, \lt_B)`$, the **lexicographic order** on $`A \times B`$ is

```math
(a, b) \prec (a', b') \iff a \lt_A a' \ \lor\ (a = a' \land b \lt_B b')
```

**Theorem.** If $`\lt_A`$ and $`\lt_B`$ are well-founded, so is the lexicographic order.

**Proof.** Do well-founded induction on $`b`$ inside well-founded induction on $`a`$. A pair below $`(a, b)`$ either has $`a' \lt_A a`$ (accessible by the outer induction hypothesis) or has the same $`a`$ and $`b' \lt_B b`$ (accessible by the inner induction hypothesis). $`\square`$

**Example.** In $`\mathbb N \times \mathbb N`$, the pairs below $`(1, 0)`$ are $`(0, 0), (0, 1), (0, 2), \ldots`$, infinitely many. Still every descending sequence is finite. For example $`(1,0) \succ (0, 100) \succ (0, 99) \succ \cdots \succ (0, 0)`$ stops after 102 terms.

**Definition (key).** Let $`\top`$ be a new element that is not a label and is larger than every label. Write $`\mathrm{Label}_\top := \mathrm{Label} \cup \{\top\}`$. Since $`\omega_1`$ is a label, $`\omega_1 \lt \top`$. Let $`m \in \mathbb N`$. A **key** of length $`m`$ is a list $`\kappa = (\kappa_0, \ldots, \kappa_{m-1})`$ of $`m`$ elements of $`\mathrm{Label}_\top`$. $`\kappa_i`$ is called **coordinate** $`i`$ of $`\kappa`$. The set of keys is written $`\mathrm{Key}_m`$.

```math
\mathrm{Key}_m := \mathrm{Fin}\ m \to \mathrm{Label}_\top
```

Keys are ordered lexicographically: the first coordinate where they differ decides.

```math
\kappa \lt \kappa' \iff \exists i \lt m\ \Bigl(\bigl(\forall j \lt i\ \ \kappa_j = \kappa'_j\bigr) \land \kappa_i \lt \kappa'_i\Bigr)
```

| Two keys ($`m = 2`$) | Result | Reason |
|---|---|---|
| $`(3, 5)`$ and $`(3, \top)`$ | $`(3, 5) \lt (3, \top)`$ | coordinate 0 is equal, coordinate 1 has $`5 \lt \top`$ |
| $`(2, \top)`$ and $`(3, 0)`$ | $`(2, \top) \lt (3, 0)`$ | coordinate 0 has $`2 \lt 3`$ |
| $`(\omega, 0)`$ and $`(5, \top)`$ | $`(5, \top) \lt (\omega, 0)`$ | coordinate 0 has $`5 \lt \omega`$ |

The comparisons of the table were checked with this definition written in Python.

**Theorem.** The order of $`\mathrm{Key}_m`$ is well-founded.

**Proof.** $`\mathrm{Label}_\top`$ is well-founded: a descending sequence contains $`\top`$ at most once, as its first term, and the rest is a descending sequence of labels. The lexicographic order on lists of length $`m`$ is the same order as the lexicographic product above taken $`m - 1`$ times. So it is well-founded by the theorem above. $`\square`$

**Definition (stage and top).** The third argument $`b`$ of the relation $`R(\theta, a, b)`$ (defined in [07](07-relation-r.md); $`\theta \in \mathrm{Key}_m`$, $`a, b \in \mathrm{Label}`$) is called the **top**. The well-founded recursion (§4) for $`R`$ takes the pair $`(b, \theta) \in \mathrm{Label} \times \mathrm{Key}_m`$ as its argument. This pair is called a **stage**. The order $`\lhd`$ of stages is the lexicographic product of the order of labels and the order of keys.

```math
(b', \kappa') \lhd (b, \theta) \iff b' \lt b\ \lor\ (b' = b \land \kappa' \lt \theta)
```

By the two theorems above, $`\lhd`$ is well-founded. A stage is unrelated to the "step" of a one-step expansion ([05](05-omegay-mountain.md) §7).

## 4. Well-founded recursion

**Theorem (well-founded recursion).** Let $`\prec`$ be a well-founded relation on $`T`$. In well-founded recursion the elements of $`T`$ are called the **arguments** of the function. Suppose a rule $`G`$ takes $`t \in T`$ and "the values at arguments smaller than $`t`$" and returns the value at $`t`$. Then there is exactly one function $`F`$ with

```math
F(t) = G\bigl(t,\ F{\restriction}\{t' \mid t' \prec t\}\bigr)
```

Here $`F{\restriction}X`$ is the function $`F`$ with its domain restricted to the set $`X`$.

**Example (Ackermann function).** Take $`\mathbb N \times \mathbb N`$ as the set of arguments, compared lexicographically.

```math
\begin{aligned}
A(0, n) &= n + 1, \cr
A(m+1, 0) &= A(m, 1), \cr
A(m+1, n+1) &= A\bigl(m,\ A(m+1, n)\bigr).
\end{aligned}
```

The arguments called on the right, $`(m, 1)`$, $`(m+1, n)`$ and $`(m, \cdot)`$, are all lexicographically smaller than the argument on the left. So well-founded recursion defines $`A`$.

The rule $`G`$ may read only the values $`F(t')`$ at arguments $`t'`$ with $`t' \prec t`$.

## 5. Guarded recursion

In the definition of $`R`$ ([07](07-relation-r.md)), which stages (§3) are read depends on the values of variables inside a formula (defined in [03](03-sigma1-elementary.md) §2). Before writing the definition we cannot say that the stages read are smaller. So we proceed as follows.

1. Wherever the value at an argument $`t'`$ is read, write "$`t' \prec t \land F(t')`$". We call the first condition $`t' \prec t`$ a **guard**. Where the argument is not smaller, this expression is false.
2. By the theorem of §4, get the defining equation $`F(t) = G(t, F{\restriction}\{t' \mid t' \prec t\})`$. At this stage the right side still contains the guards.
3. Show that the guard is always true wherever the right side actually reads a value. Then the equation without guards follows.

In [07 The relation R](07-relation-r.md), step 1 is the stage interpretations of §5, step 2 is the guarded equation of §5, and step 3 is the lemma and the theorem of §6.

**A small example.** On $`\mathbb N`$ consider a definition of the form $`F(n) := 1 + \sum_{i \in S_n} F(i)`$, where $`S_n`$ is a given finite set for each $`n`$ that may contain numbers $`\ge n`$. So as it stands, this is not a well-founded recursion. Written with the guard, $`F(n) := 1 + \sum_{i \in S_n,\ i \lt n} F(i)`$, it is defined by well-founded recursion. If $`S_n \subseteq \{0, \ldots, n-1\}`$ is shown separately, the equation without the guard, $`F(n) = 1 + \sum_{i \in S_n} F(i)`$, holds.

## 6. Termination by upper bounds of labels

**Theorem (termination by upper bounds of labels).** Let $`(L, \lt)`$ be a well-founded order, $`X`$ a set and $`\prec`$ a relation on $`X`$. Suppose a relation $`V \subseteq X \times L`$ between $`X`$ and $`L`$ satisfies the following two conditions.

```math
\begin{aligned}
&\exists \alpha_0 \in L\ \ \forall s \in X\ \ V(s, \alpha_0), \cr
&\forall s, t \in X\ \ \forall \alpha \in L\ \ \Bigl(V(s, \alpha) \land t \prec s \implies \exists \alpha' \lt \alpha\ \ V(t, \alpha')\Bigr).
\end{aligned}
```

Then $`\prec`$ is well-founded.

**Proof.** By well-founded induction on $`\alpha`$ (§2) we show

```math
\forall \alpha \in L\ \ \forall s \in X\ \ \bigl(V(s, \alpha) \implies s \text{ is accessible}\bigr)
```

Let $`V(s, \alpha)`$. If $`t \prec s`$, the second condition gives $`\alpha' \lt \alpha`$ with $`V(t, \alpha')`$. By the induction hypothesis $`t`$ is accessible. So $`s`$ is accessible (§1). By the first condition every $`s`$ satisfies $`V(s, \alpha_0)`$, so every $`s`$ is accessible. $`\square`$

- $`V`$ need not be a function. One $`s`$ may have many $`\alpha`$ with $`V(s, \alpha)`$.
- [06](06-combinatorial-layer.md) §8 uses this theorem with $`X`$ the set of expressions, $`t \prec s`$ the one-step expansion ([05](05-omegay-mountain.md) §7) and $`L = \mathrm{Label}`$. What $`V(s, \alpha)`$ is, is said in [06](06-combinatorial-layer.md) §8.
- The 1-Y version ([01](01-ordinals.md) §7), in its note 06 §6, did induction on the last label of a representation itself. Here the induction is on an upper bound $`\alpha`$ of the labels.

## 7. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "Structure of the proof" | the keys $`\mathrm{Key}_m`$ and their order (§3) |
| [README](../../README-en.md) "The relation R" | well-founded recursion on the lexicographic order of stages (top, key) (§3–§5) |
| [notes/01-design.md](../../notes/01-design.md) §2.3 (Japanese) | the order of stages and the stages read on the right side |

## 8. Lean correspondence

| Concept | Lean | File |
|---|---|---|
| accessible, well-founded | `Acc`, `WellFounded` | Lean core |
| well-founded induction | `WellFounded.induction`, `WellFoundedLT.induction` | Lean core, Mathlib |
| lexicographic product | `Prod.Lex`, `WellFounded.prod_lex` | same |
| well-founded recursion and its equation | `WellFounded.fix`, `WellFounded.fix_eq` | Lean core |
| $`\mathrm{Label}_\top`$ | `WithTop Label` | Mathlib |
| keys and their order | `Keys.Key m Label := Lex (Fin m → WithTop Label)`, `Keys.key_wellFounded` | [OmegaY/Keys.lean](../../OmegaY/Keys.lean) |
| stages and their order | `StageLT := Prod.Lex (· < ·) (· < ·)`, `stage_wf` | [Por/Relation.lean](../../Por/Relation.lean) |
| guarded step, removing the guards (§5) | `stepF`, `R_iff` | same |
| the lexicographic order of expressions is not well-founded (§1) | `Dynamics.not_wellFounded_lex_all_legal` (the sequence `onesThenTwo` in its proof) | [OmegaY/Expansion/LegalDomainBoundary.lean](../../OmegaY/Expansion/LegalDomainBoundary.lean) |
| expansion lowers the lexicographic order | `Dynamics.next_lex` | [OmegaY/Expansion/LegalDynamics.lean](../../OmegaY/Expansion/LegalDynamics.lean) |
| termination by upper bounds of labels (§6) | `Dynamics.accessible_of_representation_below`, `Dynamics.empty_accessible` | [OmegaY/Expansion/DynamicsRepresentationRank.lean](../../OmegaY/Expansion/DynamicsRepresentationRank.lean) |
