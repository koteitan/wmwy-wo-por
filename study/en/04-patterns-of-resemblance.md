[← Back](README.md) | [English](04-patterns-of-resemblance.md) | [Japanese](../04-patterns-of-resemblance.md)

# Patterns of resemblance

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | ordinal, limit ordinal |
| [02 Well-founded relations and recursion](02-well-founded.md) | well-founded recursion, guarded recursion, keys $`\mathrm{Key}_m`$, stage, top |
| [03 Structures and Σ₁-elementary substructures](03-sigma1-elementary.md) | structure $`(\gamma; \ldots)`$, $`\Sigma_1`$ formula, witness, $`\preccurlyeq_{\Sigma_1}`$, template, internal relation, top predicate, partial top predicates |

This note explains the idea of Carlson's patterns of resemblance. Next it describes how [bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) used it for BMS (the Bashicu matrix system, a system of sequences that expands matrices). Finally it says why it is not enough as it stands for ω-Y, and what this repository changes.

## 1. A relation that has itself in its language

**Definition (Carlson's ≤₁).** Define the relation $`\le_1`$ on ordinals, for ordinals $`\alpha, \beta`$, by the formula below. The structures on the right are written as in [03](03-sigma1-elementary.md) §1, and the language is $`\{\le, \le_1\}`$.

```math
\alpha \le_1 \beta \iff \alpha \le \beta \ \land\ (\alpha; \le, \le_1) \preccurlyeq_{\Sigma_1} (\beta; \le, \le_1)
```

$`\alpha \lt_1 \beta`$ means $`\alpha \lt \beta \land \alpha \le_1 \beta`$.

**Reading.** "The shape of the ordinals below $`\alpha`$ cannot be distinguished by $`\Sigma_1`$ formulas from its extension up to $`\beta`$." Here the shape consists of the order and the relation $`\le_1`$ itself.

The right side uses the $`\le_1`$ of the left side. It looks circular, but it can be defined by well-founded recursion on $`\beta`$.

- The domain of $`(\beta; \le, \le_1)`$ is $`\{x \mid x \lt \beta\}`$. The only instances of $`\le_1`$ read there are $`x \le_1 y`$ with $`x, y \lt \beta`$.
- Since $`y \lt \beta`$, the truth of $`x \le_1 y`$ is already fixed earlier in the recursion, before $`\beta`$.
- The same holds for $`(\alpha; \ldots)`$, and $`\alpha \le \beta`$.

Carlson studied the structures that extend this to $`\le_1, \ldots, \le_N`$ ($`\Sigma_1`$- to $`\Sigma_N`$-elementarity).

```math
\mathcal R_N = (\mathrm{Ord}; \le, \le_1, \ldots, \le_N)
```

$`\mathrm{Ord}`$ is the class of all ordinals. $`N`$ is a positive integer.

Reference: T. J. Carlson, Elementary patterns of resemblance, Annals of Pure and Applied Logic 108 (2001), 19–77.

## 2. Small examples

**Example 1.** For a natural number $`n \lt \beta`$, $`n \le_1 \beta`$ fails.

- If $`n \ge 1`$: with parameter $`n - 1`$, $`\exists x\ (n - 1 \lt x)`$ is true in $`\beta`$ ($`x = n`$) and false in $`n`$.
- If $`n = 0`$: $`\exists x\ (x \le x)`$ is true in $`\beta`$ and false in the empty structure $`0`$.

For the same reason, a successor ordinal $`\gamma + 1`$ is not in the relation $`\le_1`$ with any larger ordinal.

**Example 2.** $`\omega \lt_1 \omega + 1`$.

By Example 1, no two distinct points below $`\omega + 1`$ are in the relation $`\le_1`$: pairs of natural numbers by Example 1, and the only other point is $`\omega`$ itself. So in $`(\omega; \le, \le_1)`$ and $`(\omega + 1; \le, \le_1)`$, $`x \le_1 y`$ is the same as $`x = y`$. Then we compare the order-only structures $`(\omega; \le)`$ and $`(\omega + 1; \le)`$, and since $`\omega`$ is a limit, the example of [03](03-sigma1-elementary.md) §5 applies.

**Example 3.** If $`\beta \ge \omega + 2`$, then $`\omega \le_1 \beta`$ fails. $`\exists x\ \exists y\ (x \lt y \land x \le_1 y)`$ is true in $`\beta`$ (the $`x = \omega`$, $`y = \omega + 1`$ of Example 2 are both below $`\beta`$) and false in $`\omega`$ (Example 1).

$`\omega \le_1 \omega`$ holds by definition. So $`\{\beta \mid \omega \le_1 \beta\} = \{\omega, \omega + 1\}`$.

In the order-only language, $`(\omega; \le) \preccurlyeq_{\Sigma_1} (\beta; \le)`$ held for every $`\beta \gt \omega`$. Putting $`\le_1`$ itself into the language made the relation finer.

## 3. Use in termination proofs

An expansion ([05](05-omegay-mountain.md) §4) is an operation that makes a new sequence from a sequence. Each entry of the sequence is called a column ([05](05-omegay-mountain.md) §1). A termination proof of an expansion puts an ordinal label ([01](01-ordinals.md) §6) on each column and shows that the labels decrease under expansion ([02](02-well-founded.md) §6). The property needed there is **finite reflection**.

**The shape of finite reflection.** Let $`\alpha \lt_1 \beta`$. Suppose points $`\vec p`$ below $`\alpha`$ and points $`\vec y`$ below $`\beta`$ satisfy finitely many atomic conditions $`\psi(\vec p, \vec y)`$. Then there are points $`\vec y'`$ below $`\alpha`$ with $`\psi(\vec p, \vec y')`$.

**Reason.** $`\exists \vec y\ \psi(\vec p, \vec y)`$ is a $`\Sigma_1`$ formula true in $`(\beta; \ldots)`$. By $`\Sigma_1`$-elementarity it is true in $`(\alpha; \ldots)`$.

In an expansion this is used as follows. Choose a column and call it the cut ([06](06-combinatorial-layer.md) §5). Let $`\alpha`$ be the old label of the cut column. Let $`\vec p`$ be the old labels of the columns before the cut, and $`\vec y`$ the old labels of the columns that get new labels. The $`\vec y`$ are all at least $`\alpha`$. $`\psi`$ states relations between the labels of columns, for example that the labels of two columns joined by an edge of the mountain ([05](05-omegay-mountain.md) §3), a parent and a child, satisfy $`\le_1`$ and so on. The new labels $`\vec y'`$ given by finite reflection satisfy the same relations, and they are all below $`\alpha`$. So the new labels are smaller than the old ones.

**Use in bms-elem-pattern.** [bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) proved termination of BMS with $`\mathcal R_N`$. The labels of two columns that are parent and child in row $`k`$ of a BMS matrix are made to satisfy $`\lt_{k+1}`$ ($`\lt_{k+1}`$ means $`\lt`$ and $`\le_{k+1}`$). Finite reflection uses continuity and cofinality lemmas for each $`\le_n`$. The definition and examples of $`\mathcal R_N`$ are in the note [proof/pss/03-patterns.md](https://github.com/koteitan/bms-elem-pattern/blob/main/proof/pss/03-patterns.md) of that repository.

## 4. What is missing for ω-Y

The label relation required by the combinatorial layer of ω-Y (the part of Phyrion's proof that deals only with the shape of mountains and expansions, [06](06-combinatorial-layer.md)) has three arguments.

```math
R(\theta, a, b) \quad (\theta \in \mathrm{Key}_m,\ a, b \in \mathrm{Label})
```

$`m`$ is the key length. The key $`\theta`$ is a sequence of $`m`$ entries, each a label or $`\top`$ ([02](02-well-founded.md) §3). The third argument $`b`$ is the top ([02](02-well-founded.md) §3). In this repository $`R(\theta, a, b)`$ is read as "in the language whose top predicates are defined only where the key is below $`\theta`$ (§5), the structure of height $`a`$ is a $`\Sigma_1`$-elementary substructure of the structure of height $`b`$" ([07](07-relation-r.md)). This causes three problems.

**Problem 1: keys are transfinite.** Keys range over $`\mathrm{Key}_m`$ in lexicographic order. The coordinates are labels, so the order of keys is transfinite. The $`j = 1, \ldots, N`$ of $`\le_j`$ in $`\mathcal R_N`$ ($`\Sigma_1`$- to $`\Sigma_N`$-elementarity) are finitely many and counted by natural numbers. A key cannot be used as such a number.

**Problem 2: demands toward the top.** Finite reflection must also make the relation $`R(\kappa, x, b)`$ ($`\kappa`$ a key) from a point $`x`$ to the top $`b`$ true for the new labels. A condition of this form is called a demand (the top atoms of [06](06-combinatorial-layer.md) §2). $`b`$ is not an element of the structure $`(b; \ldots)`$. Unfolding the definition of $`R`$ does not give a $`\Sigma_1`$ formula.

**Problem 3: the keys of demands name points that move.** Let $`f`$ be the labels of the columns ($`f(i)`$ the label of column $`i`$). A demand has the form $`R(\mathrm{eval}\ t\ f, f(p), b)`$, where $`p`$ is a column number and $`t`$ a template ([03](03-sigma1-elementary.md) §7). The template decides which column's label is put at each coordinate of the key. We say that "the template names the column". Phyrion's finite reflection does not require these columns to lie before the cut (§3; see the comment on `finite_reflection` in [OmegaY/Reflection.lean](../../OmegaY/Reflection.lean): "No root used in a key is required to be retained"). So a label inside a key may belong to a witness ([03](03-sigma1-elementary.md) §2) that the reflection relabels. The 1-Y version ([01](01-ordinals.md) §7) decided whether a top predicate is defined by "the position of a parameter". That method does not work here.

## 5. The changes made in this repository

As in [notes/01-design.md](../../notes/01-design.md) §2, the following changes are made.

1. **Every key gives $`\Sigma_1`$-elementarity.** The difference in strength between keys is not the quantifier complexity but which top predicates are defined.
2. **Top predicates are atomic symbols.** A structure of height $`c`$ has a symbol $`\mathrm{Top}_{t,i}`$ ([03](03-sigma1-elementary.md) §7) for each template $`t`$ and position $`i`$, interpreted as "$`R(\mathrm{eval}\ t\ \vec v, v_i, c)`$". Demands toward the top become atomic formulas (Problem 2).
3. **Top predicates are defined only where the key is below $`\theta`$.** Where they are not defined, top literals are false ([03](03-sigma1-elementary.md) §8). Whether they are defined depends on the value of the key (Problem 3). Lowering witnesses pointwise keeps the key below $`\theta`$, because $`\mathrm{eval}`$ is monotone (`Lit.holds_of_le`).
4. **Internal relations exist for every key.** For each template $`t`$ and positions $`i, j`$ there is a symbol $`\mathrm{Rel}_{t,i,j}`$ ([03](03-sigma1-elementary.md) §7), interpreted as $`\mathrm{Rel}_{t,i,j}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v, v_i, v_j)`$.
5. **The stages are (top, key).** The top $`b`$ is the outermost component ([02](02-well-founded.md) §3). The right side at stage of key $`\theta`$ reads only top predicates of keys below $`\theta`$. This is exactly the "defined range" of item 3 (Problem 1).

The resulting relation $`R`$ is not Carlson's $`\mathcal R_N`$ itself. We do not claim that it is the same as $`\mathcal R_N`$. The definition is given in [07 The relation R](07-relation-r.md).

| | $`\mathcal R_N`$ (bms-elem-pattern) | 1-Y version (1y-wo-por) | Phyrion's original semantic layer for ω-Y | this repository |
|---|---|---|---|---|
| argument that distinguishes the relations | $`j = 1, \ldots, N`$ | $`(k, \eta) \in \mathbb N \times \mathrm{Ord}`$ | keys $`\theta \in \mathrm{Key}_m`$ | keys $`\theta \in \mathrm{Key}_m`$ |
| content of $`R(\cdot, a, b)`$ | $`\Sigma_j`$-elementarity | $`\Sigma_1`$-elementarity | finite positive graphs below $`b`$ can be compressed below $`a`$ | $`\Sigma_1`$-elementarity |
| relation to the top | continuity and cofinality lemmas | atomic symbols (whether defined is decided by the positions of variables) | demands inside the graphs | partial atomic symbols (defined by the value of the key) |
| recursion | top $`\beta`$ | (top, $`k`$, $`\eta`$) | (top, key) | (top, key) |

The terms of the table are as follows ([notes/00-survey.md](../../notes/00-survey.md) §3.1, §3.2).

- $`(k, \eta)`$ of the 1-Y version: $`k`$ is the number of a row of the 1-Y mountain, and $`\eta`$ is the label of the root column.
- Phyrion's graph: a finite set of points with finitely many conditions of the relation $`R`$ between points and finitely many demands from points to the top (the same shape as a graph of [06](06-combinatorial-layer.md) §2). Positive means that the conditions contain no negation.
- "Finite positive graphs below $`b`$ can be compressed below $`a`$": suppose a strictly increasing labelling below $`b`$ makes the relations between the points of the graph true, and makes the demands (with keys below $`\theta`$) true for the top $`b`$. Then there is a strictly increasing labelling below $`a`$ that makes the same relations true and the demands true for the top $`a`$. The original labels below $`a`$ are not moved.

Phyrion's original semantic layer is summarized in [notes/00-survey.md](../../notes/00-survey.md) §3.2. It is not included in this repository ([NOTICE](../../NOTICE)).

## 6. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "Structure of the proof", "The relation R" | the semantic layer replaced by the relation of $`\Sigma_1`$-elementary substructures |
| [notes/01-design.md](../../notes/01-design.md) §0, §2 | summary of the design and the definitions |
| [notes/00-survey.md](../../notes/00-survey.md) §3.2–§3.4 | Phyrion's original relation, and the problems in extending the 1-Y method |
| [Por/Formula.lean](../../Por/Formula.lean), [Por/Relation.lean](../../Por/Relation.lean) | items 1–5 of §5 |

## 7. Lean correspondence

$`\le_1`$ itself does not appear in the Lean code of this repository. The corresponding objects are:

| Concept | Lean | File |
|---|---|---|
| the relation $`R`$ | `Por.R` | [Por/Relation.lean](../../Por/Relation.lean) |
| stages | `StageLT`, `stage_wf` | same |
| interpretation of the top predicates | `topR c` | same |
| interpretation of the internal relations | `relR` | same |
| the defined range | `allow` $`= (\cdot \lt \theta)`$ in `ElemL` | [Por/Formula.lean](../../Por/Formula.lean) |
| lowering keeps the key condition | `Lit.holds_of_le` | same |
