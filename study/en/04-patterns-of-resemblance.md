[← Back](README.md) | [English](04-patterns-of-resemblance.md) | [Japanese](../04-patterns-of-resemblance.md)

# Patterns of resemblance

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | ordinal, limit ordinal, $`\mathrm{Ord}`$, label |
| [02 Well-founded relations and well-founded recursion](02-well-founded.md) | well-founded recursion, argument, guarded recursion, keys $`\mathrm{Key}_m`$, stage, top |
| [03 Structures and Σ₁-elementary substructures](03-sigma1-elementary.md) | structures $`(\gamma; \ldots)`$, point, $`\Sigma_1`$ formulas, $`\preccurlyeq_{\Sigma_1}`$, template, $`\mathrm{eval}`$, top predicate (§7), partial top predicates (§8) |

This note explains the idea of Carlson's patterns of resemblance. It then says how [bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) used it for BMS. Finally it says why this is not enough for ω-Y as it stands, and what this repository changes.

## 1. A relation whose language contains itself

**Definition (Carlson's ≤₁).** Define a relation $`\le_1`$ on ordinals by

```math
\alpha \le_1 \beta \iff \alpha \le \beta \ \land\ (\alpha; \le, \le_1) \preccurlyeq_{\Sigma_1} (\beta; \le, \le_1)
```

$`\alpha \lt_1 \beta`$ means $`\alpha \lt \beta \land \alpha \le_1 \beta`$.

**Reading.** "The shape of the ordinals below $`\alpha`$ cannot be told apart by $`\Sigma_1`$ formulas from the shape below $`\beta`$." Here the shape consists of the order and of the relation $`\le_1`$ itself.

The right side uses the relation $`\le_1`$ being defined. This looks circular, but it is a well-founded recursion on $`\beta`$.

- The domain of $`(\beta; \le, \le_1)`$ is $`\{x \mid x \lt \beta\}`$. The only $`\le_1`$ facts read there are $`x \le_1 y`$ with $`x, y \lt \beta`$.
- The truth value of $`x \le_1 y`$ has been decided at the earlier point with argument $`y \lt \beta`$.
- The same holds for $`(\alpha; \ldots)`$, since $`\alpha \le \beta`$.

Carlson studied the extension to $`\le_1, \ldots, \le_N`$ ($`\Sigma_1, \ldots, \Sigma_N`$-elementarity).

```math
\mathcal R_N = (\mathrm{Ord}; \le, \le_1, \ldots, \le_N)
```

- $`N \ge 1`$ is a natural number.
- $`\alpha \le_i \beta`$ is obtained from the definition of $`\le_1`$ by replacing $`\preccurlyeq_{\Sigma_1}`$ with elementarity for $`\Sigma_i`$ formulas. A $`\Sigma_i`$ formula starts with a block of existential quantifiers, has $`i`$ alternating blocks of existential and universal quantifiers, and then a quantifier-free formula.

Reference: T. J. Carlson, Elementary patterns of resemblance, Annals of Pure and Applied Logic 108 (2001), 19–77.

## 2. Small examples

**Example 1.** For a natural number $`n \lt \beta`$, $`n \le_1 \beta`$ fails.

- If $`n \ge 1`$: $`\exists x\ (n - 1 \lt x)`$ with parameter $`n - 1`$ is true in $`\beta`$ ($`x = n`$) and false in $`n`$.
- If $`n = 0`$: $`\exists x\ (x \le x)`$ is true in $`\beta`$ and false in the empty structure $`0`$.

For the same reason, a successor ordinal $`\gamma + 1`$ is not $`\le_1`$ any larger ordinal.

**Example 2.** $`\omega \lt_1 \omega + 1`$.

By Example 1, no two distinct points below $`\omega + 1`$ are related by $`\le_1`$: pairs of natural numbers are handled by Example 1, and the only other point is $`\omega`$ itself. So in $`(\omega; \le, \le_1)`$ and $`(\omega + 1; \le, \le_1)`$, $`x \le_1 y`$ means the same as $`x = y`$. What remains is to compare the order-only structures $`(\omega; \le)`$ and $`(\omega + 1; \le)`$, and since $`\omega`$ is a limit, the example of [03](03-sigma1-elementary.md) §5 applies.

**Example 3.** If $`\beta \ge \omega + 2`$, then $`\omega \le_1 \beta`$ fails. $`\exists x\ \exists y\ (x \lt y \land x \le_1 y)`$ is true in $`\beta`$ ($`x = \omega`$, $`y = \omega + 1`$ by Example 2, both below $`\beta`$) and false in $`\omega`$ (Example 1).

$`\omega \le_1 \omega`$ holds by the definition. Hence $`\{\beta \mid \omega \le_1 \beta\} = \{\omega, \omega + 1\}`$.

In the order-only language, $`(\omega; \le) \preccurlyeq_{\Sigma_1} (\beta; \le)`$ held for every $`\beta \gt \omega`$. Putting $`\le_1`$ itself into the language makes the relation finer.

## 3. Use in termination proofs

This section uses words that later notes define, and only describes the shape. Columns of an expression, edges of the mountain and expansion are defined in [05](05-omegay-mountain.md); the way labels are attached and the cut are defined in [06](06-combinatorial-layer.md) §2, §3.

A termination proof for expansion attaches a label ([01](01-ordinals.md) §6) to each column and shows that expansion lowers the labels ([02](02-well-founded.md) §6, [06](06-combinatorial-layer.md) §8). The property needed is **finite reflection**.

**The shape of finite reflection.** Let $`\alpha \lt_1 \beta`$. Suppose points $`\vec p`$ below $`\alpha`$ and points $`\vec y`$ below $`\beta`$ satisfy a condition $`\psi(\vec p, \vec y)`$ made of finitely many atomic formulas. Then there are points $`\vec y'`$ below $`\alpha`$ with the same condition $`\psi(\vec p, \vec y')`$.

**Reason.** $`\exists \vec y\ \psi(\vec p, \vec y)`$ is a $`\Sigma_1`$ formula true in $`(\beta; \ldots)`$. By $`\Sigma_1`$-elementarity it is true in $`(\alpha; \ldots)`$.

In an expansion, $`\vec y`$ is the list of old labels of the columns to be relabelled. If $`\psi`$ says "the labels of the columns at the two ends of each edge of the mountain satisfy $`\le_1`$ (and so on)", then the new labels $`\vec y'`$ satisfy the same edge conditions. Moreover $`\vec y'`$ lies below $`\alpha`$. In an expansion, $`\alpha`$ is the old label of the cut column, and every old label $`\vec y`$ that is replaced is $`\ge \alpha`$. So the new labels are smaller than the old ones.

**Use in bms-elem-pattern.** [bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) proved termination of BMS with $`\mathcal R_N`$. The label relation of a parent–child edge in row $`k`$ is $`\lt_{k+1}`$. Finite reflection uses $`\Sigma_n`$-elementarity and lemmas about continuity and cofinality. The definition of $`\mathcal R_N`$ and examples are in the note [proof/pss/03-patterns.md](https://github.com/koteitan/bms-elem-pattern/blob/main/proof/pss/03-patterns.md) of that repository.

## 4. What is missing for ω-Y

The label relation required by the ω-Y combinatorial layer ([06](06-combinatorial-layer.md)) has three arguments.

```math
R(\theta, a, b) \quad (\theta \in \mathrm{Key}_m,\ a, b \in \mathrm{Label})
```

Read it as "with key $`\theta`$, $`a`$ is stable into $`b`$". $`\theta`$ is a key computed from a template for each edge of the mountain ([06](06-combinatorial-layer.md) §1). This causes three problems.

**Problem 1: keys are transfinite.** The key $`\theta`$ runs lexicographically over $`\mathrm{Key}_m`$ ([02](02-well-founded.md) §3). The coordinates are labels, so the order of keys is transfinite. The relations $`\le_1, \ldots, \le_N`$ of $`\mathcal R_N`$ are finitely many and counted by natural numbers. A transfinite key cannot serve as such a number.

**Problem 2: demands toward the top.** The top $`b`$ is the label that the old last column had before the expansion ([06](06-combinatorial-layer.md) §8). Finite reflection must also make "relations $`R(\kappa, x, b)`$ to the top $`b`$" ($`\kappa`$ a key, $`x`$ the label of the parent) hold for the new labels (the top atoms of [06](06-combinatorial-layer.md) §3). $`b`$ is not an element of the structure $`(b; \ldots)`$. Writing out the definition of $`R`$ does not give a $`\Sigma_1`$ formula.

**Problem 3: the key of a demand names columns that move.** Let $`f(i)`$ be the label of column $`i`$. A demand toward the top has the form $`R(\mathrm{eval}\ t\ f,\ f(p),\ b)`$, where $`p`$ is a column number and $`t`$ a template of ω-Y ([03](03-sigma1-elementary.md) §7). If $`t_i = \mathrm{some}\ j`$, coordinate $`i`$ of the key is $`f(j)`$. We then say that "the template $`t`$ names column $`j`$". Phyrion's finite reflection ([06](06-combinatorial-layer.md) §4) does not require the named column $`j`$ to lie before the cut ($`j \lt \mathrm{cut}`$). So a label $`f(j)`$ inside a key may belong to a witness that the reflection relabels. The 1-Y version ([01](01-ordinals.md) §7) decided whether a top predicate may be read from the positions of the variables (its note 03 §8). That method does not work here.

## 5. What this repository changes

As in [notes/01-design.md](../../notes/01-design.md) §2 (Japanese), the following changes are made.

1. **Every key is $`\Sigma_1`$.** The strength of a key is decided by which top predicates are defined, not by the quantifier complexity.
2. **Top predicates ([03](03-sigma1-elementary.md) §7) are atomic symbols.** A structure of height $`c`$ has the symbol $`\mathrm{Top}_{t,i}(\vec v)`$, interpreted as "$`R(\mathrm{eval}\ t\ \vec v,\ v_i,\ c)`$". A demand toward the top becomes an atomic formula (Problem 2).
3. **The key $`\theta`$ decides which top predicates are defined.** A top predicate $`\mathrm{Top}_{t,i}(\vec v)`$ is defined only when $`\mathrm{eval}\ t\ \vec v \lt \theta`$ ([03](03-sigma1-elementary.md) §8). A larger $`\theta`$ defines more symbols, so the relation is stronger. Whether a predicate is defined depends on the value of its key, so keys that name witnesses can be handled (Problem 3). Lowering the witnesses pointwise keeps the key below $`\theta`$ (Lemma 3 of [03](03-sigma1-elementary.md) §8).
4. **The relations $`\mathrm{Rel}_{t,i,j}`$ between points ([03](03-sigma1-elementary.md) §7) are present for every key.** $`\mathrm{Rel}_{t,i,j}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ v_j)`$ for every $`t, i, j`$.
5. **The argument of the recursion ([02](02-well-founded.md) §4) is the stage $`(b, \theta)`$.** The top $`b`$ is the outermost component ([02](02-well-founded.md) §3). The right side at a stage with key $`\theta`$ reads only top predicates with keys below $`\theta`$. This is exactly the "range where they are defined" of item 3 (Problem 1).

The resulting relation $`R`$ is not Carlson's $`\mathcal R_N`$ itself, and we do not claim that it coincides with $`\mathcal R_N`$. The definition is given in [07 The relation R](07-relation-r.md).

| | $`\mathcal R_N`$ (bms-elem-pattern) | 1-Y version | Phyrion's original semantic layer | $`R`$ of this repository |
|---|---|---|---|---|
| argument that tells the relations apart | $`j = 1, \ldots, N`$ | $`(k, \eta) \in \mathbb N \times \mathrm{Ord}`$ | key $`\theta \in \mathrm{Key}_m`$ | key $`\theta \in \mathrm{Key}_m`$ |
| strength given by the argument | $`\Sigma_j`$ quantifiers | range of visible top predicates | range of keys of demands | range of defined top predicates |
| content of $`R(\cdot, a, b)`$ | $`\Sigma_j`$-elementarity | $`\Sigma_1`$-elementarity | compression of finite positive diagrams (defined below) | $`\Sigma_1`$-elementarity |
| relation to the top | lemmas on continuity and cofinality | atomic symbols (readability decided by positions of variables) | demands inside the diagram | partial atomic symbols (decided by the value of the key) |
| argument of the recursion | the top $`\beta`$ | lexicographic order on $`(b, k, \eta)`$ | stage $`(b, \theta)`$ | stage $`(b, \theta)`$ |

**Phyrion's original semantic layer.** There $`R(\theta, a, b) \iff a \lt b \land \mathrm{Reflects}(\theta, a, b)`$, and $`\mathrm{Reflects}(\theta, a, b)`$ is the following compression property ([notes/00-survey.md](../../notes/00-survey.md) §3.2, Japanese). The words are those of [06](06-combinatorial-layer.md) §1–§3: $`n`$ is the number of columns, $`G`$ a list of atoms, $`N`$ a list of top atoms, and $`f, g : \mathrm{Fin}\ n \to \mathrm{Label}`$ are labellings. "Positive" means that the conditions contain no negation.

```math
\begin{aligned}
&\forall n\ \forall G\ \forall N\ \forall f\ \Bigl(f \text{ strictly increasing} \land \bigl(\forall i\ f(i) \lt b\bigr) \land G \text{ holds at } f \land \bigl(\text{every key of } N \text{ is below } \theta\bigr) \land N \text{ holds with top } b \cr
&\qquad \implies \exists g\ \Bigl(g \text{ strictly increasing} \land \bigl(\forall i\ g(i) \lt a\bigr) \land \bigl(\forall i\ (f(i) \lt a \implies g(i) = f(i))\bigr) \land G \text{ holds at } g \land N \text{ holds with top } a\Bigr)\Bigr)
\end{aligned}
```

Phyrion's original semantic layer is not included in this repository ([NOTICE](../../NOTICE)).

## 6. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "Structure of the proof" | the semantic layer is replaced by a relation of $`\Sigma_1`$-elementary substructures; Phyrion's original relation (compression) |
| [README](../../README-en.md) "The relation R" | top predicates are atomic symbols, defined only for keys below $`\theta`$ (§5) |
| [notes/01-design.md](../../notes/01-design.md) §0, §2 (Japanese) | summary of the design and definitions |
| [notes/00-survey.md](../../notes/00-survey.md) §3.2–§3.4 (Japanese) | Phyrion's original relation and the problems in extending the 1-Y method |

## 7. Lean correspondence

$`\le_1`$ itself does not appear in the Lean code of this repository. The corresponding objects are the following.

| Concept | Lean | File |
|---|---|---|
| the relation $`R`$ | `Por.R` (`Reflection.R` from the combinatorial layer) | [Por/Relation.lean](../../Por/Relation.lean), [OmegaY/Reflection.lean](../../OmegaY/Reflection.lean) |
| stages | `StageLT`, `stage_wf` | [Por/Relation.lean](../../Por/Relation.lean) |
| interpretations of the top predicates and internal relations | `topR c`, `relR` | same |
| range where top predicates are defined, $`\kappa \lt \theta`$ | the `(· < θ)` inside `ElemL` | [Por/Formula.lean](../../Por/Formula.lean) |
| lowering pointwise keeps the key condition | `Lit.holds_of_le` | same |
| named columns need not lie before the cut | the comment on `finite_reflection`: "No root used in a key is required to be retained" | [OmegaY/Reflection.lean](../../OmegaY/Reflection.lean) |
| atoms, top atoms, conditions on demands | `InternalAtom`, `TopAtom`, `KeysBelow`, `FixesBelow` | [OmegaY/Reflection/Interface.lean](../../OmegaY/Reflection/Interface.lean) |
