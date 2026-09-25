[← Back](README.md) | [English](03-sigma1-elementary.md) | [Japanese](../03-sigma1-elementary.md)

# Structures and Σ₁-elementary substructures

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | ordinal, limit ordinal, $`\{x \mid x \lt \gamma\}`$, the label type, $`\mathrm{Fin}\ n`$, position |
| [02 Well-founded relations and recursion](02-well-founded.md) | keys $`\mathrm{Key}_m`$ and their order, top, guard |

This note explains the model-theoretic terms used in the definition of the relation $`R`$: first-order structures, $`\Sigma_1`$ formulas, $`\Sigma_1`$-elementary substructures and the Tarski–Vaught test. The second half (§7, §8) explains how Lean represents them.

## 1. Languages and structures

**Definition (language).** A **language** is a collection of relation symbols, each with a fixed number of arguments. This repository uses no function symbols and no constant symbols.

**Definition (structure).** A **structure** $`\mathfrak A`$ for a language $`L`$ consists of a set $`A`$ (the domain, possibly empty) and an interpretation $`P^{\mathfrak A} \subseteq A^n`$ of each symbol $`P`$ with $`n`$ arguments.

**Notation.** A structure is written $`(A; P_1, P_2, \ldots)`$.

- Left of the semicolon, $`A`$ is the domain. When an ordinal $`\gamma`$ is written on the left, the domain is $`\{x \mid x \lt \gamma\}`$.
- Right of the semicolon are the interpretations of the symbols. A symbol and its interpretation are written with the same letter.
- The relations on the right are read restricted to the domain.

Example: the domain of $`(4; \lt)`$ is $`\{0, 1, 2, 3\}`$, and its relation is $`\lt`$ on $`\{0, 1, 2, 3\}`$.

| Language | Structure | Domain |
|---|---|---|
| $`\{\lt\}`$ | $`(\omega; \lt)`$ | natural numbers |
| $`\{\lt\}`$ | $`(\gamma; \lt)`$ | $`\{x \mid x \lt \gamma\}`$ |
| $`\{\lt, E\}`$ ($`E`$ a symbol with 2 arguments) | $`(\omega; \lt, E)`$, $`E(x, y) :\iff y = x + 1`$ | natural numbers |

Every structure in this repository has a domain of the form $`\{x \mid x \lt \gamma\}`$. We call $`\gamma`$ the **height** of the structure.

## 2. Formulas and Σ₁ formulas

**Definition (formula).** Formulas are built as follows.

- **Atomic formulas**: $`P(x_1, \ldots, x_n)`$ ($`P`$ a symbol with $`n`$ arguments, $`x_i`$ variables).
- Formulas joined by $`\neg, \land, \lor, \to`$.
- A formula with $`\exists x`$ or $`\forall x`$ in front.

**Definition (quantifier-free formula).** A formula without the quantifiers $`\exists`$, $`\forall`$.

**Definition (Σ₁ formula).** A formula of the form

```math
\exists y_1 \cdots \exists y_k\ \psi(\vec p, y_1, \ldots, y_k)
```

with $`\psi`$ quantifier-free, that is, only existential quantifiers in front, is a **$`\Sigma_1`$ formula**. $`k`$ is a natural number. $`\vec p`$ is a tuple of free variables, into which elements of the domain (**parameters**) are put later.

| Formula | Kind |
|---|---|
| $`p \lt q`$ | quantifier-free (also $`\Sigma_1`$, with $`k = 0`$) |
| $`\exists y\ (p \lt y)`$ | $`\Sigma_1`$ |
| $`\exists y\ \exists z\ (p \lt y \land y \lt z \land E(y, z))`$ | $`\Sigma_1`$ |
| $`\forall y\ (y \lt p \lor p \lt y \lor y = p)`$ | not $`\Sigma_1`$ |

**Definition (satisfaction).** For a structure $`\mathfrak A`$ and a tuple of parameters $`\vec p`$ (each entry an element of $`A`$; we write $`\vec p \in A`$), $`\mathfrak A \models \varphi(\vec p)`$ means "$`\varphi`$ is true in $`\mathfrak A`$ at $`\vec p`$". A quantifier $`\exists y`$ ranges over the domain $`A`$. When $`\mathfrak A \models \exists \vec y\ \psi(\vec p, \vec y)`$, a tuple $`\vec y`$ of elements of $`A`$ that makes $`\psi(\vec p, \vec y)`$ true is called a **witness**.

Example: $`(\omega; \lt) \models \exists y\ (3 \lt y)`$ is true. $`(4; \lt) \models \exists y\ (3 \lt y)`$ is false, because the domain of $`(4; \lt)`$ is $`\{0, 1, 2, 3\}`$.

## 3. Conjunctions of literals

**Definition (literal).** An atomic formula or the negation of an atomic formula is a **literal**.

**Fact (disjunctive normal form).** A quantifier-free formula is equivalent to a finite disjunction of conjunctions of literals. An existential quantifier distributes over a disjunction.

```math
\exists \vec y\ (\psi_1 \lor \psi_2) \iff \exists \vec y\ \psi_1 \ \lor\ \exists \vec y\ \psi_2
```

So every $`\Sigma_1`$ formula is equivalent to a finite disjunction of formulas of the form "existential quantifiers in front of a conjunction of literals". If two structures agree on all formulas of this form, they agree on all $`\Sigma_1`$ formulas.

**Example.** $`\exists y\ \bigl((p \lt y \land \neg(y \lt q)) \lor E(p, y)\bigr)`$ is equivalent to $`\exists y\ (p \lt y \land \neg(y \lt q)) \lor \exists y\ E(p, y)`$.

**Equality.** If $`\lt`$ is a linear order, equality is not needed: $`x = y \iff \neg(x \lt y) \land \neg(y \lt x)`$.

The formulas of this repository have only the form "existential quantifiers in front of a conjunction of literals" (§7).

## 4. Substructures and upward preservation

**Definition (substructure).** $`\mathfrak A`$ is a **substructure** of $`\mathfrak B`$ if $`A \subseteq B`$ and each symbol is interpreted by the restriction, that is, $`P^{\mathfrak A}(\vec a) \iff P^{\mathfrak B}(\vec a)`$ for $`\vec a \in A`$.

**Property 1.** In a substructure, quantifier-free formulas about elements of $`A`$ have the same truth value, because the atomic formulas have the same truth values.

**Property 2 (Σ₁ is preserved upward).** In a substructure, if $`\mathfrak A \models \exists \vec y\ \psi(\vec p, \vec y)`$ then $`\mathfrak B \models \exists \vec y\ \psi(\vec p, \vec y)`$. The witnesses $`\vec y`$ from $`\mathfrak A`$ are also in $`B`$, and by Property 1 the truth of $`\psi`$ is the same.

**The converse fails.** $`(4; \lt)`$ is a substructure of $`(\omega; \lt)`$. $`\exists y\ (3 \lt y)`$ is true in $`\omega`$ and false in $`4`$.

## 5. Σ₁-elementary substructures

**Definition (Σ₁-elementary substructure).** $`\mathfrak A`$ is a **$`\Sigma_1`$-elementary substructure** of $`\mathfrak B`$ if $`\mathfrak A`$ is a substructure of $`\mathfrak B`$ and for every $`\Sigma_1`$ formula $`\varphi`$ and all parameters $`\vec p \in A`$:

```math
\mathfrak A \models \varphi(\vec p) \iff \mathfrak B \models \varphi(\vec p)
```

This is written $`\mathfrak A \preccurlyeq_{\Sigma_1} \mathfrak B`$.

**Meaning.** A claim "there are finitely many elements like this" that uses only elements of $`A`$ is true in $`\mathfrak A`$ if it is true in $`\mathfrak B`$. The witnesses can be chosen again inside $`A`$.

**Example (the language of order only).** Let $`0 \lt \alpha \lt \beta`$ be ordinals.

```math
(\alpha; \lt) \preccurlyeq_{\Sigma_1} (\beta; \lt) \iff \alpha \text{ is a limit ordinal}
```

**Proof.**

- If $`\alpha = \gamma + 1`$: with parameter $`\gamma`$, $`\exists y\ (\gamma \lt y)`$ is true in $`\beta`$ ($`y = \gamma + 1`$) and false in $`\alpha`$. So it fails.
- If $`\alpha`$ is a limit: suppose a $`\Sigma_1`$ formula $`\exists \vec y\ \psi(\vec p, \vec y)`$ is true in $`\beta`$. Move its witnesses $`\vec y`$ into $`\alpha`$, keeping their positions relative to the parameters.
  - Witnesses below the largest parameter are already in $`\alpha`$. Keep them.
  - There are finitely many witnesses above the largest parameter (if there are no parameters, count all witnesses here). Since $`\alpha`$ is a limit, there are infinitely many elements of $`\alpha`$ above the largest parameter ([01](01-ordinals.md) §2). Place the witnesses there in the same order.
  - Moving them does not change the truth values of $`\lt`$. So $`\psi`$ is true in $`\alpha`$.
  - The other direction is Property 2 of §4. $`\square`$

$`\alpha = 0`$ is also excluded: $`\exists y\ \neg(y \lt y)`$ is false in the empty structure $`0`$ and true in $`\beta`$.

## 6. The Tarski–Vaught test (Σ₁ version)

To show $`\Sigma_1`$-elementarity it is enough to check the downward direction.

**Theorem (Tarski–Vaught test, Σ₁ version).** Let $`\mathfrak A`$ be a substructure of $`\mathfrak B`$. The following are equivalent.

1. $`\mathfrak A \preccurlyeq_{\Sigma_1} \mathfrak B`$.
2. For quantifier-free $`\psi`$ and $`\vec p \in A`$: if $`\mathfrak B \models \exists \vec y\ \psi(\vec p, \vec y)`$, then $`\mathfrak B \models \psi(\vec p, \vec y)`$ for some $`\vec y \in A`$.

**Proof.** 1 to 2: the formula is true in $`\mathfrak A`$, so it has witnesses in $`A`$, and by Property 1 of §4 $`\psi`$ is also true in $`\mathfrak B`$. 2 to 1: the upward direction is Property 2 of §4. The downward direction: the witnesses of 2 are in $`A`$, and by Property 1 $`\mathfrak A \models \psi(\vec p, \vec y)`$. $`\square`$

The general Tarski–Vaught test says the same for all formulas. This repository uses only $`\Sigma_1`$.

**How it is used.** Condition 2 says "$`A`$ is closed under witnesses". `lam_good` in [08 Closure and Good points](08-closure-chain.md) is proved in this form: start from $`\gamma`$, add witnesses of true claims, and take the supremum.

## 7. Σ₁ formulas in Lean

The formulas in Lean are in [Por/Formula.lean](../../Por/Formula.lean). Fix the following three things.

- $`\mathrm{Label}`$: the type of labels, a linear order. The label type of [01](01-ordinals.md) §6 is an example.
- $`\mathrm{Key}`$: the type of keys, a linear order. $`\mathrm{Key}_m`$ of [02](02-well-founded.md) §3 is an example.
- `S : KeySyntax Label Key`: a **key syntax**. It consists of three parts.
  - `S.Template n`: the type of **templates** over $`n`$ variables.
  - `S.eval t v`: the key obtained by evaluating the template $`t`$ at the values $`v : \mathrm{Fin}\ n \to \mathrm{Label}`$ of the variables.
  - `S.monotone_eval`: `S.eval` is pointwise monotone. That is, if $`w_i \le v_i`$ for all $`i`$, then $`\mathrm{eval}\ t\ w \le \mathrm{eval}\ t\ v`$.

The templates of ω-Y are explained in [06](06-combinatorial-layer.md) §1. There a template is a sequence that puts, at each coordinate of the key, $`\mathrm{some}\ i`$ (put the value of the variable $`v_i`$) or $`\mathrm{none}`$ (put $`\top`$).

**Language.** The variables are $`v_0, \ldots, v_{n-1}`$, and we write $`\vec v = (v_0, \ldots, v_{n-1})`$. The number $`i`$ is the position of the variable ([01](01-ordinals.md) §7). There are three kinds of symbols.

- The order $`\lt`$.
- For each template $`t`$ and positions $`i, j`$, an **internal relation** $`\mathrm{Rel}_{t,i,j}(\vec v)`$. It is a relation between the two points $`v_i, v_j`$.
- For each template $`t`$ and position $`i`$, a **top predicate** $`\mathrm{Top}_{t,i}(\vec v)`$. It is a relation from the point $`v_i`$ to the height $`c`$ of the structure (the top, [02](02-well-founded.md) §3). $`c`$ itself is not in the domain.

The key of $`\mathrm{Rel}_{t,i,j}`$ and $`\mathrm{Top}_{t,i}`$ is $`\mathrm{eval}\ t\ v`$, so the key depends on the values of the variables. The meaning of the two symbols is given in [07](07-relation-r.md) §2. In this note their interpretations are taken as arguments (`Lit.Holds`).

**Definition (`Lit n`).** A literal over $`n`$ variables is one of three kinds. $`i, j`$ are positions and $`t`$ is a template. `pos = true` is the positive literal, `pos = false` the negated one.

| Lean | Reading | Key |
|---|---|---|
| `Lit.lt i j pos` | $`v_i \lt v_j`$ | none |
| `Lit.rel t i j pos` | $`\mathrm{Rel}_{t,i,j}(\vec v)`$ with key $`\mathrm{eval}\ t\ v`$ | $`\mathrm{eval}\ t\ v`$ |
| `Lit.top t i pos` | $`\mathrm{Top}_{t,i}(\vec v)`$ with key $`\mathrm{eval}\ t\ v`$ | $`\mathrm{eval}\ t\ v`$ |

**Definition (`Form`).** A formula is a triple $`(n, \mathit{fixed}, \mathit{lits})`$.

| Component | Meaning |
|---|---|
| $`n`$ | the number of variables |
| $`\mathit{fixed} : \mathrm{Fin}\ n \to \mathrm{Bool}`$ | positions marked true are parameters, the others are existentially quantified |
| $`\mathit{lits}`$ | a list of literals; the formula is their conjunction |

**Definition (`Lit.Holds`).** It defines when a literal holds at the values $`v : \mathrm{Fin}\ n \to \mathrm{Label}`$ of the variables. It takes three interpretations. $`\kappa`$ is a key and $`x, y`$ are labels. `rel κ x y` says "the internal relation of key $`\kappa`$ holds between $`x, y`$", `top κ x` says "the top predicate of key $`\kappa`$ holds at $`x`$", and `allow κ` says "the top predicate of key $`\kappa`$ is defined".

```math
\begin{aligned}
\mathrm{lt}\ i\ j\ \mathit{pos} &: \quad (v_i \lt v_j) \iff \mathit{pos}, \cr
\mathrm{rel}\ t\ i\ j\ \mathit{pos} &: \quad \mathrm{rel}(\mathrm{eval}\ t\ v, v_i, v_j) \iff \mathit{pos}, \cr
\mathrm{top}\ t\ i\ \mathit{pos} &: \quad \mathrm{allow}(\mathrm{eval}\ t\ v) \ \land\ \bigl(\mathrm{top}(\mathrm{eval}\ t\ v, v_i) \iff \mathit{pos}\bigr).
\end{aligned}
```

**Definition (`Sat`).** Let $`c`$ be a label, $`\varphi = (n, \mathit{fixed}, \mathit{lits})`$ a formula, and $`p : \mathrm{Fin}\ n \to \mathrm{Label}`$. `Sat rel top allow c φ p` means "$`\varphi`$ is true at the parameters $`p`$ in the structure of height $`c`$".

```math
\mathrm{Sat}(c, \varphi, p) \iff \exists v\ \Bigl(\forall i\ (\mathit{fixed}_i \to v_i = p_i)\Bigr) \land \Bigl(\forall i\ \ v_i \lt c\Bigr) \land \Bigl(\forall \ell \in \mathit{lits}\ \ \ell \text{ holds at } v\Bigr)
```

$`p`$ is a tuple of length $`n`$, but only the parameter positions are read. The condition $`v_i \lt c`$ expresses "the domain is $`\{x \mid x \lt c\}`$". It also requires $`v_i = p_i \lt c`$ at the parameter positions.

**Example.** $`\varphi = (2,\ (\mathrm{true}, \mathrm{false}),\ [\mathrm{lt}\ 0\ 1\ \mathrm{true}])`$ is $`\exists v_1\ (p_0 \lt v_1)`$. If the labels are ordinals, $`\mathrm{Sat}(c, \varphi, p)`$ is the same as $`p_0 + 1 \lt c`$.

## 8. Comparing two structures, and partial top predicates

The comparison in this repository differs from the textbook definition in two ways.

**Difference 1: the same symbol is interpreted differently.** The definition of $`R`$ compares a structure of height $`a`$ with a structure of height $`b`$ ([07](07-relation-r.md)). The top predicate means "the relation to $`a`$" at height $`a`$ and "the relation to $`b`$" at height $`b`$. So as it stands the smaller one is not a substructure.

Therefore `ElemL` does not assume a substructure. It only requires that every formula with parameters below $`a`$ has the same truth value in both. $`\theta`$ is a key and $`a, b`$ are labels. $`\varphi`$ ranges over formulas and $`p : \mathrm{Fin}\ n \to \mathrm{Label}`$ ($`n`$ the number of variables of $`\varphi`$) over tuples of parameters. In the formula, of the arguments of `Sat` only the interpretation of the top predicate and the height are written.

```math
\mathrm{ElemL}(\theta, a, b) \iff \forall \varphi\ \forall p\ \Bigl(\bigl(\forall i\ (\mathit{fixed}_i \to p_i \lt a)\bigr) \implies \bigl(\mathrm{Sat}(\mathrm{top}_A, a, \varphi, p) \iff \mathrm{Sat}(\mathrm{top}_B, b, \varphi, p)\bigr)\Bigr)
```

In Lean this is `ElemL rel topA topB θ a b`. The interpretation `rel` of the internal relation is shared by the two structures. The top predicate is interpreted by `topA` at height $`a`$ and by `topB` at height $`b`$. In both `Sat`, `allow` is $`\kappa \mapsto \kappa \lt \theta`$. Taking formulas in which every variable is a parameter (quantifier-free formulas), the literals about points below $`a`$ have the same truth value. Top literals agree too, at the keys where they are defined. So when the agreement holds, the two structures interpret the symbols in the same way on the points below $`a`$, the structure of height $`a`$ is a substructure of the structure of height $`b`$, and it is $`\Sigma_1`$-elementary.

**Difference 2: top predicates are partial.** A top predicate is defined only where its key is below $`\theta`$. A top literal can be true only where it is defined. This holds for positive and negated literals alike.

**Example.** Let the key length be $`m = 1`$ ([02](02-well-founded.md) §3) and $`\theta = (5)`$ (the key whose coordinate 0 is the label 5). There are two variables $`v_0, v_1`$, and the templates have the ω-Y form of §7. The template $`t = (\mathrm{some}\ 0)`$ gives the key $`(v_0)`$, and the template $`t_\top = (\mathrm{none})`$ gives the key $`(\top)`$.

| Literal | $`v = (3, 10)`$ | $`v = (7, 10)`$ |
|---|---|---|
| `top t 1 true` | same as $`\mathrm{top}((3), 10)`$ | false (key $`(7)`$ is not below $`\theta`$) |
| `top t 1 false` | same as $`\neg\,\mathrm{top}((3), 10)`$ | false |
| `top t_⊤ 1 true` | false (key $`(\top)`$ is not below $`\theta`$) | false |

**Difference from the 1-Y version.** The 1-Y version ([01](01-ordinals.md) §7) decided whether a top predicate is defined from the positions of variables alone. Here, whether a top predicate is defined depends on the value of the key $`\mathrm{eval}\ t\ v`$, that is, on the values of the variables. So two lemmas are needed.

- `Lit.holds_allow_mono`: enlarging `allow` keeps a literal true.
- `Lit.holds_of_le`: let $`\theta, \Theta`$ be keys and $`w \le v`$ pointwise. Suppose a literal holds at $`v`$ with `allow` $`= (\cdot \lt \theta)`$, and the same literal holds at $`w`$ (possibly with other interpretations) with `allow` $`= (\cdot \lt \Theta)`$. Then it holds at $`w`$ with `allow` $`= (\cdot \lt \theta)`$. For a top literal this is because $`\mathrm{eval}\ t\ w \le \mathrm{eval}\ t\ v \lt \theta`$ (`S.monotone_eval`). The other literals do not read `allow`.

The second lemma says "lowering the witnesses pointwise keeps the key condition $`\lt \theta`$". It is used in key weakening in [07](07-relation-r.md) and in `top_abs` in [09](09-obligations.md).

**Only what is read matters.** `Lit.holds_congr` and `sat_congr` say: if two interpretations agree on the internal relation wherever the second point is below the height $`c`$, and on the top predicate at the defined keys, then the truth values agree, because a formula reads nothing else. They are used to remove the guards ([02](02-well-founded.md) §5) in `R_iff` of [07](07-relation-r.md).

## 9. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "The relation R" | $`\preccurlyeq_{\Sigma_1}`$ and the partial top predicates |
| [notes/01-design.md](../../notes/01-design.md) §2.1, §2.2 | structures and formulas |
| [notes/01-design.md](../../notes/01-design.md) §3.3 | Good points in Tarski–Vaught form |
| [Por/Formula.lean](../../Por/Formula.lean) | all of §7 and §8 |
| [Por/Supply.lean](../../Por/Supply.lean) | §6 (`lam_good`) |

## 10. Lean correspondence

| Concept | Lean | File |
|---|---|---|
| key syntax | `KeySyntax` (`Template`, `eval`, `monotone_eval`) | [OmegaY/Reflection/Interface.lean](../../OmegaY/Reflection/Interface.lean) |
| literals | `Lit` (`lt`, `rel`, `top`) | [Por/Formula.lean](../../Por/Formula.lean) |
| formulas | `Form` (`n`, `fixed`, `lits`) | same |
| truth of a literal | `Lit.Holds` | same |
| a $`\Sigma_1`$ formula is true | `Sat` | same |
| elementarity with top predicates defined below $`\theta`$ | `ElemL` | same |
| same reads give the same truth | `Lit.holds_congr`, `sat_congr` | same |
| enlarging `allow` | `Lit.holds_allow_mono` | same |
| lowering pointwise keeps the key condition | `Lit.holds_of_le` | same |
