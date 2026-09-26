[← Back](README.md) | [English](03-sigma1-elementary.md) | [Japanese](../03-sigma1-elementary.md)

# Structures and Σ₁-elementary substructures

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | ordinal, limit ordinal, $`\{x \mid x \lt \gamma\}`$, labels $`\mathrm{Label}`$ (§6), $`\mathrm{Fin}\ n`$, $`\mathrm{Option}`$ (§7) |
| [02 Well-founded relations and well-founded recursion](02-well-founded.md) | keys $`\mathrm{Key}_m`$ and their order, $`\top`$, top (§3) |

This note explains the model-theoretic terms used in the definition of the relation $`R`$: first-order structures, $`\Sigma_1`$ formulas, $`\Sigma_1`$-elementary substructures and the Tarski–Vaught test. §7 and §8 explain the normal form of $`\Sigma_1`$ formulas used in this repository and the way two structures are compared.

## 1. Languages and structures

**Definition (language).** A **language** is a collection of relation symbols, each with a fixed number of arguments (its arity). This repository uses no function symbols and no constant symbols.

**Definition (structure).** A **structure** $`\mathfrak A`$ for a language $`L`$ consists of a set $`A`$ (the domain, possibly empty) and an interpretation $`P^{\mathfrak A} \subseteq A^n`$ of each symbol $`P`$ of arity $`n`$.

**Notation.** We write a structure as $`(A; P_1, \ldots, P_k)`$.

- Left of the semicolon, $`A`$ is the domain.
- Right of the semicolon are the interpretations of the symbols, in the order of the language. A symbol and its interpretation are written with the same letter.
- When an ordinal $`\gamma`$ stands on the left, the domain is $`\{x \mid x \lt \gamma\}`$.
- The relations on the right are restricted to the domain. For example, the $`\le`$ of $`(\gamma; \le)`$ is $`\{(x, y) \mid x, y \lt \gamma,\ x \le y\}`$.

Example: $`(4; \lt)`$ has domain $`\{0, 1, 2, 3\}`$, and its relation is $`\lt`$ on $`\{0, 1, 2, 3\}`$.

| Language | Structure | Domain |
|---|---|---|
| $`\{\lt\}`$ | $`(\omega; \lt)`$ | natural numbers |
| $`\{\lt\}`$ | $`(\gamma; \lt)`$ | $`\{x \mid x \lt \gamma\}`$ |
| $`\{\lt, E\}`$ ($`E`$ of arity 2) | $`(\omega; \lt, E)`$, $`E(x, y) :\iff y = x + 1`$ | natural numbers |

Every structure in this repository has a domain of the form $`\{x \mid x \lt \gamma\}`$. We call $`\gamma`$ the **height** of the structure. The elements of the domain are called **points**.

## 2. Formulas and Σ₁ formulas

**Definition (formula).** Formulas are built as follows.

- **Atomic formulas**: $`P(x_1, \ldots, x_n)`$ ($`P`$ a symbol of arity $`n`$, $`x_i`$ variables).
- Formulas combined with $`\neg, \land, \lor, \to`$.
- Formulas with $`\exists x`$ or $`\forall x`$ in front.

**Definition (quantifier-free formula).** A formula that contains no quantifier $`\exists`$ or $`\forall`$.

**Definition (Σ₁ formula).** A formula of the form

```math
\exists y_1 \cdots \exists y_{\mathit{bb}}\ \psi(\vec p, y_1, \ldots, y_{\mathit{bb}})
```

with $`\psi`$ quantifier-free, that is, only existential quantifiers in front, is a **$`\Sigma_1`$ formula**. $`\mathit{bb} \in \mathbb N`$ is the number of existentially quantified variables. $`\vec p`$ are free variables; later elements of the domain (**parameters**) are put in their place. A letter with an arrow, such as $`\vec p`$ or $`\vec y`$, stands for a finite list of variables (or elements).

| Formula | Kind |
|---|---|
| $`p \lt q`$ | quantifier-free (also $`\Sigma_1`$, with $`\mathit{bb} = 0`$) |
| $`\exists y\ (p \lt y)`$ | $`\Sigma_1`$ |
| $`\exists y\ \exists z\ (p \lt y \land y \lt z \land E(y, z))`$ | $`\Sigma_1`$ |
| $`\forall y\ (y \lt p \lor p \lt y \lor y = p)`$ | not $`\Sigma_1`$ |

**Definition (satisfaction).** For a structure $`\mathfrak A`$ and parameters $`\vec p \in A`$ (each entry an element of $`A`$), $`\mathfrak A \models \varphi(\vec p)`$ means "$`\varphi`$ is true in $`\mathfrak A`$ at $`\vec p`$". A quantifier $`\exists y`$ ranges over the domain $`A`$.

Example: $`(\omega; \lt) \models \exists y\ (3 \lt y)`$ is true. $`(4; \lt) \models \exists y\ (3 \lt y)`$ is false, because the domain of $`(4; \lt)`$ is $`\{0, 1, 2, 3\}`$.

**Definition (witness).** If $`\mathfrak A \models \exists \vec y\ \psi(\vec p, \vec y)`$, a list $`\vec y`$ of elements of $`A`$ that makes $`\psi(\vec p, \vec y)`$ true is called a **witness**.

## 3. Conjunctions of literals

**Definition (literal).** An atomic formula or the negation of an atomic formula is a **literal**.

A quantifier-free formula is equivalent to a finite disjunction of conjunctions of literals (disjunctive normal form). An existential quantifier distributes over a disjunction.

```math
\exists \vec y\ (\psi_1 \lor \psi_2) \iff \exists \vec y\ \psi_1 \ \lor\ \exists \vec y\ \psi_2
```

So every $`\Sigma_1`$ formula is equivalent to a finite disjunction of formulas of the following form.

```math
\exists \vec y\ (\ell_1 \land \cdots \land \ell_k) \qquad (\ell_1, \ldots, \ell_k \text{ literals})
```

If all formulas of this form have the same truth value in two structures, then all $`\Sigma_1`$ formulas do.

**Example.** In the language $`\{\lt, E\}`$, $`\exists y\ \bigl((p \lt y \land \neg(y \lt q)) \lor E(p, y)\bigr)`$ is equivalent to $`\exists y\ (p \lt y \land \neg(y \lt q)) \lor \exists y\ E(p, y)`$.

- If $`\lt`$ is a linear order, equality is determined by $`\lt`$: $`v_a = v_b \iff \neg(v_a \lt v_b) \land \neg(v_b \lt v_a)`$. No equality symbol is needed.

## 4. Substructures and upward preservation

**Definition (substructure).** $`\mathfrak A`$ is a **substructure** of $`\mathfrak B`$ if $`A \subseteq B`$ and each symbol is interpreted by the restriction, that is, $`P^{\mathfrak A}(\vec a) \iff P^{\mathfrak B}(\vec a)`$ for $`\vec a \in A`$.

**Property 1.** In a substructure, quantifier-free formulas about elements of $`A`$ have the same truth value, because the atomic formulas have the same truth values.

**Property 2 (Σ₁ goes up).** In a substructure, if $`\mathfrak A \models \exists \vec y\ \psi(\vec p, \vec y)`$ then $`\mathfrak B \models \exists \vec y\ \psi(\vec p, \vec y)`$. The witnesses $`\vec y`$ in $`\mathfrak A`$ are also in $`B`$, and by Property 1 $`\psi`$ has the same truth value.

**The converse fails.** $`(4; \lt)`$ is a substructure of $`(\omega; \lt)`$. $`\exists y\ (3 \lt y)`$ is true in $`\omega`$ and false in $`4`$.

## 5. Σ₁-elementary substructures

**Definition (Σ₁-elementary substructure).** $`\mathfrak A`$ is a **$`\Sigma_1`$-elementary substructure** of $`\mathfrak B`$ if $`\mathfrak A`$ is a substructure of $`\mathfrak B`$ and, for every $`\Sigma_1`$ formula $`\varphi`$ and all parameters $`\vec p \in A`$,

```math
\mathfrak A \models \varphi(\vec p) \iff \mathfrak B \models \varphi(\vec p)
```

We write $`\mathfrak A \preccurlyeq_{\Sigma_1} \mathfrak B`$.

**Meaning.** A statement "there are finitely many elements like this" that mentions only elements of $`A`$ is true in $`\mathfrak A`$ whenever it is true in $`\mathfrak B`$. The witnesses can be chosen again inside $`A`$.

**Example (order only).** Let $`0 \lt \alpha \lt \beta`$ be ordinals.

```math
(\alpha; \lt) \preccurlyeq_{\Sigma_1} (\beta; \lt) \iff \alpha \text{ is a limit ordinal}
```

**Proof.**

- If $`\alpha = \gamma + 1`$: $`\exists y\ (\gamma \lt y)`$ with parameter $`\gamma`$ is true in $`\beta`$ ($`y = \gamma + 1`$) and false in $`\alpha`$. So it fails.
- If $`\alpha`$ is a limit: suppose a $`\Sigma_1`$ formula $`\exists \vec y\ \psi(\vec p, \vec y)`$ is true in $`\beta`$. Move its witnesses $`\vec y`$ into $`\alpha`$, keeping their order relative to the parameters.
  - Witnesses below the largest parameter are already in $`\alpha`$. Keep them.
  - There are finitely many witnesses above the largest parameter (when there are no parameters, count all witnesses here). Since $`\alpha`$ is a limit, there are infinitely many elements of $`\alpha`$ above the largest parameter ([01](01-ordinals.md) §2). Put the witnesses there in the same order.
  - Moving them does not change the truth values of the atomic formulas with $`\lt`$. So $`\psi`$ is true in $`\alpha`$.
  - The other direction is Property 2 of §4. $`\square`$

$`\alpha = 0`$ is also excluded: $`\exists y\ \neg(y \lt y)`$ is false in the empty structure $`0`$ and true in $`\beta`$.

## 6. The Tarski–Vaught test (Σ₁ version)

To prove $`\Sigma_1`$-elementarity it suffices to check the downward direction.

**Theorem (Tarski–Vaught test, Σ₁ version).** Let $`\mathfrak A`$ be a substructure of $`\mathfrak B`$. The following are equivalent.

1. $`\mathfrak A \preccurlyeq_{\Sigma_1} \mathfrak B`$.
2. For quantifier-free $`\psi`$ and $`\vec p \in A`$: if $`\mathfrak B \models \exists \vec y\ \psi(\vec p, \vec y)`$, then $`\mathfrak B \models \psi(\vec p, \vec y)`$ for some $`\vec y \in A`$.

**Proof.** 1 to 2: the formula is true in $`\mathfrak A`$, so there are witnesses in $`A`$; by Property 1 of §4, $`\psi`$ is true in $`\mathfrak B`$ too. 2 to 1: the upward direction is Property 2 of §4. For the downward direction, the witnesses from 2 lie in $`A`$, and by Property 1 we get $`\mathfrak A \models \psi(\vec p, \vec y)`$. $`\square`$

The general Tarski–Vaught test says the same for all formulas. This repository uses only $`\Sigma_1`$.

**How it is used.** Condition 2 says "$`A`$ is closed under witnesses". The theorem (λ(γ) is Good) of [08 Closure and chain](08-closure-chain.md) §6 is proved in this form: start from $`\gamma`$, keep adding witnesses of true statements, and take the supremum.

## 7. The normal form of Σ₁ formulas

The language of this repository consists of $`\lt`$, the symbols $`\mathrm{Rel}_{t,i,j}`$ and the symbols $`\mathrm{Top}_{t,i}`$. The index $`t`$ is a template and $`i, j`$ are positions; both are defined below. The interpretations of the symbols are fixed in [07](07-relation-r.md) §2. Here we use only the following.

- In the structure of height $`c`$, $`\mathrm{Rel}_{t,i,j}`$ is a relation between points.
- In the structure of height $`c`$, $`\mathrm{Top}_{t,i}`$ is a relation from points to $`c`$, which lies outside the domain. In [07](07-relation-r.md) §2 this $`c`$ becomes the top ([02](02-well-founded.md) §3) of $`R`$. $`\mathrm{Top}_{t,i}`$ is called a **top predicate**. The interpretation of a top predicate differs for each height $`c`$.
- Each of these symbols carries a key. The key is computed from the values of the variables by a template.

**Definition (key syntax).** Let $`K`$ be the set of keys. In this repository $`K = \mathrm{Key}_m`$ ([02](02-well-founded.md) §3). A **key syntax** consists of the following three things.

- For each $`n \in \mathbb N`$, a set $`\mathcal T_n`$. Its elements are called **templates** over $`n`$ variables.
- For each $`n`$, a function $`\mathrm{eval} : \mathcal T_n \times (\mathrm{Fin}\ n \to \mathrm{Label}) \to K`$. We write $`\mathrm{eval}(t, \vec v)`$ as $`\mathrm{eval}\ t\ \vec v`$ and call it the key obtained by evaluating the template $`t`$ at the values $`\vec v`$ of the variables.
- Monotonicity: pointwise smaller values give a smaller key.

```math
\forall t \in \mathcal T_n\ \ \forall \vec v, \vec w\ \ \Bigl(\bigl(\forall i \lt n\ \ w_i \le v_i\bigr) \implies \mathrm{eval}\ t\ \vec w \le \mathrm{eval}\ t\ \vec v\Bigr)
```

**Example (the key syntax of ω-Y).** Let $`K = \mathrm{Key}_m`$ and $`\mathcal T_n := \mathrm{Fin}\ m \to \mathrm{Option}(\mathrm{Fin}\ n)`$, and define coordinate $`i`$ of the key by

```math
(\mathrm{eval}\ t\ \vec v)_i := \begin{cases} v_j & (t_i = \mathrm{some}\ j) \cr \top & (t_i = \mathrm{none}) \end{cases}
```

For $`m = 2`$ and $`n = 3`$, $`t = (\mathrm{some}\ 0, \mathrm{none})`$ gives the key $`(v_0, \top)`$ and $`t' = (\mathrm{some}\ 0, \mathrm{some}\ 2)`$ gives the key $`(v_0, v_2)`$. Each coordinate is some $`v_j`$ or $`\top`$, so monotonicity holds. $`\mathcal T_n`$ is a finite set with $`(n+1)^m`$ elements. [06](06-combinatorial-layer.md) §1 uses this key syntax.

**Definition (position).** List the variables of a formula over $`n`$ variables as $`v_0, \ldots, v_{n-1}`$ and write $`\vec v = (v_0, \ldots, v_{n-1})`$. The index $`i`$ is called the **position** of the variable $`v_i`$.

**Definition (literal).** A literal over $`n`$ variables is of one of the following 6 kinds. $`i, j`$ are positions and $`t \in \mathcal T_n`$ is a template.

| Literal | Key |
|---|---|
| $`v_i \lt v_j`$, $`\neg(v_i \lt v_j)`$ | none |
| $`\mathrm{Rel}_{t,i,j}`$, $`\neg\mathrm{Rel}_{t,i,j}`$ | $`\mathrm{eval}\ t\ \vec v`$ |
| $`\mathrm{Top}_{t,i}`$, $`\neg\mathrm{Top}_{t,i}`$ | $`\mathrm{eval}\ t\ \vec v`$ |

**Definition (normal form).** A $`\Sigma_1`$ formula is given by a triple $`\varphi = (n, F, L)`$.

| Component | Meaning |
|---|---|
| $`n \in \mathbb N`$ | number of variables |
| $`F \subseteq \mathrm{Fin}\ n`$ | set of parameter positions; the variables at positions not in $`F`$ are existentially quantified |
| $`L`$ | a finite list of literals; the formula is their conjunction |

**Definition (structure).** A structure of this repository is written in the following form.

```math
\mathfrak A = (c;\ \lt,\ \mathrm{rel},\ \mathrm{top},\ \mathrm{allow})
```

- $`c \in \mathrm{Label}`$ is the height, and the domain is $`\{x \mid x \lt c\}`$.
- $`\mathrm{rel}(\kappa, x, y)`$ ($`\kappa \in K`$, $`x, y \in \mathrm{Label}`$) collects the interpretations of the symbols $`\mathrm{Rel}_{t,i,j}`$ into one: $`\mathrm{Rel}_{t,i,j}(\vec v) :\iff \mathrm{rel}(\mathrm{eval}\ t\ \vec v,\ v_i,\ v_j)`$.
- $`\mathrm{top}(\kappa, x)`$ collects the interpretations of the symbols $`\mathrm{Top}_{t,i}`$ into one: $`\mathrm{Top}_{t,i}(\vec v) :\iff \mathrm{top}(\mathrm{eval}\ t\ \vec v,\ v_i)`$.
- $`\mathrm{allow}(\kappa)`$ is a condition on keys meaning "the top predicate of key $`\kappa`$ is **defined**". Its meaning is explained in §8.

**Definition (truth of a literal).** We write $`\vec v \models \ell`$ when the literal $`\ell`$ holds at the list of values $`\vec v \in (\mathrm{Fin}\ n \to \mathrm{Label})`$. Put $`\kappa := \mathrm{eval}\ t\ \vec v`$.

```math
\begin{aligned}
\vec v \models v_i \lt v_j &\iff v_i \lt v_j, \cr
\vec v \models \mathrm{Rel}_{t,i,j} &\iff \mathrm{rel}(\kappa, v_i, v_j), \cr
\vec v \models \mathrm{Top}_{t,i} &\iff \mathrm{allow}(\kappa) \ \land\ \mathrm{top}(\kappa, v_i), \cr
\vec v \models \neg\mathrm{Top}_{t,i} &\iff \mathrm{allow}(\kappa) \ \land\ \neg\,\mathrm{top}(\kappa, v_i).
\end{aligned}
```

$`\neg(v_i \lt v_j)`$ and $`\neg\mathrm{Rel}_{t,i,j}`$ are the negations of the first and second lines. $`\neg\mathrm{Top}_{t,i}`$ is not the negation of the third line. If $`\mathrm{allow}(\kappa)`$ is false, both $`\mathrm{Top}_{t,i}`$ and $`\neg\mathrm{Top}_{t,i}`$ are false.

**Definition (satisfaction).** For $`\varphi = (n, F, L)`$ and $`\vec p \in (\mathrm{Fin}\ n \to \mathrm{Label})`$ define

```math
\mathfrak A \models \varphi(\vec p) \iff \exists \vec v \in (\mathrm{Fin}\ n \to \mathrm{Label})\ \Bigl(\bigl(\forall i \in F\ \ v_i = p_i\bigr) \land \bigl(\forall i \lt n\ \ v_i \lt c\bigr) \land \bigl(\forall \ell \in L\ \ \vec v \models \ell\bigr)\Bigr)
```

- $`\vec p`$ is a list of length $`n`$, but only its entries at the positions in $`F`$ are read.
- The condition $`v_i \lt c`$ expresses "the domain is $`\{x \mid x \lt c\}`$". It also requires $`p_i = v_i \lt c`$ at the positions in $`F`$.
- The $`v_i`$ at positions not in $`F`$ are the witnesses.

**Example.** $`\varphi = (2, \{0\}, [v_0 \lt v_1])`$ is $`\exists v_1\ (p_0 \lt v_1)`$. It is true at height $`c`$ exactly when $`p_0 + 1 \lt c`$ (checked in Python for natural numbers $`c \lt 8`$).

## 8. Comparing two structures, and partial top predicates

The comparison used in this repository differs from the textbook definition in two ways.

**Difference 1: one symbol, two interpretations.** The definition of $`R`$ ([07](07-relation-r.md) §4) compares the structure of height $`a`$ with the structure of height $`b`$ (labels $`a \lt b`$). The top predicate $`\mathrm{Top}_{t,i}`$ is interpreted as "the relation to $`a`$" at height $`a`$ and as "the relation to $`b`$" at height $`b`$. So as it stands, one is not a substructure of the other.

Therefore this comparison does not assume a substructure. It only requires that every $`\Sigma_1`$ formula with parameters below $`a`$ has the same truth value on both sides.

**Definition (comparison).** Let two structures differ only in their heights and in the interpretations of the top predicates.

```math
\mathfrak A = (a;\ \lt,\ \mathrm{rel},\ \mathrm{top}_a,\ \mathrm{allow}), \qquad \mathfrak B = (b;\ \lt,\ \mathrm{rel},\ \mathrm{top}_b,\ \mathrm{allow})
```

```math
\mathfrak A \preccurlyeq_{\Sigma_1} \mathfrak B \ :\iff\ \forall \varphi = (n, F, L)\ \ \forall \vec p\ \ \Bigl(\bigl(\forall i \in F\ \ p_i \lt a\bigr) \implies \bigl(\mathfrak A \models \varphi(\vec p) \iff \mathfrak B \models \varphi(\vec p)\bigr)\Bigr)
```

Taking $`F = \mathrm{Fin}\ n`$ (no quantifier), the literals about points below $`a`$ have the same truth values. The literals of top predicates also agree at the keys where $`\mathrm{allow}`$ is true. So when the agreement holds and the top predicates are restricted to the keys where $`\mathrm{allow}`$ is true, the smaller structure is a substructure of the larger one, and a $`\Sigma_1`$-elementary one.

**Difference 2: top predicates are partial.** A top predicate is defined only at the keys where $`\mathrm{allow}`$ is true. As in §7, where $`\mathrm{allow}(\kappa)`$ is false, both $`\mathrm{Top}_{t,i}`$ and $`\neg\mathrm{Top}_{t,i}`$ are false.

| Condition $`\mathrm{allow}(\kappa)`$ | Top predicates that are defined | Used for |
|---|---|---|
| always true | all | the structure of height $`\omega_1`$ (Good, defined in [08](08-closure-chain.md) §1) |
| $`\kappa \lt \theta`$ | those whose key is below $`\theta`$ | the structures $`\mathfrak A^c_\theta`$ (defined in [07](07-relation-r.md) §3) |

**Example.** Let the key length be $`m = 1`$, $`\theta = (5)`$ (the key whose coordinate 0 is the label 5) and $`\mathrm{allow}(\kappa) :\iff \kappa \lt \theta`$. There are two variables $`v_0, v_1`$, and the templates are those of the key syntax of ω-Y in §7. $`t = (\mathrm{some}\ 0)`$ gives the key $`(v_0)`$ and $`t_\top = (\mathrm{none})`$ gives the key $`(\top)`$.

| Literal | $`\vec v = (3, 10)`$ | $`\vec v = (7, 10)`$ |
|---|---|---|
| $`\mathrm{Top}_{t,1}`$ | same as $`\mathrm{top}((3), 10)`$ | false (the key $`(7)`$ is $`\ge \theta`$) |
| $`\neg\mathrm{Top}_{t,1}`$ | same as $`\neg\,\mathrm{top}((3), 10)`$ | false |
| $`\mathrm{Top}_{t_\top,1}`$ | false (the key $`(\top)`$ is $`\ge \theta`$) | false |

The values of the table were checked with the definitions of §7 written in Python, both for $`\mathrm{top}((3), 10)`$ true and for it false.

**Difference from the 1-Y version.** The 1-Y version ([01](01-ordinals.md) §7), in its note 03 §8, decided whether a top predicate may be read from the positions of the variables alone. In this repository, whether it is defined depends on the value of the key $`\mathrm{eval}\ t\ \vec v`$, that is, on the values of the variables. So the following three lemmas are used.

**Lemma 1 (same readings, same truth value).** Let two structures $`(c; \lt, \mathrm{rel}, \mathrm{top}, \mathrm{allow})`$ and $`(c; \lt, \mathrm{rel}', \mathrm{top}', \mathrm{allow})`$ with the same height $`c`$ and the same $`\mathrm{allow}`$ satisfy

```math
\forall \kappa\ \forall x\ \forall y \lt c\ \ \bigl(\mathrm{rel}(\kappa, x, y) \iff \mathrm{rel}'(\kappa, x, y)\bigr), \qquad \forall \kappa\ \forall x\ \ \bigl(\mathrm{allow}(\kappa) \implies (\mathrm{top}(\kappa, x) \iff \mathrm{top}'(\kappa, x))\bigr)
```

Then for every $`\varphi`$ and $`\vec p`$ the truth values in the two structures are equal.

**Proof.** Every list of values $`\vec v`$ lies below $`c`$, so a $`\mathrm{Rel}`$ literal reads only places with $`y \lt c`$. A literal of a top predicate is false in both structures if $`\mathrm{allow}(\kappa)`$ is false, and reads the same value if it is true. $`\square`$

**Lemma 2 (widening allow).** Let $`\forall \kappa\ (\mathrm{allow}(\kappa) \implies \mathrm{allow}'(\kappa))`$. If $`\vec v \models \ell`$ under $`\mathrm{allow}`$, then $`\vec v \models \ell`$ under $`\mathrm{allow}'`$.

**Proof.** Only the literals of top predicates read $`\mathrm{allow}`$, and for them $`\mathrm{allow}(\kappa)`$ gives $`\mathrm{allow}'(\kappa)`$. $`\square`$

**Lemma 3 (lowering pointwise keeps the key condition).** Let $`\theta, \Theta`$ be keys and $`\vec w, \vec v`$ lists of values with $`\forall i \lt n\ \ w_i \le v_i`$. For a literal $`\ell`$ assume the following two.

- $`\vec v \models \ell`$ (interpretations $`\mathrm{rel}, \mathrm{top}`$, $`\mathrm{allow}(\kappa) :\iff \kappa \lt \theta`$).
- $`\vec w \models \ell`$ (interpretations $`\mathrm{rel}', \mathrm{top}'`$, $`\mathrm{allow}(\kappa) :\iff \kappa \lt \Theta`$).

Then $`\vec w \models \ell`$ (interpretations $`\mathrm{rel}', \mathrm{top}'`$, $`\mathrm{allow}(\kappa) :\iff \kappa \lt \theta`$).

**Proof.** For a literal of a top predicate, the monotonicity of the key syntax (§7) gives $`\mathrm{eval}\ t\ \vec w \le \mathrm{eval}\ t\ \vec v \lt \theta`$. The other literals do not read $`\mathrm{allow}`$. $`\square`$

Lemma 1 is used in [07](07-relation-r.md) §6 to remove the guards ([02](02-well-founded.md) §5). Lemmas 2 and 3 are used in the weakening of [07](07-relation-r.md) §7 and in [09](09-obligations.md).

## 9. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "The relation R" | $`\preccurlyeq_{\Sigma_1}`$, formulas that are existentially quantified conjunctions of literals, partial top predicates (§7, §8) |
| [README](../../README-en.md) "Proofs of the three theorems" | Good points in Tarski–Vaught form (§6); lowering pointwise keeps the key below $`\theta`$ (Lemma 3 of §8) |
| [notes/01-design.md](../../notes/01-design.md) §2.1, §2.2 (Japanese) | structures and formulas |
| [notes/01-design.md](../../notes/01-design.md) §3.3 (Japanese) | Good points in Tarski–Vaught form |

## 10. Lean correspondence

| Concept | Lean | File |
|---|---|---|
| key syntax | `KeySyntax` (`Template`, `eval`, `monotone_eval`) | [OmegaY/Reflection/Interface.lean](../../OmegaY/Reflection/Interface.lean) |
| key syntax of ω-Y | `Keys.Template m n`, `Keys.eval`, `Keys.eval_mono`, `KeyReflection.vectorSyntax m`, `Model.keySyntax m` | [OmegaY/Keys.lean](../../OmegaY/Keys.lean), [OmegaY/KeyReflection.lean](../../OmegaY/KeyReflection.lean), [OmegaY/Model.lean](../../OmegaY/Model.lean) |
| literal | `Lit n` (`lt i j pos`, `rel t i j pos`, `top t i pos`; `pos = false` is the negation) | [Por/Formula.lean](../../Por/Formula.lean) |
| normal form $`(n, F, L)`$ | `Form` (`n`, `fixed : Fin n → Bool`, `lits`); $`F = \{i \mid \mathit{fixed}_i = \mathrm{true}\}`$ | same |
| truth of a literal $`\vec v \models \ell`$ | `Lit.Holds rel top allow v` | same |
| satisfaction $`(c; \lt, \mathrm{rel}, \mathrm{top}, \mathrm{allow}) \models \varphi(\vec p)`$ | `Sat rel top allow c φ p` | same |
| comparison (§8, $`\mathrm{allow}(\kappa) :\iff \kappa \lt \theta`$) | `ElemL rel topA topB θ a b` | same |
| Lemma 1 | `Lit.holds_congr`, `sat_congr` | same |
| Lemma 2 | `Lit.holds_allow_mono` | same |
| Lemma 3 | `Lit.holds_of_le` | same |
