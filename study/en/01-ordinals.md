[← Back](README.md) | [English](01-ordinals.md) | [Japanese](../01-ordinals.md)

# Ordinals and ω₁

Prerequisites: none

This note explains ordinals and $`\omega_1`$. Later notes attach ordinals $`\le \omega_1`$ (the labels of §6) to the columns of expressions in the proof that expansion terminates ([06](06-combinatorial-layer.md) §4, §8). The facts that are used are the regularity in §5, the labels in §6 and the counting of parameter lists in §7.

## 1. Well-orders and ordinals

**Definition (well-order).** A linear order $`\lt`$ on a set $`X`$ is a **well-order** if every nonempty subset of $`X`$ has a least element.

**Definition (infinite descending sequence).** A sequence $`(x_n)_{n \in \mathbb N}`$ with $`x_0 \gt x_1 \gt x_2 \gt \cdots`$ is an **infinite descending sequence**.

A linear order is a well-order if and only if it has no infinite descending sequence. The direction "no infinite descending sequence implies well-order" uses a weak form of the axiom of choice (dependent choice).

| Order | Well-order? | Reason |
|---|---|---|
| $`(\mathbb N, \lt)`$ | yes | every nonempty subset has a least element |
| $`(\mathbb Z, \lt)`$ | no | $`0 \gt -1 \gt -2 \gt \cdots`$ |
| $`(\mathbb Q_{\ge 0}, \lt)`$ | no | $`1 \gt 1/2 \gt 1/4 \gt \cdots`$ |

**Definition (ordinal).** An **ordinal** is the order type of a well-order. We identify an ordinal $`\alpha`$ with the set $`\{\beta \mid \beta \lt \alpha\}`$ of smaller ordinals.

In increasing order:

```math
0,\ 1,\ 2,\ \ldots,\ \omega,\ \omega+1,\ \omega+2,\ \ldots,\ \omega \cdot 2,\ \ldots,\ \omega^2,\ \ldots,\ \omega^\omega,\ \ldots
```

- $`\omega`$ is the order type of the natural numbers. $`\omega = \{0, 1, 2, \ldots\}`$.
- The ordinals are well-ordered by $`\lt`$. Every nonempty collection of ordinals has a least element.
- We write $`\mathrm{Ord}`$ for the class of all ordinals.
- An ordinal below $`\omega^\omega`$ can be written in exactly one way as $`\omega^{d} c_d + \cdots + \omega c_1 + c_0`$ ($`d, c_0, \ldots, c_d \in \mathbb N`$), where $`c_d \ne 0`$ if $`d \gt 0`$ (Cantor normal form). The rows of the mountains in [05](05-omegay-mountain.md) are ordinals of this form.

## 2. Successors and limits

**Definition (successor).** $`\alpha + 1`$ is the ordinal right after $`\alpha`$. An ordinal of the form $`\alpha + 1`$ is a **successor ordinal**.

**Definition (limit ordinal).** An ordinal that is neither 0 nor a successor ordinal is a **limit ordinal**.

| Ordinal | Kind |
|---|---|
| $`0`$ | neither |
| $`5`$, $`\omega+1`$, $`\omega \cdot 2 + 3`$ | successor |
| $`\omega`$, $`\omega \cdot 2`$, $`\omega^2`$ | limit |

**Property.** If $`\alpha`$ is a limit ordinal and $`\beta \lt \alpha`$, then $`\beta + 1 \lt \alpha`$. So above $`\beta`$ there are infinitely many elements below $`\alpha`$.

This property is used in an example of [03 Structures and Σ₁-elementary substructures](03-sigma1-elementary.md).

## 3. Suprema

**Definition (supremum).** The **supremum** $`\sup S`$ of a set $`S`$ of ordinals is the least ordinal that is $`\ge`$ every element of $`S`$.

- If $`S`$ has a largest element, $`\sup S`$ is that element. This is always the case for a nonempty finite set. The supremum of the empty set is $`0`$.
- If $`S`$ has no largest element, $`\sup S`$ is not in $`S`$.

| $`S`$ | $`\sup S`$ |
|---|---|
| $`\{2, 5, 3\}`$ | $`5`$ |
| $`\{0, 1, 2, \ldots\}`$ | $`\omega`$ |
| $`\{\omega, \omega+1, \omega+2, \ldots\}`$ | $`\omega \cdot 2`$ |

To get an ordinal strictly above all $`y_i`$, use $`\sup_{i} (y_i + 1)`$. Indeed $`y_i \lt y_i + 1 \le \sup_i (y_i + 1)`$. The "height of witnesses" defined in [08 Closure and chain](08-closure-chain.md) §3 has this form.

## 4. Countability and ω₁

**Definition (countable).** A set $`X`$ is **countable** if $`X`$ is empty or there is a surjection $`\mathbb N \to X`$.

**Definition (countable ordinal).** An ordinal $`\alpha`$ is **countable** if $`\{\beta \mid \beta \lt \alpha\}`$ is countable.

$`0, 1, \omega, \omega+1, \omega \cdot 2, \omega^2, \omega^\omega, \varepsilon_0`$ are all countable.

**Definition (ω₁).** $`\omega_1`$ is the least uncountable ordinal. So the ordinals below $`\omega_1`$ are exactly the countable ordinals.

```math
\alpha \lt \omega_1 \iff \alpha \text{ is countable}
```

Three facts are used.

- $`0 \lt \omega_1`$.
- $`\alpha \lt \omega_1 \implies \alpha + 1 \lt \omega_1`$.
- $`\gamma \lt \omega_1 \implies \{\beta \mid \beta \lt \gamma\}`$ is countable.

Reason for the second: $`\{\beta \mid \beta \lt \alpha + 1\} = \{\beta \mid \beta \lt \alpha\} \cup \{\alpha\}`$, and a countable set with one more point is countable. In other words, $`\omega_1`$ is a limit ordinal.

## 5. Regularity of ω₁

**Theorem (regularity of ω₁).** If $`\alpha_n \lt \omega_1`$ for every $`n \in \mathbb N`$, then

```math
\sup_{n \in \mathbb N} \alpha_n \lt \omega_1
```

The index set need not be $`\mathbb N`$. Any countable index set works.

**Proof.** Let $`\sigma := \sup_n \alpha_n`$. If $`\beta \lt \sigma`$, then $`\beta \lt \alpha_n`$ for some $`n`$. So

```math
\{\beta \mid \beta \lt \sigma\} = \bigcup_{n} \{\beta \mid \beta \lt \alpha_n\}
```

The right side is a countable union of countable sets. The terms with $`\alpha_n = 0`$ add nothing to the union, so drop them. For each remaining $`n`$ choose a surjection $`e_n : \mathbb N \to \alpha_n`$. Then $`(n, t) \mapsto e_n(t)`$ is a surjection from $`\mathbb N \times \mathbb N`$ onto the union. Since $`\mathbb N \times \mathbb N`$ is countable, so is the union. Hence $`\sigma`$ is countable and $`\sigma \lt \omega_1`$. $`\square`$

- Choosing countably many surjections $`e_n`$ at once uses the axiom of choice (countable choice).
- The statement fails for an uncountable index set. For example $`\sup_{\alpha \lt \omega_1} \alpha = \omega_1`$.

## 6. Labels

**Definition (label).** An ordinal $`\le \omega_1`$ is called a **label**. We write $`\mathrm{Label}`$ for the set of labels.

```math
\mathrm{Label} := \{\, o \in \mathrm{Ord} \mid o \le \omega_1 \,\}
```

Labels are ordered by the order $`\lt`$ of ordinals. $`\mathrm{Label}`$ is a set of ordinals, so by §1 it is well-ordered. The least label is $`0`$ and the largest label is $`\omega_1`$.

Three facts are used. All follow from §4.

- $`0 \lt \omega_1`$.
- $`\forall x \in \mathrm{Label}\ \ x \le \omega_1`$.
- If $`a \in \mathrm{Label}`$ and $`a \lt \omega_1`$, then $`\{x \in \mathrm{Label} \mid x \lt a\} = \{\beta \mid \beta \lt a\}`$ is countable.

**Why ω₁ itself is a label.** The labels attached to the columns of expressions are all below $`\omega_1`$ ([06](06-combinatorial-layer.md) §4). On the other hand, the relation $`R`$ defined in [07](07-relation-r.md) also takes $`\omega_1`$ as its third argument ([08](08-closure-chain.md) §1, [09](09-obligations.md) §3). That is why $`\omega_1`$ is a label too.

## 7. Counting parameter lists

**Notation.** For $`n \in \mathbb N`$ let $`\mathrm{Fin}\ n := \{0, 1, \ldots, n-1\}`$. For a set $`X`$, $`\mathrm{Fin}\ n \to X`$ is the set of lists $`(x_0, \ldots, x_{n-1})`$ of $`n`$ elements of $`X`$.

**Notation (Option).** For a set $`X`$ let $`\mathrm{Option}\,X := \{\mathrm{some}\ x \mid x \in X\} \cup \{\mathrm{none}\}`$. $`\mathrm{none}`$ is a new element different from every $`\mathrm{some}\ x`$.

Later, labels are put into some of the $`n`$ variables of a formula (defined in [03](03-sigma1-elementary.md) §2). These labels are used as parameters of formulas ([03](03-sigma1-elementary.md) §2), so we call them parameters here too. One list records at which indices there is a parameter and what its value is.

**Definition (partial parameter list).** For a label $`\gamma`$ and $`n \in \mathbb N`$ define

```math
\mathrm{Par}_n(\gamma) := \mathrm{Fin}\ n \to \mathrm{Option}\,\{\, x \in \mathrm{Label} \mid x \lt \gamma \,\}
```

For $`q \in \mathrm{Par}_n(\gamma)`$, $`q_i = \mathrm{some}\ x`$ means "put the parameter $`x`$ at index $`i`$", and $`q_i = \mathrm{none}`$ means "put no parameter at index $`i`$". From $`q`$ we make a list of labels $`\mathrm{toP}(q) \in (\mathrm{Fin}\ n \to \mathrm{Label})`$:

```math
\mathrm{toP}(q)_i := \begin{cases} x & (q_i = \mathrm{some}\ x) \cr 0 & (q_i = \mathrm{none}) \end{cases}
```

**Theorem (countable).** If $`\gamma \lt \omega_1`$, then $`\mathrm{Par}_n(\gamma)`$ is countable for each $`n \in \mathbb N`$.

**Proof.** $`\{x \in \mathrm{Label} \mid x \lt \gamma\}`$ is countable (§6). $`\mathrm{Option}`$ adds one point, so the set stays countable. A finite product of countable sets is countable. $`\square`$

**Theorem (every parameter tuple can be written).** Let $`n \in \mathbb N`$, $`F \subseteq \mathrm{Fin}\ n`$ and $`p \in (\mathrm{Fin}\ n \to \mathrm{Label})`$ with $`p_i \lt \gamma`$ for all $`i \in F`$. Then there is a $`q \in \mathrm{Par}_n(\gamma)`$ with $`\mathrm{toP}(q)_i = p_i`$ for all $`i \in F`$.

**Proof.** Put $`q_i := \mathrm{some}\ p_i`$ for $`i \in F`$ and $`q_i := \mathrm{none}`$ for $`i \notin F`$. $`\square`$

**Example.** Let $`\gamma = \omega + 1`$, $`n = 3`$, $`F = \{0, 2\}`$ and $`p = (3, 5, \omega)`$. Then $`q = (\mathrm{some}\ 3, \mathrm{none}, \mathrm{some}\ \omega) \in \mathrm{Par}_3(\omega + 1)`$ and $`\mathrm{toP}(q) = (3, 0, \omega)`$. The value $`5`$ at index $`1 \notin F`$ does not survive in $`q`$.

**Why it is needed.** In [08 Closure and chain](08-closure-chain.md) we take a supremum over all formulas with parameters below $`\gamma`$. The index set is the set of all pairs of a formula $`\varphi`$ and an element of $`\mathrm{Par}_n(\gamma)`$, where $`n`$ is the number of variables of $`\varphi`$. There are countably many formulas ([08](08-closure-chain.md) §2), so this set is countable too. So the theorem of §5 applies directly.

**Difference from the 1-Y version.** The **1-Y version** is the [study/](https://github.com/koteitan/1y-wo-por/tree/main/study) of the sister project [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por). It explains a proof of the same shape for the 1-Y sequence. Its note 01 §6 enumerates the ordinals below $`\gamma`$ by a surjection $`e_\gamma : \mathbb N \to \gamma`$ and writes parameters as lists of natural numbers. There the index set does not depend on $`\gamma`$. This repository puts the ordinals of the parameters directly into the index. The index set depends on $`\gamma`$, but it is countable, so the theorem of §5 applies.

## 8. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "Structure of the proof" | each column gets a label, an ordinal $`\le \omega_1`$ (§6) |
| [README](../../README-en.md) "The relation R" | labels are ordered by $`\lt`$, a well-order (§1, §6) |
| [README](../../README-en.md) "Proofs of the three theorems" | by the regularity of $`\omega_1`$ (§5), the Good points are cofinal in $`\omega_1`$ |
| [notes/01-design.md](../../notes/01-design.md) §3.3 (Japanese) | Good points, countably many formulas, $`\omega`$ iterations (§5, §7) |

## 9. Lean correspondence

| Concept | Lean | File |
|---|---|---|
| type of ordinals, $`\{\beta \mid \beta \lt \gamma\}`$ | `Ordinal.{0}`, `Set.Iio γ` | Mathlib |
| $`\lt`$ is well-founded | `wellFounded_lt` | Mathlib |
| supremum, $`y_i \lt \sup_i (y_i + 1)`$ | `iSup` (`⨆`), `Ordinal.lt_iSup_add_one` | Mathlib |
| countable | `Countable` | Mathlib |
| $`\omega_1`$ and the three facts of §4 | `ω₁`, `Ordinal.omega_pos 1`, `(isSuccLimit_omega 1).add_one_lt`, `countable_iio_ordinal` (from `Cardinal.mk_Iio_ordinal`) | Mathlib, [Por/Supply.lean](../../Por/Supply.lean) |
| regularity (§5) | `Ordinal.iSup_lt_omega_one` (used in `wh_lt`, `nextO_lt`, `lam_lt`) | Mathlib, [Por/Supply.lean](../../Por/Supply.lean) |
| labels, $`0`$, $`\omega_1`$ | `Label := {o : Ordinal.{0} // o ≤ ω₁}`, `zeroL`, `top`, `zeroL_lt_top`, `le_topL`, `countable_iio` | [Por/Supply.lean](../../Por/Supply.lean) |
| other names for the labels | `OrdinalSupply.Label`, `OrdinalSupply.top`, `bot_lt_top`, `Model.Label` | [OmegaY/Reflection/OrdinalSupply.lean](../../OmegaY/Reflection/OrdinalSupply.lean), [OmegaY/Model.lean](../../OmegaY/Model.lean) |
| $`\mathrm{Fin}\ n`$, $`\mathrm{Option}`$ | `Fin n`, `Option` | Lean core |
| $`\mathrm{Par}_n(\gamma)`$, $`\mathrm{toP}`$ | `Fin n → Option (Set.Iio γ)`, `toP` | [Por/Supply.lean](../../Por/Supply.lean) |
| $`\mathrm{Par}_n(\gamma)`$ is countable | the `infer_instance` inside `input_countable` | same |
