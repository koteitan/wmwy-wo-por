[← Back](README.md) | [English](01-ordinals.md) | [Japanese](../01-ordinals.md)

# Ordinals and ω₁

Prerequisites: none

This note explains the ordinals used as labels and $`\omega_1`$, which bounds the labels. The facts used later are the regularity in §5, the label type in §6 and the counting of parameters in §7.

## 1. Well-orders and ordinals

**Definition (well-order).** A total order $`\lt`$ on a set $`X`$ is a **well-order** if every nonempty subset of $`X`$ has a least element.

**Definition (infinite descending sequence).** A sequence $`(x_n)_{n \in \mathbb N}`$ with $`x_0 \gt x_1 \gt x_2 \gt \cdots`$ is an **infinite descending sequence**.

A total order is a well-order if and only if it has no infinite descending sequence. The direction "no infinite descending sequence implies well-order" uses a weak form of the axiom of choice (dependent choice).

| Order | Well-order? | Reason |
|---|---|---|
| $`(\mathbb N, \lt)`$ | yes | every nonempty subset has a least element |
| $`(\mathbb Z, \lt)`$ | no | $`0 \gt -1 \gt -2 \gt \cdots`$ |
| $`(\mathbb Q_{\ge 0}, \lt)`$ | no | $`1 \gt 1/2 \gt 1/4 \gt \cdots`$ |

**Definition (ordinal).** An **ordinal** is the order type of a well-order. An ordinal $`\alpha`$ is identified with the set $`\{\beta \mid \beta \lt \alpha\}`$ of smaller ordinals.

In increasing order:

```math
0,\ 1,\ 2,\ \ldots,\ \omega,\ \omega+1,\ \omega+2,\ \ldots,\ \omega \cdot 2,\ \ldots,\ \omega^2,\ \ldots,\ \omega^\omega,\ \ldots
```

- $`\omega`$ is the type of the natural numbers: $`\omega = \{0, 1, 2, \ldots\}`$.
- The ordinals are well-ordered by $`\lt`$. Every collection of ordinals has a least element.
- An ordinal below $`\omega^\omega`$ can be written in exactly one way as $`\omega^{d} c_d + \cdots + \omega c_1 + c_0`$ with $`c_i \in \mathbb N`$ (Cantor normal form). The rows of the mountain in [05](05-omegay-mountain.md) are ordinals of this form.

In Lean the type of ordinals is `Ordinal.{0}`. $`\{\beta \mid \beta \lt \gamma\}`$ is `Set.Iio γ`.

## 2. Successors and limits

**Definition (successor).** $`\alpha + 1`$ is the ordinal right after $`\alpha`$. An ordinal of the form $`\alpha + 1`$ is a **successor ordinal**.

**Definition (limit ordinal).** An ordinal that is neither 0 nor a successor is a **limit ordinal**.

| Ordinal | Kind |
|---|---|
| $`0`$ | neither |
| $`5`$, $`\omega+1`$, $`\omega \cdot 2 + 3`$ | successor |
| $`\omega`$, $`\omega \cdot 2`$, $`\omega^2`$ | limit |

**Property.** If $`\alpha`$ is a limit ordinal and $`\beta \lt \alpha`$, then $`\beta + 1 \lt \alpha`$. Hence there are infinitely many elements above $`\beta`$ and below $`\alpha`$.

- This property is used in the examples of [03](03-sigma1-elementary.md).
- In Lean it is used for $`\omega_1`$ (§4) in the form `(isSuccLimit_omega 1).add_one_lt`, in `wh_lt` and `nextO_lt` of [08](08-closure-chain.md).

## 3. Suprema

**Definition (supremum).** The **supremum** $`\sup S`$ of a set $`S`$ of ordinals is the least ordinal that is at least every element of $`S`$.

- If $`S`$ has a greatest element, $`\sup S`$ is that element. A nonempty finite set always has one. The supremum of the empty set is $`0`$.
- If $`S`$ has no greatest element, $`\sup S`$ is not in $`S`$.

| $`S`$ | $`\sup S`$ |
|---|---|
| $`\{2, 5, 3\}`$ | $`5`$ |
| $`\{0, 1, 2, \ldots\}`$ | $`\omega`$ |
| $`\{\omega, \omega+1, \omega+2, \ldots\}`$ | $`\omega \cdot 2`$ |

To get a number strictly greater than every element, use $`\sup_{i} (y_i + 1)`$, since $`y_i \lt y_i + 1 \le \sup_i (y_i + 1)`$. In Lean this is `Ordinal.lt_iSup_add_one`. The height of witnesses `wh` in [08](08-closure-chain.md) has this form.

In Lean the indexed supremum is `⨆ i, f i` (`iSup`).

## 4. Countability and ω₁

**Definition (countable).** A set $`X`$ is **countable** if it is empty or there is a surjection $`\mathbb N \to X`$. In Lean this is the type class `Countable`.

**Definition (countable ordinal).** An ordinal $`\alpha`$ is **countable** if $`\{\beta \mid \beta \lt \alpha\}`$ is countable.

$`0, 1, \omega, \omega+1, \omega \cdot 2, \omega^2, \omega^\omega, \varepsilon_0`$ are all countable.

**Definition (ω₁).** $`\omega_1`$ is the first uncountable ordinal. The ordinals below $`\omega_1`$ are exactly the countable ordinals.

```math
\alpha \lt \omega_1 \iff \alpha \text{ is countable}
```

In Lean it is written `ω₁`. This repository uses the following facts.

| Name | Content |
|---|---|
| `Ordinal.omega_pos 1` | $`0 \lt \omega_1`$ |
| `(isSuccLimit_omega 1).add_one_lt` | $`\alpha \lt \omega_1 \implies \alpha + 1 \lt \omega_1`$ |
| `Por.Supply.countable_iio_ordinal` | $`a \lt \omega_1 \implies \{\beta \mid \beta \lt a\}`$ is countable |

`countable_iio_ordinal` follows from the fact that the cardinality of $`\{\beta \mid \beta \lt a\}`$ is the cardinality of $`a`$ (`Cardinal.mk_Iio_ordinal`) and that $`a \lt \omega_1`$ implies that this cardinality is at most $`\aleph_0`$.

## 5. Regularity of ω₁

**Theorem (regularity of ω₁).** Let $`I`$ be a countable index set and $`\alpha_i \lt \omega_1`$ for each $`i \in I`$. Then:

```math
\sup_{i \in I} \alpha_i \lt \omega_1
```

**Proof.** Put $`\sigma := \sup_i \alpha_i`$. If $`\beta \lt \sigma`$, then $`\beta \lt \alpha_i`$ for some $`i`$. Hence

```math
\{\beta \mid \beta \lt \sigma\} = \bigcup_{i \in I} \{\beta \mid \beta \lt \alpha_i\}
```

The right side is a countable union of countable sets. Terms with $`\alpha_i = 0`$ add nothing, so drop them. For each remaining $`i`$ choose a surjection $`e_i : \mathbb N \to \alpha_i`$. Enumerating $`I`$ by $`\mathbb N`$, the map $`(n, t) \mapsto e_{i_n}(t)`$ is a surjection from $`\mathbb N \times \mathbb N`$ onto the union. $`\mathbb N \times \mathbb N`$ is countable, so the union is countable. Hence $`\sigma`$ is countable and $`\sigma \lt \omega_1`$. $`\square`$

- Choosing countably many surjections $`e_i`$ at once uses the axiom of choice (countable choice).
- It fails for an uncountable index set. For example, $`\sup_{\alpha \lt \omega_1} \alpha = \omega_1`$.

In Lean this is `Ordinal.iSup_lt_omega_one`. The index type must have a `Countable` instance. This repository uses it in three places (all in [Por/Supply.lean](../../Por/Supply.lean)).

| Place | Index type | What the supremum is taken of |
|---|---|---|
| `wh_lt` | `Fin φ.n` | the heights of one tuple of witnesses |
| `nextO_lt` | `Input S γ` (§7) | heights of witnesses |
| `lam_lt` | `ℕ` | the closure tower |

## 6. The label type

**Definition (label).** A label is an ordinal at most $`\omega_1`$.

```math
\mathrm{Label} = \{\, o \mid o \le \omega_1 \,\}, \qquad \mathrm{top} = \omega_1
```

In Lean these are `Por.Supply.Label := {o : Ordinal.{0} // o ≤ ω₁}` and `Por.Supply.top`. `OmegaY.Reflection.OrdinalSupply.Label` and `OmegaY.Model.Label` are other names for the same type. The order is the restriction of the order of ordinals, and it is a well-order.

| Name | Content |
|---|---|
| `Por.Supply.zeroL` | the label $`0`$ |
| `Por.Supply.zeroL_lt_top` | $`0 \lt \omega_1`$ |
| `Por.Supply.le_topL` | every label $`x`$ satisfies $`x \le \omega_1`$ |
| `Por.Supply.countable_iio` | for a label $`a \lt \omega_1`$, the set of labels below $`a`$ is countable |
| `OrdinalSupply.bot_lt_top` | the least label $`\bot = 0`$ satisfies $`\bot \lt \omega_1`$ |

**Why ω₁ itself is a label.** Every label of a representation lies below $`\omega_1`$ (`KeyRepresentation.bounded` in [06](06-combinatorial-layer.md)). On the other hand, the semantic layer uses relations "with top $`\omega_1`$", $`R(\kappa, x, \omega_1)`$ (Good in [08](08-closure-chain.md), `top_abs` in [09](09-obligations.md)). For this, $`\omega_1`$ is an element of the same type.

## 7. Counting parameters

In [08](08-closure-chain.md) we take a supremum over "all formulas with parameters below $`\gamma`$". The index type is chosen as follows.

**Definition (`Input`).**

```math
\mathrm{Input}(\gamma) = \sum_{\varphi \in \mathrm{Form}} \bigl(\mathrm{Fin}\ n_\varphi \to \mathrm{Option}\{\, x \mid x \lt \gamma \,\}\bigr)
```

Each position gets a label below $`\gamma`$ or nothing (`none`). `toP` turns an input into a tuple of labels, replacing `none` by $`0`$.

**Theorem (`input_countable`).** If $`\gamma \lt \omega_1`$, then `Input S γ` is countable.

**Proof.** The type of formulas `Form S` is countable ([08](08-closure-chain.md) §2). The set of labels below $`\gamma`$ is countable (`countable_iio`). Functions on a finite type into a countable type, `Option`, and dependent sums of countable types are countable. $`\square`$

**Example.** Let $`\gamma = \omega + 1`$. For a formula $`\varphi`$ in 3 variables whose positions 0 and 2 are parameters, the parameters $`(3, \cdot, \omega)`$ are given by the input $`(\varphi, (\mathrm{some}\ 3, \mathrm{none}, \mathrm{some}\ \omega))`$.

The 1-Y version enumerated the points below $`\gamma`$ by lists of natural numbers, so that the index type did not depend on $`\gamma`$. This repository uses the points themselves as indices. The index type depends on $`\gamma`$, but it is countable, so the theorem of §5 applies directly.

## 8. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "The relation R", "Proofs of the three theorems" | labels are ordinals at most $`\omega_1`$; Good points are cofinal in $`\omega_1`$ |
| [notes/01-design.md](../../notes/01-design.md) §3.3 | closed points, countably many formulas, $`\omega`$ iterations |
| [Por/Supply.lean](../../Por/Supply.lean) | all of §4–§7 |
| [OmegaY/Reflection/OrdinalSupply.lean](../../OmegaY/Reflection/OrdinalSupply.lean) | `Label`, `top`, `OrderBot`, `bot_lt_top` |

## 9. Lean correspondence

| Concept | Lean | File |
|---|---|---|
| type of ordinals | `Ordinal.{0}` | Mathlib |
| $`\lt`$ is well-founded | `wellFounded_lt` | Mathlib |
| supremum | `iSup` (`⨆`), `Ordinal.lt_iSup_add_one` | Mathlib |
| $`\omega_1`$ | `ω₁`, `Ordinal.omega_pos 1`, `isSuccLimit_omega 1` | Mathlib |
| regularity | `Ordinal.iSup_lt_omega_one` | Mathlib |
| below a countable ordinal is countable | `countable_iio_ordinal`, `countable_iio` | [Por/Supply.lean](../../Por/Supply.lean) |
| labels and top | `Label`, `top`, `zeroL`, `zeroL_lt_top`, `le_topL` | same |
| other names of the label type | `OrdinalSupply.Label`, `OrdinalSupply.top`, `bot_lt_top`, `Model.Label` | [OmegaY/Reflection/OrdinalSupply.lean](../../OmegaY/Reflection/OrdinalSupply.lean), [OmegaY/Model.lean](../../OmegaY/Model.lean) |
| inputs of parameters | `Input`, `toP`, `input_countable` | [Por/Supply.lean](../../Por/Supply.lean) |
