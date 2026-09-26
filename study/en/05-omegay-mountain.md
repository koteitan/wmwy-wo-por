[← Back](README.md) | [English](05-omegay-mountain.md) | [Japanese](../05-omegay-mountain.md)

# The ω-Y sequence and its mountain

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | ordinals, Cantor normal form of ordinals below $`\omega^\omega`$, the 1-Y version |
| [02 Well-founded relations and well-founded recursion](02-well-founded.md) | well-founded, the lexicographic order is not well-founded |

This note explains the definitions of weak-magma ω-Y sequences and their expansion. The definitions are Phyrion's ([Phyrion1343/omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean)), and this repository uses its Lean definitions unchanged (§9). The parts that are the same as for 1-Y sequences ([1-Y version, study/05](https://github.com/koteitan/1y-wo-por/blob/main/study/en/05-1y-mountain.md)) are written with the same sentences and formulas as in the 1-Y version. The differences are that rows are ordinals (§2), the way the parent is found (§3), and the way the mountain is copied (step 1 of §4).

The values in the examples were computed by a Python program that transcribes the formulas of this note literally (2026-09-27). Its results were compared with those of Phyrion's JavaScript reference implementation ([reference/engine.js](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean/blob/main/reference/engine.js)) ("Check of the formulas" in §4). The comparisons with 1-Y in §3 and §4 were computed with the reference implementation with added logging and a Python program that follows the definitions of the 1-Y version (2026-09-26).

## 1. Expressions

**Definition (expression).** An **expression** is a finite sequence of positive integers $`s = (s_0, \ldots, s_{n-1})`$ ($`n \in \mathbb N`$) that is empty or has $`s_0 = 1`$.

- Positions are counted from 0. Entry $`i`$ is called "column $`i`$".
- A **seed** is an expression $`(1, m)`$ with an integer $`m \ge 2`$. An expression need not be obtainable from a seed by expansions (§4). In the 1-Y version $`m \ge 1`$.
- Expressions are ordered by the lexicographic order $`\lt_{\mathrm{lex}}`$. A proper prefix is smaller. As in [02](02-well-founded.md) §1, this order is not well-founded on all expressions.

## 2. Rows

The rows of the ω-Y mountain are not natural numbers but ordinals below $`\omega^\omega`$. This section is not in the 1-Y version.

**Definition (row).** A **row** is an ordinal below $`\omega^\omega`$. We write a row $`a`$ in Cantor normal form as below and call $`c_i(a)`$ the **coefficients** of $`a`$ ($`c_i(a) = 0`$ for $`i \gt d`$).

```math
a = \omega^{d} c_d(a) + \cdots + \omega^{2} c_2(a) + \omega\, c_1(a) + c_0(a)
```

Rows are ordered as ordinals. In terms of coefficients:

```math
a \lt b \iff \exists i\ \bigl(c_i(a) \lt c_i(b) \ \wedge\ \forall j \gt i\ \ c_j(a) = c_j(b)\bigr)
```

| Row | Coefficients $`(c_0, c_1, c_2)`$ |
|---|---|
| $`1`$ | $`(1, 0, 0)`$ |
| $`2`$ | $`(2, 0, 0)`$ |
| $`\omega`$ | $`(0, 1, 0)`$ |
| $`\omega + 1`$ | $`(1, 1, 0)`$ |
| $`\omega \cdot 2`$ | $`(0, 2, 0)`$ |
| $`\omega^2`$ | $`(0, 0, 1)`$ |

**Definition (jump).** The **jump** of two rows $`a, b`$ is defined by

```math
\mathrm{jump}(a, b) = \begin{cases} 0 & (a = b) \cr 1 + \max\{\, i \mid c_i(a) \ne c_i(b) \,\} & (a \ne b) \end{cases}
```

**Definition (adding a power of ω).** For a row $`a`$ and a natural number $`e`$, $`a + \omega^e`$ is the ordinal sum. In terms of coefficients:

```math
c_i(a + \omega^e) = \begin{cases} 0 & (i \lt e) \cr c_e(a) + 1 & (i = e) \cr c_i(a) & (i \gt e) \end{cases}
```

We have $`a \lt a + \omega^e`$ and $`\mathrm{jump}(a, a + \omega^e) = e + 1`$.

**Definition (next row).** Let $`B(a, b) := a + \omega^{\mathrm{jump}(a, b)}`$.

| $`a`$ | $`b`$ | $`\mathrm{jump}(a, b)`$ | $`B(a, b)`$ |
|---|---|---|---|
| $`1`$ | $`1`$ | $`0`$ | $`2`$ |
| $`2`$ | $`2`$ | $`0`$ | $`3`$ |
| $`2`$ | $`1`$ | $`1`$ | $`2 + \omega = \omega`$ |
| $`\omega`$ | $`1`$ | $`2`$ | $`\omega + \omega^2 = \omega^2`$ |
| $`\omega`$ | $`\omega`$ | $`0`$ | $`\omega + 1`$ |
| $`\omega + 1`$ | $`\omega`$ | $`1`$ | $`\omega \cdot 2`$ |

If $`a = b`$ then $`B(a, b) = a + 1`$, and the row goes up by one. This is the same as the movement of rows in the mountain of the 1-Y sequence (the sequence treated by the 1-Y version in [01](01-ordinals.md) §7). If $`a \ne b`$, the row jumps by a power of $`\omega`$.

**Definition (layer).** The **layer** of a row $`a \ge 1`$ is $`\mathrm{lay}(a) := \max\{\, i \mid c_i(a) \ne 0 \,\}`$. $`\mathrm{lay}(a) = k`$ is the same as $`\omega^k \le a \lt \omega^{k+1}`$.

## 3. The mountain

From an expression $`s`$ we build, for each column, a finite set of rows and a value and a parent for each row. This table is the **mountain** $`M(s)`$ of $`s`$. We write $`\mathrm{rows}(c)`$ for the set of rows of column $`c`$; it is a finite set of rows containing 0 and 1. We write $`v_a(c)`$ for the value and $`\mathrm{par}_a(c)`$ for the parent of column $`c`$ in row $`a \in \mathrm{rows}(c)`$.

- A pair $`(c, a)`$ with $`a \in \mathrm{rows}(c)`$ is a **node**. For a node $`u = (c, a)`$ we write $`\mathrm{col}(u) := c`$, $`\mathrm{row}(u) := a`$, $`v(u) := v_a(c)`$.
- A node $`(c, 0)`$ in row 0 is a **phantom** (a placeholder node). A node in row 1 is a **bottom node**. Row 1 corresponds to row 0 of 1-Y.
- In column $`c`$, $`a^{+} := \min\{\, b \in \mathrm{rows}(c) \mid b \gt a \,\}`$ is the row directly above $`a`$, and $`a^{-} := \max\{\, b \in \mathrm{rows}(c) \mid b \lt a \,\}`$ the row directly below. $`\mathrm{top}(c) := \max \mathrm{rows}(c)`$ is the top row.
- The parent $`\mathrm{par}_a(c)`$ of a row $`a \lt \mathrm{top}(c)`$ is a node of a column to the left. The **left leg** of the node in a row $`b \ge 1`$ is $`\lambda(c, b) := \mathrm{par}_{b^{-}}(c)`$ ($`(c, b) \ne (0, 1)`$).

**Definition (mountain).** For columns $`c = 0, 1, \ldots`$ in order, $`\mathrm{rows}(c)`$, the values and the parents are given by the following formulas.

- Row 0: $`v_0(c) := 0`$. If $`c \ge 1`$, $`\mathrm{par}_0(c) := (c - 1, 0)`$.
- Row 1: $`v_1(c) := s_c`$.
- If $`a \ge 1`$ and $`v_a(c) \gt 1`$, the parent $`\pi := \mathrm{par}_a(c)`$ is found by "finding the parent" below, and the next row and its value are

```math
a^{+} := B(a, \mathrm{row}(\pi)), \qquad v_{a^{+}}(c) := v_a(c) - v(\pi)
```

- $`\mathrm{rows}(c)`$ consists of row 0, row 1 and the rows made by this rule. The row $`a`$ with $`v_a(c) = 1`$ is $`\mathrm{top}(c)`$, and it has no parent.

The second formula has the same form as the 1-Y "difference" $`v_{r+1}(c) = v_r(c) - v_r(p)`$. Values strictly decrease upward, so $`\mathrm{rows}(c)`$ is finite.

**Definition (finding the parent).** For a node $`\nu = (c', b)`$ in a row $`b \ge 1`$, with $`\lambda(\nu) = (p, e)`$, let

```math
\mathrm{next}(\nu) := \bigl(p,\ \max(\{e\} \cup \{\, a \in \mathrm{rows}(p) \mid a \le b \,\})\bigr)
```

It is the node reached from the left leg of $`\nu`$ by climbing column $`p`$ as high as possible within rows at most $`b`$. The parent of a node $`u = (c, a)`$ with $`v_a(c) \gt 1`$ is

```math
\mathrm{par}_a(c) := \mathrm{next}^{j}(u), \qquad j := \min\{\, j \ge 1 \mid 0 \lt v(\mathrm{next}^{j}(u)) \lt v_a(c) \,\}
```

This has the same form as the 1-Y "parent in row $`r+1`$" (the largest ancestor $`p`$ with $`0 \lt v(p) \lt v(c)`$): it follows the ancestors from the right and takes the first one that satisfies the condition. In ω-Y the columns followed are determined by the left legs and the climbing.

$`j`$ always exists. $`\mathrm{next}`$ strictly decreases the column, and the row stays at least 1. When column 0 is reached, the node is $`(0, 1)`$, and $`v(0, 1) = s_0 = 1 \lt v_a(c)`$.

**Property (parent in row 1).** If $`s_c \gt 1`$, then $`\mathrm{par}_1(c) = (p, 1)`$, where $`p`$ is the largest $`p`$ with $`p \lt c`$ and $`s_p \lt s_c`$. This is the same as the 1-Y parent in row 0 (1-Y version, §2).

Proof. $`\lambda(c', 1) = (c' - 1, 0)`$, and the largest row of $`\mathrm{rows}(c' - 1)`$ that is at most 1 is 1. So $`\mathrm{next}(c', 1) = (c' - 1, 1)`$. Repeating $`\mathrm{next}`$ from $`(c, 1)`$ visits $`(c-1, 1), (c-2, 1), \ldots`$ in order, with values $`s_{c-1}, s_{c-2}, \ldots`$, all greater than 0. ∎

**Definition (edge).** For a row $`1 \le a \lt \mathrm{top}(c)`$ there is a **parent–child edge** (or just **edge**) from the node $`(c, a)`$ to $`(c, a^{+})`$. $`(c, a)`$ is the **lower node**, $`(c, a^{+})`$ the **upper node**, and $`\mathrm{par}_a(c)`$ the **parent** of the edge. The parent is always in a column to the left.

- The **degree** of the edge is $`\delta_c(a) := \mathrm{jump}(a, \mathrm{row}(\mathrm{par}_a(c)))`$. We have $`a^{+} = a + \omega^{\delta_c(a)}`$. For row 0 we also set $`\delta_c(0) := 0`$ ($`0^{+} = 1 = 0 + \omega^0`$).
- The **layer** of the edge is the layer $`\mathrm{lay}(a^{+})`$ of the row of the upper node.
- The step from a phantom to the bottom node is not called an edge.

**Example ($`(1, 4, 20)`$).** In the table, "$`v \leftarrow (p, e)`$" means value $`v`$ with left leg (the parent of the edge below) the node $`(p, e)`$. The left leg of a bottom node (the phantom of the column to the left) is not written. The ω-Y mountain has no stack of layers as in 1-Y; it is a single table.

| row | column 0 | column 1 | column 2 |
|---|---|---|---|
| $`\omega^2 \cdot 2`$ | | | $`1 \leftarrow (1, \omega^2)`$ |
| $`\omega^2 + \omega`$ | | | $`2 \leftarrow (1, \omega^2)`$ |
| $`\omega^2 + 1`$ | | | $`3 \leftarrow (1, \omega^2)`$ |
| $`\omega^2`$ | | $`1 \leftarrow (0, 1)`$ | $`4 \leftarrow (1, \omega)`$ |
| $`\omega \cdot 2`$ | | | $`6 \leftarrow (1, \omega)`$ |
| $`\omega + 1`$ | | | $`8 \leftarrow (1, \omega)`$ |
| $`\omega`$ | | $`2 \leftarrow (0, 1)`$ | $`10 \leftarrow (1, 2)`$ |
| $`3`$ | | | $`13 \leftarrow (1, 2)`$ |
| $`2`$ | | $`3 \leftarrow (0, 1)`$ | $`16 \leftarrow (1, 1)`$ |
| $`1`$ | $`1`$ | $`4`$ | $`20`$ |
| $`0`$ | phantom | phantom | phantom |

- Column 0: $`v_1(0) = 1`$, so $`\mathrm{rows}(0) = \{0, 1\}`$.
- Column 1: $`\mathrm{par}_1(1) = (0, 1)`$ (value $`1 \lt 4`$), $`2 = B(1, 1)`$, value $`4 - 1 = 3`$. In row 2, $`\mathrm{next}(1, 2) = (0, \max(\{1\} \cup \{0, 1\})) = (0, 1)`$, and the parent is again $`(0, 1)`$. $`B(2, 1) = 2 + \omega = \omega`$ (jump 1), value 2. In the same way $`B(\omega, 1) = \omega + \omega^2 = \omega^2`$ (jump 2), value 1, and the column ends.
- Column 2: at every node $`j = 1`$, that is, $`\mathrm{next}(u)`$ itself is the parent. The table below lists, from the bottom node up, $`\mathrm{next}(u)`$ and the next row and value.

| node $`u`$ (row, value) | $`\lambda(u)`$ | $`\mathrm{next}(u)`$ and its value | next row $`B`$ | next value |
|---|---|---|---|---|
| $`1`$, 20 | $`(1, 0)`$ | $`(1, 1)`$, 4 | $`B(1, 1) = 2`$ (jump 0) | $`20 - 4 = 16`$ |
| $`2`$, 16 | $`(1, 1)`$ | $`(1, 2)`$, 3 (does not climb to row $`\omega \gt 2`$) | $`B(2, 2) = 3`$ (jump 0) | $`16 - 3 = 13`$ |
| $`3`$, 13 | $`(1, 2)`$ | $`(1, 2)`$, 3 | $`B(3, 2) = 3 + \omega = \omega`$ (jump 1) | $`13 - 3 = 10`$ |
| $`\omega`$, 10 | $`(1, 2)`$ | $`(1, \omega)`$, 2 | $`B(\omega, \omega) = \omega + 1`$ (jump 0) | $`10 - 2 = 8`$ |
| $`\omega + 1`$, 8 | $`(1, \omega)`$ | $`(1, \omega)`$, 2 | $`B(\omega + 1, \omega) = \omega \cdot 2`$ (jump 1) | $`8 - 2 = 6`$ |
| $`\omega \cdot 2`$, 6 | $`(1, \omega)`$ | $`(1, \omega)`$, 2 | $`B(\omega \cdot 2, \omega) = \omega^2`$ (jump 2) | $`6 - 2 = 4`$ |
| $`\omega^2`$, 4 | $`(1, \omega)`$ | $`(1, \omega^2)`$, 1 | $`B(\omega^2, \omega^2) = \omega^2 + 1`$ (jump 0) | $`4 - 1 = 3`$ |
| $`\omega^2 + 1`$, 3 | $`(1, \omega^2)`$ | $`(1, \omega^2)`$, 1 | $`B(\omega^2 + 1, \omega^2) = \omega^2 + \omega`$ (jump 1) | $`3 - 1 = 2`$ |
| $`\omega^2 + \omega`$, 2 | $`(1, \omega^2)`$ | $`(1, \omega^2)`$, 1 | $`B(\omega^2 + \omega, \omega^2) = \omega^2 \cdot 2`$ (jump 2) | $`2 - 1 = 1`$ |

The parents of column 2 run through the nodes of column 1 from the bottom. The first node after a change of parent is in the same row as the parent, with jump 0. While the parent stays the same, the jump grows to 1, then 2. When the new row reaches the row of the next node of column 1 (rows $`\omega`$ and $`\omega^2`$), $`\mathrm{next}`$ climbs to that node and the parent changes.

The edges of column 1 go up to rows 2, $`\omega`$, $`\omega^2`$ from the bottom, so their layers are 0, 1, 2.

**Correspondence with the 1-Y mountain.** The 1-Y mountain (1-Y version, §2–§4) is a stack of the mountains of layers $`0, 1, 2, \ldots`$. The top value of layer $`k`$ is the value of row 0 of layer $`k + 1`$. So line up the values of column $`c`$ of 1-Y in one sequence: layer 0 from row 0 to the top, then layer 1 from row 1 to the top, then layer 2 from row 1 to the top, and so on (the top of layer $`k`$ and row 0 of layer $`k + 1`$ count as one entry). Neighbours in this sequence are joined by 1-Y parent–child edges. In the range checked by computer, the following two facts held.

1. Reading the values $`v_a(c)`$ ($`a \ge 1`$) of column $`c`$ of $`M(s)`$ from the bottom gives the sequence of column $`c`$ of 1-Y.
2. The edge of $`M(s)`$ that corresponds to the 1-Y edge of layer $`k`$ and row $`r`$ with parent column $`p`$ has layer $`k`$. Its parent is a node of column $`p`$ at the same position (layer $`k`$, row $`r`$) in the sequence of column $`p`$.

So in this range the ω-Y mountain is the 1-Y layers joined into one column per column, and the layer of an edge stands for the 1-Y layer. The height $`h_k(c)`$ of column $`c`$ in layer $`k`$ of 1-Y is the number of edges of layer $`k`$ in column $`c`$ of $`M(s)`$.

The range checked is the 40850 expressions of length at most 6 whose last entry is not 1 and that are reached from the seeds $`(1, 2)`$, $`(1, 3)`$, $`(1, 4)`$ by repeatedly taking 1-Y expansions ($`N = 1, 2, 3`$) and prefixes (2026-09-26). Among their mountains, only that of $`(1, 4)`$ has a row $`\omega^2`$ or larger. Outside this range the facts can fail. In $`(1, 4, 15)`$, reached by 1-Y from the seed $`(1, 5)`$, the values and parents agree, but the top edge of column 2 is in layer 2 in 1-Y, while in ω-Y it is the edge to row $`\omega \cdot 2`$, in layer 1. In $`(1, 4, 16)`$ the parent of the top edge of column 2 is column 1 in 1-Y and column 0 in ω-Y, so even the parents differ. Both mountains have a row $`\omega^2`$ or larger. This is not a proof, and it is not shown in Lean.

## 4. Expansion

**Definition (root).** Let $`x := n - 1`$ be the last column. If in some row $`a`$ the column $`x`$ has a parent $`\pi = \mathrm{par}_a(x)`$ with $`v_a(x) = v(\pi) + 1`$, then $`\pi`$ is the **root**.

- There is at most one such $`a`$, and $`a^{+} = \mathrm{top}(x)`$: indeed $`v_{a^{+}}(x) = v_a(x) - v(\pi) = 1`$, and value 1 occurs only in the top row. So the root is the parent of the top edge of column $`x`$.
- If $`s_x \gt 1`$, a root exists (column $`x`$ has edges, and its top edge satisfies the condition). If $`s_x = 1`$, column $`x`$ has no edge and there is no root.
- We write the root as $`(z, d)`$: $`z`$ is the root column and $`d`$ the root row. $`K := \mathrm{lay}(\mathrm{top}(x))`$ is the **root layer** (the layer of the top edge).

The bad root of 1-Y (1-Y version, §5) is defined by the same formula $`v(x) = v(p) + 1`$. For the expressions in the table below, the root column and the root layer equal the column and layer of the 1-Y bad root.

| Expression | root $`(z, d)`$ | $`\mathrm{top}(x)`$ | root layer $`K`$ | (layer, row, column) of the 1-Y bad root |
|---|---|---|---|---|
| $`(1, 2, 3)`$ | $`(1, 1)`$ | $`2`$ | 0 | $`(0, 0, 1)`$ |
| $`(1, 2, 4)`$ | $`(1, 2)`$ | $`3`$ | 0 | $`(0, 1, 1)`$ |
| $`(1, 3)`$ | $`(0, 1)`$ | $`\omega`$ | 1 | $`(1, 0, 0)`$ |
| $`(1, 2, 4, 3)`$ | $`(1, 1)`$ | $`2`$ | 0 | $`(0, 0, 1)`$ |

**Definition (expansion $`s[N]`$).** $`N \in \mathbb N`$ is the number of copies. Let $`x`$ be the last column.

- (0) No root ($`s`$ is empty or $`s_x = 1`$): delete the last column. $`s[N] = (s_0, \ldots, s_{x-1})`$. For the empty expression $`s[N] = ()`$.
- Root $`(z, d)`$: let $`L := x - z`$, and build the expression $`s[N]`$ of length $`W := x + N L`$ by steps 1 and 2 below. The values are not copied directly; the mountain is copied, and the values are rebuilt from it. If $`N = 0`$, then $`W = x`$ and $`s[0] = (s_0, \ldots, s_{x-1})`$.

**Definition (block).** If there is a root $`(z, d)`$, then for $`i = 0, 1, \ldots, N`$ the columns $`z + i L`$ to $`z + (i+1) L - 1`$ of $`s[N]`$ form **block $`i`$**. Block 0 is the original columns $`z, \ldots, x - 1`$, and blocks $`1, \ldots, N`$ are its copies. Every column from $`z`$ on is written uniquely as $`c = z + i L + j`$ ($`0 \le i \le N`$, $`0 \le j \lt L`$); $`i`$ is its block number and $`j`$ its position in the block. For example, in $`(1, 2, 2)[2] = (1, 2, 1, 2, 1, 2)`$ we have $`z = 0`$, $`x = 2`$, and blocks 0, 1, 2 are the columns $`\{0, 1\}`$, $`\{2, 3\}`$, $`\{4, 5\}`$.

**Definition (source column).** For a column $`c = z + i L + j \ge x`$, the source column $`\sigma`$ and the shift count $`b`$ are: if $`j \ge 1`$, $`\sigma := z + j`$ and $`b := i`$; if $`j = 0`$, $`\sigma := x`$ and $`b := i - 1`$. Then $`c = \sigma + b L`$. Column $`c = x`$ has $`\sigma = x`$, $`b = 0`$. The 1-Y version uses this $`\sigma, b`$ only in branch (3-2) of §6; ω-Y uses it in all layers.

**Definition (shift).** For $`i \in \mathbb N`$ and a column $`p`$, let $`m_i(p) := p`$ if $`p \lt z`$, and $`m_i(p) := p + i L`$ if $`p \ge z`$. It moves a column of block 0 to the same position in block $`i`$.

The following definitions exist only in ω-Y.

**Definition (decremented mountain).** Let $`s' := (s_0, \ldots, s_{x-1}, s_x - 1)`$. We write $`\widetilde{\mathrm{rows}}(c)`$, $`\tilde v_a(c)`$, $`\widetilde{\mathrm{par}}_a(c)`$, $`\tilde\lambda(c, a)`$, $`\tilde\delta_c(a)`$, $`\widetilde{\mathrm{top}}(c)`$ for the rows, values, parents, left legs, degrees and top rows of $`M(s')`$. For a node $`u = (c, a)`$ we write $`\widetilde{\mathrm{par}}(u) := \widetilde{\mathrm{par}}_a(c)`$. The mountain of a column $`c \lt x`$ depends only on $`s_0, \ldots, s_c`$, so it is the same in $`M(s')`$ and $`M(s)`$. In particular the root $`(z, d)`$ is also a node of $`M(s')`$.

**Remark (column $`x`$).** Let the rows of column $`x`$ of $`M(s)`$ be $`0 = a_0 \lt 1 = a_1 \lt \cdots \lt a_T = \mathrm{top}(x)`$. For $`1 \le k \le T - 1`$: $`a_k \in \widetilde{\mathrm{rows}}(x)`$, $`\tilde\lambda(x, a_k) = \lambda(x, a_k)`$, and $`\tilde v_{a_k}(x) = v_{a_k}(x) - 1`$. So the edges of column $`x`$ of $`M(s)`$ below the top edge are the same in $`M(s')`$.

Proof. By induction on $`k`$. For $`k = 1`$ both are row 1 with left leg $`(x - 1, 0)`$ and values $`s_x`$ and $`s_x - 1`$. Let $`k \le T - 2`$. $`a_{k+1}`$ is not the top, so $`v_{a_{k+1}}(x) \ge 2`$. Hence $`\pi_k := \mathrm{par}_{a_k}(x)`$ has $`v(\pi_k) = v_{a_k}(x) - v_{a_{k+1}}(x) \le v_{a_k}(x) - 2`$, and $`\tilde v_{a_k}(x) = v_{a_k}(x) - 1 \ge 2`$. So $`M(s')`$ also looks for a parent of row $`a_k`$. $`\mathrm{next}`$ depends only on the row and left leg of the current node and on the columns left of $`x`$, so the sequence $`\mathrm{next}^j(x, a_k)`$ is the same in $`M(s)`$ and $`M(s')`$. A node rejected in $`M(s)`$ has value 0 or at least $`v_{a_k}(x)`$, so it is also rejected for $`\tilde v_{a_k}(x)`$. $`\pi_k`$ has $`0 \lt v(\pi_k) \lt \tilde v_{a_k}(x)`$, so it is also the parent in $`M(s')`$. Hence $`\widetilde{\mathrm{par}}_{a_k}(x) = \pi_k`$, the row directly above is the same $`a_{k+1}`$, and $`\tilde v_{a_{k+1}}(x) = v_{a_{k+1}}(x) - 1`$. For $`k = T - 1`$, $`\pi_{T-1}`$ is the root and $`v(\pi_{T-1}) = v_{a_{T-1}}(x) - 1 = \tilde v_{a_{T-1}}(x)`$, so it is not a parent in $`M(s')`$. From there up $`M(s')`$ may differ from $`M(s)`$. ∎

**Definition (boundary rows).** $`\Gamma := \{\mathrm{top}(x)\} \cup \{\, a \in \mathrm{rows}(z) \mid 1 \le a \le d \,\}`$: the top row of column $`x`$, and the rows of the root column at or below the root (without the phantom).

**Definition (marker).** A node $`\mu = (c, a)`$ of $`M(s')`$ ($`a \lt \widetilde{\mathrm{top}}(c)`$) is a **marker** if

```math
z \lt c \le x \ \wedge\ a \le d \ \wedge\ \exists m \ge 1\ \Bigl(\mathrm{col}\bigl(\widetilde{\mathrm{par}}^{m}(\mu)\bigr) = z \ \wedge\ \forall i \in \{1, \ldots, m\}\ \ \mathrm{row}\bigl(\widetilde{\mathrm{par}}^{i}(\mu)\bigr) = a\Bigr)
```

that is, following parents within the same row reaches the node $`(z, a)`$ of the root column at or below the root. We write $`\mathrm{Mk}`$ for the set of markers and $`\mathrm{Mk}(\sigma)`$ for the markers in column $`\sigma`$.

- Every phantom $`(c, 0)`$ with $`z \lt c \le x`$ is a marker ($`\widetilde{\mathrm{par}}_0(c) = (c - 1, 0)`$).
- The parent $`\widetilde{\mathrm{par}}(\mu)`$ of a marker $`\mu`$ is a marker or a node of column $`z`$. So $`\mathrm{col}(\widetilde{\mathrm{par}}(\mu)) \ge z`$.

**Definition (reference rows).** For $`b \ge 1`$, using column $`x + (b - 1) L`$ (column $`x`$ of $`M(s')`$ when $`b = 1`$, and the first column $`z + bL`$ of block $`b`$ when $`b \ge 2`$), let

```math
\beta_b(\gamma) := \max\{\, e \in \mathrm{rows}'(x + (b - 1) L) \mid e \lt \gamma \,\} \quad (\gamma \in \Gamma), \qquad g_b(a) := \min\{\, \beta_b(\gamma) \mid \gamma \in \Gamma,\ \beta_b(\gamma) \ge a \,\}
```

$`\mathrm{rows}'`$ is the set of rows of the new mountain built in step 1 below. Column $`x + (b-1)L`$ is left of the column $`c = \sigma + bL \gt x`$, so it is already built.

**Definition (copied left leg).** For a node $`\nu`$ and a row $`\gamma`$, let

```math
\mathrm{tr}_b(\nu, \gamma) := \begin{cases} \nu & (\mathrm{col}(\nu) \lt z) \cr \bigl(m_b(\mathrm{col}(\nu)),\ \max\{\, e \in \mathrm{rows}'(m_b(\mathrm{col}(\nu))) \mid e \lt \gamma \,\}\bigr) & (\mathrm{col}(\nu) \ge z) \end{cases}
```

A node left of the root column is used as is. Otherwise the highest node below row $`\gamma`$ in the shifted column is used.

**Step 1 (copy the mountain).** For each column $`c \lt W`$ of $`s[N]`$, in increasing order of $`c`$, the set of rows $`\mathrm{rows}'(c)`$ and the left legs $`\lambda'(c, e)`$ of the rows $`e \ge 1`$ are defined as follows. The parents are, as in §3, $`\mathrm{par}'_a(c) := \lambda'(c, a^{+})`$, where $`a^{+}`$ is the row directly above in $`\mathrm{rows}'(c)`$.

- Column $`c \le x`$: as column $`c`$ of $`M(s')`$. $`\mathrm{rows}'(c) := \widetilde{\mathrm{rows}}(c)`$, $`\lambda'(c, e) := \tilde\lambda(c, e)`$. For $`c \lt x`$ this is also column $`c`$ of $`M(s)`$.
- Column $`c \gt x`$ ($`c = \sigma + bL`$, $`b \ge 1`$): for each marker $`\mu = (\sigma, a)`$ in $`\mathrm{Mk}(\sigma)`$, place the following three kinds of nodes. $`\mathrm{rows}'(c)`$ is the set of all rows of the placed nodes.
  - **(T) translation**: place a node in row $`a`$. If $`a \ge 1`$, $`\lambda'(c, a) := \mathrm{tr}_b(\tilde\lambda(\sigma, a), a)`$.
  - **(C) contour**: let the rows of column $`\sigma`$ of $`M(s')`$ from $`\mu`$ up be $`a_0 := a`$, $`a_{t+1} := a_t^{+}`$. Let $`t_\mu := \min\{\, t \ge 0 \mid a_t = \widetilde{\mathrm{top}}(\sigma) \ \vee\ (\sigma, a_{t+1}) \in \mathrm{Mk} \,\}`$. Define rows $`\gamma_0 := g_b(a)`$, $`\gamma_{t+1} := \gamma_t + \omega^{\tilde\delta_\sigma(a_t)}`$, and for $`1 \le t \le t_\mu`$ place a node in row $`\gamma_t`$ with $`\lambda'(c, \gamma_t) := \mathrm{tr}_b(\tilde\lambda(\sigma, a_t), \gamma_t)`$.
  - **(F) fill**: let $`p := \widetilde{\mathrm{par}}(\mu)`$. For each row $`e_q \in \mathrm{rows}'(m_b(\mathrm{col}(p)))`$ with $`a \le e_q \lt g_b(a)`$, let $`q := (m_b(\mathrm{col}(p)), e_q)`$, and for $`0 \le i \le \delta'(q)`$ place a node in row $`e_q + \omega^{i}`$ with $`\lambda'(c, e_q + \omega^{i}) := q`$. Here $`\delta'(q)`$ is the degree of $`q`$ in the new mountain: $`e_q^{+} = e_q + \omega^{\delta'(q)}`$.

For an expression, the set in $`g_b(a)`$ is never empty, and the nodes placed in one column by step 1 all have different rows (shown in Lean; §9).

**Definition (source node, gap node).** The **source node** of a node $`(c, a)`$ placed by (T) is $`(\sigma, a)`$, and that of a node $`(c, \gamma_t)`$ placed by (C) is $`(\sigma, a_t)`$. If the upper node of a new edge has a source node $`(\sigma, a_s)`$, the edge of $`M(s')`$ whose upper node is $`(\sigma, a_s)`$ is the **source edge** of that edge. A node placed by (F) is a **gap node**. The source node of a node in a column $`c \le x`$ is the node itself.

**Step 2 (rebuild the values).** For each column $`c \lt W`$, let $`\mathrm{top}'(c) := \max \mathrm{rows}'(c)`$, and define the values by

```math
v'_a(c) := 1 + \sum_{e \in \mathrm{rows}'(c),\ a \le e \lt \mathrm{top}'(c)} v'(\mathrm{par}'_e(c)) \qquad (1 \le a \le \mathrm{top}'(c))
```

Parents are columns to the left, so the formula is computed from the left. Finally $`s[N] := (v'_1(0), \ldots, v'_1(W - 1))`$.

This formula is the difference $`v_{a^{+}}(c) = v_a(c) - v(\mathrm{par}_a(c))`$ of §3 run backwards: the top value is 1, and each row down adds the value of the parent. It is the formula of step 2 of §6 of the 1-Y version with top value $`t_k(c) = 1`$ and a single layer. For columns $`c \le x`$ it gives the values of $`M(s')`$.

### The branch tree

The edges that step 1 makes in the mountain of $`s[N]`$ are divided into the branches below. The numbers of the branches are the same as the branch numbers of step 1 of §6 of the 1-Y version. Branches with the same number make, in the checked range, the same edges as the same 1-Y branch ("Correspondence with the 1-Y expansion" below). Branch (4) does not exist in 1-Y. The branches do not change how edges are placed; they only number the edges placed by step 1.

Notation. An edge is represented by its upper node $`(c, a^{+})`$. $`\ell := \mathrm{lay}(a^{+})`$ is the layer of the edge. If the upper node has a source node, we write it $`(\sigma, a_s)`$ ($`a_s = a`$ for (T), $`a_s = a_t`$ for (C)). An edge with $`a^{+} = a_s`$ is **copied in the same row**. Edges from (T) and edges of column $`x`$ are always so. The set of rows of the gap nodes of column $`c`$ in layer $`\ell`$ is $`F_\ell(c) := \{\, e \in \mathrm{rows}'(c) \mid (c, e) \text{ is a gap node},\ \mathrm{lay}(e) = \ell \,\}`$.

Each branch is named by the number at its head, such as (2-3-1). In the examples below, the branches that make an edge are listed as "branches used"; the branches (1-1), (2-1), (3-1) that keep the original are not listed. "Unchanged" means $`\mathrm{rows}'(c) = \mathrm{rows}(c)`$ and $`\lambda'(c, e) = \lambda(c, e)`$.

- **(0)** No root: delete the last column (the definition above).
- **(1) Layer $`\ell \gt K`$ (above the root)**
  - (1-1) $`c \lt x`$: unchanged.
  - (1-2) $`c \ge x`$, an edge copied in the same row: the row of the upper node is $`a_s`$, the parent is $`\mathrm{tr}_b(\tilde\lambda(\sigma, a_s), a_s)`$ ($`\tilde\lambda(x, a_s)`$ for $`c = x`$).
- **(2) Layer $`\ell = K`$ (the root layer)**
  - (2-1) $`c \lt x`$: unchanged.
  - (2-2) $`c \gt x`$, $`j \ge 1`$ ($`\sigma \lt x`$), an edge copied in the same row: the row of the upper node is $`a_s`$, the parent is $`\mathrm{tr}_b(\tilde\lambda(\sigma, a_s), a_s)`$.
  - (2-3) $`c \ge x`$, $`j = 0`$ ($`\sigma = x`$, the first column of a block), an edge copied in the same row: the row of the upper node is $`a_s`$. Let $`\nu := \tilde\lambda(x, a_s)`$. The parent depends on the column of $`\nu`$.
    - (2-3-1) $`\mathrm{col}(\nu) \ge z`$: the parent is $`\bigl(m_b(\mathrm{col}(\nu)),\ \max\{\, e \in \mathrm{rows}'(m_b(\mathrm{col}(\nu))) \mid e \lt a_s \,\}\bigr)`$ ($`\nu`$ for $`c = x`$).
    - (2-3-2) $`\mathrm{col}(\nu) \lt z`$: the parent is $`\nu`$ itself.
- **(3) Layer $`\ell \lt K`$ (below the root)**
  - (3-1) $`c \lt x`$: unchanged.
  - (3-2) $`c \ge x`$. The edges of layer $`\lt K`$ of $`c = x`$ are the same as in $`M(s)`$, so unchanged (Remark (column $`x`$); in the checked range, every edge of layer $`\lt K`$ of column $`x`$ of $`M(s')`$ was below the top edge of column $`x`$ of $`M(s)`$). The edges of $`c \gt x`$ are as follows.
    - (3-2-1) $`F_\ell(c) \ne \emptyset`$:
      - (3-2-1-1) the upper node is from (T): the row of the upper node is $`a`$, the parent is $`\mathrm{tr}_b(\tilde\lambda(\sigma, a), a)`$.
      - (3-2-1-2) the upper node is from (F) with $`i = 0`$: the row of the upper node is $`e_q + 1`$, the parent is $`q`$.
      - (3-2-1-3) the upper node is from (C), not copied in the same row, with $`\mathrm{lay}(a_t) = \ell`$: the row of the upper node is $`\gamma_t`$, the parent is $`\mathrm{tr}_b(\tilde\lambda(\sigma, a_t), \gamma_t)`$.
    - (3-2-2) $`F_\ell(c) = \emptyset`$, an edge copied in the same row: the row of the upper node is $`a_s`$, the parent is $`\mathrm{tr}_b(\tilde\lambda(\sigma, a_s), a_s)`$.
- **(4) Branches not in 1-Y**
  - (4-1) the upper node is from (F) with $`i \ge 1`$: the row of the upper node is $`e_q + \omega^{i}`$, the parent is $`q`$.
  - (4-2) the upper node is from (C), not copied in the same row, with $`\mathrm{lay}(a_t) \ne \ell`$: the row of the upper node is $`\gamma_t`$, the parent is $`\mathrm{tr}_b(\tilde\lambda(\sigma, a_t), \gamma_t)`$.
  - (4-3) edges in none of (1)–(3), (4-1), (4-2). They are of three kinds: the upper node is from (F) with $`i = 0`$ and $`\ell \ge K`$; the upper node is from (C), not copied in the same row, with $`\mathrm{lay}(a_t) = \ell`$, and $`\ell \ge K`$ or $`F_\ell(c) = \emptyset`$; the upper node is from (C), copied in the same row, with $`\ell \lt K`$ and $`F_\ell(c) \ne \emptyset`$.

---

**Example 1 ($`(1)[2]`$).** An example with no root. The last column is $`x = 0`$, and $`s_0 = 1`$, so column 0 has no edge. So the last column is deleted, and $`(1)[2] = ()`$. For every $`N`$, $`(1)[N] = ()`$.

**Branches used.** (0).

---

**Example 2 ($`(1, 2, 3)[2]`$).** In the root layer, the first column of a block uses a parent left of the root column.

**Branches used.** (2-3-2): columns 2, 3 of layer 0.

1. **The original mountain.** The table is read as in the example of §3.

   | row | column 0 | column 1 | column 2 |
   |---|---|---|---|
   | $`2`$ | | $`1 \leftarrow (0, 1)`$ | $`1 \leftarrow (1, 1)`$ |
   | $`1`$ | $`1`$ | $`2`$ | $`3`$ |

2. **The root.** The last column is $`x = 2`$, and $`v_1(2) = 3 = v(1, 1) + 1`$. So the root is $`(z, d) = (1, 1)`$ and $`K = \mathrm{lay}(2) = 0`$. $`L = 1`$, $`W = 2 + 2 \cdot 1 = 4`$, and columns 2 and 3 both have $`j = 0`$. Column 2 has $`\sigma = 2`$, $`b = 0`$, and column 3 has $`\sigma = 2`$, $`b = 1`$.

3. **Copy the mountain.** $`s' = (1, 2, 2)`$, and column 2 of $`M(s')`$ has value 2 in row 1 and value $`1 \leftarrow (0, 1)`$ in row 2 ($`\mathrm{next}(2, 1) = (1, 1)`$ has value 2, which does not satisfy $`0 \lt v \lt 2`$, so it is rejected, and the next node $`(0, 1)`$ is the parent). $`\Gamma = \{2, 1\}`$. The only marker of column 2 is the phantom $`(2, 0)`$. The parent $`(0, 1)`$ of $`(2, 1)`$ skips column $`z = 1`$, so $`(2, 1)`$ is not a marker.
   - Column 2 ($`c = x`$): as column 2 of $`M(s')`$. The edge $`1 \to 2`$ has parent $`\nu = (0, 1)`$ with $`\mathrm{col}(\nu) = 0 \lt z`$, so it is (2-3-2).
   - Column 3 ($`b = 1`$): the reference column is column 2, with $`\beta_1(2) = 1`$, $`\beta_1(1) = 0`$, $`g_1(0) = 0`$. From the phantom marker, (T) places row 0, and (C) places $`\gamma_1 = 0 + \omega^0 = 1`$ and $`\gamma_2 = 1 + \omega^0 = 2`$. The left leg of row 1 is $`\mathrm{tr}_1((1, 0), 1) = (2, 0)`$, and the left leg of row 2 is $`\mathrm{tr}_1((0, 1), 2) = (0, 1)`$ (unchanged since $`0 \lt z`$). The edge $`1 \to 2`$ is copied in the same row as its source node $`(2, 2)`$, and it is (2-3-2). (F) places nothing, since no row has $`0 \le e_q \lt 0`$.

4. **Rebuild the values.** Columns 2 and 3 have 1 in row 2 and $`1 + v(0, 1) = 2`$ in row 1. So $`(1, 2, 3)[2] = (1, 2, 2, 2)`$.

---

**Example 3 ($`(1, 3, 3)[2]`$).** Gap nodes appear in a layer below the root.

**Branches used.** (2-2): columns 3, 5 of layer 1. (3-2-1-2), (3-2-1-3): columns 3, 4, 5 of layer 0.

1. **The original mountain.**

   | row | column 0 | column 1 | column 2 |
   |---|---|---|---|
   | $`\omega`$ | | $`1 \leftarrow (0, 1)`$ | $`1 \leftarrow (0, 1)`$ |
   | $`2`$ | | $`2 \leftarrow (0, 1)`$ | $`2 \leftarrow (0, 1)`$ |
   | $`1`$ | $`1`$ | $`3`$ | $`3`$ |

2. **The root.** The last column is $`x = 2`$, and $`v_2(2) = 2 = v(0, 1) + 1`$. So the root is $`(z, d) = (0, 1)`$ and $`K = \mathrm{lay}(\omega) = 1`$. $`L = 2`$, $`W = 2 + 2 \cdot 2 = 6`$, and the new columns 3, 4, 5 have $`(\sigma, b) = (1, 1)`$, $`(2, 1)`$, $`(1, 2)`$. $`\Gamma = \{\omega, 1\}`$.

3. **Copy the mountain.** $`s' = (1, 3, 2)`$, and column 2 of $`M(s')`$ has value 2 in row 1 and value $`1 \leftarrow (0, 1)`$ in row 2. The markers are, in each of columns 1 and 2, the phantom and the node in row 1 ($`\widetilde{\mathrm{par}}(1, 1) = (0, 1)`$ and $`\widetilde{\mathrm{par}}(2, 1) = (0, 1)`$, staying in row 1). The reference column of block 1 is column 2 (rows 0, 1, 2), so $`g_1(1) = \beta_1(\omega) = 2`$. The reference column of block 2 is column 4 (rows 0, 1, 2, 3), so $`g_2(1) = \beta_2(\omega) = 3`$.

   The nodes placed in column 3 ($`\sigma = 1`$, $`b = 1`$) from the marker $`\mu = (1, 1)`$ are:

   | row of the upper node | kind | parent | branch |
   |---|---|---|---|
   | $`\omega`$ | (C), $`\gamma_2 = 3 + \omega^{1}`$, source $`(1, \omega)`$ | $`\mathrm{tr}_1((0, 1), \omega) = (2, 2)`$ | (2-2) |
   | $`3`$ | (C), $`\gamma_1 = 2 + \omega^{0}`$, source $`(1, 2)`$ | $`\mathrm{tr}_1((0, 1), 3) = (2, 2)`$ | (3-2-1-3) |
   | $`2`$ | (F), $`p = (0, 1)`$, $`q = (m_1(0), 1) = (2, 1)`$, $`i = 0`$ | $`(2, 1)`$ | (3-2-1-2) |
   | $`1`$ | (T) | $`\mathrm{tr}_1((0, 0), 1) = (2, 0)`$ | (bottom node, not an edge) |

   The edge to row $`\omega`$ is copied in the same row $`\omega`$ as its source edge, in layer $`1 = K`$, with $`\sigma = 1 \lt x`$, so it is (2-2). The edge to row 3 is copied to a row different from the source row 2; its layer 0 is the same as the source's, and column 3 has a gap node in layer 0 (row 2), so it is (3-2-1-3).

   Column 4 ($`\sigma = 2`$, $`b = 1`$) gets, from $`\mu = (2, 1)`$, row 1 by (T), row $`2 + \omega^0 = 3`$ by (C) (source $`(2, 2)`$, parent $`(2, 2)`$), and row 2 by (F) (parent $`(2, 1)`$). Column 5 ($`\sigma = 1`$, $`b = 2`$) gets, starting from $`g_2(1) = 3`$, rows $`4`$ and $`4 + \omega = \omega`$ by (C) (both with parent $`(4, 3)`$), and rows 2 and 3 by (F) with parents the rows 1 and 2 of column $`m_2(0) = 4`$.

   | row | column 3 | column 4 | column 5 |
   |---|---|---|---|
   | $`\omega`$ | ← (2, 2) | | ← (4, 3) |
   | $`4`$ | | | ← (4, 3) |
   | $`3`$ | ← (2, 2) | ← (2, 2) | ← (4, 2) |
   | $`2`$ | ← (2, 1) | ← (2, 1) | ← (4, 1) |
   | $`1`$ | ← (2, 0) | ← (3, 0) | ← (4, 0) |

4. **Rebuild the values.** Column 3 has, from the top, $`1`$, $`1 + v(2, 2) = 2`$, $`2 + v(2, 2) = 3`$, $`3 + v(2, 1) = 5`$. Column 4 has 1, 2, 4 from the top, and column 5 has 1, 2, 3, 5, 9. So $`(1, 3, 3)[2] = (1, 3, 2, 5, 4, 9)`$.

   Column 5 has one more node than column 3. In the 1-Y version this is branch (3-2-1): the copy in block 2 grows by 2 rows in layer 0.

---

**Example 4 ($`(1, 4)[2]`$).** An example that uses branch (4). The result is $`(1, 3, 10)`$, which differs from $`(1, 3, 9)`$ of 1-Y.

**Branches used.** (3-2-1-2): column 2 of layer 0. (3-2-1-3), (4-1), (4-2): column 2 of layer 1.

1. **The original mountain.** Column 1 of $`M(1, 4)`$ has, like column 1 in the example of §3, the values 4, 3, 2, 1 in rows 1, 2, $`\omega`$, $`\omega^2`$, all with parent $`(0, 1)`$.
2. **The root.** The root is $`(z, d) = (0, 1)`$ and $`K = \mathrm{lay}(\omega^2) = 2`$. $`L = 1`$, $`W = 1 + 2 = 3`$, and column 2 has $`\sigma = 1`$, $`b = 1`$. $`\Gamma = \{\omega^2, 1\}`$.
3. **Copy the mountain.** $`s' = (1, 3)`$, and column 1 of $`M(s')`$ has the values 3, 2, 1 in rows 1, 2, $`\omega`$. The markers are $`(1, 0)`$ and $`(1, 1)`$. The reference column is column 1, with $`\beta_1(\omega^2) = \omega`$ and $`\beta_1(1) = 0`$, so $`g_1(1) = \omega`$. The nodes placed from $`\mu = (1, 1)`$ are:

   | row of the upper node | kind | parent | branch |
   |---|---|---|---|
   | $`\omega \cdot 2`$ | (C), $`\gamma_2 = (\omega + 1) + \omega^{1}`$, source $`(1, \omega)`$ | $`\mathrm{tr}_1((0, 1), \omega \cdot 2) = (1, \omega)`$ | (3-2-1-3) |
   | $`\omega + 1`$ | (C), $`\gamma_1 = \omega + \omega^{0}`$, source $`(1, 2)`$ | $`\mathrm{tr}_1((0, 1), \omega + 1) = (1, \omega)`$ | (4-2) |
   | $`\omega`$ | (F), $`q = (1, 2)`$, $`\delta'(q) = 1`$, $`i = 1`$ | $`(1, 2)`$ | (4-1) |
   | $`3`$ | (F), $`q = (1, 2)`$, $`i = 0`$ | $`(1, 2)`$ | (3-2-1-2) |
   | $`2`$ | (F), $`q = (1, 1)`$, $`i = 0`$ | $`(1, 1)`$ | (3-2-1-2) |
   | $`1`$ | (T) | $`\mathrm{tr}_1((0, 0), 1) = (1, 0)`$ | (bottom node) |

   The edge to row $`\omega + 1`$ moves from layer 0 of its source $`(1, 2)`$ to layer 1, so it is (4-2). The edge to row $`\omega \cdot 2`$ is in layer 1, the same as its source $`(1, \omega)`$, and column 2 has a gap node in layer 1 (row $`\omega`$), so it is (3-2-1-3).
4. **Rebuild the values.** Column 2 has, from the top, $`1`$, $`1 + v(1, \omega) = 2`$, $`2 + v(1, \omega) = 3`$, $`3 + v(1, 2) = 5`$, $`5 + v(1, 2) = 7`$, $`7 + v(1, 1) = 10`$. So $`(1, 4)[2] = (1, 3, 10)`$.

   Column 2 of 1-Y has 2 edges in layer 0 and 2 edges in layer 1, with values 9, 6, 4, 2, 1 from the bottom. Column 2 of ω-Y has 2 edges in layer 0 and 3 edges in layer 1. The extra edge is the (4-2) edge $`\omega \to \omega + 1`$, and the bottom value is larger by the value 1 of its parent ($`10 = 9 + 1`$).

### Correspondence with the 1-Y expansion

Identify the edges of ω-Y and 1-Y by "Correspondence with the 1-Y mountain" in §3. Then the words of the expansion correspond as follows. The 1-Y symbols are those of §3–§6 of the 1-Y version. Symbols used by both ($`z`$, $`K`$, $`L`$, $`W`$, blocks, $`\sigma`$, $`b`$, $`m_i`$) have the same meaning.

| 1-Y | ω-Y |
|---|---|
| the edge of column $`c`$ in layer $`k`$ from row $`r`$ to $`r + 1`$ | the $`(r + 1)`$-th edge from the bottom among the edges of column $`c`$ in layer $`k`$ |
| height $`h_k(c)`$ | the number of edges of column $`c`$ in layer $`k`$ |
| parent $`\mathrm{par}_{k,r}(c)`$ | the column of the parent of that edge |
| column $`z`$ and layer $`K`$ of the bad root | the root column $`z`$ and the root layer $`K`$ |
| row $`d`$ of the bad root | the number of edges of layer $`K`$ in column $`z`$ below the root (not the root row $`d`$ of ω-Y) |
| column $`x`$ ($`i = 1`$, $`j = 0`$) | column $`x`$ of $`M(s')`$ ($`b = 0`$) |
| column $`z + i L + j \gt x`$ | column $`\sigma + bL`$ made by (T), (C), (F) from the markers of column $`\sigma`$ |
| in a layer $`k \lt K`$, $`\sigma`$ lies above $`z`$ | $`F_k(c) \ne \emptyset`$ |

Branches with the same number do the same thing, as follows. The minimal example is the lexicographically smallest expression, in the checked range, that passes the branch with $`N = 2`$.

| Branch | What 1-Y does | What ω-Y does | Minimal example |
|---|---|---|---|
| (0) | no bad root; delete the last column | no root; delete the last column | $`(1)`$ |
| (1-1), (2-1), (3-1) | unchanged | columns $`\lt x`$ unchanged | |
| (1-2) | layer $`\gt K`$; copy column $`z + j`$ shifted $`i`$ times | layer $`\gt K`$; column $`x`$ is the decremented mountain, the others are copied in the same row | $`(1, 3, 2)`$ |
| (2-2) | layer $`K`$, $`j \ge 1`$; copy shifted | layer $`K`$, $`j \ge 1`$; copy in the same row | $`(1, 2, 2)`$ |
| (2-3-1) | layer $`K`$, $`j = 0`$, row $`\lt d`$; the parent of $`x`$ shifted $`i - 1`$ times | layer $`K`$, $`j = 0`$; $`\mathrm{col}(\nu) \ge z`$, the parent shifted $`b = i - 1`$ times | $`(1, 2, 4)`$ |
| (2-3-2) | layer $`K`$, $`j = 0`$, row $`\ge d`$; the parent of $`z`$ used as is | layer $`K`$, $`j = 0`$; $`\mathrm{col}(\nu) \lt z`$, the parent used as is | $`(1, 2, 3)`$ |
| (3-2-1-1) | layer $`\lt K`$, above $`z`$, row $`\lt f`$; copy shifted | layer $`\lt K`$, $`F_\ell(c) \ne \emptyset`$; edges from (T) | $`(1, 3, 2, 5)`$ |
| (3-2-1-2) | stretch by $`b e`$ rows from row $`f`$; the parent is $`\mathrm{par}_{k,f}(\sigma) + b L`$ | edges from (F) with $`i = 0`$; the parent is $`q`$ in column $`m_b(\mathrm{col}(p))`$ | $`(1, 3)`$ |
| (3-2-1-3) | row $`\ge f + b e`$; copy lifted by $`b e`$ rows | edges from (C) whose row is raised, in the same layer | $`(1, 3)`$ |
| (3-2-2) | layer $`\lt K`$, not above $`z`$; copy shifted | layer $`\lt K`$, $`F_\ell(c) = \emptyset`$; copy in the same row | $`(1, 3, 4, 2, 5, 6, 5)`$ |
| (4-1) | none | edges from (F) with $`i \ge 1`$ | $`(1, 4)`$ |
| (4-2) | none | edges from (C) whose layer differs from the source edge | $`(1, 4)`$ |
| (4-3) | none | none of (1)–(3), (4-1), (4-2) | $`(1, 3, 10)`$ |

"The parent is in one column" in 1-Y branch (3-2-1-2) corresponds to the weak-magma rule "the parents of the gap nodes all lie in one column $`m_b(\mathrm{col}(p))`$" (§5). 1-Y branches (3-2-1-1) and (3-2-2) both copy with a shift and without changing the row. In ω-Y both become copies in the same row, and the only difference is whether $`F_\ell(c)`$ is empty.

**Checked range (comparison with 1-Y).** The following was checked by computer (2026-09-26). It is not a proof, and it is not shown in Lean.

- For the same 40850 expressions as in §3, of the 122550 expansions with $`N = 1, 2, 3`$, the 122548 other than $`(1, 4)[2]`$ and $`(1, 4)[3]`$ give the same values in ω-Y and 1-Y. In these, the mountain of $`s[N]`$ also has, under the correspondence of §3, the same values and parents as the copied 1-Y mountain (1-Y version, §6, step 1), and the layers of the edges equal the 1-Y layers. For all edges of columns $`x`$ and beyond (about 4.33 million), the number in the branch tree equals the 1-Y branch number. Branch (4) did not occur.
- $`(1, 4)[2]`$ and $`(1, 4)[3]`$ give different values (ω-Y: $`(1, 3, 10)`$, $`(1, 3, 10, 37)`$; 1-Y: $`(1, 3, 9)`$, $`(1, 3, 9, 27)`$). Both pass (4-1) and (4-2).
- For the 3542 expressions of length at most 5 reached from the same seeds by ω-Y expansions (10626 expansions), too, the values differ from 1-Y only for $`(1, 4)[2]`$ and $`(1, 4)[3]`$. For length at most 6, 30000 expansions chosen at random from 546090 showed no difference. But in expressions not reached in 1-Y, such as $`(1, 3, 10) = (1, 4)[2]`$, the layers can shift as at the end of §3, and 957 expansions passed (4-3). Their values were the same as the values computed by the 1-Y rule.
- For expressions whose mountain $`M(s)`$ has the same values and parents as in 1-Y, the expansions whose values differ from 1-Y were exactly the expansions that pass (4-1) (checked on the range above and on the expressions of length at most 4 reached by ω-Y from the seed $`(1, 5)`$). (4-1) and (4-2) occurred only when $`K \ge 2`$.
- For the 532 expressions of length at most 4 reached by 1-Y from the seed $`(1, 5)`$ (1596 expansions), 378 expansions give different values, and the correspondence of the numbers fails. These mountains have rows $`\omega^2`$ or larger.

The minimal examples were found by going through, in lexicographic order, the expressions reached from the ω-Y seeds by expansions and prefixes (length at most 8, entries at most 12, up to $`(1, 3, 4, 2, 5, 6, 5)`$; for branch (4), length at most 5, entries at most 40, up to $`(1, 4)`$). The minimal examples of branches (0)–(3) are the same as in the 1-Y version.

**Why branch (4) is not in 1-Y.** 1-Y branch (3-2-1) stretches the column by $`b e`$ rows from row $`f`$, separately for each layer $`k`$ below the root. The stretched rows and the lifted rows stay in layer $`k`$. The ω-Y (F) fills the rows from $`a`$ up to $`g_b(a)`$ at once, for each marker $`\mu = (\sigma, a)`$. If $`\delta'(q) \ge 1`$, it places nodes in rows $`e_q + \omega^{i}`$ with $`i \ge 1`$. Such a node is in a higher layer than $`q`$ ((4-1)). (C) starts at $`g_b(a)`$, so if $`\mathrm{lay}(g_b(a))`$ is larger than the layer of the source edge, the copied edge moves to a higher layer ((4-2)). Both happen when a layer boundary lies between $`a`$ and $`g_b(a)`$. The 1-Y branches have no such form. In the checked range, every expansion that passes (4-3) is an expansion of an expression whose edges of $`M(s)`$ have layers shifted from the 1-Y layers (end of §3). In such expressions even the numbers (1)–(3) can differ from the 1-Y branches. For example, in $`(1, 3, 10)[2]`$ of §6, the edge to row $`\omega`$ of column 3 is (2-3-1) in ω-Y and (3-2-1-1) in 1-Y.

**Check of the formulas.** A Python program that transcribes the formulas of §3 and §4 of this note literally was compared with the expansions of the reference implementation (2026-09-27). For the 101369 expressions of length at most 5 reached from the seeds $`(1, 2)`$, $`(1, 3)`$, $`(1, 4)`$, $`(1, 5)`$ by repeated expansions ($`N = 0, 1, 2, 3`$; $`N = 0`$ deletes the last column, so prefixes are reached as well), all 405476 expansions with $`N = 0, 1, 2, 3`$ gave the same result. The set in $`g_b(a)`$ of step 1 was never empty, and no column received two nodes in the same row. The branch-tree numbers also agreed, on all 30052039 edges of columns $`x`$ and beyond, with the numbers of the numbering program used in the comparison of 2026-09-26. That every edge of layer $`\lt K`$ of column $`x`$ of $`M(s')`$ lies below the top edge of column $`x`$ of $`M(s)`$ (branch (3-2) of §4) also held for every expansion in this range. Length 6 was not checked, because collecting the expressions with the reference implementation alone takes more than 60 seconds.

## 5. Weak magma and the official ω-Y

The official ω-Y is defined by `expand` in Naruyoko's program ([notes/00-survey.md](../../notes/00-survey.md) §1.2). The rule (F) of §4 is called the **weak magma** rule. Weak-magma ω-Y is ω-Y with the expansion of §4. It does not agree with the official ω-Y. On 3001 expressions reached from $`(1, 3)`$, $`(1, 4)`$, $`(1, 5)`$ by repeatedly taking official expansions and prefixes, 480 of the 9003 expansions with $`N = 1, 2, 3`$ give different results (notes/00-survey.md §1.6).

According to [notes/02-feasibility.md](../../notes/02-feasibility.md) §2, only the choice of the parents of the gap nodes differs.

- weak: the parents $`q`$ of the gap nodes all lie in one column $`m_b(\mathrm{col}(p))`$, where $`p = \widetilde{\mathrm{par}}(\mu)`$ is the parent of the marker $`\mu`$.
- official: for each gap row, choose one node of the root column (how it is chosen is in notes/02-feasibility.md §2.2). Let $`u`$ be the node of column $`\sigma`$ of $`M(s')`$ in the row of the chosen node. Let $`\sigma' := \mathrm{col}(\tilde\lambda(u))`$ (if $`u`$ is a bottom node, $`\tilde\lambda(u) = (\sigma - 1, 0)`$ and $`\sigma' = \sigma - 1`$). The parents of the gap nodes lie in column $`m_b(\sigma')`$.

**Example.** In $`(1, 3, 3)[2]`$, the parent of the node in row 2 of column 4 (a gap node) is $`(2, 1)`$ (value 2) in weak and $`(3, 1)`$ (value 5) in the official version. The bottom value of column 4 is $`2 + 2 = 4`$ in weak and $`2 + 5 = 7`$ in the official version. In total, weak gives $`(1, 3, 2, 5, 4, 9)`$ and the official version $`(1, 3, 2, 5, 7, 12)`$ (the official values are from notes/02-feasibility.md §2.3 and were not computed in Lean).

notes/02-feasibility.md counts the bottom row as 0: it writes $`\delta`$ for the row $`1 + \delta`$ of this note. In that note "$`k \leftarrow c_j@h`$" is a node in row $`k`$ whose left leg is the node of column $`j`$ in row $`h`$. For example "$`1 \leftarrow c_2@0`$" in that note is "row 2, left leg $`(2, 1)`$" in this note.

Termination of the official ω-Y is not a theorem of this repository. The official ω-Y is treated in [koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por).

**On "no extraction".** Phyrion calls this variant "weak magma, no extraction". The proof for the 1-Y sequence has a step called extraction. The definition of ω-Y has no step corresponding to it (the table in notes/00-survey.md §3.5). It uses a single mountain whose rows are ordinals. The exact meaning of the extraction rule in ω-Y has not been checked (notes/00-survey.md §1.5).

## 6. Examples of expansion

The values were computed by the Python program that transcribes the formulas of §4, and checked to be equal to the values of the reference implementation (2026-09-27). The rows with ✓ in the column "Lean" gave the same values when the Lean definition was evaluated with `#eval` in Lean 4.33.1 (2026-09-23).

"Branches used" lists the numbers of the branches of the branch tree of §4 that make an edge, and (0) when there is no root. The unchanged branches (1-1), (2-1), (3-1) are not listed. ★ marks the lexicographically smallest expression, in the checked range, that passes the branch with $`N = 2`$ (§4). The column "1-Y" is the value of the same expression expanded by the 1-Y rule (1-Y version, §6). "same" means the same value as ω-Y.

| Expression $`s`$ | $`N`$ | $`s[N]`$ | Branches used | 1-Y | Lean |
|---|---|---|---|---|---|
| $`(1)`$ | 5 | $`()`$ | (0)★ | same | |
| $`(1, 2)`$ | 3 | $`(1, 1, 1, 1)`$ | none | same | ✓ |
| $`(1, 2, 2)`$ | 2 | $`(1, 2, 1, 2, 1, 2)`$ | (2-2)★ | same | ✓ |
| $`(1, 2, 3)`$ | 0 | $`(1, 2)`$ | none | same | |
| $`(1, 2, 3)`$ | 1 | $`(1, 2, 2)`$ | (2-3-2) | same | |
| $`(1, 2, 3)`$ | 2 | $`(1, 2, 2, 2)`$ | (2-3-2)★ | same | ✓ |
| $`(1, 2, 4)`$ | 2 | $`(1, 2, 3, 4)`$ | (2-3-1)★ | same | ✓ |
| $`(1, 2, 4)`$ | 3 | $`(1, 2, 3, 4, 5)`$ | (2-3-1) | same | |
| $`(1, 2, 4, 3)`$ | 2 | $`(1, 2, 4, 2, 4, 2, 4)`$ | (2-2), (2-3-2) | same | |
| $`(1, 2, 4, 8, 10, 8)`$ | 2 | $`(1, 2, 4, 8, 10, 7, 12, 14, 11, 17, 19)`$ | (2-2), (2-3-1) | same | |
| $`(1, 3)`$ | 2 | $`(1, 2, 4)`$ | (3-2-1-2)★, (3-2-1-3)★ | same | ✓ |
| $`(1, 3)`$ | 3 | $`(1, 2, 4, 8)`$ | (3-2-1-2), (3-2-1-3) | same | ✓ |
| $`(1, 3, 2)`$ | 2 | $`(1, 3, 1, 3, 1, 3)`$ | (1-2)★, (2-2) | same | |
| $`(1, 3, 2, 5)`$ | 2 | $`(1, 3, 2, 4, 8)`$ | (3-2-1-1)★, (3-2-1-2), (3-2-1-3) | same | |
| $`(1, 3, 3)`$ | 0 | $`(1, 3)`$ | none | same | ✓ |
| $`(1, 3, 3)`$ | 1 | $`(1, 3, 2, 5)`$ | (2-2), (3-2-1-2), (3-2-1-3) | same | ✓ |
| $`(1, 3, 3)`$ | 2 | $`(1, 3, 2, 5, 4, 9)`$ | (2-2), (3-2-1-2), (3-2-1-3) | same | ✓ |
| $`(1, 3, 3)`$ | 3 | $`(1, 3, 2, 5, 4, 9, 8, 17)`$ | (2-2), (3-2-1-2), (3-2-1-3) | same | ✓ |
| $`(1, 3, 4)`$ | 2 | $`(1, 3, 3, 3)`$ | (1-2), (2-3-2) | same | ✓ |
| $`(1, 3, 4, 2, 5, 6, 5)`$ | 2 | $`(1, 3, 4, 2, 5, 6, 4, 9, 10, 8, 17, 18)`$ | (2-2), (3-2-1-1), (3-2-1-2), (3-2-1-3), (3-2-2)★ | same | |
| $`(1, 3, 9, 23)`$ | 2 | $`(1, 3, 9, 22, 50, 110, 238)`$ | (2-2), (2-3-1), (3-2-1-1), (3-2-1-2), (3-2-1-3) | same | |
| $`(1, 3, 10)`$ | 2 | $`(1, 3, 9, 27)`$ | (2-3-1), (3-2-1-1), (3-2-1-2), (3-2-1-3), (4-3)★ | same | |
| $`(1, 4)`$ | 1 | $`(1, 3)`$ | none | same | ✓ |
| $`(1, 4)`$ | 2 | $`(1, 3, 10)`$ | (3-2-1-2), (3-2-1-3), (4-1)★, (4-2)★ | $`(1, 3, 9)`$ | ✓ |
| $`(1, 4)`$ | 3 | $`(1, 3, 10, 37)`$ | (3-2-1-2), (3-2-1-3), (4-1), (4-2) | $`(1, 3, 9, 27)`$ | ✓ |
| $`(1, 4, 4)`$ | 2 | $`(1, 4, 3, 11, 10, 38)`$ | (2-2), (3-2-1-2), (3-2-1-3), (4-1), (4-2) | $`(1, 4, 3, 10, 9, 28)`$ | ✓ |

$`(1, 3, 10)`$ is not reached from a seed in 1-Y ("Checked range" in §4). Its expansion gives the same values under the 1-Y rule, but the layers of the edges of ω-Y are shifted from the 1-Y layers, so it passes (4-3).

## 7. One-step expansion and the final theorems

**Definition (one-step expansion).** $`t`$ is a nontrivial one-step expansion of $`s`$ if $`s[N] = t`$ for some $`N \in \mathbb N`$ and $`t \ne s`$. We write this $`t \prec s`$.

- The empty expression expands to itself. So the empty expression has no one-step expansion. For a nonempty expression $`s`$ we have $`s[N] \ne s`$, so $`t \prec s`$ is the same as "$`s \ne ()`$ and $`t = s[N]`$ for some $`N`$".
- A one-step expansion lowers the lexicographic order. But the lexicographic order is not well-founded, so this alone does not give termination.
- The expansion is defined for every expression (step 1 of §4 finishes without getting stuck). This is shown in Lean.

**Definition (reachable).** If there are $`s = t_0, t_1, \ldots, t_j = t`$ ($`j \in \mathbb N`$) where each $`t_{i+1}`$ is an expansion $`t_i[N_i]`$ ($`N_i \in \mathbb N`$) of $`t_i`$, we say $`t`$ is **reachable** from $`s`$ and write $`s \to^{*} t`$. Since $`j = 0`$ is allowed, $`s`$ is reachable from $`s`$. An expression reachable from $`s`$ is a **descendant** of $`s`$.

**Definition (dimension).** A natural number $`D`$ is a **dimension** of the mountain of an expression $`s`$ if every row $`a`$ of $`M(s)`$ has $`c_i(a) = 0`$ for $`i \gt D`$.

- If $`D`$ is a dimension of the mountain of $`s`$, it is also a dimension of the mountain of $`s[N]`$ (shown in Lean).
- So one $`D`$ chosen for the starting expression works for all its descendants. $`D`$ fixes the key length $`D + 1`$ of [06](06-combinatorial-layer.md).

The final theorems of this repository ([README](../../README-en.md) "The four final theorems") are:

1. Theorem 1: the one-step expansion relation $`\prec`$ is well-founded.
2. Theorem 2: the set of expressions reachable from a seed is well-ordered by the lexicographic order.
3. Theorem 3: for every expression, the set of its descendants is well-ordered by the lexicographic order.
4. Theorem 4: however the copy counts are chosen, repeated expansion reaches the empty expression.

Theorems 2–4 follow from Theorem 1 by combinatorial arguments only. The proof of Theorem 1 is the topic of [06](06-combinatorial-layer.md) and the later notes.

## 8. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "Target: weak-magma ω-Y" | the expansion treated, and how it differs from the official ω-Y |
| [README](../../README-en.md) "Notation", "The four final theorems" | expressions, $`s[N]`$, $`\prec`$, the four theorems |
| [notes/00-survey.md](../../notes/00-survey.md) §1.3–§1.6 | the shape of the mountain, expansion, variants, comparison with the official version |
| [notes/02-feasibility.md](../../notes/02-feasibility.md) §1.1, §2 | notation, and the difference in choosing the parents of the gap nodes |
| [OmegaY/Rows.lean](../../OmegaY/Rows.lean), [OmegaY/Canonical/Build.lean](../../OmegaY/Canonical/Build.lean), [OmegaY/Expansion/Build.lean](../../OmegaY/Expansion/Build.lean) | the definitions of §2–§4 |

## 9. Lean correspondence

| Concept | Lean | File |
|---|---|---|
| expressions | `Canonical.Legal`, `Dynamics.Expr` | [OmegaY/Canonical/Totality.lean](../../OmegaY/Canonical/Totality.lean), [OmegaY/Expansion/LegalDynamics.lean](../../OmegaY/Expansion/LegalDynamics.lean) |
| seeds ($`(1, n+2)`$), lexicographic order | `Dynamics.seed`, `Dynamics.Lex` | [OmegaY/Expansion/LegalDynamics.lean](../../OmegaY/Expansion/LegalDynamics.lean) |
| rows, coefficients, order of rows | `Row`, `Row.coeff`, `Row.LexLt` | [OmegaY/Rows.lean](../../OmegaY/Rows.lean) |
| jump, $`a + \omega^e`$, next row $`B`$ | `Row.jump`, `Row.bump`, `Row.B` | same |
| nodes, mountains (a column is an array from the bottom; a node has a row, a value and a left leg) | `Canonical.Cell`, `Canonical.Ref`, `Canonical.Mountain`, `Canonical.phantom` | [OmegaY/Canonical/Build.lean](../../OmegaY/Canonical/Build.lean) |
| finding the parent ($`\mathrm{next}`$ and $`j`$) | `climb`, `nextCandidate`, `findParent` | same |
| building the mountain | `growColumn`, `buildColumn`, `build` | same |
| expansion, root, boundary rows $`\Gamma`$, decremented mountain | `expandDiagram`, `expand`, `valuesOf` | [OmegaY/Expansion/Build.lean](../../OmegaY/Expansion/Build.lean) |
| markers | `weakParent`, `weakReaches`, `markers` | same |
| reference rows $`\beta_b`$, $`g_b`$ | `below`, `referenceAt` | same |
| (T), (C), (F), $`\mathrm{tr}_b`$ | `copyEdge`, `contour`, `fill`, `copyColumn`, `copyBlock` | same |
| step 2 (rebuild the values) | `finish`, `backfill` | same |
| the expansion is defined for every expression | `expand_total` | [OmegaY/Expansion/Totality.lean](../../OmegaY/Expansion/Totality.lean) |
| layers, branch tree, correspondence with 1-Y | none (not defined in Lean; only checked by computer) | |
| one-step expansion, lowering the lexicographic order | `Dynamics.next`, `Dynamics.Step`, `Dynamics.next_lex` | [OmegaY/Expansion/LegalDynamics.lean](../../OmegaY/Expansion/LegalDynamics.lean) |
| preservation of the dimension | `expandDiagram_key_dimension`, `Dynamics.next_key_dimension`, `Dynamics.fixed_dimension_for_descendants` | [OmegaY/Expansion/SupportedDimension.lean](../../OmegaY/Expansion/SupportedDimension.lean), [OmegaY/Expansion/DynamicsRowBound.lean](../../OmegaY/Expansion/DynamicsRowBound.lean) |
| Theorems 1–4 | `omegaY_step_wellFounded`, `omegaY_generated_isWellOrder`, `omegaY_descendants_isWellOrder`, `omegaY_trajectory_terminates` | [OmegaY/Expansion/WellFounded.lean](../../OmegaY/Expansion/WellFounded.lean) |
| deriving Theorems 2–4 from Theorem 1 | `Dynamics.generated_isWellOrder`, `Dynamics.every_legal_root_isWellOrder`, `omegaY_no_infinite_step_chain` | [OmegaY/Expansion/GeneratedWellOrder.lean](../../OmegaY/Expansion/GeneratedWellOrder.lean), [OmegaY/Expansion/WellFounded.lean](../../OmegaY/Expansion/WellFounded.lean) |
