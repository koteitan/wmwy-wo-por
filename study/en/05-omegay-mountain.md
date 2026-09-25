[← Back](README.md) | [English](05-omegay-mountain.md) | [Japanese](../05-omegay-mountain.md)

# The ω-Y sequence and its mountain

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | ordinal, Cantor normal form of ordinals below $`\omega^\omega`$, the 1-Y version |
| [02 Well-founded relations and recursion](02-well-founded.md) | well-founded, the lexicographic order on expressions is not well-founded |

This note explains how the weak-magma ω-Y sequence and its expansion are defined in Lean. The definitions are those of Phyrion's formalization ([Phyrion1343/omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean)), copied unchanged into `OmegaY/` of this repository. The mountain is in [OmegaY/Canonical/Build.lean](../../OmegaY/Canonical/Build.lean) and the expansion in [OmegaY/Expansion/Build.lean](../../OmegaY/Expansion/Build.lean).

The example values were computed with `#eval` of `Canonical.build`, `Canonical.fullSummary`, `Expansion.expand`, `Expansion.expandDiagram` and `Expansion.markers` in Lean 4.33.1 (2026-09-23). The intermediate steps follow those definitions by hand.

## 1. Expressions

**Definition (expression).** An **expression** is a finite sequence of positive integers $`s = (s_0, \ldots, s_x)`$ that is empty or has $`s_0 = 1`$ (`Canonical.Legal`, `Dynamics.Expr`).

- Columns are numbered from 0. The $`i`$-th entry is "column $`i`$". The number of the last column is written $`x`$.
- An expression from which expansion (§4) starts is called a **seed**. The standard seeds are $`(1, m)`$ with $`m`$ an integer $`\ge 2`$. In Lean `Dynamics.seed n` $`= (1, n+2)`$.
- Expressions are ordered by the lexicographic order of [02](02-well-founded.md) §1 (`Dynamics.Lex`). This order is not well-founded on all expressions.

## 2. Rows

The rows of an ω-Y mountain are not natural numbers but ordinals below $`\omega^\omega`$.

**Definition (row).** A **row** is a sequence of coefficients $`(c_0, c_1, c_2, \ldots)`$, all but finitely many 0 (`OmegaY.Row`, coefficients `Row.coeff`). It is identified with the ordinal

```math
\omega^{d} c_d + \cdots + \omega^{2} c_2 + \omega c_1 + c_0
```

Write $`c_i(a)`$ for the coefficient $`c_i`$ of a row $`a`$. The order compares at the largest exponent where the coefficients differ (`Row.LexLt`). This is the order of ordinals. Lean displays a row (`Row.toList`) as its coefficients in increasing order of exponent.

| Row | Display |
|---|---|
| $`1`$ | `[1]` |
| $`2`$ | `[2]` |
| $`\omega`$ | `[0, 1]` |
| $`\omega + 1`$ | `[1, 1]` |
| $`\omega \cdot 2`$ | `[0, 2]` |
| $`\omega^2`$ | `[0, 0, 1]` |

**Definition (jump).** The **jump** of two rows $`a, b`$ is (`Row.jump`):

```math
\mathrm{jump}(a, b) = \begin{cases} 0 & (a = b) \cr 1 + \max\{\, i \mid c_i(a) \ne c_i(b) \,\} & (a \ne b) \end{cases}
```

**Definition (adding a power of ω).** $`\mathrm{bump}(a, d) = a + \omega^d`$ (ordinal sum) (`Row.bump`). In coefficients: set the coefficients below $`d`$ to 0, add 1 to the coefficient of $`d`$, and keep the coefficients above $`d`$.

**Definition (next row).** $`B(a, b) = \mathrm{bump}(a, \mathrm{jump}(a, b)) = a + \omega^{\mathrm{jump}(a, b)}`$ (`Row.B`).

| $`a`$ | $`b`$ | $`\mathrm{jump}(a, b)`$ | $`B(a, b)`$ |
|---|---|---|---|
| $`1`$ | $`1`$ | $`0`$ | $`2`$ |
| $`2`$ | $`2`$ | $`0`$ | $`3`$ |
| $`2`$ | $`1`$ | $`1`$ | $`2 + \omega = \omega`$ |
| $`\omega`$ | $`1`$ | $`2`$ | $`\omega + \omega^2 = \omega^2`$ |
| $`\omega`$ | $`\omega`$ | $`0`$ | $`\omega + 1`$ |
| $`\omega + 1`$ | $`\omega`$ | $`1`$ | $`\omega \cdot 2`$ |

If $`a = b`$, the row goes up by 1. This is how rows of a mountain of the 1-Y sequence (the sequence treated by the 1-Y version of [01](01-ordinals.md) §7) move. If $`a \ne b`$, the row jumps by a power of $`\omega`$.

## 3. Building the mountain

The **mountain** $`M(s)`$ of an expression $`s`$ is an array of columns, and a column is an array of nodes from bottom to top (`Canonical.Mountain`, `Canonical.Column`). Column $`c`$ of the mountain corresponds to column $`c`$ of the expression. The nodes in a column are numbered 0, 1, 2, … from the bottom. A node `Cell` has three components: the row `row`, the value `value`, and the left leg `left`. Write $`\mathrm{row}(u)`$ and $`\mathrm{value}(u)`$ for the row and value of a node $`u`$. `left` points to a node of a column to the left.

**Definition (canonical mountain `Canonical.build`).** Build the columns $`c = 0, 1, \ldots, x`$ from left to right.

1. Node 0 is the **phantom** (a placeholder node), with row 0 and value 0.
2. Node 1 is the **bottom node**, with row 1 and value $`s_c`$. Its left leg is the phantom of column $`c - 1`$ (none for $`c = 0`$).
3. While the value $`v`$ of the top node $`u`$ is greater than 1, repeat (`growColumn`): find the **father** $`\pi`$ of $`u`$, and put above $`u`$ a node with row $`B(\mathrm{row}(u), \mathrm{row}(\pi))`$, value $`v - \mathrm{value}(\pi)`$ and left leg $`\pi`$.
4. When a node of value 1 is reached, the column is finished. Every column has value 1 at the top.

**Definition (finding the father, `findParent`).** Start with the candidate $`\nu`$ equal to $`u`$ itself. Repeat the following Q step (`nextCandidate`).

- Follow the left leg $`L`$ of $`\nu`$. In the column of $`L`$, climb up from $`L`$ as long as the next node's row is at most $`\mathrm{row}(\nu)`$ (`climb`). The node reached is the new candidate $`\nu`$.
- If the new candidate has $`0 \lt \mathrm{value}(\nu) \lt v`$, then $`\nu`$ is the father. Otherwise repeat the Q step from this $`\nu`$.

The bottom nodes are in row 1. In row 1 the candidates are the bottom nodes of columns $`c-1, c-2, \ldots`$ in turn. So the father of a bottom node is the bottom node of the rightmost column with value smaller than $`s_c`$. This is the same as the parent in row 0 of a 1-Y mountain (the 1-Y mountain counts the bottom row as 0).

**Definition (edge).** If a node $`u`$ (not a phantom) has a node $`u^+`$ directly above it, there is an **edge** from $`u`$ to $`u^+`$. The left leg of $`u^+`$ is the **father** $`\pi`$ of the edge. The father is always in a column to the left.

```math
\mathrm{value}(u^+) = \mathrm{value}(u) - \mathrm{value}(\pi), \qquad \mathrm{row}(u^+) = \mathrm{row}(u) + \omega^{\mathrm{jump}(\mathrm{row}(u), \mathrm{row}(\pi))}
```

The jump $`\mathrm{jump}(\mathrm{row}(u), \mathrm{row}(\pi))`$ is the **degree** of the edge (`RealStoredEdge.degree` in [06](06-combinatorial-layer.md)).

**Example ($`(1, 3, 3)`$).** In the table, "$`v \leftarrow (j, h)`$" means that the value is $`v`$ and the left leg (the father of the edge from the node below) is the node of column $`j`$ in row $`h`$. Lean's reference `Ref` uses the index from the bottom instead of the row. The left legs of bottom nodes (the phantoms of the columns to the left) are not written.

| Row | Column 0 | Column 1 | Column 2 |
|---|---|---|---|
| $`\omega`$ | | $`1 \leftarrow (0, 1)`$ | $`1 \leftarrow (0, 1)`$ |
| $`2`$ | | $`2 \leftarrow (0, 1)`$ | $`2 \leftarrow (0, 1)`$ |
| $`1`$ | $`1`$ | $`3`$ | $`3`$ |
| $`0`$ | phantom | phantom | phantom |

- Bottom node of column 1 (value 3): the Q step reaches the bottom node of column 0 (value 1). Since $`1 \lt 3`$, it is the father. The next node has row $`B(1, 1) = 2`$ and value $`3 - 1 = 2`$.
- Node of column 1 in row 2 (value 2): its left leg is $`(0, 1)`$, and column 0 has no node above it. The candidate is $`(0, 1)`$, and $`1 \lt 2`$, so it is the father. The next node has row $`B(2, 1) = \omega`$ and value 1.
- Bottom node of column 2 (value 3): the first candidate is the bottom node of column 1, whose value 3 is not smaller than $`3`$. The next candidate is the bottom node of column 0, which is the father.

**Example ($`(1, 4)`$).** Column 1 has values $`4, 3, 2, 1`$ in rows $`1, 2, \omega, \omega^2`$, and every father is $`(0, 1)`$. Row $`\omega^2`$ is $`B(\omega, 1)`$.

**Example (column 2 of $`(1, 3, 10)`$).** It has values $`10, 7, 5, 3, 2, 1`$ in rows $`1, 2, 3, \omega, \omega + 1, \omega \cdot 2`$. The fathers are, in order, $`(1, 1), (1, 2), (1, 2), (1, \omega), (1, \omega)`$. For example the node in row $`\omega`$ is at $`B(3, 2) = 3 + \omega = \omega`$, and the node in row $`\omega \cdot 2`$ at $`B(\omega + 1, \omega) = \omega \cdot 2`$.

## 4. Expansion

**Definition (expansion `expand s N`).** From an expression $`s = (s_0, \ldots, s_x)`$ and a natural number $`N`$, it makes a new expression $`s[N]`$. $`N`$ is the number of copies.

**Case 1.** If $`s`$ is empty, $`s_x = 1`$, or $`N = 0`$: delete the last column. $`s[N] = (s_0, \ldots, s_{x-1})`$ (in Lean the last column of the mountain is removed by `pop`).

**Case 2.** Otherwise the steps are (`expandDiagram`):

1. **Root.** In the mountain of $`s`$, the father of the top edge of column $`x`$ is the **root** $`r`$. Let $`c_r`$ be the column of the root and $`w = x - c_r`$ the width.
2. **Decrement.** Build the mountain $`M(s')`$ of $`s' = (s_0, \ldots, s_{x-1}, s_x - 1)`$.
3. **Boundary rows.** In the mountain of $`s`$, list, from the top, the row of the top node of column $`x`$ and the rows of the nodes of the root column at or below the root, excluding the phantom (`boundaries`).
4. **Markers.** A node of $`M(s')`$ to the right of the root column is a **marker** (`markers`) if it is in the same row as a node $`z`$ of the root column (the root or a node below it, including the phantom) and reaches $`z`$ by following **weak fathers**. The weak father of a node $`u`$ is the father $`\pi`$ of the edge from $`u`$ upward, provided $`\mathrm{row}(\pi) = \mathrm{row}(u)`$ (`weakParent`).
5. **Blocks.** For $`b = 1, \ldots, N`$ in order, copy the columns $`y = c_r + 1, \ldots, x`$ to the columns $`y + b w`$ (`copyBlock`, `copyColumn`). The $`w`$ columns copied in the $`b`$-th round are called **block** $`b`$.
6. **Cut.** Delete the last column (the copy of column $`x`$ in block $`N`$). Read the value of the bottom node of each column (`valuesOf`).

The length of $`s[N]`$ is $`x + N w`$.

**Copying a column (`copyColumn`).** When column $`y`$ is copied in block $`b`$, the edges of column $`y`$ of $`M(s')`$ are called the **source edges**. Write $`\mathrm{col}(p)`$ for the number of the column of a node $`p`$. For each marker $`\mu`$ of $`y`$, three kinds of nodes are placed.

- **Translation** (`copyEdge`): a node in row $`\mathrm{row}(\mu)`$. Let $`\ell`$ be the left leg of $`\mu`$. The left leg of the new node is the same node $`\ell`$ if $`\ell`$ is left of the root column. Otherwise it is the highest node of column $`\mathrm{col}(\ell) + b w`$ whose row is below $`\mathrm{row}(\mu)`$. A phantom marker is copied to a phantom.
- **Contour** (`contour`): first fix the reference row $`g`$. In the current last column (the copy of column $`x`$ in block $`b-1`$; for $`b = 1`$, column $`x`$ of $`M(s')`$), take for each boundary row the highest node strictly below it (`below`). $`g`$ is the row of the last of these whose row is at least $`\mathrm{row}(\mu)`$ (`referenceAt`). Then copy the source edges upward from $`\mu`$ in order. Stop before an edge whose upper node is another marker. Stop at the top of the column. A source edge of degree $`d`$ becomes an edge from the current row $`h`$ to the row $`h + \omega^d`$; the first $`h`$ is $`g`$. The left leg is the image of the father of the source edge, by the same rule as for translation.
- **Fill** (`fill`, the weak magma): let $`p`$ be the father of the source edge from $`\mu`$ upward. For every node $`q`$ of column $`\mathrm{col}(p) + b w`$ with $`\mathrm{row}(\mu) \le \mathrm{row}(q) \lt g`$, let $`q^+`$ be the node directly above $`q`$, and place nodes in rows $`\mathrm{row}(q) + \omega^i`$ for $`i = \mathrm{jump}(\mathrm{row}(q), \mathrm{row}(q^+)) - 1, \ldots, 0`$. The left leg of each is $`q`$. The nodes placed by the fill are called **gap nodes**.

Finally the nodes are sorted by row (`finish`). The top node gets value 1, and the values are set from top to bottom by $`\mathrm{value}(u) = \mathrm{value}(u^+) + \mathrm{value}(\pi)`$, where $`\pi`$ is the left leg of $`u^+`$ (`backfill`).

**Example ($`(1, 3, 3)[2]`$).** The result is $`(1, 3, 2, 5, 4, 9)`$.

- The root is $`(0, 1)`$, so $`c_r = 0`$ and $`w = 2`$. $`s' = (1, 3, 2)`$. Column 2 of $`M(s')`$ has value 2 in row 1 and $`1 \leftarrow (0, 1)`$ in row 2.
- The boundary rows are $`(\omega, 1)`$. The markers are, in each of columns 1 and 2, the node in row 1 and the phantom (checked with `#eval`).
- References of block 1: in column 2 of $`M(s')`$, the highest node below row $`\omega`$ is in row 2, and the highest node below row 1 is the phantom (row 0).

Block 1 copies column 1 to column 3.

| Node | Kind | Reason |
|---|---|---|
| row 1 | translation | marker $`(1, 1)`$; the left leg is the phantom of column 2 |
| row 2, left leg $`(2, 1)`$ | fill | the father of the source edge $`(1,1) \to (1,2)`$ is $`(0, 1)`$; in column $`0 + 2 = 2`$, $`q = (2, 1)`$ has $`1 \le 1 \lt g = 2`$; $`\mathrm{jump}(1, 2) = 1`$, so row $`1 + \omega^0 = 2`$ |
| row 3, left leg $`(2, 2)`$ | contour | the source edge $`(1,1) \to (1,2)`$ has degree 0; $`g + \omega^0 = 3`$ |
| row $`\omega`$, left leg $`(2, 2)`$ | contour | the source edge $`(1,2) \to (1,\omega)`$ has degree 1; $`3 + \omega = \omega`$ |

From the top, the values are $`1`$, $`1 + \mathrm{value}(2,2) = 2`$, $`2 + \mathrm{value}(2,2) = 3`$, $`3 + \mathrm{value}(2,1) = 5`$. So column 3 has value 5. In the same way column 4 (the copy of column 2) gets value 4. Block 2 makes columns 5 and 6, and column 6 is cut.

Columns 3–5 of `expandDiagram [1,3,3] 2`:

| Row | Column 3 | Column 4 | Column 5 |
|---|---|---|---|
| $`\omega`$ | $`1 \leftarrow (2, 2)`$ | | $`1 \leftarrow (4, 3)`$ |
| $`4`$ | | | $`2 \leftarrow (4, 3)`$ |
| $`3`$ | $`2 \leftarrow (2, 2)`$ | $`1 \leftarrow (2, 2)`$ | $`3 \leftarrow (4, 2)`$ |
| $`2`$ | $`3 \leftarrow (2, 1)`$ | $`2 \leftarrow (2, 1)`$ | $`5 \leftarrow (4, 1)`$ |
| $`1`$ | $`5`$ | $`4`$ | $`9`$ |

Column 5 is the copy of column 1 in block 2. The source father $`(0, 1)`$ is copied to column $`0 + 2 \cdot 2 = 4`$. Block 2 takes its references from column 4. The highest node of column 4 below the boundary row $`\omega`$ is in row 3. So $`g = 3`$, and the contour of column 5 starts at row $`3 + 1 = 4`$. The fill uses the nodes of column 4 in rows 1 and 2 as fathers and places nodes in rows 2 and 3. Column 5 has one more node than column 3.

## 5. Weak magma and the official ω-Y

The official ω-Y is defined by `expand` in Naruyoko's program ([notes/00-survey.md](../../notes/00-survey.md) §1.2). The fill rule of §4 is called the **weak magma** rule. Weak-magma ω-Y is ω-Y with the expansion of §4. It does not agree with the official ω-Y. On 3001 expressions reached from $`(1, 3)`$, $`(1, 4)`$, $`(1, 5)`$ by repeatedly taking official expansions and prefixes, 480 of the 9003 expansions with $`N = 1, 2, 3`$ give different results (notes/00-survey.md §1.6).

According to [notes/02-feasibility.md](../../notes/02-feasibility.md) §2, only the fill rule differs.

- weak: the left legs of the gap nodes all lie in one column $`\mathrm{col}(p) + b w`$, where $`p`$ is the father of the source edge from $`\mu`$ upward.
- official: for each gap row, choose one node of the root column (how it is chosen is in notes/02-feasibility.md §2.2). Let $`z`$ be the node of column $`y`$ of $`M(s')`$ in the row of the chosen node. Let $`y'`$ be the column of the left leg of $`z`$ ($`y' = y - 1`$ if $`z`$ is in the bottom row). The left legs of the gap nodes lie in the copy of column $`y'`$ ($`y' + b w`$ if $`y' \ge c_r`$, and $`y'`$ if $`y' \lt c_r`$).

**Example.** In $`(1, 3, 3)[2]`$, the left leg of the node in row 2 of column 4 (a gap node) is $`(2, 1)`$ (value 2) in weak and $`(3, 1)`$ (value 5) in the official version. The bottom value of column 4 is $`2 + 2 = 4`$ in weak and $`2 + 5 = 7`$ in the official version. In total, weak gives $`(1, 3, 2, 5, 4, 9)`$ and the official version $`(1, 3, 2, 5, 7, 12)`$ (the official values are from notes/02-feasibility.md §2.3 and were not computed in Lean).

notes/02-feasibility.md counts the bottom row as 0: it writes $`\delta`$ for the Lean row $`1 + \delta`$. In that note "$`k \leftarrow c_j@h`$" is a node in row $`k`$ whose left leg is the node of column $`j`$ in row $`h`$. For example "$`1 \leftarrow c_2@0`$" in that note is "row 2, left leg $`(2, 1)`$" in this note.

Termination of the official ω-Y is not a theorem of this repository. The official ω-Y is treated in [koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por).

**On "no extraction".** Phyrion calls this variant "weak magma, no extraction". The proof for the 1-Y sequence has a step called extraction. The Lean definition of ω-Y has no step corresponding to it (the table in notes/00-survey.md §3.5). It uses a single mountain whose rows are ordinals. The exact meaning of the extraction rule in ω-Y has not been checked (notes/00-survey.md §1.5).

## 6. Examples of expansion

All are values of `#eval Expansion.expand s N`.

| Expression $`s`$ | $`N`$ | $`s[N]`$ |
|---|---|---|
| $`(1, 2)`$ | 3 | $`(1, 1, 1, 1)`$ |
| $`(1, 2, 2)`$ | 2 | $`(1, 2, 1, 2, 1, 2)`$ |
| $`(1, 2, 3)`$ | 2 | $`(1, 2, 2, 2)`$ |
| $`(1, 2, 4)`$ | 2 | $`(1, 2, 3, 4)`$ |
| $`(1, 3)`$ | 2 | $`(1, 2, 4)`$ |
| $`(1, 3)`$ | 3 | $`(1, 2, 4, 8)`$ |
| $`(1, 3, 3)`$ | 0 | $`(1, 3)`$ |
| $`(1, 3, 3)`$ | 1 | $`(1, 3, 2, 5)`$ |
| $`(1, 3, 3)`$ | 2 | $`(1, 3, 2, 5, 4, 9)`$ |
| $`(1, 3, 3)`$ | 3 | $`(1, 3, 2, 5, 4, 9, 8, 17)`$ |
| $`(1, 3, 4)`$ | 2 | $`(1, 3, 3, 3)`$ |
| $`(1, 4)`$ | 1 | $`(1, 3)`$ |
| $`(1, 4)`$ | 2 | $`(1, 3, 10)`$ |
| $`(1, 4)`$ | 3 | $`(1, 3, 10, 37)`$ |
| $`(1, 4, 4)`$ | 2 | $`(1, 4, 3, 11, 10, 38)`$ |

## 7. One expansion step and the final theorems

**Definition (one expansion step).** $`t \prec s`$ (`Dynamics.Step t s`) means $`s \ne ()`$ and $`t = s[N]`$ for some $`N`$.

- `Dynamics.next s N` is the successful result of the expansion program. It succeeds on every expression (`expand_total`).
- One expansion step strictly decreases the lexicographic order (`Dynamics.next_lex`).
- If in every row of a mountain the coefficients above exponent $`D`$ are 0, $`D`$ is called a **dimension** of the mountain. If a mountain has dimension $`D`$, so does the mountain after expansion (`expandDiagram_key_dimension`, `Dynamics.next_key_dimension`). So one $`D`$, chosen for the starting expression, serves all expressions reached from it by repeated expansion steps (`Dynamics.fixed_dimension_for_descendants`). $`D`$ fixes the length $`D + 1`$ of the keys in [06](06-combinatorial-layer.md).

The final theorems ([OmegaY/Expansion/WellFounded.lean](../../OmegaY/Expansion/WellFounded.lean), namespace `OmegaY.Expansion`) are:

1. `omegaY_step_wellFounded`: $`\prec`$ is well-founded.
2. `omegaY_generated_isWellOrder`: the set of expressions generated from the seeds is well-ordered by the lexicographic order.
3. `omegaY_descendants_isWellOrder`: for every expression, the set of expressions reachable from it is well-ordered by the lexicographic order.
4. `omegaY_trajectory_terminates`: however the numbers of copies are chosen, repeated expansion reaches the empty expression.

2–4 follow from 1 by combinatorial arguments only (`Dynamics.generated_isWellOrder`, `Dynamics.every_legal_root_isWellOrder`, `omegaY_no_infinite_step_chain`). The proof of 1 is the subject of [06](06-combinatorial-layer.md) onward.

## 8. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "Target: weak-magma ω-Y" | the expansion treated, and how it differs from the official ω-Y |
| [README](../../README-en.md) "Notation", "The four final theorems" | expressions, $`s[N]`$, $`\prec`$, the four theorems |
| [notes/00-survey.md](../../notes/00-survey.md) §1.3–§1.6 | the shape of the mountain, expansion, variants, comparison with the official version |
| [notes/02-feasibility.md](../../notes/02-feasibility.md) §1.1, §2 | notation, and the difference in the fill rule |
| [OmegaY/Rows.lean](../../OmegaY/Rows.lean), [OmegaY/Canonical/Build.lean](../../OmegaY/Canonical/Build.lean), [OmegaY/Expansion/Build.lean](../../OmegaY/Expansion/Build.lean) | the definitions of §2–§4 |

## 9. Lean correspondence

| Concept | Lean | File |
|---|---|---|
| expressions | `Canonical.Legal`, `Dynamics.Expr` | [OmegaY/Canonical/Totality.lean](../../OmegaY/Canonical/Totality.lean), [OmegaY/Expansion/LegalDynamics.lean](../../OmegaY/Expansion/LegalDynamics.lean) |
| seeds, lexicographic order | `Dynamics.seed`, `Dynamics.Lex` | [OmegaY/Expansion/LegalDynamics.lean](../../OmegaY/Expansion/LegalDynamics.lean) |
| rows, jump, adding a power, next row | `Row`, `Row.jump`, `Row.bump`, `Row.B` | [OmegaY/Rows.lean](../../OmegaY/Rows.lean) |
| nodes, mountains | `Canonical.Cell`, `Canonical.Ref`, `Canonical.Mountain`, `Canonical.phantom` | [OmegaY/Canonical/Build.lean](../../OmegaY/Canonical/Build.lean) |
| finding the father | `climb`, `nextCandidate`, `findParent` | same |
| building the mountain | `growColumn`, `buildColumn`, `build` | same |
| expansion | `expandDiagram`, `expand`, `valuesOf` | [OmegaY/Expansion/Build.lean](../../OmegaY/Expansion/Build.lean) |
| markers | `weakParent`, `weakReaches`, `markers` | same |
| copying columns | `copyEdge`, `contour`, `fill`, `below`, `referenceAt`, `copyColumn`, `copyBlock` | same |
| restoring values | `finish`, `backfill` | same |
| one expansion step | `Dynamics.next`, `Dynamics.Step`, `Dynamics.next_lex` | [OmegaY/Expansion/LegalDynamics.lean](../../OmegaY/Expansion/LegalDynamics.lean) |
| preservation of the dimension | `expandDiagram_key_dimension`, `Dynamics.next_key_dimension`, `Dynamics.fixed_dimension_for_descendants` | [OmegaY/Expansion/SupportedDimension.lean](../../OmegaY/Expansion/SupportedDimension.lean), [OmegaY/Expansion/DynamicsRowBound.lean](../../OmegaY/Expansion/DynamicsRowBound.lean) |
| final theorems | `omegaY_step_wellFounded` and the others | [OmegaY/Expansion/WellFounded.lean](../../OmegaY/Expansion/WellFounded.lean) |
