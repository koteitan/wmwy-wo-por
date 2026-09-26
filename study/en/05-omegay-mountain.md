[← Back](README.md) | [English](05-omegay-mountain.md) | [Japanese](../05-omegay-mountain.md)

# The ω-Y sequence and its mountain

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | ordinal, Cantor normal form of ordinals below $`\omega^\omega`$, the 1-Y version |
| [02 Well-founded relations and recursion](02-well-founded.md) | well-founded, the lexicographic order on expressions is not well-founded |

This note explains how the weak-magma ω-Y sequence and its expansion are defined in Lean. The definitions are those of Phyrion's formalization ([Phyrion1343/omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean)), copied unchanged into `OmegaY/` of this repository. The mountain is in [OmegaY/Canonical/Build.lean](../../OmegaY/Canonical/Build.lean) and the expansion in [OmegaY/Expansion/Build.lean](../../OmegaY/Expansion/Build.lean).

The example values were computed with `#eval` of `Canonical.build`, `Canonical.fullSummary`, `Expansion.expand`, `Expansion.expandDiagram` and `Expansion.markers` in Lean 4.33.1 (2026-09-23). The layers and the correspondence with the 1-Y mountain in §3, the branch tree and the comparison with 1-Y in §4, the example $`(1, 4)[2]`$ in §4, and the values of §6 were computed with Phyrion's JavaScript reference implementation ([reference/engine.js](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean/blob/main/reference/engine.js), which corresponds to [OmegaY/Expansion/Build.lean](../../OmegaY/Expansion/Build.lean)) with added logging, and with a Python program that follows the definition of the 1-Y version (2026-09-26). The intermediate steps follow those definitions by hand.

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
3. While the value $`v`$ of the top node $`u`$ is greater than 1, repeat (`growColumn`): find the **parent** $`\pi`$ of $`u`$, and put above $`u`$ a node with row $`B(\mathrm{row}(u), \mathrm{row}(\pi))`$, value $`v - \mathrm{value}(\pi)`$ and left leg $`\pi`$.
4. When a node of value 1 is reached, the column is finished. Every column has value 1 at the top.

**Definition (finding the parent, `findParent`).** Start with the candidate $`\nu`$ equal to $`u`$ itself. Repeat the following Q step (`nextCandidate`).

- Follow the left leg $`L`$ of $`\nu`$. In the column of $`L`$, climb up from $`L`$ as long as the next node's row is at most $`\mathrm{row}(\nu)`$ (`climb`). The node reached is the new candidate $`\nu`$.
- If the new candidate has $`0 \lt \mathrm{value}(\nu) \lt v`$, then $`\nu`$ is the parent. Otherwise repeat the Q step from this $`\nu`$.

The bottom nodes are in row 1. In row 1 the candidates are the bottom nodes of columns $`c-1, c-2, \ldots`$ in turn. So the parent of a bottom node is the bottom node of the rightmost column with value smaller than $`s_c`$. This is the same as the parent in row 0 of a 1-Y mountain (the 1-Y mountain counts the bottom row as 0).

**Definition (edge).** If a node $`u`$ (not a phantom) has a node $`u^+`$ directly above it, there is an **edge** from $`u`$ to $`u^+`$. The left leg of $`u^+`$ is the **parent** $`\pi`$ of the edge. The parent is always in a column to the left.

```math
\mathrm{value}(u^+) = \mathrm{value}(u) - \mathrm{value}(\pi), \qquad \mathrm{row}(u^+) = \mathrm{row}(u) + \omega^{\mathrm{jump}(\mathrm{row}(u), \mathrm{row}(\pi))}
```

The jump $`\mathrm{jump}(\mathrm{row}(u), \mathrm{row}(\pi))`$ is the **degree** of the edge (`RealStoredEdge.degree` in [06](06-combinatorial-layer.md)).

**Example ($`(1, 4, 20)`$).** In the table, "$`v \leftarrow (j, h)`$" means that the value is $`v`$ and the left leg (the parent of the edge from the node below) is the node of column $`j`$ in row $`h`$. The Lean reference `Ref` uses the index from the bottom instead of the row. The left leg of the bottom row (the phantom of the left column) is not written. An ω-Y mountain has no layers as in 1-Y; the whole mountain is one table.

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

- Column 0: the bottom node has value 1, so the column ends with the phantom and the bottom node.
- Column 1: the left leg of the bottom node (value 4) is the phantom of column 0, from which the search climbs to the node of row 1 (value 1). Since $`1 \lt 4`$, it is the parent. The next node has row $`B(1, 1) = 2`$ and value 3. The left leg of the node in row 2 is $`(0, 1)`$, and column 0 has no node above it, so the parent is $`(0, 1)`$ again: row $`B(2, 1) = 2 + \omega = \omega`$ (jump 1), value 2. Likewise row $`B(\omega, 1) = \omega + \omega^2 = \omega^2`$ (jump 2), value 1, and the column ends.
- Column 2: for every node, the first candidate of step Q is already the parent. The next table lists, from the bottom node up, how the parent is found and the row and value of the next node.

| Node (row, value) | Candidates (step Q) | Parent | Row of the next node $`B`$ | Next value |
|---|---|---|---|---|
| $`1`$, 20 | The left leg is the phantom of column 1. Row $`1 \le 1`$, so climb to $`(1, 1)`$. Value 4 | $`(1, 1)`$ | $`B(1, 1) = 2`$ (jump 0) | $`20 - 4 = 16`$ |
| $`2`$, 16 | From the left leg $`(1, 1)`$, row $`2 \le 2`$, so climb to $`(1, 2)`$ (not to row $`\omega`$). Value 3 | $`(1, 2)`$ | $`B(2, 2) = 3`$ (jump 0) | $`16 - 3 = 13`$ |
| $`3`$, 13 | Left leg $`(1, 2)`$. The row $`\omega`$ above is larger than 3, so no climb. Value 3 | $`(1, 2)`$ | $`B(3, 2) = 3 + \omega = \omega`$ (jump 1) | $`13 - 3 = 10`$ |
| $`\omega`$, 10 | From the left leg $`(1, 2)`$, row $`\omega \le \omega`$, so climb to $`(1, \omega)`$. Value 2 | $`(1, \omega)`$ | $`B(\omega, \omega) = \omega + 1`$ (jump 0) | $`10 - 2 = 8`$ |
| $`\omega + 1`$, 8 | Left leg $`(1, \omega)`$. The row $`\omega^2`$ above is larger, so no climb. Value 2 | $`(1, \omega)`$ | $`B(\omega + 1, \omega) = \omega \cdot 2`$ (jump 1) | $`8 - 2 = 6`$ |
| $`\omega \cdot 2`$, 6 | Left leg $`(1, \omega)`$. No climb. Value 2 | $`(1, \omega)`$ | $`B(\omega \cdot 2, \omega) = \omega \cdot 2 + \omega^2 = \omega^2`$ (jump 2) | $`6 - 2 = 4`$ |
| $`\omega^2`$, 4 | From the left leg $`(1, \omega)`$, row $`\omega^2 \le \omega^2`$, so climb to $`(1, \omega^2)`$. Value 1 | $`(1, \omega^2)`$ | $`B(\omega^2, \omega^2) = \omega^2 + 1`$ (jump 0) | $`4 - 1 = 3`$ |
| $`\omega^2 + 1`$, 3 | Left leg $`(1, \omega^2)`$, the top of column 1. Value 1 | $`(1, \omega^2)`$ | $`B(\omega^2 + 1, \omega^2) = \omega^2 + \omega`$ (jump 1) | $`3 - 1 = 2`$ |
| $`\omega^2 + \omega`$, 2 | Likewise value 1 | $`(1, \omega^2)`$ | $`B(\omega^2 + \omega, \omega^2) = \omega^2 \cdot 2`$ (jump 2) | $`2 - 1 = 1`$ |

The parents of column 2 go up column 1 from the bottom. The first node after the parent changes lies in the same row as the parent, and its jump is 0. After that, while the parent stays the same, the jump grows to 1 and 2. When the new row reaches the row of the next node of column 1 (rows $`\omega`$ and $`\omega^2`$), step Q climbs to that node and the parent changes. The values go down by the values of the parents (4, 3, 2, 1 of column 1).

**Definition (layer).** For a row $`a \ge 1`$, the natural number $`k`$ with $`\omega^k \le a \lt \omega^{k+1}`$ is called the **layer** of $`a`$. It is the largest exponent $`i`$ with a nonzero coefficient $`c_i(a)`$. The layer of an edge $`u \to u^+`$ is the layer of the row of $`u^+`$. For example, the edges of column 1 in the example above go up to rows 2, $`\omega`$, $`\omega^2`$ from the bottom, so their layers are 0, 1, 2.

**Correspondence with the 1-Y mountain.** The 1-Y mountain ([1-Y version, study/05](https://github.com/koteitan/1y-wo-por/blob/main/study/en/05-1y-mountain.md) §2–§4) is a stack of the mountains of layers $`0, 1, 2, \ldots`$. The top value of layer $`k`$ is the value of row 0 of layer $`k + 1`$. So line up the values of column $`c`$ of 1-Y in one sequence: layer 0 from row 0 to the top, then layer 1 from row 1 to the top, then layer 2 from row 1 to the top, and so on (the top of layer $`k`$ and row 0 of layer $`k + 1`$ count as one entry). Neighbours in this sequence are joined by 1-Y parent–child edges. In the range checked by computer, the following two facts held.

1. Reading the values of the nodes of column $`c`$ of $`M(s)`$ from the bottom gives the sequence of column $`c`$ of 1-Y.
2. The edge of $`M(s)`$ that corresponds to the 1-Y edge of layer $`k`$ and row $`r`$ with parent column $`p`$ has layer $`k`$. Its parent is a node of column $`p`$ at the same position (layer $`k`$, row $`r`$) in the sequence of column $`p`$.

So in this range the ω-Y mountain is the 1-Y layers joined into one column per column, and the layer of a row stands for the 1-Y layer. The height $`h_k(c)`$ of column $`c`$ in layer $`k`$ of 1-Y is the number of edges of layer $`k`$ in column $`c`$ of $`M(s)`$.

The range checked is the 40850 expressions of length at most 6 whose last entry is not 1 and that are reached from the seeds $`(1, 2)`$, $`(1, 3)`$, $`(1, 4)`$ by repeatedly taking 1-Y expansions ($`N = 1, 2, 3`$) and prefixes (2026-09-26). Among their mountains, only that of $`(1, 4)`$ has a row $`\omega^2`$ or larger. Outside this range the facts can fail. In $`(1, 4, 15)`$, reached by 1-Y from the seed $`(1, 5)`$, the values and parents agree, but the top edge of column 2 is in layer 2 in 1-Y, while in ω-Y it is the edge to row $`\omega \cdot 2`$, in layer 1. In $`(1, 4, 16)`$ the parent of the top edge of column 2 is column 1 in 1-Y and column 0 in ω-Y, so even the parents differ. Both mountains have a row $`\omega^2`$ or larger. This is not a proof, and it is not shown in Lean.

## 4. Expansion

**Definition (expansion `expand s N`).** From an expression $`s = (s_0, \ldots, s_x)`$ and a natural number $`N`$, it makes a new expression $`s[N]`$. $`N`$ is the number of copies.

**Case 1.** If $`s`$ is empty, $`s_x = 1`$, or $`N = 0`$: delete the last column. $`s[N] = (s_0, \ldots, s_{x-1})`$ (in Lean the last column of the mountain is removed by `pop`).

**Case 2.** Otherwise the steps are (`expandDiagram`):

1. **Root.** In the mountain of $`s`$, the parent of the top edge of column $`x`$ is the **root** $`r`$. Let $`c_r`$ be the column of the root and $`w = x - c_r`$ the width.
2. **Decrement.** Build the mountain $`M(s')`$ of $`s' = (s_0, \ldots, s_{x-1}, s_x - 1)`$.
3. **Boundary rows.** In the mountain of $`s`$, list, from the top, the row of the top node of column $`x`$ and the rows of the nodes of the root column at or below the root, excluding the phantom (`boundaries`).
4. **Markers.** A node of $`M(s')`$ to the right of the root column is a **marker** (`markers`) if it is in the same row as a node $`z`$ of the root column (the root or a node below it, including the phantom) and reaches $`z`$ by following **weak parents**. The weak parent of a node $`u`$ is the parent $`\pi`$ of the edge from $`u`$ upward, provided $`\mathrm{row}(\pi) = \mathrm{row}(u)`$ (`weakParent`).
5. **Blocks.** For $`b = 1, \ldots, N`$ in order, copy the columns $`y = c_r + 1, \ldots, x`$ to the columns $`y + b w`$ (`copyBlock`, `copyColumn`). The $`w`$ columns copied in the $`b`$-th round are called **block** $`b`$.
6. **Cut.** Delete the last column (the copy of column $`x`$ in block $`N`$). Read the value of the bottom node of each column (`valuesOf`).

The length of $`s[N]`$ is $`x + N w`$. The columns left of column $`x`$ stay the columns of $`M(s)`$, and column $`x`$ is column $`x`$ of $`M(s')`$.

**Copying a column (`copyColumn`).** When column $`y`$ is copied in block $`b`$, the edges of column $`y`$ of $`M(s')`$ are called the **source edges**. Write $`\mathrm{col}(p)`$ for the number of the column of a node $`p`$. For each marker $`\mu`$ of $`y`$, three kinds of nodes are placed.

- **Translation** (`copyEdge`): a node in row $`\mathrm{row}(\mu)`$. Let $`\ell`$ be the left leg of $`\mu`$. The left leg of the new node is the same node $`\ell`$ if $`\ell`$ is left of the root column. Otherwise it is the highest node of column $`\mathrm{col}(\ell) + b w`$ whose row is below $`\mathrm{row}(\mu)`$. A phantom marker is copied to a phantom.
- **Contour** (`contour`): first fix the reference row $`g`$. In the current last column (the copy of column $`x`$ in block $`b-1`$; for $`b = 1`$, column $`x`$ of $`M(s')`$), take for each boundary row the highest node strictly below it (`below`). $`g`$ is the row of the last of these whose row is at least $`\mathrm{row}(\mu)`$ (`referenceAt`). Then copy the source edges upward from $`\mu`$ in order. Stop before an edge whose upper node is another marker. Stop at the top of the column. A source edge of degree $`d`$ becomes an edge from the current row $`h`$ to the row $`h + \omega^d`$; the first $`h`$ is $`g`$. The left leg is the image of the parent of the source edge, by the same rule as for translation.
- **Fill** (`fill`, the weak magma): let $`p`$ be the parent of the source edge from $`\mu`$ upward. For every node $`q`$ of column $`\mathrm{col}(p) + b w`$ with $`\mathrm{row}(\mu) \le \mathrm{row}(q) \lt g`$, let $`q^+`$ be the node directly above $`q`$, and place nodes in rows $`\mathrm{row}(q) + \omega^i`$ for $`i = \mathrm{jump}(\mathrm{row}(q), \mathrm{row}(q^+)) - 1, \ldots, 0`$. The left leg of each is $`q`$. The nodes placed by the fill are called **gap nodes**.

Finally the nodes are sorted by row (`finish`). The top node gets value 1, and the values are set from top to bottom by $`\mathrm{value}(u) = \mathrm{value}(u^+) + \mathrm{value}(\pi)`$, where $`\pi`$ is the left leg of $`u^+`$ (`backfill`).

**Remark (column $`x`$).** Let $`u_0, \ldots, u_t`$ be the nodes of column $`x`$ of $`M(s)`$ from the bottom ($`u_t`$ is the top). Column $`x`$ of $`M(s')`$ has nodes with the same rows and the same left legs as $`u_0, \ldots, u_{t-1}`$, and their values are 1 smaller. So the edges below the top edge of column $`x`$ of $`M(s)`$ are the same in $`M(s')`$.

Proof. By induction on $`j`$. For $`j = 0`$ both are the bottom node in row 1, and the left leg is the phantom of column $`x - 1`$. Let $`j \le t - 2`$. Since $`u_{j+1}`$ is not the top, its value is at least 2. So the value of the parent $`\pi_j`$ of $`u_j`$ is $`\mathrm{value}(u_j) - \mathrm{value}(u_{j+1}) \le \mathrm{value}(u_j) - 2`$, and the value of $`u_j`$ is at least 3. The node of $`M(s')`$ in the same row has value at least 2, so it is not the top and a parent is searched. Then the candidates appear in the same order (the candidates depend on rows and left legs, and the columns left of $`x`$ are the same). A candidate rejected in $`M(s)`$ has value 0 or at least $`\mathrm{value}(u_j)`$, so it is also rejected for the value that is 1 smaller. $`\pi_j`$ has value at most $`\mathrm{value}(u_j) - 2`$, so it is also the parent for the value that is 1 smaller. Hence the next node has the same row and left leg, and its value is 1 smaller. The value of $`u_{t-1}`$ is the value of the root plus 1, so in $`M(s')`$ the root is not the parent, and from there up the column may differ from $`M(s)`$. ∎

### Branch tree

The edges of the mountain of $`s[N]`$ in case 2 are sorted into the following branches. The branch numbers are the same as those of the 1-Y expansion ([1-Y version, study/05](https://github.com/koteitan/1y-wo-por/blob/main/study/en/05-1y-mountain.md) §6, step 1). In the checked range, a branch makes the same edges as the 1-Y branch with the same number (see "Correspondence with the 1-Y expansion" below). Branch (4) does not exist in 1-Y.

The branches do not change how edges are placed. Every edge is placed by one of the steps above (decrement, translation, contour, fill). The branches only give that edge a number.

**Definition (root layer $`K`$).** $`K`$ is the layer (§3) of the top edge of column $`x`$ of $`M(s)`$ (the edge whose parent is the root).

Some words.

- As in §3, the layer and the parent of an edge $`u \to u^+`$ are the layer of the row of $`u^+`$ and the left leg of $`u^+`$. An edge whose upper node is a gap node is called a "gap edge". Edges whose upper nodes were placed by translation or contour are called "translation edges" and "contour edges".
- A translation edge or a contour edge has the source edge it was copied from (for translation, the source edge going up to $`\mu`$; for contour, the copied source edge). If the row of the upper node of the edge equals the row of the upper node of its source edge, the edge is said to be **copied in the same row**. Translation edges always are. Contour edges are if $`g = \mathrm{row}(\mu)`$.
- A column $`c \gt x`$ is the copy of column $`y`$ in block $`b \ge 1`$, with $`c = y + b w`$. Let $`\ell`$ be the layer of the edge.

The branches are as follows.

- **(0)** When $`s`$ is empty or $`s_x = 1`$ (case 1): delete the last column. This is the 1-Y case "no bad root". In case 1 with $`N = 0`$ and $`s_x \gt 1`$, no branch is passed. In 1-Y too, only the unchanged branches are passed then, and the result is again the expression with the last column deleted.
- **(1) $`\ell \gt K`$ (layers above the root)**
  - (1-1) Columns $`\lt x`$: unchanged (edges of $`M(s)`$).
  - (1-2) The edges of column $`x`$ (edges of $`M(s')`$), and the edges of columns $`c \gt x`$ copied in the same row. The parent of the edge is the parent of the source edge copied by the translation rule.
- **(2) $`\ell = K`$ (the root layer)**
  - (2-1) Columns $`\lt x`$: unchanged.
  - (2-2) Edges of columns $`c \gt x`$ with $`y \lt x`$, copied in the same row.
  - (2-3) The edges of column $`x`$, and the edges of columns $`c \gt x`$ with $`y = x`$ copied in the same row. This is the 1-Y "first column of a block". It splits by the column of the parent of the edge.
    - (2-3-1) The parent of the edge is in the root column or to its right. In columns $`c \gt x`$, the parent of the edge is in the column of the parent of the source edge shifted by $`b w`$.
    - (2-3-2) The parent of the edge is left of the root column. In columns $`c \gt x`$, the parent of the edge is the same node as the parent of the source edge.
- **(3) $`\ell \lt K`$ (layers below the root)**
  - (3-1) Columns $`\lt x`$: unchanged.
  - (3-2) Columns $`\ge x`$. The edges of column $`x`$ below its top edge are unchanged (the remark above). In the checked range, all edges of column $`x`$ in layers $`\lt K`$ were there (in 1-Y too, column $`x`$ is shifted 0 times and stays unchanged). The edges of columns $`c \gt x`$ are as follows.
    - (3-2-1) When column $`c`$ has a gap node in layer $`\ell`$:
      - (3-2-1-1) Translation edges.
      - (3-2-1-2) Gap edges with $`i = 0`$. The upper node is in row $`\mathrm{row}(q) + 1`$, and the parent of the edge is $`q`$ in column $`\mathrm{col}(p) + b w`$.
      - (3-2-1-3) Contour edges not copied in the same row whose layer is the layer of the source edge. They are the source edges copied upward from row $`g`$.
    - (3-2-2) Otherwise: edges copied in the same row.
- **(4) Branches not in 1-Y**: edges that fall in none of (1)–(3).
  - (4-1) Gap edges with $`i \ge 1`$.
  - (4-2) Contour edges whose layer differs from the layer of the source edge.
  - (4-3) All others.

**Example ($`(1, 3, 3)[2]`$).** The result is $`(1, 3, 2, 5, 4, 9)`$.

**Branches passed.** (2-2): columns 3, 5 in layer 1. (3-2-1-2), (3-2-1-3): columns 3, 4, 5 in layer 0.

$`M(1, 3, 3)`$ is as follows (read the table as in the example of §3).

| Row | Column 0 | Column 1 | Column 2 |
|---|---|---|---|
| $`\omega`$ | | $`1 \leftarrow (0, 1)`$ | $`1 \leftarrow (0, 1)`$ |
| $`2`$ | | $`2 \leftarrow (0, 1)`$ | $`2 \leftarrow (0, 1)`$ |
| $`1`$ | $`1`$ | $`3`$ | $`3`$ |
| $`0`$ | phantom | phantom | phantom |

- The root is $`(0, 1)`$, so $`c_r = 0`$ and $`w = 2`$. The top edge of column 2 goes from row 2 to row $`\omega`$, so $`K = 1`$. $`s' = (1, 3, 2)`$. Column 2 of $`M(s')`$ has value 2 in row 1 and $`1 \leftarrow (0, 1)`$ in row 2.
- The boundary rows are $`(\omega, 1)`$. The markers are, in each of columns 1 and 2, the node in row 1 and the phantom (checked with `#eval`).
- References of block 1: in column 2 of $`M(s')`$, the highest node below row $`\omega`$ is in row 2, and the highest node below row 1 is the phantom (row 0).

Block 1 copies column 1 to column 3.

| Node | Kind | Branch | Reason |
|---|---|---|---|
| row 1 | translation | (the bottom node, not an edge) | marker $`(1, 1)`$; the left leg is the phantom of column 2 |
| row 2, left leg $`(2, 1)`$ | fill | (3-2-1-2) | the parent of the source edge $`(1,1) \to (1,2)`$ is $`(0, 1)`$; in column $`0 + 2 = 2`$, $`q = (2, 1)`$ has $`1 \le 1 \lt g = 2`$; $`\mathrm{jump}(1, 2) = 1`$, so only $`i = 0`$, row $`1 + \omega^0 = 2`$ |
| row 3, left leg $`(2, 2)`$ | contour | (3-2-1-3) | the source edge $`(1,1) \to (1,2)`$ has degree 0; $`g + \omega^0 = 3`$; this differs from the upper row 2 of the source edge; the layer is 0 in both |
| row $`\omega`$, left leg $`(2, 2)`$ | contour | (2-2) | the source edge $`(1,2) \to (1,\omega)`$ has degree 1; $`3 + \omega = \omega`$; the upper row is $`\omega`$ as for the source edge; layer $`1 = K`$, $`y = 1 \lt x`$ |

Column 3 has a gap node (row 2) in layer 0, so its edges in layer 0 go to branch (3-2-1). From the top, the values are $`1`$, $`1 + \mathrm{value}(2,2) = 2`$, $`2 + \mathrm{value}(2,2) = 3`$, $`3 + \mathrm{value}(2,1) = 5`$. So column 3 has value 5. In the same way column 4 (the copy of column 2) gets value 4. Block 2 makes columns 5 and 6, and column 6 is cut.

Columns 3–5 of `expandDiagram [1,3,3] 2`:

| Row | Column 3 | Column 4 | Column 5 |
|---|---|---|---|
| $`\omega`$ | $`1 \leftarrow (2, 2)`$ | | $`1 \leftarrow (4, 3)`$ |
| $`4`$ | | | $`2 \leftarrow (4, 3)`$ |
| $`3`$ | $`2 \leftarrow (2, 2)`$ | $`1 \leftarrow (2, 2)`$ | $`3 \leftarrow (4, 2)`$ |
| $`2`$ | $`3 \leftarrow (2, 1)`$ | $`2 \leftarrow (2, 1)`$ | $`5 \leftarrow (4, 1)`$ |
| $`1`$ | $`5`$ | $`4`$ | $`9`$ |

Column 5 is the copy of column 1 in block 2. The source parent $`(0, 1)`$ is copied to column $`0 + 2 \cdot 2 = 4`$. Block 2 takes its references from column 4. The highest node of column 4 below the boundary row $`\omega`$ is in row 3. So $`g = 3`$, and the contour of column 5 starts at row $`3 + 1 = 4`$. The fill uses the nodes of column 4 in rows 1 and 2 as parents and places nodes in rows 2 and 3. Column 5 has one more node than column 3. In the 1-Y version this is branch (3-2-1): the copy in block 2 is stretched by 2 rows in layer 0.

### Correspondence with the 1-Y expansion

Identify the edges of ω-Y and 1-Y by "Correspondence with the 1-Y mountain" in §3. Then the words of the expansion correspond as follows. The 1-Y symbols are those of the 1-Y version, study/05 §3–§6.

| 1-Y | ω-Y |
|---|---|
| the edge of column $`c`$ in layer $`k`$ from row $`r`$ to $`r + 1`$ | the $`(r + 1)`$-th edge from the bottom among the edges of column $`c`$ in layer $`k`$ |
| height $`h_k(c)`$ | the number of edges of column $`c`$ in layer $`k`$ |
| parent $`\mathrm{par}_{k,r}(c)`$ | the column of the parent of that edge |
| column $`z`$ and layer $`K`$ of the bad root | the root column $`c_r`$ and the root layer $`K`$ |
| row $`d`$ of the bad root | the number of edges of layer $`K`$ in column $`c_r`$ below the root |
| $`L = x - z`$ | width $`w`$ |
| column $`z + i L + j`$ ($`j \ge 1`$) | the copy of column $`c_r + j`$ in block $`i`$ |
| column $`z + i L`$ ($`j = 0`$, $`i \ge 2`$) | the copy of column $`x`$ in block $`i - 1`$ |
| column $`x`$ ($`i = 1`$, $`j = 0`$) | column $`x`$ of $`M(s')`$ (decrement) |
| shift $`m_i`$ | the translation rule (left of the root column: unchanged; otherwise: column shifted by $`b w`$) |
| number of shifts $`b`$ in branch (3-2) | block number $`b`$ |
| in a layer $`k \lt K`$, the column copied from is above $`z`$ | the column has a gap node in layer $`k`$ |

Branches with the same number do the same thing, as follows. The minimal example is the lexicographically smallest expression, in the checked range, that passes the branch with $`N = 2`$.

| Branch | What 1-Y does | What ω-Y does | Minimal example |
|---|---|---|---|
| (0) | no bad root; delete the last column | empty or $`s_x = 1`$; delete the last column | $`(1)`$ |
| (1-1), (2-1), (3-1) | unchanged | columns $`\lt x`$ unchanged | |
| (1-2) | layer $`\gt K`$; copy column $`z + j`$ shifted $`i`$ times | layer $`\gt K`$; column $`x`$ is the decremented mountain, the others are copied in the same row | $`(1, 3, 2)`$ |
| (2-2) | layer $`K`$, $`j \ge 1`$; copy shifted | layer $`K`$, $`y \lt x`$; copy in the same row | $`(1, 2, 2)`$ |
| (2-3-1) | layer $`K`$, $`j = 0`$, row $`\lt d`$; the parent of $`x`$ shifted $`i - 1`$ times | layer $`K`$, column $`x`$ and its copies; parent in the root column or to its right | $`(1, 2, 4)`$ |
| (2-3-2) | layer $`K`$, $`j = 0`$, row $`\ge d`$; the parent of $`z`$ used as is | layer $`K`$, column $`x`$ and its copies; parent left of the root column, the same node | $`(1, 2, 3)`$ |
| (3-2-1-1) | layer $`\lt K`$, above $`z`$, row $`\lt f`$; copy shifted | layer $`\lt K`$, a layer with gap nodes; translation edges | $`(1, 3, 2, 5)`$ |
| (3-2-1-2) | stretch by $`b e`$ rows from row $`f`$; the parent is $`\mathrm{par}_{k,f}(\sigma) + b L`$ | gap edges with $`i = 0`$; the parent is $`q`$ in column $`\mathrm{col}(p) + b w`$ | $`(1, 3)`$ |
| (3-2-1-3) | row $`\ge f + b e`$; copy lifted by $`b e`$ rows | contour edges whose row is raised, in the same layer | $`(1, 3)`$ |
| (3-2-2) | layer $`\lt K`$, not above $`z`$; copy shifted | layer $`\lt K`$, a layer without gap nodes; copy in the same row | $`(1, 3, 4, 2, 5, 6, 5)`$ |
| (4-1) | none | gap edges with $`i \ge 1`$ | $`(1, 4)`$ |
| (4-2) | none | contour edges whose layer differs from the source edge | $`(1, 4)`$ |
| (4-3) | none | none of (1)–(3), (4-1), (4-2) | $`(1, 3, 10)`$ |

"The parent is in one column" in 1-Y branch (3-2-1-2) corresponds to the weak-magma rule "the left legs of the gap nodes all lie in one column" (§5). 1-Y branches (3-2-1-1) and (3-2-2) both copy with a shift and without changing the row. In ω-Y both become copies in the same row, and the only difference is whether that layer has gap nodes.

**Checked range.** The following was checked by computer (2026-09-26). It is not a proof, and it is not shown in Lean.

- For the same 40850 expressions as in §3, of the 122550 expansions with $`N = 1, 2, 3`$, the 122548 other than $`(1, 4)[2]`$ and $`(1, 4)[3]`$ give the same values in ω-Y and 1-Y. In these, the mountain of $`s[N]`$ also has, under the correspondence of §3, the same values and parents as the copied 1-Y mountain (1-Y version, study/05 §6, step 1), and the layers of the edges equal the 1-Y layers. For all edges of columns $`x`$ and beyond (about 4.33 million), the number in the branch tree equals the 1-Y branch number. Branch (4) did not occur.
- $`(1, 4)[2]`$ and $`(1, 4)[3]`$ give different values (ω-Y: $`(1, 3, 10)`$, $`(1, 3, 10, 37)`$; 1-Y: $`(1, 3, 9)`$, $`(1, 3, 9, 27)`$). Both pass (4-1) and (4-2).
- For the 3542 expressions of length at most 5 reached from the same seeds by ω-Y expansions (10626 expansions), too, the values differ from 1-Y only for $`(1, 4)[2]`$ and $`(1, 4)[3]`$. For length at most 6, 30000 expansions chosen at random from 546090 showed no difference. But in expressions not reached in 1-Y, such as $`(1, 3, 10) = (1, 4)[2]`$, the layers can shift as at the end of §3, and 957 expansions passed (4-3). Their values were the same as the values computed by the 1-Y rule.
- For expressions whose mountain $`M(s)`$ has the same values and parents as in 1-Y, the expansions whose values differ from 1-Y were exactly the expansions that pass (4-1) (checked on the range above and on the expressions of length at most 4 reached by ω-Y from the seed $`(1, 5)`$). (4-1) and (4-2) occurred only when $`K \ge 2`$.
- For the 532 expressions of length at most 4 reached by 1-Y from the seed $`(1, 5)`$ (1596 expansions), 378 expansions give different values, and the correspondence of the numbers fails. These mountains have rows $`\omega^2`$ or larger.

The minimal examples were found by going through, in lexicographic order, the expressions reached from the ω-Y seeds by expansions and prefixes (length at most 8, entries at most 12, up to $`(1, 3, 4, 2, 5, 6, 5)`$; for branch (4), length at most 5, entries at most 40, up to $`(1, 4)`$). The minimal examples of branches (0)–(3) are the same as in the 1-Y version.

**Why branch (4) is not in 1-Y.** 1-Y branch (3-2-1) stretches the column by $`b e`$ rows from row $`f`$, separately for each layer $`k`$ below the root. The stretched rows and the lifted rows stay in layer $`k`$. The ω-Y fill fills the rows from $`\mathrm{row}(\mu)`$ up to $`g`$ at once, for each marker $`\mu`$. If the jump from $`q`$ to $`q^+`$ is 2 or more, it places nodes in rows $`\mathrm{row}(q) + \omega^i`$ with $`i \ge 1`$. Such a node is in a higher layer than $`q`$ ((4-1)). The contour starts at $`g`$, so if the layer of $`g`$ is larger than the layer of the source edge, the copied edge moves to a higher layer ((4-2)). Both happen when a layer boundary lies between $`\mathrm{row}(\mu)`$ and $`g`$. The 1-Y branches have no such form. In the checked range, every expansion that passes (4-3) is an expansion of an expression whose rows of $`M(s)`$ have layers shifted from the 1-Y layers (end of §3). In such expressions even the numbers (1)–(3) can differ from the 1-Y branches. For example, in $`(1, 3, 10)[2]`$ of §6, the edge to row $`\omega`$ of column 3 is (2-3-1) in ω-Y and (3-2-1-1) in 1-Y.

**Example ($`(1, 4)[2]`$).** The result is $`(1, 3, 10)`$, which differs from $`(1, 3, 9)`$ of 1-Y.

**Branches passed.** (3-2-1-2): column 2 in layer 0. (3-2-1-3), (4-1), (4-2): column 2 in layer 1.

- Column 1 of $`M(1, 4)`$ has, like column 1 in the example of §3, the values 4, 3, 2, 1 in rows 1, 2, $`\omega`$, $`\omega^2`$. The root is $`(0, 1)`$, $`c_r = 0`$, $`w = 1`$, $`K = 2`$.
- $`s' = (1, 3)`$, and column 1 of $`M(s')`$ has the values 3, 2, 1 in rows 1, 2, $`\omega`$. The boundary rows are $`(\omega^2, 1)`$, and the markers are $`(1, 1)`$ and the phantom.
- The references of block 1 are the highest node of column 1 of $`M(s')`$ below row $`\omega^2`$ (row $`\omega`$) and the phantom below row 1. For $`\mu = (1, 1)`$, $`g = \omega`$.

Column 2 is as follows.

| Row | value ← left leg | Kind | Branch |
|---|---|---|---|
| $`\omega \cdot 2`$ | $`1 \leftarrow (1, \omega)`$ | contour (source edge $`(1, 2) \to (1, \omega)`$) | (3-2-1-3) |
| $`\omega + 1`$ | $`2 \leftarrow (1, \omega)`$ | contour (source edge $`(1, 1) \to (1, 2)`$, moved from layer 0 to layer 1) | (4-2) |
| $`\omega`$ | $`3 \leftarrow (1, 2)`$ | fill ($`q = (1, 2)`$, $`q^+ = (1, \omega)`$, jump 2, $`i = 1`$) | (4-1) |
| $`3`$ | $`5 \leftarrow (1, 2)`$ | fill ($`q = (1, 2)`$, $`i = 0`$) | (3-2-1-2) |
| $`2`$ | $`7 \leftarrow (1, 1)`$ | fill ($`q = (1, 1)`$, $`i = 0`$) | (3-2-1-2) |
| $`1`$ | $`10`$ | translation (the bottom node) | |

In 1-Y, column 2 has 2 edges in layer 0 and 2 edges in layer 1, and its values from the bottom are 9, 6, 4, 2, 1. The parents of the edges correspond to the nodes in rows 1, 2, 2, $`\omega`$ of the sequence of column 1. In ω-Y, column 2 has 2 edges in layer 0 and 3 edges in layer 1. The extra edge is the (4-2) edge $`\omega \to \omega + 1`$, and it makes the bottom value larger by the value 1 of its parent ($`10 = 9 + 1`$).

## 5. Weak magma and the official ω-Y

The official ω-Y is defined by `expand` in Naruyoko's program ([notes/00-survey.md](../../notes/00-survey.md) §1.2). The fill rule of §4 is called the **weak magma** rule. Weak-magma ω-Y is ω-Y with the expansion of §4. It does not agree with the official ω-Y. On 3001 expressions reached from $`(1, 3)`$, $`(1, 4)`$, $`(1, 5)`$ by repeatedly taking official expansions and prefixes, 480 of the 9003 expansions with $`N = 1, 2, 3`$ give different results (notes/00-survey.md §1.6).

According to [notes/02-feasibility.md](../../notes/02-feasibility.md) §2, only the fill rule differs.

- weak: the left legs of the gap nodes all lie in one column $`\mathrm{col}(p) + b w`$, where $`p`$ is the parent of the source edge from $`\mu`$ upward.
- official: for each gap row, choose one node of the root column (how it is chosen is in notes/02-feasibility.md §2.2). Let $`z`$ be the node of column $`y`$ of $`M(s')`$ in the row of the chosen node. Let $`y'`$ be the column of the left leg of $`z`$ ($`y' = y - 1`$ if $`z`$ is in the bottom row). The left legs of the gap nodes lie in the copy of column $`y'`$ ($`y' + b w`$ if $`y' \ge c_r`$, and $`y'`$ if $`y' \lt c_r`$).

**Example.** In $`(1, 3, 3)[2]`$, the left leg of the node in row 2 of column 4 (a gap node) is $`(2, 1)`$ (value 2) in weak and $`(3, 1)`$ (value 5) in the official version. The bottom value of column 4 is $`2 + 2 = 4`$ in weak and $`2 + 5 = 7`$ in the official version. In total, weak gives $`(1, 3, 2, 5, 4, 9)`$ and the official version $`(1, 3, 2, 5, 7, 12)`$ (the official values are from notes/02-feasibility.md §2.3 and were not computed in Lean).

notes/02-feasibility.md counts the bottom row as 0: it writes $`\delta`$ for the Lean row $`1 + \delta`$. In that note "$`k \leftarrow c_j@h`$" is a node in row $`k`$ whose left leg is the node of column $`j`$ in row $`h`$. For example "$`1 \leftarrow c_2@0`$" in that note is "row 2, left leg $`(2, 1)`$" in this note.

Termination of the official ω-Y is not a theorem of this repository. The official ω-Y is treated in [koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por).

**On "no extraction".** Phyrion calls this variant "weak magma, no extraction". The proof for the 1-Y sequence has a step called extraction. The Lean definition of ω-Y has no step corresponding to it (the table in notes/00-survey.md §3.5). It uses a single mountain whose rows are ordinals. The exact meaning of the extraction rule in ω-Y has not been checked (notes/00-survey.md §1.5).

## 6. Examples of expansion

The values were computed with Phyrion's JavaScript reference implementation (2026-09-26). The rows with ✓ in the column "Lean" gave the same values with `#eval Expansion.expand s N` (Lean 4.33.1, 2026-09-23).

"Branches passed" lists the numbers of the branches of the branch tree of §4 that the edges of the mountain fall in, and (0) for case 1 with $`s_x = 1`$. The unchanged branches (1-1), (2-1), (3-1) are not listed. ★ marks the lexicographically smallest expression, in the checked range, that passes the branch with $`N = 2`$ (§4). The column "1-Y" is the value of the same expression expanded by the 1-Y rule (1-Y version, study/05 §6). "same" means the same value as ω-Y.

| Expression $`s`$ | $`N`$ | $`s[N]`$ | Branches passed | 1-Y | Lean |
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

$`(1, 3, 10)`$ is not reached from the seeds in 1-Y ("Checked range" in §4). Its expansion gives the same value under the 1-Y rule, but it passes (4-3) because the layers of the ω-Y rows are shifted from the 1-Y layers.

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
| finding the parent | `climb`, `nextCandidate`, `findParent` | same |
| building the mountain | `growColumn`, `buildColumn`, `build` | same |
| expansion | `expandDiagram`, `expand`, `valuesOf` | [OmegaY/Expansion/Build.lean](../../OmegaY/Expansion/Build.lean) |
| markers | `weakParent`, `weakReaches`, `markers` | same |
| copying columns | `copyEdge`, `contour`, `fill`, `below`, `referenceAt`, `copyColumn`, `copyBlock` | same |
| restoring values | `finish`, `backfill` | same |
| layers, branch tree, correspondence with 1-Y | none (not defined in Lean; only checked by computer) | |
| one expansion step | `Dynamics.next`, `Dynamics.Step`, `Dynamics.next_lex` | [OmegaY/Expansion/LegalDynamics.lean](../../OmegaY/Expansion/LegalDynamics.lean) |
| preservation of the dimension | `expandDiagram_key_dimension`, `Dynamics.next_key_dimension`, `Dynamics.fixed_dimension_for_descendants` | [OmegaY/Expansion/SupportedDimension.lean](../../OmegaY/Expansion/SupportedDimension.lean), [OmegaY/Expansion/DynamicsRowBound.lean](../../OmegaY/Expansion/DynamicsRowBound.lean) |
| final theorems | `omegaY_step_wellFounded` and the others | [OmegaY/Expansion/WellFounded.lean](../../OmegaY/Expansion/WellFounded.lean) |
