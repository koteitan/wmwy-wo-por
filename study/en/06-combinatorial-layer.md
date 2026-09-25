[← Back](README.md) | [English](06-combinatorial-layer.md) | [Japanese](../06-combinatorial-layer.md)

# Phyrion's combinatorial layer for ω-Y

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | label, $`\omega_1`$, $`\mathrm{Fin}\ n`$, $`\mathrm{Option}`$ |
| [02 Well-founded relations and recursion](02-well-founded.md) | keys $`\mathrm{Key}_m`$, coordinate, top, termination by a bound on labels (§6) |
| [05 The ω-Y sequence and its mountain](05-omegay-mountain.md) | expression, legal, row, jump, mountain, node, edge, father, degree, root, block, expansion, dimension, $`\mathrm{col}`$ |

This note explains the part of Phyrion's proof that does not use the meaning of the labels. This part is called the **combinatorial layer**. This layer proves well-foundedness of expansion using only three theorems (§5) about the label relation $`R`$. This repository uses the layer unchanged ([NOTICE](../../NOTICE)). Most of it is in the 549 modules of `OmegaY/`; this note explains only its entry and exit points.

- $`R(\theta, a, b)`$ is a relation with three arguments: $`\theta`$ is a key, and $`a`$ and $`b`$ are labels. The combinatorial layer does not use the definition of $`R`$.
- The part that defines $`R`$ and proves the three theorems of §5 is called the **semantic layer** (§10). The semantic layer of this repository is explained in [07](07-relation-r.md)–[09](09-obligations.md).
- Among the files of `OmegaY/`, `Reflection.lean`, `Reflection/`, `KeyReflection.lean` and `Model.lean` are short files that only connect the combinatorial layer with the semantic layer. They are called the **thin files**. The remaining files are called the **core**.

## 1. Keys and templates

**Definition (key syntax `KeySyntax`).** Let $`\mathrm{Label}`$ be the type of labels and $`\mathrm{Key}`$ the type of keys, both linear orders. Let $`n`$ be a natural number; the points numbered $`0, \ldots, n-1`$ are called **vertices**. In ω-Y the vertices are the columns of a mountain. A key syntax consists of three things ([OmegaY/Reflection/Interface.lean](../../OmegaY/Reflection/Interface.lean)). It is the same as the key syntax of [03](03-sigma1-elementary.md) §7.

- `Template n`: the type of **templates** over $`n`$ vertices.
- `eval t f`: the key obtained by evaluating the template $`t`$ at the vertex labels $`f : \mathrm{Fin}\ n \to \mathrm{Label}`$.
- `monotone_eval`: if $`g \le f`$ pointwise, then $`\mathrm{eval}\ t\ g \le \mathrm{eval}\ t\ f`$.

**Templates of ω-Y (`OmegaY.Keys`).** A template for keys of length $`m`$ puts a vertex number or $`\top`$ in each coordinate.

```math
\mathrm{Template}_{m,n} = \mathrm{Fin}\ m \to \mathrm{Option}(\mathrm{Fin}\ n), \qquad (\mathrm{eval}\ t\ f)_i = \begin{cases} \top & (t_i = \mathrm{none}) \cr f(j) & (t_i = \mathrm{some}\ j) \end{cases}
```

As a key syntax this is `KeyReflection.vectorSyntax m`, and `Model.keySyntax m` is another name for it.

**Example.** Let $`m = 2`$ and $`n = 3`$. For $`t = (\mathrm{some}\ 0, \mathrm{none})`$, $`\mathrm{eval}\ t\ f = (f(0), \top)`$. For $`t' = (\mathrm{some}\ 0, \mathrm{some}\ 2)`$, $`\mathrm{eval}\ t'\ f = (f(0), f(2))`$.

| Name | Content |
|---|---|
| `Keys.eval_mono` | if $`g \le f`$ pointwise, then $`\mathrm{eval}\ t\ g \le \mathrm{eval}\ t\ f`$ |
| `Keys.templateKey t` | $`\mathrm{eval}\ t\ \mathrm{id}`$: the key obtained by using the vertex numbers themselves as labels |
| `Keys.eval_lt_of_template_lt` | if $`f`$ is strictly increasing and $`\mathrm{templateKey}\ t \lt \mathrm{templateKey}\ s`$, then $`\mathrm{eval}\ t\ f \lt \mathrm{eval}\ s\ f`$ |
| `Keys.relabel t μ`, `Keys.eval_relabel` | the template with vertices renamed by a map of vertices $`\mu : \mathrm{Fin}\ n \to \mathrm{Fin}\ n'`$; for labels $`h : \mathrm{Fin}\ n' \to \mathrm{Label}`$ of the new vertices, $`\mathrm{eval}(\mathrm{relabel}\ t\ \mu)\ h = \mathrm{eval}\ t\ (h \circ \mu)`$ |
| `Keys.shared_root_before_infinity` | $`(a, a) \lt (a, \top)`$ for a label $`a`$ |

Because of `eval_lt_of_template_lt`, comparing keys reduces to comparing column numbers. Keys can be compared combinatorially, before any labels are chosen.

## 2. Internal atoms and top atoms

**Definition (atoms).** Let $`S`$ be a key syntax and $`n`$ the number of vertices. The following two kinds, each carrying a template $`t`$ over $`n`$ variables, are called **atoms** ([OmegaY/Reflection/Interface.lean](../../OmegaY/Reflection/Interface.lean)). The parent $`p`$ and the child $`q`$ are vertices. $`f : \mathrm{Fin}\ n \to \mathrm{Label}`$ gives the labels of the vertices. $`b`$ is a label called the **top** ([02](02-well-founded.md) §3). The top is not the label of any vertex.

| Lean | Components | What holds (labels $`f`$) |
|---|---|---|
| `InternalAtom S n` | template, parent $`p`$, child $`q`$, $`p \lt q`$ | $`R(\mathrm{eval}\ t\ f,\ f(p),\ f(q))`$ |
| `TopAtom S n` | template, parent $`p`$ | for a top $`b`$: $`R(\mathrm{eval}\ t\ f,\ f(p),\ b)`$ |

A **graph** with $`n`$ vertices is a pair of a list $`G`$ of internal atoms and a list $`N`$ of top atoms. A top atom is an edge to a point $`b`$ outside the graph. A top atom is also called a **demand**. The key of an atom is $`\mathrm{eval}\ t\ f`$.

| Lean | Meaning |
|---|---|
| `InternalHolds S R G f` | every internal atom of $`G`$ holds at $`f`$ |
| `TopHolds S R N f b` | every top atom of $`N`$ holds for the top $`b`$ |
| `KeysBelow S N f θ` | every atom of $`N`$ has key below $`\theta`$ |
| `Bounded f b` | $`f(i) \lt b`$ for every $`i`$ |

## 3. Scale roots and the keys of mountain edges

Each mountain edge gets a key template ([OmegaY/Geometry/MountainKeys.lean](../../OmegaY/Geometry/MountainKeys.lean)).

**Definition (edge).** `RealStoredEdge` is a triple of a node `lower` that is not a phantom, the node `upper` directly above it, and the left leg `parent` of `upper` (the edges of [05](05-omegay-mountain.md) §3). The **degree** is $`d = \mathrm{jump}(\mathrm{row}(\mathrm{lower}), \mathrm{row}(\mathrm{parent}))`$ (`degree`).

**Definition (scale root).** Let $`k`$ be a natural number. The **scale-$`k`$ father** of a node $`u`$ is the father of the edge from $`u`$ upward, if that edge has degree at most $`k`$ (`scaleParent`). Following scale-$`k`$ fathers until there is none gives the **scale-$`k`$ root** $`\rho_k(u)`$ (`scaleRoot`). A larger scale allows more edges to be followed, so the root is in the same column or further left (`scaleRoot_scale_antitone`).

**Definition (dimension).** If every row of a mountain has coefficient 0 at all exponents above $`D`$, then $`D`$ is a **dimension** of the mountain (`MountainKeyDimension`). Every finite mountain has one (`exists_key_dimension`). The degree of each edge is at most $`D`$ (`degree_le`).

**Definition (the key of an edge, `keyTemplate`).** For an edge $`e`$ (father $`\pi`$, degree $`d`$) of a mountain of dimension $`D`$, the template has length $`m = D + 1`$, and coordinate $`i`$ corresponds to scale $`D - i`$.

```math
\kappa_D(e) = \bigl(\mathrm{col}\,\rho_D(\pi),\ \mathrm{col}\,\rho_{D-1}(\pi),\ \ldots,\ \mathrm{col}\,\rho_d(\pi),\ \underbrace{\top, \ldots, \top}_{d}\bigr)
```

There are $`D + 1 - d`$ finite coordinates, and each names a column at or left of the father's column (`keyTemplate_column_bound`). The child's column is never named.

**Example.** The values below were checked with `#eval` of a small function that follows the definitions of `keyTemplate` and `scaleRoot`. $`f_j`$ is the label of column $`j`$.

| Expression | $`D`$ | Edge (column, rows) | Father | Degree | Key |
|---|---|---|---|---|---|
| $`(1, 3)`$ | 1 | column 1, $`1 \to 2`$ | $`(0, 1)`$ | 0 | $`(f_0, f_0)`$ |
| | | column 1, $`2 \to \omega`$ | $`(0, 1)`$ | 1 | $`(f_0, \top)`$ |
| $`(1, 4)`$ | 2 | column 1, $`1 \to 2`$ | $`(0, 1)`$ | 0 | $`(f_0, f_0, f_0)`$ |
| | | column 1, $`2 \to \omega`$ | $`(0, 1)`$ | 1 | $`(f_0, f_0, \top)`$ |
| | | column 1, $`\omega \to \omega^2`$ | $`(0, 1)`$ | 2 | $`(f_0, \top, \top)`$ |
| $`(1, 3, 5)`$ | 1 | column 2, $`1 \to 2`$ | $`(1, 1)`$ | 0 | $`(f_0, f_0)`$ |
| | | column 2, $`2 \to \omega`$ | $`(0, 1)`$ | 1 | $`(f_0, \top)`$ |

The first edge of column 2 of $`(1, 3, 5)`$ has its father in column 1, but its key names column 0. The edge from the father $`(1, 1)`$ upward has degree 0 and father $`(0, 1)`$. A key names the roots of the father, not the father itself.

**Theorem (`key_strict_in_column`).** Of two edges in the same column, the lower edge has a strictly smaller key than the upper edge (for strictly increasing labels). In each column of the table above, keys also increase upward.

## 4. Representations

**Definition (representation `KeyRepresentation hF D`).** Fix a mountain and a dimension $`D`$ of it (§3). In Lean a mountain is written `Frame`, and `hF` is a proof of the shape condition of the mountain (`Frame.Ordered`). $`\mathit{width}`$ is the number of columns of the mountain. A **representation** of the mountain is a labelling of its columns $`f : \mathrm{Fin}\ \mathit{width} \to \mathrm{Label}`$ with ([OmegaY/Geometry/RepresentedMountain.lean](../../OmegaY/Geometry/RepresentedMountain.lean)):

1. $`f`$ is strictly increasing (`strictMono`).
2. every $`f(i)`$ is below $`\omega_1`$ (`bounded`).
3. for every edge $`e`$ (father $`\pi`$, lower node $`\mathrm{lower}`$), $`R_{D+1}(\mathrm{eval}\ \kappa_D(e)\ f,\ f(\mathrm{col}\,\pi),\ f(\mathrm{col}\,\mathrm{lower}))`$ (`edges`).

$`R_{D+1}`$ is the relation `Model.R (D + 1)` for keys of length $`D + 1`$.

**Example.** A representation of $`(1, 3, 5)`$ is $`f_0 \lt f_1 \lt f_2 \lt \omega_1`$ with:

```math
R((f_0, f_0), f_0, f_1), \quad R((f_0, \top), f_0, f_1), \quad R((f_0, f_0), f_1, f_2), \quad R((f_0, \top), f_0, f_2)
```

| Name | Content |
|---|---|
| `keyRepresentation_exists` | every mountain has a representation (from `initial_finite_graph`, §5) |
| `KeyRepresentation.restrict` | a restriction to a prefix of the columns is a representation |
| `KeyRepresentation.lastLabel` | the label of the last column |
| `restrict_below_last` | the labels of a restriction to a proper prefix are all below the old last label |

## 5. The three theorems

The combinatorial layer uses only the following three theorems from the semantic layer ([notes/01-design.md](../../notes/01-design.md) §1). $`R`$ is `Reflection.R S`, and $`\mathrm{top}`$ is $`\omega_1`$. $`\theta, \Theta`$ are keys and $`a, b, \beta`$ are labels. $`n`$ is the number of vertices and $`(G, N)`$ a graph with $`n`$ vertices (§2). We write $`f \lt b`$ when $`f(i) \lt b`$ for all $`i`$.

**Theorem (`key_weaken`).** If $`\theta \le \Theta`$ and $`R(\Theta, a, b)`$, then $`R(\theta, a, b)`$.

**Theorem (`finite_reflection`).** Assume:

1. $`f : \mathrm{Fin}\ n \to \mathrm{Label}`$ is strictly increasing and $`f \lt b`$ (`Bounded f b`).
2. the internal atoms of $`G`$ hold at $`f`$.
3. the top atoms of $`N`$ have keys below $`\theta`$, and $`N`$ holds for the top $`b`$.
4. for a vertex $`\mathrm{cut} \in \mathrm{Fin}\ n`$, $`R(\theta, f(\mathrm{cut}), b)`$. This vertex is called the **cut**, and this relation the **control relation**.

Then there is $`g : \mathrm{Fin}\ n \to \mathrm{Label}`$ with:

1. $`g`$ strictly increasing and $`g \lt f(\mathrm{cut})`$.
2. $`g(i) = f(i)`$ for $`i \lt \mathrm{cut}`$.
3. $`g \le f`$ pointwise.
4. $`G`$ holds at $`g`$, and $`N`$ holds for the top $`f(\mathrm{cut})`$.

The columns named by keys need not be before the cut.

**Theorem (`initial_finite_graph`).** For every graph $`(G, N)`$ there are $`\beta \lt \omega_1`$ and a strictly increasing $`f \lt \beta`$ such that $`G`$ holds at $`f`$ and $`N`$ holds for the top $`\beta`$.

## 6. Splicing one block

One finite reflection adds one block of columns ([OmegaY/Splice.lean](../../OmegaY/Splice.lean)). The vertices of the graph are called columns. Let $`n`$ be the number of columns and $`\mathrm{cut}`$ the cut (§5).

**Definition (column maps).** The new number of columns is $`n + (n - \mathrm{cut})`$ (`Splice.width`). The maps below send an old column $`i \in \mathrm{Fin}\ n`$ to a new column.

| Lean | Map |
|---|---|
| `old i` | $`i \mapsto i`$ |
| `moved i` | $`i`$ if $`i \lt \mathrm{cut}`$, otherwise $`n + (i - \mathrm{cut})`$ |
| `boundary` | column $`n`$ ($`= \mathrm{moved}(\mathrm{cut})`$) |

**Definition (new labels `labels cut f g`).** $`f`$ are the old labels and $`g`$ the labels given by finite reflection (§5). New column $`i \lt n`$ gets $`g(i)`$, and column $`i \ge n`$ gets $`f(\mathrm{cut} + i - n)`$. So the labels of the old columns $`\mathrm{cut}, \ldots, n - 1`$ appear unchanged at the right end.

**Example.** For $`n = 4`$ and $`\mathrm{cut} = 1`$ the new labels are:

```math
(g_0, g_1, g_2, g_3, f_1, f_2, f_3), \qquad g_0 = f_0,\quad g_1, g_2, g_3 \lt f_1
```

**Theorem (`reflected_block`).** Under the assumptions of finite reflection in §5, for the $`g`$ given by the reflection, `labels cut f g` is strictly increasing and below $`b`$. The atoms of $`G`$ mapped by `old` hold at the new labels (the columns of `old` carry the labels $`g`$). The atoms mapped by `moved` also hold at the new labels (the columns of `moved` carry the labels $`f`$).

**Definition (classification `Classified`).** An atom $`e`$ of a graph on the new columns is **classified** if it is one of:

1. an atom of $`G`$ mapped by `old`.
2. an atom whose parent and child are the parent and child of an atom $`s`$ of $`G`$ mapped by `moved`, and whose template key $`\mathrm{templateKey}`$ (§1) is at most the key of the template of $`s`$ renamed by `moved` (`relabel`, §1) (a copy with a weaker key).
3. a `seamAtom` made from a demand $`\tau \in N`$: parent the column `old` of the parent of $`\tau`$, child `boundary`.

**Theorem (`classified_graph_represented`).** If every atom of the new graph is classified, the whole graph holds at the new labels. Kind 1 follows from the reflection, kind 2 from `key_weaken` (`holds_weakened_copy`), and kind 3 from the fact that the demands hold for the top $`f(\mathrm{cut})`$ and that the label of `boundary` is $`f(\mathrm{cut})`$ (`holds_seam`).

## 7. Repeated reflection with reservoirs

Expansion adds blocks $`N`$ times. For this the facts needed by the next reflection are carried along as **reservoirs**. A reservoir is a list of atoms: a list $`F`$ of internal atoms (the **internal reservoir**) and a list $`T`$ of top atoms (the **top reservoir**) ([OmegaY/Splice/Reservoirs.lean](../../OmegaY/Splice/Reservoirs.lean), [OmegaY/Splice/IteratedReservoirs.lean](../../OmegaY/Splice/IteratedReservoirs.lean)).

**Definition (`ReservoirState G F T control f β`).** $`G`$ is the list of internal atoms of the current graph, $`F`$ the internal reservoir, and $`T`$ the top reservoir. `control` is a top atom, called the **control atom**; write $`t_c`$ for its template. $`f`$ are the labels of the columns and $`\beta`$ is a label (the top). `ReservoirState G F T control f β` means that the following six hold.

| Field | Content |
|---|---|
| `strict`, `bounded` | $`f`$ is strictly increasing and $`f \lt \beta`$ |
| `graph` | the current graph $`G`$ holds |
| `internal` | the internal reservoir $`F`$ holds |
| `virtual` | the top reservoir $`T`$ holds for the top $`\beta`$ |
| `controlled` | $`R(\mathrm{eval}\ t_c\ f,\ f(\mathrm{control.parent}),\ \beta)`$ |

**Theorem (`splice_reservoirs`).** Assume: a state `ReservoirState G F T control f β`; every atom of the list $`N`$ of demands has an atom of $`T`$ with the same parent and a template key $`\mathrm{templateKey}`$ (§1) at least as large (`DemandCovered`); the template keys of the atoms of $`N`$ are strictly below the template key of the control atom; and the atoms of the new graph $`H`$ are `ReservoirClassified` (the three kinds of §6, with kind 2 taken from $`F`$ and kind 3 being demands with weaker keys). Then one finite reflection with cut `control.parent` gives a state with the same $`\beta`$ for $`H`$ and the `moved` images of $`F`$, $`T`$ and `control`.

The reflection is given $`G`$ and $`F`$ together. That the demand keys are below the control key gives `KeysBelow` for finite reflection.

**Definition (block indices).** Let $`x`$ be the number of the last column of the original expression. Without the last column there are $`x`$ columns. Let $`y`$ be the root column ($`c_r`$ of [05](05-omegay-mountain.md) §4). $`b`$ is the number of a block, and $`i \in \mathrm{Fin}\ x`$ an original column.

| Lean | Value |
|---|---|
| `blockWidth x y b` | $`x + b(x - y)`$ |
| `blockCut b` | $`y + b(x - y)`$ |
| `blockSource b i` | $`i`$ if $`i \lt y`$, otherwise $`i + b(x - y)`$ |

**Theorem (`iterated_reservoirs`).** If there is a state for block 0, and in each block the demands are covered by the top reservoir (`DemandCovered`), the demand keys are below the control key, and the graph of the next block is classified, then there is a state for block $`b`$ for every $`b`$. $`\beta`$ does not change. The cut of block $`b`$ is `blockCut b`.

## 8. Descent of the last label

**Theorem (`ActualRepresentationDescent`, `actual_representation_descent`).** Let $`s = (s_0, \ldots, s_x)`$ be a nonempty legal expression, $`D`$ a dimension of its mountain, and $`f`$ a representation of its mountain. $`f(x)`$ is the label of the last column, called the **last label**. Then for every natural number $`N`$ there is a representation $`f'`$ (dimension $`D`$) of the mountain of $`s[N]`$ whose labels are all below $`f(x)`$.

**Case 1 (the last column is deleted).** Restrict $`f`$ to the prefix (`expandDiagram_trivial_representation_descent`). The labels are all below $`f(x)`$ (`restrict_below_last`).

**Case 2 (blocks are copied).** Notation (`RootGeometry`, [OmegaY/Expansion/InitialControlKeys.lean](../../OmegaY/Expansion/InitialControlKeys.lean)):

- **control edge**: the top edge of column $`x`$ (`controlEdge`). Its father is the root $`r`$.
- **lower edges**: the edges of column $`x`$ below the control edge (`LowerEdge`). Their keys are strictly below the key of the control edge (`lower_key_strict`, from `key_strict_in_column` of §3).
- $`\beta = f(x)`$.

The state of block 0 is made from the old labels $`f(0), \ldots, f(x - 1)`$ ([OmegaY/Expansion/ActualInitialReservoir.lean](../../OmegaY/Expansion/ActualInitialReservoir.lean)).

| Component | Content |
|---|---|
| $`G_0`$ | the edges of the mountain without column $`x`$ |
| $`F`$ | the same edges (`initialSpliceFacts`), moved by `blockSource` in each block |
| $`T`$ | the lower edges as top atoms, with column $`x`$ read as the top $`\beta`$ (`initialSpliceVirtualFacts`) |
| control | the control edge read in the same way as a top atom (`initialSpliceControl`); its parent is the root column |

Each of these is an edge relation of the old representation $`f`$ itself, so it holds without any reflection.

Next, `splice_reservoirs` of §7 is applied from block $`b`$ to block $`b + 1`$ (`iterated_actual_reservoirs`). What is needed is that every edge of the mountain of block $`b+1`$ is `ReservoirClassified` (`actual_splice_edge_classified`). This is a finite fact about the shape of the expansion program, and it uses the weak-magma fill rule ([05](05-omegay-mountain.md) §5). Its core is the following two facts ([notes/02-feasibility.md](../../notes/02-feasibility.md) §3.1, §4.2).

- **Key bound for copied edges** (`ActualCopiedKeyBound`): an edge $`e`$ of a new block has a source edge $`e'`$ of $`M(s')`$ ([05](05-omegay-mountain.md) §4). The father column and child column of $`e`$ are the copies of those of $`e'`$. The key of $`e`$ is at most the copy of the key of $`e'`$.
- **Classification of fill edges** (`ActualFillCopiedKey`): the key of an edge to a gap node ([05](05-omegay-mountain.md) §4) is below the key of a copied edge with the same endpoint columns. So it is handled from the bound of that copied edge by `key_weaken`.

The labels of the state of block $`N`$ form a representation of the mountain of $`s[N]`$ (`representationOfSpliceGraph`). They are all below $`\beta = f(x)`$ (`represent_actual_expansion`).

**Example ($`(1, 3, 3)`$).** $`x = 2`$, and the root column is 0. The control edge is the edge $`2 \to \omega`$ of column 2, with key $`(f_0, \top)`$. The lower edge is the edge $`1 \to 2`$ of column 2, with key $`(f_0, f_0)`$. $`\beta = f_2`$.

- Block 0: labels $`(f_0, f_1)`$. The control relation is $`R((f_0, \top), f_0, f_2)`$, and the top reservoir is $`R((f_0, f_0), f_0, f_2)`$.
- Block 0 → 1: the cut is $`0`$. Reflection gives $`g_0 \lt g_1 \lt f_0`$. The new labels are $`(g_0, g_1, f_0, f_1)`$.
- Block 1 → 2: the cut is $`2`$, with label $`f_0`$. Reflection gives $`g'_2 \lt g'_3 \lt f_0`$; columns 0 and 1 do not move. The new labels are $`(g_0, g_1, g'_2, g'_3, f_0, f_1)`$.

This is a representation of $`(1, 3, 3)[2] = (1, 3, 2, 5, 4, 9)`$, and every label is below $`f_2`$. Which edge falls into which kind is shown by `actual_splice_edge_classified` in Lean.

**Well-foundedness.** $`D`$ does not change along descendants ([05](05-omegay-mountain.md) §7). From the theorem above and the induction of [02](02-well-founded.md) §6 (`accessible_of_representation_below`), $`\prec`$ is well-founded (`step_wellFounded_of_actual_representation_descent`). The first representation comes from `keyRepresentation_exists`.

## 9. Where the three theorems are used

These are the calls in the core (see the beginning of this note) found with `grep` (excluding the thin files `Reflection.lean`, `Reflection/`, `KeyReflection.lean` and `Model.lean`).

| Theorem | Called from |
|---|---|
| `key_weaken` | `Splice.holds_weakened_copy` ([OmegaY/Splice.lean](../../OmegaY/Splice.lean)), `DemandCovered.top_holds`, `holds_weakened_seam` ([OmegaY/Splice/Reservoirs.lean](../../OmegaY/Splice/Reservoirs.lean)), `ActualCopiedKeyBound.represented` ([OmegaY/Expansion/ActualCopiedKeyLabels.lean](../../OmegaY/Expansion/ActualCopiedKeyLabels.lean)) |
| `finite_reflection` | `Splice.reflected_block`, `Splice.splice_reservoirs`, `RootGeometry.reflect_initial_control` ([OmegaY/Expansion/InitialControlKeys.lean](../../OmegaY/Expansion/InitialControlKeys.lean)) |
| `initial_finite_graph` | `actual_keys_initially_represented` ([OmegaY/Geometry/MountainKeys.lean](../../OmegaY/Geometry/MountainKeys.lean)); the list of demands is empty |

## 10. What is left for the semantic layer

The combinatorial layer does not ask why finite reflection holds. The job of the **semantic layer** is to supply an $`R`$ satisfying the three theorems of §5.

- Phyrion's semantic layer: $`R(\theta, a, b)`$ says "finite positive graphs below $`b`$ can be compressed below $`a`$" (the meaning of the words is in [04](04-patterns-of-resemblance.md) §5 and [notes/00-survey.md](../../notes/00-survey.md) §3.2). It is not included in this repository.
- The semantic layer of this repository: $`R`$ is the relation of $`\Sigma_1`$-elementary substructures of [07 The relation R](07-relation-r.md). The proofs are in [09 Proofs of the three theorems](09-obligations.md).

## 11. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "Structure of the proof" | the two layers and the table of the three theorems |
| [notes/01-design.md](../../notes/01-design.md) §1 | the names the core uses from the semantic layer |
| [notes/00-survey.md](../../notes/00-survey.md) §3.2, §3.5 | keys, keys of mountain edges, preservation of the dimension, correspondence with 1-Y |
| [notes/02-feasibility.md](../../notes/02-feasibility.md) §3, §4 | in the official ω-Y the upper bound on the keys of copied edges fails |
| [OmegaY/Reflection/Interface.lean](../../OmegaY/Reflection/Interface.lean) | the definitions of §1 and §2 (Phyrion's, copied unchanged) |

## 12. Lean correspondence

| Concept | Lean | File |
|---|---|---|
| key syntax | `KeySyntax` | [OmegaY/Reflection/Interface.lean](../../OmegaY/Reflection/Interface.lean) |
| atoms and what holds | `InternalAtom`, `TopAtom`, `InternalHolds`, `TopHolds`, `KeysBelow`, `Bounded` | same |
| keys and templates of ω-Y | `Keys.Key`, `Keys.Template`, `Keys.eval`, `Keys.eval_mono`, `Keys.templateKey`, `Keys.eval_lt_of_template_lt`, `Keys.relabel` | [OmegaY/Keys.lean](../../OmegaY/Keys.lean) |
| the concrete key syntax | `KeyReflection.vectorSyntax`, `Model.keySyntax`, `Model.R` | [OmegaY/KeyReflection.lean](../../OmegaY/KeyReflection.lean), [OmegaY/Model.lean](../../OmegaY/Model.lean) |
| scale roots | `scaleParent`, `scaleRoot`, `scaleRoot_scale_antitone` | [OmegaY/Geometry/MountainKeys.lean](../../OmegaY/Geometry/MountainKeys.lean) |
| edges and their keys | `RealStoredEdge`, `degree`, `keyTemplate`, `keyTemplate_column_bound`, `atom` | same |
| material for the first representation | `actual_keys_initially_represented` | same |
| keys increase in a column | `key_strict_in_column` | [OmegaY/Geometry/VerticalEdgeKeys.lean](../../OmegaY/Geometry/VerticalEdgeKeys.lean) |
| representations | `KeyRepresentation`, `keyRepresentation_exists`, `restrict`, `lastLabel` | [OmegaY/Geometry/RepresentedMountain.lean](../../OmegaY/Geometry/RepresentedMountain.lean) |
| one block | `Splice.width`, `old`, `moved`, `boundary`, `labels`, `reflected_block`, `Classified`, `classified_graph_represented` | [OmegaY/Splice.lean](../../OmegaY/Splice.lean) |
| reservoirs | `ReservoirState`, `DemandCovered`, `ReservoirClassified`, `splice_reservoirs` | [OmegaY/Splice/Reservoirs.lean](../../OmegaY/Splice/Reservoirs.lean) |
| repeating blocks | `blockWidth`, `blockCut`, `blockSource`, `iterated_reservoirs` | [OmegaY/Splice/BlockIndices.lean](../../OmegaY/Splice/BlockIndices.lean), [OmegaY/Splice/IteratedReservoirs.lean](../../OmegaY/Splice/IteratedReservoirs.lean) |
| control edge and lower edges | `controlEdge`, `LowerEdge`, `controlAtom`, `lowerAtom`, `lower_key_strict` | [OmegaY/Expansion/InitialControlKeys.lean](../../OmegaY/Expansion/InitialControlKeys.lean) |
| actual blocks | `iterated_actual_reservoirs`, `represent_actual_expansion` | [OmegaY/Expansion/ActualSpliceRepresentation.lean](../../OmegaY/Expansion/ActualSpliceRepresentation.lean) |
| classification of actual edges | `actual_splice_edge_classified` | [OmegaY/Expansion/ActualSpliceGeometry.lean](../../OmegaY/Expansion/ActualSpliceGeometry.lean) |
| state of block 0 | `zero_reservoir`, `initialSpliceFacts`, `initialSpliceVirtualFacts`, `initialSpliceControl` | [OmegaY/Expansion/ActualInitialReservoir.lean](../../OmegaY/Expansion/ActualInitialReservoir.lean), [OmegaY/Expansion/ActualSpliceFacts.lean](../../OmegaY/Expansion/ActualSpliceFacts.lean) |
| descent | `ActualRepresentationDescent`, `actual_representation_descent` | [OmegaY/Expansion/DynamicsRepresentationRank.lean](../../OmegaY/Expansion/DynamicsRepresentationRank.lean), [OmegaY/Expansion/ActualRepresentationDescent.lean](../../OmegaY/Expansion/ActualRepresentationDescent.lean) |
| well-foundedness | `accessible_of_representation_below`, `step_wellFounded_of_actual_representation_descent` | [OmegaY/Expansion/DynamicsRepresentationRank.lean](../../OmegaY/Expansion/DynamicsRepresentationRank.lean) |
