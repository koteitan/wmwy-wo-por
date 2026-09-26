[← Back](README.md) | [English](06-combinatorial-layer.md) | [Japanese](../06-combinatorial-layer.md)

# Phyrion's combinatorial layer for ω-Y

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | labels $`\mathrm{Label}`$ (§6), $`\mathrm{Fin}\ n`$, $`\mathrm{Option}`$ (§7) |
| [02 Well-founded relations and well-founded recursion](02-well-founded.md) | well-founded, accessible, well-founded induction (§1, §2), keys $`\mathrm{Key}_m`$ and their order, $`\top`$, top (§3), termination by an upper bound of labels (§6) |
| [03 Structures and Σ₁-elementary substructures](03-sigma1-elementary.md) | key syntax, template, $`\mathcal T_n`$, $`\mathrm{eval}`$, the key syntax of ω-Y (§7) |
| [05 The ω-Y sequence and its mountain](05-omegay-mountain.md) | expression, row, coefficient, jump, next row $`B`$, mountain $`M(s)`$, $`\mathrm{next}`$, node, $`\mathrm{col}`$, $`\mathrm{row}`$, $`\mathrm{top}(c)`$, parent $`\mathrm{par}_a(c)`$, edge, lower node, degree $`\delta_c(a)`$, root $`(z, d)`$, expansion $`s[N]`$, block, $`L`$, shift $`m_i`$, one-step expansion $`\prec`$, dimension (§7) |

This note explains the combinatorial layer of Phyrion's proof. This layer takes a relation $`R`$ as argument (§2), does not use what the values of the labels are, and proves well-foundedness of expansion from three theorems about $`R`$ (§5). This repository uses the theorem of this layer as it is.

## 1. Diagrams

**Definition (atom).** Let $`m, n \in \mathbb N`$; $`m`$ is the length of keys and $`n`$ the number of columns. An **atom** is a triple $`e = (t, p, q)`$. It represents one parent–child edge ([05](05-omegay-mountain.md) §3).

- $`t \in \mathcal T_n`$: a template. It belongs to the key syntax of ω-Y of [03](03-sigma1-elementary.md) §7, so $`\mathcal T_n = \mathrm{Fin}\ m \to \mathrm{Option}(\mathrm{Fin}\ n)`$. It computes the key of the edge from the labels of the columns. It replaces the layer $`k`$ and the root column $`r`$ of the 1-Y version.
- $`p \in \mathbb N`$: the column number of the parent.
- $`q \in \mathbb N`$: the column number of the child.

$`p`$, $`q`$ and the $`j`$ of a template coordinate $`t_i = \mathrm{some}\ j`$ are all column numbers (natural numbers). The labels attached to columns are defined in §2.

It is **valid** for size $`n`$ if $`p \lt q \lt n`$.

**Definition (diagram).** A **diagram** is a size $`n`$ together with a finite list of valid atoms. $`n \in \mathbb N`$ is the number of columns, and the columns are numbered $`0, 1, \ldots, n - 1`$. We write $`e \in G`$ when $`e`$ is in the list of atoms of the diagram $`G`$.

- In the diagram of an expression $`s = (s_0, \ldots, s_{n-1})`$, $`n`$ is the length of the expression.

**Definition (the key read on column numbers).** Natural numbers are ordinals below $`\omega_1`$, so they are labels. For a template $`t \in \mathcal T_n`$, write $`\bar t`$ for the key obtained by evaluating $`t`$ with the column numbers themselves as labels.

```math
\bar t := \mathrm{eval}\ t\ \mathrm{id}, \qquad \bar t_i = \begin{cases} j & (t_i = \mathrm{some}\ j) \cr \top & (t_i = \mathrm{none}) \end{cases}
```

In the tables below a template $`t`$ is written as $`\bar t`$. For example, $`\bar t = (0, \top)`$ means $`t = (\mathrm{some}\ 0, \mathrm{none})`$.

**Property 1 (keys are compared by column numbers).** If $`f : \mathrm{Fin}\ n \to \mathrm{Label}`$ is strictly increasing, then for templates $`t, t'`$:

```math
\bar t \le \bar t' \implies \mathrm{eval}\ t\ f \le \mathrm{eval}\ t'\ f, \qquad \bar t \lt \bar t' \implies \mathrm{eval}\ t\ f \lt \mathrm{eval}\ t'\ f
```

**Proof.** If $`\bar t_i = \bar t'_i`$ then $`t_i = t'_i`$, so coordinate $`i`$ of the two keys is equal. If the first different coordinate $`i`$ has $`\bar t_i \lt \bar t'_i`$, then $`t_i = \mathrm{some}\ j`$ and either $`t'_i = \mathrm{some}\ j'`$ ($`j \lt j'`$) or $`t'_i = \mathrm{none}`$. In the first case $`f(j) \lt f(j')`$; in the second $`f(j) \lt \top`$. $`\square`$

So the order of keys can be decided from column numbers alone, before the labels are chosen.

**Definition (mapping by a map of columns).** Let $`\mu`$ be a map of column numbers. The template $`\mu t`$ obtained by mapping $`t`$ with $`\mu`$ is

```math
(\mu t)_i := \begin{cases} \mathrm{some}\ \mu(j) & (t_i = \mathrm{some}\ j) \cr \mathrm{none} & (t_i = \mathrm{none}) \end{cases}
```

The atom $`e = (t, p, q)`$ mapped by $`\mu`$ is $`\mu e := (\mu t, \mu(p), \mu(q))`$. The list of all atoms of a diagram $`G`$ mapped by $`\mu`$ is written $`\mu G`$.

**Property 2.** For every list of labels $`h`$, $`\mathrm{eval}\ (\mu t)\ h = \mathrm{eval}\ t\ (h \circ \mu)`$. If $`\mu`$ is strictly increasing, then $`\bar t \le \bar t' \implies \overline{\mu t} \le \overline{\mu t'}`$ and $`\bar t \lt \bar t' \implies \overline{\mu t} \lt \overline{\mu t'}`$.

**Proof.** The first holds because every coordinate is $`h(\mu(j))`$ or $`\top`$. The second is the proof of Property 1 again ($`j \lt j'`$ implies $`\mu(j) \lt \mu(j')`$). $`\square`$

**Definition (prefix).** Let $`n' \le n`$. The **prefix of size $`n'`$** of a diagram $`G`$ of size $`n`$ is the diagram of size $`n'`$ that keeps only the atoms $`(t, p, q)`$ of $`G`$ with $`q \lt n'`$. We assume that the templates of the kept atoms point only to columns below $`n'`$ (for diagrams of expressions this always holds, by Property 3 below).

**Definition (scale root).** Consider the mountain $`M(s)`$ of an expression $`s`$. Let $`k \in \mathbb N`$. The **scale-$`k`$ root** $`\rho_k(u)`$ of a node $`u = (c, a)`$ is

```math
\rho_k(c, a) := \begin{cases} \rho_k\bigl(\mathrm{par}_a(c)\bigr) & (1 \le a \lt \mathrm{top}(c),\ \delta_c(a) \le k) \cr (c, a) & (\text{otherwise}) \end{cases}
```

If the edge upward from $`u`$ has degree at most $`k`$, move to the parent of that edge; otherwise stop. Parents are in columns to the left, so the recursion stops, and $`\mathrm{col}(\rho_k(u)) \le \mathrm{col}(u)`$.

**The diagram of an expression.** Choose an expression $`s`$ and a dimension $`D`$ of $`M(s)`$ ([05](05-omegay-mountain.md) §7). The diagram $`G_D(s)`$ of the expression has one atom for each edge of $`M(s)`$. The length of keys is $`m = D + 1`$. For an edge $`e`$ with lower node $`(c, a)`$, parent $`\pi = \mathrm{par}_a(c)`$ and degree $`\delta = \delta_c(a)`$, it contains the atom

```math
\bigl(\kappa_D(e),\ \mathrm{col}(\pi),\ c\bigr)
```

where $`\kappa_D(e)`$ is the template of the edge $`e`$; coordinate $`i`$ corresponds to scale $`D - i`$.

```math
\kappa_D(e)_i := \begin{cases} \mathrm{some}\ \mathrm{col}\bigl(\rho_{D-i}(\pi)\bigr) & (\delta \le D - i) \cr \mathrm{none} & (\delta \gt D - i) \end{cases}
```

So, with $`f(j)`$ the label of column $`j`$, the key of the edge is

```math
\mathrm{eval}\ \kappa_D(e)\ f = \Bigl(f\bigl(\mathrm{col}\,\rho_D(\pi)\bigr),\ f\bigl(\mathrm{col}\,\rho_{D-1}(\pi)\bigr),\ \ldots,\ f\bigl(\mathrm{col}\,\rho_\delta(\pi)\bigr),\ \underbrace{\top, \ldots, \top}_{\delta}\Bigr)
```

**Property 3.** For an edge $`e`$ (lower node $`(c, a)`$, parent $`\pi`$, degree $`\delta`$):

1. $`\delta \le D`$.
2. If $`\kappa_D(e)_i = \mathrm{some}\ j`$ then $`j \le \mathrm{col}(\pi) \lt c`$. The template points only to columns at or left of the parent's column. It never points to the child's column.

**Proof.** 1: the row of the upper node is $`a + \omega^{\delta}`$ ([05](05-omegay-mountain.md) §3), whose coefficient $`c_\delta`$ is at least 1 ("adding a power of ω" in [05](05-omegay-mountain.md) §2). By the definition of dimension, $`\delta \le D`$. 2: $`\mathrm{col}(\rho_k(\pi)) \le \mathrm{col}(\pi)`$, and the parent is in a column to the left. $`\square`$

**Property 4 (keys increase within a column).** If $`e, e'`$ are two edges of the same column and the row of the lower node of $`e`$ is below that of $`e'`$, then $`\bar\kappa_D(e) \lt \bar\kappa_D(e')`$. It is not proved here.

Property 4 was checked with a Python program that transcribes the formulas of 05 §3, §4, on the mountains of the same range of expressions as the lemma of §7 (2026-09-27).

| Expression | $`D`$ | Atoms $`(\bar t, p, q)`$ |
|---|---|---|
| $`(1, 2, 2)`$ | 0 | $`((0), 0, 1)`$, $`((0), 0, 2)`$ |
| $`(1, 2, 4)`$ | 0 | $`((0), 0, 1)`$, $`((0), 1, 2)`$, $`((1), 1, 2)`$ |
| $`(1, 3)`$ | 1 | $`((0, 0), 0, 1)`$, $`((0, \top), 0, 1)`$ |
| $`(1, 4)`$ | 2 | $`((0, 0, 0), 0, 1)`$, $`((0, 0, \top), 0, 1)`$, $`((0, \top, \top), 0, 1)`$ |
| $`(1, 3, 5)`$ | 1 | $`((0, 0), 0, 1)`$, $`((0, \top), 0, 1)`$, $`((0, 0), 1, 2)`$, $`((0, \top), 0, 2)`$ |

The values in the table were computed with a Python program that transcribes the definitions of this section (2026-09-27). The $`D`$ in the table is the smallest dimension (the largest exponent of a nonzero coefficient of a row of the mountain).

**Example (the atoms of $`(1, 2, 4)`$).** First build the mountain ([05](05-omegay-mountain.md) §3). The table is read as in the example of [05](05-omegay-mountain.md) §3: "$`v \leftarrow (p, e)`$" means value $`v`$ with left leg (the parent of the edge below) the node $`(p, e)`$.

| Row | column 0 | column 1 | column 2 |
|---|---|---|---|
| $`3`$ | | | $`1 \leftarrow (1, 2)`$ |
| $`2`$ | | $`1 \leftarrow (0, 1)`$ | $`2 \leftarrow (1, 1)`$ |
| $`1`$ | $`1`$ | $`2`$ | $`4`$ |

- Column 1: $`\mathrm{par}_1(1) = (0, 1)`$ (value $`1 \lt 2`$), the next row is $`B(1, 1) = 2`$ and its value $`2 - 1 = 1`$ ends the column.
- Column 2: $`\mathrm{par}_1(2) = (1, 1)`$ (value $`2 \lt 4`$), the next row is $`B(1, 1) = 2`$ with value $`4 - 2 = 2`$. In row 2, $`\mathrm{next}(2, 2) = (1, \max(\{1\} \cup \{0, 1, 2\})) = (1, 2)`$, whose value is $`1 \lt 2`$, so the parent is $`(1, 2)`$. The next row is $`B(2, 2) = 3`$ and its value $`2 - 1 = 1`$ ends the column.
- All rows are below $`\omega`$, so $`D = 0`$. Keys have length 1, and coordinate 0 corresponds to scale 0. Every edge has degree 0, so coordinate 0 is finite.

So there are 3 edges, and each becomes one atom. The size is $`n = 3`$.

| Edge (column, rows) | Parent $`\pi`$ | Degree $`\delta`$ | How to find $`\rho_0(\pi)`$ | Atom $`(\bar t, p, q)`$ | Validity $`p \lt q \lt 3`$ |
|---|---|---|---|---|---|
| column 1, $`1 \to 2`$ | $`(0, 1)`$ | $`\mathrm{jump}(1, 1) = 0`$ | $`(0, 1)`$ is the top of column 0 and has no edge upward. Root $`(0, 1)`$ | $`((0), 0, 1)`$ | $`0 \lt 1 \lt 3`$ |
| column 2, $`1 \to 2`$ | $`(1, 1)`$ | $`\mathrm{jump}(1, 1) = 0`$ | the edge upward from $`(1, 1)`$ has degree $`0 \le 0`$; move to its parent $`(0, 1)`$. Root $`(0, 1)`$ | $`((0), 1, 2)`$ | $`1 \lt 2 \lt 3`$ |
| column 2, $`2 \to 3`$ | $`(1, 2)`$ | $`\mathrm{jump}(2, 2) = 0`$ | $`(1, 2)`$ is the top of column 1. Root $`(1, 2)`$ | $`((1), 1, 2)`$ | $`1 \lt 2 \lt 3`$ |

- The second and third atoms are both the edge with parent 1 and child 2, but their templates differ ($`(0)`$ and $`(1)`$). That is why they are different atoms.
- The edge of the third atom is the top edge of column 2, and its parent $`(1, 2)`$ is the root of $`(1, 2, 4)`$ ([05](05-omegay-mountain.md) §4).
- The atoms of the 1-Y version are $`(0, 0, 0, 1)`$, $`(0, 0, 1, 2)`$, $`(0, 1, 1, 2)`$. In this example the root column $`r`$ of the 1-Y atom $`(k, r, p, q)`$ has become the template $`(r)`$.

**Example (the atoms of $`(1, 3)`$).** This expression has an edge of degree 1.

| Row | column 0 | column 1 |
|---|---|---|
| $`\omega`$ | | $`1 \leftarrow (0, 1)`$ |
| $`2`$ | | $`2 \leftarrow (0, 1)`$ |
| $`1`$ | $`1`$ | $`3`$ |

- Column 1: $`\mathrm{par}_1(1) = (0, 1)`$ (value $`1 \lt 3`$), the next row is $`B(1, 1) = 2`$ with value $`3 - 1 = 2`$. In row 2, $`\mathrm{next}(1, 2) = (0, \max(\{1\} \cup \{0, 1\})) = (0, 1)`$, whose value is $`1 \lt 2`$, so the parent is $`(0, 1)`$. Since $`\mathrm{jump}(2, 1) = 1`$, the next row is $`B(2, 1) = \omega`$ and its value $`2 - 1 = 1`$ ends the column.
- The coefficient $`c_1`$ of row $`\omega`$ is 1, so $`D = 1`$. Keys have length 2; coordinate 0 corresponds to scale 1 and coordinate 1 to scale 0.

| Edge (column, rows) | Parent $`\pi`$ | Degree $`\delta`$ | How to find the template | Atom $`(\bar t, p, q)`$ | Validity $`p \lt q \lt 2`$ |
|---|---|---|---|---|---|
| column 1, $`1 \to 2`$ | $`(0, 1)`$ | 0 | both coordinates 0 and 1 have $`\delta \le D - i`$. $`\rho_1(0, 1) = \rho_0(0, 1) = (0, 1)`$ | $`((0, 0), 0, 1)`$ | $`0 \lt 1 \lt 2`$ |
| column 1, $`2 \to \omega`$ | $`(0, 1)`$ | 1 | coordinate 0: $`1 \le 1`$, so $`\mathrm{col}\,\rho_1(0, 1) = 0`$. Coordinate 1: $`1 \gt 0`$, so $`\top`$ | $`((0, \top), 0, 1)`$ | $`0 \lt 1 \lt 2`$ |

- The two atoms have the same parent and child; only the templates differ. In the 1-Y version only the layer $`k`$ differed ($`(0, 0, 0, 1)`$ and $`(1, 0, 0, 1)`$).
- The template $`(0, 0)`$ of the lower edge is below the template $`(0, \top)`$ of the upper edge (Property 4). The upper edge is the top edge of column 1, and its parent $`(0, 1)`$ is the root ([05](05-omegay-mountain.md) §4).

**Example ($`(1, 3, 5)`$).** The first edge $`1 \to 2`$ of column 2 has its parent $`(1, 1)`$ in column 1, but its template points to column 0. The edge upward from $`(1, 1)`$ has degree 0 and parent $`(0, 1)`$. The template points not to the parent but to the scale root of the parent.

## 2. Representations

Choose one relation $`R`$ and keep it fixed. All definitions below are relative to this relation.

- The elements of $`\mathrm{Label}`$ are called **labels** ([01](01-ordinals.md) §6). A representation below attaches one label to each column of a diagram.
- $`\lt`$ is the order of labels (the order of ordinals).
- $`R(\theta, a, b)`$ is a relation of three arguments: $`\theta \in \mathrm{Key}_m`$ is a key and $`a, b`$ are labels. In the definition of a representation below, $`\theta`$ receives the key of the edge, $`a`$ the label of the parent, and $`b`$ the label of the child. Read $`R(\theta, a, b)`$ as "with key $`\theta`$, $`a`$ is stable into $`b`$". This is only a reading; what $`R`$ is does not matter here (§9).

The layer $`k`$ and root label $`\eta`$ of the four-argument $`R(k, \eta, a, b)`$ of the 1-Y version have become a single key $`\theta`$. There is no domain $`D`$ as in the 1-Y version.

**Definition (holds).** For a function $`f : \mathrm{Fin}\ n \to \mathrm{Label}`$, an atom $`(t, p, q)`$ **holds** for $`f`$ if $`R(\mathrm{eval}\ t\ f, f(p), f(q))`$.

**Definition (representation).** A function $`f : \mathrm{Fin}\ n \to \mathrm{Label}`$ is a **representation** of a diagram $`G`$ of size $`n`$ if the following three conditions hold.

1. $`f(i) \lt \omega_1`$ for $`i \lt n`$.
2. $`f(i) \lt f(j)`$ for $`i \lt j \lt n`$.
3. Every atom of $`G`$ holds for $`f`$.

$`f(i)`$ is called the label of column $`i`$. Condition 1 replaces the condition $`D(f(i))`$ of the 1-Y version. A representation of the mountain of an expression $`s`$ in dimension $`D`$ is a representation of $`G_D(s)`$.

**Example.** A representation of the diagram of $`(1, 2, 4)`$ ($`D = 0`$) is an $`f`$ with

```math
f(0) \lt f(1) \lt f(2) \lt \omega_1, \quad R((f(0)), f(0), f(1)), \quad R((f(0)), f(1), f(2)), \quad R((f(1)), f(1), f(2))
```

A representation of the diagram of $`(1, 3, 5)`$ ($`D = 1`$) is an $`f`$ with the following, writing $`f_j := f(j)`$.

```math
f_0 \lt f_1 \lt f_2 \lt \omega_1, \quad R((f_0, f_0), f_0, f_1), \quad R((f_0, \top), f_0, f_1), \quad R((f_0, f_0), f_1, f_2), \quad R((f_0, \top), f_0, f_2)
```

## 3. Demands toward the top

**Definition (top atom).** A **top atom** is a pair $`d = (t, p)`$ ($`t \in \mathcal T_n`$, $`p \in \mathbb N`$); it is valid for size $`n`$ if $`p \lt n`$. A label $`\beta`$ of a point outside the diagram is called a **top**. For a function $`f : \mathrm{Fin}\ n \to \mathrm{Label}`$, $`d`$ **holds** for the top $`\beta`$ if $`R(\mathrm{eval}\ t\ f, f(p), \beta)`$. Mapped by a map of columns $`\mu`$, it becomes $`\mu d := (\mu t, \mu(p))`$.

A top atom is an edge to a point $`\beta`$ outside the diagram. In an expansion ([05](05-omegay-mountain.md) §4), the label of the old last column plays the role of $`\beta`$.

**Difference from ordinary atoms.** A top atom is an atom $`(t, p, q)`$ with the child $`q`$ removed. The child is not a column of the diagram but a point outside it, whose label we write $`\beta`$.

| | atom | top atom |
|---|---|---|
| form | $`(t, p, q)`$ | $`(t, p)`$ |
| child | column $`q`$ of the diagram | a point outside the diagram (label $`\beta`$) |
| valid | $`p \lt q \lt n`$ | $`p \lt n`$ |
| holds | $`R(\mathrm{eval}\ t\ f, f(p), f(q))`$ | $`R(\mathrm{eval}\ t\ f, f(p), \beta)`$ |

**Example 1 (the form).** The atoms of $`(1, 2, 4)`$ are $`((0), 0, 1)`$, $`((0), 1, 2)`$, $`((1), 1, 2)`$ (§1). Remove the last column 2 and consider the diagram of columns 0, 1 only (size 2). The two edges to column 2 now have their child outside the diagram, so we write them as top atoms.

- $`((0), 1)`$: it holds when $`R((f(0)), f(1), \beta)`$.
- $`((1), 1)`$: it holds when $`R((f(1)), f(1), \beta)`$.

Here $`\beta = f(2)`$ is the label of column 2, which is now outside. Templates point only to columns at or left of the parent (Property 3), so after the child is removed the columns the template points to are still in the diagram.

**Definition (demand).** A top atom $`d`$ that is passed to finite reflection of §4 separately from the diagram $`G`$ is called a **demand**. A finite list of demands is written $`\mathrm{needs}`$. Finite reflection guarantees that the demands that hold for the top $`\beta`$ before the reflection hold for the new top $`f(\mathrm{cut})`$ after it ($`\mathrm{cut}`$ is the cut defined below).

**Steps of an expansion.** Consider expanding an expression $`s`$ to $`s[N]`$ (expansion: [05](05-omegay-mountain.md) §4). Let $`x`$ be the last column of $`s`$, $`(z, d)`$ the root, and $`L := x - z`$. From column $`z`$ on, $`s[N]`$ is divided into blocks $`0, 1, \ldots, N`$ ([05](05-omegay-mountain.md) §4). In §7, a representation of $`G_D(s[N])`$ is built from one of $`G_D(s)`$ by adding the blocks one at a time. For $`i = 0, 1, \ldots, N - 1`$, the procedure that adds block $`i + 1`$ is called **step $`i`$**.

**Definition (control edge and lower edges).** The top edge of column $`x`$ of $`M(s)`$ is called the **control edge** $`e_c`$. Its parent is the root $`(z, d)`$ ([05](05-omegay-mountain.md) §4). The other edges of column $`x`$ (the edges below the control edge) are called the **lower edges**.

**Demands in an expansion.** At each step $`i`$, $`\mathrm{needs}`$ is built as follows. $`m_i`$ is the shift of [05](05-omegay-mountain.md) §4: it keeps columns $`j \lt z`$ and moves columns $`j \ge z`$ to $`j + iL`$.

- At step $`i`$, the first column of block $`i`$, $`\mathrm{cut} := z + iL`$, is called the **cut**.
- The label of the column to be added next, $`x + iL`$ (the first column of block $`i + 1`$), becomes the new top $`f(\mathrm{cut})`$.
- For each lower edge $`e`$ (parent $`\pi`$), the top atom $`\bigl(\kappa_D(e), \mathrm{col}(\pi)\bigr)`$ mapped by $`m_i`$ becomes a demand. This list is written $`T_i`$.

```math
\mathrm{needs} := T_i := \Bigl[\ m_i\bigl(\kappa_D(e),\ \mathrm{col}(\pi_e)\bigr)\ \Bigm|\ e \text{ is a lower edge}\ \Bigr]
```

The control edge is not made a demand. Instead, the relation $`R(\theta, f(\mathrm{cut}), \beta)`$ is passed to finite reflection of §4 (hypothesis 3). A relation of this form is called the **control relation**. The key $`\theta`$ is the template of the control edge mapped by $`m_i`$ and evaluated. At step 0, $`\theta = \mathrm{eval}\ \kappa_D(e_c)\ f`$. The $`\theta`$ of later steps is described in §7.

**Property 5 (the keys of the demands are below the control key).** For a lower edge $`e`$ and $`i \in \mathbb N`$, $`\overline{m_i \kappa_D(e)} \lt \overline{m_i \kappa_D(e_c)}`$. Hence $`\mathrm{eval}\ (m_i \kappa_D(e))\ f \lt \mathrm{eval}\ (m_i \kappa_D(e_c))\ f`$ for every strictly increasing $`f`$.

**Proof.** By Property 4, $`\bar\kappa_D(e) \lt \bar\kappa_D(e_c)`$. $`m_i`$ is strictly increasing, so by Property 2, $`\overline{m_i \kappa_D(e)} \lt \overline{m_i \kappa_D(e_c)}`$. The rest is Property 1. $`\square`$

**Example 2 (step 0 of the expansion of $`(1, 2, 4)`$).** $`x = 2`$, the root is $`(z, d) = (1, 2)`$, $`L = 1`$, $`D = 0`$, and $`s[N] = (1, 2, \ldots, N + 2)`$ ([05](05-omegay-mountain.md) §6). Look at step $`i = 0`$.

- The diagram $`G`$ is the diagram of $`(1, 2)`$: size 2, atom $`((0), 0, 1)`$. $`f`$ is the original representation, $`\beta = f(2)`$, and the cut is $`\mathrm{cut} = z = 1`$.
- The edges of column 2 are $`1 \to 2`$ (parent $`(1, 1)`$, template $`(0)`$) and $`2 \to 3`$ (parent $`(1, 2)`$, template $`(1)`$). The control edge is $`2 \to 3`$, and $`1 \to 2`$ is the only lower edge. $`m_0`$ is the identity, so $`\mathrm{needs} = [((0), 1)]`$. It holds for $`\beta = f(2)`$ by the original atom $`((0), 1, 2)`$.
- The atom $`((1), 1, 2)`$ of the control edge is not a demand. It becomes the control relation $`R((f(1)), f(1), f(2))`$, with $`\theta = (f(1))`$.
- The key $`(f(0))`$ of the demand is below $`\theta = (f(1))`$ (hypothesis 5 of §4), because $`f(0) \lt f(1)`$.
- The $`g`$ given by finite reflection (§4) has $`g(0) = f(0)`$ and $`g(1) \lt f(1)`$, and the demand holds for the top $`f(\mathrm{cut}) = f(1)`$, that is, $`R((g(0)), g(1), f(1))`$.
- Column 2 of the new diagram gets $`f(\mathrm{cut}) = f(1)`$ (§6), so the labels are $`(g(0), g(1), f(1))`$. The atoms of the diagram of $`(1, 2, 3)`$ are $`((0), 0, 1)`$ and $`((0), 1, 2)`$, and the latter is exactly the demand above. In this way a demand becomes an edge of the new diagram.

**Definition (bound).** Let $`n \in \mathbb N`$, $`f : \mathrm{Fin}\ n \to \mathrm{Label}`$ and $`\beta \in \mathrm{Label}`$. $`f`$ is **bounded by** $`\beta`$ if $`f(i) \lt \beta`$ for all $`i \lt n`$.

## 4. Finite reflection

**Definition (demand with key below θ).** For a key $`\theta`$ and a function $`f : \mathrm{Fin}\ n \to \mathrm{Label}`$, a top atom $`d = (t, p)`$ **has key below $`\theta`$** if $`\mathrm{eval}\ t\ f \lt \theta`$.

This replaces the "admissible demand" of the 1-Y version (a lower layer, or a root before the cut whose label is below $`\theta`$). The columns the template points to need not lie before the cut.

**Example.** Look at step 0 of an expansion ("Steps of an expansion" of §3). $`\mathrm{cut}`$ and $`\theta`$ are determined by the root and the control edge ("Demands in an expansion" of §3). $`f`$ is the original representation, whose labels increase with the column.

- $`(1, 2, 4)`$: the root is $`(1, 2)`$, so $`\mathrm{cut} = 1`$ and $`\theta = (f(1))`$ (Example 2 of §3).
- $`(1, 3)`$: $`x = 1`$, the root is $`(0, 1)`$ ([05](05-omegay-mountain.md) §4), so $`\mathrm{cut} = 0`$. The control edge is $`2 \to \omega`$ of column 1, so $`\theta = (f(0), \top)`$. The only lower edge is $`1 \to 2`$, so $`\mathrm{needs} = [((0, 0), 0)]`$.

| Expression | Top atom $`(\bar t, p)`$ | Key | Below $`\theta`$? | Reason |
|---|---|---|---|---|
| $`(1, 2, 4)`$ | $`((0), 1)`$ | $`(f(0))`$ | yes | $`f(0) \lt f(1)`$ |
| $`(1, 2, 4)`$ | $`((1), 1)`$ | $`(f(1))`$ | no | equal to $`\theta`$ |
| $`(1, 3)`$ | $`((0, 0), 0)`$ | $`(f(0), f(0))`$ | yes | coordinate 0 is equal, and $`f(0) \lt \top`$ at coordinate 1 |
| $`(1, 3)`$ | $`((0, \top), 0)`$ | $`(f(0), \top)`$ | no | equal to $`\theta`$ |

The two that are not below are the control edges ($`((1), 1, 2)`$ and $`((0, \top), 0, 1)`$) with the child removed. These edges are not made demands; they are passed as the control relation.

**Definition (finite reflection).** A relation $`R`$ (§2) satisfies **finite reflection** if the following holds.

For every diagram $`G`$, function $`f : \mathrm{Fin}\ n \to \mathrm{Label}`$, natural number $`\mathrm{cut}`$, key $`\theta`$, label $`\beta`$ and list $`\mathrm{needs}`$ of top atoms, assume that all of the following six hypotheses hold.

1. $`G`$ is a diagram of size $`n`$ and $`\mathrm{cut} \lt n`$. $`f`$ is a representation of $`G`$.
2. $`f`$ is bounded by $`\beta`$.
3. The control relation (§3) $`R(\theta, f(\mathrm{cut}), \beta)`$ holds.
4. Every element of the list of demands $`\mathrm{needs}`$ is valid.
5. Every element has key below $`\theta`$.
6. Every element holds for the top $`\beta`$.

Then there is a function $`g : \mathrm{Fin}\ n \to \mathrm{Label}`$ with the following five properties.

1. $`g`$ is a representation of $`G`$.
2. $`g(i) = f(i)`$ for $`i \lt \mathrm{cut}`$.
3. $`g`$ is bounded by $`f(\mathrm{cut})`$.
4. $`g(i) \le f(i)`$ for $`i \lt n`$.
5. Every demand holds for the top $`f(\mathrm{cut})`$.

By hypothesis 2, $`f(i) \lt \beta \le \omega_1`$, so condition 1 of "representation" in hypothesis 1 follows from hypothesis 2. Condition 1 in conclusion 1 also follows from conclusion 3.

**Meaning.** The labels left of the cut stay. The labels from the cut on are replaced so that all of them lie below $`f(\mathrm{cut})`$. The edge conditions and the demands toward the top (with the top changed from $`\beta`$ to $`f(\mathrm{cut})`$) are kept. This is exactly the shape of finite reflection in [04](04-patterns-of-resemblance.md) §3. Unlike the 1-Y version, the columns that the key of a demand points to need not lie before the cut. Their labels are replaced too.

## 5. The three theorems

The main theorem of the combinatorial layer (below, the **entry theorem**) uses these three theorems about the relation $`R`$. The letters in the table range over $`\theta, \Theta \in \mathrm{Key}_m`$ and $`a, b \in \mathrm{Label}`$.

| Name | Statement |
|---|---|
| key weakening | $`\theta \le \Theta`$ and $`R(\Theta, a, b)`$ imply $`R(\theta, a, b)`$ |
| finite reflection | finite reflection of §4 holds for $`R`$ |
| initial representation | for every diagram $`G`$ (size $`n`$) and every list $`\mathrm{needs}`$ of top atoms, there are a $`\beta \lt \omega_1`$ and a representation $`f`$ of $`G`$ bounded by $`\beta`$ such that every element of $`\mathrm{needs}`$ holds for the top $`\beta`$ |

The conclusion is "the one-step expansion relation is well-founded" (Theorem 1 of [05](05-omegay-mountain.md) §7).

They correspond to the six hypotheses of the 1-Y version as follows.

| Hypothesis of the 1-Y version | ω-Y |
|---|---|
| well-foundedness, transitivity | the order of labels is the order of ordinals, so they are not hypotheses ([01](01-ordinals.md) §1) |
| strictness | not used. $`f(\mathrm{cut}) \lt \beta`$ follows from hypothesis 2 of finite reflection |
| weakening | key weakening. A key $`\theta \le \Theta`$ instead of root labels $`\eta' \lt \eta`$ |
| finite reflection | finite reflection |
| initial representation | initial representation, for all diagrams and lists of top atoms, not only for diagrams of expressions |

## 6. Splicing one block

One finite reflection makes a diagram one block longer. Take $`G`$ (size $`n`$), $`f`$, $`\mathrm{cut}`$, $`\theta`$, $`\beta`$, $`\mathrm{needs}`$ satisfying the six hypotheses of §4, and fix a $`g`$ given by finite reflection.

**Definition (the map of columns).** The new diagram has size $`n + (n - \mathrm{cut})`$. An old column $`j \lt n`$ is moved to the new column $`\mathrm{mv}(j)`$.

```math
\mathrm{mv}(j) := \begin{cases} j & (j \lt \mathrm{cut}) \cr n + (j - \mathrm{cut}) & (\mathrm{cut} \le j \lt n) \end{cases}
```

$`\mathrm{mv}`$ is strictly increasing and $`\mathrm{mv}(\mathrm{cut}) = n`$. A column $`j \lt n`$ that is not moved is column $`j`$ of the new diagram too.

**Definition (spliced labels).**

```math
h(c) := \begin{cases} g(c) & (c \lt n) \cr f(\mathrm{cut} + c - n) & (n \le c \lt n + (n - \mathrm{cut})) \end{cases}
```

$`h(c) = g(c)`$ for $`c \lt n`$, $`h(\mathrm{mv}(j)) = f(j)`$ for $`j \lt n`$ (for $`j \lt \mathrm{cut}`$ this uses $`g(j) = f(j)`$ of conclusion 2), and in particular $`h(n) = f(\mathrm{cut})`$. So $`f(\mathrm{cut}), \ldots, f(n-1)`$ appear unchanged at the right end.

**Example.** For $`n = 4`$ and $`\mathrm{cut} = 1`$, writing $`f_j := f(j)`$ and $`g_j := g(j)`$:

```math
h = (g_0, g_1, g_2, g_3, f_1, f_2, f_3), \qquad g_0 = f_0, \quad g_1 \lt g_2 \lt g_3 \lt f_1
```

**Theorem (splicing one block).** $`h`$ is strictly increasing and bounded by $`\beta`$. Suppose every atom $`e = (t, p, q)`$ of a diagram $`H`$ of size $`n + (n - \mathrm{cut})`$ satisfies one of the following.

1. $`e \in G`$.
2. There is an atom $`e' = (t', p', q')`$ of $`G`$ with $`p = \mathrm{mv}(p')`$, $`q = \mathrm{mv}(q')`$ and $`\bar t \le \overline{\mathrm{mv}\, t'}`$.
3. There is a demand $`d = (t', p') \in \mathrm{needs}`$ with $`p = p'`$, $`q = n`$ and $`\bar t \le \bar t'`$.

Then $`h`$ is a representation of $`H`$.

**Proof.**

- Order: for $`c \lt c' \lt n`$, $`g`$ is strictly increasing. For $`c \lt n \le c'`$, $`h(c) = g(c) \lt f(\mathrm{cut}) \le h(c')`$. For $`n \le c \lt c'`$, $`f`$ is strictly increasing.
- Bound: $`g(c) \lt f(\mathrm{cut}) \lt \beta`$ and $`f(j) \lt \beta`$. So $`h(c) \lt \beta \le \omega_1`$.
- Atoms of case 1: by conclusion 1 of finite reflection, $`e`$ holds for $`g`$. Every column $`e`$ reads is below $`n`$, where $`h = g`$.
- Atoms of case 2: $`f`$ is a representation of $`G`$, so $`R(\mathrm{eval}\ t'\ f, f(p'), f(q'))`$. By Property 2 and $`h \circ \mathrm{mv} = f`$, $`\mathrm{eval}\ (\mathrm{mv}\, t')\ h = \mathrm{eval}\ t'\ f`$, $`h(p) = f(p')`$ and $`h(q) = f(q')`$. By Property 1, $`\mathrm{eval}\ t\ h \le \mathrm{eval}\ (\mathrm{mv}\, t')\ h`$. Key weakening gives $`R(\mathrm{eval}\ t\ h, h(p), h(q))`$.
- Atoms of case 3: by conclusion 5 of finite reflection, $`R(\mathrm{eval}\ t'\ g, g(p'), f(\mathrm{cut}))`$. $`h(n) = f(\mathrm{cut})`$, and $`h = g`$ on the columns $`t'`$ and $`p'`$ read. By Property 1, $`\mathrm{eval}\ t\ h \le \mathrm{eval}\ t'\ h`$, and key weakening gives $`R(\mathrm{eval}\ t\ h, h(p), h(n))`$. $`\square`$

The 1-Y version used weakening when the root of a copied atom moved to an earlier block and when the root of a demand lay in an earlier block. ω-Y uses key weakening in cases 2 and 3.

## 7. Iterated reflection with reservoirs

In this section, $`s`$ is an expression with root $`(z, d)`$, $`x`$ its last column, $`L := x - z`$, $`D`$ a dimension of $`M(s)`$, $`f`$ a representation of $`G_D(s)`$, and $`\beta := f(x)`$. $`e_c`$ is the control edge and $`T_i`$ the list of demands of §3.

**Definition (reservoirs).** The following three are called the **reservoirs**. For $`i \in \mathbb N`$ their images under $`m_i`$ are used as well.

```math
F := G_D(s[0]), \qquad T := T_0, \qquad c := \bigl(\kappa_D(e_c),\ z\bigr), \qquad F_i := m_i F, \quad c_i := m_i c = \bigl(m_i \kappa_D(e_c),\ z + iL\bigr)
```

- $`F`$ is the internal reservoir. Since $`s[0] = (s_0, \ldots, s_{x-1})`$, $`F`$ is the prefix of size $`x`$ of $`G_D(s)`$, made of the edges of $`M(s)`$ left of column $`x`$.
- $`T = T_0`$ is the top reservoir (the lower edges) and $`c`$ is the control edge. $`T_i = m_i T`$.

**Definition (state of step $`i`$).** A list of labels $`f_i : \mathrm{Fin}\ (x + iL) \to \mathrm{Label}`$ is a **state of step $`i`$** if the following five conditions hold.

1. $`f_i`$ is strictly increasing and bounded by $`\beta`$.
2. Every atom of $`G_D(s[i])`$ holds for $`f_i`$.
3. Every atom of $`F_i`$ holds for $`f_i`$.
4. Every element of $`T_i`$ holds for the top $`\beta`$.
5. $`c_i`$ holds for the top $`\beta`$, that is, the control relation $`R\bigl(\mathrm{eval}\ (m_i \kappa_D(e_c))\ f_i,\ f_i(z + iL),\ \beta\bigr)`$ holds.

**Lemma (classification of the edges of a block).** Let $`i \in \mathbb N`$ and $`n := x + iL`$. Every atom $`e = (t, p, q)`$ of $`G_D(s[i+1])`$ satisfies one of the following.

1. $`q \lt n`$ and $`e \in G_D(s[i])`$.
2. There is an atom $`(t', p', q')`$ of $`F`$ with $`p = m_{i+1}(p')`$, $`q = m_{i+1}(q')`$ and $`\bar t \le \overline{m_{i+1} t'}`$.
3. $`q = n`$, and there is a lower edge $`e'`$ (parent $`\pi'`$) with $`p = m_i(\mathrm{col}(\pi'))`$ and $`\bar t \le \overline{m_i \kappa_D(e')}`$.

It is not proved here. Case 2 reads $`e`$ as an edge of $`F`$ shifted $`i + 1`$ times, with a weakened key. For edges of column $`n`$, case 2 comes from edges of the root column $`z`$. Case 3 is a lower edge shifted $`i`$ times with its child at column $`n`$. Cases 2 and 3 use (T), (C), (F) of step 1 of [05](05-omegay-mountain.md) §4 and the weak-magma rule ([05](05-omegay-mountain.md) §5). In the official ω-Y, case 2 fails ([notes/02-feasibility.md](../../notes/02-feasibility.md) §3.1, Japanese).

This lemma was checked with a Python program that transcribes the formulas of 05 §3, §4 and the definitions of this section (2026-09-27). For the 564 expressions whose last entry is not 1 among those of length at most 5 reached from the seeds $`(1, 2)`$, $`(1, 3)`$, $`(1, 4)`$, $`(1, 5)`$ by repeated expansion ($`N = 0, 1, 2, 3`$), it held for all $`i = 0, 1, 2`$ (104607 atoms). Among expressions of length at most 6, 10884 were checked in lexicographic order for $`i = 0, 1`$ (stopped after 55 seconds).

**Theorem (one reflection with reservoirs).** If $`f_i`$ is a state of step $`i`$, there is a state $`f_{i+1}`$ of step $`i + 1`$ with $`f_{i+1}(\mathrm{mv}(j)) = f_i(j)`$.

**Proof.** Let $`n := x + iL`$. Use finite reflection (§4) with

```math
G := G_D(s[i]) \cup F_i, \qquad \mathrm{needs} := T_i, \qquad \mathrm{cut} := z + iL, \qquad \theta := \mathrm{eval}\ (m_i \kappa_D(e_c))\ f_i
```

- Hypotheses 1, 2: from conditions 1, 2, 3 of the state and $`f_i(j) \lt \beta \le \omega_1`$.
- Hypothesis 3: condition 5 of the state.
- Hypothesis 4: the parents of lower edges are in columns below $`x`$, so their images under $`m_i`$ are below $`n`$.
- Hypothesis 5: Property 5.
- Hypothesis 6: condition 4 of the state.

With the resulting $`g`$, build the $`h`$ of §6 and let $`f_{i+1} := h`$. Since $`n - \mathrm{cut} = L`$, the new size is $`x + (i+1)L`$. $`\mathrm{mv}`$ keeps $`j \lt z + iL`$ and moves $`j \ge z + iL`$ to $`j + L`$. Hence $`\mathrm{mv} \circ m_i = m_{i+1}`$.

1. By the theorem of §6.
2. The three cases of the lemma become the three cases of the theorem of §6. Case 1 as it is ($`G_D(s[i]) \subseteq G`$). In case 2 take $`e' := m_i(t', p', q') \in F_i`$; then $`\mathrm{mv}\, e' = m_{i+1}(t', p', q')`$. In case 3 take $`d := m_i\bigl(\kappa_D(e'), \mathrm{col}(\pi')\bigr) \in T_i`$.
3. $`F_{i+1} = \mathrm{mv}\, F_i`$. The atoms of $`F_i`$ hold for $`f_i`$ and $`h \circ \mathrm{mv} = f_i`$, so by Property 2 the mapped atoms hold for $`h`$.
4. $`T_{i+1} = \mathrm{mv}\, T_i`$, which holds for the top $`\beta`$ for the same reason as 3.
5. $`c_{i+1} = \mathrm{mv}\, c_i`$, as in 4. $`\mathrm{mv}(z + iL) = n = z + (i+1)L`$ is the next cut. $`\square`$

**Theorem (iterated reflection with reservoirs).** The restriction $`f_0`$ of $`f`$ to the columns left of $`x`$ is a state of step 0. Hence there is a state of step $`i`$ for every $`i \in \mathbb N`$.

**Proof.** $`m_0`$ is the identity.

1. $`f`$ is strictly increasing, and $`f(j) \lt f(x) = \beta`$ for $`j \lt x`$.
2. and 3. $`G_D(s[0]) = F`$ is a prefix of $`G_D(s)`$ whose templates do not point to column $`x`$ (Property 3). So atoms that hold for $`f`$ hold for $`f_0`$.
4. For a lower edge $`e`$, the atom $`(\kappa_D(e), \mathrm{col}(\pi), x)`$ holds for $`f`$, that is, $`R(\mathrm{eval}\ \kappa_D(e)\ f, f(\mathrm{col}(\pi)), f(x))`$. This says that the top atom $`(\kappa_D(e), \mathrm{col}(\pi))`$ holds for the top $`\beta`$.
5. The same as 4 for the control edge.

The rest is the previous theorem, used by induction on $`i`$. $`\square`$

## 8. Descent of the last label

**Definition (last label).** For a representation $`f`$ of a diagram of size $`n \gt 0`$, the label $`f(n-1)`$ of the last column is called the **last label** of $`f`$.

**Theorem (the labels go below the last label).** Let $`s`$ be a nonempty expression and $`D`$ a dimension of $`M(s)`$, and suppose $`G_D(s)`$ has a representation with last label $`\beta`$. Then for every $`N \in \mathbb N`$, $`G_D(s[N])`$ has a representation all of whose labels are below $`\beta`$.

$`D`$ is also a dimension of $`M(s[N])`$ ([05](05-omegay-mountain.md) §7). $`s[N]`$ may be empty. The 1-Y version stated "the last label goes down"; here we state that all labels lie below $`\beta`$.

**Outline of the proof.** Let $`x`$ be the last column of $`s`$, and let $`f`$ be a representation of $`G_D(s)`$ with last label $`\beta = f(x)`$.

1. No root, or $`N = 0`$: $`s[N]`$ is $`s`$ without its last column. $`G_D(s[N])`$ is the prefix of size $`x`$ of $`G_D(s)`$. The restriction of $`f`$ to the columns left of $`x`$ is a representation, and all its labels are below $`f(x) = \beta`$.
2. Root $`(z, d)`$ and $`N \ge 1`$:
   - For $`i = 0, 1, \ldots, N`$, $`G_D(s[i])`$ is called diagram $`i`$. Its size is $`x + iL`$. Diagram 0 is the prefix of size $`x`$ of $`G_D(s)`$, and diagram $`N`$ is the target diagram.
   - The control edge gives $`R(\mathrm{eval}\ \kappa_D(e_c)\ f, f(z), f(x))`$. This is the first control relation.
   - The lower edges become top atoms toward the top $`\beta`$ (built as in Example 1 of §3). Every diagram of every step is bounded above by $`\beta`$, so no column of a diagram has the label $`\beta`$. So these top atoms remain edges to the outside point $`\beta`$.
   - Step $`i`$ (§3), going from diagram $`i`$ to diagram $`i + 1`$, uses finite reflection once (the theorem of §7). The cut is the start of block $`i`$, $`\mathrm{cut} = z + iL`$. The 1-Y version built the demands at each step from the new mountain. ω-Y passes every time the lower edges and the shifted edges left of column $`x`$ (the reservoirs), and obtains the new edges from them by key weakening (§6).
   - After $`N`$ repetitions we get a state $`f_N`$ of step $`N`$. By conditions 1 and 2 of the state, $`f_N`$ is a representation of $`G_D(s[N])`$ bounded by $`\beta`$. $`\square`$

**Where the three theorems are used.**

| Theorem | Where |
|---|---|
| key weakening | cases 2 and 3 of the theorem of §6 (copied edges and edges that come from demands) |
| finite reflection | once per block (§7) |
| initial representation | the start of the induction ($`G = G_D(s)`$, $`\mathrm{needs}`$ empty) |

The well-foundedness of the order of labels is used for the induction.

**Well-foundedness.** Apply the theorem of [02](02-well-founded.md) §6 (termination by an upper bound of labels) for each $`D`$ as follows.

| General form | ω-Y |
|---|---|
| element of $`X`$ | an expression $`s`$ whose mountain has dimension $`D`$ |
| $`t \prec s`$ | nontrivial one-step expansion ($`t = s[N] \ne s`$) |
| $`(L, \lt)`$ | the order of labels $`(\mathrm{Label}, \lt)`$ |
| $`V(s, \alpha)`$ | $`G_D(s)`$ has a representation all of whose labels are below $`\alpha`$ |

- First hypothesis: $`\alpha_0 := \omega_1`$. By the initial representation, every $`s`$ has a representation bounded by some $`\beta \lt \omega_1`$.
- Second hypothesis: let $`V(s, \alpha)`$ and $`t \prec s`$. Then $`s`$ is nonempty. The last label $`\alpha' := f(x)`$ of the representation is below $`\alpha`$, and by the theorem above $`V(t, \alpha')`$. The mountain of $`t`$ also has dimension $`D`$.

Every expression $`s`$ has a dimension $`D`$ (the mountain has finitely many rows, so take the largest exponent of a nonzero coefficient). The expressions reached from $`s`$ also have dimension $`D`$ ([05](05-omegay-mountain.md) §7), so $`s`$ is accessible for $`\prec`$ ([02](02-well-founded.md) §1). Hence $`\prec`$ is well-founded (Theorem 1 of [05](05-omegay-mountain.md) §7).

**Example ($`(1, 3, 3)[2]`$).** $`x = 2`$, the root is $`(z, d) = (0, 1)`$, $`L = 2`$, $`D = 1`$. Write $`f_j := f(j)`$.

- The control edge is the edge $`2 \to \omega`$ of column 2, with template $`(0, \top)`$, so $`c = ((0, \top), 0)`$. The lower edge is the edge $`1 \to 2`$ of column 2, so $`T = [((0, 0), 0)]`$. $`\beta = f_2`$.
- The internal reservoir is $`F = G_1((1, 3)) = [((0, 0), 0, 1),\ ((0, \top), 0, 1)]`$.
- State of step 0: labels $`(f_0, f_1)`$. The control relation is $`R((f_0, \top), f_0, f_2)`$, and $`T`$ gives $`R((f_0, f_0), f_0, f_2)`$.
- Step 0: the cut is 0. Reflection gives $`g_0 \lt g_1 \lt f_0`$. The new labels are $`(g_0, g_1, f_0, f_1)`$, which represent the diagram of $`s[1] = (1, 3, 2, 5)`$. Its atoms are classified as follows.

| Atom $`(\bar t, p, q)`$ | Case of the lemma | Source |
|---|---|---|
| $`((0, 0), 0, 1)`$, $`((0, \top), 0, 1)`$ | 1 | $`G_1((1, 3))`$ |
| $`((0, 0), 0, 2)`$ | 3 | the lower edge $`((0, 0), 0)`$ |
| $`((0, 0), 2, 3)`$ | 2 | $`((0, 0), 0, 1)`$ of $`F`$ mapped by $`m_1`$ is $`((2, 2), 2, 3)`$; $`(0, 0) \le (2, 2)`$ |
| $`((2, 2), 2, 3)`$ | 2 | the same, with equal templates |
| $`((2, \top), 2, 3)`$ | 2 | $`((0, \top), 0, 1)`$ of $`F`$ mapped by $`m_1`$ |

- Step 1: the cut is 2, whose label is $`f_0`$. Reflection gives $`g'_2 \lt g'_3 \lt f_0`$. Columns 0 and 1 do not move. The new labels are $`(g_0, g_1, g'_2, g'_3, f_0, f_1)`$.

This is a representation of $`(1, 3, 3)[2] = (1, 3, 2, 5, 4, 9)`$, and every label is below $`f_2`$. The classification in the table was computed with the Python program above.

## 9. What remains for the semantic layer

The combinatorial layer does not ask why finite reflection holds. Supplying an $`R`$ with the three theorems of §5 is the job of the **semantic layer**.

- Phyrion's semantic layer: it gives an $`R`$ different from that of this repository. $`R(\theta, a, b)`$ says "finite positive diagrams below $`b`$ can be compressed below $`a`$" ([04](04-patterns-of-resemblance.md) §5, [notes/00-survey.md](../../notes/00-survey.md) §3.2, Japanese). It is not included in this repository.
- The semantic layer of this repository: $`R`$ is the $`\Sigma_1`$-elementary-substructure relation of [07 The relation R](07-relation-r.md). The proofs are in [09 Proofs of the three theorems](09-obligations.md).

## 10. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "Structure of the proof" | the two layers and the table of the three theorems |
| [notes/01-design.md](../../notes/01-design.md) §1 (Japanese) | what the combinatorial layer uses from the semantic layer |
| [notes/00-survey.md](../../notes/00-survey.md) §3.2, §3.5 (Japanese) | keys, keys of mountain edges, preservation of dimension, correspondence with 1-Y |
| [notes/02-feasibility.md](../../notes/02-feasibility.md) §3, §4 (Japanese) | in the official ω-Y, case 2 of the lemma of §7 fails |

## 11. Lean correspondence

| Concept | Lean | File |
|---|---|---|
| key syntax | `KeySyntax` | [OmegaY/Reflection/Interface.lean](../../OmegaY/Reflection/Interface.lean) |
| atom, top atom | `InternalAtom` (`key`, `parent`, `child`), `TopAtom` (`key`, `parent`) | same |
| holds, key below $`\theta`$, bound | `InternalHolds`, `TopHolds`, `KeysBelow`, `Bounded` | same |
| keys and templates | `Keys.Key`, `Keys.Template`, `Keys.eval`, `Keys.eval_mono` | [OmegaY/Keys.lean](../../OmegaY/Keys.lean) |
| $`\bar t`$, Property 1 | `Keys.templateKey`, `Keys.eval_lt_of_template_lt`, `Keys.eval_le_of_template_le` | same |
| $`\mu t`$, Property 2 | `Keys.relabel`, `Keys.eval_relabel` | same |
| the concrete key syntax | `KeyReflection.vectorSyntax`, `Model.keySyntax`, `Model.R` | [OmegaY/KeyReflection.lean](../../OmegaY/KeyReflection.lean), [OmegaY/Model.lean](../../OmegaY/Model.lean) |
| scale roots | `scaleParent`, `scaleRoot` (monotone in the scale: `scaleRoot_scale_antitone`) | [OmegaY/Geometry/MountainKeys.lean](../../OmegaY/Geometry/MountainKeys.lean) |
| edges, degree, template $`\kappa_D`$, Property 3 | `RealStoredEdge`, `degree`, `degree_le`, `keyTemplate`, `keyTemplate_column_bound`, `atom` | same |
| dimension | `exists_key_dimension`, `MountainKeyDimension`, `KeyDimension` | same, [OmegaY/Expansion/SupportedDimension.lean](../../OmegaY/Expansion/SupportedDimension.lean) |
| Property 4 | `key_strict_in_column`, `topAtom_key_strict_in_column` | [OmegaY/Geometry/VerticalEdgeKeys.lean](../../OmegaY/Geometry/VerticalEdgeKeys.lean), [OmegaY/Geometry/TopEdgeKeys.lean](../../OmegaY/Geometry/TopEdgeKeys.lean) |
| representation of a mountain | `KeyRepresentation`, `keyRepresentation_exists`, `restrict`, `lastLabel`, `restrict_below_last` | [OmegaY/Geometry/RepresentedMountain.lean](../../OmegaY/Geometry/RepresentedMountain.lean) |
| the three theorems (names read by the combinatorial layer) | `Reflection.key_weaken`, `Reflection.finite_reflection`, `OrdinalSupply.initial_finite_graph`, `Model.key_weaken`, `Model.finite_reflection`, `Model.initial_finite_graph` | [OmegaY/Reflection.lean](../../OmegaY/Reflection.lean), [OmegaY/Reflection/OrdinalSupply.lean](../../OmegaY/Reflection/OrdinalSupply.lean), [OmegaY/Model.lean](../../OmegaY/Model.lean) |
| $`\mathrm{mv}`$ and $`h`$ of §6 | `Splice.width`, `old`, `moved`, `boundary`, `labels` | [OmegaY/Splice.lean](../../OmegaY/Splice.lean) |
| the theorem of §6 | `reflected_block`, `Classified`, `mapAtom`, `seamAtom`, `holds_weakened_copy`, `holds_seam`, `classified_graph_represented` | same |
| reservoirs, states, one step of §7 | `mapTop`, `ReservoirState`, `DemandCovered`, `ReservoirClassified`, `holds_weakened_seam`, `splice_reservoirs` | [OmegaY/Splice/Reservoirs.lean](../../OmegaY/Splice/Reservoirs.lean) |
| block numbers ($`x + iL`$, $`z + iL`$, $`m_i`$) | `blockWidth`, `blockCut`, `blockSource`, `blockMoved` | [OmegaY/Splice/BlockIndices.lean](../../OmegaY/Splice/BlockIndices.lean) |
| the iteration of §7 | `block_reservoir_step`, `iterated_reservoirs`, `BlockReservoirGeometry` | [OmegaY/Splice/IteratedReservoirs.lean](../../OmegaY/Splice/IteratedReservoirs.lean) |
| control edge and lower edges, Property 5 | `controlEdge`, `LowerEdge`, `controlAtom`, `lowerAtom`, `lower_key_strict`, `reflect_initial_control` | [OmegaY/Expansion/InitialControlKeys.lean](../../OmegaY/Expansion/InitialControlKeys.lean) |
| the reservoirs $`F`$, $`T`$, $`c`$ and their images under $`m_i`$ | `initialSpliceFacts`, `initialSpliceVirtualFacts`, `initialSpliceControl`, `spliceGraph`, `spliceFacts`, `spliceVirtualFacts`, `spliceControl` | [OmegaY/Expansion/ActualSpliceFacts.lean](../../OmegaY/Expansion/ActualSpliceFacts.lean) |
| the state of step 0 | `initial_reservoir`, `zero_reservoir` | [OmegaY/Expansion/ActualInitialReservoir.lean](../../OmegaY/Expansion/ActualInitialReservoir.lean) |
| the lemma of §7 | `actual_splice_edge_classified` (case 1: `retained_splice_classified`; column $`n`$: `boundary_splice_classified`; right of column $`n`$: `ordinary_splice_classified`) | [OmegaY/Expansion/ActualSpliceGeometry.lean](../../OmegaY/Expansion/ActualSpliceGeometry.lean), [OmegaY/Expansion/ActualBoundarySplice.lean](../../OmegaY/Expansion/ActualBoundarySplice.lean), [OmegaY/Expansion/ActualOrdinarySplice.lean](../../OmegaY/Expansion/ActualOrdinarySplice.lean) |
| the core of case 2 of the lemma of §7 | `ActualCopiedKeyBound`, `Preparation.copied_edge_key_bound` | [OmegaY/Expansion/ActualCopiedKeyBound.lean](../../OmegaY/Expansion/ActualCopiedKeyBound.lean), [OmegaY/Expansion/ActualFillCopiedKey.lean](../../OmegaY/Expansion/ActualFillCopiedKey.lean) |
| case 2 of the theorem of §8 | `iterated_actual_reservoirs`, `representationOfSpliceGraph`, `represent_actual_expansion` | [OmegaY/Expansion/ActualSpliceRepresentation.lean](../../OmegaY/Expansion/ActualSpliceRepresentation.lean) |
| case 1 of the theorem of §8 | `expandDiagram_trivial_representation_descent` | [OmegaY/Geometry/RepresentedMountain.lean](../../OmegaY/Geometry/RepresentedMountain.lean) |
| the theorem of §8 | `ActualRepresentationDescent`, `actual_representation_descent` | [OmegaY/Expansion/DynamicsRepresentationRank.lean](../../OmegaY/Expansion/DynamicsRepresentationRank.lean), [OmegaY/Expansion/ActualRepresentationDescent.lean](../../OmegaY/Expansion/ActualRepresentationDescent.lean) |
| well-foundedness | `RepresentationDescent`, `accessible_of_representation_below`, `empty_accessible`, `step_wellFounded_of_actual_representation_descent` | [OmegaY/Expansion/DynamicsRepresentationRank.lean](../../OmegaY/Expansion/DynamicsRepresentationRank.lean) |
| callers of the three theorems (found with `grep`, excluding `Reflection.lean`, `Reflection/`, `KeyReflection.lean`, `Model.lean`) | key weakening: `Splice.holds_weakened_copy`, `DemandCovered.top_holds`, `holds_weakened_seam`, `ActualCopiedKeyBound.represented`. Finite reflection: `Splice.reflected_block`, `Splice.splice_reservoirs`, `RootGeometry.reflect_initial_control`. Initial representation: `actual_keys_initially_represented` (with an empty list of demands) | [OmegaY/Splice.lean](../../OmegaY/Splice.lean), [OmegaY/Splice/Reservoirs.lean](../../OmegaY/Splice/Reservoirs.lean), [OmegaY/Expansion/ActualCopiedKeyLabels.lean](../../OmegaY/Expansion/ActualCopiedKeyLabels.lean), [OmegaY/Expansion/InitialControlKeys.lean](../../OmegaY/Expansion/InitialControlKeys.lean), [OmegaY/Geometry/MountainKeys.lean](../../OmegaY/Geometry/MountainKeys.lean) |
| the definitions of §1–§3 moved unchanged from Phyrion's | the interface in the `Reflection` namespace | [OmegaY/Reflection/Interface.lean](../../OmegaY/Reflection/Interface.lean), [NOTICE](../../NOTICE) |
