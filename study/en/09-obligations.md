[← Back](README.md) | [English](09-obligations.md) | [Japanese](../09-obligations.md)

# Proofs of the three theorems

Prerequisites

| Note | Terms used here |
|---|---|
| [06 Phyrion's combinatorial layer for ω-Y](06-combinatorial-layer.md) | combinatorial layer, vertex, graph, internal atoms, top atoms, demand, cut, `finite_reflection`, `initial_finite_graph`, control relation, `control` |
| [07 The relation R](07-relation-r.md) | $`R`$, $`\mathfrak A^c_\theta`$, `R_iff`, `key_weaken`, partial top predicates |
| [08 Closure below ω₁ and the sequence of Good points](08-closure-chain.md) | $`\mathfrak B`$, Good, `points` |

This note explains how the relation $`R`$ satisfies the three theorems of the combinatorial layer. The core is finite reflection (§2) and the first representation (§3).

## 1. Overview

| Theorem | Proof | Names the combinatorial layer calls |
|---|---|---|
| key weakening | `Por.key_weaken` ([07](07-relation-r.md) §7) | `Reflection.key_weaken`, `KeyReflection.weaken`, `Model.key_weaken` |
| finite reflection | `Por.finite_reflection` (§2) | `Reflection.finite_reflection`, `Model.finite_reflection` |
| first representation | `Por.Supply.initial_finite_graph` (§3) | `OrdinalSupply.initial_finite_graph`, `Model.initial_finite_graph` |

The names the combinatorial layer calls are given in the following files, with Phyrion's statements unchanged.

- [OmegaY/Reflection.lean](../../OmegaY/Reflection.lean): `R S θ a b := Por.R S θ a b`. `key_weaken` and `finite_reflection` return the `Por` theorems.
- [OmegaY/Reflection/OrdinalSupply.lean](../../OmegaY/Reflection/OrdinalSupply.lean): `Label` and `top` are those of `Por.Supply`. `initial_finite_graph` returns `Por.Supply.initial_finite_graph`.
- [OmegaY/Model.lean](../../OmegaY/Model.lean) and [OmegaY/KeyReflection.lean](../../OmegaY/KeyReflection.lean): the instances for the syntax `keySyntax m` of keys of length $`m`$. They are unchanged from Phyrion's files (KeyReflection only changes an import).

## 2. Finite reflection

**What is shown.** Under the assumptions of [06](06-combinatorial-layer.md) §5, construct $`g`$. Notation: $`n`$ is the number of vertices, $`f : \mathrm{Fin}\ n \to \mathrm{Label}`$ the labels of the vertices, $`b`$ the top, $`\theta`$ a key, $`\mathrm{cut}`$ the cut, the control relation is $`R(\theta, f(\mathrm{cut}), b)`$, $`G`$ the list of internal atoms, and $`N`$ the list of demands (top atoms). For an atom $`e`$, write $`t_e`$ for its template, $`p_e`$ for its parent and $`q_e`$ for its child.

**The reflected formula (`reflForm`).** The variables are $`v_0, \ldots, v_{n-1}`$, and the positions $`i \lt \mathrm{cut}`$ are parameters. The literals (`reflLits`) are of three kinds:

```math
\bigwedge_{i, j \lt n} \bigl( (v_i \lt v_j) \iff (i \lt j) \bigr) \ \land\ \bigwedge_{e \in G} \mathrm{Rel}_{e}(\vec v) \ \land\ \bigwedge_{d \in N} \mathrm{Top}_{d}(\vec v)
```

$`\mathrm{Rel}_e(\vec v)`$ is the internal relation $`\mathrm{Rel}_{t_e, p_e, q_e}(\vec v)`$, that is, $`R(\mathrm{eval}\ t_e\ \vec v, v_{p_e}, v_{q_e})`$. $`\mathrm{Top}_d(\vec v)`$ is the top predicate $`\mathrm{Top}_{t_d, p_d}(\vec v)`$, that is, $`R(\mathrm{eval}\ t_d\ \vec v, v_{p_d}, c)`$, where $`c`$ is the height of the structure in which the formula is read ([07](07-relation-r.md) §2). `reflLits_holds` rewrites "all these literals hold" into three statements: "the order of $`v`$ is the order of the indices", "$`G`$ holds", and "the keys of $`N`$ are defined and $`N`$ holds".

**Proof.**

1. From `R_iff`, get the elementarity $`E`$ at key $`\theta`$ between the structures of heights $`f(\mathrm{cut})`$ and $`b`$.
2. The parameters $`f(i)`$ ($`i \lt \mathrm{cut}`$) are below $`f(\mathrm{cut})`$, since $`f`$ is strictly increasing.
3. At height $`b`$, $`v = f`$ satisfies the formula. The order follows from $`f`$ being strictly increasing, $`\mathrm{Rel}`$ from the assumption on $`G`$, and $`\mathrm{Top}`$ from "the keys are below $`\theta`$" (`KeysBelow`) and "$`N`$ holds for the top $`b`$".
4. By $`E`$ the formula is true at height $`f(\mathrm{cut})`$ as well. Call its witness $`g`$.
5. $`g`$ satisfies:
   - by the order literals, $`g`$ is strictly increasing;
   - $`g(i) \lt f(\mathrm{cut})`$ (witnesses lie in the domain);
   - $`g(i) = f(i)`$ for $`i \lt \mathrm{cut}`$ (parameters);
   - $`G`$ holds at $`g`$, and $`N`$ holds for the top $`f(\mathrm{cut})`$ (the top predicates at height $`f(\mathrm{cut})`$ are $`R(\cdot, \cdot, f(\mathrm{cut}))`$);
   - $`g \le f`$ pointwise: equal for $`i \lt \mathrm{cut}`$, and otherwise $`g(i) \lt f(\mathrm{cut}) \le f(i)`$. $`\square`$

**Example (block 0 → 1 of [06](06-combinatorial-layer.md) §8).** Let $`n = 2`$, $`f = (f_0, f_1)`$, $`\mathrm{cut} = 0`$, $`\theta = (f_0, \top)`$ and $`b = f_2`$. $`G`$ is the two edges of column 1 and $`N`$ is the one lower edge. The reflected formula is as follows (there are no parameters). $`\mathrm{Top}_{(v_0, v_0)}(v_0)`$ says that the top predicate of key $`(v_0, v_0)`$ holds at $`v_0`$ (here the value of the key is written as the subscript instead of the template).

```math
\exists v_0\ \exists v_1\ \bigl[\ v_0 \lt v_1 \land R((v_0, v_0), v_0, v_1) \land R((v_0, \top), v_0, v_1) \land \mathrm{Top}_{(v_0, v_0)}(v_0)\ \bigr]
```

- At height $`f_2`$, $`v = (f_0, f_1)`$ is a witness. The key $`(f_0, f_0)`$ of the top literal is below $`\theta = (f_0, \top)`$, so it is defined, and $`R((f_0, f_0), f_0, f_2)`$ holds.
- Reflection gives $`g_0 \lt g_1 \lt f_0`$ satisfying the same conditions for the top $`f_0`$. The key of the top literal becomes $`(g_0, g_0)`$: the point named by the key is itself a witness.

**Not used.** That $`b`$ is Good, or that $`b`$ or $`f(\mathrm{cut})`$ is a limit.

## 3. The first representation

### 3.1 Absoluteness of top predicates

**Theorem (`top_abs`).** Let $`\alpha`$ be a label with $`\mathrm{Good}(\alpha)`$ and $`\alpha \lt \omega_1`$. For every key $`\kappa`$ and label $`x \lt \alpha`$:

```math
R(\kappa, x, \alpha) \iff R(\kappa, x, \omega_1)
```

**Proof.** Well-founded induction on $`\kappa`$ (`WellFoundedLT.induction`, [02](02-well-founded.md) §2).

1. Unfold both sides with `R_iff`. Both $`x \lt \alpha`$ and $`x \lt \omega_1`$ are true. What remains is that a formula $`\varphi`$ at key $`\kappa`$ (parameters $`\lt x`$) has the same truth value in the structure $`\mathfrak A^\alpha_\kappa`$ of height $`\alpha`$ and the structure $`\mathfrak A^{\omega_1}_\kappa`$ of height $`\omega_1`$ (`absA`).
2. $`\varphi`$ reads only top predicates of keys $`\kappa' \lt \kappa`$. By the induction hypothesis, on points below $`\alpha`$ they have the same truth value at height $`\alpha`$ and at height $`\omega_1`$ (`lit_abs`).
3. From height $`\alpha`$ to height $`\omega_1`$: the witnesses are below $`\alpha \lt \omega_1`$, and by 2 the literals have the same truth values.
4. From height $`\omega_1`$ to height $`\alpha`$: take a witness $`v \lt \omega_1`$.
   - Enlarge `allow` to "always true" (`lit_true`). This gives a formula in $`\mathfrak B`$.
   - By $`\mathrm{Good}(\alpha)`$, lower the witness, with the positions where $`v_i \lt \alpha`$ as parameters (`lower`). The new witness $`w`$ is below $`\alpha`$, equals $`v_i`$ where $`v_i \lt \alpha`$, and $`w \le v`$ pointwise.
   - By $`w \le v`$ and monotonicity of `eval`, the keys of the top literals stay below $`\kappa`$ (`lit_lower`).
   - By 2, return to the top predicates of height $`\alpha`$. $`\square`$

The third item of step 4 uses "lowering pointwise keeps the key condition" of [03](03-sigma1-elementary.md) §8.

### 3.2 Good points are in the relation R

**Theorem (`good_R`).** For labels $`\alpha, \beta`$, if $`\mathrm{Good}(\alpha)`$, $`\mathrm{Good}(\beta)`$ and $`\alpha \lt \beta \lt \omega_1`$, then $`R(\kappa, \alpha, \beta)`$ for every key $`\kappa`$.

**Proof.** $`\alpha \lt \beta`$ holds. For a formula $`\psi`$ at key $`\kappa`$ and parameters $`\vec p \lt \alpha`$, chain the equivalences

```math
\mathfrak A^{\alpha}_{\kappa} \models \psi \iff \mathfrak A^{\omega_1}_{\kappa} \models \psi \iff \mathfrak A^{\beta}_{\kappa} \models \psi
```

The first is `absA'` at $`\alpha`$, the second `absA'` at $`\beta`$ (`absA'` is `absA` with `top_abs` plugged in). $`\square`$

The key $`\kappa`$ is arbitrary: Good points are related at every key.

### 3.3 A representation of every finite graph

**Theorem (`initial_finite_graph`).** For every graph $`(G, N)`$ there are $`\beta \lt \omega_1`$ and a strictly increasing $`f \lt \beta`$ such that $`G`$ holds at $`f`$ and $`N`$ holds for the top $`\beta`$.

**Proof.** Let $`n`$ be the number of vertices of the graph. Put $`\beta := c_n`$ and $`f(i) := c_i`$ (the sequence of Good points of [08](08-closure-chain.md) §7).

- $`f`$ is strictly increasing and $`c_i \lt c_n`$ (`points_strictMono`), and $`c_n \lt \omega_1`$ (`points_lt`).
- An internal atom $`e`$ has parent $`\lt`$ child, so `good_R` gives $`R(\mathrm{eval}\ t_e\ f, c_{p_e}, c_{q_e})`$.
- A top atom $`d`$ has parent $`\lt n`$, so `good_R` gives $`R(\mathrm{eval}\ t_d\ f, c_{p_d}, c_n)`$. $`\square`$

One sequence $`c`$ represents all graphs at once. No key condition (`KeysBelow`) is needed.

### 3.4 First representation with a control

`initial_controlled_graph` in [OmegaY/Model.lean](../../OmegaY/Model.lean) uses `initial_finite_graph` with one more top atom (the one that plays the role of `control` of [06](06-combinatorial-layer.md) §7) added to $`N`$, and also obtains the control relation and "the demand keys are below the key of `control`". The key comparison follows from the comparison of templates (`eval_lt_of_template_lt`). The combinatorial layer does not call this theorem (checked with `grep`).

## 4. The final theorems and the axioms

The final theorem is connected as follows ([OmegaY/Expansion/WellFounded.lean](../../OmegaY/Expansion/WellFounded.lean)).

```lean
theorem omegaY_step_wellFounded : WellFounded Dynamics.Step :=
  Dynamics.step_wellFounded_of_actual_representation_descent actual_representation_descent
```

- `actual_representation_descent` is the descent of [06](06-combinatorial-layer.md) §8. Finite reflection and key weakening are used in the splicing inside it.
- The first representation comes from `keyRepresentation_exists`, which uses `initial_finite_graph`.
- The other three final theorems follow from `omegaY_step_wellFounded` by combinatorial arguments only ([05](05-omegay-mountain.md) §7).

**Axioms.** [OmegaY/Audit.lean](../../OmegaY/Audit.lean) checks the axioms of every theorem whose name starts with `OmegaY.` or `Por.`. All depend only on `propext`, `Classical.choice` and `Quot.sound` ([README](../../README-en.md) "Axiom audit").

**Strength.** The proof uses the axiom of choice and the regularity of $`\omega_1`$. The labels are Good points below $`\omega_1`$ whose concrete values are unknown. No ordinal bound and no ordinal notation system (a way to write ordinals as finite strings of symbols) is obtained.

## 5. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "Proofs of the three theorems" | summary of key weakening, finite reflection and the first labelling |
| [README](../../README-en.md) "Axiom audit" | the axioms of §4 |
| [notes/01-design.md](../../notes/01-design.md) §3, §4 | the proofs of the three theorems and the split into files |
| [Por/Relation.lean](../../Por/Relation.lean) | §2 |
| [Por/Supply.lean](../../Por/Supply.lean) | §3 |
| [OmegaY/Reflection.lean](../../OmegaY/Reflection.lean), [OmegaY/Reflection/OrdinalSupply.lean](../../OmegaY/Reflection/OrdinalSupply.lean), [OmegaY/Model.lean](../../OmegaY/Model.lean) | the files of §1 |
| [OmegaY/Expansion/WellFounded.lean](../../OmegaY/Expansion/WellFounded.lean), [OmegaY/Audit.lean](../../OmegaY/Audit.lean) | §4 |

## 6. Lean correspondence

| Concept | Lean | File |
|---|---|---|
| the reflected formula | `reflLits`, `reflForm`, `reflLits_holds` | [Por/Relation.lean](../../Por/Relation.lean) |
| finite reflection | `finite_reflection` | same |
| parts for literals | `lit_true`, `lit_lower`, `lit_abs` | [Por/Supply.lean](../../Por/Supply.lean) |
| lowering witnesses | `lower` | same |
| one step of absoluteness | `absA`, `absA'` | same |
| absoluteness of top predicates | `top_abs` | same |
| relation between Good points | `good_R` | same |
| first representation | `initial_finite_graph` | same |
| the files of §1 | `Reflection.R`, `Reflection.key_weaken`, `Reflection.finite_reflection` | [OmegaY/Reflection.lean](../../OmegaY/Reflection.lean) |
| same | `OrdinalSupply.initial_finite_graph` | [OmegaY/Reflection/OrdinalSupply.lean](../../OmegaY/Reflection/OrdinalSupply.lean) |
| instances for keys of length $`m`$ | `Model.R`, `Model.key_weaken`, `Model.finite_reflection`, `Model.initial_finite_graph`, `Model.initial_controlled_graph` | [OmegaY/Model.lean](../../OmegaY/Model.lean) |
| final theorems | `omegaY_step_wellFounded`, `omegaY_generated_isWellOrder`, `omegaY_descendants_isWellOrder`, `omegaY_trajectory_terminates` | [OmegaY/Expansion/WellFounded.lean](../../OmegaY/Expansion/WellFounded.lean) |
