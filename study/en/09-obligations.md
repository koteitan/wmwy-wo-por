[← Back](README.md) | [English](09-obligations.md) | [Japanese](../09-obligations.md)

# Proofs of the three theorems

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | $`\lt`$ on ordinals is well-founded (§1), labels (§6) |
| [02 Well-founded relations and well-founded recursion](02-well-founded.md) | well-founded induction (§2), the order of keys is well-founded (§3) |
| [03 Structures and Σ₁-elementary substructures](03-sigma1-elementary.md) | the normal form $`(n, F, L)`$, literals, $`\mathrm{Rel}_{t,i,j}`$, $`\mathrm{Top}_{t,i}`$, satisfaction (§7), Lemmas 2 and 3 (§8) |
| [06 Phyrion's combinatorial layer for ω-Y](06-combinatorial-layer.md) | atom, diagram, holds, representation, top, top atom, demand, cut, control relation, demand with key below $`\theta`$, finite reflection, the three theorems, entry theorem, $`G_D(s)`$ |
| [07 The relation R](07-relation-r.md) | $`R`$, the structure $`\mathfrak A^c_\theta`$, true interpretation, $`\mathrm{Elem}`$, the defining equation (§6), the theorem of key weakening (§7) |
| [08 Closure below ω₁ and the chain](08-closure-chain.md) | $`\mathfrak B`$, $`\mathfrak B{\restriction}\gamma`$, Good, the chain $`c_t`$ and Properties 9–11 (§7) |

This note explains how the relation $`R`$ satisfies the three theorems of the combinatorial layer. The main parts are finite reflection (§2) and the first representation (§3).

## 1. List of theorems

The labels are $`\mathrm{Label}`$ ([01](01-ordinals.md) §6), and $`R`$ is the relation of [07](07-relation-r.md).

| Theorem ([06](06-combinatorial-layer.md) §5) | Section |
|---|---|
| key weakening | [07](07-relation-r.md) §7 |
| finite reflection | §2 |
| initial representation | §3 |

- Key weakening: this is the theorem (key weakening) of [07](07-relation-r.md) §7 itself. It is proved in the form $`\theta \le \Theta`$, which is the form the combinatorial layer asks for.
- The well-foundedness of the order of labels is the well-foundedness of $`\lt`$ on ordinals ([01](01-ordinals.md) §1).

## 2. Finite reflection

**Goal.** Under the hypotheses of [06](06-combinatorial-layer.md) §4, build $`g`$. Notation: $`G`$, $`f`$, $`\mathrm{cut} \in \mathbb N`$, the key $`\theta`$, the label $`\beta`$ and $`\mathrm{needs}`$ are as in [06](06-combinatorial-layer.md) §4. $`n`$ is the size of $`G`$, $`f`$ the representation, the control relation is $`R(\theta, f(\mathrm{cut}), \beta)`$, and the demands are $`d = (t_d, p_d)`$. An atom of $`G`$ is written $`e = (t_e, p_e, q_e)`$.

**Proof.**

1. Let $`a := f(\mathrm{cut})`$. By the defining equation of [07](07-relation-r.md) §6, $`a \lt \beta`$ and $`\mathrm{Elem}(\theta, a, \beta)`$.
2. Let the parameter positions be $`F := \{i \mid i \lt \mathrm{cut}\}`$ and the parameters $`f(0), \ldots, f(\mathrm{cut} - 1)`$. Since $`f`$ is increasing, all are $`\lt a`$.
3. Build the formula $`\Phi := (n, F, L)`$ in the normal form of [03](03-sigma1-elementary.md) §7. $`L`$ consists of these literals.
   - Order: for each $`i, j \lt n`$, $`v_i \lt v_j`$ if $`i \lt j`$, and $`\neg(v_i \lt v_j)`$ otherwise.
   - Atoms: $`\mathrm{Rel}_{t_e, p_e, q_e}`$ for each $`e \in G`$.
   - Demands: $`\mathrm{Top}_{t_d, p_d}`$ for each $`d \in \mathrm{needs}`$.

   With $`z_i := f(i)`$ for $`i \lt \mathrm{cut}`$ and $`z_i := v_i`$ for $`\mathrm{cut} \le i \lt n`$, $`\Phi`$ is the formula

```math
\Phi \equiv \exists v_{\mathrm{cut}} \cdots \exists v_{n-1}\ \Bigl[\ \bigwedge_{i \lt j \lt n} z_i \lt z_j \ \land\ \bigwedge_{j \le i \lt n} \neg(z_i \lt z_j) \ \land\ \bigwedge_{e \in G} \mathrm{Rel}_{t_e, p_e, q_e}(\vec z) \ \land\ \bigwedge_{d \in \mathrm{needs}} \mathrm{Top}_{t_d, p_d}(\vec z)\ \Bigr]
```

4. $`\Phi`$ can be read in the structure $`\mathfrak A^c_\theta`$ of any key. There is no level condition as in the 1-Y version. The top predicate $`\mathrm{Top}_{t_d, p_d}(\vec z)`$ is defined only when the key $`\mathrm{eval}\ t_d\ \vec z`$ is below $`\theta`$ ([07](07-relation-r.md) §3).
5. $`\Phi`$ is true at height $`\beta`$ ($`\mathfrak A^\beta_\theta \models \Phi(f)`$). With witnesses $`v_i := f(i)`$ we get $`z = f`$. The order part follows from condition 2 of the representation and the $`\mathrm{Rel}`$ part from condition 3. The $`\mathrm{Top}`$ part follows from the keys of the demands being below $`\theta`$ (hypothesis 5, so they are defined) and the demands holding for the top $`\beta`$ (hypothesis 6, $`R(\mathrm{eval}\ t_d\ f, f(p_d), \beta)`$).
6. By the elementarity of step 1, $`\Phi`$ is true at height $`a`$ ($`\mathfrak A^a_\theta \models \Phi(f)`$). Take its witnesses $`v'_i \lt a`$.
7. Define $`g`$ by $`g(i) := f(i)`$ for $`i \lt \mathrm{cut}`$ and $`g(i) := v'_i`$ otherwise.
   - $`g`$ is strictly increasing (the order part of $`\Phi`$).
   - Every atom of $`G`$ holds for $`g`$ (the $`\mathrm{Rel}`$ part of $`\Phi`$; $`\mathrm{Rel}`$ is interpreted by $`R`$ itself).
   - $`g(i) \lt a`$ (on the left $`f(i) \lt f(\mathrm{cut})`$; on the right the witnesses are $`\lt a`$). So $`g(i) \lt \omega_1`$, and $`g`$ is a representation of $`G`$.
   - $`g(i) \le f(i)`$ (equal for $`i \lt \mathrm{cut}`$; otherwise $`g(i) \lt a = f(\mathrm{cut}) \le f(i)`$).
   - Every demand has $`R(\mathrm{eval}\ t_d\ g, g(p_d), a)`$ (at height $`a`$, $`\mathrm{Top}_{t,i}(\vec v)`$ means $`R(\mathrm{eval}\ t\ \vec v, v_i, a)`$). $`\square`$

**Example 1.** Use Example 2 of [06](06-combinatorial-layer.md) §3 (step 0 of the expansion of $`(1, 2, 4)`$). $`G`$ is the diagram of $`(1, 2)`$ (atom $`((0), 0, 1)`$), $`n = 2`$, $`\mathrm{cut} = 1`$, $`\theta = (f(1))`$, $`\beta = f(2)`$, and the only demand is $`d = ((0), 1)`$. The parameter is $`p_0 = f(0)`$, and $`\Phi`$ is as follows. Here $`\mathrm{Rel}`$ and $`\mathrm{Top}`$ are spelled out with the values of the keys, and the negative order literals that follow from $`p_0 \lt v_1`$ are omitted. $`\mathrm{Top}_{(p_0)}(v_1)`$ means that the top predicate of key $`(p_0)`$ holds at $`v_1`$, that is, $`R((p_0), v_1, c)`$ at height $`c`$.

```math
\exists v_1\ \bigl[\ p_0 \lt v_1 \land R((p_0), p_0, v_1) \land \mathrm{Top}_{(p_0)}(v_1)\ \bigr]
```

- At height $`\beta`$ the witness is $`v_1 = f(1)`$. The key $`(f(0))`$ of the top predicate is below $`\theta = (f(1))`$, so it is defined, and $`R((f(0)), f(1), f(2))`$ holds.
- Reflection gives a new $`v'_1`$ below $`f(1)`$ with $`R((f(0)), f(0), v'_1)`$ and $`R((f(0)), v'_1, f(1))`$. Then $`g = (f(0), v'_1)`$.

**Example 2.** Use step 0 of the example ($`(1, 3, 3)[2]`$) of [06](06-combinatorial-layer.md) §8. $`n = 2`$, $`f_j := f(j)`$, $`\mathrm{cut} = 0`$, $`\theta = (f_0, \top)`$, $`\beta = f_2`$. $`G`$ is the two edges of column 1, and the demand is the lower edge $`((0, 0), 0)`$. There are no parameters. Spelled out as in Example 1, $`\Phi`$ is

```math
\exists v_0\ \exists v_1\ \bigl[\ v_0 \lt v_1 \land R((v_0, v_0), v_0, v_1) \land R((v_0, \top), v_0, v_1) \land \mathrm{Top}_{(v_0, v_0)}(v_0)\ \bigr]
```

- At height $`f_2`$ the witness is $`v = (f_0, f_1)`$. The key $`(f_0, f_0)`$ of the top predicate is below $`\theta = (f_0, \top)`$, so it is defined, and $`R((f_0, f_0), f_0, f_2)`$ holds.
- Reflection gives $`g_0 \lt g_1 \lt f_0`$ satisfying the same conditions for the top $`f_0`$. The key of the top predicate becomes $`(g_0, g_0)`$. The column 0 that the key points to is not before the cut, and its label is also a witness.

**Difference from the 1-Y version.** The 1-Y version fixed a set of named positions and a bound on symbols to build a formula of a level. They are not needed here, because whether a top predicate is defined is decided by the value of the key ([03](03-sigma1-elementary.md) §8).

**Not used.** That $`\beta`$ is Good, that $`a`$ or $`\beta`$ is a limit.

## 3. The first representation

### 3.1 Absoluteness of the top predicates

**Theorem (absoluteness of the top predicates).** Let $`\delta`$ be a label with $`\mathrm{Good}(\delta)`$ and $`\delta \lt \omega_1`$. For every key $`\kappa`$ and label $`x \lt \delta`$,

```math
R(\kappa, x, \delta) \iff R(\kappa, x, \omega_1)
```

**Proof.** Well-founded induction on $`\kappa`$ ([02](02-well-founded.md) §2; the order of keys is well-founded, [02](02-well-founded.md) §3).

1. Open both sides with the defining equation ([07](07-relation-r.md) §6). Both $`x \lt \delta`$ and $`x \lt \omega_1`$ hold. What remains is that, for every formula $`\varphi = (n, F, L)`$ and every $`\vec p`$ with $`p_i \lt \delta`$ at the positions of $`F`$,

```math
\mathfrak A^\delta_\kappa \models \varphi(\vec p) \iff \mathfrak A^{\omega_1}_\kappa \models \varphi(\vec p)
```

2. For a list of values $`\vec v`$ below $`\delta`$, every literal has the same truth value at heights $`\delta`$ and $`\omega_1`$. The key $`\kappa' := \mathrm{eval}\ t\ \vec v`$ read by a top-predicate literal is defined only when $`\kappa' \lt \kappa`$, and then $`R(\kappa', v_i, \delta) \iff R(\kappa', v_i, \omega_1)`$ by the induction hypothesis. The other literals do not read the height.
3. From height $`\delta`$ to height $`\omega_1`$: the witnesses are below $`\delta \lt \omega_1`$, and by 2 the literals have the same truth values.
4. From height $`\omega_1`$ to height $`\delta`$: take witnesses $`\vec v`$ ($`v_i \lt \omega_1`$).
   - Extend $`\mathrm{allow}`$ to "always true" (Lemma 2 of [03](03-sigma1-elementary.md) §8). Then $`\vec v`$ is a witness in $`\mathfrak B`$.
   - With $`F' := \{i \mid v_i \lt \delta\}`$, use $`\mathrm{Good}(\delta)`$ on the formula $`(n, F', L)`$. The witness $`\vec w`$ in $`\mathfrak B{\restriction}\delta`$ has $`w_i \lt \delta`$, $`w_i = v_i`$ at the positions of $`F'`$, and $`w_i \lt \delta \le v_i`$ at the other positions. So $`\vec w \le \vec v`$ pointwise.
   - By the monotonicity of the key syntax, the key of a top-predicate literal is $`\mathrm{eval}\ t\ \vec w \le \mathrm{eval}\ t\ \vec v \lt \kappa`$, so it stays below $`\kappa`$ (the same reason as Lemma 3 of [03](03-sigma1-elementary.md) §8).
   - Go back to the top predicates of height $`\delta`$ by 2. At the positions of $`F`$, $`p_i \lt \delta`$, so $`w_i = v_i = p_i`$. $`\square`$

The second bullet of 4 lowers the witnesses pointwise. The 1-Y version used "visibility depends only on positions"; here keys depend on values, so monotonicity shows that the keys stay below $`\kappa`$ after lowering.

### 3.2 Good points are related by R

**Theorem (Good points are related by R).** For labels $`\alpha, \beta`$ with $`\mathrm{Good}(\alpha)`$, $`\mathrm{Good}(\beta)`$ and $`\alpha \lt \beta \lt \omega_1`$, $`R(\kappa, \alpha, \beta)`$ holds for every key $`\kappa`$.

**Proof.** $`\alpha \lt \beta`$. For a formula $`\varphi = (n, F, L)`$ and $`\vec p`$ with $`p_i \lt \alpha`$ at the positions of $`F`$, chain these equivalences.

```math
\mathfrak A^{\alpha}_{\kappa} \models \varphi(\vec p) \iff \mathfrak A^{\omega_1}_{\kappa} \models \varphi(\vec p) \iff \mathfrak A^{\beta}_{\kappa} \models \varphi(\vec p)
```

The first is steps 1–4 of the proof of §3.1 at $`\alpha`$, the second the same at $`\beta`$, using the theorem of §3.1 itself instead of the induction hypothesis. $`\square`$

The key $`\kappa`$ is arbitrary. Good points are related by every key.

### 3.3 Representations of all diagrams

**Theorem (representations of all diagrams).** For every diagram $`G`$ (size $`n`$) and every list $`\mathrm{needs}`$ of top atoms, there are a $`\beta \lt \omega_1`$ and a representation $`f`$ of $`G`$ bounded by $`\beta`$ such that every element of $`\mathrm{needs}`$ holds for the top $`\beta`$.

**Proof.** Let $`\beta := c_n`$ and $`f(i) := c_i`$ (the chain of [08](08-closure-chain.md) §7).

- $`f`$ is strictly increasing, and $`c_i \lt c_n`$ for $`i \lt n`$ (Property 10). $`c_n \lt \omega_1`$ (Property 9). Every $`c_i`$ is Good (Property 11).
- An atom $`(t, p, q)`$ has $`p \lt q`$, so $`c_p \lt c_q`$. Applying the theorem of §3.2 with the key $`\mathrm{eval}\ t\ f`$ gives $`R(\mathrm{eval}\ t\ f, c_p, c_q)`$.
- A top atom $`(t, p)`$ has $`p \lt n`$, so $`c_p \lt c_n`$. By the theorem of §3.2, $`R(\mathrm{eval}\ t\ f, c_p, c_n)`$. $`\square`$

One chain $`c`$ represents all diagrams at once. In particular it represents the diagram $`G_D(s)`$ of every expression (with empty $`\mathrm{needs}`$), so the initial representation holds. No key condition and no seed condition is needed.

## 4. Summary and the final theorems

By §1–§3, $`R`$ satisfies all three theorems.

1. $`\theta \le \Theta`$ and $`R(\Theta, a, b)`$ imply $`R(\theta, a, b)`$.
2. Finite reflection ([06](06-combinatorial-layer.md) §4) holds.
3. For every diagram $`G`$ and every list $`\mathrm{needs}`$ of top atoms, there are a $`\beta \lt \omega_1`$ and a representation of $`G`$ bounded by $`\beta`$ for which $`\mathrm{needs}`$ holds for the top $`\beta`$.

Applying the entry theorem of [06](06-combinatorial-layer.md) §5 to this, the one-step expansion relation is well-founded (Theorem 1 of [05](05-omegay-mountain.md) §7). Finite reflection and key weakening are used in the splicing of [06](06-combinatorial-layer.md) §6, §7. The other Theorems 2–4 follow from Theorem 1 by combinatorial arguments only.

**Strength.** The proof uses the axiom of choice and the regularity of $`\omega_1`$. The labels are Good points below $`\omega_1`$ whose values are not known. No ordinal bound and no ordinal notation system (a way to write ordinals as finite strings of symbols) is obtained.

## 5. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "Proofs of the three theorems" | summary of key weakening, finite reflection and the initial labelling |
| [README](../../README-en.md) "Axiom audit" | the axioms the proof uses |
| [notes/01-design.md](../../notes/01-design.md) §3, §4 (Japanese) | proofs of the three theorems and the split into files |

## 6. Lean correspondence

| Concept | Lean | File |
|---|---|---|
| the reflected formula $`\Phi`$ | `reflLits`, `reflForm`, `reflLits_holds` | [Por/Relation.lean](../../Por/Relation.lean) |
| finite reflection (§2) | `Por.finite_reflection` | same |
| pieces for literals (§3.1, steps 2 and 4) | `lit_true`, `lit_lower`, `lit_abs` | [Por/Supply.lean](../../Por/Supply.lean) |
| lowering witnesses (§3.1, step 4) | `lower` | same |
| the equivalence of step 1 of §3.1 | `absA`, `absA'` | same |
| absoluteness of the top predicates | `top_abs` | same |
| Good points are related | `good_R` | same |
| representations of all diagrams | `Por.Supply.initial_finite_graph` (the chain is `points`) | same |
| names called by the combinatorial layer (Phyrion's statements, with the proofs replaced by the theorems of `Por`) | `Reflection.R` (defined as `Por.R`), `Reflection.key_weaken`, `Reflection.finite_reflection` | [OmegaY/Reflection.lean](../../OmegaY/Reflection.lean) |
| same | `OrdinalSupply.Label`, `OrdinalSupply.top`, `OrdinalSupply.initial_finite_graph` | [OmegaY/Reflection/OrdinalSupply.lean](../../OmegaY/Reflection/OrdinalSupply.lean) |
| instance for key length $`m`$ (unchanged from Phyrion's files; `KeyReflection` changes only its imports) | `Model.R`, `Model.key_weaken`, `Model.finite_reflection`, `Model.initial_finite_graph`, `KeyReflection.weaken` | [OmegaY/Model.lean](../../OmegaY/Model.lean), [OmegaY/KeyReflection.lean](../../OmegaY/KeyReflection.lean) |
| the first representation with control ($`\mathrm{needs}`$ plus the control top atom; not called from the combinatorial layer, checked with `grep`) | `Model.initial_controlled_graph` (key comparison by `Keys.eval_lt_of_template_lt`) | [OmegaY/Model.lean](../../OmegaY/Model.lean) |
| the final theorems (§4) | `omegaY_step_wellFounded := Dynamics.step_wellFounded_of_actual_representation_descent actual_representation_descent`, `omegaY_generated_isWellOrder`, `omegaY_descendants_isWellOrder`, `omegaY_trajectory_terminates` | [OmegaY/Expansion/WellFounded.lean](../../OmegaY/Expansion/WellFounded.lean) |
| axiom audit | every theorem whose name starts with `OmegaY.` or `Por.` depends only on `propext`, `Classical.choice`, `Quot.sound` | [OmegaY/Audit.lean](../../OmegaY/Audit.lean) |
