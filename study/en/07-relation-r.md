[← Back](README.md) | [English](07-relation-r.md) | [Japanese](../07-relation-r.md)

# The relation R

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | labels $`\mathrm{Label}`$ (§6) |
| [02 Well-founded relations and well-founded recursion](02-well-founded.md) | keys $`\mathrm{Key}_m`$ and their order, stage, top, the order $`\lhd`$ of stages (§3), well-founded recursion, guarded recursion |
| [03 Structures and Σ₁-elementary substructures](03-sigma1-elementary.md) | height, point, witness, key syntax, template, $`\mathrm{eval}`$, position, normal form $`(n, F, L)`$, structures $`(c; \lt, \mathrm{rel}, \mathrm{top}, \mathrm{allow})`$, top predicate (§7), the way two structures are compared and Lemmas 1–3 (§8) |
| [04 Patterns of resemblance](04-patterns-of-resemblance.md) | the idea of making top predicates atomic symbols |
| [06 Phyrion's combinatorial layer for ω-Y](06-combinatorial-layer.md) | combinatorial layer, the role of $`R(\theta, a, b)`$, key weakening among the three theorems |

This note explains the definition of the label relation $`R`$ of this repository and the properties that follow directly from it.

## 1. Notation

- $`\mathrm{Label}`$: the labels ([01](01-ordinals.md) §6).
- $`\mathrm{Key}_m`$: the keys of length $`m`$ and their lexicographic order $`\lt`$ ([02](02-well-founded.md) §3).
- Stages $`(b, \theta) \in \mathrm{Label} \times \mathrm{Key}_m`$ and their lexicographic order $`\lhd`$ ([02](02-well-founded.md) §3): $`(b', \kappa') \lhd (b, \theta) \iff b' \lt b \lor (b' = b \land \kappa' \lt \theta)`$.
- Key syntax: the key syntax of ω-Y in [03](03-sigma1-elementary.md) §7. The definitions and proofs below use only its monotonicity and the fact that $`\mathrm{Label}`$ and $`\mathrm{Key}_m`$ are well-ordered linear orders.
- $`R(\theta, a, b)`$: key $`\theta \in \mathrm{Key}_m`$, lower point $`a \in \mathrm{Label}`$, upper point $`b \in \mathrm{Label}`$ (the top). $`R`$ is defined in §4. §2 and §3 use $`R`$ in the interpretations of symbols. As §5 explains, this use is not circular.

## 2. The language

There are three kinds of symbols. $`n`$ is the number of variables, $`t \in \mathcal T_n`$ a template and $`i, j \lt n`$ positions ([03](03-sigma1-elementary.md) §7).

| Symbol | Arity | Meaning (in the structure of height $`c`$) |
|---|---|---|
| $`\lt`$ | 2 | order of labels |
| $`\mathrm{Rel}_{t,i,j}`$ | $`n`$ | $`\mathrm{Rel}_{t,i,j}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ v_j)`$ |
| $`\mathrm{Top}_{t,i}`$ | $`n`$ | $`\mathrm{Top}_{t,i}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ c)`$ |

$`\mathrm{Rel}_{t,i,j}`$ relates points to points, and $`\mathrm{Top}_{t,i}`$ relates a point to the top $`c`$ (a top predicate) ([03](03-sigma1-elementary.md) §7). $`c`$ itself is not in the domain. Both symbols compute their key from the $`n`$ points by the template.

In the form of [03](03-sigma1-elementary.md) §7, the interpretations are the following $`\mathrm{relR}`$ and $`\mathrm{topR}_c`$.

```math
\mathrm{relR}(\kappa, x, y) :\iff R(\kappa, x, y), \qquad \mathrm{topR}_c(\kappa, x) :\iff R(\kappa, x, c)
```

We call the interpretations of the table the **true interpretations**, to distinguish them from the stage interpretations of §5. The true interpretation of the top predicates depends on the height $`c`$.

## 3. The structure 𝔄^c_θ

**Definition (the structure 𝔄^c_θ).** For a key $`\theta`$ and a label $`c`$, the structure $`\mathfrak A^c_\theta`$ of height $`c`$ is the following (notation of [03](03-sigma1-elementary.md) §7).

```math
\mathfrak A^c_\theta = \bigl(c;\ \lt,\ \mathrm{relR},\ \mathrm{topR}_c,\ \mathrm{allow}_\theta\bigr), \qquad \mathrm{allow}_\theta(\kappa) :\iff \kappa \lt \theta
```

- The domain is $`\{x \mid x \lt c\}`$.
- $`\mathrm{Rel}_{t,i,j}`$ is present for every template.
- $`\mathrm{Top}_{t,i}(\vec v)`$ is defined only when $`\mathrm{eval}\ t\ \vec v \lt \theta`$. Where it is not defined, both $`\mathrm{Top}_{t,i}`$ and $`\neg\mathrm{Top}_{t,i}`$ are false ([03](03-sigma1-elementary.md) §8).

**Example.** Let the key length be $`m = 1`$ and $`\theta = (\omega)`$. The templates are those of the key syntax of ω-Y ([03](03-sigma1-elementary.md) §7): $`t = (\mathrm{some}\ 0)`$ gives the key $`(v_0)`$ and $`t_\top = (\mathrm{none})`$ gives the key $`(\top)`$.

- $`\mathrm{Top}_{t,i}`$ is defined when $`v_0 \lt \omega`$, that is, when $`v_0`$ is a natural number.
- $`\mathrm{Top}_{t_\top,i}`$ is defined nowhere, because the key $`(\top)`$ is $`\ge \theta`$.
- If $`\theta = (\top)`$, $`\mathrm{Top}_{t,i}`$ is defined everywhere. $`\mathrm{Top}_{t_\top,i}`$ is still defined nowhere, because $`(\top) \lt (\top)`$ is false.
- The formula $`\varphi = (2, \{0\}, [v_0 \lt v_1,\ \mathrm{Top}_{t,1}])`$ means the following in $`\mathfrak A^c_{(\omega)}`$ (the entry $`p_1`$ of $`\vec p = (p_0, p_1)`$ is not read).

```math
\mathfrak A^c_{(\omega)} \models \varphi(\vec p) \iff p_0 \lt \omega\ \land\ \exists v_1 \lt c\ \bigl(p_0 \lt v_1 \land R((p_0), v_1, c)\bigr)
```

Whether a top predicate is defined was checked with the order of keys written in Python, for $`v_0 \in \{0, 7, \omega, \omega + 3\}`$.

## 4. The definition

**Definition (R).**

```math
R(\theta, a, b) \iff a \lt b \ \land\ \mathfrak A^{a}_{\theta} \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_{\theta}
```

Here $`\mathfrak A^{a}_{\theta} \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_{\theta}`$ is the comparison of [03](03-sigma1-elementary.md) §8. That is, for every formula $`\varphi = (n, F, L)`$ and every $`\vec p`$ with $`p_i \lt a`$ at the positions in $`F`$,

```math
\mathfrak A^{a}_{\theta} \models \varphi(\vec p) \iff \mathfrak A^{b}_{\theta} \models \varphi(\vec p)
```

We write $`\mathrm{Elem}(\theta, a, b)`$ for this comparison (with the true interpretations). The top predicates of the two structures are different ($`R`$ to $`a`$ and $`R`$ to $`b`$) (Difference 1 of [03](03-sigma1-elementary.md) §8).

The condition "root label $`\le a`$" of the $`R`$ of the 1-Y version ([01](01-ordinals.md) §7) is not present here.

## 5. The recursion

The right side reads $`R`$ itself. We use well-founded recursion on the lexicographic order $`\lhd`$ of stages $`(b, \theta)`$ ([02](02-well-founded.md) §3), defining all $`a`$ at once.

**What the right side reads.** Only three kinds, all at smaller stages.

| What is read | Stage | Why smaller |
|---|---|---|
| $`\mathrm{Rel}_{t,i,j}(\vec v)`$, that is $`R(\kappa, x, y)`$ | $`(y, \kappa)`$ | the points are below the height ($`a`$ or $`b`$), so $`y \lt b`$ |
| a top predicate $`R(\kappa, x, a)`$ of $`\mathfrak A^{a}_\theta`$ | $`(a, \kappa)`$ | $`a \lt b`$ |
| a defined top predicate $`R(\kappa, x, b)`$ of $`\mathfrak A^{b}_\theta`$ | $`(b, \kappa)`$ | it is defined only when $`\kappa \lt \theta`$ |

The third row is the main point. Since the top predicates of $`\mathfrak A^{b}_\theta`$ are defined only below the key $`\theta`$, the right side does not read the stage $`(b, \theta)`$ itself.

**Guarded recursion.** The value at the stage $`(b, \theta)`$ is the set of $`a`$ with $`R(\theta, a, b)`$. It is defined with the following **stage interpretations**. The superscript $`\mathrm{st}`$ marks a stage interpretation. Each of the three contains, as a guard, the condition that the stage is smaller ([02](02-well-founded.md) §5).

| Stage interpretation | Formula |
|---|---|
| $`\mathrm{relR}^{\mathrm{st}}(\kappa, x, y)`$ | $`y \lt b \land R(\kappa, x, y)`$ |
| $`\mathrm{topR}^{\mathrm{st},a}(\kappa, x)`$ | $`a \lt b \land R(\kappa, x, a)`$ |
| $`\mathrm{topR}^{\mathrm{st},b}(\kappa, x)`$ | $`\kappa \lt \theta \land R(\kappa, x, b)`$ |

Write $`\mathrm{Elem}^{\mathrm{st}}(\theta, a, b)`$ for $`\Sigma_1`$-elementarity with the stage interpretations.

```math
\mathrm{Elem}^{\mathrm{st}}(\theta, a, b) :\iff \bigl(a;\ \lt,\ \mathrm{relR}^{\mathrm{st}},\ \mathrm{topR}^{\mathrm{st},a},\ \mathrm{allow}_\theta\bigr) \preccurlyeq_{\Sigma_1} \bigl(b;\ \lt,\ \mathrm{relR}^{\mathrm{st}},\ \mathrm{topR}^{\mathrm{st},b},\ \mathrm{allow}_\theta\bigr)
```

The stage interpretations read $`R`$ only at smaller stages, so the well-founded recursion of [02](02-well-founded.md) §4 determines $`R`$. The defining equation is the following guarded equation.

```math
R(\theta, a, b) \iff a \lt b \land \mathrm{Elem}^{\mathrm{st}}(\theta, a, b)
```

## 6. Removing the guards

**Lemma (removing the guards).** If $`a \lt b`$, then $`\mathrm{Elem}^{\mathrm{st}}(\theta, a, b) \iff \mathrm{Elem}(\theta, a, b)`$. That is, $`\Sigma_1`$-elementarity for the stage interpretations is equivalent to $`\Sigma_1`$-elementarity for the true interpretations.

**Proof.** Show that the guards are true wherever a formula reads, on both sides. Then apply Lemma 1 of [03](03-sigma1-elementary.md) §8 at height $`a`$ and at height $`b`$.

1. $`\mathrm{Rel}`$: Lemma 1 needs agreement only where the second point is below the height ($`a`$ or $`b`$). Both heights are $`\le b`$, so the guard $`y \lt b`$ is true.
2. Top predicates at height $`a`$: the guard is $`a \lt b`$, which is the assumption.
3. Top predicates at height $`b`$: Lemma 1 needs agreement only where $`\mathrm{allow}_\theta(\kappa)`$, that is $`\kappa \lt \theta`$. The guard $`\kappa \lt \theta`$ is then true.

So for each $`\varphi, \vec p`$, at height $`a`$ and at height $`b`$, the two interpretations give the same truth value. $`\square`$

**Theorem (defining equation).**

```math
R(\theta, a, b) \iff a \lt b \land \mathrm{Elem}(\theta, a, b)
```

**Proof.** Apply the lemma (removing the guards) under $`a \lt b`$ to the guarded equation of §5. $`\square`$

## 7. Properties that follow directly

**Theorem (strictness).** $`R(\theta, a, b)`$ implies $`a \lt b`$. This is the first condition on the right side of the defining equation.

**Theorem (key weakening).** If $`\theta \le \Theta`$ and $`R(\Theta, a, b)`$, then $`R(\theta, a, b)`$. This is the key weakening of [06](06-combinatorial-layer.md) §5.

**Proof.** The defining equation gives $`a \lt b`$ and $`\mathrm{Elem}(\Theta, a, b)`$. Since $`\theta \le \Theta`$, $`\kappa \lt \theta \implies \kappa \lt \Theta`$. Take $`\varphi = (n, F, L)`$ and $`\vec p`$ with $`p_i \lt a`$ at the positions in $`F`$, and show both directions.

**Direction 1: $`\mathfrak A^a_\theta \models \varphi(\vec p) \implies \mathfrak A^b_\theta \models \varphi(\vec p)`$.** Take a witness $`\vec w`$ at height $`a`$ ($`w_i \lt a`$). Form the formula $`\varphi' := (n, \mathrm{Fin}\ n, L)`$ in which every position is a parameter. By Lemma 2 of [03](03-sigma1-elementary.md) §8, $`\mathfrak A^a_\Theta \models \varphi'(\vec w)`$. By $`\mathrm{Elem}(\Theta, a, b)`$, $`\mathfrak A^b_\Theta \models \varphi'(\vec w)`$. All variables of $`\varphi'`$ are fixed, so its witness is $`\vec w`$ itself. Lemma 3 with $`\vec v := \vec w`$ shows that $`\vec w`$ satisfies all literals of $`L`$ in $`\mathfrak A^b_\theta`$ too. So $`\mathfrak A^b_\theta \models \varphi(\vec p)`$.

**Direction 2: $`\mathfrak A^b_\theta \models \varphi(\vec p) \implies \mathfrak A^a_\theta \models \varphi(\vec p)`$.** Take a witness $`\vec v`$ at height $`b`$ ($`v_i \lt b`$). Let $`F' := \{i \mid v_i \lt a\}`$ and $`\varphi' := (n, F', L)`$. Then $`F \subseteq F'`$. By Lemma 2, $`\mathfrak A^b_\Theta \models \varphi'(\vec v)`$. At the positions in $`F'`$ we have $`v_i \lt a`$, so $`\mathrm{Elem}(\Theta, a, b)`$ gives $`\mathfrak A^a_\Theta \models \varphi'(\vec v)`$, with a witness $`\vec w`$ ($`w_i \lt a`$) satisfying

```math
\forall i \in F'\ \ w_i = v_i, \qquad \forall i \notin F'\ \ w_i \lt a \le v_i, \qquad \text{hence}\ \ \forall i \lt n\ \ w_i \le v_i
```

By Lemma 3, $`\vec w`$ satisfies all literals of $`L`$ in $`\mathfrak A^a_\theta`$ too. At the positions in $`F`$, $`w_i = v_i = p_i`$. So $`\mathfrak A^a_\theta \models \varphi(\vec p)`$. $`\square`$

The second direction needs to lower the witnesses pointwise. That is why the monotonicity of the key syntax ([03](03-sigma1-elementary.md) §7) is used, through Lemma 3.

**Property (defined top predicates agree).** Let $`R(\theta, a, b)`$ and let every entry of $`\vec v`$ be below $`a`$. If $`\mathrm{eval}\ t\ \vec v \lt \theta`$, then

```math
R(\mathrm{eval}\ t\ \vec v,\ v_i,\ a) \iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ b)
```

**Reason.** Use the quantifier-free formula $`(n, \mathrm{Fin}\ n, [\mathrm{Top}_{t,i}])`$ with parameters $`\vec v`$. At height $`a`$ it means the left side, at height $`b`$ the right side. The proof does not use this property. It uses the theorem (absoluteness of the top predicates) of [09](09-obligations.md) §3.1, which has a similar form: the top predicates agree between a Good point ([08](08-closure-chain.md) §1) and $`\omega_1`$.

**Property (the lower point is a limit ordinal).** $`R(\theta, a, b)`$ implies that $`a`$ is a nonzero limit ordinal.

**Reason.** As in the example of [03](03-sigma1-elementary.md) §5.

- If $`a = 0`$: $`\varphi = (1, \emptyset, [\,])`$, that is $`\exists v_0\ (\text{true})`$, is true at height $`b`$ ($`v_0 = 0 \lt b`$) and false at height 0.
- If $`a = \gamma + 1`$: use $`\varphi = (2, \{0\}, [v_0 \lt v_1])`$ with the parameter $`p_0 = \gamma \lt a`$. It is true at height $`b`$ ($`v_1 = \gamma + 1 \lt b`$) and false at height $`a`$.

Both contradict $`\mathrm{Elem}`$. The combinatorial layer does not use this property.

## 8. Properties that are not used

**Transitivity.** $`R(\theta, a, b) \land R(\theta, b, c) \implies R(\theta, a, c)`$.

**Proof.** $`a \lt b \lt c`$. The structure $`\mathfrak A^b_\theta`$ is the same in both comparisons. If $`p_i \lt a`$ at the positions in $`F`$, then also $`p_i \lt b`$, so $`\mathfrak A^a_\theta \models \varphi(\vec p) \iff \mathfrak A^b_\theta \models \varphi(\vec p) \iff \mathfrak A^c_\theta \models \varphi(\vec p)`$. $`\square`$

The combinatorial layer does not use this property.

## 9. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "The relation R" | the defining equation and the three kinds of reads in the recursion on stages |
| [README](../../README-en.md) "Proofs of the three theorems" | summary of the proof of key weakening (§7) |
| [notes/01-design.md](../../notes/01-design.md) §2, §3.1 (Japanese) | definition, recursion, key weakening |

## 10. Lean correspondence

| Concept | Lean | File |
|---|---|---|
| stages and $`\lhd`$ | `StageLT`, `stage_wf` | [Por/Relation.lean](../../Por/Relation.lean) |
| stage interpretations and the guarded step | `stepF` (the guard $`a \lt b`$ is written once, as the leading `∃ hab : a < s.1`) | same |
| $`R`$ | `Por.R S θ a b := stage_wf.fix (stepF S) (b, θ) a` | same |
| true interpretations | `relR`, `topR c` | same |
| $`\mathrm{Elem}(\theta, a, b)`$ | `ElemL (relR S) (topR S a) (topR S b) θ a b` | [Por/Formula.lean](../../Por/Formula.lean) |
| lemma (removing the guards) and the defining equation | `R_iff` (uses `WellFounded.fix_eq` and `sat_congr`) | [Por/Relation.lean](../../Por/Relation.lean) |
| strictness | `R_lt` | same |
| key weakening | `key_weaken` (uses `Lit.holds_allow_mono` and `Lit.holds_of_le`) | same |
| names read by the combinatorial layer | `Reflection.R`, `Reflection.key_weaken`, `Model.key_weaken` | [OmegaY/Reflection.lean](../../OmegaY/Reflection.lean), [OmegaY/Model.lean](../../OmegaY/Model.lean) |
| defined top predicates agree, the lower point is a limit, transitivity | none (not proved in Lean) | |
