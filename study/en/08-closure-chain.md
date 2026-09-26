[← Back](README.md) | [English](08-closure-chain.md) | [Japanese](../08-closure-chain.md)

# Closure below ω₁ and the chain

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | $`\omega_1`$, regularity (§5), labels (§6), $`\mathrm{Fin}\ n`$, partial parameter lists $`\mathrm{Par}_n(\gamma)`$, $`\mathrm{toP}`$ (§7) |
| [03 Structures and Σ₁-elementary substructures](03-sigma1-elementary.md) | witness, substructure, Tarski–Vaught test, template, normal form $`(n, F, L)`$, literal, structures $`(c; \lt, \mathrm{rel}, \mathrm{top}, \mathrm{allow})`$ (§7) |
| [07 The relation R](07-relation-r.md) | $`R`$, the symbols $`\mathrm{Rel}_{t,i,j}`$, $`\mathrm{Top}_{t,i}`$ and their true interpretations $`\mathrm{relR}`$, $`\mathrm{topR}_c`$ |

This note explains how to build points below $`\omega_1`$ that are closed under $`\Sigma_1`$ witnesses. The idea is the one of the Löwenheim–Skolem theorem: add witnesses and take the supremum. The chain of these points gives the first labels in [09](09-obligations.md).

## 1. The ambient structure and Good

**Definition (ambient structure).** Let $`\mathfrak B`$ be the structure of height $`\omega_1`$ in which the top predicates are defined at every key (notation of [03](03-sigma1-elementary.md) §7).

```math
\mathfrak B = \bigl(\omega_1;\ \lt,\ \mathrm{relR},\ \mathrm{topR}_{\omega_1},\ \mathrm{allow}_{\mathrm{all}}\bigr), \qquad \mathrm{topR}_{\omega_1}(\kappa, x) :\iff R(\kappa, x, \omega_1), \qquad \mathrm{allow}_{\mathrm{all}}(\kappa) :\iff \text{true}
```

The top predicates are defined at every key ([03](03-sigma1-elementary.md) §8).

**Definition (Good).** For a label $`\gamma`$, let $`\mathfrak B{\restriction}\gamma`$ be $`\mathfrak B`$ with its domain restricted to $`\{x \mid x \lt \gamma\}`$. The top predicates remain those toward $`\omega_1`$.

```math
\mathfrak B{\restriction}\gamma = \bigl(\gamma;\ \lt,\ \mathrm{relR},\ \mathrm{topR}_{\omega_1},\ \mathrm{allow}_{\mathrm{all}}\bigr), \qquad \mathrm{Good}(\gamma) :\iff \mathfrak B{\restriction}\gamma \preccurlyeq_{\Sigma_1} \mathfrak B
```

That is, $`\mathfrak B{\restriction}\gamma \models \varphi(\vec p) \iff \mathfrak B \models \varphi(\vec p)`$ for every formula $`\varphi = (n, F, L)`$ and every $`\vec p`$ with $`p_i \lt \gamma`$ at the positions in $`F`$.

$`\mathfrak B{\restriction}\gamma`$ is a genuine substructure of $`\mathfrak B`$ (same interpretations, smaller domain). So the Tarski–Vaught test of [03](03-sigma1-elementary.md) §6 applies directly. The upward direction $`\mathfrak B{\restriction}\gamma \models \varphi(\vec p) \implies \mathfrak B \models \varphi(\vec p)`$ always holds (Property 2 of [03](03-sigma1-elementary.md) §4). So $`\mathrm{Good}(\gamma)`$ is equivalent to the following downward condition alone.

```math
\forall \varphi\ \forall \vec p\ \Bigl(\bigl(\forall i \in F\ \ p_i \lt \gamma\bigr) \land \mathfrak B \models \varphi(\vec p) \implies \mathfrak B{\restriction}\gamma \models \varphi(\vec p)\Bigr)
```

## 2. There are countably many formulas

**Definition (the set of formulas).** Let $`\mathcal F`$ be the set of all normal forms $`(n, F, L)`$ of [03](03-sigma1-elementary.md) §7: $`n \in \mathbb N`$, $`F \subseteq \mathrm{Fin}\ n`$, and $`L`$ a finite list of literals over $`n`$ variables.

**Why it is countable.** Once $`n`$ is fixed, a literal is given by the following tuple.

| Literal | Tuple |
|---|---|
| $`v_i \lt v_j`$, $`\neg(v_i \lt v_j)`$ | $`(i, j, \pm)`$ |
| $`\mathrm{Rel}_{t,i,j}`$, $`\neg\mathrm{Rel}_{t,i,j}`$ | $`(t, i, j, \pm)`$ |
| $`\mathrm{Top}_{t,i}`$, $`\neg\mathrm{Top}_{t,i}`$ | $`(t, i, \pm)`$ |

$`\pm`$ is one of two values, positive or negated. There are finitely many $`i, j \in \mathrm{Fin}\ n`$, and the set $`\mathcal T_n`$ of templates is countable (for the key syntax of ω-Y it has $`(n+1)^m`$ elements; [03](03-sigma1-elementary.md) §7). So there are countably many literals over $`n`$ variables, and countably many finite lists of them. There are $`2^n`$ choices of $`F`$. $`n`$ is a natural number. So $`\mathcal F`$ is countable.

The sets $`\mathcal T_n`$ of templates must be countable. One formula uses only finitely many templates, but for the set of all formulas to be countable, the set of all templates must be countable. About the key syntax, the definitions and proofs of this note use only that each $`\mathcal T_n`$ is countable.

## 3. Height of witnesses

**Definition (height of witnesses).** For a formula $`\varphi = (n, F, L) \in \mathcal F`$ and a list of labels $`\vec p \in (\mathrm{Fin}\ n \to \mathrm{Label})`$:

- if $`\mathfrak B \models \varphi(\vec p)`$, choose with the axiom of choice one list $`\vec v`$ ($`v_i \lt \omega_1`$) as in the definition of satisfaction of [03](03-sigma1-elementary.md) §7, and let $`h(\varphi, \vec p) := \sup_{i \lt n} (v_i + 1)`$;
- otherwise let $`h(\varphi, \vec p) := 0`$.

**Theorem (the height of witnesses is below ω₁).** $`h(\varphi, \vec p) \lt \omega_1`$.

**Proof.** It is the maximum of finitely many $`v_i + 1`$, each below $`\omega_1`$ ([01](01-ordinals.md) §4). $`\square`$

All entries of the chosen $`\vec v`$ lie below $`h(\varphi, \vec p)`$ ([01](01-ordinals.md) §3).

## 4. One closure step

**Definition (inputs).** For a label $`\gamma`$, define the set of pairs of a formula and a partial parameter list ([01](01-ordinals.md) §7):

```math
\mathrm{Input}(\gamma) := \bigl\{\, (\varphi, q) \ \bigm|\ \varphi = (n, F, L) \in \mathcal F,\ \ q \in \mathrm{Par}_n(\gamma) \,\bigr\}
```

If $`\gamma \lt \omega_1`$, $`\mathrm{Input}(\gamma)`$ is countable, because $`\mathcal F`$ is countable (§2) and each $`\mathrm{Par}_n(\gamma)`$ is countable ([01](01-ordinals.md) §7).

**Definition (one closure step).** For a label $`\gamma`$ define

```math
\mathrm{next}(\gamma) := \min\Bigl(\max\Bigl(\gamma + 1,\ \sup_{(\varphi, q) \in \mathrm{Input}(\gamma)} h\bigl(\varphi, \mathrm{toP}(q)\bigr)\Bigr),\ \omega_1\Bigr)
```

The $`\min(\cdot, \omega_1)`$ only makes the value a label ($`\le \omega_1`$). If $`\gamma \lt \omega_1`$, by Property 2 the $`\min`$ changes nothing.

| Property | Statement | Reason |
|---|---|---|
| Property 1 | $`\gamma \lt \omega_1 \implies \gamma \lt \mathrm{next}(\gamma)`$ | the term $`\gamma + 1`$ |
| Property 2 | $`\gamma \lt \omega_1 \implies \mathrm{next}(\gamma) \lt \omega_1`$ | $`\gamma + 1 \lt \omega_1`$ and a supremum of countably many ([01](01-ordinals.md) §4, §5) |
| Property 3 | if $`\gamma \lt \omega_1`$, $`p_i \lt \gamma`$ at the positions in $`F`$ and $`\mathfrak B \models \varphi(\vec p)`$, then $`\mathfrak B{\restriction}\mathrm{next}(\gamma) \models \varphi(\vec p)`$ | proof below |

**Proof of Property 3.** By the theorem (every parameter tuple can be written) of [01](01-ordinals.md) §7, there is $`q \in \mathrm{Par}_n(\gamma)`$ with $`\mathrm{toP}(q)_i = p_i`$ at the positions in $`F`$. Truth in $`\mathfrak B`$ reads only the parameters at the positions in $`F`$, so $`\mathfrak B \models \varphi(\mathrm{toP}(q))`$. The $`\vec v`$ chosen for $`(\varphi, \mathrm{toP}(q))`$ has $`v_i = p_i`$ at the positions in $`F`$, and all its entries lie below $`h(\varphi, \mathrm{toP}(q))`$ (§3). This is one of the terms of the supremum, so they lie below $`\mathrm{next}(\gamma)`$. So $`\vec v`$ is a witness in $`\mathfrak B{\restriction}\mathrm{next}(\gamma)`$. $`\square`$

## 5. λ

**Definition (λ).**

```math
\mathrm{next}^0(\gamma) := \gamma, \quad \mathrm{next}^{t+1}(\gamma) := \mathrm{next}\bigl(\mathrm{next}^t(\gamma)\bigr), \qquad \lambda(\gamma) := \sup_{t \in \mathbb N} \mathrm{next}^t(\gamma)
```

Here $`t \in \mathbb N`$. An ordinal of the form $`\lambda(\gamma)`$ is called a **closure point**. Since $`\lambda(\gamma) \le \omega_1`$, a closure point is a label.

| Property | Statement |
|---|---|
| Property 4 | $`\gamma \lt \omega_1 \implies \mathrm{next}^t(\gamma) \lt \omega_1`$ |
| Property 5 | $`\gamma \lt \omega_1`$, $`t \le t' \implies \mathrm{next}^t(\gamma) \le \mathrm{next}^{t'}(\gamma)`$ |
| Property 6 | $`\gamma \lt \omega_1 \implies \lambda(\gamma) \lt \omega_1`$ (supremum of countably many) |
| Property 7 | $`\gamma \lt \omega_1 \implies \gamma \lt \lambda(\gamma)`$ |
| Property 8 | if $`\gamma \lt \omega_1`$, $`k \in \mathbb N`$ and $`p_0, \ldots, p_{k-1} \lt \lambda(\gamma)`$, then all are $`\lt \mathrm{next}^t(\gamma)`$ for some $`t`$ |

Property 4 follows from Property 2 by induction on $`t`$. Property 5 follows from Properties 1 and 4. Property 7 is $`\gamma \lt \mathrm{next}^1(\gamma) \le \lambda(\gamma)`$. Property 8 is shown as follows. Each $`p_i`$ is below the supremum, so $`p_i \lt \mathrm{next}^{t_i}(\gamma)`$ for some $`t_i`$. Take $`t := \max_i t_i`$ and use Property 5.

## 6. λ(γ) is Good

**Theorem (λ(γ) is Good).** If $`\gamma \lt \omega_1`$, then $`\mathrm{Good}(\lambda(\gamma))`$.

**Proof.** We show the downward condition of §1, in the form of the Tarski–Vaught test ([03](03-sigma1-elementary.md) §6). Let $`p_i \lt \lambda(\gamma)`$ at the positions in $`F`$ and $`\mathfrak B \models \varphi(\vec p)`$. By Property 8, for some $`t`$, $`p_i \lt \mathrm{next}^t(\gamma)`$ at the positions in $`F`$. Applying Property 3 at $`\mathrm{next}^t(\gamma)`$ (below $`\omega_1`$ by Property 4), the witnesses can be taken below $`\mathrm{next}^{t+1}(\gamma) \le \lambda(\gamma)`$. $`\square`$

**Corollary (the Good points are unbounded in ω₁).** If $`\sigma \lt \omega_1`$, there is $`\alpha`$ with $`\sigma \lt \alpha \lt \omega_1`$ and $`\mathrm{Good}(\alpha)`$. $`\alpha = \lambda(\sigma)`$ works (Properties 6, 7 and the theorem above).

**Example (only the shape).** Let $`\gamma = 0`$. $`\lambda(0)`$ contains witnesses of every true $`\Sigma_1`$ statement of $`\mathfrak B`$ whose parameters lie below $`\lambda(0)`$. The actual value of $`\lambda(0)`$ is not known. The proof never uses the value, only $`\lambda(0) \lt \omega_1`$ and $`\mathrm{Good}(\lambda(0))`$.

**About the set of Good points.** We neither show nor use that the set of Good points is closed in $`\omega_1`$ (that the supremum of an increasing sequence of Good points is Good). That is why it is not called a club (closed unbounded set).

## 7. The chain

**Definition (the chain).**

```math
c_0 := \lambda(0), \qquad c_{t+1} := \lambda(c_t)
```

| Property | Statement |
|---|---|
| Property 9 | $`c_t \lt \omega_1`$ |
| Property 10 | $`c_0 \lt c_1 \lt c_2 \lt \cdots`$ |
| Property 11 | $`\mathrm{Good}(c_t)`$ |

All follow from §5 and §6 by induction on $`t`$.

Any two points of this chain are related by $`R`$ at every key. The proof needs that at a Good point the top predicates agree with the top predicates of $`\omega_1`$. Both are explained in [09](09-obligations.md) §3.

## 8. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "Proofs of the three theorems" | "there are countably many formulas, so the Good points are cofinal in $`\omega_1`$" (§2, §6); the sequence of Good points (§7) |
| [notes/01-design.md](../../notes/01-design.md) §3.3 (Japanese) | ambient structure, Good, $`\omega`$ iterations, the sequence of Good points |

## 9. Lean correspondence

| Concept | Lean | File |
|---|---|---|
| truth in $`\mathfrak B`$ | `Sat (relR S) (topR S top) (fun _ => True) top φ p` | [Por/Supply.lean](../../Por/Supply.lean) |
| Good (the downward form of §1) | `Good` | same |
| formulas are countable (§2) | `litCode`, `litCode_inj`, `lit_countable`, `formCode`, `formCode_inj`, `form_countable` | same |
| templates are countable | the assumption `[∀ n, Countable (S.Template n)]`, `Keys.template_countable`, `Model.keySyntax_countable` | same, [OmegaY/Keys.lean](../../OmegaY/Keys.lean), [OmegaY/Model.lean](../../OmegaY/Model.lean) |
| height of witnesses $`h`$ | `wh`, `wh_lt`, `wit_lt_wh` | [Por/Supply.lean](../../Por/Supply.lean) |
| $`\mathrm{Input}(\gamma)`$ | `Input S γ := Σ φ : Form S, Fin φ.n → Option (Set.Iio γ)`, `input_countable` | same |
| $`\mathrm{next}`$ (the value before the $`\min`$ is `nextO`) | `nextO`, `next`, `next_val`, `nextO_lt`, `wh_le_nextO` | same |
| Properties 1–3 | `lt_next`, `next_lt`, `wit_below` | same |
| $`\mathrm{next}^t`$, $`\lambda`$ | `tower`, `lamO`, `lam` | same |
| Properties 4–8 | `tower_lt`, `tower_succ_lt`, `tower_mono`, `tower_le_lam`, `lam_lt`, `lt_lam`, `exists_tower` | same |
| λ(γ) is Good, corollary | `lam_good`, `good_cofinal` | same |
| the chain and Properties 9–11 | `points`, `points_lt`, `points_strictMono`, `points_good` | same |
