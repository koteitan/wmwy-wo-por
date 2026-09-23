[← Back](README.md) | [English](08-closure-chain.md) | [Japanese](../08-closure-chain.md)

# Closure below ω₁ and the sequence of closed points

Prerequisites

| Note | Terms used here |
|---|---|
| [01 Ordinals and ω₁](01-ordinals.md) | $`\omega_1`$, regularity, the label type, `Input`, `toP` |
| [03 Structures and Σ₁-elementary substructures](03-sigma1-elementary.md) | the Tarski–Vaught test, `Form`, `Sat` |
| [07 The relation R](07-relation-r.md) | $`R`$, `relR`, `topR` |

This note explains how to build, below $`\omega_1`$, points that are "closed under $`\Sigma_1`$ witnesses". The idea is the same as in the Löwenheim–Skolem theorem: add witnesses and take the supremum. The sequence of such points gives the first labels in [09](09-obligations.md). The Lean file is [Por/Supply.lean](../../Por/Supply.lean). This note assumes that the template types are countable (`[∀ n, Countable (S.Template n)]`). The template types of ω-Y are finite (`Keys.template_countable`).

## 1. The ambient structure and Good

**Definition (ambient structure).** Let $`\mathfrak B`$ be the structure of height $`\omega_1`$ in which the top predicates are defined for every key.

```math
\mathfrak B = \bigl(\omega_1;\ \lt,\ (\mathrm{Rel}_{t,i,j}),\ (\mathrm{Top}^{\omega_1}_{t,i})\bigr), \qquad \mathrm{Top}^{\omega_1}_{t,i}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ \omega_1)
```

In Lean, truth in $`\mathfrak B`$ is `Sat (relR S) (topR S top) (fun _ => True) top φ p`. Since `allow` is always true, every top literal is defined.

**Definition (Good).** Let $`\mathfrak B{\restriction}\alpha`$ be $`\mathfrak B`$ with its domain restricted to $`\{x \mid x \lt \alpha\}`$. The top predicates stay those toward $`\omega_1`$.

```math
\mathrm{Good}(\alpha) :\iff \forall \varphi\ \forall \vec p \lt \alpha\ \bigl(\mathfrak B \models \varphi(\vec p) \implies \mathfrak B{\restriction}\alpha \models \varphi(\vec p)\bigr)
```

`Good α` in Lean has this form. $`\mathfrak B{\restriction}\alpha`$ is a genuine substructure of $`\mathfrak B`$ (same interpretations, smaller domain). The converse implication always holds (witnesses $`\lt \alpha`$ are $`\lt \omega_1`$). So by the Tarski–Vaught test of [03](03-sigma1-elementary.md) §6, $`\mathrm{Good}(\alpha)`$ is the same as $`\mathfrak B{\restriction}\alpha \preccurlyeq_{\Sigma_1} \mathfrak B`$.

## 2. There are countably many formulas

**Theorem (`form_countable`).** The type of formulas `Form S` is countable.

**Proof.** Encode literals by an injection into a sum of tuple types (`litCode`, `litCode_inj`).

| Literal | Code |
|---|---|
| `lt i j pos` | $`(i, j, \mathit{pos})`$ |
| `rel t i j pos` | $`(t, i, j, \mathit{pos})`$ |
| `top t i pos` | $`(t, i, \mathit{pos})`$ |

The component types (`Fin n`, `Bool`, `S.Template n`) are countable, so the type of literals is countable (`lit_countable`). Encode formulas by an injection into the dependent sum $`(n, \mathit{fixed}, \mathit{lits})`$ (`formCode`, `formCode_inj`). Natural numbers, functions on a finite type, and lists over a countable type are countable. $`\square`$

The template types must be countable. One formula uses only finitely many templates, but for the set of all formulas to be countable, the set of all templates must be countable.

## 3. Heights of witnesses

**Definition (`wh`).** For a formula $`\varphi`$ and parameters $`\vec p`$:

- if $`\mathfrak B \models \varphi(\vec p)`$, choose one tuple of witnesses $`v`$ (`Classical.choose`) and put $`\mathrm{wh}(\varphi, \vec p) := \sup_{i \lt n} (v_i + 1)`$;
- otherwise put $`\mathrm{wh}(\varphi, \vec p) := 0`$.

| Theorem | Content | Reason |
|---|---|---|
| `wh_lt` | $`\mathrm{wh}(\varphi, \vec p) \lt \omega_1`$ | a supremum of finitely many $`v_i + 1 \lt \omega_1`$ ([01](01-ordinals.md) §5) |
| `wit_lt_wh` | every chosen witness is below $`\mathrm{wh}(\varphi, \vec p)`$ | `Ordinal.lt_iSup_add_one` |

## 4. One step of the closure

**Definition (`next`).**

```math
\mathrm{nextO}(\gamma) := \max\Bigl(\gamma + 1,\ \sup_{q \in \mathrm{Input}(\gamma)} \mathrm{wh}\bigl(q_\varphi, \mathrm{toP}(q)\bigr)\Bigr), \qquad \mathrm{next}(\gamma) := \min\bigl(\mathrm{nextO}(\gamma), \omega_1\bigr)
```

The supremum ranges over all formulas with parameters below $`\gamma`$, $`q \in \mathrm{Input}(\gamma)`$ ([01](01-ordinals.md) §7). The $`\min`$ only puts the value into the label type; if $`\gamma \lt \omega_1`$ then $`\mathrm{next}(\gamma) = \mathrm{nextO}(\gamma)`$ (`next_val`).

| Theorem | Content | Reason |
|---|---|---|
| `lt_next` | $`\gamma \lt \omega_1 \implies \gamma \lt \mathrm{next}(\gamma)`$ | the term $`\gamma + 1`$ |
| `next_lt` | $`\gamma \lt \omega_1 \implies \mathrm{next}(\gamma) \lt \omega_1`$ | `Input` is countable; a countable supremum (`nextO_lt`) |
| `wit_below` | if $`\gamma \lt \omega_1`$, $`\vec p \lt \gamma`$ and $`\mathfrak B \models \varphi(\vec p)`$, then $`\mathfrak B{\restriction}\mathrm{next}(\gamma) \models \varphi(\vec p)`$ | proof below |

**Proof of `wit_below`.** Make the input $`q`$ with $`p_i`$ at the parameter positions and `none` elsewhere. `toP` turns `none` into 0, but truth in $`\mathfrak B`$ reads only the parameter positions, so $`\mathfrak B \models \varphi(\mathrm{toP}(q))`$. The witnesses chosen for $`q`$ are below $`\mathrm{wh}(q)`$ (`wit_lt_wh`). This is one of the terms of the supremum, so they are below $`\mathrm{next}(\gamma)`$ (`wh_le_nextO`). $`\square`$

## 5. The tower and λ

**Definition (`tower`, `lam`).**

```math
\mathrm{next}^0(\gamma) := \gamma, \quad \mathrm{next}^{t+1}(\gamma) := \mathrm{next}\bigl(\mathrm{next}^t(\gamma)\bigr), \qquad \lambda(\gamma) := \sup_{t \in \mathbb N} \mathrm{next}^t(\gamma)
```

| Theorem | Content |
|---|---|
| `tower_lt` | $`\gamma \lt \omega_1 \implies \mathrm{next}^t(\gamma) \lt \omega_1`$ |
| `tower_succ_lt` | $`\mathrm{next}^t(\gamma) \lt \mathrm{next}^{t+1}(\gamma)`$ |
| `tower_mono` | $`t \le t' \implies \mathrm{next}^t(\gamma) \le \mathrm{next}^{t'}(\gamma)`$ |
| `tower_le_lam` | $`\mathrm{next}^t(\gamma) \le \lambda(\gamma)`$ |
| `lam_lt` | $`\gamma \lt \omega_1 \implies \lambda(\gamma) \lt \omega_1`$ (a countable supremum) |
| `lt_lam` | $`\gamma \lt \omega_1 \implies \gamma \lt \lambda(\gamma)`$ |
| `exists_tower` | if finitely many $`p_i \lt \lambda(\gamma)`$, then all are $`\lt \mathrm{next}^t(\gamma)`$ for some $`t`$ |

Proof of `exists_tower`: each $`p_i`$ is below the supremum, so $`p_i \lt \mathrm{next}^{t_i}(\gamma)`$ for some $`t_i`$. Take $`t := \max_i t_i`$ and use `tower_mono`.

## 6. λ(γ) is Good

**Theorem (`lam_good`).** If $`\gamma \lt \omega_1`$ then $`\mathrm{Good}(\lambda(\gamma))`$.

**Proof.** In the form of the Tarski–Vaught test ([03](03-sigma1-elementary.md) §6). Let $`\vec p \lt \lambda(\gamma)`$ and $`\mathfrak B \models \varphi(\vec p)`$. By `exists_tower`, $`\vec p \lt \mathrm{next}^t(\gamma)`$ for some $`t`$. Using `wit_below` at $`\mathrm{next}^t(\gamma)`$, the witnesses can be taken below $`\mathrm{next}^{t+1}(\gamma) \le \lambda(\gamma)`$. $`\square`$

**Theorem (`good_cofinal`).** If $`\sigma \lt \omega_1`$, there is $`\alpha`$ with $`\sigma \lt \alpha \lt \omega_1`$ and $`\mathrm{Good}(\alpha)`$. $`\alpha = \lambda(\sigma)`$ works.

**Example (shape only).** $`\lambda(0)`$ contains witnesses for every $`\Sigma_1`$ claim true in $`\mathfrak B`$ with parameters below $`\lambda(0)`$. The concrete value of $`\lambda(0)`$ is unknown. The proof does not use the value; it uses only $`\lambda(0) \lt \omega_1`$ and $`\mathrm{Good}(\lambda(0))`$.

**On the set of Good points.** It is neither shown nor used that the set of Good points is closed in $`\omega_1`$. So we do not call it a club (closed unbounded set).

## 7. The sequence of closed points

**Definition (`points`).**

```math
c_0 := \lambda(0), \qquad c_{k+1} := \lambda(c_k)
```

| Theorem | Content |
|---|---|
| `points_lt` | $`c_k \lt \omega_1`$ |
| `points_strictMono` | $`c_0 \lt c_1 \lt c_2 \lt \cdots`$ |
| `points_good` | $`\mathrm{Good}(c_k)`$ |

All follow from §5 and §6 by induction on $`k`$.

Any two points of this sequence are in the relation $`R`$ at every key (`good_R`). The proof needs that at a Good point the top predicates agree with those of $`\omega_1`$ (`top_abs`). Both are explained in [09](09-obligations.md) §3.

## 8. Where this repository uses it

| Place | Use |
|---|---|
| [README](../../README-en.md) "Proofs of the three theorems" | "there are countably many formulas, so Good points are cofinal in $`\omega_1`$" |
| [notes/01-design.md](../../notes/01-design.md) §3.3 | closed points, $`\omega`$ iterations, the sequence of closed points |
| [Por/Supply.lean](../../Por/Supply.lean) | everything in this note |

## 9. Lean correspondence

| Concept | Lean | File |
|---|---|---|
| Good | `Good` | [Por/Supply.lean](../../Por/Supply.lean) |
| formulas are countable | `litCode`, `litCode_inj`, `lit_countable`, `formCode`, `formCode_inj`, `form_countable` | same |
| templates are finite | `Keys.template_countable`, `Model.keySyntax_countable` | [OmegaY/Keys.lean](../../OmegaY/Keys.lean), [OmegaY/Model.lean](../../OmegaY/Model.lean) |
| heights of witnesses | `wh`, `wh_lt`, `wit_lt_wh` | [Por/Supply.lean](../../Por/Supply.lean) |
| one step of the closure | `nextO`, `next`, `next_val`, `nextO_lt`, `next_lt`, `lt_next`, `wh_le_nextO`, `wit_below` | same |
| tower and λ | `tower`, `tower_lt`, `tower_succ_lt`, `tower_mono`, `lamO`, `lam`, `tower_le_lam`, `lam_lt`, `lt_lam`, `exists_tower` | same |
| λ is Good | `lam_good`, `good_cofinal` | same |
| the sequence of closed points | `points`, `points_lt`, `points_good`, `points_strictMono` | same |
