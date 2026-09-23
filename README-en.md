[English](README-en.md) | [Japanese](README.md)

# wmwy-wo-por: well-foundedness of weak-magma ω-Y by patterns of resemblance

This repository proves in Lean 4 that expansion in the weak-magma ω-Y sequence system is well-founded.

The proof is based on Phyrion's proof ([Phyrion1343/omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean)). Its combinatorial part is used unchanged. Only the semantic part is replaced, by a relation in the style of patterns of resemblance ($`\Sigma_1`$-elementary substructures). Neither the constructible universe $`L`$ nor admissible ordinals are used. It is the ω-Y counterpart of what the sister project [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por) did for 1-Y.

- Lean 4.33.1, Mathlib v4.33.1.
- No `sorry`, no new axiom. The only axioms are `propext`, `Classical.choice` and `Quot.sound`.
- No dependency on the unlicensed YesMetaZFC.

## Target: weak-magma ω-Y

The target is the same expansion as in Phyrion's formalization, called the "weak magma, no extraction" ω-Y. The rules are in [OmegaY/Expansion/Build.lean](OmegaY/Expansion/Build.lean). This repository calls it **weak-magma ω-Y** and treats it as a sequence system distinct from the official ω-Y.

Weak-magma ω-Y does not agree with the official ω-Y (Naruyoko's program). On 3001 standard forms, 480 of 9003 expansions differ. The smallest example is $`(1,3,3)[2]`$. See [notes/00-survey.md](notes/00-survey.md) (Japanese). Termination of the official ω-Y is not a theorem of this repository; the official ω-Y is treated in a separate repository, [koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por). The cause of the difference is in [notes/02-feasibility.md](notes/02-feasibility.md) (Japanese): only the rule that fills the gap in a copied block, the magma, differs.

## What is proved

### Notation

- An expression is a finite sequence of positive integers that is empty or starts with 1 (`Dynamics.Expr`).
- $`s[N]`$ is the expansion of $`s`$ with copy count $`N`$ (`expand s N`).
- $`t \prec s`$ (`Dynamics.Step t s`) means $`s \ne ()`$ and $`t = s[N]`$ for some $`N`$.
- $`s \to^{*} t`$ means that $`t`$ is reached from $`s`$ by zero or more expansions.
- $`\lt_{\mathrm{lex}}`$ is the lexicographic order of expressions.

### The four final theorems

They are in [OmegaY/Expansion/WellFounded.lean](OmegaY/Expansion/WellFounded.lean), namespace `OmegaY.Expansion`.

1. `omegaY_step_wellFounded`: $`\prec`$ is well-founded, that is, there is no infinite sequence

```math
s_0,\ s_1,\ s_2,\ \ldots \qquad s_n \ne (),\quad s_{n+1} = s_n[N_n] \quad (n \in \mathbb N)
```

2. `omegaY_generated_isWellOrder`: the set of expressions generated from the standard seeds $`(1, m+2)`$ is well-ordered by $`\lt_{\mathrm{lex}}`$.
3. `omegaY_descendants_isWellOrder`: for every expression $`s`$, the set $`\{\, t \mid s \to^{*} t \,\}`$ is well-ordered by $`\lt_{\mathrm{lex}}`$.
4. `omegaY_trajectory_terminates`: for every choice of copy counts $`N_0, N_1, \ldots`$, the expansion sequence reaches the empty sequence.

The first is the main one. The combinatorial layer derives the other three from it.

## Structure of the proof

Phyrion's proof has two layers.

- The combinatorial layer (most of `OmegaY/`, and `ZeroY/`). It turns an ω-Y mountain into a finite graph and labels each column with an ordinal $`\le \omega_1`$. It shows that the expanded graph has a labelling whose last label is smaller.
- The semantic layer. It supplies a relation $`R(\theta,a,b)`$ between labels, where $`\theta`$ is a key: a vector $`\mathrm{Key}_m = \mathrm{Lex}(\mathrm{Fin}\ m \to \mathrm{Label} \cup \{\top\})`$ whose length $`m`$ is fixed by the starting expression.

The combinatorial layer uses only three theorems of the semantic layer.

| Name | Content |
|---|---|
| `Reflection.key_weaken` | if $`\theta \le \Theta`$ and $`R(\Theta,a,b)`$ then $`R(\theta,a,b)`$ |
| `Reflection.finite_reflection` | finite reflection: a finite graph below $`b`$ with demands to $`b`$ (keys below $`\theta`$) is moved below $`f(\mathrm{cut})`$ by $`R(\theta, f(\mathrm{cut}), b)`$, fixing the points before the cut |
| `OrdinalSupply.initial_finite_graph` | every finite graph has a labelling below $`\omega_1`$ |

Phyrion's semantic layer does not use admissible ordinals either. There, $`R(\theta,a,b)`$ says that finite positive graphs below $`b`$ can be compressed below $`a`$. This repository replaces it by a relation of $`\Sigma_1`$-elementary substructures.

## The relation R

```math
R(\theta,a,b) \iff a \lt b \ \land\ \mathfrak A^{a}_{\theta} \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_{\theta}
```

$`\mathfrak A^{c}_{\theta}`$ is the structure of height $`c`$.

- Domain $`\{x \mid x \lt c\}`$, order $`\lt`$.
- Internal relations: for each key template $`t`$ and positions $`i, j`$, $`\mathrm{Rel}_{t,i,j}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ v_j)`$.
- Top predicates: for each template $`t`$ and position $`i`$, $`\mathrm{Top}_{t,i}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ c)`$, defined only when the key $`\mathrm{eval}\ t\ \vec v`$ is below $`\theta`$. A top literal can be true only where it is defined.
- $`\preccurlyeq_{\Sigma_1}`$: every $`\Sigma_1`$ formula (an existentially quantified conjunction of literals) with parameters below $`a`$ has the same truth value in the two structures.

The right-hand side reads $`R`$ itself, so $`R`$ is defined by well-founded recursion on (top, key) in lexicographic order; every instance of $`R`$ read on the right is at a smaller stage. In Lean these are `Por.R` and its defining equation `Por.R_iff` ([Por/Relation.lean](Por/Relation.lean)).

### Proofs of the three theorems

- Key weakening: move the witnesses in $`\mathfrak A^{b}_{\theta}`$ that are below $`a`$ into the parameters and move the rest down. The new witnesses are pointwise below the old ones. Since $`\mathrm{eval}`$ is monotone, the keys stay below $`\theta`$.
- Finite reflection: write the graph and the demands as one $`\Sigma_1`$ formula and move it down by $`\Sigma_1`$-elementarity.
- Initial labellings: $`\mathrm{Good}(\alpha)`$ says that the height-$`\alpha`$ structure is a $`\Sigma_1`$-elementary substructure of the height-$`\omega_1`$ structure with all top predicates defined. There are countably many formulas, so Good points are cofinal in $`\omega_1`$. At a Good point, replacing the top $`\alpha`$ by $`\omega_1`$ does not change $`R`$ (`top_abs`, by induction on the key). Two Good points are related at every key (`good_R`). A sequence of Good points represents every finite graph.

The proof uses choice and the regularity of $`\omega_1`$. It gives no ordinal bound or notation system.

The detailed design is in [notes/01-design.md](notes/01-design.md) (Japanese).

## Mathematical background

[study/](study/en/README.md) has background notes for reading this repository (in English and Japanese). There are nine: ordinals and $`\omega_1`$, well-founded recursion and the order of keys, $`\Sigma_1`$-elementary substructures and partial top predicates, Carlson's patterns of resemblance, the mountain and expansion of an ω-Y sequence, Phyrion's combinatorial layer for ω-Y, the relation $`R`$, closure below $`\omega_1`$ and the sequence of closed points, and the proofs of the three theorems. Every note names the Lean declarations.

## Files

| Path | Content |
|---|---|
| [Por/Formula.lean](Por/Formula.lean), [Por/Relation.lean](Por/Relation.lean), [Por/Supply.lean](Por/Supply.lean) | The model of the semantic layer, about 650 lines, using Mathlib |
| [OmegaY/Reflection.lean](OmegaY/Reflection.lean), [OmegaY/Reflection/](OmegaY/Reflection/) | Thin files that give the names the combinatorial layer calls by the theorems of the model, and the interface definitions |
| [Por/BMS/](Por/BMS/) | The BMS layer called by the 0-Y layer, written for 1y-wo-por, about 3,300 lines |
| [ZeroY/](ZeroY/) | Phyrion's 0-Y layer, taken through 1y-wo-por, 20 modules |
| [OmegaY/](OmegaY/) | Phyrion's combinatorial layer for ω-Y, 549 modules |
| [notes/](notes/) | Survey and design notes (Japanese) |
| [study/](study/en/README.md) | Notes on the mathematical background (in English and Japanese) |
| [LICENSE](LICENSE), [NOTICE](NOTICE) | Apache-2.0 and provenance |

## Building

```sh
lake exe cache get
lake build
```

- The default targets are `Por` and `OmegaY`. `OmegaY` includes the axiom audit [OmegaY/Audit.lean](OmegaY/Audit.lean).
- `leanman build` was run on 2026-09-23 with exit code 0.

## Axiom audit

[OmegaY/Audit.lean](OmegaY/Audit.lean) checks the axioms of every theorem whose name starts with `OmegaY.` or `Por.`. Output (2026-09-23):

```text
Audited 6614 research theorems: only propext, Classical.choice and Quot.sound occur. No new axiom declaration.
'OmegaY.Expansion.omegaY_step_wellFounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'OmegaY.Expansion.omegaY_generated_isWellOrder' depends on axioms: [propext, Classical.choice, Quot.sound]
'OmegaY.Expansion.omegaY_descendants_isWellOrder' depends on axioms: [propext, Classical.choice, Quot.sound]
'OmegaY.Expansion.omegaY_trajectory_terminates' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Acknowledgements and license

This repository is licensed under the Apache License 2.0 ([LICENSE](LICENSE)). Provenance and changes are recorded in [NOTICE](NOTICE).

- Combinatorial layer: adapted from `OmegaY/` of [Phyrion1343/omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean) (Apache-2.0, revision `33c16a8`). The overall shape of the proof is Phyrion's. Each file starts with its original path and the changes.
- 0-Y layer: `formalization/ZeroY` of [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean) (Apache-2.0, revision `6533b29`), taken through 1y-wo-por.
- BMS layer: `Por/BMS/` was written for 1y-wo-por. Phyrion's ω-Y formalization depends on unlicensed BMS code (YesMetaZFC, [EgoFakeFantasy/BMS-Well-Ordering-Lean](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean)). This repository does not depend on it and copies none of its lines.

## References

- Phyrion, [omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean). Lean formalization of the well-foundedness of weak-magma ω-Y.
- Phyrion, [1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean). Lean formalization of the well-foundedness of 1-Y.
- T. J. Carlson, Elementary patterns of resemblance, Annals of Pure and Applied Logic 108 (2001), 19–77.
- koteitan, [1y-wo-por](https://github.com/koteitan/1y-wo-por). Well-foundedness of 1-Y by patterns of resemblance.
- koteitan, [bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern). Well-foundedness of BMS by patterns of resemblance.
