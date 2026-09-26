[← Back](README.md) | [English](en/01-ordinals.md) | [Japanese](01-ordinals.md)

# 順序数と ω₁

前提: なし

このノートは、順序数と $`\omega_1`$ を説明する。あとのノートでは、展開の停止性の証明で、式の列に $`\omega_1`$ 以下の順序数（§6 のラベル）を付けて使う（[06](06-combinatorial-layer.md) §2、§8）。使う事実は §5 の正則性、§6 のラベル、§7 のパラメータの列の数え方である。

## 1. 整列順序と順序数

**定義（整列順序）.** 集合 $`X`$ の上の全順序 $`\lt`$ が **整列順序** であるとは、$`X`$ の空でない部分集合がどれも最小元を持つことをいう。

**定義（無限降下列）.** $`x_0 \gt x_1 \gt x_2 \gt \cdots`$ となる列 $`(x_n)_{n \in \mathbb N}`$ を **無限降下列** と呼ぶ。

全順序が整列順序であることと、無限降下列が無いことは同値である。「無限降下列が無いなら整列順序」の向きには、選択公理の弱い形（従属選択）を使う。

| 順序 | 整列か | 理由 |
|---|---|---|
| $`(\mathbb N, \lt)`$ | はい | 空でない部分集合は最小元を持つ |
| $`(\mathbb Z, \lt)`$ | いいえ | $`0 \gt -1 \gt -2 \gt \cdots`$ |
| $`(\mathbb Q_{\ge 0}, \lt)`$ | いいえ | $`1 \gt 1/2 \gt 1/4 \gt \cdots`$ |

**定義（順序数）.** **順序数** は整列順序の型である。順序数 $`\alpha`$ は、それより小さい順序数の集合 $`\{\beta \mid \beta \lt \alpha\}`$ と同一視する。

小さい順に並べると次のようになる。

```math
0,\ 1,\ 2,\ \ldots,\ \omega,\ \omega+1,\ \omega+2,\ \ldots,\ \omega \cdot 2,\ \ldots,\ \omega^2,\ \ldots,\ \omega^\omega,\ \ldots
```

- $`\omega`$ は自然数全体の型である。$`\omega = \{0, 1, 2, \ldots\}`$。
- 順序数の全体は $`\lt`$ で整列する。空でない順序数の集まりには、どれも最小元がある。
- 順序数の全体を $`\mathrm{Ord}`$ と書く。
- $`\omega^\omega`$ より小さい順序数は、$`\omega^{d} c_d + \cdots + \omega c_1 + c_0`$（$`d, c_0, \ldots, c_d \in \mathbb N`$）の形にただ 1 通りに書ける（Cantor の標準形）。ただし $`d \gt 0`$ なら $`c_d \ne 0`$ とする。[05](05-omegay-mountain.md) の山の行はこの形の順序数である。

## 2. 後者と極限

**定義（後者）.** $`\alpha + 1`$ は $`\alpha`$ の次の順序数である。$`\alpha + 1`$ の形の順序数を **後者順序数** と呼ぶ。

**定義（極限順序数）.** 0 でも後者順序数でもない順序数を **極限順序数** と呼ぶ。

| 順序数 | 種類 |
|---|---|
| $`0`$ | どちらでもない |
| $`5`$、$`\omega+1`$、$`\omega \cdot 2 + 3`$ | 後者 |
| $`\omega`$、$`\omega \cdot 2`$、$`\omega^2`$ | 極限 |

**性質.** $`\alpha`$ が極限順序数で $`\beta \lt \alpha`$ なら、$`\beta + 1 \lt \alpha`$ である。したがって $`\beta`$ より上に、$`\alpha`$ より下の元が無限個ある。

この性質は [03 構造と Σ₁ 初等部分構造](03-sigma1-elementary.md) の例で使う。

## 3. 上限

**定義（上限）.** 順序数の集合 $`S`$ の **上限** $`\sup S`$ は、$`S`$ のすべての元以上である最小の順序数である。

- $`S`$ が最大元を持てば、$`\sup S`$ はその最大元である。空でない有限集合ならいつもそうである。空集合の上限は $`0`$ である。
- $`S`$ が最大元を持たなければ、$`\sup S`$ は $`S`$ に入らない。

| $`S`$ | $`\sup S`$ |
|---|---|
| $`\{2, 5, 3\}`$ | $`5`$ |
| $`\{0, 1, 2, \ldots\}`$ | $`\omega`$ |
| $`\{\omega, \omega+1, \omega+2, \ldots\}`$ | $`\omega \cdot 2`$ |

「すべての元より真に大きい」数が欲しいときは、$`\sup_{i} (y_i + 1)`$ を使う。$`y_i \lt y_i + 1 \le \sup_i (y_i + 1)`$ だからである。[08 閉包と鎖](08-closure-chain.md) §3 で定義する「証人の高さ」はこの形である。

## 4. 可算と ω₁

**定義（可算）.** 集合 $`X`$ が **可算** であるとは、$`X`$ が空であるか、全射 $`\mathbb N \to X`$ があることをいう。

**定義（可算順序数）.** 順序数 $`\alpha`$ が **可算** であるとは、$`\{\beta \mid \beta \lt \alpha\}`$ が可算であることをいう。

$`0, 1, \omega, \omega+1, \omega \cdot 2, \omega^2, \omega^\omega, \varepsilon_0`$ はどれも可算である。

**定義（ω₁）.** $`\omega_1`$ は最初の非可算順序数である。つまり、$`\omega_1`$ より小さい順序数はちょうど可算順序数である。

```math
\alpha \lt \omega_1 \iff \alpha \text{ は可算}
```

次の 3 つを使う。

- $`0 \lt \omega_1`$。
- $`\alpha \lt \omega_1 \implies \alpha + 1 \lt \omega_1`$。
- $`\gamma \lt \omega_1 \implies \{\beta \mid \beta \lt \gamma\}`$ は可算。

2 つめの理由：$`\{\beta \mid \beta \lt \alpha + 1\} = \{\beta \mid \beta \lt \alpha\} \cup \{\alpha\}`$ で、可算集合に 1 点を足しても可算である。言いかえると、$`\omega_1`$ は極限順序数である。

## 5. ω₁ の正則性

**定理（ω₁ の正則性）.** 各 $`n \in \mathbb N`$ について $`\alpha_n \lt \omega_1`$ なら、次が成り立つ。

```math
\sup_{n \in \mathbb N} \alpha_n \lt \omega_1
```

添字の集合は $`\mathbb N`$ でなくても、可算ならよい。

**証明.** $`\sigma := \sup_n \alpha_n`$ と置く。$`\beta \lt \sigma`$ なら、ある $`n`$ で $`\beta \lt \alpha_n`$ である。よって

```math
\{\beta \mid \beta \lt \sigma\} = \bigcup_{n} \{\beta \mid \beta \lt \alpha_n\}
```

である。右辺は可算集合の可算個の和である。$`\alpha_n = 0`$ の項は和に何も足さないので除く。残りの各 $`n`$ で全射 $`e_n : \mathbb N \to \alpha_n`$ を 1 つずつ選ぶと、$`(n, t) \mapsto e_n(t)`$ は $`\mathbb N \times \mathbb N`$ から和の上への全射になる。$`\mathbb N \times \mathbb N`$ は可算なので、和も可算である。よって $`\sigma`$ は可算で、$`\sigma \lt \omega_1`$ である。$`\square`$

- 全射 $`e_n`$ を可算個同時に選ぶところで、選択公理（可算選択）を使う。
- 添字が非可算なら成り立たない。例えば $`\sup_{\alpha \lt \omega_1} \alpha = \omega_1`$ である。

## 6. ラベル

**定義（ラベル）.** $`\omega_1`$ 以下の順序数を **ラベル** と呼ぶ。ラベルの集合を $`\mathrm{Label}`$ と書く。

```math
\mathrm{Label} := \{\, o \in \mathrm{Ord} \mid o \le \omega_1 \,\}
```

ラベルの順序は順序数の $`\lt`$ である。$`\mathrm{Label}`$ は順序数の集合なので、§1 から整列している。最小のラベルは $`0`$、最大のラベルは $`\omega_1`$ である。

次の 3 つを使う。どれも §4 から出る。

- $`0 \lt \omega_1`$。
- $`\forall x \in \mathrm{Label}\ \ x \le \omega_1`$。
- $`a \in \mathrm{Label}`$、$`a \lt \omega_1`$ なら、$`\{x \in \mathrm{Label} \mid x \lt a\} = \{\beta \mid \beta \lt a\}`$ は可算。

**なぜ ω₁ 自身をラベルに入れるか.** 式の列に付けるラベルは、どれも $`\omega_1`$ より小さい（[06](06-combinatorial-layer.md) §2）。一方、[07](07-relation-r.md) で定義する関係 $`R`$ は、3 つめの引数に $`\omega_1`$ も取る（[08](08-closure-chain.md) §1、[09](09-obligations.md) §3）。そのために $`\omega_1`$ もラベルに入れる。

## 7. パラメータの列の数え方

**記法.** $`n \in \mathbb N`$ について $`\mathrm{Fin}\ n := \{0, 1, \ldots, n-1\}`$ とする。集合 $`X`$ について、$`\mathrm{Fin}\ n \to X`$ は $`X`$ の元を $`n`$ 個並べた列 $`(x_0, \ldots, x_{n-1})`$ の集合である。

**記法（Option）.** 集合 $`X`$ について、$`\mathrm{Option}\,X := \{\mathrm{some}\ x \mid x \in X\} \cup \{\mathrm{none}\}`$ とする。$`\mathrm{none}`$ は、$`\mathrm{some}\ x`$ のどれとも違う新しい元である。

あとで、論理式（[03](03-sigma1-elementary.md) §2 で定義する）の $`n`$ 個の変数のうち一部に、ラベルを入れる。このラベルは論理式のパラメータ（[03](03-sigma1-elementary.md) §2）として使うので、ここでもパラメータと呼ぶ。どの番号にパラメータを入れるかと、その値を、1 つの列で表す。

**定義（部分的なパラメータの列）.** ラベル $`\gamma`$ と $`n \in \mathbb N`$ について、次の集合を定める。

```math
\mathrm{Par}_n(\gamma) := \mathrm{Fin}\ n \to \mathrm{Option}\,\{\, x \in \mathrm{Label} \mid x \lt \gamma \,\}
```

$`q \in \mathrm{Par}_n(\gamma)`$ の $`q_i = \mathrm{some}\ x`$ は「番号 $`i`$ にパラメータ $`x`$ を置く」ことを、$`q_i = \mathrm{none}`$ は「番号 $`i`$ にパラメータを置かない」ことを表す。$`q`$ からラベルの列 $`\mathrm{toP}(q) \in (\mathrm{Fin}\ n \to \mathrm{Label})`$ を次で作る。

```math
\mathrm{toP}(q)_i := \begin{cases} x & (q_i = \mathrm{some}\ x) \cr 0 & (q_i = \mathrm{none}) \end{cases}
```

**定理（可算）.** $`\gamma \lt \omega_1`$ なら、各 $`n \in \mathbb N`$ で $`\mathrm{Par}_n(\gamma)`$ は可算である。

**証明.** $`\{x \in \mathrm{Label} \mid x \lt \gamma\}`$ は可算である（§6）。$`\mathrm{Option}`$ は 1 点を足すだけなので、可算のままである。可算集合の有限個の直積は可算である。$`\square`$

**定理（どのパラメータも表せる）.** $`n \in \mathbb N`$、$`F \subseteq \mathrm{Fin}\ n`$、$`p \in (\mathrm{Fin}\ n \to \mathrm{Label})`$ で、すべての $`i \in F`$ について $`p_i \lt \gamma`$ とする。このとき、ある $`q \in \mathrm{Par}_n(\gamma)`$ で、すべての $`i \in F`$ について $`\mathrm{toP}(q)_i = p_i`$ である。

**証明.** $`i \in F`$ なら $`q_i := \mathrm{some}\ p_i`$、$`i \notin F`$ なら $`q_i := \mathrm{none}`$ と置く。$`\square`$

**例.** $`\gamma = \omega + 1`$、$`n = 3`$、$`F = \{0, 2\}`$、$`p = (3, 5, \omega)`$ とする。$`q = (\mathrm{some}\ 3, \mathrm{none}, \mathrm{some}\ \omega) \in \mathrm{Par}_3(\omega + 1)`$ で、$`\mathrm{toP}(q) = (3, 0, \omega)`$ である。番号 $`1 \notin F`$ の値 $`5`$ は $`q`$ に残らない。

**なぜ要るか.** [08 閉包と鎖](08-closure-chain.md) では、$`\gamma`$ より下のパラメータを持つすべての論理式について上限を取る。添字の集合は、論理式 $`\varphi`$ と、$`\varphi`$ の変数の数 $`n`$ の $`\mathrm{Par}_n(\gamma)`$ の元の組の全体になる。論理式は可算個なので（[08](08-closure-chain.md) §2）、この集合も可算である。よって §5 の定理をそのまま使える。

**1-Y 版との違い.** **1-Y 版** は、姉妹プロジェクト [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por) の [study/](https://github.com/koteitan/1y-wo-por/tree/main/study) である。1-Y 数列について、このリポジトリと同じ形の証明を説明している。1-Y 版の 01 §6 は、$`\gamma`$ より下の順序数を全射 $`e_\gamma : \mathbb N \to \gamma`$ で数え、パラメータを自然数の列で表した。添字の集合は $`\gamma`$ に依らない。このリポジトリは、パラメータの順序数をそのまま添字に入れる。添字の集合は $`\gamma`$ に依るが、可算なので §5 の定理を使える。

## 8. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md)「証明の形」 | 各列に $`\omega_1`$ 以下の順序数のラベルを付ける（§6） |
| [README](../README.md)「関係 R」 | ラベルの順序は $`\lt`$ で、整列している（§1、§6） |
| [README](../README.md)「3 つの定理の証明」 | $`\omega_1`$ の正則性（§5）から、Good な点が $`\omega_1`$ の中で共終になる |
| [notes/01-design.md](../notes/01-design.md) §3.3 | Good な点、可算個の論理式、$`\omega`$ 回のくり返し（§5、§7） |

## 9. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| 順序数の型、$`\{\beta \mid \beta \lt \gamma\}`$ | `Ordinal.{0}`、`Set.Iio γ` | Mathlib |
| $`\lt`$ が整礎 | `wellFounded_lt` | Mathlib |
| 上限、$`y_i \lt \sup_i (y_i + 1)`$ | `iSup`（`⨆`）、`Ordinal.lt_iSup_add_one` | Mathlib |
| 可算 | `Countable` | Mathlib |
| $`\omega_1`$ と §4 の 3 つの事実 | `ω₁`、`Ordinal.omega_pos 1`、`(isSuccLimit_omega 1).add_one_lt`、`countable_iio_ordinal`（`Cardinal.mk_Iio_ordinal` から） | Mathlib、[Por/Supply.lean](../Por/Supply.lean) |
| 正則性（§5） | `Ordinal.iSup_lt_omega_one`（使う場所は `wh_lt`、`nextO_lt`、`lam_lt`） | Mathlib、[Por/Supply.lean](../Por/Supply.lean) |
| ラベル、$`0`$、$`\omega_1`$ | `Label := {o : Ordinal.{0} // o ≤ ω₁}`、`zeroL`、`top`、`zeroL_lt_top`、`le_topL`、`countable_iio` | [Por/Supply.lean](../Por/Supply.lean) |
| ラベルの別名 | `OrdinalSupply.Label`、`OrdinalSupply.top`、`bot_lt_top`、`Model.Label` | [OmegaY/Reflection/OrdinalSupply.lean](../OmegaY/Reflection/OrdinalSupply.lean)、[OmegaY/Model.lean](../OmegaY/Model.lean) |
| $`\mathrm{Fin}\ n`$、$`\mathrm{Option}`$ | `Fin n`、`Option` | Lean のコア |
| $`\mathrm{Par}_n(\gamma)`$、$`\mathrm{toP}`$ | `Fin n → Option (Set.Iio γ)`、`toP` | [Por/Supply.lean](../Por/Supply.lean) |
| $`\mathrm{Par}_n(\gamma)`$ が可算 | `input_countable` の中の `infer_instance` | 同上 |
