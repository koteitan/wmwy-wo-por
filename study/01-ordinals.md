[← Back](README.md) | [English](en/01-ordinals.md) | [Japanese](01-ordinals.md)

# 順序数と ω₁

前提: なし

このノートは、ラベルに使う順序数と、ラベルの上限に使う $`\omega_1`$ を説明する。使う事実は §5 の正則性、§6 のラベルの型、§7 のパラメータの数え方である。

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
- 順序数の全体は $`\lt`$ で整列する。どの順序数の集まりにも最小元がある。
- $`\omega^\omega`$ より小さい順序数は、$`\omega^{d} c_d + \cdots + \omega c_1 + c_0`$（$`c_i \in \mathbb N`$）の形にただ 1 通りに書ける（Cantor の標準形）。[05](05-omegay-mountain.md) の山の行はこの形の順序数である。

Lean では、順序数の型は `Ordinal.{0}` である。$`\{\beta \mid \beta \lt \gamma\}`$ は `Set.Iio γ` である。

## 2. 後者と極限

**定義（後者）.** $`\alpha + 1`$ は $`\alpha`$ の次の順序数である。$`\alpha + 1`$ の形の順序数を **後者順序数** と呼ぶ。

**定義（極限順序数）.** 0 でも後者順序数でもない順序数を **極限順序数** と呼ぶ。

| 順序数 | 種類 |
|---|---|
| $`0`$ | どちらでもない |
| $`5`$、$`\omega+1`$、$`\omega \cdot 2 + 3`$ | 後者 |
| $`\omega`$、$`\omega \cdot 2`$、$`\omega^2`$ | 極限 |

**性質.** $`\alpha`$ が極限順序数で $`\beta \lt \alpha`$ なら、$`\beta + 1 \lt \alpha`$ である。したがって $`\beta`$ より上に、$`\alpha`$ より下の元が無限個ある。

- この性質は [03](03-sigma1-elementary.md) の例で使う。
- Lean では、$`\omega_1`$（§4）について `(isSuccLimit_omega 1).add_one_lt` の形で使う。[08](08-closure-chain.md) の `wh_lt` と `nextO_lt` である。

## 3. 上限

**定義（上限）.** 順序数の集合 $`S`$ の **上限** $`\sup S`$ は、$`S`$ のすべての元以上である最小の順序数である。

- $`S`$ が最大元を持てば、$`\sup S`$ はその最大元である。空でない有限集合ならいつもそうである。空集合の上限は $`0`$ である。
- $`S`$ が最大元を持たなければ、$`\sup S`$ は $`S`$ に入らない。

| $`S`$ | $`\sup S`$ |
|---|---|
| $`\{2, 5, 3\}`$ | $`5`$ |
| $`\{0, 1, 2, \ldots\}`$ | $`\omega`$ |
| $`\{\omega, \omega+1, \omega+2, \ldots\}`$ | $`\omega \cdot 2`$ |

「すべての元より真に大きい」数が欲しいときは、$`\sup_{i} (y_i + 1)`$ を使う。$`y_i \lt y_i + 1 \le \sup_i (y_i + 1)`$ だからである。Lean では `Ordinal.lt_iSup_add_one` である。[08](08-closure-chain.md) の証人の高さ `wh` はこの形である。

Lean では、添字つきの上限は `⨆ i, f i`（`iSup`）である。

## 4. 可算と ω₁

**定義（可算）.** 集合 $`X`$ が **可算** であるとは、$`X`$ が空であるか、全射 $`\mathbb N \to X`$ があることをいう。Lean では型のクラス `Countable` である。

**定義（可算順序数）.** 順序数 $`\alpha`$ が **可算** であるとは、$`\{\beta \mid \beta \lt \alpha\}`$ が可算であることをいう。

$`0, 1, \omega, \omega+1, \omega \cdot 2, \omega^2, \omega^\omega, \varepsilon_0`$ はどれも可算である。

**定義（ω₁）.** $`\omega_1`$ は最初の非可算順序数である。つまり、$`\omega_1`$ より小さい順序数はちょうど可算順序数である。

```math
\alpha \lt \omega_1 \iff \alpha \text{ は可算}
```

Lean では `ω₁` と書く。このリポジトリは次の事実を使う。

| 名前 | 内容 |
|---|---|
| `Ordinal.omega_pos 1` | $`0 \lt \omega_1`$ |
| `(isSuccLimit_omega 1).add_one_lt` | $`\alpha \lt \omega_1 \implies \alpha + 1 \lt \omega_1`$ |
| `Por.Supply.countable_iio_ordinal` | $`a \lt \omega_1 \implies \{\beta \mid \beta \lt a\}`$ は可算 |

`countable_iio_ordinal` は、$`\{\beta \mid \beta \lt a\}`$ の濃度が $`a`$ の濃度に等しいこと（`Cardinal.mk_Iio_ordinal`）と、$`a \lt \omega_1`$ なら $`a`$ の濃度が $`\aleph_0`$ 以下であることから出す。

## 5. ω₁ の正則性

**定理（ω₁ の正則性）.** 可算な添字の集合 $`I`$ と、各 $`i \in I`$ について $`\alpha_i \lt \omega_1`$ があるとする。このとき次が成り立つ。

```math
\sup_{i \in I} \alpha_i \lt \omega_1
```

**証明.** $`\sigma := \sup_i \alpha_i`$ と置く。$`\beta \lt \sigma`$ なら、ある $`i`$ で $`\beta \lt \alpha_i`$ である。よって

```math
\{\beta \mid \beta \lt \sigma\} = \bigcup_{i \in I} \{\beta \mid \beta \lt \alpha_i\}
```

である。右辺は可算集合の可算個の和である。$`\alpha_i = 0`$ の項は和に何も足さないので除く。残りの各 $`i`$ で全射 $`e_i : \mathbb N \to \alpha_i`$ を 1 つずつ選ぶ。$`I`$ を $`\mathbb N`$ で数え上げると、$`(n, t) \mapsto e_{i_n}(t)`$ は $`\mathbb N \times \mathbb N`$ から和の上への全射になる。$`\mathbb N \times \mathbb N`$ は可算なので、和も可算である。よって $`\sigma`$ は可算で、$`\sigma \lt \omega_1`$ である。$`\square`$

- 全射 $`e_i`$ を可算個同時に選ぶところで、選択公理（可算選択）を使う。
- 添字が非可算なら成り立たない。例えば $`\sup_{\alpha \lt \omega_1} \alpha = \omega_1`$ である。

Lean では `Ordinal.iSup_lt_omega_one` である。添字の型は `Countable` のインスタンスを持つ必要がある。このリポジトリでは 3 か所で使う（どれも [Por/Supply.lean](../Por/Supply.lean)）。

| 使う場所 | 添字の型 | 上限を取るもの |
|---|---|---|
| `wh_lt` | `Fin φ.n` | 1 組の証人の高さ |
| `nextO_lt` | `Input S γ`（§7） | 証人の高さ |
| `lam_lt` | `ℕ` | 閉包の塔 |

## 6. ラベルの型

**定義（ラベル）.** ラベルは $`\omega_1`$ 以下の順序数である。

```math
\mathrm{Label} = \{\, o \mid o \le \omega_1 \,\}, \qquad \mathrm{top} = \omega_1
```

Lean では `Por.Supply.Label := {o : Ordinal.{0} // o ≤ ω₁}` と `Por.Supply.top` である。`OmegaY.Reflection.OrdinalSupply.Label` と `OmegaY.Model.Label` は同じ型の別名である。順序は順序数の順序を制限したもので、整列している。

| 名前 | 内容 |
|---|---|
| `Por.Supply.zeroL` | ラベル $`0`$ |
| `Por.Supply.zeroL_lt_top` | $`0 \lt \omega_1`$ |
| `Por.Supply.le_topL` | どのラベル $`x`$ も $`x \le \omega_1`$ |
| `Por.Supply.countable_iio` | ラベル $`a \lt \omega_1`$ について、$`a`$ より下のラベルの集合は可算 |
| `OrdinalSupply.bot_lt_top` | 最小のラベル $`\bot = 0`$ について $`\bot \lt \omega_1`$ |

**なぜ ω₁ 自身をラベルに入れるか.** 表現のラベルはどれも $`\omega_1`$ より下にある（[06](06-combinatorial-layer.md) の `KeyRepresentation.bounded`）。一方、意味の層は「上端が $`\omega_1`$ の関係」$`R(\kappa, x, \omega_1)`$ を使う（[08](08-closure-chain.md) の Good、[09](09-obligations.md) の `top_abs`）。そのために $`\omega_1`$ も同じ型の元にしてある。

## 7. パラメータの数え方

[08](08-closure-chain.md) では、「$`\gamma`$ より下のパラメータを持つすべての論理式」について上限を取る。添字の型を次のように決める。

**定義（`Input`）.**

```math
\mathrm{Input}(\gamma) = \sum_{\varphi \in \mathrm{Form}} \bigl(\mathrm{Fin}\ n_\varphi \to \mathrm{Option}\{\, x \mid x \lt \gamma \,\}\bigr)
```

各位置に、$`\gamma`$ より下のラベルを置くか、何も置かない（`none`）。`toP` は、`none` を $`0`$ に置き換えてラベルの列にする関数である。

**定理（`input_countable`）.** $`\gamma \lt \omega_1`$ なら、`Input S γ` は可算である。

**証明.** 論理式の型 `Form S` は可算である（[08](08-closure-chain.md) §2）。$`\gamma`$ より下のラベルの集合は可算である（`countable_iio`）。可算な型の上の有限の関数の型、`Option`、依存和は、どれも可算である。$`\square`$

**例.** $`\gamma = \omega + 1`$ とする。3 変数の論理式 $`\varphi`$ で、位置 0 と 2 をパラメータにするとき、パラメータ $`(3, \cdot, \omega)`$ は入力 $`(\varphi, (\mathrm{some}\ 3, \mathrm{none}, \mathrm{some}\ \omega))`$ で表される。

1-Y 版は、$`\gamma`$ より下の点を自然数の列で数え上げて、添字の型を $`\gamma`$ に依らないものにした。このリポジトリは点をそのまま添字にする。添字の型は $`\gamma`$ に依るが、可算なので §5 の定理をそのまま使える。

## 8. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md)「関係 R」「3 つの定理の証明」 | ラベルは $`\omega_1`$ 以下の順序数、Good な点は $`\omega_1`$ の中で共終 |
| [notes/01-design.md](../notes/01-design.md) §3.3 | 閉じた点、可算個の論理式、$`\omega`$ 回のくり返し |
| [Por/Supply.lean](../Por/Supply.lean) | §4〜§7 のすべて |
| [OmegaY/Reflection/OrdinalSupply.lean](../OmegaY/Reflection/OrdinalSupply.lean) | `Label`、`top`、`OrderBot`、`bot_lt_top` |

## 9. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| 順序数の型 | `Ordinal.{0}` | Mathlib |
| $`\lt`$ が整礎 | `wellFounded_lt` | Mathlib |
| 上限 | `iSup`（`⨆`）、`Ordinal.lt_iSup_add_one` | Mathlib |
| $`\omega_1`$ | `ω₁`、`Ordinal.omega_pos 1`、`isSuccLimit_omega 1` | Mathlib |
| 正則性 | `Ordinal.iSup_lt_omega_one` | Mathlib |
| 可算順序数の下は可算 | `countable_iio_ordinal`、`countable_iio` | [Por/Supply.lean](../Por/Supply.lean) |
| ラベルと上端 | `Label`、`top`、`zeroL`、`zeroL_lt_top`、`le_topL` | 同上 |
| ラベルの別名 | `OrdinalSupply.Label`、`OrdinalSupply.top`、`bot_lt_top`、`Model.Label` | [OmegaY/Reflection/OrdinalSupply.lean](../OmegaY/Reflection/OrdinalSupply.lean)、[OmegaY/Model.lean](../OmegaY/Model.lean) |
| パラメータの入力 | `Input`、`toP`、`input_countable` | [Por/Supply.lean](../Por/Supply.lean) |
