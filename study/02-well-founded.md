[← Back](README.md) | [English](en/02-well-founded.md) | [Japanese](02-well-founded.md)

# 整礎関係と整礎再帰

前提

| ノート | ここで使う言葉 |
|---|---|
| [01 順序数と ω₁](01-ordinals.md) | 順序数、無限降下列、ラベル $`\{o \le \omega_1\}`$ |

このノートは 3 つのことを説明する。整礎関係、整礎再帰、ラベルが下がることによる停止である。関係 $`R`$ の定義（[07](07-relation-r.md)）は §4 と §5 の形をしている。証明全体の形（[06](06-combinatorial-layer.md)）は §6 の形をしている。

## 1. 整礎関係

**定義（整礎）.** 集合 $`X`$ の上の関係 $`\prec`$ が **整礎** であるとは、$`X`$ の空でない部分集合 $`S`$ がどれも $`\prec`$-極小元を持つことをいう。極小元とは、$`y \prec x`$ となる $`y \in S`$ が無い $`x \in S`$ のことである。

整礎であることと、$`x_0 \succ x_1 \succ x_2 \succ \cdots`$ となる無限降下列が無いことは同値である。「無限降下列が無いなら整礎」の向きには、選択公理の弱い形（従属選択）を使う。

**Lean での定義.** Lean は `Acc`（到達可能）を使う。`r` は関係 $`\prec`$ で、`r y x` は $`y \prec x`$ を表す。

- `Acc r x` は、「$`r\,y\,x`$ となるすべての $`y`$ について `Acc r y`」のとき成り立つ。帰納的に定義される。
- `WellFounded r` は、すべての $`x`$ で `Acc r x` が成り立つことである。

`Acc r x` は「$`x`$ から $`r`$ を逆にたどる列は必ず止まる」という意味である。

| 関係 | 整礎か | Lean |
|---|---|---|
| $`\mathbb N`$ の $`\lt`$ | はい | `wellFounded_lt` |
| 順序数の $`\lt`$、ラベルの $`\lt`$ | はい | `wellFounded_lt` |
| 鍵の $`\lt`$（§3） | はい | `OmegaY.Keys.key_wellFounded` |
| $`\mathbb Z`$ の $`\lt`$ | いいえ | |
| 合法な式の全体の辞書式順序 | いいえ | `OmegaY.Expansion.Dynamics.not_wellFounded_lex_all_legal` |

最後の行の例。**式** は正の整数の有限列で、**合法** な式とは、空か、先頭の項が 1 の式である（[05](05-omegay-mountain.md) §1 で定義する）。式の **辞書式順序** では、最初に違う項の大小で比べる。一方が他方の真の接頭辞なら、短い方が小さい。すると次の無限降下列がある（Lean の証明の中の列 `onesThenTwo`）。

```math
(1,2) \gt (1,1,2) \gt (1,1,1,2) \gt (1,1,1,1,2) \gt \cdots
```

ω-Y の展開（式から新しい式を作る操作。[05](05-omegay-mountain.md) §4 で定義する）は辞書式順序を下げる（`Dynamics.next_lex`、[05](05-omegay-mountain.md) §7）。それでも辞書式順序だけでは停止は出ない。そこでラベルを使う（§6）。

## 2. 整礎帰納法

**定理（整礎帰納法）.** $`\prec`$ が整礎で、性質 $`P`$ が次を満たすとする。

```math
\forall x\ \Bigl(\bigl(\forall y \prec x\ \ P(y)\bigr) \implies P(x)\Bigr)
```

このとき、すべての $`x`$ で $`P(x)`$ が成り立つ。

**証明.** $`P`$ が偽になる $`x`$ の集合が空でないとする。その極小元 $`x`$ を取る。$`y \prec x`$ なら $`P(y)`$ は真である。仮定から $`P(x)`$ も真になり、矛盾する。$`\square`$

Lean では `WellFounded.induction` と `WellFoundedLT.induction` である。[09 3 つの定理の証明](09-obligations.md) の `top_abs` は、鍵（§3）の順序でこれを使う。

## 3. 辞書式積と鍵の順序

**定義（辞書式積）.** $`(A, \lt_A)`$ と $`(B, \lt_B)`$ に対し、$`A \times B`$ の **辞書式順序** を次で定める。

```math
(a, b) \prec (a', b') \iff a \lt_A a' \ \lor\ (a = a' \land b \lt_B b')
```

**定理.** $`\lt_A`$ と $`\lt_B`$ が整礎なら、辞書式順序も整礎である。

**証明.** $`a`$ についての整礎帰納法の中で、$`b`$ についての整礎帰納法をする。$`(a, b)`$ より小さい組は、$`a' \lt_A a`$ の組（外側の帰納法の仮定で到達可能）か、$`a`$ が同じで $`b' \lt_B b`$ の組（内側の帰納法の仮定で到達可能）である。$`\square`$

**例.** $`\mathbb N \times \mathbb N`$ で、$`(1, 0)`$ より小さい組は $`(0, 0), (0, 1), (0, 2), \ldots`$ と無限個ある。それでも降下列はどれも有限である。例えば $`(1,0) \succ (0, 100) \succ (0, 99) \succ \cdots \succ (0, 0)`$ は 102 項で止まる。

Lean では `Prod.Lex` と `WellFounded.prod_lex` である。

**定義（鍵）.** $`m`$ を自然数とする。長さ $`m`$ の **鍵** は、ラベル（[01](01-ordinals.md) §6）か $`\top`$ を $`m`$ 個並べた列である。$`\top`$ はラベルでない新しい元で、どのラベルよりも大きい。[01](01-ordinals.md) §6 の $`\mathrm{top} = \omega_1`$ はラベルなので、$`\omega_1 \lt \top`$ である。

```math
\mathrm{Key}_m = \mathrm{Lex}\bigl(\mathrm{Fin}\ m \to \mathrm{Label} \cup \{\top\}\bigr)
```

$`\mathrm{Fin}\ m = \{0, \ldots, m-1\}`$（[01](01-ordinals.md) §5）で、$`\mathrm{Fin}\ m \to X`$ は $`X`$ の元を $`m`$ 個並べた列である。列の $`i`$ 番目の元を **座標** $`i`$ と呼ぶ。$`\mathrm{Lex}(\ldots)`$ は、この列の集合に辞書式順序を入れたものである。つまり **最初に違う座標** で比べる。Lean では `OmegaY.Keys.Key m Label := Lex (Fin m → WithTop Label)` である。

| 比べる 2 つの鍵（$`m = 2`$） | 結果 | 理由 |
|---|---|---|
| $`(3, 5)`$ と $`(3, \top)`$ | $`(3, 5) \lt (3, \top)`$ | 座標 0 が等しく、座標 1 で $`5 \lt \top`$ |
| $`(2, \top)`$ と $`(3, 0)`$ | $`(2, \top) \lt (3, 0)`$ | 座標 0 で $`2 \lt 3`$ |
| $`(\omega, 0)`$ と $`(5, \top)`$ | $`(5, \top) \lt (\omega, 0)`$ | 座標 0 で $`5 \lt \omega`$ |

**定理（`key_wellFounded`）.** $`\mathrm{Key}_m`$ の順序は整礎である。

**証明.** $`\mathrm{Label} \cup \{\top\}`$ は整礎である。降下列は $`\top`$ を高々最初の項に 1 回含み、残りはラベルの降下列だからである。長さ $`m`$ の列の辞書式順序は、上の辞書式積を $`m - 1`$ 回くり返したものと同じ順序である。よって整礎である。$`\square`$

Lean では、Mathlib のインスタンス（有限の添字の上の辞書式順序は整礎）から `wellFounded_lt` で出す。

**定義（段と上端）.** [07](07-relation-r.md) で定義する関係 $`R(\theta, a, b)`$（$`\theta`$ は鍵、$`a`$ と $`b`$ はラベル）は、組 $`(b, \theta)`$ についての整礎再帰で定義する（§4）。この組を **段** と呼ぶ。3 番目の引数 $`b`$ を **上端** と呼ぶ。段の順序 $`\lhd`$ は、ラベルの順序と鍵の順序の辞書式積である（[Por/Relation.lean](../Por/Relation.lean)）。

```math
(b', \kappa') \lhd (b, \theta) \iff b' \lt b\ \lor\ (b' = b \land \kappa' \lt \theta)
```

$`b', b`$ はラベル、$`\kappa', \theta`$ は鍵である。上の 2 つの定理から、$`\lhd`$ は整礎である。Lean では `StageLT := Prod.Lex (· < ·) (· < ·)` と `stage_wf` である。

## 4. 整礎再帰

**定理（整礎再帰）.** $`\prec`$ を $`T`$ の上の整礎関係とする。$`V`$ を値の集合とする。各 $`t \in T`$ と、「$`t`$ より小さい引数での値」を受け取って、$`t`$ での値を返す規則 $`G`$ があるとする。このとき、次を満たす関数 $`F : T \to V`$ がちょうど 1 つある。$`F{\restriction}X`$ は、$`F`$ を集合 $`X`$ に制限した関数である。

```math
F(t) = G\bigl(t,\ F{\restriction}\{t' \mid t' \prec t\}\bigr)
```

**例（Ackermann 関数）.** 引数の組 $`(m, n)`$ の集合 $`\mathbb N \times \mathbb N`$ に、§3 の辞書式順序を入れる。

```math
\begin{aligned}
A(0, n) &= n + 1, \cr
A(m+1, 0) &= A(m, 1), \cr
A(m+1, n+1) &= A\bigl(m,\ A(m+1, n)\bigr).
\end{aligned}
```

右辺が呼ぶ引数 $`(m, 1)`$、$`(m+1, n)`$、$`(m, \cdot)`$ は、どれも左辺の引数より辞書式に小さい。だから整礎再帰で定義できる。

**Lean での形.** `WellFounded.fix` は、規則 $`G`$ を次の型で受け取る。`r` は関係 $`\prec`$ で、`r t' t` は $`t' \prec t`$ である。

```lean
G : (t : T) → ((t' : T) → r t' t → V) → V
```

2 番目の引数（以下 `IH`）は、引数 `t'` と、`t'` が小さいことの証明を受け取る。証明が無いと呼べない。定義の等式は `WellFounded.fix_eq` である。

## 5. ガードつきの再帰

関係 $`R`$ の定義（[07](07-relation-r.md)）では、「どの段（§3）を読むか」が論理式（[03](03-sigma1-elementary.md) §2）の中の変数の値で決まる。書く前に、読む段が小さいとは言えない。そこで次の形にする。

1. 読みたい値を $`\exists h : (\text{段が小さい}),\ \mathrm{IH}(\text{段}, h)`$ と書く。これを **ガード** と呼ぶ。段が小さくないところでは、この式は偽になる。
2. 定義の等式 `fix_eq` を得る。この段階では、右辺にガードが付いている。
3. 右辺が実際に読むところでは、ガードがいつも真であることを示す。するとガードを外した等式が得られる。

[07 関係 R](07-relation-r.md) では、1 が `stepF`、2 と 3 が `R_iff` の証明である。

**小さい例.** $`\mathbb N`$ の上で $`F(n) := 1 + \sum_{i \in S_n} F(i)`$ という形の定義を考える。$`S_n`$ は $`n`$ ごとに与えた有限集合で、$`n`$ 以上の数を含むかもしれない。そのため、このままでは整礎再帰にならない。ガードつきで $`F(n) := 1 + \sum_{i \in S_n,\ i \lt n} F(i)`$ と書けば、整礎再帰で定義できる。$`S_n \subseteq \{0, \ldots, n-1\}`$ が別に示せれば、ガードを外した式 $`F(n) = 1 + \sum_{i \in S_n} F(i)`$ が成り立つ。

## 6. ラベルの上界による停止

状態の集合 $`X`$ の上の 1 段の関係 $`\to`$ が整礎であることを、整礎な順序 $`(L, \lt)`$ のラベルで示す。

**定理.** 状態 $`s \in X`$ とラベル $`\alpha \in L`$ の間の関係 $`\mathrm{valid}(s, \alpha)`$ が次を満たすとする。

- ある $`\alpha_0`$ があって、どの状態 $`s`$ でも $`\mathrm{valid}(s, \alpha_0)`$ である。
- $`\mathrm{valid}(s, \alpha)`$ で $`s \to t`$ なら、ある $`\alpha' \lt \alpha`$ で $`\mathrm{valid}(t, \alpha')`$ である。

このとき、$`\to`$ は整礎である。つまり $`s_0 \to s_1 \to s_2 \to \cdots`$ という無限列は無い。

**証明.** $`\alpha`$ についての整礎帰納法で、「$`\mathrm{valid}(s, \alpha)`$ なら $`s`$ は到達可能」を示す。$`s \to t`$ なら $`t`$ に $`\alpha' \lt \alpha`$ があるので、帰納法の仮定から $`t`$ は到達可能である。$`\square`$

大事な点は、ラベルが 1 つの状態に 1 つに決まっている必要が無いことである。「どれか 1 つのラベル付けがある」ことと「1 段進むと、もっと小さい上界のラベル付けがある」ことだけを使う。

ω-Y の証明では次のように当てはめる（[06](06-combinatorial-layer.md) §8）。表の言葉は後のノートで定義する。式 $`s`$ の展開 $`s[N]`$（$`N`$ はコピーの回数）は [05](05-omegay-mountain.md) §4、$`()`$ は空の式、山は [05](05-omegay-mountain.md) §3、山の次元 $`D`$ は [05](05-omegay-mountain.md) §7 である。山の **表現** は、山の列に付けた $`\omega_1`$ より下のラベルの狭義増加の列で、山の辺ごとの条件を満たすものである（[06](06-combinatorial-layer.md) §4）。

| 一般形 | ω-Y |
|---|---|
| 状態 | 式 $`s`$（`Dynamics.Expr`） |
| $`s \to t`$ | 1 段の展開 `Dynamics.Step t s`（$`s \ne ()`$ かつ $`t = s[N]`$） |
| ラベル | `Model.Label`（$`\omega_1`$ 以下の順序数） |
| $`\mathrm{valid}(s, \alpha)`$ | $`s`$ の山に次元 $`D`$ の表現があり、そのラベルがどれも $`\alpha`$ より小さい（$`D`$ は始めの式で固定する） |
| $`\alpha_0`$ | $`\omega_1`$（`keyRepresentation_exists` と `KeyRepresentation.bounded`） |
| $`\alpha'`$ | 古い表現の末尾のラベル（最後の列のラベル） |

Lean の本体は `Dynamics.accessible_of_representation_below` で、同じ帰納法を直接書いている（[OmegaY/Expansion/DynamicsRepresentationRank.lean](../OmegaY/Expansion/DynamicsRepresentationRank.lean)）。1-Y 版は末尾のラベルそのものについて帰納法をした。ω-Y 版はすべてのラベルの上界 $`\alpha`$ について帰納法をする。そのため、展開の結果が空の式でも、末尾のラベルを考えなくてよい。空の式からの 1 段の展開は無い（`Step` の定義が $`s \ne ()`$ を要求する。`Dynamics.empty_accessible`）。

## 7. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md)「関係 R」 | （上端、鍵）の辞書式順序による整礎再帰 |
| [notes/01-design.md](../notes/01-design.md) §2.3 | 再帰の段の順序と、右辺が読む段 |
| [Por/Relation.lean](../Por/Relation.lean) | §3〜§5（`StageLT`、`stage_wf`、`stepF`、`R`、`R_iff`） |
| [Por/Supply.lean](../Por/Supply.lean) | §2（`top_abs` の鍵についての帰納法） |
| [OmegaY/Keys.lean](../OmegaY/Keys.lean) | §3（鍵の順序と `key_wellFounded`） |
| [OmegaY/Expansion/DynamicsRepresentationRank.lean](../OmegaY/Expansion/DynamicsRepresentationRank.lean) | §6（ラベルの上界についての帰納法） |

## 8. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| 到達可能 | `Acc` | Lean のコア |
| 整礎 | `WellFounded` | Lean のコア |
| 整礎帰納法 | `WellFounded.induction`、`WellFoundedLT.induction` | Lean のコア、Mathlib |
| 辞書式積 | `Prod.Lex`、`WellFounded.prod_lex` | 同上 |
| 整礎再帰とその等式 | `WellFounded.fix`、`WellFounded.fix_eq` | Lean のコア |
| 段とその順序 | `StageLT`、`stage_wf` | [Por/Relation.lean](../Por/Relation.lean) |
| ガードつきの 1 段 | `stepF` | 同上 |
| ガードを外す | `R_iff` | 同上 |
| 鍵とその順序 | `Keys.Key`、`Keys.key_wellFounded` | [OmegaY/Keys.lean](../OmegaY/Keys.lean) |
| 式の辞書式順序が整礎でない | `Dynamics.not_wellFounded_lex_all_legal` | [OmegaY/Expansion/LegalDomainBoundary.lean](../OmegaY/Expansion/LegalDomainBoundary.lean) |
| ラベルの上界による停止 | `Dynamics.accessible_of_representation_below`、`Dynamics.empty_accessible` | [OmegaY/Expansion/DynamicsRepresentationRank.lean](../OmegaY/Expansion/DynamicsRepresentationRank.lean) |
