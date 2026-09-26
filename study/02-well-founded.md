[← Back](README.md) | [English](en/02-well-founded.md) | [Japanese](02-well-founded.md)

# 整礎関係と整礎再帰

前提

| ノート | ここで使う言葉 |
|---|---|
| [01 順序数と ω₁](01-ordinals.md) | 順序数、$`\mathrm{Ord}`$、無限降下列、$`\lt`$ が整礎であること、ラベル $`\mathrm{Label}`$（§6）、$`\mathrm{Fin}\ m`$（§7） |

このノートは、整礎関係と整礎再帰を説明する。関係 $`R`$ の定義（[07](07-relation-r.md)）は §4 と §5 の形をしている。展開の停止性の証明（[06](06-combinatorial-layer.md) §8）は §6 の形をしている。

## 1. 整礎関係

**定義（整礎）.** 集合 $`X`$ の上の関係 $`\prec`$ が **整礎** であるとは、$`X`$ の空でない部分集合 $`S`$ がどれも $`\prec`$-極小元を持つことをいう。極小元とは、$`y \prec x`$ となる $`y \in S`$ が無い $`x \in S`$ のことである。

整礎であることと、$`x_0 \succ x_1 \succ x_2 \succ \cdots`$ となる無限降下列が無いことは同値である。「無限降下列が無いなら整礎」の向きには、選択公理の弱い形（従属選択）を使う。

**定義（到達可能）.** $`x`$ が **到達可能** であるとは、$`y \prec x`$ となるすべての $`y`$ が到達可能であることをいう。これは帰納的な定義である。到達可能な元の集合は、この条件で閉じた最小の集合である。

$`x`$ が到達可能であることは、「$`x`$ から $`\prec`$ を逆にたどる列は必ず止まる」という意味である。$`\prec`$ が整礎であることは、すべての $`x`$ が到達可能であることと同値である。

| 関係 | 整礎か |
|---|---|
| $`\mathbb N`$ の $`\lt`$ | はい |
| 順序数の $`\lt`$（ラベルの $`\lt`$ も） | はい |
| $`\mathbb Z`$ の $`\lt`$ | いいえ |
| ω-Y の式の辞書式順序 | いいえ |

最後の行の例。ω-Y の式は、[05](05-omegay-mountain.md) §1 で定義する正の整数の有限列である。式の辞書式順序では真の接頭辞が小さく、最初に違う項で比べる。すると次の無限降下列がある。

```math
(1,2) \gt (1,1,2) \gt (1,1,1,2) \gt (1,1,1,1,2) \gt \cdots
```

ω-Y の展開は辞書式順序を下げる（[05](05-omegay-mountain.md) §7）。それでも辞書式順序だけでは停止は出ない。そこで、式の列にラベル（[01](01-ordinals.md) §6）を付けて、ラベルが展開で下がることを使う（§6、[06](06-combinatorial-layer.md) §8）。

## 2. 整礎帰納法

**定理（整礎帰納法）.** $`\prec`$ が整礎で、性質 $`P`$ が次を満たすとする。

```math
\forall x\ \Bigl(\bigl(\forall y \prec x\ \ P(y)\bigr) \implies P(x)\Bigr)
```

このとき、すべての $`x`$ で $`P(x)`$ が成り立つ。

**証明.** $`P`$ が偽になる $`x`$ の集合が空でないとする。その極小元 $`x`$ を取る。$`y \prec x`$ なら $`P(y)`$ は真である。仮定から $`P(x)`$ も真になり、矛盾する。$`\square`$

[09 3 つの定理の証明](09-obligations.md) §3.1 の定理（上端の述語の絶対性）は、鍵（§3）の順序でこれを使う。

## 3. 辞書式積

**定義（辞書式積）.** $`(A, \lt_A)`$ と $`(B, \lt_B)`$ に対し、$`A \times B`$ の **辞書式順序** を次で定める。

```math
(a, b) \prec (a', b') \iff a \lt_A a' \ \lor\ (a = a' \land b \lt_B b')
```

**定理.** $`\lt_A`$ と $`\lt_B`$ が整礎なら、辞書式順序も整礎である。

**証明.** $`a`$ についての整礎帰納法の中で、$`b`$ についての整礎帰納法をする。$`(a, b)`$ より小さい組は、$`a' \lt_A a`$ の組（外側の帰納法の仮定で到達可能）か、$`a`$ が同じで $`b' \lt_B b`$ の組（内側の帰納法の仮定で到達可能）である。$`\square`$

**例.** $`\mathbb N \times \mathbb N`$ で、$`(1, 0)`$ より小さい組は $`(0, 0), (0, 1), (0, 2), \ldots`$ と無限個ある。それでも降下列はどれも有限である。例えば $`(1,0) \succ (0, 100) \succ (0, 99) \succ \cdots \succ (0, 0)`$ は 102 項で止まる。

**定義（鍵）.** $`\top`$ をラベルでない新しい元とし、どのラベルよりも大きいとする。$`\mathrm{Label}_\top := \mathrm{Label} \cup \{\top\}`$ と書く。$`\omega_1`$ はラベルなので、$`\omega_1 \lt \top`$ である。$`m \in \mathbb N`$ とする。長さ $`m`$ の **鍵** は、$`\mathrm{Label}_\top`$ の元を $`m`$ 個並べた列 $`\kappa = (\kappa_0, \ldots, \kappa_{m-1})`$ である。$`\kappa_i`$ を $`\kappa`$ の **座標** $`i`$ と呼ぶ。鍵の集合を $`\mathrm{Key}_m`$ と書く。

```math
\mathrm{Key}_m := \mathrm{Fin}\ m \to \mathrm{Label}_\top
```

鍵の順序は、最初に違う座標で比べる辞書式順序である。

```math
\kappa \lt \kappa' \iff \exists i \lt m\ \Bigl(\bigl(\forall j \lt i\ \ \kappa_j = \kappa'_j\bigr) \land \kappa_i \lt \kappa'_i\Bigr)
```

| 比べる 2 つの鍵（$`m = 2`$） | 結果 | 理由 |
|---|---|---|
| $`(3, 5)`$ と $`(3, \top)`$ | $`(3, 5) \lt (3, \top)`$ | 座標 0 が等しく、座標 1 で $`5 \lt \top`$ |
| $`(2, \top)`$ と $`(3, 0)`$ | $`(2, \top) \lt (3, 0)`$ | 座標 0 で $`2 \lt 3`$ |
| $`(\omega, 0)`$ と $`(5, \top)`$ | $`(5, \top) \lt (\omega, 0)`$ | 座標 0 で $`5 \lt \omega`$ |

表の比較は、この定義を Python で書いて確かめた。

**定理.** $`\mathrm{Key}_m`$ の順序は整礎である。

**証明.** $`\mathrm{Label}_\top`$ は整礎である。降下列は $`\top`$ を高々最初の項に 1 回含み、残りはラベルの降下列だからである。長さ $`m`$ の列の辞書式順序は、上の辞書式積を $`m - 1`$ 回くり返したものと同じ順序である。よって上の定理から整礎である。$`\square`$

**定義（段と上端）.** 関係 $`R(\theta, a, b)`$（[07](07-relation-r.md) で定義する。$`\theta \in \mathrm{Key}_m`$、$`a, b \in \mathrm{Label}`$）の 3 つめの引数 $`b`$ を **上端** と呼ぶ。$`R`$ の整礎再帰（§4）では、組 $`(b, \theta) \in \mathrm{Label} \times \mathrm{Key}_m`$ を引数にする。この組を **段** と呼ぶ。段の順序 $`\lhd`$ は、ラベルの順序と鍵の順序の辞書式積である。

```math
(b', \kappa') \lhd (b, \theta) \iff b' \lt b\ \lor\ (b' = b \land \kappa' \lt \theta)
```

上の 2 つの定理から、$`\lhd`$ は整礎である。「1 段の展開」（[05](05-omegay-mountain.md) §7）の「1 段」は展開 1 回のことで、この段とは関係ない。

## 4. 整礎再帰

**定理（整礎再帰）.** $`\prec`$ を $`T`$ の上の整礎関係とする。整礎再帰では、$`T`$ の元を関数の **引数** と呼ぶ。各 $`t \in T`$ と、「$`t`$ より小さい引数での値」を受け取って、$`t`$ での値を返す規則 $`G`$ があるとする。このとき、次を満たす関数 $`F`$ がちょうど 1 つある。

```math
F(t) = G\bigl(t,\ F{\restriction}\{t' \mid t' \prec t\}\bigr)
```

ここで $`F{\restriction}X`$ は、$`F`$ の定義域を集合 $`X`$ に制限した関数である。

**例（Ackermann 関数）.** 引数の集合を $`\mathbb N \times \mathbb N`$ とし、辞書式順序で比べる。

```math
\begin{aligned}
A(0, n) &= n + 1, \cr
A(m+1, 0) &= A(m, 1), \cr
A(m+1, n+1) &= A\bigl(m,\ A(m+1, n)\bigr).
\end{aligned}
```

右辺が呼ぶ引数 $`(m, 1)`$、$`(m+1, n)`$、$`(m, \cdot)`$ は、どれも左辺の引数より辞書式に小さい。だから整礎再帰で定義できる。

規則 $`G`$ が読んでよいのは、$`t' \prec t`$ となる引数 $`t'`$ での値 $`F(t')`$ だけである。

## 5. ガードつきの再帰

関係 $`R`$ の定義（[07](07-relation-r.md)）では、「どの段（§3）を読むか」が論理式（[03](03-sigma1-elementary.md) §2 で定義する）の中の変数の値で決まる。書く前に、読む段が小さいとは言えない。そこで次の形にする。

1. 引数 $`t'`$ での値を読むところを「$`t' \prec t \land F(t')`$」と書く。前半の条件 $`t' \prec t`$ を **ガード** と呼ぶ。引数が小さくないところでは、この式は偽になる。
2. §4 の定理から、定義の等式 $`F(t) = G(t, F{\restriction}\{t' \mid t' \prec t\})`$ を得る。この段階では、右辺にガードが付いている。
3. 右辺が実際に読むところでは、ガードがいつも真であることを示す。するとガードを外した等式が得られる。

[07 関係 R](07-relation-r.md) では、1 が §5 の段の解釈、2 が §5 のガードつきの等式、3 が §6 の補題と定理である。

**小さい例.** $`\mathbb N`$ の上で $`F(n) := 1 + \sum_{i \in S_n} F(i)`$ という形の定義を考える。$`S_n`$ は $`n`$ ごとに与えた有限集合で、$`n`$ 以上の数を含むかもしれない。そのため、このままでは整礎再帰にならない。ガードつきで $`F(n) := 1 + \sum_{i \in S_n,\ i \lt n} F(i)`$ と書けば、整礎再帰で定義できる。$`S_n \subseteq \{0, \ldots, n-1\}`$ が別に示せれば、ガードを外した式 $`F(n) = 1 + \sum_{i \in S_n} F(i)`$ が成り立つ。

## 6. ラベルの上界による停止

**定理（ラベルの上界による停止）.** $`(L, \lt)`$ を整礎な順序、$`X`$ を集合、$`\prec`$ を $`X`$ の上の関係とする。$`X`$ と $`L`$ の間の関係 $`V \subseteq X \times L`$ が、次の 2 つを満たすとする。

```math
\begin{aligned}
&\exists \alpha_0 \in L\ \ \forall s \in X\ \ V(s, \alpha_0), \cr
&\forall s, t \in X\ \ \forall \alpha \in L\ \ \Bigl(V(s, \alpha) \land t \prec s \implies \exists \alpha' \lt \alpha\ \ V(t, \alpha')\Bigr).
\end{aligned}
```

このとき $`\prec`$ は整礎である。

**証明.** $`\alpha`$ についての整礎帰納法（§2）で、次を示す。

```math
\forall \alpha \in L\ \ \forall s \in X\ \ \bigl(V(s, \alpha) \implies s \text{ は到達可能}\bigr)
```

$`V(s, \alpha)`$ とする。$`t \prec s`$ なら、2 つめの仮定から $`\alpha' \lt \alpha`$ で $`V(t, \alpha')`$ である。帰納法の仮定から $`t`$ は到達可能である。よって $`s`$ は到達可能である（§1）。1 つめの仮定から、どの $`s`$ も $`V(s, \alpha_0)`$ を満たすので、到達可能である。$`\square`$

- $`V`$ は関数でなくてよい。1 つの $`s`$ に、$`V(s, \alpha)`$ となる $`\alpha`$ がいくつあってもよい。
- [06](06-combinatorial-layer.md) §8 は、$`X`$ を式の集合、$`t \prec s`$ を 1 段の展開（[05](05-omegay-mountain.md) §7）、$`L`$ を $`\mathrm{Label}`$ としてこの定理を使う。$`V(s, \alpha)`$ の中身は [06](06-combinatorial-layer.md) §8 で述べる。
- 1-Y 版（[01](01-ordinals.md) §7）の 06 §6 は、表現の末尾のラベルそのものについて帰納法をした。ここでは、ラベルの上界 $`\alpha`$ について帰納法をする。

## 7. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md)「証明の形」 | 鍵 $`\mathrm{Key}_m`$ とその順序（§3） |
| [README](../README.md)「関係 R」 | 段（上端、鍵）の辞書式順序による整礎再帰（§3〜§5） |
| [notes/01-design.md](../notes/01-design.md) §2.3 | 段の順序と、右辺が読む段 |

## 8. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| 到達可能、整礎 | `Acc`、`WellFounded` | Lean のコア |
| 整礎帰納法 | `WellFounded.induction`、`WellFoundedLT.induction` | Lean のコア、Mathlib |
| 辞書式積 | `Prod.Lex`、`WellFounded.prod_lex` | 同上 |
| 整礎再帰とその等式 | `WellFounded.fix`、`WellFounded.fix_eq` | Lean のコア |
| $`\mathrm{Label}_\top`$ | `WithTop Label` | Mathlib |
| 鍵とその順序 | `Keys.Key m Label := Lex (Fin m → WithTop Label)`、`Keys.key_wellFounded` | [OmegaY/Keys.lean](../OmegaY/Keys.lean) |
| 段とその順序 | `StageLT := Prod.Lex (· < ·) (· < ·)`、`stage_wf` | [Por/Relation.lean](../Por/Relation.lean) |
| ガードつきの 1 段、ガードを外す（§5） | `stepF`、`R_iff` | 同上 |
| 式の辞書式順序が整礎でない（§1） | `Dynamics.not_wellFounded_lex_all_legal`（証明の中の列 `onesThenTwo`） | [OmegaY/Expansion/LegalDomainBoundary.lean](../OmegaY/Expansion/LegalDomainBoundary.lean) |
| 展開は辞書式順序を下げる | `Dynamics.next_lex` | [OmegaY/Expansion/LegalDynamics.lean](../OmegaY/Expansion/LegalDynamics.lean) |
| ラベルの上界による停止（§6） | `Dynamics.accessible_of_representation_below`、`Dynamics.empty_accessible` | [OmegaY/Expansion/DynamicsRepresentationRank.lean](../OmegaY/Expansion/DynamicsRepresentationRank.lean) |
