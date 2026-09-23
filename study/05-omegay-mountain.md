[← Back](README.md) | [English](en/05-omegay-mountain.md) | [Japanese](05-omegay-mountain.md)

# ω-Y 数列と山

前提

| ノート | ここで使う言葉 |
|---|---|
| [01 順序数と ω₁](01-ordinals.md) | 順序数、$`\omega^\omega`$ より小さい順序数の Cantor の標準形 |
| [02 整礎関係と整礎再帰](02-well-founded.md) | 整礎、式の辞書式順序が整礎でないこと |

このノートは、weak-magma ω-Y 数列とその展開が Lean でどう定義されているかを説明する。定義は Phyrion 氏の形式化（[Phyrion1343/omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean)）のもので、このリポジトリの `OmegaY/` に変えずに移してある。山は [OmegaY/Canonical/Build.lean](../OmegaY/Canonical/Build.lean)、展開は [OmegaY/Expansion/Build.lean](../OmegaY/Expansion/Build.lean) にある。

例の値は、`Canonical.build`、`Canonical.fullSummary`、`Expansion.expand`、`Expansion.expandDiagram`、`Expansion.markers` を Lean 4.33.1 の `#eval` で計算したものである（2026-09-23）。途中の手順は、その定義を手でたどったものである。

## 1. 式

**定義（式）.** **式** は正の整数の有限列 $`s = (s_0, \ldots, s_x)`$ で、空か、$`s_0 = 1`$ のものである（`Canonical.Legal`、`Dynamics.Expr`）。

- 列の番号は 0 から数える。$`i`$ 番目の項を「列 $`i`$」と呼ぶ。最後の列の番号を $`x`$ と書く。
- 標準の種は $`(1, m)`$（$`m \ge 2`$）である。Lean では `Dynamics.seed n` $`= (1, n+2)`$ である。
- 式の順序は辞書式順序である（`Dynamics.Lex`）。真の接頭辞は小さい。[02](02-well-founded.md) §1 のとおり、この順序は式全体の上では整礎でない。

## 2. 行

ω-Y の山の行は、自然数ではなく $`\omega^\omega`$ より小さい順序数である。

**定義（行）.** **行** は、有限個を除いて 0 の係数の列 $`(c_0, c_1, c_2, \ldots)`$ である（`OmegaY.Row`、係数は `Row.coeff`）。次の順序数と同一視する。

```math
\omega^{d} c_d + \cdots + \omega^{2} c_2 + \omega c_1 + c_0
```

順序は、係数が違う最も大きい指数で比べる（`Row.LexLt`）。これは順序数の順序と同じである。Lean の表示（`Row.toList`）は係数を指数の小さい順に並べる。

| 行 | 表示 |
|---|---|
| $`1`$ | `[1]` |
| $`2`$ | `[2]` |
| $`\omega`$ | `[0, 1]` |
| $`\omega + 1`$ | `[1, 1]` |
| $`\omega \cdot 2`$ | `[0, 2]` |
| $`\omega^2`$ | `[0, 0, 1]` |

**定義（跳び）.** 2 つの行 $`a, b`$ の **跳び** を次で定める（`Row.jump`）。

```math
\mathrm{jump}(a, b) = \begin{cases} 0 & (a = b) \cr 1 + \max\{\, i \mid c_i(a) \ne c_i(b) \,\} & (a \ne b) \end{cases}
```

**定義（ω の冪を足す）.** $`\mathrm{bump}(a, d) = a + \omega^d`$（順序数の和）である（`Row.bump`）。係数で書くと、$`d`$ より下の係数を 0 にし、$`d`$ の係数に 1 を足し、$`d`$ より上の係数はそのままにする。

**定義（次の行）.** $`B(a, b) = \mathrm{bump}(a, \mathrm{jump}(a, b)) = a + \omega^{\mathrm{jump}(a, b)}`$ である（`Row.B`）。

| $`a`$ | $`b`$ | $`\mathrm{jump}(a, b)`$ | $`B(a, b)`$ |
|---|---|---|---|
| $`1`$ | $`1`$ | $`0`$ | $`2`$ |
| $`2`$ | $`2`$ | $`0`$ | $`3`$ |
| $`2`$ | $`1`$ | $`1`$ | $`2 + \omega = \omega`$ |
| $`\omega`$ | $`1`$ | $`2`$ | $`\omega + \omega^2 = \omega^2`$ |
| $`\omega`$ | $`\omega`$ | $`0`$ | $`\omega + 1`$ |
| $`\omega + 1`$ | $`\omega`$ | $`1`$ | $`\omega \cdot 2`$ |

$`a = b`$ なら行は 1 つ上がる。これは 1-Y の山の行の動きと同じである。$`a \ne b`$ なら行は $`\omega`$ の冪だけ跳ぶ。

## 3. 山の作り方

山は列の配列で、列は下から上への節点の配列である（`Canonical.Mountain`、`Canonical.Column`）。節点 `Cell` は 3 つの成分を持つ。行 `row`、値 `value`、左の脚 `left` である。`left` は左の列の節点を指す。

**定義（標準の山 `Canonical.build`）.** 列 $`c = 0, 1, \ldots, x`$ を左から順に作る。

1. 番号 0 の節点は **phantom**（仮の節点）で、行 0、値 0 である。
2. 番号 1 の節点は **最下の節点** で、行 1、値 $`s_c`$ である。左の脚は列 $`c - 1`$ の phantom である（$`c = 0`$ では無い）。
3. 一番上の節点 $`u`$ の値 $`v`$ が 1 より大きい間、次をくり返す（`growColumn`）。$`u`$ の **父** $`\pi`$ を探す。$`u`$ の上に、行 $`B(\mathrm{row}(u), \mathrm{row}(\pi))`$、値 $`v - \mathrm{value}(\pi)`$、左の脚 $`\pi`$ の節点を積む。
4. 値が 1 の節点に着いたら、その列は終わりである。どの列も一番上の値は 1 である。

**定義（父の探し方 `findParent`）.** 候補 $`w`$ を $`u`$ 自身から始める。次の Q の手順をくり返す（`nextCandidate`）。

- $`w`$ の左の脚 $`L`$ をたどる。$`L`$ の列の中で、$`L`$ から上へ、次の節点の行が $`\mathrm{row}(w)`$ 以下である限り登る（`climb`）。着いた節点を新しい候補 $`w`$ にする。
- 新しい候補の値が $`0 \lt \mathrm{value}(w) \lt v`$ なら、$`w`$ が父である。そうでなければ、この $`w`$ から Q の手順をくり返す。

最下の行では、候補は列 $`c-1, c-2, \ldots`$ の最下の節点を順にたどる。したがって最下の節点の父は、値が $`s_c`$ より小さい最も右の列の最下の節点である。これは 1-Y の行 0 の親と同じである。

**定義（辺）.** 節点 $`u`$（phantom でない）の真上に節点 $`u^+`$ があるとき、$`u`$ から $`u^+`$ への **辺** がある。$`u^+`$ の左の脚を辺の **父** $`\pi`$ と呼ぶ。父はいつも左の列にある。

```math
\mathrm{value}(u^+) = \mathrm{value}(u) - \mathrm{value}(\pi), \qquad \mathrm{row}(u^+) = \mathrm{row}(u) + \omega^{\mathrm{jump}(\mathrm{row}(u), \mathrm{row}(\pi))}
```

跳び $`\mathrm{jump}(\mathrm{row}(u), \mathrm{row}(\pi))`$ を辺の **次数** と呼ぶ（[06](06-combinatorial-layer.md) の `RealStoredEdge.degree`）。

**例（$`(1, 3, 3)`$）.** 表の「$`v \leftarrow (j, h)`$」は、値が $`v`$ で、左の脚（下の節点からの辺の父）が列 $`j`$ の行 $`h`$ の節点であることを表す。Lean の参照 `Ref` は行の代わりに下からの番号を使う。最下の行の左の脚（左の列の phantom）は書かない。

| 行 | 列 0 | 列 1 | 列 2 |
|---|---|---|---|
| $`\omega`$ | | $`1 \leftarrow (0, 1)`$ | $`1 \leftarrow (0, 1)`$ |
| $`2`$ | | $`2 \leftarrow (0, 1)`$ | $`2 \leftarrow (0, 1)`$ |
| $`1`$ | $`1`$ | $`3`$ | $`3`$ |
| $`0`$ | phantom | phantom | phantom |

- 列 1 の最下の節点（値 3）：Q の手順で列 0 の最下の節点（値 1）に着く。$`1 \lt 3`$ なので父である。次の節点は行 $`B(1, 1) = 2`$、値 $`3 - 1 = 2`$ である。
- 列 1 の行 2 の節点（値 2）：左の脚は $`(0, 1)`$ で、列 0 にはその上の節点が無い。候補は $`(0, 1)`$ で、$`1 \lt 2`$ なので父である。次の節点は行 $`B(2, 1) = \omega`$、値 1 である。
- 列 2 の最下の節点（値 3）：最初の候補は列 1 の最下の節点で、値 3 は $`3`$ より小さくない。次の候補は列 0 の最下の節点で、父である。

**例（$`(1, 4)`$）.** 列 1 は行 $`1, 2, \omega, \omega^2`$ に値 $`4, 3, 2, 1`$ を持ち、父はどれも $`(0, 1)`$ である。行 $`\omega^2`$ は $`B(\omega, 1)`$ である。

**例（$`(1, 3, 10)`$ の列 2）.** 行 $`1, 2, 3, \omega, \omega + 1, \omega \cdot 2`$ に値 $`10, 7, 5, 3, 2, 1`$ を持つ。父は順に $`(1, 1), (1, 2), (1, 2), (1, \omega), (1, \omega)`$ である。例えば行 $`\omega`$ の節点は $`B(3, 2) = 3 + \omega = \omega`$、行 $`\omega \cdot 2`$ の節点は $`B(\omega + 1, \omega) = \omega \cdot 2`$ である。

## 4. 展開

**定義（展開 `expand s N`）.** $`N`$ はコピーの回数である。

**場合 1.** $`s`$ が空、$`s_x = 1`$、または $`N = 0`$ のとき：最後の列を消す。$`s[N] = (s_0, \ldots, s_{x-1})`$ である（Lean では山の最後の列を `pop` する）。

**場合 2.** それ以外のとき：次の手順である（`expandDiagram`）。

1. **根.** $`s`$ の山で、列 $`x`$ の一番上の辺の父を **根** $`r`$ と呼ぶ。根の列を $`c_r`$ とする。幅を $`w = x - c_r`$ とする。
2. **減一.** $`s' = (s_0, \ldots, s_{x-1}, s_x - 1)`$ の山 $`M(s')`$ を作る。
3. **境界の行.** 列 $`x`$ の一番上の節点の行と、根の列の節点のうち根とそれより下のもの（phantom を除く）の行を、上から並べる（`boundaries`）。
4. **marker.** $`M(s')`$ の節点で、根の列より右にあり、次の条件を満たすものを **marker** と呼ぶ（`markers`）。根の列の節点 $`z`$（根か、それより下の節点。phantom も含む）と同じ行にあり、**弱い父** をたどって $`z`$ に着く。節点 $`u`$ の弱い父とは、$`u`$ から上への辺の父 $`\pi`$ で、$`\mathrm{row}(\pi) = \mathrm{row}(u)`$ のものである（`weakParent`）。
5. **ブロック.** $`b = 1, \ldots, N`$ の順に、列 $`y = c_r + 1, \ldots, x`$ を列 $`y + b w`$ へ写す（`copyBlock`、`copyColumn`）。
6. **切る.** 最後の列（ブロック $`N`$ での列 $`x`$ の写し）を消す。各列の最下の節点の値を読む（`valuesOf`）。

$`s[N]`$ の長さは $`x + N w`$ である。

**列の写し方（`copyColumn`）.** ブロック $`b`$ で列 $`y`$ を写すとき、$`y`$ の marker $`\mu`$ ごとに、次の 3 種類の節点を置く。

- **平行移動**（`copyEdge`）：行 $`\mathrm{row}(\mu)`$ に節点を置く。左の脚は、$`\mu`$ の左の脚が根の列より左にあればそれと同じ節点、そうでなければ「その列 $`+ b w`$」の列で、行が $`\mathrm{row}(\mu)`$ より小さい最も高い節点である。phantom の marker は phantom に写す。
- **輪郭**（`contour`）：参照の行 $`g`$ を決める。今の最後の列（ブロック $`b-1`$ での列 $`x`$ の写し、$`b = 1`$ では $`M(s')`$ の列 $`x`$）で、各境界の行より真に下の最も高い節点を取る（`below`）。そのうち行が $`\mathrm{row}(\mu)`$ 以上の最後のものの行が $`g`$ である（`referenceAt`）。次に、$`\mu`$ から上へ源の辺を順に写す。辺の上端が別の marker なら、その辺の手前で止める。列の頂上に着いたら止める。次数 $`d`$ の源の辺は、今の行 $`t`$ から行 $`t + \omega^d`$ への辺になる。最初の $`t`$ は $`g`$ である。左の脚は、平行移動と同じ規則で、源の辺の父を写したものである。
- **充填**（`fill`、weak magma）：$`\mu`$ から上への源の辺の父を $`p`$ とする。列 $`\mathrm{col}(p) + b w`$ の節点 $`q`$ で $`\mathrm{row}(\mu) \le \mathrm{row}(q) \lt g`$ のものすべてについて、$`q`$ の真上の節点を $`q^+`$ とし、行 $`\mathrm{row}(q) + \omega^j`$（$`j = \mathrm{jump}(\mathrm{row}(q), \mathrm{row}(q^+)) - 1, \ldots, 0`$）に節点を置く。左の脚はどれも $`q`$ である。

最後に節点を行の順に並べる（`finish`）。一番上の節点の値を 1 とし、上から下へ $`\mathrm{value}(u) = \mathrm{value}(u^+) + \mathrm{value}(\pi)`$（$`\pi`$ は $`u^+`$ の左の脚）で値を決める（`backfill`）。

**例（$`(1, 3, 3)[2]`$）.** 結果は $`(1, 3, 2, 5, 4, 9)`$ である。

- 根は $`(0, 1)`$ で、$`c_r = 0`$、$`w = 2`$ である。$`s' = (1, 3, 2)`$ である。$`M(s')`$ の列 2 は、行 1 に値 2、行 2 に値 $`1 \leftarrow (0, 1)`$ を持つ。
- 境界の行は $`(\omega, 1)`$ である。marker は、列 1 と列 2 のそれぞれで、行 1 の節点と phantom である（`#eval` で確かめた）。
- ブロック 1 の参照：$`M(s')`$ の列 2 で、行 $`\omega`$ より下の最も高い節点は行 2、行 1 より下の最も高い節点は phantom（行 0）である。

ブロック 1 で列 1 を列 3 へ写す。

| 節点 | 種類 | 理由 |
|---|---|---|
| 行 1 | 平行移動 | marker $`(1, 1)`$。左の脚は列 2 の phantom |
| 行 2、左の脚 $`(2, 1)`$ | 充填 | 源の辺 $`(1,1) \to (1,2)`$ の父は $`(0, 1)`$。列 $`0 + 2 = 2`$ の $`q = (2, 1)`$ は $`1 \le 1 \lt g = 2`$。$`\mathrm{jump}(1, 2) = 1`$ なので行 $`1 + \omega^0 = 2`$ |
| 行 3、左の脚 $`(2, 2)`$ | 輪郭 | 源の辺 $`(1,1) \to (1,2)`$ は次数 0。$`g + \omega^0 = 3`$ |
| 行 $`\omega`$、左の脚 $`(2, 2)`$ | 輪郭 | 源の辺 $`(1,2) \to (1,\omega)`$ は次数 1。$`3 + \omega = \omega`$ |

値は上から $`1`$、$`1 + \mathrm{value}(2,2) = 2`$、$`2 + \mathrm{value}(2,2) = 3`$、$`3 + \mathrm{value}(2,1) = 5`$ である。よって列 3 の値は 5 である。同じようにして列 4（列 2 の写し）の値は 4 になる。ブロック 2 で列 5、6 ができ、列 6 を切る。

`expandDiagram [1,3,3] 2` の列 3〜5 は次のとおりである。

| 行 | 列 3 | 列 4 | 列 5 |
|---|---|---|---|
| $`\omega`$ | $`1 \leftarrow (2, 2)`$ | | $`1 \leftarrow (4, 3)`$ |
| $`4`$ | | | $`2 \leftarrow (4, 3)`$ |
| $`3`$ | $`2 \leftarrow (2, 2)`$ | $`1 \leftarrow (2, 2)`$ | $`3 \leftarrow (4, 2)`$ |
| $`2`$ | $`3 \leftarrow (2, 1)`$ | $`2 \leftarrow (2, 1)`$ | $`5 \leftarrow (4, 1)`$ |
| $`1`$ | $`5`$ | $`4`$ | $`9`$ |

列 5 はブロック 2 での列 1 の写しである。源の父 $`(0, 1)`$ は列 $`0 + 2 \cdot 2 = 4`$ へ写る。ブロック 2 の参照は列 4 から取る。境界の行 $`\omega`$ より下で最も高い列 4 の節点は行 3 にある。したがって $`g = 3`$ で、列 5 の輪郭は行 $`3 + 1 = 4`$ から始まる。充填は列 4 の行 1 と行 2 の節点を父にして、行 2 と行 3 に節点を置く。列 5 には列 3 より 1 つ多い節点がある。

## 5. weak magma と公式の ω-Y

公式の ω-Y は、Naruyoko 氏のプログラムの `expand` で定義される（[notes/00-survey.md](../notes/00-survey.md) §1.2）。weak-magma ω-Y はそれと一致しない。標準形 3001 個の 9003 回の展開のうち、480 回で結果が違う（notes/00-survey.md §1.6）。

[notes/02-feasibility.md](../notes/02-feasibility.md) §2 によると、違うのは充填の規則だけである。

- weak：すき間の節点の左の脚は、みな 1 本の列 $`\mathrm{col}(p) + b w`$ にある。$`p`$ は $`\mu`$ から上への源の辺の父である。
- 公式：すき間は、根と同じ段の行の横のつながりを写す。左の脚は、その行での左の脚の列の像にある。最下の行では、ひとつ左の列である。

**例.** $`(1, 3, 3)[2]`$ の列 4 の行 2 の節点（すき間）の左の脚は、weak では $`(2, 1)`$（値 2）、公式では $`(3, 1)`$（値 5）である。列 4 の最下の値は、weak では $`2 + 2 = 4`$、公式では $`2 + 5 = 7`$ である。全体は weak $`(1, 3, 2, 5, 4, 9)`$、公式 $`(1, 3, 2, 5, 7, 12)`$ である（公式の値は notes/02-feasibility.md §2.3 のもので、Lean では計算していない）。

notes/02-feasibility.md は最下の行を 0 と数える。Lean の行 $`1 + \delta`$ を $`\delta`$ と書く。例えば同ノートの「$`1 \leftarrow c_2@0`$」は、このノートの「行 2、左の脚 $`(2, 1)`$」である。

公式の ω-Y の停止性は、このリポジトリの定理ではない。公式の ω-Y は [koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por) で扱う。

**「no extraction」について.** Phyrion 氏はこの変種を「weak magma、no extraction」と呼ぶ。Lean の定義には、1-Y の層の抜き出しに当たる段が無く、行が順序数の 1 つの山だけを使う（notes/00-survey.md §3.5 の表）。ω-Y での提取（extraction）の正確な意味は、確かめていない（notes/00-survey.md §1.5）。

## 6. 展開の例

どれも `#eval Expansion.expand s N` の値である。

| 式 $`s`$ | $`N`$ | $`s[N]`$ |
|---|---|---|
| $`(1, 2)`$ | 3 | $`(1, 1, 1, 1)`$ |
| $`(1, 2, 2)`$ | 2 | $`(1, 2, 1, 2, 1, 2)`$ |
| $`(1, 2, 3)`$ | 2 | $`(1, 2, 2, 2)`$ |
| $`(1, 2, 4)`$ | 2 | $`(1, 2, 3, 4)`$ |
| $`(1, 3)`$ | 2 | $`(1, 2, 4)`$ |
| $`(1, 3)`$ | 3 | $`(1, 2, 4, 8)`$ |
| $`(1, 3, 3)`$ | 0 | $`(1, 3)`$ |
| $`(1, 3, 3)`$ | 1 | $`(1, 3, 2, 5)`$ |
| $`(1, 3, 3)`$ | 2 | $`(1, 3, 2, 5, 4, 9)`$ |
| $`(1, 3, 3)`$ | 3 | $`(1, 3, 2, 5, 4, 9, 8, 17)`$ |
| $`(1, 3, 4)`$ | 2 | $`(1, 3, 3, 3)`$ |
| $`(1, 4)`$ | 1 | $`(1, 3)`$ |
| $`(1, 4)`$ | 2 | $`(1, 3, 10)`$ |
| $`(1, 4)`$ | 3 | $`(1, 3, 10, 37)`$ |
| $`(1, 4, 4)`$ | 2 | $`(1, 4, 3, 11, 10, 38)`$ |

## 7. 1 段の展開と最終定理

**定義（1 段の展開）.** $`t \prec s`$（`Dynamics.Step t s`）は、$`s \ne ()`$ かつ、ある $`N`$ で $`t = s[N]`$ であることである。

- `Dynamics.next s N` は、展開のプログラムが成功した結果である。どの合法な式でも成功する（`expand_total`）。
- 1 段の展開は辞書式順序を真に下げる（`Dynamics.next_lex`）。
- 山の行の係数が指数 $`D`$ より上でみな 0 なら、展開したあとの山も同じである（`expandDiagram_key_dimension`、`Dynamics.next_key_dimension`）。したがって $`D`$ は始めの式ごとに 1 つ選べば、その子孫すべてで使える（`Dynamics.fixed_dimension_for_descendants`）。$`D`$ は [06](06-combinatorial-layer.md) の鍵の長さ $`D + 1`$ を決める。

最終定理（[OmegaY/Expansion/WellFounded.lean](../OmegaY/Expansion/WellFounded.lean)、名前空間 `OmegaY.Expansion`）は次のとおりである。

1. `omegaY_step_wellFounded`：$`\prec`$ は整礎である。
2. `omegaY_generated_isWellOrder`：種から生成される式の集合は、辞書式順序で整列する。
3. `omegaY_descendants_isWellOrder`：どの式でも、そこから届く式の集合は、辞書式順序で整列する。
4. `omegaY_trajectory_terminates`：コピーの回数の列をどう選んでも、展開を続けると空の式に着く。

2〜4 は 1 から組合せの議論だけで出る（`Dynamics.generated_isWellOrder`、`Dynamics.every_legal_root_isWellOrder`、`omegaY_no_infinite_step_chain`）。1 の証明が [06](06-combinatorial-layer.md) 以降の話題である。

## 8. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md)「対象：weak-magma ω-Y」 | 対象の展開と、公式の ω-Y との違い |
| [README](../README.md)「記号」「最終定理 4 つ」 | 式、$`s[N]`$、$`\prec`$、4 つの定理 |
| [notes/00-survey.md](../notes/00-survey.md) §1.3〜§1.6 | 山の形、展開、変種、公式との比較 |
| [notes/02-feasibility.md](../notes/02-feasibility.md) §1.1、§2 | 記法と、充填の規則の違い |
| [OmegaY/Rows.lean](../OmegaY/Rows.lean)、[OmegaY/Canonical/Build.lean](../OmegaY/Canonical/Build.lean)、[OmegaY/Expansion/Build.lean](../OmegaY/Expansion/Build.lean) | §2〜§4 の定義 |

## 9. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| 合法な式、式 | `Canonical.Legal`、`Dynamics.Expr` | [OmegaY/Canonical/Totality.lean](../OmegaY/Canonical/Totality.lean)、[OmegaY/Expansion/LegalDynamics.lean](../OmegaY/Expansion/LegalDynamics.lean) |
| 種、辞書式順序 | `Dynamics.seed`、`Dynamics.Lex` | [OmegaY/Expansion/LegalDynamics.lean](../OmegaY/Expansion/LegalDynamics.lean) |
| 行、跳び、冪を足す、次の行 | `Row`、`Row.jump`、`Row.bump`、`Row.B` | [OmegaY/Rows.lean](../OmegaY/Rows.lean) |
| 節点、山 | `Canonical.Cell`、`Canonical.Ref`、`Canonical.Mountain`、`Canonical.phantom` | [OmegaY/Canonical/Build.lean](../OmegaY/Canonical/Build.lean) |
| 父の探索 | `climb`、`nextCandidate`、`findParent` | 同上 |
| 山の構成 | `growColumn`、`buildColumn`、`build` | 同上 |
| 展開 | `expandDiagram`、`expand`、`valuesOf` | [OmegaY/Expansion/Build.lean](../OmegaY/Expansion/Build.lean) |
| marker | `weakParent`、`weakReaches`、`markers` | 同上 |
| 列の写し | `copyEdge`、`contour`、`fill`、`below`、`referenceAt`、`copyColumn`、`copyBlock` | 同上 |
| 値の復元 | `finish`、`backfill` | 同上 |
| 1 段の展開 | `Dynamics.next`、`Dynamics.Step`、`Dynamics.next_lex` | [OmegaY/Expansion/LegalDynamics.lean](../OmegaY/Expansion/LegalDynamics.lean) |
| 次元の保存 | `expandDiagram_key_dimension`、`Dynamics.next_key_dimension`、`Dynamics.fixed_dimension_for_descendants` | [OmegaY/Expansion/SupportedDimension.lean](../OmegaY/Expansion/SupportedDimension.lean)、[OmegaY/Expansion/DynamicsRowBound.lean](../OmegaY/Expansion/DynamicsRowBound.lean) |
| 最終定理 | `omegaY_step_wellFounded` など | [OmegaY/Expansion/WellFounded.lean](../OmegaY/Expansion/WellFounded.lean) |
