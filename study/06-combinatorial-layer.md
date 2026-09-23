[← Back](README.md) | [English](en/06-combinatorial-layer.md) | [Japanese](06-combinatorial-layer.md)

# Phyrion 氏の ω-Y の組合せの層

前提

| ノート | ここで使う言葉 |
|---|---|
| [02 整礎関係と整礎再帰](02-well-founded.md) | 鍵 $`\mathrm{Key}_m`$、ラベルの上界による停止（§6） |
| [05 ω-Y 数列と山](05-omegay-mountain.md) | 式、行、跳び、辺、父、次数、根、ブロック、展開 |

このノートは、Phyrion 氏の証明のうち、ラベルの意味を使わない部分（組合せの層）を説明する。この層は、ラベルの関係 $`R`$ についての 3 つの定理だけを使って、展開の整礎性を示す。このリポジトリは、この層を変えずに使う（[NOTICE](../NOTICE)）。層の大部分は `OmegaY/` の 549 モジュールにあり、ここではその入口と出口だけを説明する。

## 1. 鍵と型板

**定義（鍵の構文 `KeySyntax`）.** 鍵の構文は次の 3 つの組である（[OmegaY/Reflection/Interface.lean](../OmegaY/Reflection/Interface.lean)）。

- `Template n`：$`n`$ 個の頂点の上の **型板** の型。
- `eval t f`：型板 $`t`$ を頂点のラベル $`f : \mathrm{Fin}\ n \to \mathrm{Label}`$ で評価した鍵。
- `monotone_eval`：各点で $`g \le f`$ なら $`\mathrm{eval}\ t\ g \le \mathrm{eval}\ t\ f`$。

**ω-Y の型板（`OmegaY.Keys`）.** 長さ $`m`$ の鍵の型板は、各座標に頂点の番号か $`\top`$ を置いたものである。

```math
\mathrm{Template}_{m,n} = \mathrm{Fin}\ m \to \mathrm{Option}(\mathrm{Fin}\ n), \qquad (\mathrm{eval}\ t\ f)_i = \begin{cases} \top & (t_i = \mathrm{none}) \cr f(j) & (t_i = \mathrm{some}\ j) \end{cases}
```

鍵の構文としては `KeyReflection.vectorSyntax m` で、`Model.keySyntax m` はその別名である。

**例.** $`m = 2`$、$`n = 3`$ とする。$`t = (\mathrm{some}\ 0, \mathrm{none})`$ なら $`\mathrm{eval}\ t\ f = (f(0), \top)`$、$`t' = (\mathrm{some}\ 0, \mathrm{some}\ 2)`$ なら $`\mathrm{eval}\ t'\ f = (f(0), f(2))`$ である。

| 名前 | 内容 |
|---|---|
| `Keys.eval_mono` | 各点で $`g \le f`$ なら $`\mathrm{eval}\ t\ g \le \mathrm{eval}\ t\ f`$ |
| `Keys.templateKey t` | $`\mathrm{eval}\ t\ \mathrm{id}`$。頂点の番号そのものをラベルとして評価した鍵 |
| `Keys.eval_lt_of_template_lt` | $`f`$ が狭義増加で、$`\mathrm{templateKey}\ t \lt \mathrm{templateKey}\ s`$ なら $`\mathrm{eval}\ t\ f \lt \mathrm{eval}\ s\ f`$ |
| `Keys.relabel t μ`、`Keys.eval_relabel` | 頂点を $`\mu`$ で付け替えた型板。$`\mathrm{eval}(\mathrm{relabel}\ t\ \mu)\ h = \mathrm{eval}\ t\ (h \circ \mu)`$ |
| `Keys.shared_root_before_infinity` | $`(a, a) \lt (a, \top)`$ |

`eval_lt_of_template_lt` があるので、鍵の比べ方は列の番号の比べ方で決まる。ラベルを選ぶ前に、組合せだけで比べられる。

## 2. 内部の原子と上端の原子

**定義（原子）.** 型板 $`t`$ を持つ次の 2 種類を使う（[OmegaY/Reflection/Interface.lean](../OmegaY/Reflection/Interface.lean)）。

| Lean | 成分 | 成り立つこと（ラベル $`f`$） |
|---|---|---|
| `InternalAtom S n` | 型板、親 $`p`$、子 $`q`$、$`p \lt q`$ | $`R(\mathrm{eval}\ t\ f,\ f(p),\ f(q))`$ |
| `TopAtom S n` | 型板、親 $`p`$ | 上端 $`b`$ について $`R(\mathrm{eval}\ t\ f,\ f(p),\ b)`$ |

上端の原子は、図式の外にある点 $`b`$ への辺である。**要求** とも呼ぶ。

| Lean | 意味 |
|---|---|
| `InternalHolds S R G f` | $`G`$ の内部の原子がすべて $`f`$ で成り立つ |
| `TopHolds S R N f b` | $`N`$ の上端の原子がすべて上端 $`b`$ について成り立つ |
| `KeysBelow S N f θ` | $`N`$ の原子の鍵がすべて $`\theta`$ より小さい |
| `Bounded f b` | すべての $`i`$ で $`f(i) \lt b`$ |

## 3. 尺度の根と、山の辺の鍵

山の辺に鍵の型板を付ける（[OmegaY/Geometry/MountainKeys.lean](../OmegaY/Geometry/MountainKeys.lean)）。

**定義（辺）.** `RealStoredEdge` は、phantom でない節点 `lower`、その真上の節点 `upper`、`upper` の左の脚 `parent` の組である（[05](05-omegay-mountain.md) §3 の辺）。**次数** は $`d = \mathrm{jump}(\mathrm{row}(\mathrm{lower}), \mathrm{row}(\mathrm{parent}))`$ である（`degree`）。

**定義（尺度の根）.** 節点 $`u`$ の **尺度 $`k`$ の父** は、$`u`$ から上への辺の父で、その辺の次数が $`k`$ 以下のものである（`scaleParent`）。尺度 $`k`$ の父を無くなるまでたどった節点を **尺度 $`k`$ の根** $`\rho_k(u)`$ と呼ぶ（`scaleRoot`）。尺度が大きいほど、たどれる辺が多いので、根は同じ列か、より左の列にある（`scaleRoot_scale_antitone`）。

**定義（次元）.** 山のすべての行で、指数 $`D`$ より上の係数が 0 のとき、$`D`$ を山の **次元** と呼ぶ（`MountainKeyDimension`）。有限の山には次元がある（`exists_key_dimension`）。辺の次数は $`D`$ 以下である（`degree_le`）。

**定義（辺の鍵 `keyTemplate`）.** 次元 $`D`$ の山の辺 $`e`$（父 $`\pi`$、次数 $`d`$）の型板は、長さ $`m = D + 1`$ で、座標 $`i`$ は尺度 $`D - i`$ に当たる。

```math
\kappa_D(e) = \bigl(\mathrm{col}\,\rho_D(\pi),\ \mathrm{col}\,\rho_{D-1}(\pi),\ \ldots,\ \mathrm{col}\,\rho_d(\pi),\ \underbrace{\top, \ldots, \top}_{d}\bigr)
```

有限の座標は $`D + 1 - d`$ 個で、どれも父の列以下の列を指す（`keyTemplate_column_bound`）。子の列は指さない。

**例.** 次の値は、`keyTemplate` と `scaleRoot` の定義をそのままたどる小さい関数を書き、`#eval` で確かめた。$`f_j`$ は列 $`j`$ のラベルである。

| 式 | $`D`$ | 辺（列、行） | 父 | 次数 | 鍵 |
|---|---|---|---|---|---|
| $`(1, 3)`$ | 1 | 列 1、$`1 \to 2`$ | $`(0, 1)`$ | 0 | $`(f_0, f_0)`$ |
| | | 列 1、$`2 \to \omega`$ | $`(0, 1)`$ | 1 | $`(f_0, \top)`$ |
| $`(1, 4)`$ | 2 | 列 1、$`1 \to 2`$ | $`(0, 1)`$ | 0 | $`(f_0, f_0, f_0)`$ |
| | | 列 1、$`2 \to \omega`$ | $`(0, 1)`$ | 1 | $`(f_0, f_0, \top)`$ |
| | | 列 1、$`\omega \to \omega^2`$ | $`(0, 1)`$ | 2 | $`(f_0, \top, \top)`$ |
| $`(1, 3, 5)`$ | 1 | 列 2、$`1 \to 2`$ | $`(1, 1)`$ | 0 | $`(f_0, f_0)`$ |
| | | 列 2、$`2 \to \omega`$ | $`(0, 1)`$ | 1 | $`(f_0, \top)`$ |

$`(1, 3, 5)`$ の列 2 の最初の辺は、父が列 1 にあるのに、鍵は列 0 を指す。父 $`(1, 1)`$ から上への辺は次数 0 で、その父は $`(0, 1)`$ だからである。鍵は父ではなく、父の根を指す。

**定理（`key_strict_in_column`）.** 同じ列の 2 つの辺で、下の辺の鍵は上の辺の鍵より真に小さい（ラベルが狭義増加のとき）。上の表の各列でも、鍵は上へ行くほど大きい。

## 4. 表現

**定義（表現 `KeyRepresentation hF D`）.** 山（`Frame`）の **表現** は、列のラベル $`f : \mathrm{Fin}\ \mathit{width} \to \mathrm{Label}`$ で、次を満たすものである（[OmegaY/Geometry/RepresentedMountain.lean](../OmegaY/Geometry/RepresentedMountain.lean)）。

1. $`f`$ は狭義増加（`strictMono`）。
2. どの $`f(i)`$ も $`\omega_1`$ より小さい（`bounded`）。
3. どの辺 $`e`$ でも $`R_{D+1}(\mathrm{eval}\ \kappa_D(e)\ f,\ f(\mathrm{col}\,\pi),\ f(\mathrm{col}\,\mathrm{lower}))`$（`edges`）。

$`R_{D+1}`$ は長さ $`D + 1`$ の鍵の関係 `Model.R (D + 1)` である。

**例.** $`(1, 3, 5)`$ の表現は、$`f_0 \lt f_1 \lt f_2 \lt \omega_1`$ で次を満たすものである。

```math
R((f_0, f_0), f_0, f_1), \quad R((f_0, \top), f_0, f_1), \quad R((f_0, f_0), f_1, f_2), \quad R((f_0, \top), f_0, f_2)
```

| 名前 | 内容 |
|---|---|
| `keyRepresentation_exists` | どの山にも表現がある（`initial_finite_graph` から。§5） |
| `KeyRepresentation.restrict` | 列の接頭辞に制限しても表現である |
| `KeyRepresentation.lastLabel` | 最後の列のラベル |
| `restrict_below_last` | 真の接頭辞に制限した表現のラベルは、どれも元の最後のラベルより小さい |

## 5. 3 つの定理

組合せの層が意味の層から使うのは、次の 3 つの定理だけである（[notes/01-design.md](../notes/01-design.md) §1）。$`R`$ は `Reflection.R S`、$`\mathrm{top}`$ は $`\omega_1`$ である。

**定理（`key_weaken`）.** $`\theta \le \Theta`$ かつ $`R(\Theta, a, b)`$ なら $`R(\theta, a, b)`$。

**定理（`finite_reflection`）.** 次を仮定する。

1. $`f : \mathrm{Fin}\ n \to \mathrm{Label}`$ は狭義増加で、$`f \lt b`$（`Bounded f b`）。
2. $`G`$ の内部の原子が $`f`$ で成り立つ。
3. $`N`$ の上端の原子の鍵がどれも $`\theta`$ より小さく、$`N`$ が上端 $`b`$ について成り立つ。
4. 切れ目 $`\mathrm{cut}`$ について $`R(\theta, f(\mathrm{cut}), b)`$（**制御関係**）。

このとき、次を満たす $`g`$ がある。

1. $`g`$ は狭義増加で、$`g \lt f(\mathrm{cut})`$。
2. $`i \lt \mathrm{cut}`$ なら $`g(i) = f(i)`$。
3. 各点で $`g \le f`$。
4. $`G`$ が $`g`$ で成り立ち、$`N`$ が上端 $`f(\mathrm{cut})`$ について成り立つ。

鍵が名指す列は、切れ目より前でなくてよい。

**定理（`initial_finite_graph`）.** どの有限の $`G`$ と $`N`$ にも、ある $`\beta \lt \omega_1`$ と狭義増加の $`f \lt \beta`$ があって、$`G`$ が $`f`$ で成り立ち、$`N`$ が上端 $`\beta`$ について成り立つ。

## 6. 1 ブロックの継ぎ合わせ

有限反映 1 回で、列を 1 ブロック増やす（[OmegaY/Splice.lean](../OmegaY/Splice.lean)）。列の数を $`n`$、切れ目を $`\mathrm{cut}`$ とする。

**定義（列の写像）.** 新しい列の数は $`n + (n - \mathrm{cut})`$ である（`Splice.width`）。

| Lean | 写像 |
|---|---|
| `old i` | $`i \mapsto i`$ |
| `moved i` | $`i \lt \mathrm{cut}`$ なら $`i`$、そうでなければ $`n + (i - \mathrm{cut})`$ |
| `boundary` | 列 $`n`$（$`= \mathrm{moved}(\mathrm{cut})`$） |

**定義（新しいラベル `labels cut f g`）.** 列 $`i \lt n`$ には $`g(i)`$、列 $`i \ge n`$ には $`f(\mathrm{cut} + i - n)`$ を付ける。つまり、古い列 $`\mathrm{cut}, \ldots, n - 1`$ のラベルが右端にそのまま並ぶ。

**例.** $`n = 4`$、$`\mathrm{cut} = 1`$ なら、新しいラベルは次のとおりである。

```math
(g_0, g_1, g_2, g_3, f_1, f_2, f_3), \qquad g_0 = f_0,\quad g_1, g_2, g_3 \lt f_1
```

**定理（`reflected_block`）.** §5 の有限反映の仮定の下で、反映で得た $`g`$ について、`labels cut f g` は狭義増加で $`b`$ より小さい。$`G`$ の原子を `old` で写したものは、新しいラベルで成り立つ（`old` の列のラベルは $`g`$ だから）。`moved` で写したものも、新しいラベルで成り立つ（`moved` の列のラベルは $`f`$ だから）。

**定義（分類 `Classified`）.** 新しい図式の原子 $`e`$ は、次のどれかである。

1. $`G`$ の原子を `old` で写したもの。
2. 端点が $`G`$ の原子 $`s`$ を `moved` で写したものと同じで、型板の鍵が $`s`$ を写した型板の鍵以下のもの（鍵を弱めた写し）。
3. 要求 $`d \in N`$ から作った `seamAtom`：親は `old` $`d`$ の親、子は `boundary`。

**定理（`classified_graph_represented`）.** 新しい図式がすべて分類されるなら、新しいラベルで全体が成り立つ。1 は反映から、2 は `key_weaken`（`holds_weakened_copy`）から、3 は要求が上端 $`f(\mathrm{cut})`$ について成り立つことと、`boundary` のラベルが $`f(\mathrm{cut})`$ であることから出る（`holds_seam`）。

## 7. 予備を持つ反映のくり返し

展開では、ブロックを $`N`$ 回くり返し増やす。そのために、次の反映に要る事実を **予備** として持ち運ぶ（[OmegaY/Splice/Reservoirs.lean](../OmegaY/Splice/Reservoirs.lean)、[OmegaY/Splice/IteratedReservoirs.lean](../OmegaY/Splice/IteratedReservoirs.lean)）。

**定義（`ReservoirState G F T control f β`）.** 次の 6 つが成り立つことである。

| 成分 | 内容 |
|---|---|
| `strict`、`bounded` | $`f`$ は狭義増加で、$`f \lt \beta`$ |
| `graph` | 今の図式 $`G`$ が成り立つ |
| `internal` | 内部の予備 $`F`$ が成り立つ |
| `virtual` | 上端の予備 $`T`$ が上端 $`\beta`$ について成り立つ |
| `controlled` | $`R(\mathrm{eval}\ \kappa_c\ f,\ f(\mathrm{control.parent}),\ \beta)`$ |

**定理（`splice_reservoirs`）.** 次を仮定する。状態 `ReservoirState G F T control f β`。要求 $`N`$ の各原子に、親が同じで型板の鍵が以上の $`T`$ の原子がある（`DemandCovered`）。要求の型板の鍵は、制御の型板の鍵より真に小さい。新しい図式 $`H`$ の原子は `ReservoirClassified` である（§6 の 3 種類で、2 は $`F`$ から、3 は鍵を弱めた要求）。このとき、切れ目を `control.parent` とする有限反映 1 回で、$`H`$、`moved` で写した $`F`$、$`T`$、`control` について、同じ $`\beta`$ の状態が得られる。

反映には $`G`$ と $`F`$ をまとめて渡す。要求の鍵が制御の鍵より小さいことが、有限反映の `KeysBelow` になる。

**定義（ブロックの番号）.** 始めの列の数を $`x`$、根の列を $`y`$ とする。

| Lean | 値 |
|---|---|
| `blockWidth x y b` | $`x + b(x - y)`$ |
| `blockCut b` | $`y + b(x - y)`$ |
| `blockSource b i` | $`i \lt y`$ なら $`i`$、そうでなければ $`i + b(x - y)`$ |

**定理（`iterated_reservoirs`）.** ブロック 0 の状態があり、各ブロックで要求が上端の予備で覆われ、要求の鍵が制御の鍵より小さく、次のブロックの図式が分類されるなら、すべての $`b`$ でブロック $`b`$ の状態がある。$`\beta`$ は変わらない。ブロック $`b`$ の切れ目は `blockCut b` である。

## 8. 末尾のラベルによる降下

**定理（`ActualRepresentationDescent`、`actual_representation_descent`）.** 合法な空でない式 $`s`$ の山の表現 $`f`$（次元 $`D`$）と、どの $`N`$ についても、$`s[N]`$ の山の表現 $`f'`$（次元 $`D`$）で、すべてのラベルが $`f(x)`$ より小さいものがある。

**場合 1（最後の列を消すとき）.** $`f`$ を接頭辞に制限する（`expandDiagram_trivial_representation_descent`）。ラベルはどれも $`f(x)`$ より小さい（`restrict_below_last`）。

**場合 2（ブロックを写すとき）.** 記号を次のとおりとする（`RootGeometry`、[OmegaY/Expansion/InitialControlKeys.lean](../OmegaY/Expansion/InitialControlKeys.lean)）。

- **制御の辺**：列 $`x`$ の一番上の辺（`controlEdge`）。父は根 $`r`$ である。
- **下の辺**：列 $`x`$ の、制御の辺より下の辺（`LowerEdge`）。鍵は制御の辺の鍵より真に小さい（`lower_key_strict`、§3 の `key_strict_in_column` から）。
- $`\beta = f(x)`$。

ブロック 0 の状態は、古いラベル $`f(0), \ldots, f(x - 1)`$ で作る（[OmegaY/Expansion/ActualInitialReservoir.lean](../OmegaY/Expansion/ActualInitialReservoir.lean)）。

| 成分 | 中身 |
|---|---|
| $`G_0`$ | 列 $`x`$ を除いた山の辺 |
| $`F`$ | 同じ辺（`initialSpliceFacts`）。ブロックごとに `blockSource` で写す |
| $`T`$ | 下の辺を、列 $`x`$ を上端 $`\beta`$ とみなした上端の原子（`initialSpliceVirtualFacts`） |
| 制御 | 制御の辺を同じようにみなした上端の原子（`initialSpliceControl`）。親は根の列 |

どれも古い表現 $`f`$ の辺の関係そのものなので、反映を使わずに成り立つ。

次に、ブロック $`b`$ から $`b + 1`$ へ §7 の `splice_reservoirs` を使う（`iterated_actual_reservoirs`）。そのとき要るのは、ブロック $`b+1`$ の山のすべての辺が `ReservoirClassified` であることである（`actual_splice_edge_classified`）。これは展開のプログラムの形についての有限の事実で、weak magma の充填の規則を使う。複写の辺の鍵の上界と、充填の辺の分類が、その中心である（[notes/02-feasibility.md](../notes/02-feasibility.md) §3.1、§4.2）。

ブロック $`N`$ の状態のラベルは、$`s[N]`$ の山の表現である（`representationOfSpliceGraph`）。どれも $`\beta = f(x)`$ より小さい（`represent_actual_expansion`）。

**例（$`(1, 3, 3)`$）.** $`x = 2`$、根の列は 0 である。制御の辺は列 2 の辺 $`2 \to \omega`$ で、鍵は $`(f_0, \top)`$ である。下の辺は列 2 の辺 $`1 \to 2`$ で、鍵は $`(f_0, f_0)`$ である。$`\beta = f_2`$ である。

- ブロック 0：ラベル $`(f_0, f_1)`$。制御関係は $`R((f_0, \top), f_0, f_2)`$、上端の予備は $`R((f_0, f_0), f_0, f_2)`$ である。
- ブロック 0 → 1：切れ目は $`0`$ である。反映で $`g_0 \lt g_1 \lt f_0`$ を得る。新しいラベルは $`(g_0, g_1, f_0, f_1)`$ である。
- ブロック 1 → 2：切れ目は $`2`$ で、ラベルは $`f_0`$ である。反映で $`g'_2 \lt g'_3 \lt f_0`$ を得る。列 0、1 は動かない。新しいラベルは $`(g_0, g_1, g'_2, g'_3, f_0, f_1)`$ である。

これが $`(1, 3, 3)[2] = (1, 3, 2, 5, 4, 9)`$ の表現で、どのラベルも $`f_2`$ より小さい。どの辺がどの種類に分類されるかは、Lean の `actual_splice_edge_classified` が示す。

**整礎性.** $`D`$ は子孫で変わらない（[05](05-omegay-mountain.md) §7）。上の定理と [02](02-well-founded.md) §6 の帰納法（`accessible_of_representation_below`）から、$`\prec`$ は整礎である（`step_wellFounded_of_actual_representation_descent`）。最初の表現は `keyRepresentation_exists` から得る。

## 9. 3 つの定理が使われる場所

`grep` で探した、コアの中の呼び出しである（薄いファイル `Reflection.lean`、`Reflection/`、`KeyReflection.lean`、`Model.lean` を除く）。

| 定理 | 呼び出す場所 |
|---|---|
| `key_weaken` | `Splice.holds_weakened_copy`（[OmegaY/Splice.lean](../OmegaY/Splice.lean)）、`DemandCovered.top_holds`、`holds_weakened_seam`（[OmegaY/Splice/Reservoirs.lean](../OmegaY/Splice/Reservoirs.lean)）、`ActualCopiedKeyBound.represented`（[OmegaY/Expansion/ActualCopiedKeyLabels.lean](../OmegaY/Expansion/ActualCopiedKeyLabels.lean)） |
| `finite_reflection` | `Splice.reflected_block`、`Splice.splice_reservoirs`、`RootGeometry.reflect_initial_control`（[OmegaY/Expansion/InitialControlKeys.lean](../OmegaY/Expansion/InitialControlKeys.lean)） |
| `initial_finite_graph` | `actual_keys_initially_represented`（[OmegaY/Geometry/MountainKeys.lean](../OmegaY/Geometry/MountainKeys.lean)）。要求のリストは空である |

## 10. 意味の層に残る仕事

組合せの層は、有限反映がなぜ成り立つかを問わない。§5 の 3 つの定理を満たす $`R`$ を与えるのが **意味の層** の仕事である。

- Phyrion 氏の意味の層：$`R(\theta, a, b)`$ は「$`b`$ より下の有限の正の図式を $`a`$ より下へ圧縮できる」ことである（[notes/00-survey.md](../notes/00-survey.md) §3.2）。このリポジトリには含めない。
- このリポジトリの意味の層：$`R`$ は [07 関係 R](07-relation-r.md) の $`\Sigma_1`$ 初等部分構造の関係である。証明は [09 3 つの定理の証明](09-obligations.md) にある。

## 11. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md)「証明の形」 | 二層の構成と、3 つの定理の表 |
| [notes/01-design.md](../notes/01-design.md) §1 | コアが意味の層から使う名前 |
| [notes/00-survey.md](../notes/00-survey.md) §3.2、§3.5 | 鍵、山の辺の鍵、次元の保存、1-Y との対応 |
| [notes/02-feasibility.md](../notes/02-feasibility.md) §3、§4 | 公式の ω-Y で、複写の辺の鍵の上界が破れること |
| [OmegaY/Reflection/Interface.lean](../OmegaY/Reflection/Interface.lean) | §1、§2 の定義（Phyrion 氏のものを変えずに移した） |

## 12. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| 鍵の構文 | `KeySyntax` | [OmegaY/Reflection/Interface.lean](../OmegaY/Reflection/Interface.lean) |
| 原子と成り立つこと | `InternalAtom`、`TopAtom`、`InternalHolds`、`TopHolds`、`KeysBelow`、`Bounded` | 同上 |
| ω-Y の鍵と型板 | `Keys.Key`、`Keys.Template`、`Keys.eval`、`Keys.eval_mono`、`Keys.templateKey`、`Keys.eval_lt_of_template_lt`、`Keys.relabel` | [OmegaY/Keys.lean](../OmegaY/Keys.lean) |
| 鍵の構文の実体 | `KeyReflection.vectorSyntax`、`Model.keySyntax`、`Model.R` | [OmegaY/KeyReflection.lean](../OmegaY/KeyReflection.lean)、[OmegaY/Model.lean](../OmegaY/Model.lean) |
| 尺度の根 | `scaleParent`、`scaleRoot`、`scaleRoot_scale_antitone` | [OmegaY/Geometry/MountainKeys.lean](../OmegaY/Geometry/MountainKeys.lean) |
| 辺とその鍵 | `RealStoredEdge`、`degree`、`keyTemplate`、`keyTemplate_column_bound`、`atom` | 同上 |
| 最初の表現の材料 | `actual_keys_initially_represented` | 同上 |
| 列の中の鍵の増加 | `key_strict_in_column` | [OmegaY/Geometry/VerticalEdgeKeys.lean](../OmegaY/Geometry/VerticalEdgeKeys.lean) |
| 表現 | `KeyRepresentation`、`keyRepresentation_exists`、`restrict`、`lastLabel` | [OmegaY/Geometry/RepresentedMountain.lean](../OmegaY/Geometry/RepresentedMountain.lean) |
| 1 ブロック | `Splice.width`、`old`、`moved`、`boundary`、`labels`、`reflected_block`、`Classified`、`classified_graph_represented` | [OmegaY/Splice.lean](../OmegaY/Splice.lean) |
| 予備 | `ReservoirState`、`DemandCovered`、`ReservoirClassified`、`splice_reservoirs` | [OmegaY/Splice/Reservoirs.lean](../OmegaY/Splice/Reservoirs.lean) |
| ブロックのくり返し | `blockWidth`、`blockCut`、`blockSource`、`iterated_reservoirs` | [OmegaY/Splice/BlockIndices.lean](../OmegaY/Splice/BlockIndices.lean)、[OmegaY/Splice/IteratedReservoirs.lean](../OmegaY/Splice/IteratedReservoirs.lean) |
| 制御の辺と下の辺 | `controlEdge`、`LowerEdge`、`controlAtom`、`lowerAtom`、`lower_key_strict` | [OmegaY/Expansion/InitialControlKeys.lean](../OmegaY/Expansion/InitialControlKeys.lean) |
| 実際のブロック | `iterated_actual_reservoirs`、`represent_actual_expansion` | [OmegaY/Expansion/ActualSpliceRepresentation.lean](../OmegaY/Expansion/ActualSpliceRepresentation.lean) |
| 実際の辺の分類 | `actual_splice_edge_classified` | [OmegaY/Expansion/ActualSpliceGeometry.lean](../OmegaY/Expansion/ActualSpliceGeometry.lean) |
| ブロック 0 の状態 | `zero_reservoir`、`initialSpliceFacts`、`initialSpliceVirtualFacts`、`initialSpliceControl` | [OmegaY/Expansion/ActualInitialReservoir.lean](../OmegaY/Expansion/ActualInitialReservoir.lean)、[OmegaY/Expansion/ActualSpliceFacts.lean](../OmegaY/Expansion/ActualSpliceFacts.lean) |
| 降下 | `ActualRepresentationDescent`、`actual_representation_descent` | [OmegaY/Expansion/DynamicsRepresentationRank.lean](../OmegaY/Expansion/DynamicsRepresentationRank.lean)、[OmegaY/Expansion/ActualRepresentationDescent.lean](../OmegaY/Expansion/ActualRepresentationDescent.lean) |
| 整礎性 | `accessible_of_representation_below`、`step_wellFounded_of_actual_representation_descent` | [OmegaY/Expansion/DynamicsRepresentationRank.lean](../OmegaY/Expansion/DynamicsRepresentationRank.lean) |
