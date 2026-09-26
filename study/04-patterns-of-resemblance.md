[← Back](README.md) | [English](en/04-patterns-of-resemblance.md) | [Japanese](04-patterns-of-resemblance.md)

# Patterns of resemblance

前提

| ノート | ここで使う言葉 |
|---|---|
| [01 順序数と ω₁](01-ordinals.md) | 順序数、極限順序数、$`\mathrm{Ord}`$、ラベル |
| [02 整礎関係と整礎再帰](02-well-founded.md) | 整礎再帰、引数、ガードつきの再帰、鍵 $`\mathrm{Key}_m`$、段、上端 |
| [03 構造と Σ₁ 初等部分構造](03-sigma1-elementary.md) | 構造 $`(\gamma; \ldots)`$、点、$`\Sigma_1`$ 論理式、$`\preccurlyeq_{\Sigma_1}`$、型板、$`\mathrm{eval}`$、上端述語（§7）、部分的な上端述語（§8） |

このノートは、Carlson の patterns of resemblance の考え方を説明する。次に、[bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) が BMS でそれをどう使ったかを述べる。最後に、ω-Y でそのままでは足りない理由と、このリポジトリの変更点を述べる。

## 1. 自分自身を言語に持つ関係

**定義（Carlson の ≤₁）.** 順序数の上の関係 $`\le_1`$ を次の式で定める。

```math
\alpha \le_1 \beta \iff \alpha \le \beta \ \land\ (\alpha; \le, \le_1) \preccurlyeq_{\Sigma_1} (\beta; \le, \le_1)
```

$`\alpha \lt_1 \beta`$ は $`\alpha \lt \beta \land \alpha \le_1 \beta`$ のことである。

**読み方.** 「$`\alpha`$ より下の順序数の形は、$`\beta`$ より下まで広げても、$`\Sigma_1`$ 論理式では見分けられない」。ここで形とは、大小関係と、関係 $`\le_1`$ 自身である。

右辺は左辺の $`\le_1`$ を使う。循環に見えるが、$`\beta`$ についての整礎再帰で定義できる。

- 構造 $`(\beta; \le, \le_1)`$ の領域は $`\{x \mid x \lt \beta\}`$ である。そこで読む $`\le_1`$ は、$`x, y \lt \beta`$ の $`x \le_1 y`$ だけである。
- $`x \le_1 y`$ の真偽は、引数 $`y \lt \beta`$ の段階で決まっている。
- 構造 $`(\alpha; \ldots)`$ も同じで、$`\alpha \le \beta`$ である。

Carlson はこれを $`\le_1, \ldots, \le_N`$（$`\Sigma_1, \ldots, \Sigma_N`$ の初等性）に広げた構造を調べた。

```math
\mathcal R_N = (\mathrm{Ord}; \le, \le_1, \ldots, \le_N)
```

- $`N \ge 1`$ は自然数である。
- $`\alpha \le_i \beta`$ は、$`\le_1`$ の定義の $`\preccurlyeq_{\Sigma_1}`$ を、$`\Sigma_i`$ 論理式での初等性に替えたものである。$`\Sigma_i`$ 論理式は、存在量化子のかたまりから始めて、存在量化子と全称量化子のかたまりを交互に $`i`$ 個並べ、その後ろに量化子の無い論理式を置いたものである。

文献：T. J. Carlson, Elementary patterns of resemblance, Annals of Pure and Applied Logic 108 (2001), 19–77。

## 2. 小さい例

**例 1.** 自然数 $`n \lt \beta`$ について、$`n \le_1 \beta`$ ではない。

- $`n \ge 1`$ のとき：パラメータ $`n - 1`$ の $`\exists x\ (n - 1 \lt x)`$ は、$`\beta`$ で真（$`x = n`$）、$`n`$ で偽である。
- $`n = 0`$ のとき：$`\exists x\ (x \le x)`$ は、$`\beta`$ で真、空の構造 $`0`$ で偽である。

同じ理由で、後者順序数 $`\gamma + 1`$ も、それより大きい順序数と $`\le_1`$ の関係にない。

**例 2.** $`\omega \lt_1 \omega + 1`$ である。

例 1 から、$`\omega + 1`$ より下の異なる 2 点は $`\le_1`$ の関係にない。自然数どうしは例 1 で、残りは $`\omega`$ 自身だけだからである。したがって $`(\omega; \le, \le_1)`$ と $`(\omega + 1; \le, \le_1)`$ では、$`x \le_1 y`$ は $`x = y`$ と同じである。すると比べるのは順序だけの構造 $`(\omega; \le)`$ と $`(\omega + 1; \le)`$ で、$`\omega`$ は極限なので [03](03-sigma1-elementary.md) §5 の例から成り立つ。

**例 3.** $`\beta \ge \omega + 2`$ なら、$`\omega \le_1 \beta`$ ではない。$`\exists x\ \exists y\ (x \lt y \land x \le_1 y)`$ は、$`\beta`$ で真（例 2 の $`x = \omega`$、$`y = \omega + 1`$ はどちらも $`\beta`$ より下にある）、$`\omega`$ で偽（例 1）だからである。

$`\omega \le_1 \omega`$ は定義から成り立つ。以上から $`\{\beta \mid \omega \le_1 \beta\} = \{\omega, \omega + 1\}`$ である。

順序だけの言語では、$`\omega`$ より大きいどの $`\beta`$ でも $`(\omega; \le) \preccurlyeq_{\Sigma_1} (\beta; \le)`$ だった。$`\le_1`$ 自身を言語に入れたので、関係が細かくなった。

## 3. 停止性の証明での使い方

この節は、あとのノートで定義する言葉を先に使って、形だけを述べる。式の列、山の辺、展開は [05](05-omegay-mountain.md) で、ラベルの付け方と切れ目は [06](06-combinatorial-layer.md) §4、§5 で定義する。

展開の停止性の証明では、列ごとにラベル（[01](01-ordinals.md) §6）を付け、展開でラベルが下がることを示す（[02](02-well-founded.md) §6、[06](06-combinatorial-layer.md) §8）。そこで要る性質は **有限反映** である。

**有限反映の形.** $`\alpha \lt_1 \beta`$ とする。$`\alpha`$ より下の点 $`\vec p`$ と、$`\beta`$ より下の点 $`\vec y`$ が、有限個の原子式の条件 $`\psi(\vec p, \vec y)`$ を満たすとする。すると、$`\alpha`$ より下の点 $`\vec y'`$ で、同じ条件 $`\psi(\vec p, \vec y')`$ を満たすものがある。

**理由.** $`\exists \vec y\ \psi(\vec p, \vec y)`$ は $`\Sigma_1`$ 論理式で、$`(\beta; \ldots)`$ で真である。$`\Sigma_1`$ 初等性から $`(\alpha; \ldots)`$ でも真である。

展開では、付け替える列の古いラベルを $`\vec y`$ として、この形を使う。$`\psi`$ に「山の辺の両端の列のラベルが関係 $`\le_1`$ などを満たす」と書いておけば、新しいラベル $`\vec y'`$ も同じ辺の条件を満たす。しかも $`\vec y'`$ は $`\alpha`$ より下にある。展開では $`\alpha`$ は切れ目の列の古いラベルで、付け替える古いラベル $`\vec y`$ はどれも $`\alpha`$ 以上である。したがって新しいラベルは古いラベルより小さい。

**bms-elem-pattern での使い方.** [bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) は、BMS の停止性を $`\mathcal R_N`$ で示した。行 $`k`$ の親子の辺のラベルの関係を $`\lt_{k+1}`$ にする。有限反映には $`\Sigma_n`$ の初等性と、連続性や共終性の補題を使う。$`\mathcal R_N`$ の定義と例は、同リポジトリのノート [proof/pss/03-patterns.md](https://github.com/koteitan/bms-elem-pattern/blob/main/proof/pss/03-patterns.md) にある。

## 4. ω-Y で足りないもの

ω-Y の組合せの層（[06](06-combinatorial-layer.md)）が要求するラベルの関係は、3 つの引数を持つ。

```math
R(\theta, a, b) \quad (\theta \in \mathrm{Key}_m,\ a, b \in \mathrm{Label})
```

「鍵 $`\theta`$ で、$`a`$ は $`b`$ へ安定している」と読む。$`\theta`$ は、山の辺ごとに型板から計算する鍵である（[06](06-combinatorial-layer.md) §3）。このため 3 つの問題が起きる。

**問題 1：鍵が超限である.** 鍵 $`\theta`$ は $`\mathrm{Key}_m`$ を辞書式に動く（[02](02-well-founded.md) §3）。座標はラベルなので、鍵の順序は超限である。$`\mathcal R_N`$ の関係 $`\le_1, \ldots, \le_N`$ は有限個で、自然数で数える。超限の鍵を、この番号にできない。

**問題 2：上端への要求.** 上端 $`b`$ は、展開の前に古い最後の列に付いていたラベルである（[06](06-combinatorial-layer.md) §8）。有限反映は「上端 $`b`$ への関係 $`R(\kappa, x, b)`$」（$`\kappa`$ は鍵、$`x`$ は親のラベル）も新しいラベルで成り立たせる必要がある（[06](06-combinatorial-layer.md) §2 の上端の原子）。$`b`$ は構造 $`(b; \ldots)`$ の元ではない。$`R`$ の定義を展開して書くと $`\Sigma_1`$ にならない。

**問題 3：要求の鍵は、動く列を名指す.** 列 $`i`$ のラベルを $`f(i)`$ とする。上端への要求は $`R(\mathrm{eval}\ t\ f,\ f(p),\ b)`$ の形である。$`p`$ は列の番号、$`t`$ は ω-Y の型板（[03](03-sigma1-elementary.md) §7）である。$`t_i = \mathrm{some}\ j`$ なら、鍵の座標 $`i`$ は $`f(j)`$ である。このとき「型板 $`t`$ は列 $`j`$ を名指す」と言う。Phyrion 氏の有限反映（[06](06-combinatorial-layer.md) §5）は、名指される列 $`j`$ が切れ目 $`\mathrm{cut}`$ より前にあること（$`j \lt \mathrm{cut}`$）を要求しない。つまり鍵の中のラベル $`f(j)`$ は、反映で付け替わる証人でもよい。1-Y 版（[01](01-ordinals.md) §7）は、上端述語を読めるかどうかを変数の位置で決めた（1-Y 版の 03 §8）。その方法はここでは使えない。

## 5. このリポジトリの変更点

[notes/01-design.md](../notes/01-design.md) §2 のとおり、次のように変えた。

1. **どの鍵でも $`\Sigma_1`$ にする.** 鍵による強さの違いは、量化子の複雑さではなく、どの上端述語が定義されているかで決める。
2. **上端述語（[03](03-sigma1-elementary.md) §7）を原子記号にする.** 高さ $`c`$ の構造は、記号 $`\mathrm{Top}_{t,i}(\vec v)`$ を「$`R(\mathrm{eval}\ t\ \vec v,\ v_i,\ c)`$」と解釈して持つ。上端への要求は原子式になる（問題 2）。
3. **鍵 $`\theta`$ で、定義される上端述語を決める.** 上端述語 $`\mathrm{Top}_{t,i}(\vec v)`$ は、$`\mathrm{eval}\ t\ \vec v \lt \theta`$ のときだけ定義される（[03](03-sigma1-elementary.md) §8）。$`\theta`$ が大きいほど、定義される記号が増え、関係は強くなる。定義されるかどうかは鍵の値で決まるので、証人を名指す鍵も扱える（問題 3）。証人を各点で下げても、鍵は $`\theta`$ より下のままである（[03](03-sigma1-elementary.md) §8 の補題 3）。
4. **点どうしの関係 $`\mathrm{Rel}_{t,i,j}`$（[03](03-sigma1-elementary.md) §7）はすべての鍵で持つ.** $`\mathrm{Rel}_{t,i,j}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ v_j)`$ をすべての $`t, i, j`$ について持つ。
5. **再帰の引数（[02](02-well-founded.md) §4）を段 $`(b, \theta)`$ にする.** 上端 $`b`$ を一番外に置く（[02](02-well-founded.md) §3）。鍵 $`\theta`$ の段の右辺は、鍵が $`\theta`$ より小さい上端述語だけを読む。これは 3 の「定義される範囲」と一致する（問題 1）。

こうしてできた関係 $`R`$ は、Carlson の $`\mathcal R_N`$ そのものではない。$`\mathcal R_N`$ と同じだとは主張しない。定義は [07 関係 R](07-relation-r.md) で述べる。

| | $`\mathcal R_N`$（bms-elem-pattern） | 1-Y 版 | Phyrion 氏の元の意味の層 | このリポジトリの $`R`$ |
|---|---|---|---|---|
| 関係を区別する引数 | $`j = 1, \ldots, N`$ | $`(k, \eta) \in \mathbb N \times \mathrm{Ord}`$ | 鍵 $`\theta \in \mathrm{Key}_m`$ | 鍵 $`\theta \in \mathrm{Key}_m`$ |
| 引数による強さ | $`\Sigma_j`$ の量化子 | 見える上端述語の範囲 | 要求の鍵の範囲 | 定義される上端述語の範囲 |
| $`R(\cdot, a, b)`$ の中身 | $`\Sigma_j`$ 初等性 | $`\Sigma_1`$ 初等性 | 有限の正の図式の圧縮（下で定義する） | $`\Sigma_1`$ 初等性 |
| 上端との関係 | 連続性・共終性の補題 | 原子記号（読めるかは変数の位置で決まる） | 図式の中の要求 | 部分的な原子記号（鍵の値で決まる） |
| 再帰の引数 | 上端 $`\beta`$ | $`(b, k, \eta)`$ の辞書式順序 | 段 $`(b, \theta)`$ | 段 $`(b, \theta)`$ |

**Phyrion 氏の元の意味の層.** そこでは $`R(\theta, a, b) \iff a \lt b \land \mathrm{Reflects}(\theta, a, b)`$ で、$`\mathrm{Reflects}(\theta, a, b)`$ は次の圧縮の性質である（[notes/00-survey.md](../notes/00-survey.md) §3.2）。言葉は [06](06-combinatorial-layer.md) §2 のもので、$`n`$ は頂点の数、$`G`$ は内部の原子のリスト、$`N`$ は上端の原子のリスト、$`f, g : \mathrm{Fin}\ n \to \mathrm{Label}`$ はラベルである。「正」とは、条件に否定を含まないことである。

```math
\begin{aligned}
&\forall n\ \forall G\ \forall N\ \forall f\ \Bigl(f \text{ は狭義増加} \land \bigl(\forall i\ f(i) \lt b\bigr) \land G \text{ が } f \text{ で成り立つ} \land \bigl(N \text{ の鍵はどれも } \theta \text{ より小さい}\bigr) \land N \text{ が上端 } b \text{ で成り立つ} \cr
&\qquad \implies \exists g\ \Bigl(g \text{ は狭義増加} \land \bigl(\forall i\ g(i) \lt a\bigr) \land \bigl(\forall i\ (f(i) \lt a \implies g(i) = f(i))\bigr) \land G \text{ が } g \text{ で成り立つ} \land N \text{ が上端 } a \text{ で成り立つ}\Bigr)\Bigr)
\end{aligned}
```

Phyrion 氏の元の意味の層は、このリポジトリには含めていない（[NOTICE](../NOTICE)）。

## 6. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md)「証明の形」 | 意味の層を $`\Sigma_1`$ 初等部分構造の関係に替えたこと、Phyrion 氏の元の関係（圧縮） |
| [README](../README.md)「関係 R」 | 上端述語を原子記号にし、鍵が $`\theta`$ 未満のときだけ定義すること（§5） |
| [notes/01-design.md](../notes/01-design.md) §0、§2 | 設計の要約と定義 |
| [notes/00-survey.md](../notes/00-survey.md) §3.2〜§3.4 | Phyrion 氏の元の関係と、1-Y の方法を広げるときの問題 |

## 7. Lean での対応

$`\le_1`$ そのものは、このリポジトリの Lean には無い。対応するのは次のものである。

| 概念 | Lean | ファイル |
|---|---|---|
| 関係 $`R`$ | `Por.R`（組合せの層からは `Reflection.R`） | [Por/Relation.lean](../Por/Relation.lean)、[OmegaY/Reflection.lean](../OmegaY/Reflection.lean) |
| 段 | `StageLT`、`stage_wf` | [Por/Relation.lean](../Por/Relation.lean) |
| 上端述語、内部の関係の解釈 | `topR c`、`relR` | 同上 |
| 定義される範囲 $`\kappa \lt \theta`$ | `ElemL` の中の `(· < θ)` | [Por/Formula.lean](../Por/Formula.lean) |
| 各点で下げても鍵の条件が残る | `Lit.holds_of_le` | 同上 |
| 名指す列が切れ目より前でなくてよいこと | `finite_reflection` の注釈「No root used in a key is required to be retained」 | [OmegaY/Reflection.lean](../OmegaY/Reflection.lean) |
| 上端の原子、要求の条件 | `InternalAtom`、`TopAtom`、`KeysBelow`、`FixesBelow` | [OmegaY/Reflection/Interface.lean](../OmegaY/Reflection/Interface.lean) |
