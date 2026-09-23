[← Back](README.md) | [English](en/04-patterns-of-resemblance.md) | [Japanese](04-patterns-of-resemblance.md)

# Patterns of resemblance

前提

| ノート | ここで使う言葉 |
|---|---|
| [01 順序数と ω₁](01-ordinals.md) | 順序数、極限順序数 |
| [02 整礎関係と整礎再帰](02-well-founded.md) | 整礎再帰、ガードつきの再帰、鍵 $`\mathrm{Key}_m`$ |
| [03 構造と Σ₁ 初等部分構造](03-sigma1-elementary.md) | 構造 $`(\gamma; \ldots)`$、$`\Sigma_1`$ 論理式、$`\preccurlyeq_{\Sigma_1}`$、部分的な上端の述語 |

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
- $`x \le_1 y`$ の真偽は、鍵 $`y \lt \beta`$ の段階で決まっている。
- 構造 $`(\alpha; \ldots)`$ も同じで、$`\alpha \le \beta`$ である。

Carlson はこれを $`\le_1, \ldots, \le_N`$（$`\Sigma_1, \ldots, \Sigma_N`$ の初等性）に広げた構造を調べた。

```math
\mathcal R_N = (\mathrm{Ord}; \le, \le_1, \ldots, \le_N)
```

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

展開の停止性の証明では、列ごとに順序数のラベルを付け、展開でラベルが下がることを示す（[02](02-well-founded.md) §6）。そこで要る性質は **有限反映** である。

**有限反映の形.** $`\alpha \lt_1 \beta`$ とする。$`\alpha`$ より下の点 $`\vec p`$ と、$`\beta`$ より下の点 $`\vec y`$ が、有限個の原子式の条件 $`\psi(\vec p, \vec y)`$ を満たすとする。すると、$`\alpha`$ より下の点 $`\vec y'`$ で、同じ条件 $`\psi(\vec p, \vec y')`$ を満たすものがある。

**理由.** $`\exists \vec y\ \psi(\vec p, \vec y)`$ は $`\Sigma_1`$ 論理式で、$`(\beta; \ldots)`$ で真である。$`\Sigma_1`$ 初等性から $`(\alpha; \ldots)`$ でも真である。

展開では、付け替える列の古いラベルを $`\vec y`$ として、この形を使う。$`\psi`$ に「親子の辺のラベルが関係 $`\le_1`$ などを満たす」と書いておけば、新しいラベル $`\vec y'`$ も同じ辺の条件を満たす。しかも $`\vec y'`$ は $`\alpha`$ より下にある。展開では $`\alpha`$ は切れ目の列の古いラベルで、付け替える古いラベル $`\vec y`$ はどれも $`\alpha`$ 以上である。したがって新しいラベルは古いラベルより小さい。

**bms-elem-pattern での使い方.** [bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) は、BMS の停止性を $`\mathcal R_N`$ で示した。行 $`k`$ の親子の辺のラベルの関係を $`\lt_{k+1}`$ にする。有限反映には $`\Sigma_n`$ の段、連続性や共終性の補題を使う。$`\mathcal R_N`$ の定義と例は、同リポジトリのノート [proof/pss/03-patterns.md](https://github.com/koteitan/bms-elem-pattern/blob/main/proof/pss/03-patterns.md) にある。

## 4. ω-Y で足りないもの

ω-Y の組合せの層（[06](06-combinatorial-layer.md)）が要求するラベルの関係は、3 つの引数を持つ。

```math
R(\theta, a, b) \quad (\theta \in \mathrm{Key}_m,\ a, b \in \mathrm{Label})
```

このリポジトリでは「鍵 $`\theta`$ の言語で、高さ $`a`$ の構造が高さ $`b`$ の構造の $`\Sigma_1`$ 初等部分構造である」と読む（[07](07-relation-r.md)）。鍵 $`\theta`$ は、ラベルか $`\top`$ を $`m`$ 個並べた列である（[02](02-well-founded.md) §3）。このため 3 つの問題が起きる。

**問題 1：段の添字が超限である.** 鍵は $`\mathrm{Key}_m`$ を辞書式に動く。座標はラベルなので、鍵の順序は超限である。$`\mathcal R_N`$ の段 $`\Sigma_1, \ldots, \Sigma_N`$ は有限個で、自然数で数える。鍵を段の番号にできない。

**問題 2：上端への要求.** 有限反映は「上端 $`b`$ への関係 $`R(\kappa, x, b)`$」も新しいラベルで成り立たせる必要がある（[06](06-combinatorial-layer.md) §2 の上端の原子）。$`b`$ は構造 $`(b; \ldots)`$ の元ではない。$`R`$ の定義を展開して書くと $`\Sigma_1`$ にならない。

**問題 3：要求の鍵は動く点を名指す.** 要求 $`R(\mathrm{eval}\ t\ f, f(p), b)`$ の鍵は、型板 $`t`$ が名指す列のラベルから決まる。Phyrion 氏の有限反映は、その列が切れ目より前にあることを要求しない（[OmegaY/Reflection.lean](../OmegaY/Reflection.lean) の `finite_reflection` の注釈「No root used in a key is required to be retained」）。つまり鍵の中のラベルは、反映で付け替わる証人でもよい。1-Y 版は、上端の述語が見えるかどうかを「パラメータの位置」で決めた。その方法はここでは使えない。

## 5. このリポジトリの変更点

[notes/01-design.md](../notes/01-design.md) §2 のとおり、次のように変えた。

1. **段はすべて $`\Sigma_1`$ にする.** 段の強さは、量化子の複雑さではなく、どの上端の述語が定義されているかで決まる。
2. **上端の述語を原子記号にする.** 高さ $`c`$ の構造は、型板 $`t`$ と位置 $`i`$ ごとに記号 $`\mathrm{Top}_{t,i}`$ を持ち、「$`R(\mathrm{eval}\ t\ \vec v, v_i, c)`$」と解釈する。上端への要求は原子式になる（問題 2）。
3. **上端の述語は、鍵が $`\theta`$ より下のところでだけ定義する.** 定義されないところでは、上端のリテラルは偽である（[03](03-sigma1-elementary.md) §8）。定義されるかどうかは鍵の値で決まる（問題 3）。証人を各点で下げても、$`\mathrm{eval}`$ が単調なので鍵は $`\theta`$ より下のままである（`Lit.holds_of_le`）。
4. **内部の関係はすべての鍵で持つ.** 型板 $`t`$ と位置 $`i, j`$ ごとに $`\mathrm{Rel}_{t,i,j}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v, v_i, v_j)`$ を持つ。
5. **再帰の段を（上端、鍵）にする.** 上端 $`b`$ を一番外に置く（[02](02-well-founded.md) §3）。鍵 $`\theta`$ の段の右辺は、鍵が $`\theta`$ より小さい上端の述語だけを読む。これは 3 の「定義される範囲」とちょうど一致する（問題 1）。

こうしてできた関係 $`R`$ は、Carlson の $`\mathcal R_N`$ そのものではない。$`\mathcal R_N`$ と同じだとは主張しない。定義は [07 関係 R](07-relation-r.md) で述べる。

| | $`\mathcal R_N`$（bms-elem-pattern） | 1-Y 版（1y-wo-por） | Phyrion 氏の ω-Y の元の意味の層 | このリポジトリ |
|---|---|---|---|---|
| 段 | $`j = 1, \ldots, N`$ | $`(k, \eta) \in \mathbb N \times \mathrm{Ord}`$ | 鍵 $`\theta \in \mathrm{Key}_m`$ | 鍵 $`\theta \in \mathrm{Key}_m`$ |
| $`R(\cdot, a, b)`$ の中身 | $`\Sigma_j`$ 初等性 | $`\Sigma_1`$ 初等性 | $`b`$ より下の有限の正の図式を $`a`$ より下へ圧縮できる | $`\Sigma_1`$ 初等性 |
| 上端との関係 | 連続性・共終性の補題 | 原子記号（見えるかどうかは変数の位置で決まる） | 図式の中の要求 | 部分的な原子記号（鍵の値で定義される） |
| 再帰 | 上端 $`\beta`$ | （上端、層、添字） | （上端、鍵） | （上端、鍵） |

Phyrion 氏の元の意味の層は [notes/00-survey.md](../notes/00-survey.md) §3.2 にまとめてある。このリポジトリには含めていない（[NOTICE](../NOTICE)）。

## 6. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md)「証明の形」「関係 R」 | 意味の層を $`\Sigma_1`$ 初等部分構造の関係に替えたこと |
| [notes/01-design.md](../notes/01-design.md) §0、§2 | 設計の要約と定義 |
| [notes/00-survey.md](../notes/00-survey.md) §3.2〜§3.4 | Phyrion 氏の元の関係と、1-Y の方法を広げるときの問題 |
| [Por/Formula.lean](../Por/Formula.lean)、[Por/Relation.lean](../Por/Relation.lean) | §5 の 1〜5 |

## 7. Lean での対応

$`\le_1`$ そのものは、このリポジトリの Lean には無い。対応するのは次のものである。

| 概念 | Lean | ファイル |
|---|---|---|
| 関係 $`R`$ | `Por.R` | [Por/Relation.lean](../Por/Relation.lean) |
| 再帰の段 | `StageLT`、`stage_wf` | 同上 |
| 上端の述語の解釈 | `topR c` | 同上 |
| 内部の関係の解釈 | `relR` | 同上 |
| 定義される範囲 | `ElemL` の `allow` $`= (\cdot \lt \theta)`$ | [Por/Formula.lean](../Por/Formula.lean) |
| 下げても鍵の条件が残る | `Lit.holds_of_le` | 同上 |
