[← Back](README.md) | [English](en/07-relation-r.md) | [Japanese](07-relation-r.md)

# 関係 R

前提

| ノート | ここで使う言葉 |
|---|---|
| [01 順序数と ω₁](01-ordinals.md) | ラベル $`\mathrm{Label}`$（§6） |
| [02 整礎関係と整礎再帰](02-well-founded.md) | 鍵 $`\mathrm{Key}_m`$ とその順序、段、上端、段の順序 $`\lhd`$（§3）、整礎再帰、ガードつきの再帰 |
| [03 構造と Σ₁ 初等部分構造](03-sigma1-elementary.md) | 高さ、点、証人、鍵の構文、型板、$`\mathrm{eval}`$、位置、標準形 $`(n, F, L)`$、構造 $`(c; \lt, \mathrm{rel}, \mathrm{top}, \mathrm{allow})`$、上端述語（§7）、2 つの構造の比べ方と補題 1〜3（§8） |
| [04 Patterns of resemblance](04-patterns-of-resemblance.md) | 上端述語を原子記号にする考え方 |
| [06 Phyrion 氏の ω-Y の組合せの層](06-combinatorial-layer.md) | 組合せの層、$`R(\theta, a, b)`$ の役割、3 つの定理のうち鍵の弱化 |

このノートは、このリポジトリのラベルの関係 $`R`$ の定義と、定義から直接出る性質を説明する。

## 1. 記号

- $`\mathrm{Label}`$：ラベル（[01](01-ordinals.md) §6）。
- $`\mathrm{Key}_m`$：長さ $`m`$ の鍵と、その辞書式順序 $`\lt`$（[02](02-well-founded.md) §3）。
- 段 $`(b, \theta) \in \mathrm{Label} \times \mathrm{Key}_m`$ と、その辞書式順序 $`\lhd`$（[02](02-well-founded.md) §3）：$`(b', \kappa') \lhd (b, \theta) \iff b' \lt b \lor (b' = b \land \kappa' \lt \theta)`$。
- 鍵の構文：[03](03-sigma1-elementary.md) §7 の ω-Y の鍵の構文。以下の定義と証明は、その単調性と、$`\mathrm{Label}`$ と $`\mathrm{Key}_m`$ が整列した線形順序であることだけを使う。
- $`R(\theta, a, b)`$：鍵 $`\theta \in \mathrm{Key}_m`$、下の点 $`a \in \mathrm{Label}`$、上の点 $`b \in \mathrm{Label}`$（上端）。$`R`$ は §4 で定義する。§2、§3 では、$`R`$ を記号の解釈に使う。§5 で述べるとおり、この使い方は循環しない。

## 2. 言語

記号は 3 種類である。$`n`$ は変数の数、$`t \in \mathcal T_n`$ は型板、$`i, j \lt n`$ は位置である（[03](03-sigma1-elementary.md) §7）。

| 記号 | 引数の数 | 意味（高さ $`c`$ の構造で） |
|---|---|---|
| $`\lt`$ | 2 | ラベルの大小 |
| $`\mathrm{Rel}_{t,i,j}`$ | $`n`$ | $`\mathrm{Rel}_{t,i,j}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ v_j)`$ |
| $`\mathrm{Top}_{t,i}`$ | $`n`$ | $`\mathrm{Top}_{t,i}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ c)`$ |

$`\mathrm{Rel}_{t,i,j}`$ は点どうしの関係、$`\mathrm{Top}_{t,i}`$ は点から上端 $`c`$ への関係（上端述語）である（[03](03-sigma1-elementary.md) §7）。$`c`$ 自身は領域に無い。どちらの記号も、鍵を $`n`$ 個の点から型板で計算する。

[03](03-sigma1-elementary.md) §7 の形で書くと、解釈は次の $`\mathrm{relR}`$ と $`\mathrm{topR}_c`$ である。

```math
\mathrm{relR}(\kappa, x, y) :\iff R(\kappa, x, y), \qquad \mathrm{topR}_c(\kappa, x) :\iff R(\kappa, x, c)
```

表の解釈を、§5 の段の解釈と区別して **真の解釈** と呼ぶ。上端述語の真の解釈は、高さ $`c`$ ごとに違う。

## 3. 構造 𝔄^c_θ

**定義（構造 𝔄^c_θ）.** 鍵 $`\theta`$ とラベル $`c`$ について、高さ $`c`$ の構造 $`\mathfrak A^c_\theta`$ を次で定める（書き方は [03](03-sigma1-elementary.md) §7）。

```math
\mathfrak A^c_\theta = \bigl(c;\ \lt,\ \mathrm{relR},\ \mathrm{topR}_c,\ \mathrm{allow}_\theta\bigr), \qquad \mathrm{allow}_\theta(\kappa) :\iff \kappa \lt \theta
```

- 領域は $`\{x \mid x \lt c\}`$ である。
- $`\mathrm{Rel}_{t,i,j}`$ はすべての型板で持つ。
- $`\mathrm{Top}_{t,i}(\vec v)`$ は、$`\mathrm{eval}\ t\ \vec v \lt \theta`$ のときだけ定義される。定義されないところでは、$`\mathrm{Top}_{t,i}`$ も $`\neg\mathrm{Top}_{t,i}`$ も偽である（[03](03-sigma1-elementary.md) §8）。

**例.** 鍵の長さを $`m = 1`$、$`\theta = (\omega)`$ とする。型板は ω-Y の鍵の構文のもので（[03](03-sigma1-elementary.md) §7）、$`t = (\mathrm{some}\ 0)`$ は鍵 $`(v_0)`$ を、$`t_\top = (\mathrm{none})`$ は鍵 $`(\top)`$ を与える。

- $`\mathrm{Top}_{t,i}`$ は、$`v_0 \lt \omega`$ のとき定義される。つまり $`v_0`$ が自然数のときである。
- $`\mathrm{Top}_{t_\top,i}`$ は、鍵 $`(\top)`$ が $`\theta`$ 以上なので、どこでも定義されない。
- $`\theta = (\top)`$ なら、$`\mathrm{Top}_{t,i}`$ はどこでも定義される。$`\mathrm{Top}_{t_\top,i}`$ は、$`(\top) \lt (\top)`$ が偽なので、やはり定義されない。
- 論理式 $`\varphi = (2, \{0\}, [v_0 \lt v_1,\ \mathrm{Top}_{t,1}])`$ は、$`\mathfrak A^c_{(\omega)}`$ で次を意味する（$`\vec p = (p_0, p_1)`$ の $`p_1`$ は読まない）。

```math
\mathfrak A^c_{(\omega)} \models \varphi(\vec p) \iff p_0 \lt \omega\ \land\ \exists v_1 \lt c\ \bigl(p_0 \lt v_1 \land R((p_0), v_1, c)\bigr)
```

定義されるかどうかの判定は、鍵の順序を Python で書いて、$`v_0 \in \{0, 7, \omega, \omega + 3\}`$ で確かめた。

## 4. 定義

**定義（R）.**

```math
R(\theta, a, b) \iff a \lt b \ \land\ \mathfrak A^{a}_{\theta} \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_{\theta}
```

ここで $`\mathfrak A^{a}_{\theta} \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_{\theta}`$ は [03](03-sigma1-elementary.md) §8 の比べ方である。つまり、すべての論理式 $`\varphi = (n, F, L)`$ と、$`F`$ の位置で $`p_i \lt a`$ となるすべての $`\vec p`$ について、次が成り立つことである。

```math
\mathfrak A^{a}_{\theta} \models \varphi(\vec p) \iff \mathfrak A^{b}_{\theta} \models \varphi(\vec p)
```

この比較（真の解釈で比べる）を $`\mathrm{Elem}(\theta, a, b)`$ と書く。2 つの構造で、上端述語は別のもの（$`a`$ への $`R`$ と $`b`$ への $`R`$）である（[03](03-sigma1-elementary.md) §8 の違い 1）。

1-Y 版（[01](01-ordinals.md) §7）の $`R`$ にある条件「根のラベル $`\le a`$」は、ここには無い。

## 5. 再帰

右辺は $`R`$ 自身を読む。段 $`(b, \theta)`$ の辞書式順序 $`\lhd`$（[02](02-well-founded.md) §3）で整礎再帰をする。すべての $`a`$ について一度に定義する。

**右辺が読む R.** 3 種類だけで、どれも段が小さい。

| 読むもの | 段 | 小さい理由 |
|---|---|---|
| $`\mathrm{Rel}_{t,i,j}(\vec v)`$、つまり $`R(\kappa, x, y)`$ | $`(y, \kappa)`$ | 点は高さ（$`a`$ か $`b`$）より下なので $`y \lt b`$ |
| $`\mathfrak A^{a}_\theta`$ の上端述語 $`R(\kappa, x, a)`$ | $`(a, \kappa)`$ | $`a \lt b`$ |
| $`\mathfrak A^{b}_\theta`$ の定義された上端述語 $`R(\kappa, x, b)`$ | $`(b, \kappa)`$ | 定義されるのは $`\kappa \lt \theta`$ のときだけ |

3 行目が要点である。$`\mathfrak A^{b}_\theta`$ の上端述語を鍵 $`\theta`$ より下でだけ定義したので、右辺は段 $`(b, \theta)`$ 自身を読まない。

**ガードつきの再帰.** 段 $`(b, \theta)`$ での値は、$`R(\theta, a, b)`$ を満たす $`a`$ の集合である。これを次の **段の解釈** で定める。記号の右肩の $`\mathrm{st}`$ は、段の解釈であることを表す印である。3 つの解釈には、段が小さいという条件をガードとして付ける（[02](02-well-founded.md) §5）。

| 段の解釈 | 式 |
|---|---|
| $`\mathrm{relR}^{\mathrm{st}}(\kappa, x, y)`$ | $`y \lt b \land R(\kappa, x, y)`$ |
| $`\mathrm{topR}^{\mathrm{st},a}(\kappa, x)`$ | $`a \lt b \land R(\kappa, x, a)`$ |
| $`\mathrm{topR}^{\mathrm{st},b}(\kappa, x)`$ | $`\kappa \lt \theta \land R(\kappa, x, b)`$ |

段の解釈で比べた $`\Sigma_1`$ 初等性を $`\mathrm{Elem}^{\mathrm{st}}(\theta, a, b)`$ と書く。

```math
\mathrm{Elem}^{\mathrm{st}}(\theta, a, b) :\iff \bigl(a;\ \lt,\ \mathrm{relR}^{\mathrm{st}},\ \mathrm{topR}^{\mathrm{st},a},\ \mathrm{allow}_\theta\bigr) \preccurlyeq_{\Sigma_1} \bigl(b;\ \lt,\ \mathrm{relR}^{\mathrm{st}},\ \mathrm{topR}^{\mathrm{st},b},\ \mathrm{allow}_\theta\bigr)
```

段の解釈は小さい段での $`R`$ だけを読むので、[02](02-well-founded.md) §4 の整礎再帰で $`R`$ が決まる。定義の等式は、次のガードつきの等式である。

```math
R(\theta, a, b) \iff a \lt b \land \mathrm{Elem}^{\mathrm{st}}(\theta, a, b)
```

## 6. ガードを外す

**補題（ガードを外す）.** $`a \lt b`$ なら、$`\mathrm{Elem}^{\mathrm{st}}(\theta, a, b) \iff \mathrm{Elem}(\theta, a, b)`$ である。つまり、段の解釈での $`\Sigma_1`$ 初等性と、真の解釈での $`\Sigma_1`$ 初等性は同値である。

**証明.** 両側の構造で、論理式が読むところではガードがいつも真であることを示す。そのあと [03](03-sigma1-elementary.md) §8 の補題 1 を、高さ $`a`$ と高さ $`b`$ でそれぞれ使う。

1. $`\mathrm{Rel}`$：補題 1 が要るのは、第 2 の点が高さ（$`a`$ か $`b`$）より下のところだけである。高さはどちらも $`b`$ 以下なので、ガード $`y \lt b`$ は真である。
2. 高さ $`a`$ の上端述語：ガードは $`a \lt b`$ で、仮定そのものである。
3. 高さ $`b`$ の上端述語：補題 1 が要るのは、$`\mathrm{allow}_\theta(\kappa)`$、つまり $`\kappa \lt \theta`$ のところだけである。ガード $`\kappa \lt \theta`$ はそのまま真である。

よって各 $`\varphi, \vec p`$ で、高さ $`a`$ でも高さ $`b`$ でも、2 つの解釈での真偽は等しい。$`\square`$

**定理（定義の式）.**

```math
R(\theta, a, b) \iff a \lt b \land \mathrm{Elem}(\theta, a, b)
```

**証明.** §5 のガードつきの等式に、$`a \lt b`$ の下で補題（ガードを外す）を使う。$`\square`$

## 7. 定義から直接出る性質

**定理（狭義性）.** $`R(\theta, a, b)`$ なら $`a \lt b`$。定義の式の右辺の 1 番目の条件である。

**定理（鍵の弱化）.** $`\theta \le \Theta`$ かつ $`R(\Theta, a, b)`$ なら $`R(\theta, a, b)`$。これが [06](06-combinatorial-layer.md) §5 の鍵の弱化である。

**証明.** 定義の式から、$`a \lt b`$ と $`\mathrm{Elem}(\Theta, a, b)`$ を得る。$`\theta \le \Theta`$ なので、$`\kappa \lt \theta \implies \kappa \lt \Theta`$ である。$`\varphi = (n, F, L)`$ と、$`F`$ の位置で $`p_i \lt a`$ の $`\vec p`$ を取り、2 つの向きを示す。

**向き 1：$`\mathfrak A^a_\theta \models \varphi(\vec p) \implies \mathfrak A^b_\theta \models \varphi(\vec p)`$.** 高さ $`a`$ の証人 $`\vec w`$（$`w_i \lt a`$）を取る。すべての位置をパラメータにした論理式 $`\varphi' := (n, \mathrm{Fin}\ n, L)`$ を作る。[03](03-sigma1-elementary.md) §8 の補題 2 から $`\mathfrak A^a_\Theta \models \varphi'(\vec w)`$ である。$`\mathrm{Elem}(\Theta, a, b)`$ から $`\mathfrak A^b_\Theta \models \varphi'(\vec w)`$ である。$`\varphi'`$ の変数はすべて固定なので、その証人は $`\vec w`$ そのものである。補題 3 を、$`\vec v := \vec w`$ として使うと、$`\vec w`$ は $`\mathfrak A^b_\theta`$ でも $`L`$ のリテラルをすべて満たす。よって $`\mathfrak A^b_\theta \models \varphi(\vec p)`$ である。

**向き 2：$`\mathfrak A^b_\theta \models \varphi(\vec p) \implies \mathfrak A^a_\theta \models \varphi(\vec p)`$.** 高さ $`b`$ の証人 $`\vec v`$（$`v_i \lt b`$）を取る。$`F' := \{i \mid v_i \lt a\}`$、$`\varphi' := (n, F', L)`$ とする。$`F \subseteq F'`$ である。補題 2 から $`\mathfrak A^b_\Theta \models \varphi'(\vec v)`$ である。$`F'`$ の位置では $`v_i \lt a`$ なので、$`\mathrm{Elem}(\Theta, a, b)`$ から $`\mathfrak A^a_\Theta \models \varphi'(\vec v)`$ で、その証人 $`\vec w`$（$`w_i \lt a`$）は次を満たす。

```math
\forall i \in F'\ \ w_i = v_i, \qquad \forall i \notin F'\ \ w_i \lt a \le v_i, \qquad \text{よって}\ \ \forall i \lt n\ \ w_i \le v_i
```

補題 3 から、$`\vec w`$ は $`\mathfrak A^a_\theta`$ でも $`L`$ のリテラルをすべて満たす。$`F`$ の位置では $`w_i = v_i = p_i`$ である。よって $`\mathfrak A^a_\theta \models \varphi(\vec p)`$ である。$`\square`$

2 つめの向きで、証人を各点で下げることが要る。そのため鍵の構文の単調性（[03](03-sigma1-elementary.md) §7）を、補題 3 を通して使う。

**性質（定義された上端述語の一致）.** $`R(\theta, a, b)`$ で、$`\vec v`$ はどの成分も $`a`$ より下とする。$`\mathrm{eval}\ t\ \vec v \lt \theta`$ なら、次が成り立つ。

```math
R(\mathrm{eval}\ t\ \vec v,\ v_i,\ a) \iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ b)
```

**理由.** 量化子の無い論理式 $`(n, \mathrm{Fin}\ n, [\mathrm{Top}_{t,i}])`$ を、パラメータ $`\vec v`$ で使う。高さ $`a`$ では左辺、高さ $`b`$ では右辺を意味する。証明はこの性質を使わない。使うのは、似た形の [09](09-obligations.md) §3.1 の定理（上端述語の絶対性）である。これは Good な点（[08](08-closure-chain.md) §1）と $`\omega_1`$ の間での上端述語の一致である。

**性質（下の点は極限順序数）.** $`R(\theta, a, b)`$ なら、$`a`$ は 0 でない極限順序数である。

**理由.** [03](03-sigma1-elementary.md) §5 の例と同じである。

- $`a = 0`$ のとき：$`\varphi = (1, \emptyset, [\,])`$、つまり $`\exists v_0\ (\text{真})`$ は、高さ $`b`$ で真（$`v_0 = 0 \lt b`$）、高さ 0 で偽である。
- $`a = \gamma + 1`$ のとき：$`\varphi = (2, \{0\}, [v_0 \lt v_1])`$ をパラメータ $`p_0 = \gamma \lt a`$ で使う。高さ $`b`$ で真（$`v_1 = \gamma + 1 \lt b`$）、高さ $`a`$ で偽である。

どちらも $`\mathrm{Elem}`$ に反する。組合せの層はこの性質を使わない。

## 8. 使わない性質

**推移性.** $`R(\theta, a, b) \land R(\theta, b, c) \implies R(\theta, a, c)`$。

**証明.** $`a \lt b \lt c`$ である。構造 $`\mathfrak A^b_\theta`$ は 2 つの比べ方で同じものである。$`F`$ の位置で $`p_i \lt a`$ なら $`p_i \lt b`$ でもあるので、$`\mathfrak A^a_\theta \models \varphi(\vec p) \iff \mathfrak A^b_\theta \models \varphi(\vec p) \iff \mathfrak A^c_\theta \models \varphi(\vec p)`$ である。$`\square`$

組合せの層はこの性質を使わない。

## 9. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md)「関係 R」 | 定義の式と、段の再帰で右辺が読む 3 種類 |
| [README](../README.md)「3 つの定理の証明」 | 鍵の弱化の証明の要約（§7） |
| [notes/01-design.md](../notes/01-design.md) §2、§3.1 | 定義、再帰、鍵の弱化 |

## 10. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| 段と $`\lhd`$ | `StageLT`、`stage_wf` | [Por/Relation.lean](../Por/Relation.lean) |
| 段の解釈とガードつきの 1 段 | `stepF`（ガード $`a \lt b`$ は先頭の `∃ hab : a < s.1` に 1 回だけ書く） | 同上 |
| $`R`$ | `Por.R S θ a b := stage_wf.fix (stepF S) (b, θ) a` | 同上 |
| 真の解釈 | `relR`、`topR c` | 同上 |
| $`\mathrm{Elem}(\theta, a, b)`$ | `ElemL (relR S) (topR S a) (topR S b) θ a b` | [Por/Formula.lean](../Por/Formula.lean) |
| 補題（ガードを外す）と定義の式 | `R_iff`（中で `WellFounded.fix_eq`、`sat_congr` を使う） | [Por/Relation.lean](../Por/Relation.lean) |
| 狭義性 | `R_lt` | 同上 |
| 鍵の弱化 | `key_weaken`（中で `Lit.holds_allow_mono`、`Lit.holds_of_le` を使う） | 同上 |
| 組合せの層が読む名前 | `Reflection.R`、`Reflection.key_weaken`、`Model.key_weaken` | [OmegaY/Reflection.lean](../OmegaY/Reflection.lean)、[OmegaY/Model.lean](../OmegaY/Model.lean) |
| 定義された上端述語の一致、下の点は極限、推移性 | なし（Lean では示していない） | |
