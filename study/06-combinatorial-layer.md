[← Back](README.md) | [English](en/06-combinatorial-layer.md) | [Japanese](06-combinatorial-layer.md)

# Phyrion 氏の ω-Y の組合せの層

前提

| ノート | ここで使う言葉 |
|---|---|
| [01 順序数と ω₁](01-ordinals.md) | ラベル $`\mathrm{Label}`$（§6）、$`\mathrm{Fin}\ n`$、$`\mathrm{Option}`$（§7） |
| [02 整礎関係と整礎再帰](02-well-founded.md) | 整礎、到達可能、整礎帰納法（§1、§2）、鍵 $`\mathrm{Key}_m`$ とその順序、$`\top`$、上端（§3）、ラベルの上界による停止（§6） |
| [03 構造と Σ₁ 初等部分構造](03-sigma1-elementary.md) | 鍵の構文、型板、$`\mathcal T_n`$、$`\mathrm{eval}`$、ω-Y の鍵の構文（§7） |
| [05 ω-Y 数列と山](05-omegay-mountain.md) | 式、行、係数、跳び、次の行 $`B`$、山 $`M(s)`$、$`\mathrm{next}`$、節点、$`\mathrm{col}`$、$`\mathrm{row}`$、$`\mathrm{top}(c)`$、親 $`\mathrm{par}_a(c)`$、辺、下の節点、次数 $`\delta_c(a)`$、根 $`(z, d)`$、展開 $`s[N]`$、ブロック、$`L`$、ずらし $`m_i`$、1 段の展開 $`\prec`$、次元（§7） |

このノートは、Phyrion 氏の証明のうち、組合せの層を説明する。この層は、関係 $`R`$ を引数に取り（§2）、ラベルの値が何であるかは使わずに、$`R`$ についての 3 つの定理（§5）から展開の整礎性を示す。このリポジトリは、この層の定理をそのまま使う。

## 1. 図式

**定義（アトム）.** $`m, n \in \mathbb N`$ とする。$`m`$ は鍵の長さ、$`n`$ は列の個数である。**アトム** は組 $`e = (t, p, q)`$ である。親子の辺（[05](05-omegay-mountain.md) §3）1 本を表す。

- $`t \in \mathcal T_n`$：型板。[03](03-sigma1-elementary.md) §7 の ω-Y の鍵の構文のもので、$`\mathcal T_n = \mathrm{Fin}\ m \to \mathrm{Option}(\mathrm{Fin}\ n)`$ である。辺の鍵を、列のラベルから計算する。1-Y 版の層 $`k`$ と根の列 $`r`$ の代わりである。
- $`p \in \mathbb N`$：親の列の番号。
- $`q \in \mathbb N`$：子の列の番号。

$`p`$、$`q`$ と、型板の座標 $`t_i = \mathrm{some}\ j`$ の $`j`$ は、どれも列の番号（自然数）である。列に付けるラベルは §2 で定義する。

サイズ $`n`$ で **妥当** とは $`p \lt q \lt n`$ のことである。

**定義（図式）.** **図式** は、サイズ $`n`$ と、妥当なアトムの有限リストの組である。$`n \in \mathbb N`$ は列の個数で、列の番号は $`0, 1, \ldots, n - 1`$ である。図式 $`G`$ のアトムのリストに $`e`$ が入ることを $`e \in G`$ と書く。

- 式 $`s = (s_0, \ldots, s_{n-1})`$ の図式では、$`n`$ は式の長さである。

**定義（列の番号で読んだ鍵）.** 自然数は $`\omega_1`$ より小さい順序数なので、ラベルである。型板 $`t \in \mathcal T_n`$ を、列の番号そのものをラベルとして評価した鍵を $`\bar t`$ と書く。

```math
\bar t := \mathrm{eval}\ t\ \mathrm{id}, \qquad \bar t_i = \begin{cases} j & (t_i = \mathrm{some}\ j) \cr \top & (t_i = \mathrm{none}) \end{cases}
```

以下の表では、型板 $`t`$ を $`\bar t`$ で書く。例えば $`\bar t = (0, \top)`$ は $`t = (\mathrm{some}\ 0, \mathrm{none})`$ である。

**性質 1（鍵の比べ方は列の番号で決まる）.** $`f : \mathrm{Fin}\ n \to \mathrm{Label}`$ が狭義増加なら、型板 $`t, t'`$ について次が成り立つ。

```math
\bar t \le \bar t' \implies \mathrm{eval}\ t\ f \le \mathrm{eval}\ t'\ f, \qquad \bar t \lt \bar t' \implies \mathrm{eval}\ t\ f \lt \mathrm{eval}\ t'\ f
```

**証明.** $`\bar t_i = \bar t'_i`$ なら $`t_i = t'_i`$ なので、2 つの鍵の座標 $`i`$ も等しい。最初に違う座標 $`i`$ で $`\bar t_i \lt \bar t'_i`$ なら、$`t_i = \mathrm{some}\ j`$ で、$`t'_i = \mathrm{some}\ j'`$（$`j \lt j'`$）か $`t'_i = \mathrm{none}`$ である。前者では $`f(j) \lt f(j')`$、後者では $`f(j) \lt \top`$ である。$`\square`$

したがって、鍵の大小は、ラベルを選ぶ前に列の番号だけで比べられる。

**定義（列の写像で写す）.** $`\mu`$ を列の番号の写像とする。型板 $`t`$ を $`\mu`$ で写した型板 $`\mu t`$ を次で定める。

```math
(\mu t)_i := \begin{cases} \mathrm{some}\ \mu(j) & (t_i = \mathrm{some}\ j) \cr \mathrm{none} & (t_i = \mathrm{none}) \end{cases}
```

アトム $`e = (t, p, q)`$ を $`\mu`$ で写したものを $`\mu e := (\mu t, \mu(p), \mu(q))`$ とする。図式 $`G`$ のアトムをすべて写したリストを $`\mu G`$ と書く。

**性質 2.** どのラベルの列 $`h`$ についても、$`\mathrm{eval}\ (\mu t)\ h = \mathrm{eval}\ t\ (h \circ \mu)`$。$`\mu`$ が狭義増加なら、$`\bar t \le \bar t' \implies \overline{\mu t} \le \overline{\mu t'}`$、$`\bar t \lt \bar t' \implies \overline{\mu t} \lt \overline{\mu t'}`$。

**証明.** 1 つめは、各座標が $`h(\mu(j))`$ か $`\top`$ であることから出る。2 つめは、性質 1 の証明と同じである（$`j \lt j'`$ なら $`\mu(j) \lt \mu(j')`$）。$`\square`$

**定義（接頭辞）.** $`n' \le n`$ とする。サイズ $`n`$ の図式 $`G`$ の **サイズ $`n'`$ の接頭辞** とは、$`G`$ のアトム $`(t, p, q)`$ のうち $`q \lt n'`$ のものだけを残した、サイズ $`n'`$ の図式である。ただし、残したアトムの型板は、$`n'`$ より小さい列だけを指すとする（式の図式では、下の性質 3 からいつもそうである）。

**定義（尺度の根）.** 式 $`s`$ の山 $`M(s)`$ を考える。$`k \in \mathbb N`$ とする。節点 $`u = (c, a)`$ の **尺度 $`k`$ の根** $`\rho_k(u)`$ を次で定める。

```math
\rho_k(c, a) := \begin{cases} \rho_k\bigl(\mathrm{par}_a(c)\bigr) & (1 \le a \lt \mathrm{top}(c),\ \delta_c(a) \le k) \cr (c, a) & (\text{それ以外}) \end{cases}
```

$`u`$ から上への辺の次数が $`k`$ 以下なら、その辺の親へ進む。そうでなければ止まる。親は左の列にあるので、この再帰は止まり、$`\mathrm{col}(\rho_k(u)) \le \mathrm{col}(u)`$ である。

**式の図式.** 式 $`s`$ と、$`M(s)`$ の次元 $`D`$（[05](05-omegay-mountain.md) §7）を 1 つ選ぶ。式の図式 $`G_D(s)`$ は、$`M(s)`$ のすべての辺を 1 つずつアトムにしたものである。鍵の長さは $`m = D + 1`$ である。下の節点が $`(c, a)`$ で、親が $`\pi = \mathrm{par}_a(c)`$、次数が $`\delta = \delta_c(a)`$ の辺 $`e`$ について、アトム

```math
\bigl(\kappa_D(e),\ \mathrm{col}(\pi),\ c\bigr)
```

を入れる。$`\kappa_D(e)`$ は辺 $`e`$ の型板で、座標 $`i`$ は尺度 $`D - i`$ に当たる。

```math
\kappa_D(e)_i := \begin{cases} \mathrm{some}\ \mathrm{col}\bigl(\rho_{D-i}(\pi)\bigr) & (\delta \le D - i) \cr \mathrm{none} & (\delta \gt D - i) \end{cases}
```

つまり、列 $`j`$ のラベルを $`f(j)`$ とすると、辺の鍵は次のとおりである。

```math
\mathrm{eval}\ \kappa_D(e)\ f = \Bigl(f\bigl(\mathrm{col}\,\rho_D(\pi)\bigr),\ f\bigl(\mathrm{col}\,\rho_{D-1}(\pi)\bigr),\ \ldots,\ f\bigl(\mathrm{col}\,\rho_\delta(\pi)\bigr),\ \underbrace{\top, \ldots, \top}_{\delta}\Bigr)
```

**性質 3.** 辺 $`e`$（下の節点 $`(c, a)`$、親 $`\pi`$、次数 $`\delta`$）について、次が成り立つ。

1. $`\delta \le D`$。
2. $`\kappa_D(e)_i = \mathrm{some}\ j`$ なら $`j \le \mathrm{col}(\pi) \lt c`$。型板は、親の列以下の列だけを指す。子の列は指さない。

**証明.** 1：上の節点の行は $`a + \omega^{\delta}`$ で（[05](05-omegay-mountain.md) §3）、その係数 $`c_\delta`$ は 1 以上である（[05](05-omegay-mountain.md) §2 の「ω の冪を足す」）。次元の定義から $`\delta \le D`$ である。2：$`\mathrm{col}(\rho_k(\pi)) \le \mathrm{col}(\pi)`$ で、親は左の列にある。$`\square`$

**性質 4（列の中で鍵が増える）.** 同じ列の 2 つの辺 $`e, e'`$ で、$`e`$ の下の節点の行が $`e'`$ の下の節点の行より小さいなら、$`\bar\kappa_D(e) \lt \bar\kappa_D(e')`$ である。ここでは証明しない。

性質 4 は、05 §3、§4 の式を写した Python のプログラムで、§7 の補題と同じ範囲の式の山で確かめた（2026-09-27）。

| 式 | $`D`$ | アトム $`(\bar t, p, q)`$ |
|---|---|---|
| $`(1, 2, 2)`$ | 0 | $`((0), 0, 1)`$、$`((0), 0, 2)`$ |
| $`(1, 2, 4)`$ | 0 | $`((0), 0, 1)`$、$`((0), 1, 2)`$、$`((1), 1, 2)`$ |
| $`(1, 3)`$ | 1 | $`((0, 0), 0, 1)`$、$`((0, \top), 0, 1)`$ |
| $`(1, 4)`$ | 2 | $`((0, 0, 0), 0, 1)`$、$`((0, 0, \top), 0, 1)`$、$`((0, \top, \top), 0, 1)`$ |
| $`(1, 3, 5)`$ | 1 | $`((0, 0), 0, 1)`$、$`((0, \top), 0, 1)`$、$`((0, 0), 1, 2)`$、$`((0, \top), 0, 2)`$ |

表の値は、この節の定義をそのまま写した Python のプログラムで計算した（2026-09-27）。表の $`D`$ は、次元のうち最小のもの（山の行の 0 でない係数の指数の最大値）である。

**例（$`(1, 2, 4)`$ のアトム）.** まず山を作る（[05](05-omegay-mountain.md) §3）。表の読み方は [05](05-omegay-mountain.md) §3 の例と同じで、「$`v \leftarrow (p, e)`$」は、値が $`v`$ で、左の脚（下の辺の親）が節点 $`(p, e)`$ であることを表す。

| 行 | 列 0 | 列 1 | 列 2 |
|---|---|---|---|
| $`3`$ | | | $`1 \leftarrow (1, 2)`$ |
| $`2`$ | | $`1 \leftarrow (0, 1)`$ | $`2 \leftarrow (1, 1)`$ |
| $`1`$ | $`1`$ | $`2`$ | $`4`$ |

- 列 1：$`\mathrm{par}_1(1) = (0, 1)`$（値 $`1 \lt 2`$）で、次の行は $`B(1, 1) = 2`$、値は $`2 - 1 = 1`$ で終わる。
- 列 2：$`\mathrm{par}_1(2) = (1, 1)`$（値 $`2 \lt 4`$）で、次の行は $`B(1, 1) = 2`$、値は $`4 - 2 = 2`$ である。行 2 では $`\mathrm{next}(2, 2) = (1, \max(\{1\} \cup \{0, 1, 2\})) = (1, 2)`$ で、値 $`1 \lt 2`$ なので、親は $`(1, 2)`$ である。次の行は $`B(2, 2) = 3`$、値は $`2 - 1 = 1`$ で終わる。
- 行はどれも $`\omega`$ より小さいので、$`D = 0`$ である。鍵の長さは 1 で、座標 0 は尺度 0 に当たる。どの辺も次数は 0 なので、座標 0 は有限である。

したがって辺は 3 本で、1 本ずつアトムになる。サイズは $`n = 3`$ である。

| 辺（列、行） | 親 $`\pi`$ | 次数 $`\delta`$ | $`\rho_0(\pi)`$ の求め方 | アトム $`(\bar t, p, q)`$ | 妥当性 $`p \lt q \lt 3`$ |
|---|---|---|---|---|---|
| 列 1、$`1 \to 2`$ | $`(0, 1)`$ | $`\mathrm{jump}(1, 1) = 0`$ | $`(0, 1)`$ は列 0 の一番上で、上への辺が無い。根は $`(0, 1)`$ | $`((0), 0, 1)`$ | $`0 \lt 1 \lt 3`$ |
| 列 2、$`1 \to 2`$ | $`(1, 1)`$ | $`\mathrm{jump}(1, 1) = 0`$ | $`(1, 1)`$ から上への辺は次数 $`0 \le 0`$ で、親 $`(0, 1)`$ へ進む。根は $`(0, 1)`$ | $`((0), 1, 2)`$ | $`1 \lt 2 \lt 3`$ |
| 列 2、$`2 \to 3`$ | $`(1, 2)`$ | $`\mathrm{jump}(2, 2) = 0`$ | $`(1, 2)`$ は列 1 の一番上。根は $`(1, 2)`$ | $`((1), 1, 2)`$ | $`1 \lt 2 \lt 3`$ |

- 2 つめと 3 つめのアトムは、どちらも親 1、子 2 の辺だが、型板が違う（$`(0)`$ と $`(1)`$）。そのため別のアトムになる。
- 3 つめのアトムの辺は列 2 の一番上の辺で、その親 $`(1, 2)`$ が $`(1, 2, 4)`$ の根である（[05](05-omegay-mountain.md) §4）。
- 1-Y 版のアトムは $`(0, 0, 0, 1)`$、$`(0, 0, 1, 2)`$、$`(0, 1, 1, 2)`$ である。この例では、1-Y 版のアトム $`(k, r, p, q)`$ の根の列 $`r`$ が、型板 $`(r)`$ になっている。

**例（$`(1, 3)`$ のアトム）.** この式では、次数 1 の辺がある。

| 行 | 列 0 | 列 1 |
|---|---|---|
| $`\omega`$ | | $`1 \leftarrow (0, 1)`$ |
| $`2`$ | | $`2 \leftarrow (0, 1)`$ |
| $`1`$ | $`1`$ | $`3`$ |

- 列 1：$`\mathrm{par}_1(1) = (0, 1)`$（値 $`1 \lt 3`$）で、次の行は $`B(1, 1) = 2`$、値は $`3 - 1 = 2`$ である。行 2 では $`\mathrm{next}(1, 2) = (0, \max(\{1\} \cup \{0, 1\})) = (0, 1)`$ で、値 $`1 \lt 2`$ なので、親は $`(0, 1)`$ である。$`\mathrm{jump}(2, 1) = 1`$ なので、次の行は $`B(2, 1) = \omega`$、値は $`2 - 1 = 1`$ で終わる。
- 行 $`\omega`$ の係数 $`c_1`$ が 1 なので、$`D = 1`$ である。鍵の長さは 2 で、座標 0 は尺度 1、座標 1 は尺度 0 に当たる。

| 辺（列、行） | 親 $`\pi`$ | 次数 $`\delta`$ | 型板の求め方 | アトム $`(\bar t, p, q)`$ | 妥当性 $`p \lt q \lt 2`$ |
|---|---|---|---|---|---|
| 列 1、$`1 \to 2`$ | $`(0, 1)`$ | 0 | 座標 0、1 とも $`\delta \le D - i`$。$`\rho_1(0, 1) = \rho_0(0, 1) = (0, 1)`$ | $`((0, 0), 0, 1)`$ | $`0 \lt 1 \lt 2`$ |
| 列 1、$`2 \to \omega`$ | $`(0, 1)`$ | 1 | 座標 0 は $`1 \le 1`$ で $`\mathrm{col}\,\rho_1(0, 1) = 0`$。座標 1 は $`1 \gt 0`$ で $`\top`$ | $`((0, \top), 0, 1)`$ | $`0 \lt 1 \lt 2`$ |

- 2 つのアトムは、親と子が同じで、型板だけが違う。1-Y 版では、層 $`k`$ だけが違った（$`(0, 0, 0, 1)`$ と $`(1, 0, 0, 1)`$）。
- 下の辺の型板 $`(0, 0)`$ は、上の辺の型板 $`(0, \top)`$ より小さい（性質 4）。上の辺は列 1 の一番上の辺で、その親 $`(0, 1)`$ が根である（[05](05-omegay-mountain.md) §4）。

**例（$`(1, 3, 5)`$）.** 列 2 の最初の辺 $`1 \to 2`$ は、親が $`(1, 1)`$ で列 1 にあるのに、型板は列 0 を指す。$`(1, 1)`$ から上への辺は次数 0 で、その親は $`(0, 1)`$ だからである。型板は親ではなく、親の尺度の根を指す。

## 2. 表現

関係 $`R`$ を 1 つ選んで決めておく。以下の定義はすべてこの関係に対してのものである。

- $`\mathrm{Label}`$ の元を **ラベル** と呼ぶ（[01](01-ordinals.md) §6）。下の表現で、図式の列に 1 つずつラベルを付ける。
- $`\lt`$ はラベルの順序（順序数の順序）である。
- $`R(\theta, a, b)`$ は 3 引数の関係である。$`\theta \in \mathrm{Key}_m`$ は鍵、$`a, b`$ はラベルである。下の表現の定義では、$`\theta`$ に辺の鍵、$`a`$ に親のラベル、$`b`$ に子のラベルが入る。$`R(\theta, a, b)`$ は「鍵 $`\theta`$ で、$`a`$ は $`b`$ へ安定している」と読む。ここでは読み方だけで、$`R`$ の中身は問わない（§9）。

1-Y 版の 4 引数の $`R(k, \eta, a, b)`$ の層 $`k`$ と根のラベル $`\eta`$ が、1 つの鍵 $`\theta`$ になった。1-Y 版の定義域 $`D`$ は無い。

**定義（成り立つ）.** 関数 $`f : \mathrm{Fin}\ n \to \mathrm{Label}`$ について、アトム $`(t, p, q)`$ が $`f`$ で **成り立つ** とは、$`R(\mathrm{eval}\ t\ f, f(p), f(q))`$ のことである。

**定義（表現）.** 関数 $`f : \mathrm{Fin}\ n \to \mathrm{Label}`$ が図式 $`G`$（サイズ $`n`$）の **表現** であるとは、次の 3 つが成り立つことをいう。

1. $`i \lt n`$ なら $`f(i) \lt \omega_1`$。
2. $`i \lt j \lt n`$ なら $`f(i) \lt f(j)`$。
3. $`G`$ の各アトムが $`f`$ で成り立つ。

$`f(i)`$ を列 $`i`$ のラベルと呼ぶ。条件 1 は、1-Y 版の条件 $`D(f(i))`$ の代わりである。式 $`s`$ の山の、次元 $`D`$ での表現とは、$`G_D(s)`$ の表現のことである。

**例.** $`(1, 2, 4)`$ の図式（$`D = 0`$）の表現は、次を満たす $`f`$ である。

```math
f(0) \lt f(1) \lt f(2) \lt \omega_1, \quad R((f(0)), f(0), f(1)), \quad R((f(0)), f(1), f(2)), \quad R((f(1)), f(1), f(2))
```

$`(1, 3, 5)`$ の図式（$`D = 1`$）の表現は、次を満たす $`f`$ である。$`f_j := f(j)`$ と書く。

```math
f_0 \lt f_1 \lt f_2 \lt \omega_1, \quad R((f_0, f_0), f_0, f_1), \quad R((f_0, \top), f_0, f_1), \quad R((f_0, f_0), f_1, f_2), \quad R((f_0, \top), f_0, f_2)
```

## 3. 上端への要求

**定義（上端のアトム）.** **上端のアトム** は組 $`d = (t, p)`$（$`t \in \mathcal T_n`$、$`p \in \mathbb N`$）で、サイズ $`n`$ で妥当とは $`p \lt n`$ のことである。図式の外にある点のラベル $`\beta`$ を **上端** と呼ぶ。関数 $`f : \mathrm{Fin}\ n \to \mathrm{Label}`$ について、$`d`$ が上端 $`\beta`$ について **成り立つ** とは、$`R(\mathrm{eval}\ t\ f, f(p), \beta)`$ のことである。列の写像 $`\mu`$ で写したものを $`\mu d := (\mu t, \mu(p))`$ とする。

上端のアトムは、図式の外にある点 $`\beta`$ への辺である。展開（[05](05-omegay-mountain.md) §4）では、古い最後の列のラベルが $`\beta`$ になる。

**ふつうのアトムとの違い.** 上端のアトムは、アトム $`(t, p, q)`$ から子 $`q`$ を除いたものである。子は図式の列ではなく、図式の外の点で、そのラベルを $`\beta`$ と書く。

| | アトム | 上端のアトム |
|---|---|---|
| 形 | $`(t, p, q)`$ | $`(t, p)`$ |
| 子 | 図式の列 $`q`$ | 図式の外の点（ラベル $`\beta`$） |
| 妥当 | $`p \lt q \lt n`$ | $`p \lt n`$ |
| 成り立つ | $`R(\mathrm{eval}\ t\ f, f(p), f(q))`$ | $`R(\mathrm{eval}\ t\ f, f(p), \beta)`$ |

**例 1（形）.** $`(1, 2, 4)`$ のアトムは $`((0), 0, 1)`$、$`((0), 1, 2)`$、$`((1), 1, 2)`$ である（§1）。最後の列 2 を除いて、列 0、1 だけの図式（サイズ 2）を考える。列 2 への 2 本の辺は、子が図式の外に出るので、上端のアトムとして書く。

- $`((0), 1)`$：成り立つとは $`R((f(0)), f(1), \beta)`$ のこと。
- $`((1), 1)`$：成り立つとは $`R((f(1)), f(1), \beta)`$ のこと。

ここで $`\beta = f(2)`$ は、外に出た列 2 のラベルである。型板は親の列以下だけを指すので（性質 3）、子を除いても、型板が指す列は図式の中にある。

**定義（要求）.** §4 の有限反映に、図式 $`G`$ とは別に渡す上端のアトム $`d`$ を **要求** と呼ぶ。要求の有限リストを $`\mathrm{needs}`$ と書く。有限反映は、反映の前に上端 $`\beta`$ について成り立つ要求が、反映の後も新しい上端 $`f(\mathrm{cut})`$（$`\mathrm{cut}`$ は下で定義する切れ目）について成り立つことを保証する。

**展開のステップ.** 式 $`s`$ を展開して $`s[N]`$ を作る場面を考える（展開は [05](05-omegay-mountain.md) §4）。$`x`$ を $`s`$ の最後の列、根を $`(z, d)`$、$`L := x - z`$ とする。$`s[N]`$ の列 $`z`$ から先は、ブロック $`0, 1, \ldots, N`$ に分かれる（[05](05-omegay-mountain.md) §4）。§7 では、$`G_D(s)`$ の表現から $`G_D(s[N])`$ の表現を、ブロックを 1 つずつ足して作る。$`i = 0, 1, \ldots, N - 1`$ について、ブロック $`i + 1`$ を足す手順を **ステップ $`i`$** と呼ぶ。

**定義（制御の辺と下の辺）.** $`M(s)`$ の列 $`x`$ の一番上の辺を **制御の辺** $`e_c`$ と呼ぶ。その親は根 $`(z, d)`$ である（[05](05-omegay-mountain.md) §4）。列 $`x`$ のほかの辺（制御の辺より下の辺）を **下の辺** と呼ぶ。

**展開での要求.** 各ステップ $`i`$ で、次のように $`\mathrm{needs}`$ を作る。$`m_i`$ は [05](05-omegay-mountain.md) §4 のずらしで、列 $`j \lt z`$ を動かさず、列 $`j \ge z`$ を $`j + iL`$ へ移す。

- ステップ $`i`$ では、ブロック $`i`$ の最初の列 $`\mathrm{cut} := z + iL`$ を **切れ目** と呼ぶ。
- 次に足す列 $`x + iL`$（ブロック $`i + 1`$ の最初の列）のラベルが、新しい上端 $`f(\mathrm{cut})`$ になる。
- 下の辺 $`e`$（親 $`\pi`$）ごとに、上端のアトム $`\bigl(\kappa_D(e), \mathrm{col}(\pi)\bigr)`$ を $`m_i`$ で写したものを要求にする。このリストを $`T_i`$ と書く。

```math
\mathrm{needs} := T_i := \Bigl[\ m_i\bigl(\kappa_D(e),\ \mathrm{col}(\pi_e)\bigr)\ \Bigm|\ e \text{ は下の辺}\ \Bigr]
```

制御の辺は要求にはしない。代わりに、関係 $`R(\theta, f(\mathrm{cut}), \beta)`$ を §4 の有限反映に渡す（仮定 3）。この形の関係を **制御関係** と呼ぶ。鍵 $`\theta`$ は、制御の辺の型板を $`m_i`$ で写して評価したものである。ステップ 0 では $`\theta = \mathrm{eval}\ \kappa_D(e_c)\ f`$ である。後のステップでの $`\theta`$ は §7 で述べる。

**性質 5（要求の鍵は制御の鍵より小さい）.** 下の辺 $`e`$ と $`i \in \mathbb N`$ について $`\overline{m_i \kappa_D(e)} \lt \overline{m_i \kappa_D(e_c)}`$。したがって、狭義増加のどの $`f`$ についても $`\mathrm{eval}\ (m_i \kappa_D(e))\ f \lt \mathrm{eval}\ (m_i \kappa_D(e_c))\ f`$ である。

**証明.** 性質 4 から $`\bar\kappa_D(e) \lt \bar\kappa_D(e_c)`$ である。$`m_i`$ は狭義増加なので、性質 2 から $`\overline{m_i \kappa_D(e)} \lt \overline{m_i \kappa_D(e_c)}`$ である。あとは性質 1 である。$`\square`$

**例 2（$`(1, 2, 4)`$ の展開のステップ 0）.** $`x = 2`$、根は $`(z, d) = (1, 2)`$、$`L = 1`$、$`D = 0`$、$`s[N] = (1, 2, \ldots, N + 2)`$ である（[05](05-omegay-mountain.md) §6）。ステップ $`i = 0`$ を見る。

- 図式 $`G`$ は $`(1, 2)`$ の図式で、サイズ 2、アトムは $`((0), 0, 1)`$ である。$`f`$ はもとの表現で、$`\beta = f(2)`$、切れ目は $`\mathrm{cut} = z = 1`$ である。
- 列 2 の辺は $`1 \to 2`$（親 $`(1, 1)`$、型板 $`(0)`$）と $`2 \to 3`$（親 $`(1, 2)`$、型板 $`(1)`$）である。制御の辺は $`2 \to 3`$ で、下の辺は $`1 \to 2`$ だけである。$`m_0`$ は恒等写像なので、$`\mathrm{needs} = [((0), 1)]`$ である。これはもとのアトム $`((0), 1, 2)`$ から、$`\beta = f(2)`$ について成り立つ。
- 制御の辺のアトム $`((1), 1, 2)`$ は要求には入らない。制御関係 $`R((f(1)), f(1), f(2))`$ になる。$`\theta = (f(1))`$ である。
- 要求の鍵 $`(f(0))`$ は $`\theta = (f(1))`$ より小さい（§4 の仮定 5）。$`f(0) \lt f(1)`$ だからである。
- 有限反映（§4）で得る $`g`$ は、$`g(0) = f(0)`$、$`g(1) \lt f(1)`$ で、要求は上端 $`f(\mathrm{cut}) = f(1)`$ について成り立つ。つまり $`R((g(0)), g(1), f(1))`$ である。
- 新しい図式の列 2 には $`f(\mathrm{cut}) = f(1)`$ を付ける（§6）。ラベルは $`(g(0), g(1), f(1))`$ になる。$`(1, 2, 3)`$ の図式のアトムは $`((0), 0, 1)`$ と $`((0), 1, 2)`$ で、後者がちょうど上の要求である。こうして要求が、新しい図式の辺になる。

**定義（上界）.** $`n \in \mathbb N`$、関数 $`f : \mathrm{Fin}\ n \to \mathrm{Label}`$、$`\beta \in \mathrm{Label}`$ とする。$`i \lt n`$ ならいつも $`f(i) \lt \beta`$ のとき、$`f`$ は $`\beta`$ で **上から押さえられる** という。

## 4. 有限反映

**定義（鍵が θ より小さい要求）.** 鍵 $`\theta`$ と関数 $`f : \mathrm{Fin}\ n \to \mathrm{Label}`$ について、上端のアトム $`d = (t, p)`$ の **鍵が $`\theta`$ より小さい** とは、$`\mathrm{eval}\ t\ f \lt \theta`$ のことである。

1-Y 版の「許される要求」（低い層か、根が切れ目より前にあって根のラベルが $`\theta`$ より小さい）の代わりである。型板が指す列が切れ目より前にあることは要らない。

**例.** 展開のステップ 0（§3 の「展開のステップ」）を見る。$`\mathrm{cut}`$ と $`\theta`$ は根と制御の辺から決まる（§3 の「展開での要求」）。$`f`$ はもとの表現で、ラベルは列の順に大きくなる。

- $`(1, 2, 4)`$：根は $`(1, 2)`$ で、$`\mathrm{cut} = 1`$、$`\theta = (f(1))`$ である（§3 の例 2）。
- $`(1, 3)`$：$`x = 1`$、根は $`(0, 1)`$ で（[05](05-omegay-mountain.md) §4）、$`\mathrm{cut} = 0`$ である。制御の辺は列 1 の $`2 \to \omega`$ で、$`\theta = (f(0), \top)`$ である。下の辺は $`1 \to 2`$ だけなので、$`\mathrm{needs} = [((0, 0), 0)]`$ である。

| 式 | 上端のアトム $`(\bar t, p)`$ | 鍵 | $`\theta`$ より小さいか | 理由 |
|---|---|---|---|---|
| $`(1, 2, 4)`$ | $`((0), 1)`$ | $`(f(0))`$ | はい | $`f(0) \lt f(1)`$ |
| $`(1, 2, 4)`$ | $`((1), 1)`$ | $`(f(1))`$ | いいえ | $`\theta`$ と等しい |
| $`(1, 3)`$ | $`((0, 0), 0)`$ | $`(f(0), f(0))`$ | はい | 座標 0 が等しく、座標 1 で $`f(0) \lt \top`$ |
| $`(1, 3)`$ | $`((0, \top), 0)`$ | $`(f(0), \top)`$ | いいえ | $`\theta`$ と等しい |

小さくない 2 つは、どちらも制御の辺（$`((1), 1, 2)`$ と $`((0, \top), 0, 1)`$）から子を除いたものである。これらの辺は要求にせず、制御関係として渡す。

**定義（有限反映）.** 関係 $`R`$（§2）が **有限反映** を満たすとは、次が成り立つことをいう。

任意の図式 $`G`$、関数 $`f : \mathrm{Fin}\ n \to \mathrm{Label}`$、自然数 $`\mathrm{cut}`$、鍵 $`\theta`$、ラベル $`\beta`$、上端のアトムのリスト $`\mathrm{needs}`$ について、次の 6 つの仮定がすべて成り立つとする。

1. $`G`$ は図式で、サイズを $`n`$ とし、$`\mathrm{cut} \lt n`$ である。$`f`$ は $`G`$ の表現である。
2. $`f`$ は $`\beta`$ で上から押さえられる。
3. 制御関係（§3）$`R(\theta, f(\mathrm{cut}), \beta)`$ が成り立つ。
4. 要求のリスト $`\mathrm{needs}`$ の各要素は妥当である。
5. 各要素の鍵は $`\theta`$ より小さい。
6. 各要素は上端 $`\beta`$ について成り立つ。

このとき、次の 5 つを満たす関数 $`g : \mathrm{Fin}\ n \to \mathrm{Label}`$ がある。

1. $`g`$ は $`G`$ の表現である。
2. $`i \lt \mathrm{cut}`$ なら $`g(i) = f(i)`$。
3. $`g`$ は $`f(\mathrm{cut})`$ で上から押さえられる。
4. $`i \lt n`$ なら $`g(i) \le f(i)`$。
5. 各要求は上端 $`f(\mathrm{cut})`$ について成り立つ。

仮定 2 から $`f(i) \lt \beta \le \omega_1`$ なので、仮定 1 の「表現」のうち条件 1 は、仮定 2 から出る。結論 1 の条件 1 も、結論 3 から出る。

**意味.** 切れ目より左のラベルは動かさない。切れ目から右のラベルを付け替えて、全部を $`f(\mathrm{cut})`$ より下に入れる。辺の条件と、上端への要求（上端を $`\beta`$ から $`f(\mathrm{cut})`$ に替えたもの）は保つ。[04](04-patterns-of-resemblance.md) §3 の有限反映の形そのものである。1-Y 版と違い、要求の鍵が指す列は、切れ目より前でなくてよい。その列のラベルも付け替わる。

## 5. 3 つの定理

組合せの層の主定理（以下、**入口の定理**）が関係 $`R`$ について使うのは、次の 3 つの定理である。表の文字は $`\theta, \Theta \in \mathrm{Key}_m`$、$`a, b \in \mathrm{Label}`$ を動く。

| 名前 | 内容 |
|---|---|
| 鍵の弱化 | $`\theta \le \Theta`$ かつ $`R(\Theta, a, b)`$ なら $`R(\theta, a, b)`$ |
| 有限反映 | $`R`$ について §4 の有限反映が成り立つ |
| 初期表現 | どの図式 $`G`$（サイズ $`n`$）と、上端のアトムのリスト $`\mathrm{needs}`$ にも、ある $`\beta \lt \omega_1`$ と、$`\beta`$ で上から押さえられる $`G`$ の表現 $`f`$ があって、$`\mathrm{needs}`$ の各要素は上端 $`\beta`$ について成り立つ |

結論は「1 段の展開の関係は整礎である」（[05](05-omegay-mountain.md) §7 の定理 1）である。

1-Y 版の 6 つの仮定とは、次のように対応する。

| 1-Y 版の仮定 | ω-Y |
|---|---|
| 整礎性、推移性 | ラベルの順序は順序数の順序なので、仮定にしない（[01](01-ordinals.md) §1） |
| 狭義性 | 使わない。$`f(\mathrm{cut}) \lt \beta`$ は有限反映の仮定 2 から出る |
| 弱化 | 鍵の弱化。根のラベル $`\eta' \lt \eta`$ の代わりに、鍵 $`\theta \le \Theta`$ |
| 有限反映 | 有限反映 |
| 初期表現 | 初期表現。式の図式だけでなく、すべての図式と上端のアトムのリストについて |

## 6. 1 ブロックの継ぎ合わせ

有限反映 1 回で、図式を 1 ブロック長くする。§4 の 6 つの仮定を満たす $`G`$（サイズ $`n`$）、$`f`$、$`\mathrm{cut}`$、$`\theta`$、$`\beta`$、$`\mathrm{needs}`$ を取り、有限反映で得た $`g`$ を 1 つ決める。

**定義（列の写像）.** 新しい図式のサイズは $`n + (n - \mathrm{cut})`$ である。古い列 $`j \lt n`$ を、新しい列 $`\mathrm{mv}(j)`$ へ移す。

```math
\mathrm{mv}(j) := \begin{cases} j & (j \lt \mathrm{cut}) \cr n + (j - \mathrm{cut}) & (\mathrm{cut} \le j \lt n) \end{cases}
```

$`\mathrm{mv}`$ は狭義増加で、$`\mathrm{mv}(\mathrm{cut}) = n`$ である。列 $`j \lt n`$ は、動かさなければ新しい図式でも列 $`j`$ である。

**定義（継ぎ合わせたラベル）.**

```math
h(c) := \begin{cases} g(c) & (c \lt n) \cr f(\mathrm{cut} + c - n) & (n \le c \lt n + (n - \mathrm{cut})) \end{cases}
```

$`c \lt n`$ では $`h(c) = g(c)`$、$`j \lt n`$ では $`h(\mathrm{mv}(j)) = f(j)`$（$`j \lt \mathrm{cut}`$ では結論 2 の $`g(j) = f(j)`$ を使う）、特に $`h(n) = f(\mathrm{cut})`$ である。つまり右端に $`f(\mathrm{cut}), \ldots, f(n-1)`$ がそのまま並ぶ。

**例.** $`n = 4`$、$`\mathrm{cut} = 1`$ なら、$`f_j := f(j)`$、$`g_j := g(j)`$ として次のとおりである。

```math
h = (g_0, g_1, g_2, g_3, f_1, f_2, f_3), \qquad g_0 = f_0, \quad g_1 \lt g_2 \lt g_3 \lt f_1
```

**定理（1 ブロックの継ぎ合わせ）.** $`h`$ は狭義増加で、$`\beta`$ で上から押さえられる。サイズ $`n + (n - \mathrm{cut})`$ の図式 $`H`$ の各アトム $`e = (t, p, q)`$ が、次のどれかを満たすとする。

1. $`e \in G`$。
2. $`G`$ のアトム $`e' = (t', p', q')`$ があって、$`p = \mathrm{mv}(p')`$、$`q = \mathrm{mv}(q')`$、$`\bar t \le \overline{\mathrm{mv}\, t'}`$。
3. 要求 $`d = (t', p') \in \mathrm{needs}`$ があって、$`p = p'`$、$`q = n`$、$`\bar t \le \bar t'`$。

このとき $`h`$ は $`H`$ の表現である。

**証明.**

- 順序：$`c \lt c' \lt n`$ なら $`g`$ が狭義増加である。$`c \lt n \le c'`$ なら $`h(c) = g(c) \lt f(\mathrm{cut}) \le h(c')`$ である。$`n \le c \lt c'`$ なら $`f`$ が狭義増加である。
- 上界：$`g(c) \lt f(\mathrm{cut}) \lt \beta`$ で、$`f(j) \lt \beta`$ である。よって $`h(c) \lt \beta \le \omega_1`$ である。
- 1 のアトム：有限反映の結論 1 から、$`e`$ は $`g`$ で成り立つ。$`e`$ が読む列はどれも $`n`$ より小さく、そこで $`h = g`$ である。
- 2 のアトム：$`f`$ は $`G`$ の表現なので、$`R(\mathrm{eval}\ t'\ f, f(p'), f(q'))`$ である。性質 2 と $`h \circ \mathrm{mv} = f`$ から、$`\mathrm{eval}\ (\mathrm{mv}\, t')\ h = \mathrm{eval}\ t'\ f`$、$`h(p) = f(p')`$、$`h(q) = f(q')`$ である。性質 1 から $`\mathrm{eval}\ t\ h \le \mathrm{eval}\ (\mathrm{mv}\, t')\ h`$ である。鍵の弱化から $`R(\mathrm{eval}\ t\ h, h(p), h(q))`$ である。
- 3 のアトム：有限反映の結論 5 から、$`R(\mathrm{eval}\ t'\ g, g(p'), f(\mathrm{cut}))`$ である。$`h(n) = f(\mathrm{cut})`$ で、$`t'`$ と $`p'`$ が読む列では $`h = g`$ である。性質 1 から $`\mathrm{eval}\ t\ h \le \mathrm{eval}\ t'\ h`$ で、鍵の弱化から $`R(\mathrm{eval}\ t\ h, h(p), h(n))`$ である。$`\square`$

1-Y 版では、写したアトムの根が前のブロックへ移る場合と、要求の根が前のブロックにある場合に、弱化を使った。ω-Y では、2 と 3 で鍵の弱化を使う。

## 7. 予備を持つ反映のくり返し

この節では、$`s`$ を根 $`(z, d)`$ を持つ式、$`x`$ をその最後の列、$`L := x - z`$、$`D`$ を $`M(s)`$ の次元、$`f`$ を $`G_D(s)`$ の表現、$`\beta := f(x)`$ とする。$`e_c`$ は制御の辺、$`T_i`$ は §3 の要求のリストである。

**定義（予備）.** 次の 3 つを **予備** と呼ぶ。$`i \in \mathbb N`$ について、$`m_i`$ で写したものも使う。

```math
F := G_D(s[0]), \qquad T := T_0, \qquad c := \bigl(\kappa_D(e_c),\ z\bigr), \qquad F_i := m_i F, \quad c_i := m_i c = \bigl(m_i \kappa_D(e_c),\ z + iL\bigr)
```

- $`F`$ は内部の予備である。$`s[0] = (s_0, \ldots, s_{x-1})`$ なので、$`F`$ は $`G_D(s)`$ のサイズ $`x`$ の接頭辞で、$`M(s)`$ の列 $`x`$ より左の辺からなる。
- $`T = T_0`$ は上端の予備（下の辺）、$`c`$ は制御の辺である。$`T_i = m_i T`$ である。

**定義（ステップ $`i`$ の状態）.** ラベル $`f_i : \mathrm{Fin}\ (x + iL) \to \mathrm{Label}`$ が **ステップ $`i`$ の状態** であるとは、次の 5 つが成り立つことをいう。

1. $`f_i`$ は狭義増加で、$`\beta`$ で上から押さえられる。
2. $`G_D(s[i])`$ の各アトムが $`f_i`$ で成り立つ。
3. $`F_i`$ の各アトムが $`f_i`$ で成り立つ。
4. $`T_i`$ の各要素が上端 $`\beta`$ について成り立つ。
5. $`c_i`$ が上端 $`\beta`$ について成り立つ。つまり、制御関係 $`R\bigl(\mathrm{eval}\ (m_i \kappa_D(e_c))\ f_i,\ f_i(z + iL),\ \beta\bigr)`$ が成り立つ。

**補題（ブロックの辺の分類）.** $`i \in \mathbb N`$、$`n := x + iL`$ とする。$`G_D(s[i+1])`$ の各アトム $`e = (t, p, q)`$ は、次のどれかを満たす。

1. $`q \lt n`$ で、$`e \in G_D(s[i])`$。
2. $`F`$ のアトム $`(t', p', q')`$ があって、$`p = m_{i+1}(p')`$、$`q = m_{i+1}(q')`$、$`\bar t \le \overline{m_{i+1} t'}`$。
3. $`q = n`$ で、下の辺 $`e'`$（親 $`\pi'`$）があって、$`p = m_i(\mathrm{col}(\pi'))`$、$`\bar t \le \overline{m_i \kappa_D(e')}`$。

ここでは証明しない。2 は、$`e`$ を、$`F`$ の辺を $`i + 1`$ 回ずらして写し、鍵を弱めたものとして読むことである。列 $`n`$ の辺では、2 は根の列 $`z`$ の辺から来る。3 は、下の辺を $`i`$ 回ずらして、子を列 $`n`$ に付けたものである。2 と 3 は、[05](05-omegay-mountain.md) §4 の手順 1 の (T)、(C)、(F) と、weak magma の規則（[05](05-omegay-mountain.md) §5）を使う。公式の ω-Y では 2 が破れる（[notes/02-feasibility.md](../notes/02-feasibility.md) §3.1）。

この補題は、05 §3、§4 の式とこの節の定義を写した Python のプログラムで確かめた（2026-09-27）。種 $`(1, 2)`$、$`(1, 3)`$、$`(1, 4)`$、$`(1, 5)`$ から、展開（$`N = 0, 1, 2, 3`$）をくり返して届く長さ 5 以下の式のうち、最後の項が 1 でない 564 個について、$`i = 0, 1, 2`$ のすべてで成り立った（アトム 104607 個）。長さ 6 以下の式では、辞書式の順に 10884 個を $`i = 0, 1`$ で調べた（55 秒で打ち切った）。

**定理（予備を持つ反映の 1 回）.** $`f_i`$ がステップ $`i`$ の状態なら、ステップ $`i + 1`$ の状態 $`f_{i+1}`$ があり、$`f_{i+1}(\mathrm{mv}(j)) = f_i(j)`$ である。

**証明.** $`n := x + iL`$ とする。有限反映（§4）を次のように使う。

```math
G := G_D(s[i]) \cup F_i, \qquad \mathrm{needs} := T_i, \qquad \mathrm{cut} := z + iL, \qquad \theta := \mathrm{eval}\ (m_i \kappa_D(e_c))\ f_i
```

- 仮定 1、2：状態の 1、2、3 と、$`f_i(j) \lt \beta \le \omega_1`$ から。
- 仮定 3：状態の 5。
- 仮定 4：下の辺の親の列は $`x`$ より小さいので、$`m_i`$ で写すと $`n`$ より小さい。
- 仮定 5：性質 5。
- 仮定 6：状態の 4。

得た $`g`$ で、§6 の $`h`$ を作り、$`f_{i+1} := h`$ とする。$`n - \mathrm{cut} = L`$ なので、新しいサイズは $`x + (i+1)L`$ である。$`\mathrm{mv}`$ は、$`j \lt z + iL`$ を動かさず、$`j \ge z + iL`$ を $`j + L`$ へ移す。よって $`\mathrm{mv} \circ m_i = m_{i+1}`$ である。

1. §6 の定理から。
2. 補題の 3 つの場合が、§6 の定理の 3 つの場合になる。1 はそのまま（$`G_D(s[i]) \subseteq G`$）。2 では $`e' := m_i(t', p', q') \in F_i`$ を取ると、$`\mathrm{mv}\, e' = m_{i+1}(t', p', q')`$ である。3 では $`d := m_i\bigl(\kappa_D(e'), \mathrm{col}(\pi')\bigr) \in T_i`$ を取る。
3. $`F_{i+1} = \mathrm{mv}\, F_i`$ である。$`F_i`$ のアトムは $`f_i`$ で成り立ち、$`h \circ \mathrm{mv} = f_i`$ なので、性質 2 から、写したアトムは $`h`$ で成り立つ。
4. $`T_{i+1} = \mathrm{mv}\, T_i`$ で、3 と同じ理由で上端 $`\beta`$ について成り立つ。
5. $`c_{i+1} = \mathrm{mv}\, c_i`$ で、4 と同じである。$`\mathrm{mv}(z + iL) = n = z + (i+1)L`$ が次の切れ目である。$`\square`$

**定理（予備を持つ反映のくり返し）.** $`f`$ を列 $`x`$ より左に制限した $`f_0`$ は、ステップ 0 の状態である。よって、すべての $`i \in \mathbb N`$ で、ステップ $`i`$ の状態がある。

**証明.** $`m_0`$ は恒等写像である。

1. $`f`$ は狭義増加で、$`j \lt x`$ なら $`f(j) \lt f(x) = \beta`$。
2. と 3. $`G_D(s[0]) = F`$ は $`G_D(s)`$ の接頭辞で、型板は列 $`x`$ を指さない（性質 3）。よって $`f`$ で成り立つアトムは $`f_0`$ でも成り立つ。
4. 下の辺 $`e`$ のアトム $`(\kappa_D(e), \mathrm{col}(\pi), x)`$ は $`f`$ で成り立つ。つまり $`R(\mathrm{eval}\ \kappa_D(e)\ f, f(\mathrm{col}(\pi)), f(x))`$ で、これは上端のアトム $`(\kappa_D(e), \mathrm{col}(\pi))`$ が上端 $`\beta`$ について成り立つことである。
5. 制御の辺について、4 と同じである。

あとは、前の定理を $`i`$ についての帰納法で使う。$`\square`$

## 8. 末尾のラベルによる降下

**定義（末尾のラベル）.** サイズ $`n \gt 0`$ の図式の表現 $`f`$ について、最後の列のラベル $`f(n-1)`$ を $`f`$ の **末尾のラベル** と呼ぶ。

**定理（ラベルが末尾のラベルより下がる）.** $`s`$ を空でない式、$`D`$ を $`M(s)`$ の次元とし、$`G_D(s)`$ に末尾のラベル $`\beta`$ の表現があるとする。このとき、どの $`N \in \mathbb N`$ についても、$`G_D(s[N])`$ に、どのラベルも $`\beta`$ より小さい表現がある。

$`M(s[N])`$ の次元も $`D`$ である（[05](05-omegay-mountain.md) §7）。$`s[N]`$ は空でもよい。1-Y 版では「末尾のラベルが下がる」と述べたが、ここでは、すべてのラベルが $`\beta`$ より下にあることを述べる。

**証明の概略.** $`x`$ を $`s`$ の最後の列とし、$`f`$ を $`G_D(s)`$ の末尾のラベル $`\beta = f(x)`$ の表現とする。

1. 根が無いとき、または $`N = 0`$ のとき：$`s[N]`$ は $`s`$ から最後の列を消したものである。$`G_D(s[N])`$ は $`G_D(s)`$ のサイズ $`x`$ の接頭辞である。$`f`$ を列 $`x`$ より左に制限したものが表現で、ラベルはどれも $`f(x) = \beta`$ より小さい。
2. 根 $`(z, d)`$ があり、$`N \ge 1`$ のとき：
   - $`i = 0, 1, \ldots, N`$ について、$`G_D(s[i])`$ を $`i`$ 番目の図式と呼ぶ。サイズは $`x + iL`$ である。0 番目の図式は $`G_D(s)`$ のサイズ $`x`$ の接頭辞で、$`N`$ 番目の図式が目標の図式である。
   - 制御の辺は $`R(\mathrm{eval}\ \kappa_D(e_c)\ f, f(z), f(x))`$ を与える。これが最初の制御関係である。
   - 下の辺は、上端 $`\beta`$ への上端のアトムになる（§3 の例 1 と同じ作り方）。どのステップの図式も $`\beta`$ で上から押さえられるので、ラベル $`\beta`$ の列は図式に無い。それでこれらの上端のアトムは、図式の外の点 $`\beta`$ への辺として残る。
   - ステップ $`i`$（§3）で $`i`$ 番目の図式から $`i + 1`$ 番目の図式を作るときに、有限反映を 1 回使う（§7 の定理）。切れ目はブロック $`i`$ の始まり $`\mathrm{cut} = z + iL`$ である。1-Y 版では、要求をステップごとに新しい山から作った。ω-Y では、下の辺と、列 $`x`$ より左の辺をずらしたもの（予備）を毎回渡し、新しい辺はそこから鍵の弱化で出す（§6）。
   - $`N`$ 回くり返すと、ステップ $`N`$ の状態 $`f_N`$ ができる。状態の 1、2 から、$`f_N`$ は $`G_D(s[N])`$ の表現で、$`\beta`$ で上から押さえられる。$`\square`$

**3 つの定理の使いどころ.**

| 定理 | 使いどころ |
|---|---|
| 鍵の弱化 | §6 の定理の 2、3（写した辺と、要求から来る辺） |
| 有限反映 | ブロックごとに 1 回（§7） |
| 初期表現 | 帰納法の出発点（$`G = G_D(s)`$、$`\mathrm{needs}`$ は空） |

ラベルの順序が整礎であることは、帰納法で使う。

**整礎性.** [02](02-well-founded.md) §6 の定理（ラベルの上界による停止）を、$`D`$ ごとに次のように当てはめる。

| 一般形 | ω-Y |
|---|---|
| $`X`$ の元 | 山の次元が $`D`$ の式 $`s`$ |
| $`t \prec s`$ | 自明でない 1 段の展開（$`t = s[N] \ne s`$） |
| $`(L, \lt)`$ | ラベルの順序 $`(\mathrm{Label}, \lt)`$ |
| $`V(s, \alpha)`$ | $`G_D(s)`$ に、どのラベルも $`\alpha`$ より小さい表現がある |

- 1 つめの仮定：$`\alpha_0 := \omega_1`$。初期表現から、どの $`s`$ にも $`\beta \lt \omega_1`$ で上から押さえられる表現がある。
- 2 つめの仮定：$`V(s, \alpha)`$ で $`t \prec s`$ とする。$`s`$ は空でない。表現の末尾のラベル $`\alpha' := f(x)`$ は $`\alpha`$ より小さく、上の定理から $`V(t, \alpha')`$ である。$`t`$ の山の次元も $`D`$ である。

どの式 $`s`$ にも次元 $`D`$ がある（山の行は有限個なので、0 でない係数の指数の最大値を取る）。$`s`$ から届く式も次元 $`D`$ を持つ（[05](05-omegay-mountain.md) §7）ので、$`s`$ は $`\prec`$ について到達可能である（[02](02-well-founded.md) §1）。よって $`\prec`$ は整礎である（[05](05-omegay-mountain.md) §7 の定理 1）。

**例（$`(1, 3, 3)[2]`$）.** $`x = 2`$、根は $`(z, d) = (0, 1)`$、$`L = 2`$、$`D = 1`$ である。$`f_j := f(j)`$ と書く。

- 制御の辺は列 2 の辺 $`2 \to \omega`$ で、型板は $`(0, \top)`$、$`c = ((0, \top), 0)`$ である。下の辺は列 2 の辺 $`1 \to 2`$ で、$`T = [((0, 0), 0)]`$ である。$`\beta = f_2`$ である。
- 内部の予備は $`F = G_1((1, 3)) = [((0, 0), 0, 1),\ ((0, \top), 0, 1)]`$ である。
- ステップ 0 の状態：ラベル $`(f_0, f_1)`$。制御関係は $`R((f_0, \top), f_0, f_2)`$、$`T`$ は $`R((f_0, f_0), f_0, f_2)`$ である。
- ステップ 0：切れ目は 0 である。反映で $`g_0 \lt g_1 \lt f_0`$ を得る。新しいラベルは $`(g_0, g_1, f_0, f_1)`$ で、$`s[1] = (1, 3, 2, 5)`$ の図式を表現する。そのアトムの分類は次のとおりである。

| アトム $`(\bar t, p, q)`$ | 補題の場合 | 元 |
|---|---|---|
| $`((0, 0), 0, 1)`$、$`((0, \top), 0, 1)`$ | 1 | $`G_1((1, 3))`$ |
| $`((0, 0), 0, 2)`$ | 3 | 下の辺 $`((0, 0), 0)`$ |
| $`((0, 0), 2, 3)`$ | 2 | $`F`$ の $`((0, 0), 0, 1)`$ を $`m_1`$ で写すと $`((2, 2), 2, 3)`$。$`(0, 0) \le (2, 2)`$ |
| $`((2, 2), 2, 3)`$ | 2 | 同じ。型板は等しい |
| $`((2, \top), 2, 3)`$ | 2 | $`F`$ の $`((0, \top), 0, 1)`$ を $`m_1`$ で写したもの |

- ステップ 1：切れ目は 2 で、そのラベルは $`f_0`$ である。反映で $`g'_2 \lt g'_3 \lt f_0`$ を得る。列 0、1 は動かない。新しいラベルは $`(g_0, g_1, g'_2, g'_3, f_0, f_1)`$ である。

これが $`(1, 3, 3)[2] = (1, 3, 2, 5, 4, 9)`$ の表現で、どのラベルも $`f_2`$ より小さい。表の分類は、上の Python のプログラムで計算した。

## 9. 意味の層に残る仕事

組合せの層は、有限反映がなぜ成り立つかを問わない。§5 の 3 つの定理を満たす $`R`$ を与えるのが **意味の層** の仕事である。

- Phyrion 氏の意味の層：このリポジトリとは別の $`R`$ を与える。$`R(\theta, a, b)`$ は「$`b`$ より下の有限の正の図式を $`a`$ より下へ圧縮できる」ことである（[04](04-patterns-of-resemblance.md) §5、[notes/00-survey.md](../notes/00-survey.md) §3.2）。このリポジトリには含めない。
- このリポジトリの意味の層：$`R`$ は [07 関係 R](07-relation-r.md) の $`\Sigma_1`$ 初等部分構造の関係である。証明は [09 3 つの定理の証明](09-obligations.md) にある。

## 10. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md)「証明の形」 | 二層の構成と、3 つの定理の表 |
| [notes/01-design.md](../notes/01-design.md) §1 | 組合せの層が意味の層から使うもの |
| [notes/00-survey.md](../notes/00-survey.md) §3.2、§3.5 | 鍵、山の辺の鍵、次元の保存、1-Y との対応 |
| [notes/02-feasibility.md](../notes/02-feasibility.md) §3、§4 | 公式の ω-Y で、§7 の補題の 2 が破れること |

## 11. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| 鍵の構文 | `KeySyntax` | [OmegaY/Reflection/Interface.lean](../OmegaY/Reflection/Interface.lean) |
| アトム、上端のアトム | `InternalAtom`（`key`、`parent`、`child`）、`TopAtom`（`key`、`parent`） | 同上 |
| 成り立つ、鍵が $`\theta`$ より小さい、上界 | `InternalHolds`、`TopHolds`、`KeysBelow`、`Bounded` | 同上 |
| 鍵と型板 | `Keys.Key`、`Keys.Template`、`Keys.eval`、`Keys.eval_mono` | [OmegaY/Keys.lean](../OmegaY/Keys.lean) |
| $`\bar t`$、性質 1 | `Keys.templateKey`、`Keys.eval_lt_of_template_lt`、`Keys.eval_le_of_template_le` | 同上 |
| $`\mu t`$、性質 2 | `Keys.relabel`、`Keys.eval_relabel` | 同上 |
| 鍵の構文の実体 | `KeyReflection.vectorSyntax`、`Model.keySyntax`、`Model.R` | [OmegaY/KeyReflection.lean](../OmegaY/KeyReflection.lean)、[OmegaY/Model.lean](../OmegaY/Model.lean) |
| 尺度の根 | `scaleParent`、`scaleRoot`（尺度による単調性 `scaleRoot_scale_antitone`） | [OmegaY/Geometry/MountainKeys.lean](../OmegaY/Geometry/MountainKeys.lean) |
| 辺、次数、型板 $`\kappa_D`$、性質 3 | `RealStoredEdge`、`degree`、`degree_le`、`keyTemplate`、`keyTemplate_column_bound`、`atom` | 同上 |
| 次元 | `exists_key_dimension`、`MountainKeyDimension`、`KeyDimension` | 同上、[OmegaY/Expansion/SupportedDimension.lean](../OmegaY/Expansion/SupportedDimension.lean) |
| 性質 4 | `key_strict_in_column`、`topAtom_key_strict_in_column` | [OmegaY/Geometry/VerticalEdgeKeys.lean](../OmegaY/Geometry/VerticalEdgeKeys.lean)、[OmegaY/Geometry/TopEdgeKeys.lean](../OmegaY/Geometry/TopEdgeKeys.lean) |
| 山の表現 | `KeyRepresentation`、`keyRepresentation_exists`、`restrict`、`lastLabel`、`restrict_below_last` | [OmegaY/Geometry/RepresentedMountain.lean](../OmegaY/Geometry/RepresentedMountain.lean) |
| 3 つの定理（組合せの層が読む名前） | `Reflection.key_weaken`、`Reflection.finite_reflection`、`OrdinalSupply.initial_finite_graph`、`Model.key_weaken`、`Model.finite_reflection`、`Model.initial_finite_graph` | [OmegaY/Reflection.lean](../OmegaY/Reflection.lean)、[OmegaY/Reflection/OrdinalSupply.lean](../OmegaY/Reflection/OrdinalSupply.lean)、[OmegaY/Model.lean](../OmegaY/Model.lean) |
| §6 の $`\mathrm{mv}`$、$`h`$ | `Splice.width`、`old`、`moved`、`boundary`、`labels` | [OmegaY/Splice.lean](../OmegaY/Splice.lean) |
| §6 の定理 | `reflected_block`、`Classified`、`mapAtom`、`seamAtom`、`holds_weakened_copy`、`holds_seam`、`classified_graph_represented` | 同上 |
| 予備、状態、§7 の 1 回 | `mapTop`、`ReservoirState`、`DemandCovered`、`ReservoirClassified`、`holds_weakened_seam`、`splice_reservoirs` | [OmegaY/Splice/Reservoirs.lean](../OmegaY/Splice/Reservoirs.lean) |
| ブロックの番号（$`x + iL`$、$`z + iL`$、$`m_i`$） | `blockWidth`、`blockCut`、`blockSource`、`blockMoved` | [OmegaY/Splice/BlockIndices.lean](../OmegaY/Splice/BlockIndices.lean) |
| §7 のくり返し | `block_reservoir_step`、`iterated_reservoirs`、`BlockReservoirGeometry` | [OmegaY/Splice/IteratedReservoirs.lean](../OmegaY/Splice/IteratedReservoirs.lean) |
| 制御の辺と下の辺、性質 5 | `controlEdge`、`LowerEdge`、`controlAtom`、`lowerAtom`、`lower_key_strict`、`reflect_initial_control` | [OmegaY/Expansion/InitialControlKeys.lean](../OmegaY/Expansion/InitialControlKeys.lean) |
| 予備 $`F`$、$`T`$、$`c`$ と $`m_i`$ で写したもの | `initialSpliceFacts`、`initialSpliceVirtualFacts`、`initialSpliceControl`、`spliceGraph`、`spliceFacts`、`spliceVirtualFacts`、`spliceControl` | [OmegaY/Expansion/ActualSpliceFacts.lean](../OmegaY/Expansion/ActualSpliceFacts.lean) |
| ステップ 0 の状態 | `initial_reservoir`、`zero_reservoir` | [OmegaY/Expansion/ActualInitialReservoir.lean](../OmegaY/Expansion/ActualInitialReservoir.lean) |
| §7 の補題 | `actual_splice_edge_classified`（場合 1：`retained_splice_classified`、列 $`n`$：`boundary_splice_classified`、列 $`n`$ より右：`ordinary_splice_classified`） | [OmegaY/Expansion/ActualSpliceGeometry.lean](../OmegaY/Expansion/ActualSpliceGeometry.lean)、[OmegaY/Expansion/ActualBoundarySplice.lean](../OmegaY/Expansion/ActualBoundarySplice.lean)、[OmegaY/Expansion/ActualOrdinarySplice.lean](../OmegaY/Expansion/ActualOrdinarySplice.lean) |
| §7 の補題の 2 の中心 | `ActualCopiedKeyBound`、`Preparation.copied_edge_key_bound` | [OmegaY/Expansion/ActualCopiedKeyBound.lean](../OmegaY/Expansion/ActualCopiedKeyBound.lean)、[OmegaY/Expansion/ActualFillCopiedKey.lean](../OmegaY/Expansion/ActualFillCopiedKey.lean) |
| §8 の定理の 2 | `iterated_actual_reservoirs`、`representationOfSpliceGraph`、`represent_actual_expansion` | [OmegaY/Expansion/ActualSpliceRepresentation.lean](../OmegaY/Expansion/ActualSpliceRepresentation.lean) |
| §8 の定理の 1 | `expandDiagram_trivial_representation_descent` | [OmegaY/Geometry/RepresentedMountain.lean](../OmegaY/Geometry/RepresentedMountain.lean) |
| §8 の定理 | `ActualRepresentationDescent`、`actual_representation_descent` | [OmegaY/Expansion/DynamicsRepresentationRank.lean](../OmegaY/Expansion/DynamicsRepresentationRank.lean)、[OmegaY/Expansion/ActualRepresentationDescent.lean](../OmegaY/Expansion/ActualRepresentationDescent.lean) |
| 整礎性 | `RepresentationDescent`、`accessible_of_representation_below`、`empty_accessible`、`step_wellFounded_of_actual_representation_descent` | [OmegaY/Expansion/DynamicsRepresentationRank.lean](../OmegaY/Expansion/DynamicsRepresentationRank.lean) |
| 3 つの定理の呼び出し元（`grep` で探した。`Reflection.lean`、`Reflection/`、`KeyReflection.lean`、`Model.lean` を除く） | 鍵の弱化：`Splice.holds_weakened_copy`、`DemandCovered.top_holds`、`holds_weakened_seam`、`ActualCopiedKeyBound.represented`。有限反映：`Splice.reflected_block`、`Splice.splice_reservoirs`、`RootGeometry.reflect_initial_control`。初期表現：`actual_keys_initially_represented`（要求のリストは空） | [OmegaY/Splice.lean](../OmegaY/Splice.lean)、[OmegaY/Splice/Reservoirs.lean](../OmegaY/Splice/Reservoirs.lean)、[OmegaY/Expansion/ActualCopiedKeyLabels.lean](../OmegaY/Expansion/ActualCopiedKeyLabels.lean)、[OmegaY/Expansion/InitialControlKeys.lean](../OmegaY/Expansion/InitialControlKeys.lean)、[OmegaY/Geometry/MountainKeys.lean](../OmegaY/Geometry/MountainKeys.lean) |
| §1〜§3 の定義を Phyrion 氏のものから変えずに移したこと | `Reflection` の名前空間のインターフェース | [OmegaY/Reflection/Interface.lean](../OmegaY/Reflection/Interface.lean)、[NOTICE](../NOTICE) |
