[← Back](README.md) | [English](en/03-sigma1-elementary.md) | [Japanese](03-sigma1-elementary.md)

# 構造と Σ₁ 初等部分構造

前提

| ノート | ここで使う言葉 |
|---|---|
| [01 順序数と ω₁](01-ordinals.md) | 順序数、極限順序数、$`\{x \mid x \lt \gamma\}`$、ラベル $`\mathrm{Label}`$（§6）、$`\mathrm{Fin}\ n`$、$`\mathrm{Option}`$（§7） |
| [02 整礎関係と整礎再帰](02-well-founded.md) | 鍵 $`\mathrm{Key}_m`$ とその順序、$`\top`$、上端（§3） |

このノートは、関係 $`R`$ の定義に使うモデル論の言葉を説明する。一階の構造、$`\Sigma_1`$ 論理式、$`\Sigma_1`$ 初等部分構造、Tarski–Vaught の判定法である。§7、§8 は、このリポジトリで使う $`\Sigma_1`$ 論理式の標準形と、2 つの構造の比べ方を説明する。

## 1. 言語と構造

**定義（言語）.** **言語** は関係記号の集まりで、各記号に引数の数が決まっている。このリポジトリでは関数記号と定数記号は使わない。

**定義（構造）.** 言語 $`L`$ の **構造** $`\mathfrak A`$ は、空でもよい集合 $`A`$（領域）と、各記号 $`P`$（引数の数 $`n`$）の解釈 $`P^{\mathfrak A} \subseteq A^n`$ の組である。

**記法.** 構造を $`(A; P_1, \ldots, P_k)`$ と書く。

- セミコロンの左 $`A`$ は領域である。
- セミコロンの右は、各記号の解釈を言語の順に並べたものである。記号とその解釈は同じ文字で書く。
- 左に順序数 $`\gamma`$ を書いたときは、領域は $`\{x \mid x \lt \gamma\}`$ である。
- 右の関係は領域に制限して読む。たとえば $`(\gamma; \le)`$ の $`\le`$ は $`\{(x, y) \mid x, y \lt \gamma,\ x \le y\}`$ である。

例：$`(4; \lt)`$ の領域は $`\{0, 1, 2, 3\}`$ で、関係は $`\{0, 1, 2, 3\}`$ の上の $`\lt`$ である。

| 言語 | 構造 | 領域 |
|---|---|---|
| $`\{\lt\}`$ | $`(\omega; \lt)`$ | 自然数 |
| $`\{\lt\}`$ | $`(\gamma; \lt)`$ | $`\{x \mid x \lt \gamma\}`$ |
| $`\{\lt, E\}`$（$`E`$ は 2 引数の記号） | $`(\omega; \lt, E)`$、$`E(x, y) :\iff y = x + 1`$ | 自然数 |

このリポジトリの構造は、どれも領域が $`\{x \mid x \lt \gamma\}`$ の形である。$`\gamma`$ を構造の **高さ** と呼ぶ。領域の元を **点** と呼ぶ。

## 2. 論理式と Σ₁ 論理式

**定義（論理式）.** 論理式は次のように作る。

- **原子式**：$`P(x_1, \ldots, x_n)`$（$`P`$ は $`n`$ 引数の記号、$`x_i`$ は変数）。
- 論理式を $`\neg, \land, \lor, \to`$ でつないだもの。
- 論理式に $`\exists x`$、$`\forall x`$ を付けたもの。

**定義（量化子の無い論理式）.** 量化子 $`\exists`$、$`\forall`$ を含まない論理式である。

**定義（Σ₁ 論理式）.** 量化子の無い論理式 $`\psi`$ に、存在量化子だけを前に付けた形

```math
\exists y_1 \cdots \exists y_{\mathit{bb}}\ \psi(\vec p, y_1, \ldots, y_{\mathit{bb}})
```

の論理式を **$`\Sigma_1`$ 論理式** と呼ぶ。$`\mathit{bb} \in \mathbb N`$ は存在量化する変数の数である。$`\vec p`$ は自由変数で、あとで領域の元（**パラメータ**）を入れる。矢印を付けた文字 $`\vec p`$、$`\vec y`$ は、有限個の変数（または元）の列を表す。

| 論理式 | 種類 |
|---|---|
| $`p \lt q`$ | 量化子なし（$`\Sigma_1`$ でもある。$`\mathit{bb} = 0`$） |
| $`\exists y\ (p \lt y)`$ | $`\Sigma_1`$ |
| $`\exists y\ \exists z\ (p \lt y \land y \lt z \land E(y, z))`$ | $`\Sigma_1`$ |
| $`\forall y\ (y \lt p \lor p \lt y \lor y = p)`$ | $`\Sigma_1`$ でない |

**定義（充足）.** 構造 $`\mathfrak A`$ と、パラメータ $`\vec p \in A`$（各成分が $`A`$ の元）について、$`\mathfrak A \models \varphi(\vec p)`$ は「$`\varphi`$ が $`\mathfrak A`$ で $`\vec p`$ について真」を表す。量化子 $`\exists y`$ は領域 $`A`$ の元を走る。

例：$`(\omega; \lt) \models \exists y\ (3 \lt y)`$ は真。$`(4; \lt) \models \exists y\ (3 \lt y)`$ は偽。$`(4; \lt)`$ の領域は $`\{0, 1, 2, 3\}`$ だからである。

**定義（証人）.** $`\mathfrak A \models \exists \vec y\ \psi(\vec p, \vec y)`$ のとき、$`\psi(\vec p, \vec y)`$ を真にする $`A`$ の元の列 $`\vec y`$ を **証人** と呼ぶ。

## 3. リテラルの連言

**定義（リテラル）.** 原子式か、原子式の否定を **リテラル** と呼ぶ。

量化子の無い論理式は、リテラルの連言の有限個の選言と同値である（選言標準形）。存在量化子は選言の上に配れる。

```math
\exists \vec y\ (\psi_1 \lor \psi_2) \iff \exists \vec y\ \psi_1 \ \lor\ \exists \vec y\ \psi_2
```

したがって、どの $`\Sigma_1`$ 論理式も、次の形の論理式の有限個の選言と同値である。

```math
\exists \vec y\ (\ell_1 \land \cdots \land \ell_k) \qquad (\ell_1, \ldots, \ell_k \text{ はリテラル})
```

2 つの構造で、この形の論理式の真偽がすべて一致すれば、すべての $`\Sigma_1`$ 論理式の真偽が一致する。

**例.** 言語 $`\{\lt, E\}`$ で、$`\exists y\ \bigl((p \lt y \land \neg(y \lt q)) \lor E(p, y)\bigr)`$ は $`\exists y\ (p \lt y \land \neg(y \lt q)) \lor \exists y\ E(p, y)`$ と同値である。

- $`\lt`$ が線形順序なら、等号は $`\lt`$ から決まる。$`v_a = v_b \iff \neg(v_a \lt v_b) \land \neg(v_b \lt v_a)`$ である。等号の記号は要らない。

## 4. 部分構造と、上への保存

**定義（部分構造）.** $`\mathfrak A`$ が $`\mathfrak B`$ の **部分構造** であるとは、$`A \subseteq B`$ で、各記号の解釈が制限になっていることをいう。つまり $`\vec a \in A`$ について $`P^{\mathfrak A}(\vec a) \iff P^{\mathfrak B}(\vec a)`$ である。

**性質 1.** 部分構造では、$`A`$ の元についての量化子の無い論理式の真偽が一致する。原子式の真偽が同じだからである。

**性質 2（Σ₁ は上に保存される）.** 部分構造で、$`\mathfrak A \models \exists \vec y\ \psi(\vec p, \vec y)`$ なら $`\mathfrak B \models \exists \vec y\ \psi(\vec p, \vec y)`$ である。$`\mathfrak A`$ の証人 $`\vec y`$ は $`B`$ にもあり、性質 1 から $`\psi`$ の真偽も同じだからである。

**逆は成り立たない.** $`(4; \lt)`$ は $`(\omega; \lt)`$ の部分構造である。$`\exists y\ (3 \lt y)`$ は $`\omega`$ で真、$`4`$ で偽である。

## 5. Σ₁ 初等部分構造

**定義（Σ₁ 初等部分構造）.** $`\mathfrak A`$ が $`\mathfrak B`$ の **$`\Sigma_1`$ 初等部分構造** であるとは、$`\mathfrak A`$ が $`\mathfrak B`$ の部分構造で、すべての $`\Sigma_1`$ 論理式 $`\varphi`$ とすべてのパラメータ $`\vec p \in A`$ について次が成り立つことをいう。

```math
\mathfrak A \models \varphi(\vec p) \iff \mathfrak B \models \varphi(\vec p)
```

これを $`\mathfrak A \preccurlyeq_{\Sigma_1} \mathfrak B`$ と書く。

**意味.** $`A`$ の元だけを使って述べられる「こういう有限個の元がある」という主張は、$`\mathfrak B`$ で真なら $`\mathfrak A`$ でも真である。証人を $`A`$ の中で取り直せる。

**例（順序だけの言語）.** $`0 \lt \alpha \lt \beta`$ を順序数とする。

```math
(\alpha; \lt) \preccurlyeq_{\Sigma_1} (\beta; \lt) \iff \alpha \text{ は極限順序数}
```

**証明.**

- $`\alpha = \gamma + 1`$ のとき：パラメータ $`\gamma`$ の $`\exists y\ (\gamma \lt y)`$ は $`\beta`$ で真（$`y = \gamma + 1`$）、$`\alpha`$ で偽である。よって成り立たない。
- $`\alpha`$ が極限のとき：$`\Sigma_1`$ 論理式 $`\exists \vec y\ \psi(\vec p, \vec y)`$ が $`\beta`$ で真だとする。その証人 $`\vec y`$ を、パラメータとの大小関係を保ったまま $`\alpha`$ の中に置き直す。
  - $`\vec p`$ の最大値より下にある証人は、もともと $`\alpha`$ の中にある。そのままでよい。
  - 最大値より上にある証人は有限個である（パラメータが無いときは、すべての証人をこちらに数える）。$`\alpha`$ が極限なので、最大値より上に $`\alpha`$ の元は無限個ある（[01](01-ordinals.md) §2）。同じ順に並べて置き直せる。
  - 置き直しても、$`\lt`$ の原子式の真偽は変わらない。よって $`\psi`$ は $`\alpha`$ で真である。
  - 逆向きは §4 の性質 2 である。$`\square`$

$`\alpha = 0`$ も除かれる。$`\exists y\ \neg(y \lt y)`$ は空の構造 $`0`$ で偽、$`\beta`$ で真である。

## 6. Tarski–Vaught の判定法（Σ₁ 版）

$`\Sigma_1`$ 初等性を示すには、下向きだけを確かめればよい。

**定理（Tarski–Vaught 判定法、Σ₁ 版）.** $`\mathfrak A`$ を $`\mathfrak B`$ の部分構造とする。次の 2 つは同値である。

1. $`\mathfrak A \preccurlyeq_{\Sigma_1} \mathfrak B`$。
2. 量化子の無い $`\psi`$ と $`\vec p \in A`$ について、$`\mathfrak B \models \exists \vec y\ \psi(\vec p, \vec y)`$ なら、ある $`\vec y \in A`$ で $`\mathfrak B \models \psi(\vec p, \vec y)`$ である。

**証明.** 1 から 2：$`\mathfrak A`$ で真になるので、$`A`$ に証人がある。§4 の性質 1 から $`\mathfrak B`$ でも $`\psi`$ が真である。2 から 1：上向きは §4 の性質 2 である。下向きは、2 の証人が $`A`$ にあり、性質 1 から $`\mathfrak A \models \psi(\vec p, \vec y)`$ となることから出る。$`\square`$

一般の Tarski–Vaught 判定法は、すべての論理式について同じことを言う。このリポジトリは $`\Sigma_1`$ だけを使う。

**使い方.** 2 の条件は「$`A`$ が証人で閉じている」ことである。[08 閉包と鎖](08-closure-chain.md) §6 の定理（λ(γ) は Good）はこの形で示す。$`\gamma`$ から始めて、真の主張の証人を足していき、上限を取る。

## 7. Σ₁ 論理式の標準形

このリポジトリの言語は、$`\lt`$ と、記号 $`\mathrm{Rel}_{t,i,j}`$ と、記号 $`\mathrm{Top}_{t,i}`$ からなる。添字 $`t`$ は型板、$`i, j`$ は位置で、どちらも下で定義する。記号の解釈は [07](07-relation-r.md) §2 で定める。ここでは次のことだけを使う。

- 高さ $`c`$ の構造では、$`\mathrm{Rel}_{t,i,j}`$ は点どうしの関係である。
- 高さ $`c`$ の構造では、$`\mathrm{Top}_{t,i}`$ は、点から、領域の外にある $`c`$ への関係である。[07](07-relation-r.md) §2 で、この $`c`$ は $`R`$ の上端（[02](02-well-founded.md) §3）になる。$`\mathrm{Top}_{t,i}`$ を **上端述語** と呼ぶ。上端述語の解釈は、高さ $`c`$ ごとに違う。
- どちらの記号も、鍵を 1 つ持つ。鍵は、変数の値から型板で計算する。

**定義（鍵の構文）.** $`K`$ を鍵の集合とする。このリポジトリでは $`K = \mathrm{Key}_m`$（[02](02-well-founded.md) §3）である。**鍵の構文** は次の 3 つの組である。

- 各 $`n \in \mathbb N`$ について、集合 $`\mathcal T_n`$。その元を $`n`$ 変数の **型板** と呼ぶ。
- 各 $`n`$ について、関数 $`\mathrm{eval} : \mathcal T_n \times (\mathrm{Fin}\ n \to \mathrm{Label}) \to K`$。$`\mathrm{eval}(t, \vec v)`$ を $`\mathrm{eval}\ t\ \vec v`$ と書き、型板 $`t`$ を変数の値 $`\vec v`$ で評価した鍵と呼ぶ。
- 単調性：各点で小さい値は、小さい鍵を与える。

```math
\forall t \in \mathcal T_n\ \ \forall \vec v, \vec w\ \ \Bigl(\bigl(\forall i \lt n\ \ w_i \le v_i\bigr) \implies \mathrm{eval}\ t\ \vec w \le \mathrm{eval}\ t\ \vec v\Bigr)
```

**例（ω-Y の鍵の構文）.** $`K = \mathrm{Key}_m`$、$`\mathcal T_n := \mathrm{Fin}\ m \to \mathrm{Option}(\mathrm{Fin}\ n)`$ とし、鍵の座標 $`i`$ を次で決める。

```math
(\mathrm{eval}\ t\ \vec v)_i := \begin{cases} v_j & (t_i = \mathrm{some}\ j) \cr \top & (t_i = \mathrm{none}) \end{cases}
```

$`m = 2`$、$`n = 3`$ なら、$`t = (\mathrm{some}\ 0, \mathrm{none})`$ は鍵 $`(v_0, \top)`$ を、$`t' = (\mathrm{some}\ 0, \mathrm{some}\ 2)`$ は鍵 $`(v_0, v_2)`$ を与える。各座標は $`v_j`$ か $`\top`$ なので、単調性が成り立つ。$`\mathcal T_n`$ は $`(n+1)^m`$ 個の元を持つ有限集合である。[06](06-combinatorial-layer.md) §1 はこの鍵の構文を使う。

**定義（位置）.** $`n`$ 変数の論理式の変数を $`v_0, \ldots, v_{n-1}`$ と並べ、$`\vec v = (v_0, \ldots, v_{n-1})`$ と書く。番号 $`i`$ を変数 $`v_i`$ の **位置** と呼ぶ。

**定義（リテラル）.** $`n`$ 変数のリテラルは次の 6 種類である。$`i, j`$ は位置、$`t \in \mathcal T_n`$ は型板である。

| リテラル | 鍵 |
|---|---|
| $`v_i \lt v_j`$、$`\neg(v_i \lt v_j)`$ | なし |
| $`\mathrm{Rel}_{t,i,j}`$、$`\neg\mathrm{Rel}_{t,i,j}`$ | $`\mathrm{eval}\ t\ \vec v`$ |
| $`\mathrm{Top}_{t,i}`$、$`\neg\mathrm{Top}_{t,i}`$ | $`\mathrm{eval}\ t\ \vec v`$ |

**定義（標準形）.** $`\Sigma_1`$ 論理式を 3 つ組 $`\varphi = (n, F, L)`$ で表す。

| 成分 | 意味 |
|---|---|
| $`n \in \mathbb N`$ | 変数の数 |
| $`F \subseteq \mathrm{Fin}\ n`$ | パラメータの位置の集合。$`F`$ に無い位置の変数は存在量化する |
| $`L`$ | リテラルの有限リスト。論理式はその連言 |

**定義（構造）.** このリポジトリの構造を次の形で書く。

```math
\mathfrak A = (c;\ \lt,\ \mathrm{rel},\ \mathrm{top},\ \mathrm{allow})
```

- $`c \in \mathrm{Label}`$ は高さで、領域は $`\{x \mid x \lt c\}`$ である。
- $`\mathrm{rel}(\kappa, x, y)`$（$`\kappa \in K`$、$`x, y \in \mathrm{Label}`$）は、記号 $`\mathrm{Rel}_{t,i,j}`$ の解釈を 1 つにまとめたものである。$`\mathrm{Rel}_{t,i,j}(\vec v) :\iff \mathrm{rel}(\mathrm{eval}\ t\ \vec v,\ v_i,\ v_j)`$。
- $`\mathrm{top}(\kappa, x)`$ は、記号 $`\mathrm{Top}_{t,i}`$ の解釈を 1 つにまとめたものである。$`\mathrm{Top}_{t,i}(\vec v) :\iff \mathrm{top}(\mathrm{eval}\ t\ \vec v,\ v_i)`$。
- $`\mathrm{allow}(\kappa)`$ は、「鍵 $`\kappa`$ の上端述語が **定義されている**」ことを表す鍵の条件である。意味は §8 で述べる。

**定義（リテラルの真偽）.** 値の列 $`\vec v \in (\mathrm{Fin}\ n \to \mathrm{Label})`$ でリテラル $`\ell`$ が成り立つことを $`\vec v \models \ell`$ と書く。$`\kappa := \mathrm{eval}\ t\ \vec v`$ と置く。

```math
\begin{aligned}
\vec v \models v_i \lt v_j &\iff v_i \lt v_j, \cr
\vec v \models \mathrm{Rel}_{t,i,j} &\iff \mathrm{rel}(\kappa, v_i, v_j), \cr
\vec v \models \mathrm{Top}_{t,i} &\iff \mathrm{allow}(\kappa) \ \land\ \mathrm{top}(\kappa, v_i), \cr
\vec v \models \neg\mathrm{Top}_{t,i} &\iff \mathrm{allow}(\kappa) \ \land\ \neg\,\mathrm{top}(\kappa, v_i).
\end{aligned}
```

$`\neg(v_i \lt v_j)`$ と $`\neg\mathrm{Rel}_{t,i,j}`$ は、それぞれ上の 1 行目、2 行目の否定である。$`\neg\mathrm{Top}_{t,i}`$ は 3 行目の否定ではない。$`\mathrm{allow}(\kappa)`$ が偽なら、$`\mathrm{Top}_{t,i}`$ も $`\neg\mathrm{Top}_{t,i}`$ も偽である。

**定義（充足）.** $`\varphi = (n, F, L)`$ と $`\vec p \in (\mathrm{Fin}\ n \to \mathrm{Label})`$ について、次で定める。

```math
\mathfrak A \models \varphi(\vec p) \iff \exists \vec v \in (\mathrm{Fin}\ n \to \mathrm{Label})\ \Bigl(\bigl(\forall i \in F\ \ v_i = p_i\bigr) \land \bigl(\forall i \lt n\ \ v_i \lt c\bigr) \land \bigl(\forall \ell \in L\ \ \vec v \models \ell\bigr)\Bigr)
```

- $`\vec p`$ は長さ $`n`$ の列だが、読むのは $`F`$ の位置だけである。
- 条件 $`v_i \lt c`$ が「領域は $`\{x \mid x \lt c\}`$」を表す。$`F`$ の位置でも $`p_i = v_i \lt c`$ が要る。
- $`F`$ に無い位置の $`v_i`$ が証人である。

**例.** $`\varphi = (2, \{0\}, [v_0 \lt v_1])`$ は $`\exists v_1\ (p_0 \lt v_1)`$ である。高さ $`c`$ で真であることは、$`p_0 + 1 \lt c`$ と同じである（$`c`$ が 8 未満の自然数の場合を Python で確かめた）。

## 8. 2 つの構造の比べ方と、部分的な上端述語

このリポジトリの比べ方には、教科書の定義と違う点が 2 つある。

**違い 1：同じ記号を別に解釈する.** 関係 $`R`$ の定義（[07](07-relation-r.md) §4）では、高さ $`a`$ の構造と高さ $`b`$ の構造（$`a \lt b`$ はラベル）を比べる。上端述語 $`\mathrm{Top}_{t,i}`$ は、高さ $`a`$ では「$`a`$ への関係」、高さ $`b`$ では「$`b`$ への関係」と解釈する。したがって、そのままでは部分構造ではない。

そこでこの比べ方は、部分構造であることを仮定しない。パラメータが $`a`$ より下のすべての $`\Sigma_1`$ 論理式で、真偽が一致することだけを要求する。

**定義（比べ方）.** 2 つの構造は、高さと上端述語の解釈だけが違うとする。

```math
\mathfrak A = (a;\ \lt,\ \mathrm{rel},\ \mathrm{top}_a,\ \mathrm{allow}), \qquad \mathfrak B = (b;\ \lt,\ \mathrm{rel},\ \mathrm{top}_b,\ \mathrm{allow})
```

```math
\mathfrak A \preccurlyeq_{\Sigma_1} \mathfrak B \ :\iff\ \forall \varphi = (n, F, L)\ \ \forall \vec p\ \ \Bigl(\bigl(\forall i \in F\ \ p_i \lt a\bigr) \implies \bigl(\mathfrak A \models \varphi(\vec p) \iff \mathfrak B \models \varphi(\vec p)\bigr)\Bigr)
```

$`F = \mathrm{Fin}\ n`$（量化子なし）の場合を取ると、$`a`$ より下の点についてのリテラルの真偽が一致する。上端述語のリテラルも、$`\mathrm{allow}`$ が真の鍵で一致する。したがって一致が言えれば、上端述語を $`\mathrm{allow}`$ が真の鍵に制限したとき、小さい方の構造は大きい方の部分構造になっていて、しかも $`\Sigma_1`$ 初等である。

**違い 2：上端述語は部分的である.** 上端述語は、$`\mathrm{allow}`$ が真の鍵でだけ定義される。§7 のとおり、$`\mathrm{allow}(\kappa)`$ が偽のところでは、$`\mathrm{Top}_{t,i}`$ も $`\neg\mathrm{Top}_{t,i}`$ も偽である。

| 条件 $`\mathrm{allow}(\kappa)`$ | 定義される上端述語 | 使う場所 |
|---|---|---|
| いつも真 | すべて | 高さ $`\omega_1`$ の構造（[08](08-closure-chain.md) §1 で定義する Good） |
| $`\kappa \lt \theta`$ | 鍵が $`\theta`$ より小さいもの | 構造 $`\mathfrak A^c_\theta`$（[07](07-relation-r.md) §3 で定義する） |

**例.** 鍵の長さを $`m = 1`$、$`\theta = (5)`$（座標 0 がラベル 5 の鍵）、$`\mathrm{allow}(\kappa) :\iff \kappa \lt \theta`$ とする。変数は $`v_0, v_1`$ の 2 つで、型板は §7 の ω-Y の鍵の構文のものである。$`t = (\mathrm{some}\ 0)`$ は鍵 $`(v_0)`$ を、$`t_\top = (\mathrm{none})`$ は鍵 $`(\top)`$ を与える。

| リテラル | $`\vec v = (3, 10)`$ | $`\vec v = (7, 10)`$ |
|---|---|---|
| $`\mathrm{Top}_{t,1}`$ | $`\mathrm{top}((3), 10)`$ と同じ | 偽（鍵 $`(7)`$ は $`\theta`$ 以上） |
| $`\neg\mathrm{Top}_{t,1}`$ | $`\neg\,\mathrm{top}((3), 10)`$ と同じ | 偽 |
| $`\mathrm{Top}_{t_\top,1}`$ | 偽（鍵 $`(\top)`$ は $`\theta`$ 以上） | 偽 |

表の値は、§7 の定義を Python で書いて、$`\mathrm{top}((3), 10)`$ が真の場合と偽の場合の両方で確かめた。

**1-Y 版との違い.** 1-Y 版（[01](01-ordinals.md) §7）の 03 §8 は、上端述語を読めるかどうかを、変数の位置だけで決めた。このリポジトリでは、定義されるかどうかは鍵の値 $`\mathrm{eval}\ t\ \vec v`$ で決まる。つまり変数の値に依る。そのため、次の 3 つの補題を使う。

**補題 1（読むところが同じなら同じ真偽）.** 高さ $`c`$ と $`\mathrm{allow}`$ が同じ 2 つの構造 $`(c; \lt, \mathrm{rel}, \mathrm{top}, \mathrm{allow})`$ と $`(c; \lt, \mathrm{rel}', \mathrm{top}', \mathrm{allow})`$ が次を満たすとする。

```math
\forall \kappa\ \forall x\ \forall y \lt c\ \ \bigl(\mathrm{rel}(\kappa, x, y) \iff \mathrm{rel}'(\kappa, x, y)\bigr), \qquad \forall \kappa\ \forall x\ \ \bigl(\mathrm{allow}(\kappa) \implies (\mathrm{top}(\kappa, x) \iff \mathrm{top}'(\kappa, x))\bigr)
```

このとき、すべての $`\varphi`$ と $`\vec p`$ で、2 つの構造での真偽は一致する。

**証明.** 値の列 $`\vec v`$ はどれも $`c`$ より下なので、$`\mathrm{Rel}`$ のリテラルは $`y \lt c`$ のところだけを読む。上端述語のリテラルは、$`\mathrm{allow}(\kappa)`$ が偽ならどちらでも偽で、真なら同じ値を読む。$`\square`$

**補題 2（allow を広げる）.** $`\forall \kappa\ (\mathrm{allow}(\kappa) \implies \mathrm{allow}'(\kappa))`$ とする。$`\mathrm{allow}`$ の下で $`\vec v \models \ell`$ なら、$`\mathrm{allow}'`$ の下でも $`\vec v \models \ell`$ である。

**証明.** $`\mathrm{allow}`$ を読むのは上端述語のリテラルだけで、そこでは $`\mathrm{allow}(\kappa)`$ から $`\mathrm{allow}'(\kappa)`$ が出る。$`\square`$

**補題 3（各点で下げても鍵の条件が残る）.** $`\theta, \Theta`$ を鍵、$`\vec w, \vec v`$ を値の列で、$`\forall i \lt n\ \ w_i \le v_i`$ とする。リテラル $`\ell`$ について、次の 2 つを仮定する。

- $`\vec v \models \ell`$（解釈 $`\mathrm{rel}, \mathrm{top}`$、$`\mathrm{allow}(\kappa) :\iff \kappa \lt \theta`$）。
- $`\vec w \models \ell`$（解釈 $`\mathrm{rel}', \mathrm{top}'`$、$`\mathrm{allow}(\kappa) :\iff \kappa \lt \Theta`$）。

このとき $`\vec w \models \ell`$（解釈 $`\mathrm{rel}', \mathrm{top}'`$、$`\mathrm{allow}(\kappa) :\iff \kappa \lt \theta`$）である。

**証明.** 上端述語のリテラルなら、鍵の構文の単調性（§7）から $`\mathrm{eval}\ t\ \vec w \le \mathrm{eval}\ t\ \vec v \lt \theta`$ である。ほかのリテラルは $`\mathrm{allow}`$ を読まない。$`\square`$

補題 1 は [07](07-relation-r.md) §6 でガード（[02](02-well-founded.md) §5）を外すのに使う。補題 2、3 は [07](07-relation-r.md) §7 の弱化と [09](09-obligations.md) で使う。

## 9. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md)「関係 R」 | $`\preccurlyeq_{\Sigma_1}`$、リテラルの連言に存在量化を付けた論理式、部分的な上端述語（§7、§8） |
| [README](../README.md)「3 つの定理の証明」 | Tarski–Vaught の形での Good な点（§6）、各点で下げても鍵が $`\theta`$ 未満のまま（§8 補題 3） |
| [notes/01-design.md](../notes/01-design.md) §2.1、§2.2 | 構造と論理式 |
| [notes/01-design.md](../notes/01-design.md) §3.3 | Tarski–Vaught の形での Good な点 |

## 10. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| 鍵の構文 | `KeySyntax`（`Template`、`eval`、`monotone_eval`） | [OmegaY/Reflection/Interface.lean](../OmegaY/Reflection/Interface.lean) |
| ω-Y の鍵の構文 | `Keys.Template m n`、`Keys.eval`、`Keys.eval_mono`、`KeyReflection.vectorSyntax m`、`Model.keySyntax m` | [OmegaY/Keys.lean](../OmegaY/Keys.lean)、[OmegaY/KeyReflection.lean](../OmegaY/KeyReflection.lean)、[OmegaY/Model.lean](../OmegaY/Model.lean) |
| リテラル | `Lit n`（`lt i j pos`、`rel t i j pos`、`top t i pos`。`pos = false` が否定） | [Por/Formula.lean](../Por/Formula.lean) |
| 標準形 $`(n, F, L)`$ | `Form`（`n`、`fixed : Fin n → Bool`、`lits`）。$`F = \{i \mid \mathit{fixed}_i = \mathrm{true}\}`$ | 同上 |
| リテラルの真偽 $`\vec v \models \ell`$ | `Lit.Holds rel top allow v` | 同上 |
| 充足 $`(c; \lt, \mathrm{rel}, \mathrm{top}, \mathrm{allow}) \models \varphi(\vec p)`$ | `Sat rel top allow c φ p` | 同上 |
| 比べ方（§8。$`\mathrm{allow}(\kappa) :\iff \kappa \lt \theta`$） | `ElemL rel topA topB θ a b` | 同上 |
| 補題 1 | `Lit.holds_congr`、`sat_congr` | 同上 |
| 補題 2 | `Lit.holds_allow_mono` | 同上 |
| 補題 3 | `Lit.holds_of_le` | 同上 |
