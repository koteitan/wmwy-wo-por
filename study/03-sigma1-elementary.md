[← Back](README.md) | [English](en/03-sigma1-elementary.md) | [Japanese](03-sigma1-elementary.md)

# 構造と Σ₁ 初等部分構造

前提

| ノート | ここで使う言葉 |
|---|---|
| [01 順序数と ω₁](01-ordinals.md) | 順序数、極限順序数、$`\{x \mid x \lt \gamma\}`$、ラベルの型、$`\mathrm{Fin}\ n`$、位置 |
| [02 整礎関係と整礎再帰](02-well-founded.md) | 鍵 $`\mathrm{Key}_m`$ とその順序、上端、ガード |

このノートは、関係 $`R`$ の定義に使うモデル論の言葉を説明する。一階の構造、$`\Sigma_1`$ 論理式、$`\Sigma_1`$ 初等部分構造、Tarski–Vaught の判定法である。後半（§7、§8）は、Lean がそれらをどう表すかを説明する。

## 1. 言語と構造

**定義（言語）.** **言語** は関係記号の集まりで、各記号に引数の数が決まっている。このリポジトリでは関数記号と定数記号は使わない。

**定義（構造）.** 言語 $`L`$ の **構造** $`\mathfrak A`$ は、空でもよい集合 $`A`$（領域）と、各記号 $`P`$（引数の数 $`n`$）の解釈 $`P^{\mathfrak A} \subseteq A^n`$ の組である。

**記法.** 構造を $`(A; P_1, P_2, \ldots)`$ と書く。

- セミコロンの左 $`A`$ は領域である。左に順序数 $`\gamma`$ を書いたときは、領域は $`\{x \mid x \lt \gamma\}`$ である。
- セミコロンの右は、各記号の解釈を並べたものである。記号とその解釈は同じ文字で書く。
- 右の関係は、領域に制限して読む。

例：$`(4; \lt)`$ の領域は $`\{0, 1, 2, 3\}`$ で、関係は $`\{0, 1, 2, 3\}`$ の上の $`\lt`$ である。

| 言語 | 構造 | 領域 |
|---|---|---|
| $`\{\lt\}`$ | $`(\omega; \lt)`$ | 自然数 |
| $`\{\lt\}`$ | $`(\gamma; \lt)`$ | $`\{x \mid x \lt \gamma\}`$ |
| $`\{\lt, E\}`$（$`E`$ は引数が 2 つの記号） | $`(\omega; \lt, E)`$、$`E(x, y) :\iff y = x + 1`$ | 自然数 |

このリポジトリの構造は、どれも領域が $`\{x \mid x \lt \gamma\}`$ の形である。$`\gamma`$ を構造の **高さ** と呼ぶ。

## 2. 論理式と Σ₁ 論理式

**定義（論理式）.** 論理式は次のように作る。

- **原子式**：$`P(x_1, \ldots, x_n)`$（$`P`$ は引数が $`n`$ 個の記号、$`x_i`$ は変数）。
- 論理式を $`\neg, \land, \lor, \to`$ でつないだもの。
- 論理式に $`\exists x`$、$`\forall x`$ を付けたもの。

**定義（量化子の無い論理式）.** 量化子 $`\exists`$、$`\forall`$ を含まない論理式である。

**定義（Σ₁ 論理式）.** 量化子の無い論理式 $`\psi`$ に、存在量化子だけを前に付けた形

```math
\exists y_1 \cdots \exists y_k\ \psi(\vec p, y_1, \ldots, y_k)
```

の論理式を **$`\Sigma_1`$ 論理式** と呼ぶ。$`k`$ は自然数である。$`\vec p`$ は自由変数の列で、あとで領域の元（**パラメータ**）を入れる。

| 論理式 | 種類 |
|---|---|
| $`p \lt q`$ | 量化子なし（$`\Sigma_1`$ でもある。$`k = 0`$） |
| $`\exists y\ (p \lt y)`$ | $`\Sigma_1`$ |
| $`\exists y\ \exists z\ (p \lt y \land y \lt z \land E(y, z))`$ | $`\Sigma_1`$ |
| $`\forall y\ (y \lt p \lor p \lt y \lor y = p)`$ | $`\Sigma_1`$ でない |

**定義（充足）.** 構造 $`\mathfrak A`$ と、パラメータの列 $`\vec p`$（各成分が $`A`$ の元。これを $`\vec p \in A`$ と書く）について、$`\mathfrak A \models \varphi(\vec p)`$ は「$`\varphi`$ が $`\mathfrak A`$ で $`\vec p`$ について真」を表す。量化子 $`\exists y`$ は領域 $`A`$ の元を走る。$`\mathfrak A \models \exists \vec y\ \psi(\vec p, \vec y)`$ のとき、$`\psi(\vec p, \vec y)`$ を真にする $`\vec y`$（$`A`$ の元の列）を **証人** と呼ぶ。

例：$`(\omega; \lt) \models \exists y\ (3 \lt y)`$ は真。$`(4; \lt) \models \exists y\ (3 \lt y)`$ は偽。$`(4; \lt)`$ の領域は $`\{0, 1, 2, 3\}`$ だからである。

## 3. リテラルの連言

**定義（リテラル）.** 原子式か、原子式の否定を **リテラル** と呼ぶ。

**事実（選言標準形）.** 量化子の無い論理式は、リテラルの連言の有限個の選言と同値である。存在量化子は選言の上に配れる。

```math
\exists \vec y\ (\psi_1 \lor \psi_2) \iff \exists \vec y\ \psi_1 \ \lor\ \exists \vec y\ \psi_2
```

したがって、どの $`\Sigma_1`$ 論理式も、「存在量化子とリテラルの連言」の形の論理式の有限個の選言と同値である。2 つの構造で、この形の論理式の真偽がすべて一致すれば、すべての $`\Sigma_1`$ 論理式の真偽が一致する。

**例.** $`\exists y\ \bigl((p \lt y \land \neg(y \lt q)) \lor E(p, y)\bigr)`$ は $`\exists y\ (p \lt y \land \neg(y \lt q)) \lor \exists y\ E(p, y)`$ と同値である。

**等号.** $`\lt`$ が線形順序なら、等号は要らない。$`x = y \iff \neg(x \lt y) \land \neg(y \lt x)`$ である。

このリポジトリの論理式は、この「存在量化子とリテラルの連言」の形だけである（§7）。

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
- $`\alpha`$ が極限のとき：$`\Sigma_1`$ 論理式 $`\exists \vec y\ \psi(\vec p, \vec y)`$ が $`\beta`$ で真だとする。その証人 $`\vec y`$ を、パラメータとの位置関係を保ったまま $`\alpha`$ の中に置き直す。
  - $`\vec p`$ の最大値より下にある証人は、もともと $`\alpha`$ の中にある。そのままでよい。
  - 最大値より上にある証人は有限個である（パラメータが無いときは、すべての証人をこちらに数える）。$`\alpha`$ が極限なので、最大値より上に $`\alpha`$ の元は無限個ある（[01](01-ordinals.md) §2）。同じ順に並べて置き直せる。
  - 置き直しても、$`\lt`$ の真偽は変わらない。よって $`\psi`$ は $`\alpha`$ で真である。
  - 逆向きは §4 の性質 2 である。$`\square`$

$`\alpha = 0`$ も除かれる。$`\exists y\ \neg(y \lt y)`$ は空の構造 $`0`$ で偽、$`\beta`$ で真である。

## 6. Tarski–Vaught の判定法（Σ₁ 版）

$`\Sigma_1`$ 初等性を示すには、下向きだけを確かめればよい。

**定理（Tarski–Vaught 判定法、Σ₁ 版）.** $`\mathfrak A`$ を $`\mathfrak B`$ の部分構造とする。次の 2 つは同値である。

1. $`\mathfrak A \preccurlyeq_{\Sigma_1} \mathfrak B`$。
2. 量化子の無い $`\psi`$ と $`\vec p \in A`$ について、$`\mathfrak B \models \exists \vec y\ \psi(\vec p, \vec y)`$ なら、ある $`\vec y \in A`$ で $`\mathfrak B \models \psi(\vec p, \vec y)`$ である。

**証明.** 1 から 2：$`\mathfrak A`$ で真になるので、$`A`$ に証人がある。§4 の性質 1 から $`\mathfrak B`$ でも $`\psi`$ が真である。2 から 1：上向きは §4 の性質 2 である。下向きは、2 の証人が $`A`$ にあり、性質 1 から $`\mathfrak A \models \psi(\vec p, \vec y)`$ となることから出る。$`\square`$

一般の Tarski–Vaught 判定法は、すべての論理式について同じことを言う。このリポジトリは $`\Sigma_1`$ だけを使う。

**使い方.** 2 の条件は「$`A`$ が証人で閉じている」ことである。[08 閉包と Good な点](08-closure-chain.md) の `lam_good` はこの形で示す。$`\gamma`$ から始めて、真の主張の証人を足していき、上限を取る。

## 7. Lean での Σ₁ 論理式

Lean の論理式は [Por/Formula.lean](../Por/Formula.lean) にある。次の 3 つを固定する。

- $`\mathrm{Label}`$：ラベルの型。線形順序である。[01](01-ordinals.md) §6 のラベルの型はその例である。
- $`\mathrm{Key}`$：鍵の型。線形順序である。[02](02-well-founded.md) §3 の $`\mathrm{Key}_m`$ はその例である。
- `S : KeySyntax Label Key`：**鍵の構文**。次の 3 つの組である。
  - `S.Template n`：$`n`$ 変数の **型板** の型。
  - `S.eval t v`：型板 $`t`$ を変数の値 $`v : \mathrm{Fin}\ n \to \mathrm{Label}`$ で評価した鍵。
  - `S.monotone_eval`：`S.eval` は各点で単調である。つまり、すべての $`i`$ で $`w_i \le v_i`$ なら $`\mathrm{eval}\ t\ w \le \mathrm{eval}\ t\ v`$ である。

ω-Y での型板は [06](06-combinatorial-layer.md) §1 で説明する。そこでは、型板は鍵の各座標に $`\mathrm{some}\ i`$（変数 $`v_i`$ の値を置く）か $`\mathrm{none}`$（$`\top`$ を置く）を書いた列である。

**言語.** 変数を $`v_0, \ldots, v_{n-1}`$ とし、$`\vec v = (v_0, \ldots, v_{n-1})`$ と書く。番号 $`i`$ は変数の位置（[01](01-ordinals.md) §7）である。記号は 3 種類である。

- 順序 $`\lt`$。
- 型板 $`t`$ と位置 $`i, j`$ ごとの **内部の関係** $`\mathrm{Rel}_{t,i,j}(\vec v)`$。2 つの点 $`v_i, v_j`$ の間の関係である。
- 型板 $`t`$ と位置 $`i`$ ごとの **上端の述語** $`\mathrm{Top}_{t,i}(\vec v)`$。点 $`v_i`$ から構造の高さ $`c`$（上端、[02](02-well-founded.md) §3）への関係である。$`c`$ 自身は領域に無い。

$`\mathrm{Rel}_{t,i,j}`$ と $`\mathrm{Top}_{t,i}`$ の鍵は $`\mathrm{eval}\ t\ v`$ である。つまり鍵は変数の値で決まる。2 つの記号の意味は [07](07-relation-r.md) §2 で与える。このノートでは、それらの解釈を引数として受け取る（`Lit.Holds`）。

**定義（`Lit n`）.** $`n`$ 変数のリテラルは次の 3 種類である。$`i, j`$ は位置、$`t`$ は型板である。`pos = true` が肯定、`pos = false` が否定である。

| Lean | 読み方 | 鍵 |
|---|---|---|
| `Lit.lt i j pos` | $`v_i \lt v_j`$ | なし |
| `Lit.rel t i j pos` | $`\mathrm{Rel}_{t,i,j}(\vec v)`$、鍵は $`\mathrm{eval}\ t\ v`$ | $`\mathrm{eval}\ t\ v`$ |
| `Lit.top t i pos` | $`\mathrm{Top}_{t,i}(\vec v)`$、鍵は $`\mathrm{eval}\ t\ v`$ | $`\mathrm{eval}\ t\ v`$ |

**定義（`Form`）.** 論理式は 3 つ組 $`(n, \mathit{fixed}, \mathit{lits})`$ である。

| 成分 | 意味 |
|---|---|
| $`n`$ | 変数の数 |
| $`\mathit{fixed} : \mathrm{Fin}\ n \to \mathrm{Bool}`$ | 真の位置がパラメータ、偽の位置が存在量化する変数 |
| $`\mathit{lits}`$ | リテラルのリスト。論理式はその連言 |

**定義（`Lit.Holds`）.** リテラルが変数の値 $`v : \mathrm{Fin}\ n \to \mathrm{Label}`$ で成り立つことを定める。3 つの解釈を受け取る。$`\kappa`$ は鍵、$`x, y`$ はラベルである。`rel κ x y` は「鍵 $`\kappa`$ の内部の関係が $`x, y`$ の間で成り立つ」、`top κ x` は「鍵 $`\kappa`$ の上端の述語が $`x`$ で成り立つ」、`allow κ` は「鍵 $`\kappa`$ の上端の述語が定義されている」ことである。

```math
\begin{aligned}
\mathrm{lt}\ i\ j\ \mathit{pos} &: \quad (v_i \lt v_j) \iff \mathit{pos}, \cr
\mathrm{rel}\ t\ i\ j\ \mathit{pos} &: \quad \mathrm{rel}(\mathrm{eval}\ t\ v, v_i, v_j) \iff \mathit{pos}, \cr
\mathrm{top}\ t\ i\ \mathit{pos} &: \quad \mathrm{allow}(\mathrm{eval}\ t\ v) \ \land\ \bigl(\mathrm{top}(\mathrm{eval}\ t\ v, v_i) \iff \mathit{pos}\bigr).
\end{aligned}
```

**定義（`Sat`）.** $`c`$ をラベル、$`\varphi = (n, \mathit{fixed}, \mathit{lits})`$ を論理式、$`p : \mathrm{Fin}\ n \to \mathrm{Label}`$ とする。`Sat rel top allow c φ p` は「高さ $`c`$ の構造で、$`\varphi`$ がパラメータ $`p`$ について真」である。

```math
\mathrm{Sat}(c, \varphi, p) \iff \exists v\ \Bigl(\forall i\ (\mathit{fixed}_i \to v_i = p_i)\Bigr) \land \Bigl(\forall i\ \ v_i \lt c\Bigr) \land \Bigl(\forall \ell \in \mathit{lits}\ \ \ell \text{ が } v \text{ で成り立つ}\Bigr)
```

$`p`$ は長さ $`n`$ の列だが、読むのはパラメータの位置だけである。条件 $`v_i \lt c`$ が「領域は $`\{x \mid x \lt c\}`$」を表す。パラメータの位置でも $`v_i = p_i \lt c`$ が要る。

**例.** $`\varphi = (2,\ (\mathrm{true}, \mathrm{false}),\ [\mathrm{lt}\ 0\ 1\ \mathrm{true}])`$ は $`\exists v_1\ (p_0 \lt v_1)`$ である。ラベルが順序数なら、$`\mathrm{Sat}(c, \varphi, p)`$ は $`p_0 + 1 \lt c`$ と同じである。

## 8. 2 つの構造の比べ方と、部分的な上端述語

このリポジトリの比べ方には、教科書の定義と違う点が 2 つある。

**違い 1：同じ記号を別に解釈する.** 関係 $`R`$ の定義では、高さ $`a`$ の構造と高さ $`b`$ の構造を比べる（[07](07-relation-r.md)）。上端の述語は、高さ $`a`$ では「$`a`$ への関係」、高さ $`b`$ では「$`b`$ への関係」と解釈する。したがって、そのままでは部分構造ではない。

そこで `ElemL` は、部分構造であることを仮定しない。パラメータが $`a`$ より下のすべての論理式で、真偽が一致することだけを要求する。$`\theta`$ は鍵、$`a, b`$ はラベルである。$`\varphi`$ は論理式を、$`p : \mathrm{Fin}\ n \to \mathrm{Label}`$（$`n`$ は $`\varphi`$ の変数の数）はパラメータの列を動く。式では、`Sat` の引数のうち、上端の述語の解釈と高さだけを書く。

```math
\mathrm{ElemL}(\theta, a, b) \iff \forall \varphi\ \forall p\ \Bigl(\bigl(\forall i\ (\mathit{fixed}_i \to p_i \lt a)\bigr) \implies \bigl(\mathrm{Sat}(\mathrm{top}_A, a, \varphi, p) \iff \mathrm{Sat}(\mathrm{top}_B, b, \varphi, p)\bigr)\Bigr)
```

Lean では `ElemL rel topA topB θ a b` である。内部の関係の解釈 `rel` は 2 つの構造で共通で、上端の述語の解釈は高さ $`a`$ では `topA`、高さ $`b`$ では `topB` である。両方の `Sat` の `allow` は $`\kappa \mapsto \kappa \lt \theta`$ である。すべての変数がパラメータの論理式（量化子の無い論理式）を取ると、$`a`$ より下の点についてのリテラルの真偽が一致する。上端のリテラルも、定義されている鍵では一致する。したがって一致が言えれば、$`a`$ より下の点の上では 2 つの構造の解釈が同じで、高さ $`a`$ の構造は高さ $`b`$ の構造の部分構造になり、しかも $`\Sigma_1`$ 初等である。

**違い 2：上端の述語は部分的である.** 上端の述語は、鍵が $`\theta`$ より小さいところでだけ定義される。上端のリテラルは、定義されているときだけ真になりうる。肯定のリテラルも否定のリテラルも同じである。

**例.** 鍵の長さを $`m = 1`$（[02](02-well-founded.md) §3）とし、$`\theta = (5)`$（座標 0 がラベル 5 の鍵）とする。変数は $`v_0, v_1`$ の 2 つで、型板は §7 の ω-Y の形である。型板 $`t = (\mathrm{some}\ 0)`$ は鍵 $`(v_0)`$ を与え、型板 $`t_\top = (\mathrm{none})`$ は鍵 $`(\top)`$ を与える。

| リテラル | $`v = (3, 10)`$ | $`v = (7, 10)`$ |
|---|---|---|
| `top t 1 true` | $`\mathrm{top}((3), 10)`$ と同じ | 偽（鍵 $`(7)`$ は $`\theta`$ 以上） |
| `top t 1 false` | $`\neg\,\mathrm{top}((3), 10)`$ と同じ | 偽 |
| `top t_⊤ 1 true` | 偽（鍵 $`(\top)`$ は $`\theta`$ 以上） | 偽 |

**1-Y 版との違い.** 1-Y 版（[01](01-ordinals.md) §7）は、上端の述語が定義されるかどうかを、変数の位置だけで決めた。このリポジトリでは、定義されるかどうかは鍵の値 $`\mathrm{eval}\ t\ v`$ で決まる。つまり変数の値に依る。そのため、次の 2 つの補題が要る。

- `Lit.holds_allow_mono`：`allow` を広げても、成り立つリテラルは成り立ったままである。
- `Lit.holds_of_le`：$`\theta, \Theta`$ を鍵とし、$`w \le v`$（各点）とする。$`v`$ でリテラルが `allow` $`= (\cdot \lt \theta)`$ の下で成り立ち、$`w`$ で同じリテラルが（別の解釈と）`allow` $`= (\cdot \lt \Theta)`$ の下で成り立つとする。このとき $`w`$ で `allow` $`= (\cdot \lt \theta)`$ の下でも成り立つ。上端のリテラルなら、$`\mathrm{eval}\ t\ w \le \mathrm{eval}\ t\ v \lt \theta`$（`S.monotone_eval`）だからである。ほかのリテラルは `allow` を読まない。

2 つめの補題は、「証人を各点で下げても、鍵の条件 $`\lt \theta`$ は残る」ことを言う。[07](07-relation-r.md) の鍵の弱化と [09](09-obligations.md) の `top_abs` で使う。

**読むところだけで決まる.** `Lit.holds_congr` と `sat_congr` は次のことを言う。2 つの解釈が、内部の関係では第 2 の点が高さ $`c`$ より下のところで一致し、上端の述語では定義されている鍵で一致するなら、真偽も一致する。論理式は、それ以外のところを読まないからである。[07](07-relation-r.md) の `R_iff` で、ガード（[02](02-well-founded.md) §5）を外すのに使う。

## 9. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md)「関係 R」 | $`\preccurlyeq_{\Sigma_1}`$ と、部分的な上端の述語 |
| [notes/01-design.md](../notes/01-design.md) §2.1、§2.2 | 構造と論理式 |
| [notes/01-design.md](../notes/01-design.md) §3.3 | Tarski–Vaught の形での Good な点 |
| [Por/Formula.lean](../Por/Formula.lean) | §7、§8 のすべて |
| [Por/Supply.lean](../Por/Supply.lean) | §6（`lam_good`） |

## 10. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| 鍵の構文 | `KeySyntax`（`Template`、`eval`、`monotone_eval`） | [OmegaY/Reflection/Interface.lean](../OmegaY/Reflection/Interface.lean) |
| リテラル | `Lit`（`lt`、`rel`、`top`） | [Por/Formula.lean](../Por/Formula.lean) |
| 論理式 | `Form`（`n`、`fixed`、`lits`） | 同上 |
| リテラルの真偽 | `Lit.Holds` | 同上 |
| $`\Sigma_1`$ 論理式が真 | `Sat` | 同上 |
| $`\theta`$ より下で定義された初等性 | `ElemL` | 同上 |
| 読むところが同じなら同じ | `Lit.holds_congr`、`sat_congr` | 同上 |
| `allow` を広げる | `Lit.holds_allow_mono` | 同上 |
| 各点で下げても鍵の条件が残る | `Lit.holds_of_le` | 同上 |
