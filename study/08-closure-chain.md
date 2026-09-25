[← Back](README.md) | [English](en/08-closure-chain.md) | [Japanese](08-closure-chain.md)

# ω₁ より下の閉包と Good な点の列

前提

| ノート | ここで使う言葉 |
|---|---|
| [01 順序数と ω₁](01-ordinals.md) | $`\omega_1`$、正則性、ラベルの型、`Input`、`toP` |
| [03 構造と Σ₁ 初等部分構造](03-sigma1-elementary.md) | 証人、パラメータ、Tarski–Vaught 判定法、鍵の構文 $`S`$、型板、`Form`、`Sat` |
| [07 関係 R](07-relation-r.md) | $`R`$、$`\mathrm{Rel}_{t,i,j}`$、$`\mathrm{Top}_{t,i}`$、`relR`、`topR`、$`\vec p \lt a`$ |

このノートは、$`\omega_1`$ より下に、$`\Sigma_1`$ の証人で閉じた点（§1 の Good な点）を作る方法を説明する。これは Löwenheim–Skolem の定理と同じ考え方で、証人を足して上限を取る。できた点を並べた列が、[09](09-obligations.md) で最初のラベルになる。Lean のファイルは [Por/Supply.lean](../Por/Supply.lean) である。このノートでは、鍵の構文 $`S`$ の型板の型（[03](03-sigma1-elementary.md) §7）が可算であることを仮定する（`[∀ n, Countable (S.Template n)]`）。ω-Y の型板の型は有限である（`Keys.template_countable`）。

## 1. 周りの構造と Good

**定義（周りの構造）.** 高さ $`\omega_1`$ で、上端の述語をすべての鍵で定義した構造を $`\mathfrak B`$ とする。記号 $`\mathrm{Rel}_{t,i,j}`$、$`\mathrm{Top}_{t,i}`$ は [07](07-relation-r.md) §2 のものである。

```math
\mathfrak B = \bigl(\omega_1;\ \lt,\ (\mathrm{Rel}_{t,i,j}),\ (\mathrm{Top}^{\omega_1}_{t,i})\bigr), \qquad \mathrm{Top}^{\omega_1}_{t,i}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ \omega_1)
```

Lean では、$`\mathfrak B`$ での真偽は `Sat (relR S) (topR S top) (fun _ => True) top φ p` である。`top` はラベル $`\omega_1`$ である（[01](01-ordinals.md) §6）。`allow` がいつも真なので、どの上端のリテラルも定義されている。

**定義（Good）.** $`\alpha`$ をラベルとする。$`\mathfrak B{\restriction}\alpha`$ を、$`\mathfrak B`$ の領域を $`\{x \mid x \lt \alpha\}`$ に制限したものとする。上端の述語は $`\omega_1`$ へのもののままである。ラベル $`\alpha`$ が **Good** であるとは、次が成り立つことをいう。$`\varphi`$ は論理式、$`\vec p \lt \alpha`$ はパラメータを動く。

```math
\mathrm{Good}(\alpha) :\iff \forall \varphi\ \forall \vec p \lt \alpha\ \bigl(\mathfrak B \models \varphi(\vec p) \implies \mathfrak B{\restriction}\alpha \models \varphi(\vec p)\bigr)
```

Lean の `Good α` はこの形である。$`\mathfrak B{\restriction}\alpha`$ は $`\mathfrak B`$ の本当の部分構造である（解釈が同じで、領域だけが違う）。逆向きの含意はいつも成り立つ（証人 $`\lt \alpha`$ は $`\lt \omega_1`$）。したがって [03](03-sigma1-elementary.md) §6 の Tarski–Vaught 判定法から、$`\mathrm{Good}(\alpha)`$ は $`\mathfrak B{\restriction}\alpha \preccurlyeq_{\Sigma_1} \mathfrak B`$ と同じである。Good な点は、$`\mathfrak B`$ で真の $`\Sigma_1`$ の主張の証人を自分より下に持つ。

## 2. 論理式は可算個

**定理（`form_countable`）.** 論理式の型 `Form S` は可算である。

**証明.** リテラルを、組の直和への単射で符号にする（`litCode`、`litCode_inj`）。

| リテラル | 符号 |
|---|---|
| `lt i j pos` | $`(i, j, \mathit{pos})`$ |
| `rel t i j pos` | $`(t, i, j, \mathit{pos})`$ |
| `top t i pos` | $`(t, i, \mathit{pos})`$ |

各成分の型（`Fin n`、`Bool`、`S.Template n`）は可算なので、リテラルの型は可算である（`lit_countable`）。論理式は依存和 $`(n, \mathit{fixed}, \mathit{lits})`$ への単射で符号にする（`formCode`、`formCode_inj`）。自然数、有限の型の上の関数、可算な型のリストは、どれも可算である。$`\square`$

型板の型が可算であることが要る。1 つの論理式は有限個の型板しか使わないが、論理式の全体が可算であるためには、型板の全体が可算でなければならない。

## 3. 証人の高さ

**定義（`wh`）.** 論理式 $`\varphi`$ とパラメータ $`\vec p`$ について、**証人の高さ** $`\mathrm{wh}(\varphi, \vec p)`$ を次で定める。$`n`$ は $`\varphi`$ の変数の数である。

- $`\mathfrak B \models \varphi(\vec p)`$ なら、証人 $`v`$ を 1 組選び（`Classical.choose`）、$`\mathrm{wh}(\varphi, \vec p) := \sup_{i \lt n} (v_i + 1)`$ とする。
- そうでなければ $`\mathrm{wh}(\varphi, \vec p) := 0`$ とする。

| 定理 | 内容 | 理由 |
|---|---|---|
| `wh_lt` | $`\mathrm{wh}(\varphi, \vec p) \lt \omega_1`$ | 有限個の $`v_i + 1 \lt \omega_1`$ の上限（[01](01-ordinals.md) §5） |
| `wit_lt_wh` | 選んだ証人はどれも $`\mathrm{wh}(\varphi, \vec p)`$ より下 | `Ordinal.lt_iSup_add_one` |

## 4. 閉包の 1 段

**定義（`next`）.** $`\gamma`$ をラベルとする。$`\mathrm{nextO}(\gamma)`$ は順序数、$`\mathrm{next}(\gamma)`$ はラベルである。

```math
\mathrm{nextO}(\gamma) := \max\Bigl(\gamma + 1,\ \sup_{q \in \mathrm{Input}(\gamma)} \mathrm{wh}\bigl(q_\varphi, \mathrm{toP}(q)\bigr)\Bigr), \qquad \mathrm{next}(\gamma) := \min\bigl(\mathrm{nextO}(\gamma), \omega_1\bigr)
```

上限は、$`\gamma`$ より下のパラメータを持つすべての論理式 $`q \in \mathrm{Input}(\gamma)`$ を動く（[01](01-ordinals.md) §7）。入力 $`q = (\varphi, q')`$ について、$`q_\varphi := \varphi`$ は論理式の成分、$`\mathrm{toP}(q) := \mathrm{toP}(q')`$ はパラメータの列である。$`\min`$ はラベルの型に入れるためのもので、$`\gamma \lt \omega_1`$ なら $`\mathrm{next}(\gamma) = \mathrm{nextO}(\gamma)`$ である（`next_val`）。

| 定理 | 内容 | 理由 |
|---|---|---|
| `lt_next` | $`\gamma \lt \omega_1 \implies \gamma \lt \mathrm{next}(\gamma)`$ | $`\gamma + 1`$ の項 |
| `next_lt` | $`\gamma \lt \omega_1 \implies \mathrm{next}(\gamma) \lt \omega_1`$ | `Input` は可算で、可算個の上限（`nextO_lt`） |
| `wit_below` | $`\gamma \lt \omega_1`$、$`\vec p \lt \gamma`$、$`\mathfrak B \models \varphi(\vec p)`$ なら、$`\mathfrak B{\restriction}\mathrm{next}(\gamma) \models \varphi(\vec p)`$ | 下の証明 |

**`wit_below` の証明.** パラメータの位置に $`p_i`$、ほかの位置に `none` を置いた入力 $`q`$ を作る。`toP` は `none` を 0 にするが、$`\mathfrak B`$ での真偽はパラメータの位置しか読まないので、$`\mathfrak B \models \varphi(\mathrm{toP}(q))`$ である。$`q`$ について選んだ証人は、$`\mathrm{wh}(q_\varphi, \mathrm{toP}(q))`$ より下にある（`wit_lt_wh`）。これは上限の項の 1 つなので、$`\mathrm{next}(\gamma)`$ より下である（`wh_le_nextO`）。$`\square`$

## 5. 塔と λ

**定義（`tower`、`lam`）.** $`\gamma`$ をラベル、$`k`$ を自然数とする。Lean の `tower S γ k` を $`\mathrm{next}^k(\gamma)`$ と書く。

```math
\mathrm{next}^0(\gamma) := \gamma, \quad \mathrm{next}^{k+1}(\gamma) := \mathrm{next}\bigl(\mathrm{next}^k(\gamma)\bigr), \qquad \lambda(\gamma) := \sup_{k \in \mathbb N} \mathrm{next}^k(\gamma)
```

| 定理 | 内容 |
|---|---|
| `tower_lt` | $`\gamma \lt \omega_1 \implies \mathrm{next}^k(\gamma) \lt \omega_1`$ |
| `tower_succ_lt` | $`\mathrm{next}^k(\gamma) \lt \mathrm{next}^{k+1}(\gamma)`$ |
| `tower_mono` | $`k \le k' \implies \mathrm{next}^k(\gamma) \le \mathrm{next}^{k'}(\gamma)`$ |
| `tower_le_lam` | $`\mathrm{next}^k(\gamma) \le \lambda(\gamma)`$ |
| `lam_lt` | $`\gamma \lt \omega_1 \implies \lambda(\gamma) \lt \omega_1`$（可算個の上限） |
| `lt_lam` | $`\gamma \lt \omega_1 \implies \gamma \lt \lambda(\gamma)`$ |
| `exists_tower` | 有限個の $`p_i \lt \lambda(\gamma)`$ なら、ある $`k`$ で全部 $`\lt \mathrm{next}^k(\gamma)`$ |

`exists_tower` の証明：各 $`p_i`$ は上限より小さいので、ある $`k_i`$ で $`p_i \lt \mathrm{next}^{k_i}(\gamma)`$ である。$`k := \max_i k_i`$ を取り、`tower_mono` を使う。

## 6. λ(γ) は Good

**定理（`lam_good`）.** $`\gamma \lt \omega_1`$ なら $`\mathrm{Good}(\lambda(\gamma))`$。

**証明.** Tarski–Vaught 判定法（[03](03-sigma1-elementary.md) §6）の形で示す。$`\vec p \lt \lambda(\gamma)`$ で $`\mathfrak B \models \varphi(\vec p)`$ とする。`exists_tower` から、ある $`k`$ で $`\vec p \lt \mathrm{next}^k(\gamma)`$ である。`wit_below` を $`\mathrm{next}^k(\gamma)`$ で使うと、証人は $`\mathrm{next}^{k+1}(\gamma) \le \lambda(\gamma)`$ より下に取れる。$`\square`$

**定理（`good_cofinal`）.** $`\sigma \lt \omega_1`$ なら、$`\sigma \lt \alpha \lt \omega_1`$ で $`\mathrm{Good}(\alpha)`$ となる $`\alpha`$ がある。$`\alpha = \lambda(\sigma)`$ でよい。

**例（形だけ）.** $`\lambda(0)`$ は、「$`\mathfrak B`$ で真の $`\Sigma_1`$ の主張で、パラメータが $`\lambda(0)`$ より下のもの」の証人をすべて含む。$`\lambda(0)`$ の具体的な値は分からない。証明は値を使わず、$`\lambda(0) \lt \omega_1`$ と $`\mathrm{Good}(\lambda(0))`$ だけを使う。

**Good な点の集合について.** Good な点の集合が $`\omega_1`$ の中で閉じていること（Good な点の増加列の上限がまた Good であること）は示していないし、使わない。そのため club（閉非有界集合）とは呼ばない。

## 7. Good な点の列

**定義（`points`）.**

```math
c_0 := \lambda(0), \qquad c_{k+1} := \lambda(c_k)
```

| 定理 | 内容 |
|---|---|
| `points_lt` | $`c_k \lt \omega_1`$ |
| `points_strictMono` | $`c_0 \lt c_1 \lt c_2 \lt \cdots`$ |
| `points_good` | $`\mathrm{Good}(c_k)`$ |

どれも §5、§6 から $`k`$ についての帰納法で出る。

この列の 2 点は、すべての鍵で $`R`$ の関係にある（`good_R`）。その証明には、Good な点で上端の述語が $`\omega_1`$ の上端の述語と一致すること（`top_abs`）が要る。どちらも [09](09-obligations.md) §3 で説明する。

## 8. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md)「3 つの定理の証明」 | 「論理式は可算個なので、Good な点は $`\omega_1`$ の中で共終である」 |
| [notes/01-design.md](../notes/01-design.md) §3.3 | Good な点、$`\omega`$ 回のくり返し、Good な点の列 |
| [Por/Supply.lean](../Por/Supply.lean) | このノートのすべて |

## 9. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| Good | `Good` | [Por/Supply.lean](../Por/Supply.lean) |
| 論理式が可算 | `litCode`、`litCode_inj`、`lit_countable`、`formCode`、`formCode_inj`、`form_countable` | 同上 |
| 型板が有限 | `Keys.template_countable`、`Model.keySyntax_countable` | [OmegaY/Keys.lean](../OmegaY/Keys.lean)、[OmegaY/Model.lean](../OmegaY/Model.lean) |
| 証人の高さ | `wh`、`wh_lt`、`wit_lt_wh` | [Por/Supply.lean](../Por/Supply.lean) |
| 閉包の 1 段 | `nextO`、`next`、`next_val`、`nextO_lt`、`next_lt`、`lt_next`、`wh_le_nextO`、`wit_below` | 同上 |
| 塔と λ | `tower`、`tower_lt`、`tower_succ_lt`、`tower_mono`、`lamO`、`lam`、`tower_le_lam`、`lam_lt`、`lt_lam`、`exists_tower` | 同上 |
| λ は Good | `lam_good`、`good_cofinal` | 同上 |
| Good な点の列 | `points`、`points_lt`、`points_good`、`points_strictMono` | 同上 |
