[← Back](README.md) | [English](en/08-closure-chain.md) | [Japanese](08-closure-chain.md)

# ω₁ より下の閉包と鎖

前提

| ノート | ここで使う言葉 |
|---|---|
| [01 順序数と ω₁](01-ordinals.md) | $`\omega_1`$、正則性（§5）、ラベル（§6）、$`\mathrm{Fin}\ n`$、部分的なパラメータの列 $`\mathrm{Par}_n(\gamma)`$、$`\mathrm{toP}`$（§7） |
| [03 構造と Σ₁ 初等部分構造](03-sigma1-elementary.md) | 証人、部分構造、Tarski–Vaught 判定法、型板、標準形 $`(n, F, L)`$、リテラル、構造 $`(c; \lt, \mathrm{rel}, \mathrm{top}, \mathrm{allow})`$（§7） |
| [07 関係 R](07-relation-r.md) | $`R`$、記号 $`\mathrm{Rel}_{t,i,j}`$、$`\mathrm{Top}_{t,i}`$ とその真の解釈 $`\mathrm{relR}`$、$`\mathrm{topR}_c`$ |

このノートは、$`\omega_1`$ より下に「$`\Sigma_1`$ の証人で閉じた点」を作る方法を説明する。これは Löwenheim–Skolem の定理と同じ考え方で、証人を足して上限を取る。できた点を並べた鎖が、[09](09-obligations.md) で最初のラベルになる。

## 1. 周りの構造と Good

**定義（周りの構造）.** すべての鍵で上端述語を定義した、高さ $`\omega_1`$ の構造を $`\mathfrak B`$ とする（書き方は [03](03-sigma1-elementary.md) §7）。

```math
\mathfrak B = \bigl(\omega_1;\ \lt,\ \mathrm{relR},\ \mathrm{topR}_{\omega_1},\ \mathrm{allow}_{\mathrm{all}}\bigr), \qquad \mathrm{topR}_{\omega_1}(\kappa, x) :\iff R(\kappa, x, \omega_1), \qquad \mathrm{allow}_{\mathrm{all}}(\kappa) :\iff \text{真}
```

上端述語はすべての鍵で定義されている（[03](03-sigma1-elementary.md) §8）。

**定義（Good）.** ラベル $`\gamma`$ について、$`\mathfrak B{\restriction}\gamma`$ を、$`\mathfrak B`$ の領域を $`\{x \mid x \lt \gamma\}`$ に制限したものとする。上端述語は $`\omega_1`$ へのもののままである。

```math
\mathfrak B{\restriction}\gamma = \bigl(\gamma;\ \lt,\ \mathrm{relR},\ \mathrm{topR}_{\omega_1},\ \mathrm{allow}_{\mathrm{all}}\bigr), \qquad \mathrm{Good}(\gamma) :\iff \mathfrak B{\restriction}\gamma \preccurlyeq_{\Sigma_1} \mathfrak B
```

つまり、すべての論理式 $`\varphi = (n, F, L)`$ と、$`F`$ の位置で $`p_i \lt \gamma`$ となるすべての $`\vec p`$ で、$`\mathfrak B{\restriction}\gamma \models \varphi(\vec p) \iff \mathfrak B \models \varphi(\vec p)`$ である。

$`\mathfrak B{\restriction}\gamma`$ は $`\mathfrak B`$ の本当の部分構造である（解釈が同じで、領域だけが違う）。だから [03](03-sigma1-elementary.md) §6 の Tarski–Vaught 判定法がそのまま使える。上向き $`\mathfrak B{\restriction}\gamma \models \varphi(\vec p) \implies \mathfrak B \models \varphi(\vec p)`$ はいつも成り立つ（[03](03-sigma1-elementary.md) §4 の性質 2）。したがって $`\mathrm{Good}(\gamma)`$ は、下向きだけの次の条件と同値である。

```math
\forall \varphi\ \forall \vec p\ \Bigl(\bigl(\forall i \in F\ \ p_i \lt \gamma\bigr) \land \mathfrak B \models \varphi(\vec p) \implies \mathfrak B{\restriction}\gamma \models \varphi(\vec p)\Bigr)
```

## 2. 論理式は可算個

**定義（論理式の集合）.** [03](03-sigma1-elementary.md) §7 の標準形 $`(n, F, L)`$ 全体の集合を $`\mathcal F`$ とする。$`n \in \mathbb N`$、$`F \subseteq \mathrm{Fin}\ n`$、$`L`$ は $`n`$ 変数のリテラルの有限リストである。

**可算である理由.** $`n`$ を決めると、リテラルは次の組で表せる。

| リテラル | 組 |
|---|---|
| $`v_i \lt v_j`$、$`\neg(v_i \lt v_j)`$ | $`(i, j, \pm)`$ |
| $`\mathrm{Rel}_{t,i,j}`$、$`\neg\mathrm{Rel}_{t,i,j}`$ | $`(t, i, j, \pm)`$ |
| $`\mathrm{Top}_{t,i}`$、$`\neg\mathrm{Top}_{t,i}`$ | $`(t, i, \pm)`$ |

$`\pm`$ は肯定か否定かの 2 通りである。$`i, j \in \mathrm{Fin}\ n`$ は有限個で、型板の集合 $`\mathcal T_n`$ は可算である（ω-Y の鍵の構文では $`(n+1)^m`$ 個。[03](03-sigma1-elementary.md) §7）。よって $`n`$ 変数のリテラルは可算個で、その有限リストも可算個である。$`F`$ は $`2^n`$ 通りである。$`n`$ は自然数である。よって $`\mathcal F`$ は可算である。

型板の集合 $`\mathcal T_n`$ が可算であることが要る。1 つの論理式は有限個の型板しか使わないが、論理式の全体が可算であるためには、型板の全体が可算でなければならない。このノートの定義と証明は、鍵の構文について、各 $`\mathcal T_n`$ が可算であることだけを使う。

## 3. 証人の高さ

**定義（証人の高さ）.** 論理式 $`\varphi = (n, F, L) \in \mathcal F`$ と、ラベルの列 $`\vec p \in (\mathrm{Fin}\ n \to \mathrm{Label})`$ について：

- $`\mathfrak B \models \varphi(\vec p)`$ なら、[03](03-sigma1-elementary.md) §7 の充足の定義の $`\vec v`$（$`v_i \lt \omega_1`$）を選択公理で 1 組選び、$`h(\varphi, \vec p) := \sup_{i \lt n} (v_i + 1)`$ とする。
- そうでなければ $`h(\varphi, \vec p) := 0`$ とする。

**定理（証人の高さは ω₁ より下）.** $`h(\varphi, \vec p) \lt \omega_1`$。

**証明.** 有限個の $`v_i + 1`$ の最大値で、どれも $`\omega_1`$ より下である（[01](01-ordinals.md) §4）。$`\square`$

選んだ $`\vec v`$ の成分はどれも $`h(\varphi, \vec p)`$ より下にある（[01](01-ordinals.md) §3）。

## 4. 閉包の 1 ステップ

**定義（入力）.** ラベル $`\gamma`$ について、論理式と部分的なパラメータの列（[01](01-ordinals.md) §7）の組の集合を次で定める。

```math
\mathrm{Input}(\gamma) := \bigl\{\, (\varphi, q) \ \bigm|\ \varphi = (n, F, L) \in \mathcal F,\ \ q \in \mathrm{Par}_n(\gamma) \,\bigr\}
```

$`\gamma \lt \omega_1`$ なら、$`\mathrm{Input}(\gamma)`$ は可算である。$`\mathcal F`$ が可算で（§2）、各 $`\mathrm{Par}_n(\gamma)`$ も可算だからである（[01](01-ordinals.md) §7）。

**定義（閉包の 1 ステップ）.** ラベル $`\gamma`$ について、次で定める。

```math
\mathrm{next}(\gamma) := \min\Bigl(\max\Bigl(\gamma + 1,\ \sup_{(\varphi, q) \in \mathrm{Input}(\gamma)} h\bigl(\varphi, \mathrm{toP}(q)\bigr)\Bigr),\ \omega_1\Bigr)
```

$`\min(\cdot, \omega_1)`$ は、値をラベル（$`\omega_1`$ 以下）にするためのものである。$`\gamma \lt \omega_1`$ なら、性質 2 から $`\min`$ は何も変えない。

| 性質 | 内容 | 理由 |
|---|---|---|
| 性質 1 | $`\gamma \lt \omega_1 \implies \gamma \lt \mathrm{next}(\gamma)`$ | $`\gamma + 1`$ の項 |
| 性質 2 | $`\gamma \lt \omega_1 \implies \mathrm{next}(\gamma) \lt \omega_1`$ | $`\gamma + 1 \lt \omega_1`$ と、可算個の上限（[01](01-ordinals.md) §4、§5） |
| 性質 3 | $`\gamma \lt \omega_1`$、$`F`$ の位置で $`p_i \lt \gamma`$、$`\mathfrak B \models \varphi(\vec p)`$ なら、$`\mathfrak B{\restriction}\mathrm{next}(\gamma) \models \varphi(\vec p)`$ | 下の証明 |

**性質 3 の証明.** [01](01-ordinals.md) §7 の定理（どのパラメータも表せる）から、ある $`q \in \mathrm{Par}_n(\gamma)`$ で、$`F`$ の位置では $`\mathrm{toP}(q)_i = p_i`$ である。$`\mathfrak B`$ での真偽は $`F`$ の位置のパラメータしか読まないので、$`\mathfrak B \models \varphi(\mathrm{toP}(q))`$ である。$`(\varphi, \mathrm{toP}(q))`$ について選んだ $`\vec v`$ は、$`F`$ の位置で $`v_i = p_i`$ を満たし、どの成分も $`h(\varphi, \mathrm{toP}(q))`$ より下にある（§3）。これは上限の項の 1 つなので、$`\mathrm{next}(\gamma)`$ より下である。よって $`\vec v`$ は $`\mathfrak B{\restriction}\mathrm{next}(\gamma)`$ での証人である。$`\square`$

## 5. λ

**定義（λ）.**

```math
\mathrm{next}^0(\gamma) := \gamma, \quad \mathrm{next}^{t+1}(\gamma) := \mathrm{next}\bigl(\mathrm{next}^t(\gamma)\bigr), \qquad \lambda(\gamma) := \sup_{t \in \mathbb N} \mathrm{next}^t(\gamma)
```

$`t \in \mathbb N`$ である。$`\lambda(\gamma)`$ の形の順序数を **閉包点** と呼ぶ。$`\lambda(\gamma) \le \omega_1`$ なので、閉包点はラベルである。

| 性質 | 内容 |
|---|---|
| 性質 4 | $`\gamma \lt \omega_1 \implies \mathrm{next}^t(\gamma) \lt \omega_1`$ |
| 性質 5 | $`\gamma \lt \omega_1`$、$`t \le t' \implies \mathrm{next}^t(\gamma) \le \mathrm{next}^{t'}(\gamma)`$ |
| 性質 6 | $`\gamma \lt \omega_1 \implies \lambda(\gamma) \lt \omega_1`$（可算個の上限） |
| 性質 7 | $`\gamma \lt \omega_1 \implies \gamma \lt \lambda(\gamma)`$ |
| 性質 8 | $`\gamma \lt \omega_1`$、$`k \in \mathbb N`$、$`p_0, \ldots, p_{k-1} \lt \lambda(\gamma)`$ なら、ある $`t`$ で全部 $`\lt \mathrm{next}^t(\gamma)`$ |

性質 4 は $`t`$ についての帰納法で、性質 2 から出る。性質 5 は性質 1 と 4 から出る。性質 7 は $`\gamma \lt \mathrm{next}^1(\gamma) \le \lambda(\gamma)`$ である。性質 8 は次のように示す。各 $`p_i`$ は上限より小さいので、ある $`t_i`$ で $`p_i \lt \mathrm{next}^{t_i}(\gamma)`$ である。$`t := \max_i t_i`$ を取り、性質 5 を使う。

## 6. λ(γ) は Good

**定理（λ(γ) は Good）.** $`\gamma \lt \omega_1`$ なら $`\mathrm{Good}(\lambda(\gamma))`$。

**証明.** Tarski–Vaught 判定法（[03](03-sigma1-elementary.md) §6）の形で、§1 の下向きの条件を示す。$`F`$ の位置で $`p_i \lt \lambda(\gamma)`$、$`\mathfrak B \models \varphi(\vec p)`$ とする。性質 8 から、ある $`t`$ で、$`F`$ の位置で $`p_i \lt \mathrm{next}^t(\gamma)`$ である。性質 3 を $`\mathrm{next}^t(\gamma)`$（性質 4 から $`\omega_1`$ より下）で使うと、証人は $`\mathrm{next}^{t+1}(\gamma) \le \lambda(\gamma)`$ より下に取れる。$`\square`$

**系（Good な点は ω₁ の中で上に限りが無い）.** $`\sigma \lt \omega_1`$ なら、$`\sigma \lt \alpha \lt \omega_1`$ で $`\mathrm{Good}(\alpha)`$ となる $`\alpha`$ がある。$`\alpha = \lambda(\sigma)`$ でよい（性質 6、7 と上の定理）。

**例（形だけ）.** $`\gamma = 0`$ とする。$`\lambda(0)`$ は、「$`\mathfrak B`$ で真の $`\Sigma_1`$ の主張で、パラメータが $`\lambda(0)`$ より下のもの」の証人をすべて含む。$`\lambda(0)`$ の具体的な値は分からない。証明は値を使わず、$`\lambda(0) \lt \omega_1`$ と $`\mathrm{Good}(\lambda(0))`$ だけを使う。

**Good な点の集合について.** Good な点の集合が $`\omega_1`$ の中で閉じていること（Good な点の増加列の上限がまた Good であること）は示していないし、使わない。そのため club（閉非有界集合）とは呼ばない。

## 7. 鎖

**定義（鎖）.**

```math
c_0 := \lambda(0), \qquad c_{t+1} := \lambda(c_t)
```

| 性質 | 内容 |
|---|---|
| 性質 9 | $`c_t \lt \omega_1`$ |
| 性質 10 | $`c_0 \lt c_1 \lt c_2 \lt \cdots`$ |
| 性質 11 | $`\mathrm{Good}(c_t)`$ |

どれも §5、§6 から $`t`$ についての帰納法で出る。

この鎖の 2 点は、すべての鍵で $`R`$ の関係にある。その証明には、Good な点で上端述語が $`\omega_1`$ の上端述語と一致することが要る。どちらも [09](09-obligations.md) §3 で説明する。

## 8. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md)「3 つの定理の証明」 | 「論理式は可算個なので、Good な点は $`\omega_1`$ の中で共終である」（§2、§6）、Good な点の列（§7） |
| [notes/01-design.md](../notes/01-design.md) §3.3 | 周りの構造、Good、$`\omega`$ 回のくり返し、Good な点の列 |

## 9. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| $`\mathfrak B`$ での真偽 | `Sat (relR S) (topR S top) (fun _ => True) top φ p` | [Por/Supply.lean](../Por/Supply.lean) |
| Good（§1 の下向きの形） | `Good` | 同上 |
| 論理式が可算（§2） | `litCode`、`litCode_inj`、`lit_countable`、`formCode`、`formCode_inj`、`form_countable` | 同上 |
| 型板が可算 | 仮定 `[∀ n, Countable (S.Template n)]`、`Keys.template_countable`、`Model.keySyntax_countable` | 同上、[OmegaY/Keys.lean](../OmegaY/Keys.lean)、[OmegaY/Model.lean](../OmegaY/Model.lean) |
| 証人の高さ $`h`$ | `wh`、`wh_lt`、`wit_lt_wh` | [Por/Supply.lean](../Por/Supply.lean) |
| $`\mathrm{Input}(\gamma)`$ | `Input S γ := Σ φ : Form S, Fin φ.n → Option (Set.Iio γ)`、`input_countable` | 同上 |
| $`\mathrm{next}`$（$`\min`$ の前の値は `nextO`） | `nextO`、`next`、`next_val`、`nextO_lt`、`wh_le_nextO` | 同上 |
| 性質 1〜3 | `lt_next`、`next_lt`、`wit_below` | 同上 |
| $`\mathrm{next}^t`$、$`\lambda`$ | `tower`、`lamO`、`lam` | 同上 |
| 性質 4〜8 | `tower_lt`、`tower_succ_lt`、`tower_mono`、`tower_le_lam`、`lam_lt`、`lt_lam`、`exists_tower` | 同上 |
| λ(γ) は Good、系 | `lam_good`、`good_cofinal` | 同上 |
| 鎖と性質 9〜11 | `points`、`points_lt`、`points_strictMono`、`points_good` | 同上 |
