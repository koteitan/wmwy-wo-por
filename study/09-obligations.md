[← Back](README.md) | [English](en/09-obligations.md) | [Japanese](09-obligations.md)

# 3 つの定理の証明

前提

| ノート | ここで使う言葉 |
|---|---|
| [01 順序数と ω₁](01-ordinals.md) | 順序数の $`\lt`$ が整礎であること（§1）、ラベル（§6） |
| [02 整礎関係と整礎再帰](02-well-founded.md) | 整礎帰納法（§2）、鍵の順序が整礎であること（§3） |
| [03 構造と Σ₁ 初等部分構造](03-sigma1-elementary.md) | 標準形 $`(n, F, L)`$、リテラル、$`\mathrm{Rel}_{t,i,j}`$、$`\mathrm{Top}_{t,i}`$、充足（§7）、補題 2、3（§8） |
| [06 Phyrion 氏の ω-Y の組合せの層](06-combinatorial-layer.md) | アトム、図式、成り立つ、表現、上端、上端のアトム、要求、切れ目、制御関係、鍵が $`\theta`$ より小さい要求、有限反映、3 つの定理、入口の定理、$`G_D(s)`$ |
| [07 関係 R](07-relation-r.md) | $`R`$、構造 $`\mathfrak A^c_\theta`$、真の解釈、$`\mathrm{Elem}`$、定義の式（§6）、鍵の弱化の定理（§7） |
| [08 ω₁ より下の閉包と鎖](08-closure-chain.md) | $`\mathfrak B`$、$`\mathfrak B{\restriction}\gamma`$、Good、鎖 $`c_t`$ と性質 9〜11（§7） |

このノートは、関係 $`R`$ が組合せの層の 3 つの定理をどう満たすかを説明する。中心は有限反映（§2）と、最初の表現（§3）である。

## 1. 定理の一覧

ラベルは $`\mathrm{Label}`$（[01](01-ordinals.md) §6）、$`R`$ は [07](07-relation-r.md) の関係である。

| 定理（[06](06-combinatorial-layer.md) §5） | 節 |
|---|---|
| 鍵の弱化 | [07](07-relation-r.md) §7 |
| 有限反映 | §2 |
| 初期表現 | §3 |

- 鍵の弱化：[07](07-relation-r.md) §7 の定理（鍵の弱化）そのものである。$`\theta \le \Theta`$ の形で示してあり、組合せの層が求める形と同じである。
- ラベルの順序が整礎であることは、順序数の $`\lt`$ が整礎であること（[01](01-ordinals.md) §1）である。

## 2. 有限反映

**示すこと.** [06](06-combinatorial-layer.md) §4 の仮定の下で、$`g`$ を作る。記号は次のとおりである。$`G`$、$`f`$、$`\mathrm{cut} \in \mathbb N`$、鍵 $`\theta`$、ラベル $`\beta`$、$`\mathrm{needs}`$ は [06](06-combinatorial-layer.md) §4 のとおりである。$`n`$ は $`G`$ のサイズ、$`f`$ は表現、制御関係は $`R(\theta, f(\mathrm{cut}), \beta)`$、要求は $`d = (t_d, p_d)`$ である。$`G`$ のアトムを $`e = (t_e, p_e, q_e)`$ と書く。

**証明.**

1. $`a := f(\mathrm{cut})`$ と置く。[07](07-relation-r.md) §6 の定義の式から $`a \lt \beta`$ と $`\mathrm{Elem}(\theta, a, \beta)`$ が出る。
2. パラメータの位置を $`F := \{i \mid i \lt \mathrm{cut}\}`$、パラメータを $`f(0), \ldots, f(\mathrm{cut} - 1)`$ とする。$`f`$ は増加なので、どれも $`\lt a`$ である。
3. [03](03-sigma1-elementary.md) §7 の標準形の論理式 $`\Phi := (n, F, L)`$ を作る。$`L`$ は次のリテラルからなる。
   - 順序：$`i, j \lt n`$ ごとに、$`i \lt j`$ なら $`v_i \lt v_j`$、そうでなければ $`\neg(v_i \lt v_j)`$。
   - アトム：$`e \in G`$ ごとに $`\mathrm{Rel}_{t_e, p_e, q_e}`$。
   - 要求：$`d \in \mathrm{needs}`$ ごとに $`\mathrm{Top}_{t_d, p_d}`$。

   $`i \lt \mathrm{cut}`$ なら $`z_i := f(i)`$、$`\mathrm{cut} \le i \lt n`$ なら $`z_i := v_i`$ とすると、$`\Phi`$ は次の論理式である。

```math
\Phi \equiv \exists v_{\mathrm{cut}} \cdots \exists v_{n-1}\ \Bigl[\ \bigwedge_{i \lt j \lt n} z_i \lt z_j \ \land\ \bigwedge_{j \le i \lt n} \neg(z_i \lt z_j) \ \land\ \bigwedge_{e \in G} \mathrm{Rel}_{t_e, p_e, q_e}(\vec z) \ \land\ \bigwedge_{d \in \mathrm{needs}} \mathrm{Top}_{t_d, p_d}(\vec z)\ \Bigr]
```

4. $`\Phi`$ は、どの鍵の構造 $`\mathfrak A^c_\theta`$ でも読める。1-Y 版の段の条件は無い。上端述語 $`\mathrm{Top}_{t_d, p_d}(\vec z)`$ は、鍵 $`\mathrm{eval}\ t_d\ \vec z`$ が $`\theta`$ より小さいときだけ定義される（[07](07-relation-r.md) §3）。
5. 高さ $`\beta`$ で $`\Phi`$ は真である（$`\mathfrak A^\beta_\theta \models \Phi(f)`$）。証人を $`v_i := f(i)`$ と取ると $`z = f`$ になる。順序は表現の条件 2、$`\mathrm{Rel}`$ は表現の条件 3 から出る。$`\mathrm{Top}`$ は、要求の鍵が $`\theta`$ より小さいこと（仮定 5、定義されている）と、要求が上端 $`\beta`$ について成り立つこと（仮定 6、$`R(\mathrm{eval}\ t_d\ f, f(p_d), \beta)`$）から出る。
6. 1 の初等性から、高さ $`a`$ でも $`\Phi`$ は真である（$`\mathfrak A^a_\theta \models \Phi(f)`$）。その証人 $`v'_i \lt a`$ を取る。
7. $`g`$ を、$`i \lt \mathrm{cut}`$ なら $`g(i) := f(i)`$、そうでなければ $`g(i) := v'_i`$ と定める。
   - $`g`$ は狭義増加である（$`\Phi`$ の順序の部分）。
   - $`G`$ の各アトムが $`g`$ で成り立つ（$`\Phi`$ の $`\mathrm{Rel}`$ の部分。$`\mathrm{Rel}`$ の解釈は $`R`$ そのものである）。
   - $`g(i) \lt a`$（左の部分は $`f(i) \lt f(\mathrm{cut})`$、右の部分は証人が $`\lt a`$）。よって $`g(i) \lt \omega_1`$ で、$`g`$ は $`G`$ の表現である。
   - $`g(i) \le f(i)`$（$`i \lt \mathrm{cut}`$ なら等しく、そうでなければ $`g(i) \lt a = f(\mathrm{cut}) \le f(i)`$）。
   - 各要求で $`R(\mathrm{eval}\ t_d\ g, g(p_d), a)`$（高さ $`a`$ では $`\mathrm{Top}_{t,i}(\vec v)`$ は $`R(\mathrm{eval}\ t\ \vec v, v_i, a)`$）。$`\square`$

**例 1.** [06](06-combinatorial-layer.md) §3 の例 2（$`(1, 2, 4)`$ の展開のステップ 0）を使う。$`G`$ は $`(1, 2)`$ の図式（アトムは $`((0), 0, 1)`$）、$`n = 2`$、$`\mathrm{cut} = 1`$、$`\theta = (f(1))`$、$`\beta = f(2)`$、要求は $`d = ((0), 1)`$ の 1 つである。パラメータは $`p_0 = f(0)`$ で、$`\Phi`$ は次のとおりである。ここでは、$`\mathrm{Rel}`$ と $`\mathrm{Top}`$ を鍵の値で読み下し、$`p_0 \lt v_1`$ から出る否定の順序のリテラルを省く。$`\mathrm{Top}_{(p_0)}(v_1)`$ は、鍵 $`(p_0)`$ の上端述語が $`v_1`$ で成り立つこと、つまり高さ $`c`$ で $`R((p_0), v_1, c)`$ である。

```math
\exists v_1\ \bigl[\ p_0 \lt v_1 \land R((p_0), p_0, v_1) \land \mathrm{Top}_{(p_0)}(v_1)\ \bigr]
```

- 高さ $`\beta`$ では $`v_1 = f(1)`$ が証人である。上端述語の鍵 $`(f(0))`$ は $`\theta = (f(1))`$ より小さいので定義されていて、$`R((f(0)), f(1), f(2))`$ が成り立つ。
- 反映すると、$`f(1)`$ より下に新しい $`v'_1`$ が取れて、$`R((f(0)), f(0), v'_1)`$ と $`R((f(0)), v'_1, f(1))`$ を満たす。$`g = (f(0), v'_1)`$ である。

**例 2.** [06](06-combinatorial-layer.md) §8 の例（$`(1, 3, 3)[2]`$）のステップ 0 を使う。$`n = 2`$、$`f_j := f(j)`$、$`\mathrm{cut} = 0`$、$`\theta = (f_0, \top)`$、$`\beta = f_2`$ である。$`G`$ は列 1 の 2 つの辺、要求は下の辺 $`((0, 0), 0)`$ である。パラメータは無い。例 1 と同じ読み下しで、$`\Phi`$ は次のとおりである。

```math
\exists v_0\ \exists v_1\ \bigl[\ v_0 \lt v_1 \land R((v_0, v_0), v_0, v_1) \land R((v_0, \top), v_0, v_1) \land \mathrm{Top}_{(v_0, v_0)}(v_0)\ \bigr]
```

- 高さ $`f_2`$ では $`v = (f_0, f_1)`$ が証人である。上端述語の鍵 $`(f_0, f_0)`$ は $`\theta = (f_0, \top)`$ より小さいので定義されていて、$`R((f_0, f_0), f_0, f_2)`$ が成り立つ。
- 反映すると、$`g_0 \lt g_1 \lt f_0`$ で、同じ条件を上端 $`f_0`$ について満たすものが得られる。上端述語の鍵は $`(g_0, g_0)`$ に変わる。鍵が指す列 0 は切れ目より前ではなく、そのラベルも証人である。

**1-Y 版との違い.** 1-Y 版は、名前の位置の集合と、記号の上限を決めて、段の論理式を作った。ここでは要らない。上端述語が定義されるかどうかは、鍵の値で決まるからである（[03](03-sigma1-elementary.md) §8）。

**使わなかったもの.** $`\beta`$ が Good であること、$`a`$ や $`\beta`$ が極限であること。

## 3. 最初の表現

### 3.1 上端述語の絶対性

**定理（上端述語の絶対性）.** ラベル $`\delta`$ について $`\mathrm{Good}(\delta)`$ かつ $`\delta \lt \omega_1`$ とする。すべての鍵 $`\kappa`$ とラベル $`x \lt \delta`$ について次が成り立つ。

```math
R(\kappa, x, \delta) \iff R(\kappa, x, \omega_1)
```

**証明.** $`\kappa`$ についての整礎帰納法をする（[02](02-well-founded.md) §2。鍵の順序は整礎である、[02](02-well-founded.md) §3）。

1. 定義の式（[07](07-relation-r.md) §6）で両辺を開く。$`x \lt \delta`$ も $`x \lt \omega_1`$ も真である。残りは、どの論理式 $`\varphi = (n, F, L)`$ と、$`F`$ の位置で $`p_i \lt \delta`$ となる $`\vec p`$ についても、次が成り立つことである。

```math
\mathfrak A^\delta_\kappa \models \varphi(\vec p) \iff \mathfrak A^{\omega_1}_\kappa \models \varphi(\vec p)
```

2. $`\delta`$ より下の値の列 $`\vec v`$ では、各リテラルの真偽は高さ $`\delta`$ と高さ $`\omega_1`$ で同じである。上端述語のリテラルで読む鍵 $`\kappa' := \mathrm{eval}\ t\ \vec v`$ は $`\kappa' \lt \kappa`$ のときだけ定義され、そのとき帰納法の仮定から $`R(\kappa', v_i, \delta) \iff R(\kappa', v_i, \omega_1)`$ である。ほかのリテラルは高さを読まない。
3. 高さ $`\delta`$ から高さ $`\omega_1`$：証人は $`\delta \lt \omega_1`$ より下にあり、2 からリテラルの真偽は同じである。
4. 高さ $`\omega_1`$ から高さ $`\delta`$：証人 $`\vec v`$（$`v_i \lt \omega_1`$）を取る。
   - $`\mathrm{allow}`$ を「いつも真」に広げる（[03](03-sigma1-elementary.md) §8 の補題 2）。すると $`\vec v`$ は $`\mathfrak B`$ での証人である。
   - $`F' := \{i \mid v_i \lt \delta\}`$ として、論理式 $`(n, F', L)`$ に $`\mathrm{Good}(\delta)`$ を使う。$`\mathfrak B{\restriction}\delta`$ での証人 $`\vec w`$ は、$`w_i \lt \delta`$ で、$`F'`$ の位置では $`w_i = v_i`$、ほかの位置では $`w_i \lt \delta \le v_i`$ である。よって各点で $`\vec w \le \vec v`$ である。
   - 鍵の構文の単調性から、上端述語のリテラルの鍵は $`\mathrm{eval}\ t\ \vec w \le \mathrm{eval}\ t\ \vec v \lt \kappa`$ で、$`\kappa`$ より小さいままである（[03](03-sigma1-elementary.md) §8 の補題 3 と同じ理由）。
   - 2 で高さ $`\delta`$ の上端述語に戻す。$`F`$ の位置では $`p_i \lt \delta`$ なので $`w_i = v_i = p_i`$ である。$`\square`$

4 の 2 つめで、証人を各点で下げる。1-Y 版では「見えるかどうかは位置だけで決まる」ことを使ったが、ここでは鍵が値で決まるので、下げても鍵が $`\kappa`$ より小さいままであることを、単調性で示す。

### 3.2 Good な点どうしは R の関係にある

**定理（Good な点どうしは R の関係にある）.** ラベル $`\alpha, \beta`$ について $`\mathrm{Good}(\alpha)`$、$`\mathrm{Good}(\beta)`$、$`\alpha \lt \beta \lt \omega_1`$ なら、すべての鍵 $`\kappa`$ で $`R(\kappa, \alpha, \beta)`$。

**証明.** $`\alpha \lt \beta`$ である。論理式 $`\varphi = (n, F, L)`$ と、$`F`$ の位置で $`p_i \lt \alpha`$ となる $`\vec p`$ について、次の同値をつなぐ。

```math
\mathfrak A^{\alpha}_{\kappa} \models \varphi(\vec p) \iff \mathfrak A^{\omega_1}_{\kappa} \models \varphi(\vec p) \iff \mathfrak A^{\beta}_{\kappa} \models \varphi(\vec p)
```

1 つめは $`\alpha`$ での、2 つめは $`\beta`$ での、§3.1 の証明の 1〜4 である。帰納法の仮定の代わりに、§3.1 の定理そのものを使う。$`\square`$

鍵 $`\kappa`$ は何でもよい。Good な点どうしは、どの鍵でも関係にある。

### 3.3 すべての図式の表現

**定理（すべての図式の表現）.** どの図式 $`G`$（サイズ $`n`$）と上端のアトムのリスト $`\mathrm{needs}`$ にも、$`\beta \lt \omega_1`$ と、$`\beta`$ で上から押さえられる $`G`$ の表現 $`f`$ があって、$`\mathrm{needs}`$ の各要素は上端 $`\beta`$ について成り立つ。

**証明.** $`\beta := c_n`$、$`f(i) := c_i`$（[08](08-closure-chain.md) §7 の鎖）とする。

- $`f`$ は狭義増加で、$`i \lt n`$ なら $`c_i \lt c_n`$ である（性質 10）。$`c_n \lt \omega_1`$ である（性質 9）。どの $`c_i`$ も Good である（性質 11）。
- アトム $`(t, p, q)`$ は $`p \lt q`$ なので $`c_p \lt c_q`$ である。§3.2 の定理を鍵 $`\mathrm{eval}\ t\ f`$ で使うと $`R(\mathrm{eval}\ t\ f, c_p, c_q)`$。
- 上端のアトム $`(t, p)`$ は $`p \lt n`$ なので $`c_p \lt c_n`$ である。§3.2 の定理から $`R(\mathrm{eval}\ t\ f, c_p, c_n)`$。$`\square`$

1 つの列 $`c`$ が、すべての図式を同時に表現する。特に、式の図式 $`G_D(s)`$ を表現するので（$`\mathrm{needs}`$ は空）、初期表現が成り立つ。鍵の条件や種の条件は要らない。

## 4. まとめと最終定理

§1〜§3 から、$`R`$ は 3 つの定理をすべて満たす。

1. $`\theta \le \Theta`$ かつ $`R(\Theta, a, b)`$ なら $`R(\theta, a, b)`$。
2. 有限反映（[06](06-combinatorial-layer.md) §4）が成り立つ。
3. どの図式 $`G`$ と上端のアトムのリスト $`\mathrm{needs}`$ にも、$`\beta \lt \omega_1`$ と、$`\beta`$ で上から押さえられる $`G`$ の表現があって、$`\mathrm{needs}`$ は上端 $`\beta`$ について成り立つ。

これを [06](06-combinatorial-layer.md) §5 の入口の定理に使うと、1 段の展開の関係は整礎である（[05](05-omegay-mountain.md) §7 の定理 1）。有限反映と鍵の弱化は、[06](06-combinatorial-layer.md) §6、§7 の継ぎ合わせで使われる。残りの定理 2〜4 は、定理 1 から組合せの議論だけで出る。

**強さ.** 証明は選択公理と $`\omega_1`$ の正則性を使う。ラベルは $`\omega_1`$ より下の Good な点で、具体的な値は分からない。順序数の上界や、順序数の表記系（順序数を有限の記号列で表す方法）は得られない。

## 5. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md)「3 つの定理の証明」 | 鍵の弱化、有限反映、最初のラベル付けの要約 |
| [README](../README.md)「公理の監査」 | 証明が使う公理 |
| [notes/01-design.md](../notes/01-design.md) §3、§4 | 3 つの定理の証明と、ファイルの分け方 |

## 6. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| 反映する論理式 $`\Phi`$ | `reflLits`、`reflForm`、`reflLits_holds` | [Por/Relation.lean](../Por/Relation.lean) |
| 有限反映（§2） | `Por.finite_reflection` | 同上 |
| リテラルの部品（§3.1 の 2、4） | `lit_true`、`lit_lower`、`lit_abs` | [Por/Supply.lean](../Por/Supply.lean) |
| 証人を下ろす（§3.1 の 4） | `lower` | 同上 |
| §3.1 の 1 の同値 | `absA`、`absA'` | 同上 |
| 上端述語の絶対性 | `top_abs` | 同上 |
| Good な点どうしの関係 | `good_R` | 同上 |
| すべての図式の表現 | `Por.Supply.initial_finite_graph`（鎖は `points`） | 同上 |
| 組合せの層が呼ぶ名前（Phyrion 氏のものと同じ文で、中身を `Por` の定理にした） | `Reflection.R`（中身は `Por.R`）、`Reflection.key_weaken`、`Reflection.finite_reflection` | [OmegaY/Reflection.lean](../OmegaY/Reflection.lean) |
| 同上 | `OrdinalSupply.Label`、`OrdinalSupply.top`、`OrdinalSupply.initial_finite_graph` | [OmegaY/Reflection/OrdinalSupply.lean](../OmegaY/Reflection/OrdinalSupply.lean) |
| 鍵の長さ $`m`$ への当てはめ（Phyrion 氏のファイルから変えていない。`KeyReflection` は import だけを変えた） | `Model.R`、`Model.key_weaken`、`Model.finite_reflection`、`Model.initial_finite_graph`、`KeyReflection.weaken` | [OmegaY/Model.lean](../OmegaY/Model.lean)、[OmegaY/KeyReflection.lean](../OmegaY/KeyReflection.lean) |
| 制御つきの最初の表現（$`\mathrm{needs}`$ に制御の上端のアトムを足したもの。組合せの層からは呼ばれない。`grep` で確かめた） | `Model.initial_controlled_graph`（鍵の比較は `Keys.eval_lt_of_template_lt`） | [OmegaY/Model.lean](../OmegaY/Model.lean) |
| 最終定理（§4） | `omegaY_step_wellFounded := Dynamics.step_wellFounded_of_actual_representation_descent actual_representation_descent`、`omegaY_generated_isWellOrder`、`omegaY_descendants_isWellOrder`、`omegaY_trajectory_terminates` | [OmegaY/Expansion/WellFounded.lean](../OmegaY/Expansion/WellFounded.lean) |
| 公理の監査 | 名前が `OmegaY.` か `Por.` で始まるすべての定理が、`propext`、`Classical.choice`、`Quot.sound` だけに依存する | [OmegaY/Audit.lean](../OmegaY/Audit.lean) |
