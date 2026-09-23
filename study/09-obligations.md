[← Back](README.md) | [English](en/09-obligations.md) | [Japanese](09-obligations.md)

# 3 つの定理の証明

前提

| ノート | ここで使う言葉 |
|---|---|
| [06 Phyrion 氏の ω-Y の組合せの層](06-combinatorial-layer.md) | 内部の原子、上端の原子、`finite_reflection`、`initial_finite_graph`、制御関係 |
| [07 関係 R](07-relation-r.md) | $`R`$、`R_iff`、`key_weaken`、部分的な上端の述語 |
| [08 ω₁ より下の閉包と閉じた点の列](08-closure-chain.md) | $`\mathfrak B`$、Good、`points` |

このノートは、関係 $`R`$ が組合せの層の 3 つの定理をどう満たすかを説明する。中心は有限反映（§2）と、最初の表現（§3）である。

## 1. 一覧

| 定理 | 証明 | コアが呼ぶ名前 |
|---|---|---|
| 鍵の弱化 | `Por.key_weaken`（[07](07-relation-r.md) §7） | `Reflection.key_weaken`、`KeyReflection.weaken`、`Model.key_weaken` |
| 有限反映 | `Por.finite_reflection`（§2） | `Reflection.finite_reflection`、`Model.finite_reflection` |
| 最初の表現 | `Por.Supply.initial_finite_graph`（§3） | `OrdinalSupply.initial_finite_graph`、`Model.initial_finite_graph` |

コアが呼ぶ名前は、Phyrion 氏のものと同じ文のまま、薄いファイルで与える。

- [OmegaY/Reflection.lean](../OmegaY/Reflection.lean)：`R S θ a b := Por.R S θ a b`。`key_weaken` と `finite_reflection` は `Por` の定理をそのまま返す。
- [OmegaY/Reflection/OrdinalSupply.lean](../OmegaY/Reflection/OrdinalSupply.lean)：`Label` と `top` は `Por.Supply` のもの。`initial_finite_graph` は `Por.Supply.initial_finite_graph` を返す。
- [OmegaY/Model.lean](../OmegaY/Model.lean) と [OmegaY/KeyReflection.lean](../OmegaY/KeyReflection.lean)：鍵の長さ $`m`$ の構文 `keySyntax m` に当てはめたもの。Phyrion 氏のファイルから変えていない（KeyReflection は import だけを変えた）。

## 2. 有限反映

**示すこと.** [06](06-combinatorial-layer.md) §5 の仮定の下で、$`g`$ を作る。記号は次のとおりである。$`n`$ は頂点の数、$`f`$ はラベル、$`b`$ は上端、制御関係は $`R(\theta, f(\mathrm{cut}), b)`$、$`G`$ は内部の原子、$`N`$ は要求である。

**反映する論理式（`reflForm`）.** 変数は $`v_0, \ldots, v_{n-1}`$ で、$`i \lt \mathrm{cut}`$ の位置をパラメータにする。リテラル（`reflLits`）は次の 3 種類である。

```math
\bigwedge_{i, j \lt n} \bigl( (v_i \lt v_j) \iff (i \lt j) \bigr) \ \land\ \bigwedge_{e \in G} \mathrm{Rel}_{e}(\vec v) \ \land\ \bigwedge_{d \in N} \mathrm{Top}_{d}(\vec v)
```

$`\mathrm{Rel}_e(\vec v)`$ は $`R(\mathrm{eval}\ t_e\ \vec v, v_{p_e}, v_{q_e})`$、$`\mathrm{Top}_d(\vec v)`$ は $`R(\mathrm{eval}\ t_d\ \vec v, v_{p_d}, \text{高さ})`$ である。`reflLits_holds` は、このリテラルがすべて成り立つことを、「$`v`$ の順序が添字の順序と同じ」「$`G`$ が成り立つ」「$`N`$ の鍵が定義されていて成り立つ」の 3 つに書き直す。

**証明.**

1. `R_iff` から、高さ $`f(\mathrm{cut})`$ と高さ $`b`$ の構造の、鍵 $`\theta`$ での初等性 $`E`$ を得る。
2. パラメータ $`f(i)`$（$`i \lt \mathrm{cut}`$）は、$`f`$ が狭義増加なので $`f(\mathrm{cut})`$ より小さい。
3. 高さ $`b`$ で、$`v = f`$ が論理式を満たす。順序は $`f`$ の狭義増加から、$`\mathrm{Rel}`$ は $`G`$ の仮定から、$`\mathrm{Top}`$ は「鍵が $`\theta`$ より小さい」（`KeysBelow`）と「$`N`$ が上端 $`b`$ について成り立つ」から出る。
4. $`E`$ から、高さ $`f(\mathrm{cut})`$ でも論理式が真である。その証人を $`g`$ とする。
5. $`g`$ は次を満たす。
   - 順序のリテラルから、$`g`$ は狭義増加である。
   - $`g(i) \lt f(\mathrm{cut})`$（証人は領域の中）。
   - $`i \lt \mathrm{cut}`$ なら $`g(i) = f(i)`$（パラメータ）。
   - $`G`$ が $`g`$ で成り立つ。$`N`$ が上端 $`f(\mathrm{cut})`$ について成り立つ（高さ $`f(\mathrm{cut})`$ の上端の述語は $`R(\cdot, \cdot, f(\mathrm{cut}))`$）。
   - 各点で $`g \le f`$：$`i \lt \mathrm{cut}`$ なら等しく、そうでなければ $`g(i) \lt f(\mathrm{cut}) \le f(i)`$。$`\square`$

**例（[06](06-combinatorial-layer.md) §8 のブロック 0 → 1）.** $`n = 2`$、$`f = (f_0, f_1)`$、$`\mathrm{cut} = 0`$、$`\theta = (f_0, \top)`$、$`b = f_2`$ とする。$`G`$ は列 1 の 2 つの辺、$`N`$ は下の辺 1 つである。反映する論理式は次のとおりである（パラメータは無い）。

```math
\exists v_0\ \exists v_1\ \bigl[\ v_0 \lt v_1 \land R((v_0, v_0), v_0, v_1) \land R((v_0, \top), v_0, v_1) \land \mathrm{Top}_{(v_0, v_0)}(v_0)\ \bigr]
```

- 高さ $`f_2`$ では $`v = (f_0, f_1)`$ が証人である。上端のリテラルの鍵 $`(f_0, f_0)`$ は $`\theta = (f_0, \top)`$ より小さいので定義されていて、$`R((f_0, f_0), f_0, f_2)`$ が成り立つ。
- 反映すると、$`g_0 \lt g_1 \lt f_0`$ で、同じ条件を上端 $`f_0`$ について満たすものが得られる。上端のリテラルの鍵は $`(g_0, g_0)`$ に変わる。鍵が名指す点も証人である。

**使わなかったもの.** $`b`$ が Good であること、$`b`$ や $`f(\mathrm{cut})`$ が極限であること。

## 3. 最初の表現

### 3.1 上端の述語の絶対性

**定理（`top_abs`）.** $`\mathrm{Good}(\alpha)`$ かつ $`\alpha \lt \omega_1`$ とする。すべての鍵 $`\kappa`$ と $`x \lt \alpha`$ について次が成り立つ。

```math
R(\kappa, x, \alpha) \iff R(\kappa, x, \omega_1)
```

**証明.** $`\kappa`$ についての整礎帰納法をする（`WellFoundedLT.induction`、[02](02-well-founded.md) §2）。

1. `R_iff` で両辺を開く。$`x \lt \alpha`$ も $`x \lt \omega_1`$ も真である。残りは、鍵 $`\kappa`$ の論理式 $`\varphi`$（パラメータ $`\lt x`$）について、高さ $`\alpha`$ の構造 $`\mathfrak A^\alpha_\kappa`$ と高さ $`\omega_1`$ の構造 $`\mathfrak A^{\omega_1}_\kappa`$ での真偽が一致することである（`absA`）。
2. $`\varphi`$ が読む上端の述語は、鍵 $`\kappa' \lt \kappa`$ のものだけである。帰納法の仮定から、$`\alpha`$ より下の点では、高さ $`\alpha`$ と高さ $`\omega_1`$ で真偽が同じである（`lit_abs`）。
3. 高さ $`\alpha`$ から高さ $`\omega_1`$：証人は $`\alpha \lt \omega_1`$ より下にあり、2 からリテラルの真偽は同じである。
4. 高さ $`\omega_1`$ から高さ $`\alpha`$：証人 $`v \lt \omega_1`$ を取る。
   - `allow` を「いつも真」に広げる（`lit_true`）。すると $`\mathfrak B`$ での論理式になる。
   - $`\mathrm{Good}(\alpha)`$ で、$`v_i \lt \alpha`$ の位置をパラメータにして証人を下ろす（`lower`）。新しい証人 $`w`$ は $`\alpha`$ より下で、$`v_i \lt \alpha`$ の位置では $`v_i`$ と等しく、各点で $`w \le v`$ である。
   - $`w \le v`$ と `eval` の単調性から、上端のリテラルの鍵は $`\kappa`$ より小さいままである（`lit_lower`）。
   - 2 で高さ $`\alpha`$ の上端の述語に戻す。$`\square`$

4 の 3 つめで、[03](03-sigma1-elementary.md) §8 の「各点で下げても鍵の条件が残る」を使う。

### 3.2 閉じた点どうしは R の関係にある

**定理（`good_R`）.** $`\mathrm{Good}(\alpha)`$、$`\mathrm{Good}(\beta)`$、$`\alpha \lt \beta \lt \omega_1`$ なら、すべての鍵 $`\kappa`$ で $`R(\kappa, \alpha, \beta)`$。

**証明.** $`\alpha \lt \beta`$ である。鍵 $`\kappa`$ の論理式 $`\psi`$ と、パラメータ $`\vec p \lt \alpha`$ について、次の同値をつなぐ。

```math
\mathfrak A^{\alpha}_{\kappa} \models \psi \iff \mathfrak A^{\omega_1}_{\kappa} \models \psi \iff \mathfrak A^{\beta}_{\kappa} \models \psi
```

1 つめは $`\alpha`$ での `absA'`、2 つめは $`\beta`$ での `absA'` である（`absA'` は `absA` に `top_abs` を入れたもの）。$`\square`$

鍵 $`\kappa`$ は何でもよい。閉じた点どうしは、どの鍵でも関係にある。

### 3.3 すべての有限の図式の表現

**定理（`initial_finite_graph`）.** どの $`G`$ と $`N`$ にも、$`\beta \lt \omega_1`$ と狭義増加の $`f \lt \beta`$ があって、$`G`$ が $`f`$ で成り立ち、$`N`$ が上端 $`\beta`$ について成り立つ。

**証明.** $`n`$ を頂点の数とする。$`\beta := c_n`$、$`f(i) := c_i`$（[08](08-closure-chain.md) §7 の閉じた点の列）とする。

- $`f`$ は狭義増加で、$`c_i \lt c_n`$ である（`points_strictMono`）。$`c_n \lt \omega_1`$ である（`points_lt`）。
- 内部の原子 $`e`$ は親 $`\lt`$ 子なので、`good_R` から $`R(\mathrm{eval}\ t_e\ f, c_{p_e}, c_{q_e})`$ である。
- 上端の原子 $`d`$ は親 $`\lt n`$ なので、`good_R` から $`R(\mathrm{eval}\ t_d\ f, c_{p_d}, c_n)`$ である。$`\square`$

1 つの列 $`c`$ が、すべての図式を同時に表現する。鍵の条件（`KeysBelow`）は要らない。

### 3.4 制御つきの最初の表現

[OmegaY/Model.lean](../OmegaY/Model.lean) の `initial_controlled_graph` は、`initial_finite_graph` を $`N`$ に制御の原子を 1 つ足して使い、制御関係と「要求の鍵が制御の鍵より小さい」も得る。鍵の比較は型板の比較（`eval_lt_of_template_lt`）から出る。この定理はコアからは呼ばれない（`grep` で確かめた）。

## 4. 最終定理と公理

最終定理は次のようにつながる（[OmegaY/Expansion/WellFounded.lean](../OmegaY/Expansion/WellFounded.lean)）。

```lean
theorem omegaY_step_wellFounded : WellFounded Dynamics.Step :=
  Dynamics.step_wellFounded_of_actual_representation_descent actual_representation_descent
```

- `actual_representation_descent` は [06](06-combinatorial-layer.md) §8 の降下である。有限反映と鍵の弱化は、その中の継ぎ合わせで使われる。
- 最初の表現は `keyRepresentation_exists` から得る。これは `initial_finite_graph` を使う。
- 残りの 3 つの最終定理は、`omegaY_step_wellFounded` から組合せの議論だけで出る（[05](05-omegay-mountain.md) §7）。

**公理.** [OmegaY/Audit.lean](../OmegaY/Audit.lean) は、名前が `OmegaY.` か `Por.` で始まるすべての定理の公理を調べる。どれも `propext`、`Classical.choice`、`Quot.sound` だけに依存する（[README](../README.md)「公理の監査」）。

**強さ.** 証明は選択公理と $`\omega_1`$ の正則性を使う。ラベルは $`\omega_1`$ より下の閉じた点で、具体的な値は分からない。順序数の上界や表記系は得られない。

## 5. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md)「3 つの定理の証明」 | 鍵の弱化、有限反映、最初のラベル付けの要約 |
| [README](../README.md)「公理の監査」 | §4 の公理 |
| [notes/01-design.md](../notes/01-design.md) §3、§4 | 3 つの定理の証明と、ファイルの分け方 |
| [Por/Relation.lean](../Por/Relation.lean) | §2 |
| [Por/Supply.lean](../Por/Supply.lean) | §3 |
| [OmegaY/Reflection.lean](../OmegaY/Reflection.lean)、[OmegaY/Reflection/OrdinalSupply.lean](../OmegaY/Reflection/OrdinalSupply.lean)、[OmegaY/Model.lean](../OmegaY/Model.lean) | §1 の薄いファイル |
| [OmegaY/Expansion/WellFounded.lean](../OmegaY/Expansion/WellFounded.lean)、[OmegaY/Audit.lean](../OmegaY/Audit.lean) | §4 |

## 6. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| 反映する論理式 | `reflLits`、`reflForm`、`reflLits_holds` | [Por/Relation.lean](../Por/Relation.lean) |
| 有限反映 | `finite_reflection` | 同上 |
| リテラルの部品 | `lit_true`、`lit_lower`、`lit_abs` | [Por/Supply.lean](../Por/Supply.lean) |
| 証人を下ろす | `lower` | 同上 |
| 絶対性の 1 段 | `absA`、`absA'` | 同上 |
| 上端の述語の絶対性 | `top_abs` | 同上 |
| 閉じた点どうしの関係 | `good_R` | 同上 |
| 最初の表現 | `initial_finite_graph` | 同上 |
| 薄いファイル | `Reflection.R`、`Reflection.key_weaken`、`Reflection.finite_reflection` | [OmegaY/Reflection.lean](../OmegaY/Reflection.lean) |
| 同上 | `OrdinalSupply.initial_finite_graph` | [OmegaY/Reflection/OrdinalSupply.lean](../OmegaY/Reflection/OrdinalSupply.lean) |
| 鍵の長さ $`m`$ への当てはめ | `Model.R`、`Model.key_weaken`、`Model.finite_reflection`、`Model.initial_finite_graph`、`Model.initial_controlled_graph` | [OmegaY/Model.lean](../OmegaY/Model.lean) |
| 最終定理 | `omegaY_step_wellFounded`、`omegaY_generated_isWellOrder`、`omegaY_descendants_isWellOrder`、`omegaY_trajectory_terminates` | [OmegaY/Expansion/WellFounded.lean](../OmegaY/Expansion/WellFounded.lean) |
