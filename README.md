[English](README-en.md) | [Japanese](README.md)

# wy-wo-por：patterns of resemblance による weak ω-Y の整礎性

weak ω-Y 数列システムの展開が整礎であることを、Lean 4 で証明したリポジトリである。

証明は Phyrion 氏の証明（[Phyrion1343/omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean)）に基づく。その証明の組合せの部分はそのまま使う。意味の部分だけを、patterns of resemblance の形の関係（$`\Sigma_1`$ 初等部分構造）に取り替えた。構成的宇宙 $`L`$ も許容順序数も使わない。姉妹プロジェクト [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por) が 1-Y でしたことの ω-Y 版である。

- Lean 4.33.1、Mathlib v4.33.1。
- `sorry` は無い。新しい公理も無い。公理は `propext`、`Classical.choice`、`Quot.sound` だけである。
- ライセンスの無い YesMetaZFC に依存しない。

## 対象

対象は Phyrion 氏の形式化と同じ展開である。「weak magma、no extraction」の ω-Y と呼ばれる。展開の規則は [OmegaY/Expansion/Build.lean](OmegaY/Expansion/Build.lean) にある。

これは公式の ω-Y（Naruyoko 氏のプログラム）と一致しない。標準形 3001 個で比べると、9003 回の展開のうち 480 回で結果が違う。最小の例は $`(1,3,3)[2]`$ である。詳しくは [notes/00-survey.md](notes/00-survey.md) にある。公式の ω-Y の停止性は、このリポジトリの定理ではない。

## 何を証明したか

### 記号

- 式は、正の整数の有限列で、空か、または最初の項が 1 のものである（`Dynamics.Expr`）。
- $`s[N]`$ は、式 $`s`$ をコピーの回数 $`N`$ で展開したものである（`expand s N`）。
- $`t \prec s`$（`Dynamics.Step t s`）は、$`s \ne ()`$ かつ、ある $`N`$ で $`t = s[N]`$ であることである。
- $`s \to^{*} t`$ は、$`s`$ から 0 回以上の展開で $`t`$ に届くことである。
- $`\lt_{\mathrm{lex}}`$ は式の辞書式順序である。

### 最終定理 4 つ

最終定理は [OmegaY/Expansion/WellFounded.lean](OmegaY/Expansion/WellFounded.lean) にある。名前空間は `OmegaY.Expansion` である。

1. `omegaY_step_wellFounded`：$`\prec`$ は整礎である。つまり、次の形の無限列は無い。

```math
s_0,\ s_1,\ s_2,\ \ldots \qquad s_n \ne (),\quad s_{n+1} = s_n[N_n] \quad (n \in \mathbb N)
```

2. `omegaY_generated_isWellOrder`：標準の種 $`(1, m+2)`$ から生成される式の集合は、$`\lt_{\mathrm{lex}}`$ で整列する。
3. `omegaY_descendants_isWellOrder`：どの式 $`s`$ についても、$`\{\, t \mid s \to^{*} t \,\}`$ は $`\lt_{\mathrm{lex}}`$ で整列する。
4. `omegaY_trajectory_terminates`：コピーの回数の列 $`N_0, N_1, \ldots`$ をどう選んでも、展開の列はいつか空の列に着く。

1 番目が中心である。2〜4 番目は、組合せの層が 1 番目から導く。

## 証明の形

Phyrion 氏の証明は二層に分かれる。

- 組合せの層（`OmegaY/` の大部分と `ZeroY/`）。ω-Y の山を有限のグラフにし、各列に $`\omega_1`$ 以下の順序数のラベルを付ける。展開したあとのグラフにも、末尾のラベルがもっと小さいラベル付けがあることを示す。
- 意味の層。ラベルの関係 $`R(\theta,a,b)`$ を与える。$`\theta`$ は鍵である。鍵は長さ $`m`$ のベクトル $`\mathrm{Key}_m = \mathrm{Lex}(\mathrm{Fin}\ m \to \mathrm{Label} \cup \{\top\})`$ で、$`m`$ は始めの式ごとに決まる。

組合せの層が意味の層から使うのは、次の 3 つの定理だけである。

| 名前 | 内容 |
|---|---|
| `Reflection.key_weaken` | $`\theta \le \Theta`$ かつ $`R(\Theta,a,b)`$ なら $`R(\theta,a,b)`$ |
| `Reflection.finite_reflection` | 有限反映：$`b`$ より下の有限のグラフと、$`b`$ への要求（鍵が $`\theta`$ 未満）を、$`R(\theta, f(\mathrm{cut}), b)`$ で $`f(\mathrm{cut})`$ より下へ写せる。切れ目より前の点は動かない |
| `OrdinalSupply.initial_finite_graph` | どの有限のグラフにも、$`\omega_1`$ より下にラベル付けがある |

Phyrion 氏の意味の層も許容順序数を使わない。そこでは $`R(\theta,a,b)`$ は「$`b`$ より下の有限の正のグラフを、$`a`$ より下へ圧縮できる」ことである。このリポジトリは、それを $`\Sigma_1`$ 初等部分構造の関係に替えた。

## 関係 R

```math
R(\theta,a,b) \iff a \lt b \ \land\ \mathfrak A^{a}_{\theta} \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_{\theta}
```

$`\mathfrak A^{c}_{\theta}`$ は高さ $`c`$ の構造である。

- 領域は $`\{x \mid x \lt c\}`$、順序は $`\lt`$。
- 内部の関係：鍵の型板 $`t`$ と位置 $`i, j`$ ごとに、$`\mathrm{Rel}_{t,i,j}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ v_j)`$。
- 上端の述語：型板 $`t`$ と位置 $`i`$ ごとに、$`\mathrm{Top}_{t,i}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ c)`$。ただし鍵 $`\mathrm{eval}\ t\ \vec v`$ が $`\theta`$ 未満のときだけ定義される。上端のリテラルは、定義されているときだけ真になりうる。
- $`\preccurlyeq_{\Sigma_1}`$：$`a`$ より下のパラメータを持つすべての $`\Sigma_1`$ 論理式（リテラルの連言に存在量化を付けたもの）の真偽が、2 つの構造で一致する。

右辺は $`R`$ 自身を読む。そこで $`R`$ を、（上端、鍵）の辞書式順序による整礎再帰で定義する。右辺が読む $`R`$ は、どれも段が小さい。Lean では `Por.R` と、その定義の式 `Por.R_iff` である（[Por/Relation.lean](Por/Relation.lean)）。

### 3 つの定理の証明

- 鍵の弱化：$`\mathfrak A^{b}_{\theta}`$ の証人のうち $`a`$ より小さいものをパラメータに移し、残りを下へ写す。新しい証人は元の証人以下（各点）になる。$`\mathrm{eval}`$ は単調なので、鍵は $`\theta`$ 未満のままである。
- 有限反映：グラフと要求を 1 つの $`\Sigma_1`$ 論理式に書いて、$`\Sigma_1`$ 初等性で下へ写す。
- 最初のラベル付け：$`\mathrm{Good}(\alpha)`$ を「上端の述語をすべて定義した高さ $`\omega_1`$ の構造の、$`\Sigma_1`$ 初等部分構造である」とする。論理式は可算個なので、Good な点は $`\omega_1`$ の中で共終である。Good な点では、上端を $`\alpha`$ と $`\omega_1`$ で取り替えても $`R`$ は変わらない（`top_abs`、鍵の帰納法）。Good な点どうしは、すべての鍵で $`R`$ の関係にある（`good_R`）。Good な点の列が、どの有限のグラフも表す。

証明は選択公理と $`\omega_1`$ の正則性を使う。順序数の上界や表記系は得られない。

詳しい設計は [notes/01-design.md](notes/01-design.md) にある（日本語）。

## ファイル

| 場所 | 中身 |
|---|---|
| [Por/Formula.lean](Por/Formula.lean)、[Por/Relation.lean](Por/Relation.lean)、[Por/Supply.lean](Por/Supply.lean) | 意味の層のモデル。約 650 行。Mathlib を使う |
| [OmegaY/Reflection.lean](OmegaY/Reflection.lean)、[OmegaY/Reflection/](OmegaY/Reflection/) | 組合せの層が呼ぶ名前を、モデルの定理で与える薄いファイルと、インターフェースの定義 |
| [Por/BMS/](Por/BMS/) | 0-Y の層が呼ぶ BMS の層。1y-wo-por で書いたもの。約 3,300 行 |
| [ZeroY/](ZeroY/) | Phyrion 氏の 0-Y の層。1y-wo-por を通して移した。20 モジュール |
| [OmegaY/](OmegaY/) | Phyrion 氏の ω-Y の組合せの層を移したもの。549 モジュール |
| [notes/](notes/) | 調査と設計のノート（日本語） |
| [LICENSE](LICENSE)、[NOTICE](NOTICE) | Apache-2.0 と出どころの記録 |

## ビルド

```sh
lake exe cache get
lake build
```

- 既定のターゲットは `Por` と `OmegaY` である。`OmegaY` は公理の監査 [OmegaY/Audit.lean](OmegaY/Audit.lean) まで含む。
- 2026-09-23 に `leanman build` を実行した。終了コードは 0 である。

## 公理の監査

[OmegaY/Audit.lean](OmegaY/Audit.lean) は、名前が `OmegaY.` か `Por.` で始まるすべての定理の公理を調べる。出力は次のとおりである（2026-09-23）。

```text
Audited 6614 research theorems: only propext, Classical.choice and Quot.sound occur. No new axiom declaration.
'OmegaY.Expansion.omegaY_step_wellFounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'OmegaY.Expansion.omegaY_generated_isWellOrder' depends on axioms: [propext, Classical.choice, Quot.sound]
'OmegaY.Expansion.omegaY_descendants_isWellOrder' depends on axioms: [propext, Classical.choice, Quot.sound]
'OmegaY.Expansion.omegaY_trajectory_terminates' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 謝辞とライセンス

このリポジトリは Apache License 2.0 である（[LICENSE](LICENSE)）。出どころと変更点は [NOTICE](NOTICE) に書いてある。

- 組合せの層：[Phyrion1343/omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean)（Apache-2.0、リビジョン `33c16a8`）の `OmegaY/` を移したものである。証明の全体の形も Phyrion 氏による。各ファイルの先頭に、元のパスと変更点を書いてある。
- 0-Y の層：[Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean)（Apache-2.0、リビジョン `6533b29`）の `formalization/ZeroY` を、1y-wo-por を通して移したものである。
- BMS の層：`Por/BMS/` は 1y-wo-por のために書いたものである。Phyrion 氏の ω-Y の形式化は、ライセンスの無い BMS のコード（YesMetaZFC、[EgoFakeFantasy/BMS-Well-Ordering-Lean](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean)）に依存する。このリポジトリはそれに依存せず、その行を 1 行も写していない。

## 参考文献

- Phyrion, [omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean). weak ω-Y の整礎性の Lean の形式化。
- Phyrion, [1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean). 1-Y の整礎性の Lean の形式化。
- T. J. Carlson, Elementary patterns of resemblance, Annals of Pure and Applied Logic 108 (2001), 19–77.
- koteitan, [1y-wo-por](https://github.com/koteitan/1y-wo-por). patterns of resemblance による 1-Y の整礎性。
- koteitan, [bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern). patterns of resemblance による BMS の整礎性。
