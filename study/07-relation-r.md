[← Back](README.md) | [English](en/07-relation-r.md) | [Japanese](07-relation-r.md)

# 関係 R

前提

| ノート | ここで使う言葉 |
|---|---|
| [02 整礎関係と整礎再帰](02-well-founded.md) | 辞書式順序、整礎再帰、ガードつきの再帰、鍵、段、上端 |
| [03 構造と Σ₁ 初等部分構造](03-sigma1-elementary.md) | 構造の高さ、証人、位置、`Lit`、`Form`、`Sat`、`ElemL`、内部の関係、上端の述語、部分的な上端の述語、`Lit.holds_of_le` |
| [04 Patterns of resemblance](04-patterns-of-resemblance.md) | 上端の述語を原子記号にする考え方 |
| [06 Phyrion 氏の ω-Y の組合せの層](06-combinatorial-layer.md) | 鍵の構文、型板、組合せの層、`key_weaken` の役割 |

このノートは、このリポジトリのラベルの関係 $`R`$ の定義と、定義から直接出る性質を説明する。Lean のファイルは [Por/Relation.lean](../Por/Relation.lean) である。

## 1. 記号

- $`\mathrm{Label}`$：ラベルの型。整列した線形順序であればよい（Lean の仮定は `LinearOrder` と `WellFoundedLT`）。最終定理で使う具体的な場合を **モデル** と呼ぶ。モデルでは $`\mathrm{Label} = \{o \le \omega_1\}`$ である（[01](01-ordinals.md) §6）。
- $`\mathrm{Key}`$：鍵の型。同じく整列した線形順序であればよい。モデルでは $`\mathrm{Key}_m`$ である（[02](02-well-founded.md) §3。$`m`$ は鍵の長さ）。
- $`S`$：鍵の構文 `KeySyntax Label Key`（[06](06-combinatorial-layer.md) §1）。
- $`R(\theta, a, b)`$：鍵 $`\theta`$、下の点 $`a`$（ラベル）、上の点 $`b`$（ラベル）。$`b`$ は上端である（[02](02-well-founded.md) §3）。Lean では `Por.R S θ a b`。

## 2. 言語

[03](03-sigma1-elementary.md) §7 の言語の記号に、ここで意味を与える。記号は 3 種類である。$`n`$ 変数の型板 $`t`$ と位置 $`i, j \lt n`$ ごとに、次の記号がある。$`\mathrm{Rel}_{t,i,j}`$ と $`\mathrm{Top}_{t,i}`$ は、[03](03-sigma1-elementary.md) §7 の $`\mathrm{Rel}_t(v_i, v_j)`$ と $`\mathrm{Top}_t(v_i)`$ のことである。

| 記号 | 引数の数 | 意味（高さ $`c`$ の構造で） |
|---|---|---|
| $`\lt`$ | 2 | ラベルの大小 |
| $`\mathrm{Rel}_{t,i,j}`$ | $`n`$ | $`\mathrm{Rel}_{t,i,j}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ v_j)`$ |
| $`\mathrm{Top}_{t,i}`$ | $`n`$ | $`\mathrm{Top}_{t,i}(\vec v) :\iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ c)`$ |

$`\vec v = (v_0, \ldots, v_{n-1})`$ は変数の値の列である。$`\mathrm{Rel}`$ は点どうしの関係、$`\mathrm{Top}`$ は点から上端 $`c`$（構造の高さ）への関係である。$`c`$ 自身は領域に無い。どちらの記号も、鍵を $`n`$ 個の点から型板で計算する。

Lean では、リテラル `Lit.rel t i j pos` と `Lit.top t i pos` がこれらの記号を読む（[03](03-sigma1-elementary.md) §7）。真の解釈は次のとおりである。

```lean
def relR : Key → Label → Label → Prop := fun κ x y => R S κ x y
def topR (c : Label) : Key → Label → Prop := fun κ x => R S κ x c
```

## 3. 構造 𝔄^c_θ

**定義.** 鍵 $`\theta`$ と高さ $`c`$ について、構造 $`\mathfrak A^c_\theta`$ を次で定める。

- 領域は $`\{x \mid x \lt c\}`$、順序は $`\lt`$。
- $`\mathrm{Rel}_{t,i,j}`$ はすべての型板で持つ。
- $`\mathrm{Top}_{t,i}(\vec v)`$ は、$`\mathrm{eval}\ t\ \vec v \lt \theta`$ のときだけ定義される。定義されないところでは、上端のリテラルは偽である。

Lean では、$`\mathfrak A^c_\theta`$ での真偽は `Sat (relR S) (topR S c) (· < θ) c φ p` である。

**例.** 鍵の長さを $`m = 1`$ とし、$`\theta = (\omega)`$ とする。型板は ω-Y の型板（[06](06-combinatorial-layer.md) §1）で、$`\mathrm{some}\ 0`$ は座標に $`v_0`$ を置き、$`\mathrm{none}`$ は $`\top`$ を置く。

- 型板 $`(\mathrm{some}\ 0)`$ の上端の述語は、$`v_0 \lt \omega`$ のとき定義される。つまり $`v_0`$ が自然数のときである。
- 型板 $`(\mathrm{none})`$ の上端の述語は、鍵が $`(\top)`$ なので、どこでも定義されない。
- $`\theta = (\top)`$ なら、型板 $`(\mathrm{some}\ 0)`$ の上端の述語は、どこでも定義される。

## 4. 定義

**定義（R）.**

```math
R(\theta, a, b) \iff a \lt b \ \land\ \mathfrak A^{a}_{\theta} \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_{\theta}
```

ここで $`\mathfrak A^{a}_{\theta} \preccurlyeq_{\Sigma_1} \mathfrak A^{b}_{\theta}`$ は、すべての論理式 $`\varphi`$ と、$`a`$ より下のすべてのパラメータ $`\vec p`$ について、次が成り立つことである。列 $`\vec p`$ の各成分が $`a`$ より下であることを $`\vec p \lt a`$ と書く。

```math
\mathfrak A^{a}_{\theta} \models \varphi(\vec p) \iff \mathfrak A^{b}_{\theta} \models \varphi(\vec p)
```

Lean では `ElemL (relR S) (topR S a) (topR S b) θ a b` である（[03](03-sigma1-elementary.md) §8）。2 つの構造で、上端の述語は別のもの（$`a`$ への $`R`$ と $`b`$ への $`R`$）である。

## 5. 再帰

右辺は $`R`$ 自身を読む。段 $`(b, \theta)`$（上端と鍵の組）の辞書式順序 $`\lhd`$（[02](02-well-founded.md) §3）で整礎再帰をする。すべての $`a`$ について一度に定義する。

**右辺が読む R.** 3 種類だけで、どれも段が小さい。

| 読むもの | 段 | 小さい理由 |
|---|---|---|
| $`\mathrm{Rel}(\vec v)`$、つまり $`R(\kappa, x, y)`$ | $`(y, \kappa)`$ | 点は高さ（$`a`$ か $`b`$）より下なので $`y \lt b`$ |
| $`\mathfrak A^{a}_\theta`$ の上端の述語 $`R(\kappa, x, a)`$ | $`(a, \kappa)`$ | $`a \lt b`$ |
| $`\mathfrak A^{b}_\theta`$ の上端の述語 $`R(\kappa, x, b)`$ | $`(b, \kappa)`$ | 定義されるのは $`\kappa \lt \theta`$ のときだけ |

3 行目が要点である。$`\mathfrak A^{b}_\theta`$ の上端の述語を鍵 $`\theta`$ より下でだけ定義したので、右辺は段 $`(b, \theta)`$ 自身を読まない。

**Lean の再帰（`stepF`）.** 段 $`s = (b, \theta)`$ で、$`R(\theta, \cdot, b)`$ を満たす $`a`$ の集合を返す。3 つの解釈には、段が小さいことの証明をガードとして付ける（[02](02-well-founded.md) §5）。

| 段の解釈 | 式 |
|---|---|
| 内部の関係 | $`\mathrm{rel}(\kappa, x, y) :\iff \exists h : y \lt b,\ R(\kappa, x, y)`$ |
| 高さ $`a`$ の上端 | $`\mathrm{top}_A(\kappa, x) :\iff R(\kappa, x, a)`$（ガードは $`a \lt b`$ で、`stepF` の先頭で要求する） |
| 高さ $`b`$ の上端 | $`\mathrm{top}_B(\kappa, x) :\iff \exists h : \kappa \lt \theta,\ R(\kappa, x, b)`$ |

```lean
noncomputable def stepF (s : Label × Key) (IH : ∀ t, StageLT t s → Label → Prop) :
    Label → Prop :=
  fun a => ∃ hab : a < s.1,
    ElemL (S := S)
      (fun κ x y => ∃ h : y < s.1, IH (y, κ) (Prod.Lex.left _ _ h) x)
      (fun κ x => IH (a, κ) (Prod.Lex.left _ _ hab) x)
      (fun κ x => ∃ h : κ < s.2, IH (s.1, κ) (Prod.Lex.right _ h) x)
      s.2 a s.1

noncomputable def R (θ : Key) (a b : Label) : Prop :=
  stage_wf.fix (stepF S) (b, θ) a
```

## 6. ガードを外す：R_iff

**定理（`R_iff`）.**

```math
R(\theta, a, b) \iff a \lt b \land \mathrm{ElemL}(\mathrm{relR}, \mathrm{topR}(a), \mathrm{topR}(b), \theta, a, b)
```

**証明.** `WellFounded.fix_eq` で 1 段展開すると、左辺は「$`a \lt b`$ かつ、段の解釈での `ElemL`」になる。$`a \lt b`$ の下で、段の解釈と真の解釈が、論理式の読むところで一致することを示す（`sat_congr`、[03](03-sigma1-elementary.md) §8）。

1. 内部の関係：読むのは第 2 の点が高さより下のところだけである。高さは $`a`$ か $`b`$ で、どちらも $`b`$ 以下なので、ガード $`y \lt b`$ は真である。
2. 高さ $`a`$ の上端：ガードは $`a \lt b`$ で、仮定そのものである。
3. 高さ $`b`$ の上端：読むのは定義されている鍵 $`\kappa \lt \theta`$ だけである。ガード $`\kappa \lt \theta`$ はそのまま真である。

よって真偽が一致し、ガードを外した式が得られる。$`\square`$

## 7. 定義から直接出る性質

**定理（`R_lt`）.** $`R(\theta, a, b)`$ なら $`a \lt b`$。`R_iff` の第 1 項である。

**定理（`key_weaken`、鍵の弱化）.** $`\theta \le \Theta`$ かつ $`R(\Theta, a, b)`$ なら $`R(\theta, a, b)`$。

**証明.** `R_iff` で $`a \lt b`$ と、鍵 $`\Theta`$ での初等性 $`E`$ を得る。鍵 $`\theta`$ の論理式 $`\varphi`$ とパラメータ $`\vec p \lt a`$ について、2 つの向きを示す。

- 高さ $`a`$ から高さ $`b`$：高さ $`a`$ の証人 $`w`$ を取る。すべての位置をパラメータにした論理式 $`\varphi'`$ を作る（パラメータは $`w`$ で、どれも $`a`$ より下）。$`\theta \le \Theta`$ なので、$`w`$ は鍵 $`\Theta`$ でも $`\varphi'`$ を満たす（`Lit.holds_allow_mono`）。$`E`$ から、高さ $`b`$ でも鍵 $`\Theta`$ で $`\varphi'`$ が真である。変数はすべて固定なので、証人は $`w`$ そのものである。上端のリテラルの鍵は $`w`$ だけで決まり、高さ $`a`$ で $`\theta`$ より下だった。よって高さ $`b`$ でも鍵 $`\theta`$ で成り立つ（`Lit.holds_of_le` を $`w \le w`$ で使う）。
- 高さ $`b`$ から高さ $`a`$：高さ $`b`$ の証人 $`v`$ を取る。$`v_i \lt a`$ の位置をパラメータにした論理式 $`\varphi'`$ を作る。$`\theta \le \Theta`$ なので、$`v`$ は鍵 $`\Theta`$ でも $`\varphi'`$ を満たす。$`E`$ から、高さ $`a`$ の証人 $`w`$ があり、$`v_i \lt a`$ の位置では $`w_i = v_i`$ である。ほかの位置では $`w_i \lt a \le v_i`$ である。よって各点で $`w \le v`$ である。上端のリテラルの鍵は $`\mathrm{eval}\ t\ w \le \mathrm{eval}\ t\ v \lt \theta`$ なので、$`w`$ は鍵 $`\theta`$ でも成り立つ（`Lit.holds_of_le`）。元のパラメータの位置は $`p_i \lt a`$ なので、$`w`$ はそこで $`p`$ と一致する。$`\square`$

2 つめの向きで、証人を各点で下げることが要る。そのため `eval` の単調性（[06](06-combinatorial-layer.md) §1 の `monotone_eval`）を使う。

**性質（定義された上端の述語の一致）.** $`R(\theta, a, b)`$ で、$`\vec v \lt a`$ とする。$`\mathrm{eval}\ t\ \vec v \lt \theta`$ なら、次が成り立つ。

```math
R(\mathrm{eval}\ t\ \vec v,\ v_i,\ a) \iff R(\mathrm{eval}\ t\ \vec v,\ v_i,\ b)
```

**理由.** すべての変数がパラメータの論理式 $`\mathrm{Top}_{t,i}(\vec v)`$ を使う。高さ $`a`$ では左辺、高さ $`b`$ では右辺を意味する。この性質は Lean の定理としては書いていない。証明では、似た形の `top_abs`（Good な点と $`\omega_1`$ の間での上端の述語の一致、[09](09-obligations.md) §3）を使う。Good は [08](08-closure-chain.md) §1 で定義する。

**性質（下の点は極限順序数）.** ラベルが順序数で $`R(\theta, a, b)`$ なら、$`a`$ は 0 でない極限順序数である。

**理由.** [03](03-sigma1-elementary.md) §5 の例と同じである。

- $`a = 0`$ のとき：1 変数、パラメータなし、リテラルなしの論理式 $`\exists v_0\ (\text{真})`$ は、高さ $`b`$ で真、高さ 0 で偽である。
- $`a = \gamma + 1`$ のとき：パラメータ $`\gamma \lt a`$ の $`\exists v_1\ (\gamma \lt v_1)`$ は、高さ $`b`$ で真（$`v_1 = \gamma + 1 \lt b`$）、高さ $`a`$ で偽である。

どちらも初等性に反する。この性質は Lean では示していない。組合せの層も使わない。

## 8. 使わない性質

**推移性.** $`R(\theta, a, b) \land R(\theta, b, c) \implies R(\theta, a, c)`$ である。中間の構造 $`\mathfrak A^b_\theta`$ は 2 つの関係で同じものなので、パラメータ $`\vec p \lt a`$ の論理式について 2 つの同値をつなげばよい。この性質は Lean では示していない。組合せの層も使わない。

## 9. このリポジトリでの使われ方

| 場所 | 使い方 |
|---|---|
| [README](../README.md)「関係 R」 | 定義の式と、再帰の段 |
| [README](../README.md)「3 つの定理の証明」 | 鍵の弱化の証明の要約 |
| [notes/01-design.md](../notes/01-design.md) §2、§3.1 | 定義、再帰、鍵の弱化 |
| [Por/Relation.lean](../Por/Relation.lean) | このノートのすべて |
| [OmegaY/Reflection.lean](../OmegaY/Reflection.lean) | `Reflection.R` を `Por.R` で、`Reflection.key_weaken` を `Por.key_weaken` で与える |

## 10. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| 段と順序 | `StageLT`、`stage_wf` | [Por/Relation.lean](../Por/Relation.lean) |
| 再帰の 1 段 | `stepF` | 同上 |
| 関係 | `R` | 同上 |
| 真の解釈 | `relR`、`topR` | 同上 |
| 定義の式 | `R_iff` | 同上 |
| 真に小さい | `R_lt` | 同上 |
| 鍵の弱化 | `key_weaken` | 同上 |
| 初等性、真偽 | `ElemL`、`Sat` | [Por/Formula.lean](../Por/Formula.lean) |
| 読むところだけで決まる | `sat_congr` | 同上 |
| 鍵の弱化の部品 | `Lit.holds_allow_mono`、`Lit.holds_of_le` | 同上 |
