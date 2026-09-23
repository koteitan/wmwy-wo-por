# memo — wmwy-wo-por

## 経緯

- 2026-09-23：目標を「Phyrion 氏の形式化と同じ展開の定義（weak ω-Y）」に決めた（著作者の指示「まずはPhyrion氏のleanと同じ展開の定義で」）。
- 2026-09-23：v0.1.0。Phyrion 氏の `OmegaY/` を移し、YesMetaZFC を 1y-wo-por の `Por/BMS` と `ZeroY` に替えた。コードの変更は `transGen_head` の 3 か所だけで、そのまま緑になった。
- 2026-09-23：公開（当時の名前 wy-wo-por）。
- 2026-09-23：wmwy-wo-por に改名した。weak-magma ω-Y を公式の ω-Y とは別の数列システムとして扱う。公式の ω-Y は新しいリポジトリ wy-wo-por で扱う（著作者の指示）。
- 2026-09-23：公式の ω-Y の予備調査（notes/02-feasibility.md）。食い違いは magma（充填）の規則だけで起きる。複写辺の鍵の上界（ActualCopiedKeyBound）が、公式 ≠ weak の展開のちょうど全部（1495 回）で破れる。
- 2026-09-23：意味の層を Σ₁ 初等部分構造の関係に替えた（notes/01-design.md）。骨格のファイルを先に書き、関係の部分と供給の部分を 2 つのエージェントで並行に証明し、1 つにまとめた。最初のビルドで緑。

## 行の照合（YesMetaZFC）

EgoFakeFantasy/BMS-Well-Ordering-Lean `bae7e3d` の YesMetaZFC/BMS と、Phyrion 氏の 1-Y のリポジトリの vendor/bms/YesMetaZFC/BMS の全行（正規化して 25 文字以上、5,155 行）と比べた（2026-09-23）。

- `Por/`（このリポジトリと 1y-wo-por で書いたもの）：本体の行の一致は 0。
- `ZeroY/`：12 行、`OmegaY/`：11 行。どれも Phyrion 氏自身のファイルにある汎用の 1 行（`apply List.map_congr_left`、`induction fuel generalizing current with` など）で、YesMetaZFC から写したものではない。

## 公式の ω-Y

公式の ω-Y（Naruyoko 氏のプログラム）と weak ω-Y は食い違う（notes/00-survey.md §1.6）。公式の ω-Y の停止性は未解決で、このリポジトリの定理ではない。
