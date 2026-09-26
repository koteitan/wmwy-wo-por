[← Back](README.md) | [English](rule.md) | [Japanese](../rule.md)

# Working rules for study/

## Order

- Arrange the material so that it can be read from the top. Do not use a term that no earlier section or note has explained.
- Start each note with a "Prerequisites" table that says which terms of earlier notes it uses.
- End each note with a table "Where this repository uses it" that lists README sections and notes/ sections, followed by a table "Lean correspondence" (concept, Lean name, file).

## Content

- Write the definition first, then a small example.
- Give a proof or a proof outline for each theorem. Say so when something is not proved here.
- When example values are computed, say how (by hand or by computer).
- Do not write about the formalization (the proof assistant) in the main text. Names, files and code of the formalization go only in the final "Lean correspondence" table. Give theorems and objects a mathematical name or a number ("Property 2", "Lemma 1 of §8", and so on).
- Where the mathematics is the same as in the 1-Y version (study/ of [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por)), use the same sentences and formulas as the 1-Y version. Change only what differs mathematically.

## Sentences

- Write short sentences, one point per sentence.
- Do not use metaphors. Use literal words.
- Write in formulas what can be written in formulas.

## Formulas (so that GitHub renders them)

- Write inline math as `` $`...`$ ``.
- Write display math in a ```` ```math ```` fence.
- In inline math write the inequality signs as `\lt` and `\gt`.
- Break rows with `\cr`. Do not use two backslashes.
- Inside a list item, do not use a math fence. Use inline math only.
- Do not write `|` in math inside a table cell. Use `\mid`.

## References to other projects

- Refer to other projects by their public GitHub URL. Do not write local paths.
