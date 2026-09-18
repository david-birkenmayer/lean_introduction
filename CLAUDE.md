# Lean Introduction — workshop materials

Teaching material for a ~one-session **introduction to Lean 4 for mathematicians**
(AG Optimierung, RPTU Kaiserslautern). Author: David A. Birkenmayer.

The session alternates: **slides → participants play in a Lean file → slides → …**.
Participants edit the files in the browser (Lean web editor, `live.lean-lang.org`),
not in a local checkout.

## Teaching goals (drive every decision here)

1. Show that **dependent type theory can express mathematics**.
2. Get participants **typing their own proofs**, not just watching.
3. Teach basic Lean syntax in **term mode**. Tactics are only peeked at right at
   the end — do not introduce `by`, `simp`, `induction`, `rfl`, … into the
   exercises unless explicitly asked.

## Layout

| Path | What it is |
| --- | --- |
| `interactive/part{1..4}_*.lean` | **The current exercise files.** One per stage, handed out in order. |
| `solutions/part{1..4}_*.lean` | Intended to be the filled-in twin of each `interactive/` file. |
| `interactive.lean`, `interactive_solutions.lean` | The **original single-file version**, superseded by `interactive/`. Kept as reference — `interactive_solutions.lean` is the only place where *all* proofs (incl. `commutative`) are actually solved. |
| `presentation/main.typ` | The slide deck (Typst + Touying). Still largely a skeleton with `*blah:*` placeholders. |
| `presentation/university.typ`, `template.typ` | RPTU-branded Touying theme by Fabian von der Warth; `template.typ` is his original deck kept as a usage example. Treat both as vendored — edit `main.typ`. |
| `ideas.txt` | Loose brain-dump of topics that might make it into slides. Not a spec. |

The four parts: **1 natural numbers / functions**, **2 `Even` as an inductive
predicate**, **3 `NEqual` (`≡`) and its equivalence properties**, **4 `add`,
with `commutative` as the "final boss"**.

## Conventions in the Lean files

- **Each file is self-contained and importless.** No `import`, no Mathlib, no
  `Nat` — everything is rebuilt from the custom `inductive N`. A participant must
  be able to paste one file into the web editor and have it work standalone.
  So `partN` re-declares everything from earlier parts, **already solved**, as a
  prelude above its own exercises.
- **`_` is the exercise hole.** It is deliberately *not* `sorry`: Lean reports
  "don't know how to synthesize placeholder" and shows the **expected type and
  local context in the Infoview**, which is exactly the pedagogical point.
  A file with unsolved exercises is *supposed* to show errors.
- ASCII arrows `->`, not `→`. `succ (succ zero)`, not numerals.
- `set_option pp.fieldNotation false` at the top of every file, so the Infoview
  prints `succ (succ zero)` instead of `zero.succ.succ`.
- Custom notation: `infix:20 (priority := high) " ≡ " => NEqual`,
  `infix:50 (priority := high) " + " => add`.
- Comments are addressed to the participant in second person ("Exercise: …",
  "Guess the result without looking!", "Uncomment this next line: why does it fail?").
  Keep that voice.
- Recursion is done with `match … with` in term mode (including proofs by
  recursion on a proof, e.g. `symmetric`), relying on Lean's structural
  termination checker.

## Current state / known rough edges

Worth confirming with the user before "fixing" any of these — several are just
mid-migration:

- `interactive/` and `solutions/` are **untracked**; git still has the old names
  `stages/` and `stages_solutions/` staged as deleted. The rename is uncommitted.
- **`solutions/` is stale.** Only `part1` matches its `interactive/` twin. `part2`,
  `part3` and `part4` are copies of the old monolithic `interactive.lean` cut at
  successive points — each one solves the *previous* part and leaves its own part
  as `_`. They are effectively another copy of the exercise files, not solutions.
- `interactive/part4_addition.lean` has a header typo: `Part 3: Addition`.
- `main.typ` slides 2–4 end in `*blah:*` placeholder overlays.

## Building

**Lean:** there is no `lakefile` and no `elan`/`lean` on this machine — the Lean
files **cannot be typechecked locally**. `lean-toolchain` pins
`leanprover/lean4:v4.34.0` only to record the version the web editor should match.
When changing Lean code, reason it through carefully; you cannot compile to check.

**Slides:** `typst` is installed. Fonts are bundled next to the deck, so:

```bash
cd presentation && typst compile --font-path . --root . main.typ
```

Two harmless warnings are expected: `main.typ` asks for `Latin Modern Sans 17`
but only `Latin Modern Sans 12` (`lmsans12-regular.otf`) is bundled.
