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
| `interactive_sol/part{1..4}_*.lean` | The filled-in twin of each `interactive/` file — same text, holes filled. Keep them diff-identical apart from the hole lines. |
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
- Say **term**, never "expression" — Lean's own name for this style is
  *term mode*, and the course teaches it by that name.
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

- `interactive_sol/` is **untracked**, and git still has `solutions/` staged as
  deleted (that directory was renamed). Uncommitted.
- **`interactive_sol/` is stale for parts 2–4.** `part1` is a true twin of its
  exercise file (verified: 0 errors, diff is only the hole lines). `part2`,
  `part3` and `part4` are still copies of the old monolithic `interactive.lean`
  cut at successive points — each solves the *previous* part and leaves its own
  part as `_`, so they are extra exercise files, not solutions.
- `interactive/part4_addition.lean` has a header typo: `Part 3: Addition`.
- `main.typ` slides 2–4 end in `*blah:*` placeholder overlays.

## Building

**Lean:** elan is installed at `~/.elan/bin` with `leanprover/lean4:v4.34.0`,
matching `lean-toolchain`. It is on `PATH` only for *login* shells (added by
`~/.profile`), so in a non-login shell prefix commands with:

```bash
export PATH="$HOME/.elan/bin:$PATH"
```

There is no `lakefile`, but none is needed — the files have no imports, so
`lean interactive/part1_natural_numbers.lean` typechecks a file directly.
**Always typecheck Lean changes before reporting them.** Note that exercise files
are *expected* to error on their `_` holes; compare against the solution instead.

**Slides:** `typst` is installed. Fonts are bundled next to the deck, so:

```bash
cd presentation && typst compile --font-path . --root . main.typ
```

Two harmless warnings are expected: `main.typ` asks for `Latin Modern Sans 17`
but only `Latin Modern Sans 12` (`lmsans12-regular.otf`) is bundled.
