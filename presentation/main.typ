#import "university.typ": *
// The Lean logo spelling: L∃∀N (quantifiers from the bundled math font, which has the glyphs).
// "Latin Modern Sans 17" is the thin large-size cut, so the letters match the thin quantifiers.
#let lean = box(text(font: "Latin Modern Sans 17")[L#text(font: "Latin Modern Math")[∃∀]N])
#let ub = "ub"
#let lb = "lb"
#let subs = $subset.eq$
#let sups = $supset.eq$
#let eps = $epsilon$
#let ni = $in.rev$
#let nin = $in.not$
#let nni = $in.not.rev$
#let bset(a, b) = ${#a | #b}$
#let time(a) = $cal(O)(#a)$
#let ip(x, y) = $lr(angle.l #x, #y angle.r)$
#let script-symbols = (sym.lt, sym.lt.eq, sym.lt.equiv, sym.gt, sym.gt.eq, sym.gt.equiv, sym.prec.eq, sym.prec.eq, sym.succ.eq, sym.prec, sym.succ, sym.prec.equiv, sym.succ.equiv, sym.prec.eq.not, sym.prec.neq, sym.prec.nequiv, sym.succ.neq, sym.succ.nequiv)
#show math.equation: eq => {
  set text(weight: 400)
  set block(breakable: true)
  show regex(script-symbols.join("|")): math.scripts
  eq
}

#show: university-theme.with(
  aspect-ratio: "16-9",
  main-color: "dunkelblau",
  secondary-color: "hellblau",
  affiliations: ("RPTU Kaiserslautern-Landau"),
  sponsor-logos: ("/logos/affiliations/RPTU_Minimal.svg"),
  config-info(
    title: text(font: "Latin Modern Sans 17")[Introduction into \ #text(size: 2em, lean)],
    short-title: "Introduction into Lean",
    author: ("David A. Birkenmayer"),
    institution: "AG Optimierung, RPTU Kaiserslautern",
  ),
)

// Restyle the two markup shortcuts. NOTE: two stacked `#show ...: set text(...)` rules (one
// carrying font: "Red Hat Text") make Touying collapse to a single slide — use the function
// form instead, which is robust.
//  *strong* -> real bold, black (LM Sans has no bold face, so use the bundled Red Hat Text).
//  _emph_   -> red italic (takes over the theme's old red accent).
#show strong: it => text(fill: black, font: "Red Hat Text", weight: "bold", it.body)
#show emph: it => text(fill: red, style: "italic", it.body)


== What is L$exists$$forall$N?

#slide(repeat: 3, self => [
  #let (uncover, only) = utils.methods(self)

  #v(2em)
  #uncover("1-")[
    Lean is...
    - a _functional programming language_
  ]
  #uncover("2-")[
    - _statically_ and _dependently typed_
  ]

  #uncover("3-")[
    - a _theorem prover_
  ]


])


== imperative vs functional programming
#let imp-fill = rptu-colors.orange.lighten(86%)
#let fun-fill = rptu-colors.hellblau.lighten(88%)
#let imp-ink = rptu-colors.orange.darken(45%)
#let fun-ink = rptu-colors.dunkelblau
#let th(c, body) = text(font: "Red Hat Text", weight: "bold", fill: c, body)

#let py-sum = [```
def total(xs):
    s = 0
    for x in xs:
        s = s + x
    return s
```]

#let lean-sum = [```
def total (xs : List Int) : Int :=
  match xs with
  | []     => 0
  | x :: ys => x + total ys
```]

// One table: shared header, the example, then the comparison rows, which
// appear one per subslide. `self.subslide` also gates the row tint, so an
// unrevealed row shows nothing at all rather than an empty coloured band.
// `annot`, if given, is (after: <row index>, span: <rows>, label: .., height: ..).
// It inserts one extra beat right after row `after`, in which a brace appears
// spanning the last `span` rows; rows below that point shift one beat later.
#let example-table(self, head-a, head-b, rows, annot: none) = {
  let uncover = utils.methods(self).uncover
  let a-start = if annot == none { -1 } else { annot.after - annot.span + 1 }
  let a-stage = if annot == none { 0 } else { annot.after + 3 }
  let stage-of(i) = i + 2 + (if annot != none and i > annot.after { 1 } else { 0 })
  let body = ()
  for (i, r) in rows.enumerate() {
    for c in r { body.push(uncover(str(stage-of(i)) + "-", c)) }
    if annot == none or i < a-start or i > annot.after {
      body.push([])
    } else if i == a-start {
      body.push(table.cell(rowspan: annot.span, uncover(str(a-stage) + "-",
        place(right + horizon, dx: -30pt, box(width: 140pt, align(right,
          [$stretch(brace.r, size: #annot.height)$ #h(5pt) #annot.label]))))))
    }
  }
  table(
    columns: (8.5em, 1fr, 1fr, 0pt),
    inset: (x, y) => if x == 3 { 0pt } else { (x: 8pt, y: 7pt) },
    align: (x, y) => {
      let v = if y == 1 { top } else { horizon }
      if x == 0 { right + v } else { left + v }
    },
    stroke: (x, y) => if y == 0 {
      (bottom: 0.8pt + rptu-colors.dunkelblau)
    } else if y == 1 {
      (bottom: 0.5pt + rptu-colors.blaugrau.lighten(45%))
    },
    fill: (x, y) => if y >= 1 and y <= self.subslide {
      if x == 1 { imp-fill } else if x == 2 { fun-fill }
    },
    table.header([], th(imp-ink, head-a), th(fun-ink, head-b), []),
    [example], py-sum, lean-sum, [],
    ..body
  )
}

#slide(repeat: 10, self => [
  #let (uncover, only) = utils.methods(self)

  #v(1em)
  #set text(size: 0.95em)
  #example-table(self, [Python --- imperative], [Lean --- functional], (
    ([a program],   [changes a state],
                       [builds a term]),
    ([code describes], [a sequence of instructions],
                       [applying and composing functions]),
    ([variables are],  [mutable],
                       [immutable]),
    ([repetition is],  [a loop],
                       [recursion]),
    ([a function is],  [a subroutine],
                       [a value with a type]),
    ([a function can], [have side-effects],
                       [only map input to output]),
    ([the same inputs], [can result in different outputs],
                       [will produce the same outputs]),
    ([you gain],       [speed and control],
                       [abstraction]),
  ), annot: (after: 6, span: 2, label: [_pure function_], height: 41pt))
])


== dynamic vs static typing

#slide(repeat: 4, self => [
  #v(1em)
  #set text(size: 0.95em)
  #example-table(self, [Python --- dynamically typed], [Lean --- statically typed], (
    ([types are checked], [at run-time],
                          [at compile-time]),
    ([a type error is],   [a crash, on the unlucky input],
                          [a compilation error]),
    ([a type is],         [an optional hint, ignored by the interpreter],
                          [a promise the compiler enforces]),
  ))
])

== L$exists$$forall$N is statically typed

#slide(repeat: 2, self => [
  #let (uncover, only) = utils.methods(self)

  #v(0.5em)
  #uncover("1-")[
    This is a second, independent axis: C is statically typed and imperative,
    Python is dynamically typed and imperative.
  ]

  #v(0.6em)
  #uncover("2-")[
    Ordinary static type systems stop at "is a list".
    Once a type can say "is a sorted list of length $n$", it can also say
    _"is a proof that $n$ is even"_ --- and that is the rest of this talk.
  ]

])

== L$exists$$forall$N is dependently typed

#slide(repeat: 3, self => [
  #let (uncover, only) = utils.methods(self)

  #v(0.5em)
  #uncover("1-")[
    - every object has a type
    - type-correctness is checked at compile-time
    - _types are themselves values_ (types are first-class citizens)
    - types can _depend_ on values
    - types themselves can do computation
    
  ]
  
  #uncover("2-")[
    *blah:* \
  ]

  #uncover("3-")[
    *blah:* \
  ]

])

== Lean is a theorem prover

#slide(repeat: 3, self => [
  #let (uncover, only) = utils.methods(self)

  #v(0.5em)
  #uncover("1-")[
    - 
    
  ]
  
  #uncover("2-")[
    *blah:* \
  ]

  #uncover("3-")[
    *blah:* \
  ]

])


#bibliography("refs.bib")

== This is the end
#v(10em)
#set text(30pt)
#align(center)[
Thank you for your attention!
]
#set text(15pt)
#align(center)[
Shoutout to Fabian vdW for the Slide design
]


== Unsplit Slide

#slide(repeat: 3, self => [
  #let (uncover, only) = utils.methods(self)

  #v(0.5em)
  #uncover("1-")[
    *blah:* 

  ]
  
  #uncover("2-")[
    *blah:* \
  ]

  #uncover("3-")[
    *blah:* \
  ]

])



== Split Slide

#slide(repeat: 3, self => [
  #let (uncover, only) = utils.methods(self)

  #columns(2, gutter: 8pt)[
  #v(0.5em)
  #uncover("1-")[
    *blah:* 
  ]
  
  #uncover("2-")[
    *blah:* \
  ]


  #colbreak()
  #uncover("3-")[
    *blah:* \
  ]
]

])


