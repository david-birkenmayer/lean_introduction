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
    - _dependently typed_
  ]

  #uncover("3-")[
    - a _theorem prover_
  ]


])


== L$exists$$forall$N is a functional programming language

#slide(repeat: 3, self => [
  #let (uncover, only) = utils.methods(self)

  #v(0.5em)
  #uncover("1-")[
    - everything is an expression
    - functions are values 
    - functions are _pure_
    - inductive types, pattern matching, lambda abstraction
    - functions regulate everything


    - *Upside:* Allows for clean mathematical reasoning and Proofs
    - *Downside:* Slow for many tasks, I/O is awkward
    
  ]
  
  #uncover("2-")[
    *blah:* \
  ]

  #uncover("3-")[
    *blah:* \
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


