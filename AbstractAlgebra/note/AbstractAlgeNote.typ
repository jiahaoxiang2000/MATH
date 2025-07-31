#import "@preview/theorion:0.3.2": *
#import "chapters/set.typ": set-content
#import "chapters/ring.typ": ring-content

// Document configuration
#let title = "Algebra Note"
#let author = "isomo"
#let date = datetime.today()

// Custom color scheme inspired by elegant academic style
#let primary-color = rgb("#034c48")  // Light sea green
#let secondary-color = rgb("#113f64") // Steel blue
#let accent-color = rgb("#d01238")    // Crimson
#let text-color = rgb("#172a2a")      // Dark slate gray

// Page setup with academic styling
#set page(
  paper: "a4",
  margin: (left: 2.5cm, right: 2.5cm, top: 3cm, bottom: 3cm),
  numbering: "1",
  number-align: center,
  header: context {
    if counter(page).get().first() > 1 {
      align(center, line(length: 100%, stroke: 0.5pt + gray))
      v(-0.75em)
      align(center, text(size: 10pt, fill: gray, title))
    }
  },
)

// Typography setup
#set text(
  font: "New Computer Modern",
  size: 11pt,
  fill: text-color,
  lang: "en",
)

#set par(
  justify: true,
  leading: 0.65em,
  spacing: 1.2em,
)

// Set heading numbering
#set heading(numbering: "1.1.1")

// Heading styles
#show heading.where(level: 1): it => {
  pagebreak(weak: true)
  v(2em)
  block[
    #set align(center)
    #set text(size: 20pt, weight: "bold", fill: primary-color)
    #if it.numbering != none [
      #counter(heading).display(it.numbering)
      #h(1em)
    ]
    #upper(it.body)
    #v(1em)
    #line(length: 60%, stroke: 2pt + primary-color)
  ]
  v(1.5em)
}

#show heading.where(level: 2): it => {
  v(1.5em)
  block[
    #set text(size: 16pt, weight: "bold", fill: secondary-color)
    #if it.numbering != none [
      #counter(heading).display(it.numbering)
      #h(1em)
    ]
    #it.body
    #v(0.5em)
    #line(length: 100%, stroke: 1pt + secondary-color)
  ]
  v(1em)
}

#show heading.where(level: 3): it => {
  v(1em)
  block[
    #set text(size: 14pt, weight: "bold", fill: text-color)
    #if it.numbering != none [
      #counter(heading).display(it.numbering)
      #h(1em)
    ]
    #it.body
  ]
  v(0.75em)
}

// Configure theorem environments with theorion
#show: show-theorion

// Math equation numbering - disabled
#set math.equation(numbering: none)

// Bibliography setup (if references.bib exists)
#let bibliography-file = "../references.bib"

// Custom functions for colored text shortcuts
#let redt(content) = text(fill: rgb("#DC143C"), content)
#let bluet(content) = text(fill: rgb("#1E90FF"), content)
#let greent(content) = text(fill: rgb("#32CD32"), content)

// Title page
#align(center)[
  #v(2cm)
  #text(size: 24pt, weight: "bold", fill: primary-color)[
    #upper(title)
  ]
  #v(1cm)
  #text(size: 14pt, fill: secondary-color)[
    Abstract Algebra Notes
  ]
  #v(2cm)
  #text(size: 12pt)[
    *Author:* #author \
    *Date:* #date.display("[month repr:long] [day], [year]")
  ]
  #v(1cm)
  #line(length: 50%, stroke: 1pt + primary-color)
]

#pagebreak()

// Table of contents
#outline(
  title: [Table of Contents],
  indent: auto,
)

#pagebreak()

// Preface
= Preface

These abstract algebra notes primarily focus on self-study, with a writing style that deliberately maintains low information density and includes some redundancy for clarity.

My first encounter with abstract algebra was through an English textbook, which was heavily focused on theorem proofs. Progress was slow, and I struggled to see practical applications. After spending considerable time with this approach, I sought Chinese resources for potentially better learning methods. On Bilibili, I discovered Maki's abstract algebra lectures and accompanying notes, which provided an excellent introduction to the subject. However, the content still had some gaps. Later, after finding a recommended algebra book, "Methods of Algebra" by Professor Li Wenwei, I began compiling these notes based on that foundation to aid my future studies. The "Methods of Algebra" book is difficult, we math level maybe on the freshman level, so we find the "Algebra Note" by the Professor Li Wenwei, which is more suitable for us.

Something we not understand is marked (MORE), which meaning need more thinking or more information.

= Introduction

== What is Algebra?

In light of this, classical algebra can be understood as the art of solving equations by:
- Replacing specific numbers with variables
- Using operations such as transposition of terms

This traditional approach forms the foundation of algebraic manipulation and equation solving.

#theorem(title: "Fundamental Theorem of Algebra")[
  Let $f = X^n + a_(n-1)X^(n-1) + ... + a_0$ be a polynomial in $X$ with complex coefficients, where $n ∈ bb(Z)_(≥ 1)$. Then there exist $x_1, ..., x_n ∈ bb(C)$ such that:
  $
    f = product_(k=1)^n (X-x_k)
  $
  These $x_1, ..., x_n$ are precisely the complex roots of $f$ (counting multiplicity); they are unique up to reordering.
]

Now let us further explain the previously raised question: What is algebra?

- *What is an equation?* \
  An expression obtained through a finite number of basic operations: addition, subtraction, multiplication, and division (with non-zero denominators).

- *What are numbers?* \
  At minimum, this includes common number systems like $bb(Q)$, $bb(R)$, and $bb(C)$. All these systems support four basic operations, though division requires non-zero denominators. Note that $bb(Z)$ is not included in this list, as division is not freely applicable in $bb(Z)$.

- *What is the art of solving?* \
  This involves:
  - Determining whether equations have solutions
  - Finding exact solutions when possible
  - Developing efficient algorithms, Providing methods for approximating solutions

#set-content

#ring-content
