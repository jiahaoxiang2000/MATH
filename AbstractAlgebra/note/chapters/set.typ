#import "@preview/theorion:0.3.2": *

#let set-content = [
  = Sets Mappings and Relationships

  == Set Theory

  #remark[
    Element of Set also one of Set.
  ]

  #axiom(title: "Extensionality")[
    If two sets have the same elements, then they are equal.
    $
      A = B ⟺ (A subset B) ∧ (B subset A)
    $
  ] <axiom:extensionality>

  #axiom(title: "Pairing")[
    For any elements $x$ and $y$, there exists a set $\{x,y\}$ whose elements are exactly $x$ and $y$.
  ] <axiom:pairing>

  #axiom(title: "Schema of Separation")[
    Let $cal(P)$ be a property of sets, and let $cal(P)(u)$ denote that set $u$ satisfies property $cal(P)$. Then for any set $X$, there exists a set $Y$ such that:
    $
      Y = \{u ∈ X : cal(P)(u)\}
    $
  ] <axiom:separation>

  #axiom(title: "Union")[
    For any set $X$, there exists its union set $union.big X$ defined as:
    $
      union.big X := \{u : exists v in X, u in v\}
    $
  ] <axiom:union>

  #axiom(title: "Power Set")[
    For any set $X$, there exists its power set $cal(P)(X)$ defined as:
    $
      cal(P)(X) := \{u : u subset X\}
    $
  ] <axiom:powerset>

  #axiom(title: "Infinity")[
    There exists an infinite set. More precisely, there exists a set $X$ such that:
    1. $∅ ∈ X$
    2. If $y ∈ X$, then $y union \{y\} ∈ X$
  ] <axiom:infinity>

  #axiom(title: "Schema of Replacement")[
    Let $cal(F)$ be a function with domain set $X$. Then there exists a set $cal(F)(X)$ defined as:
    $
      cal(F)(X) = \{cal(F)(x) : x ∈ X\}
    $
  ] <axiom:replacement>

  #remark[
    The Replacement Axiom and the Separation Axiom Schema are to construct new sets from existing sets. Different is the Replacement can equal size of the set, but the Separation is a subset numbers of the set.
  ]

  #definition(title: "Cartesian Product")[
    For any two sets $A$ and $B$, their Cartesian product $A times B$ (also called simply the product) consists of all ordered pairs $(a,b)$ where $a ∈ A$ and $b ∈ B$. In other words:
    $
      A times B := {(a,b) : a ∈ A, b ∈ B}
    $
  ]

  #axiom(title: "Regularity")[
    Every non-empty set contains an element which is minimal with respect to the membership relation $∈$.
  ] <axiom:regularity>

  #axiom(title: "Choice")[
    Let $X$ be a set of non-empty sets. Then there exists a function $g : X → union.big X$ (called a choice function) such that:
    $
      ∀ x ∈ X, g(x) ∈ x
    $
  ] <axiom:choice>

  #example(title: "Symmetric Difference")[
    The symmetric difference of sets $X$ and $Y$ is defined as $X triangle Y := (X \\ Y) union (Y \\ X)$.
    Let's verify that $X triangle Y = (X union Y) \\ (X inter Y)$.

    #proof[
      Let $z$ be an arbitrary element. Then:
      $
        z ∈ X triangle Y & ⟺ z ∈ (X \\ Y) union (Y \\ X)                  \
                         & ⟺ z ∈ X \\ Y "or" z ∈ Y \\ X                   \
                         & ⟺ (z ∈ X "and" z ∉ Y) "or" (z ∈ Y "and" z ∉ X) \
                         & ⟺ z ∈ X union Y "and" z ∉ X inter Y            \
                         & ⟺ z ∈ (X union Y) \\ (X inter Y)
      $
      Therefore, $X triangle Y = (X union Y) \\ (X inter Y)$.
    ]
  ]

  == Mappings

  #definition(title: "Mapping")[
    Let $A$ and $B$ be sets. A mapping from $A$ to $B$ is written as $f : A arrow B$ or $A arrow^f B$.

    In set-theoretic language, we understand a mapping $f : A → B$ as a subset of $A times B$, denoted $Gamma_f$, satisfying the following condition: for each $a ∈ A$, the set
    $
      \{b ∈ B : (a,b) ∈ Gamma_f\}
    $
    is a singleton, whose unique element is denoted $f(a)$ and called the image of $a$ under $f$.
  ]

  #definition(title: "Left and Right Inverses")[
    Consider a pair of mappings $A arrow.r^f B arrow.r^g A$.
    If $g compose f = "id"_A$, then:
    - We call $g$ the left inverse of $f$
    - We call $f$ the right inverse of $g$

    A mapping with a left inverse (or right inverse) is called left invertible (or right invertible).
  ]


]

