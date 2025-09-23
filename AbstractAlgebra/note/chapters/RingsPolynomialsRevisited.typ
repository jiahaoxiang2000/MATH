// (Revisiting Rings and Polynomials)

#import "@preview/theorion:0.3.2": *
#import "@preview/cetz:0.3.0": canvas, draw
#let rings-polynomials-revisited-content = [

  = Ring and Polynomial Revisited

  == Ideals and Quotient Rings

  #definition[
    Let $I$ be a non-empty subset of ring $R$. $I$ is called an *ideal* of $R$ when the following conditions hold#footnote[This terminology comes from the study of "ideal numbers" in number theory by 19th century mathematicians like Kummer, Dedekind, etc.]:

    - *Closure under addition* If $x, y ∈ I$ then $x + y ∈ I$.
    - *Two-sided closure under multiplication* For any $r ∈ R$ we have $r I ⊂ I$ and $I r ⊂ I$.
  ]

  #proposition[
    For any ideal $I$ of ring $R$, we have
    $ I = R arrow.l.r.double.long 1 in I. $
  ]

  #definition[
    *Kernel of Ring Homomorphism* Let $f : R arrow R'$ be a ring homomorphism. Its *kernel* (also called *null kernel*) is defined as
    $ "ker"(f) := f^(-1)(0) = {x in R : f(x) = 0}. $
    This is an ideal of $R$.
  ]

  #definition[
    *Quotient Ring* Let $I$ be an ideal of ring $R$. Define
    $ R\/I := {"cosets " x + I : x in R} = R\/equiv_I. $

    On $R\/I$ we can reasonably define operations on cosets:

    ▷ *Addition*
    $ (x + I) + (y + I) := x + y + I; $

    ▷ *Multiplication*
    $ (x + I) dot (y + I) := x y + I; $

    ▷ *Zero element*
    $ 0_(R\/I) := I = 0_R + I quad ("as a coset of " I); $

    ▷ *Unit element*
    $ 1_(R\/I) := 1_R + I. $

    The resulting ring $(R\/I, +, dot, 0_(R\/I), 1_(R\/I))$ is called the *quotient ring* of $R$ by the ideal $I$.
  ]

  #proposition[
    If $R$ is a commutative ring and $I subset R$ is an ideal, then $R\/I$ is also a commutative ring.
  ]

  #proposition[
    Let $I$ be an ideal of ring $R$, and $f : R arrow R'$ be a ring homomorphism.

    (i) If $I subset "ker"(f)$, then there exists a unique ring homomorphism $overline(f) : R\/I arrow R'$ such that the following diagram commutes:
    #align(center)[
      #canvas(length: 1.5cm, {
        import draw: *

        content((0, 2), $R$)
        content((3, 2), $R'$)
        content((0, 0), $R\/I$)

        line((0.3, 2), (2.7, 2), mark: (end: ">"))
        content((1.5, 2.4), $f$)

        line((0, 1.7), (0, 0.3), mark: (end: ">"))
        content((-0.5, 1), $q$)

        line((0.3, 0.2), (2.6, 1.7), mark: (end: ">"))
        content((1.8, 0.6), $overline(f)$)
      })
    ]
    In other words, $overline(f) compose q = f$.
    Specifically, $overline(f)(x + I) = f(x)$.

    (ii) If $I = "ker"(f)$ and $R' = "im"(f)$, then $overline(f)$ is a ring isomorphism.
  ]

  #corollary[
    Let $f : R_1 arrow R_2$ be a ring homomorphism, $I_1 subset R_1$ and $I_2 subset R_2$ be ideals, and $f(I_1) subset I_2$. Then there exists a unique ring homomorphism $overline(f) : R_1\/I_1 arrow R_2\/I_2$ such that the following diagram commutes:

    #align(center)[
      #canvas(length: 1.5cm, {
        import draw: *

        content((0, 2), $R_1$)
        content((3, 2), $R_2$)
        content((0, 0), $R_1\/I_1$)
        content((3, 0), $R_2\/I_2$)

        line((0.3, 2), (2.7, 2), mark: (end: ">"))
        content((1.5, 2.4), $f$)

        line((0, 1.7), (0, 0.3), mark: (end: ">"))
        content((-0.5, 1), $q_1$)

        line((3, 1.7), (3, 0.3), mark: (end: ">"))
        content((3.5, 1), $q_2$)

        line((0.3, 0), (2.7, 0), mark: (end: ">"))
        content((1.5, -0.3), $overline(f)$)
      })
    ]

    In other words, $q_2 compose f = overline(f) compose q_1$.
    In the diagram, $q_1$ and $q_2$ are respectively the quotient homomorphisms from $R_1$ and $R_2$ to their respective quotient rings. Specifically, $overline(f)(x + I_1) = f(x) + I_2$.
  ]

  #proposition[
    Let $I$ be an ideal of $R$, $overline(R) := R\/I$, and let the quotient map still be denoted $q : R arrow overline(R)$. We have a bijection

    $ {J subset R : "ideal", J supset I} arrow.l.r.double^(1:1) {overline(J) subset overline(R) : "ideal"} $

    given by the maps:
    $ J arrow.bar overline(J) := q(J) $
    $ overline(J) arrow.bar J := q^(-1)(overline(J)) $

    This bijection has the following properties:

    - It is *strictly order-preserving*: $J_1 supset J_2$ if and only if $overline(J_1) supset overline(J_2)$.
    - If $J$ corresponds to $overline(J)$, then there is a natural ring isomorphism
      $ R\/J tilde.equiv overline(R)\/overline(J) $
      $ x + J arrow.bar q(x) + overline(J). $
  ]

  == Unique Factorization Properties of Polynomials

  #definition[
    Let $R$ be an integral domain, $x, y in R$. If there exists $r in R^times$ such that $x = r y$, then we write $x tilde y$.
  ]

  #lemma[
    Let $R$ be an integral domain, $x, y in R$. Then:
    - $x | y$ if and only if $(x) supset (y)$;
    - $x tilde y$ if and only if $x$ and $y$ divide each other, if and only if $(x) = (y)$.
  ]

  #definition[
    Let $p$ be a non-zero element of integral domain $R$, with $p in.not R^times$.

    - If $p$ satisfies $p | a b arrow.l.r.double.long (p | a) or (p | b)$, then $p$ is called a *prime element*.

    - If $p$ satisfies $a | p arrow.l.r.double.long (a tilde p) or (a tilde 1)$, then $p$ is called an *irreducible element*.
  ]

  #lemma[
    Let $p$ be a prime element of integral domain $R$. Then $p$ is an irreducible element.
  ]

  #definition[
    If for every non-zero element $r$ in integral domain $R$, there exist $n in bb(Z)_(gt.eq 0)$ and irreducible elements $p_1, dots, p_n in R$ such that
    $ r tilde p_1 dots p_n, $
    and the $tilde$ equivalence classes of $p_1, dots, p_n$ (counting multiplicities) are uniquely determined by $r$ up to reordering, then $R$ is called a *unique factorization domain*. By convention, when $n = 0$, the above expression should be interpreted as $r tilde 1$.
  ]

  #definition[
    Let $R$ be a unique factorization domain, $h in "Frac"(R) \\ {0}$. Then there exist $f, g in R$ such that $g eq.not 0$ and $f$ and $g$ are coprime, and $h = f/g$. Such a fraction $f/g$ is called a *reduced fraction*.

    If $f_1, g_1 in R$ also satisfy $g_1 eq.not 0$ and $h = f_1/g_1$, then we must have $f | f_1$ and $g | g_1$.
  ]

  #lemma[
    All ideals $I$ of the integral domain $F[X]$ are principal ideals.
  ]

  #lemma[
    All irreducible elements of the integral domain $F[X]$ are prime elements.
  ]

  #theorem[
    *(Fundamental Theorem of Arithmetic for Polynomial Rings)* The integral domain $F[X]$ is a unique factorization domain.
  ]

  #theorem[
    *(Partial Fraction Decomposition)* Let $f, g in F[X]$ with $g eq.not 0$ and $g = g_1 dots g_n$, where $g_1, dots, g_n in F[X]$ are pairwise coprime. Then there exist unique $q, h_1, dots, h_n in F[X]$ such that:

    - $h_i in F[X]$ satisfies $deg h_i < deg g_i$ for $1 lt.eq i lt.eq n$;

    - We have the equality in $F(X)$:
      $ f/g = q + sum_(i=1)^n h_i/g_i. $
  ]

  == Simple Generalization: Unique Factorization in Principal Ideal Domains

  #definition[
    Let $R$ be an integral domain. If all ideals of $R$ are principal ideals, then $R$ is called a *principal ideal domain*.
  ]

  #proposition[
    An integral domain $R$ is a unique factorization domain if and only if the following conditions hold:

    ◦ Every $r ∈ R ∖ {0}$ can be written as a product of irreducible elements.

    ◦ Every irreducible element is a prime element.
  ]

  #lemma[
    Let $R$ be a principal ideal domain, and let $(I_n)_(n=1)^infinity$ be a sequence of ideals of $R$ satisfying $I_1 ⊂ I_2 ⊂ I_3 ⊂ ⋯$. Then for sufficiently large $n ∈ bb(Z)_(≥1)$, we have $I_n = I_(n+1) = ⋯$.
  ]

  #theorem[
    If $R$ is a principal ideal domain, then $R$ is a unique factorization domain.
  ]

  #proposition[
    Let $R$ be a principal ideal domain. Elements $r_1, ..., r_n$ are coprime if and only if $angle.l r_1, ..., r_n angle.r = R$, or equivalently, there exist $s_1, ..., s_n ∈ R$ such that $sum_(i=1)^n r_i s_i = 1$.
  ]

  #proposition[
    Let $R$ be a principal ideal domain, $t ∈ R ∖ {0}$ and $t in.not R^times$. The following properties are equivalent:

    (i) $R\/(t)$ is a field;

    (ii) $R\/(t)$ is an integral domain;

    (iii) $t$ is a prime element;

    (iv) $t$ is irreducible.
  ]

  #theorem[
    *(Chinese Remainder Theorem for Principal Ideal Domains)* Let $R$ be a principal ideal domain, $a_1, ..., a_n ∈ R ∖ {0}$ be pairwise coprime, and $a := a_1 ⋯ a_n$. Then there is a ring isomorphism
    $
      phi : R\/(a) & arrow product_(i=1)^n R\/(a_i) \
           r + (a) & arrow.bar (r + (a_i))_(i=1)^n.
    $
  ]

  == Formal Derivatives

  #definition[
    *(Formal Derivative)* Let $f = sum_(n≥0) a_n X^n ∈ F[X]$. Define the *formal derivative* of $f$ as
    $ f' := sum_(n≥1) n a_n X^(n-1) ∈ F[X], $
    where $n a_n ∈ F$ is understood in the sense of (3.1.1). Recursively define the derivatives of any order by
    $ f^((0)) = f, quad f^((m)) := (f^((m-1)))' quad (m ∈ bb(Z)_(≥1)) $
    We also write $f'' = (f')'$, and so on.
  ]

  #corollary[
    The derivative mapping $f arrow.bar f'$ is a linear map from the $F$-vector space $F[X]$ to itself.
  ]

  #proposition[
    The property $f' = 0 arrow.double.l.r.long f ∈ F$ holds in $F[X]$ if and only if $"char"(F) = 0$.
  ]


]
