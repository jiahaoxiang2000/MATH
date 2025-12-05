// (Revisiting Rings and Polynomials)

#import "command.typ": *

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
    #cetz.canvas(
      length: 1.5cm,
      {
        import cetz.draw: *

        content((0, 2), $R$)
        content((3, 2), $R'$)
        content((0, 0), $R\/I$)

        line((0.3, 2), (2.7, 2), mark: (end: ">"))
        content((1.5, 2.4), $f$)

        line((0, 1.7), (0, 0.3), mark: (end: ">"))
        content((-0.5, 1), $q$)

        line((0.3, 0.2), (2.6, 1.7), mark: (end: ">"))
        content((1.8, 0.6), $overline(f)$)
      },
    )
  ]
  In other words, $overline(f) compose q = f$.
  Specifically, $overline(f)(x + I) = f(x)$.

  (ii) If $I = "ker"(f)$ and $R' = "im"(f)$, then $overline(f)$ is a ring isomorphism.
]

#corollary[
  Let $f : R_1 arrow R_2$ be a ring homomorphism, $I_1 subset R_1$ and $I_2 subset R_2$ be ideals, and $f(I_1) subset I_2$. Then there exists a unique ring homomorphism $overline(f) : R_1\/I_1 arrow R_2\/I_2$ such that the following diagram commutes:

  #align(center)[
    #cetz.canvas(
      length: 1.5cm,
      {
        import cetz.draw: *

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
      },
    )
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
  Let $R$ be a unique factorization domain, $h in "Frac"(R) \\ {0}$. Then there exist $f, g in R$ such that $g eq.not 0$ and $f$ and $g$ are coprime, and $h = f / g$. Such a fraction $f / g$ is called a *reduced fraction*.

  If $f_1, g_1 in R$ also satisfy $g_1 eq.not 0$ and $h = f_1 / g_1$, then we must have $f | f_1$ and $g | g_1$.
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
    $ f / g = q + sum_(i=1)^n h_i / g_i. $
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
  where $n a_n ∈ F$ . Recursively define the derivatives of any order by
  $ f^((0)) = f, quad f^((m)) := (f^((m-1)))' quad (m ∈ bb(Z)_(≥1)) $
  We also write $f'' = (f')'$, and so on.
]

#corollary[
  The derivative mapping $f arrow.bar f'$ is a linear map from the $F$-vector space $F[X]$ to itself.
]

#proposition[
  The property $f' = 0 arrow.double.l.r.long f ∈ F$ holds in $F[X]$ if and only if $"char"(F) = 0$.
]

#proposition[
  There exists a unique mapping
  $ F(X) arrow F(X) $
  $ f arrow.bar f' $
  such that its restriction to $F[X]$ gives the formal derivative of polynomials, and for all $f, g ∈ F(X)$ we have
  $ (f + g)' = f' + g', $
  $ (f g)' = f' g + f g'. $
  In fact, it can be precisely given by the formula:
  $ (f / g)' = (f' g - f g') / g^2, $
  where $f, g ∈ F[X]$ and $g ≠ 0$.
]

#definition[
  *(Formal Partial Derivatives)* For an $n$-variable polynomial expressed as a finite sum
  $ f = sum_(i_1, ..., i_n ≥ 0) c_(i_1, ..., i_n) X_1^(i_1) ⋯ X_n^(i_n) ∈ F[X_1, ..., X_n] $
  and $1 ≤ k ≤ n$, we borrow notation from analysis to define
  $
    (partial f) / (partial X_k) := sum_(i_1, ..., i_n ≥ 0) i_k c_(i_1, ..., i_n) X_1^(i_1) ⋯ X_k^(i_k - 1) ⋯ X_n^(i_n).
  $
]

== Applications: Mason–Stothers Theorem

#definition[
  *(Radical of a Polynomial)* Let $f ∈ F[X]$ be nonzero. Define the *radical* of $f$ by
  $ rad(f) := product_(p ∣ f) p, $
  where $p$ runs over the monic irreducible polynomials of $F[X]$ that divide $f$. If $f ∈ F^times$, interpret the right-hand side as $1$.
]

#lemma[
  Let $f, g ∈ F[X]$ be coprime with $f' ≠ 0$ and $g' ≠ 0$. Then $f f' ≠ g g'.$
]

#theorem[
  *(Mason–Stothers Theorem, 1981)* Let $a, b, c ∈ F[X]$ be pairwise coprime polynomials with $a' ≠ 0$, $b' ≠ 0$, $c' ≠ 0$, and suppose $a + b + c = 0$. Then
  $ max {"deg"(a), "deg"(b), "deg"(c)} ≤ "deg"(rad(a b c)) - 1. $
]

#corollary[
  *(Polynomial Fermat's Last Theorem)* Let $n ∈ bb(Z)_(≥1)$ with $"char"(F) ∤ n$. Suppose there exist pairwise coprime polynomials $u, v, w ∈ F[X]$ whose derivatives satisfy $u' ≠ 0$, $v' ≠ 0$, $w' ≠ 0$, and that $u^n + v^n = w^n$. Then $n < 3$.
]

== Roots and Repeated Factors

We already know $F[X]$ is a unique factorization domain. By a simple degree argument the linear polynomial $X - a$ is irreducible for every $a ∈ F$. Consequently, $X - a$ and $h ∈ F[X]$ are coprime if and only if $X - a$ does not divide $h$, which is equivalent to $h(a) ≠ 0$ by the remainder theorem.

Fix $a ∈ F$. Every nonzero $f ∈ F[X]$ can be written uniquely in the form
$
  f = (X - a)^(m_a) h,
$
where $m_a ∈ bb(Z)_(≥0)$, $h ∈ F[X]$, and $h(a) ≠ 0$ (equivalently, $h$ is coprime to $X - a$). The exponent $m_a$ is determined uniquely by $f$ and $a$, and satisfies $m_a > 0$ precisely when $a$ is a root of $f$.

#definition[
  *(Multiplicity of a Root)* In the factorization $f = (X - a)^(m_a) h$ above, the integer $m_a$ is called the *multiplicity* of $a$ in the nonzero polynomial $f$.
]

#definition[
  *(Splitting Polynomial)* A polynomial $f ∈ F[X]$ is said to *split* over $F$ if it factors as a product of linear polynomials in $F[X]$.
]

#proposition[
  Let $f ∈ F[X]$ be nonzero and let $a_1, …, a_m ∈ F$ be its roots counted with multiplicities. Then $0 ≤ m ≤ "deg"(f)$. Moreover, $m = "deg"(f)$ if and only if $f$ is constant or $f$ splits over $F$.
]

#definition[
  *(Algebraically Closed Field)* A field $F$ is *algebraically closed* if every nonconstant polynomial over $F$ splits over $F$.
]

#proposition[
  Let $f ∈ F[X]$ be nonzero.

  (i) If $f$ and $f'$ are coprime, then $f$ has no repeated factors.

  (ii) If $f$ has no repeated factors and each irreducible factor $p$ of $f$ satisfies $p' ≠ 0$ (which holds automatically when $"char"(F) = 0$), then $f$ and $f'$ are coprime.
]

#corollary[
  Suppose $f ∈ F[X]$ splits over $F$. Then $f$ has no repeated roots if and only if $f$ and $f'$ are coprime.
]

== Symmetric Polynomials

#definition[
  *(Symmetric Polynomial)* Let $f ∈ F[X_1, ..., X_n]$. If $sigma f = f$ holds for all $sigma in S_n$, then $f$ is called a *symmetric polynomial*.
]

#definition[
  *(Elementary Symmetric Polynomials)* For $1 ≤ k ≤ n$, define the $n$-variable polynomial
  $ e_k := sum_(1 ≤ i_1 < ⋯ < i_k ≤ n) X_(i_1) ⋯ X_(i_k). $
  It is easy to see that this is a homogeneous symmetric polynomial of degree $k$, called the *$k$-th elementary symmetric polynomial*. For the case $k = 0$, we conveniently define $e_0 := 1$.
]

#lemma[
  Let $f$ be an $n$-variable symmetric polynomial. Then $f(X_1, ..., X_(n-1), 0) = 0$ if and only if $e_n | f$.
]

#theorem[
  *(Fundamental Theorem of Symmetric Polynomials)* Let $f$ be an $n$-variable symmetric polynomial. Then there exists $g ∈ F[X_1, ..., X_n]$ such that
  $ f = g(e_1, ..., e_n). $
]

#theorem[
  Let $g ∈ F[X_1, ..., X_n]$. If $g(e_1, ..., e_n) = 0$, then $g = 0$.
]

== Resultants

#definition[
  *(Resultant)* Let $n, m ∈ bb(Z)_(≥1)$. Consider elements of $F[X]$
  $ f = v_0 X^n + ⋯ + v_n, $
  $ g = w_0 X^m + ⋯ + w_m, $
  where $v_i, w_j ∈ F$. Define the *resultant* of $f$ and $g$ as
  $
    "Res"(f, g) := det mat(
      v_0, v_1, ..., v_n, , , , ;
      , v_0, v_1, ..., v_n, , , ;
      , , dots.down, dots.down, dots.down, dots.down, , ;
      , , , v_0, v_1, ..., v_n;
      w_0, w_1, ..., w_m, , , , ;
      , w_0, w_1, ..., w_m, , , ;
      , , dots.down, dots.down, dots.down, dots.down, , ;
      , , , w_0, w_1, ..., w_m
    )
  $
  This is a determinant of order $n + m$, where the first $m$ rows contain shifted copies of the coefficients of $f$, the next $n$ rows contain shifted copies of the coefficients of $g$, and blank entries are zero.
] <def-resultant>

#lemma[
  Fix $n, m ∈ bb(Z)_(≥1)$. Let $f, g ∈ F[X]$ be as in @def-resultant. Then $"Res"(f, g) = 0$ if and only if there exist $f_1, g_1 ∈ F[X]$, not both zero, such that
  $ f g_1 + g f_1 = 0, quad deg f_1 < n, quad deg g_1 < m. $
]

#theorem[
  Fix $n, m ∈ bb(Z)_(≥1)$. Let $f, g ∈ F[X]$ be as in @def-resultant. Then $"Res"(f, g) = 0$ if and only if one of the following conditions holds: either $v_0 = 0 = w_0$, or $f$ and $g$ have a common factor of degree $> 0$.
]

#theorem[
  Fix $n, m ∈ bb(Z)_(≥1)$. Let $f, g ∈ F[X]$ have the following factorizations
  $ f = a product_(i=1)^n (X - alpha_i), quad g = b product_(j=1)^m (X - beta_j), $
  where $a, b$ and $alpha_i, beta_j$ are all elements of $F$. Then
  $
    "Res"(f, g) = a^m product_(i=1)^n g(alpha_i) = (-1)^(n m) b^n product_(j=1)^m f(beta_j) = a^m b^n product_(i, j) (alpha_i - beta_j).
  $
]

== Introduction to Irreducible Polynomials

#definition[
  *(Content and Primitive Polynomials)* Let $f = sum_(k=0)^n a_k X^k ∈ bb(Z)[X]$ be nonzero. Define
  $ c(f) := gcd(a_0, ..., a_n) $
  to be the greatest common divisor of all coefficients. If $c(f) = 1$, then $f$ is called a *primitive polynomial*.
]

#lemma[
  *(Gauss's Lemma)* Let $g, h ∈ bb(Z)[X]$ be primitive polynomials. Then $g h$ is also primitive.
]

#lemma[
  For all nonzero $g, h ∈ bb(Z)[X]$, we have $c(g h) = c(g) c(h)$.
]

#proposition[
  Let $f ∈ bb(Z)[X]$ be a primitive polynomial. The following are equivalent:

  (a) $f$ is irreducible in $bb(Q)[X]$;

  (b) There do not exist polynomials $g, h ∈ bb(Z)[X]$, both of degree $> 0$, such that $f = g h$.

  Moreover, if a primitive polynomial $f$ factors as $g h$ in $bb(Q)[X]$, then by multiplying $g$ and $h$ by some $alpha ∈ bb(Q)^times$ and $alpha^(-1)$ respectively, we can ensure that both $g$ and $h$ are primitive polynomials.
] <prop-primitive-irreducible>

#theorem[
  The irreducible elements of the integral domain $bb(Z)[X]$ fall into two classes:

  ▷ *First class:* Irreducible elements of $bb(Z)$.

  ▷ *Second class:* Primitive polynomials $f$ of degree $> 0$ that satisfy the equivalent conditions (a) or (b) of @prop-primitive-irreducible.

  Furthermore, $bb(Z)[X]$ is a unique factorization domain.
]

#theorem[
  *(Eisenstein's Criterion)* Let $n ∈ bb(Z)_(≥1)$ and $f = a_0 + a_1 X + ⋯ + a_n X^n ∈ bb(Z)[X]$. If there exists a prime $p$ satisfying
  $ p divides.not a_n, $
  $ 0 ≤ i < n ==> p | a_i, $
  $ p^2 divides.not a_0, $
  then $f$ is irreducible as an element of $bb(Q)[X]$.
]

#proposition[
  *(Rational Root Test)* Let $alpha = u \/ v$ be a rational number that is a root of a polynomial with integer coefficients $a_n X^n + a_(n-1) X^(n-1) + ⋯ + a_0 ∈ bb(Z)[X]$, where $u$ and $v$ are coprime. Then $v | a_n$ and $u | a_0$.
]

#corollary[
  Any rational root of a monic polynomial with integer coefficients must be an integer.
]

== Constructing Field Extensions from Irreducible Polynomials

#lemma[
  Let $f ∈ F[X] ∖ F$. Then
  $
    ι : F & → F[X]\/(f) \
        a & ↦ a + (f)
  $
  is an injective ring homomorphism.
]

#lemma[
  Let $f ∈ F[X] ∖ F$. Then the cosets of $1, X, ..., X^(deg f - 1)$ modulo $(f)$ form a basis for $F[X]\/(f)$ as an $F$-vector space.
]

#proposition[
  Let $f = sum_(n≥0) a_n X^n ∈ F[X]$ be irreducible.

  (i) With respect to the field embedding $ι : F ↪ F[X]\/(f) =: E$, let $α := X + (f) ∈ E$. Then the polynomial $f^ι ∈ E[X]$ satisfies $f^ι (α) = 0$.

  (ii) If $L$ is a commutative ring, $ξ : F → L$ is a ring homomorphism, and $β ∈ L$ satisfies $f^ξ (β) = 0$, then there exists a unique ring homomorphism $ψ : E → L$ such that $ψ(α) = β$ and the following diagram commutes:
  #align(center)[
    #cetz.canvas(
      length: 1.5cm,
      {
        import cetz.draw: *

        content((0, 2), $F$)
        content((3, 2), $E$)
        content((1.5, 0), $L$)

        line((0.3, 2), (2.7, 2), mark: (end: ">"))
        content((1.5, 2.4), $ι$)

        line((0.3, 1.7), (1.2, 0.3), mark: (end: ">"))
        content((0.3, 1), $ξ$)

        line((2.7, 1.7), (1.8, 0.3), mark: (end: ">"))
        content((2.7, 1), $ψ$)
      },
    )
  ]
  This is equivalent to saying that $ψ$ is a linear map with respect to the $F$-vector space structure on $E$ (or $L$) given by $ι$ (or $ξ$).
]

#corollary[
  For any field $F$ and any nonconstant polynomial $f ∈ F[X]$, there exists a field embedding $F ↪ E_f$ such that $f$ splits over $E_f$.
]

#definition[
  *(Degree of Extension)* Consider a field $F$, a ring $L$, together with a given homomorphism $F → L$. This data makes $L$ an $F$-vector space. Define the *degree* of $L$ relative to $F$ as
  $ [L : F] := dim_F L. $
  In particular, for any field extension $E$ of $F$, we can discuss its degree $[E : F]$.
]

#proposition[
  *(Tower Law)* Let $E$ be a field extension of $F$, and let $L$ be any ring with a given homomorphism $E → L$, making $L$ an $E$-vector space. If we restrict the scalar multiplication to the subfield $F$, then $L$ is also an $F$-vector space. The degrees satisfy the tower property:
  $ [L : F] = [L : E] · [E : F]. $
]

#corollary[
  Let $f ∈ F[X]$ satisfy $n := deg f ≥ 1$. Then the extension field $E_f$  can be suitably chosen such that $[E_f : F] ≤ n!$.
]


