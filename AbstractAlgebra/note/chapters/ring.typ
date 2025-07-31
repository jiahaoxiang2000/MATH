#import "@preview/theorion:0.3.2": *

#let ring-content = [
  = Ring, Field and Polynomial

  == Ring & Field

  #definition(title: "Ring")[
    A ring is a tuple $(R,+,dot,0_R,1_R)$ where $R$ is a set, $0_R,1_R in R$, and $+: R times R arrow R$ and $dot: R times R arrow R$ are binary operations satisfying:
    1. Addition satisfies:
      - Associativity: $(x + y) + z = x + (y + z)$
      - Identity: $x + 0_R = x = 0_R + x$
      - Commutativity: $x + y = y + x$
      - Inverse: For all $x$ there exists $-x$ with $x + (-x) = 0_R$

    2. Multiplication (written as $x y$ for $x dot y$) satisfies:
      - Associativity: $(x y)z = x(y z)$
      - Identity: $x dot 1_R = x = 1_R dot x$

    3. Distributive Laws:
      - $(x + y)z = x z + y z$
      - $z(x + y) = z x + z y$

    Where $x,y,z$ represent arbitrary elements of $R$. When no confusion arises, we write $0_R, 1_R$ as $0,1$ and denote the ring by $R$. We write $x + (-y)$ as $x - y$.
  ]

  #definition(title: "Subring")[
    Let $R$ be a ring. A subset $R_0 subset.eq R$ containing $0_R, 1_R$ is called a subring of $R$ if it is closed under:
    - Addition: $x,y in R_0 arrow.double x + y in R_0$
    - Multiplication: $x,y in R_0 arrow.double x y in R_0$
    - Additive inverse: $x in R_0 arrow.double -x in R_0$

    Then $(R_0,+,dot,0_R,1_R)$ forms a ring.
  ]

  #definition(title: "Ring Invertibility")[
    Let $x$ be an element of a ring $R$.
    - If there exists $y in R$ such that $x y = 1$ (resp. $y x = 1$), then $y$ is called a right inverse (resp. left inverse) of $x$
    - $x$ is called right invertible (resp. left invertible) if it has a right (resp. left) inverse
    - $x$ is called invertible if it has both left and right inverses

    The set of invertible elements in $R$ is denoted by $R^times$.
  ]

  #proposition(title: "Uniqueness of Ring Inverses")[
    If an element $x$ in a ring $R$ is invertible, then:
    1. Its left inverse is also its right inverse
    2. There exists a unique $x^(-1) in R$ such that $x^(-1)x = 1 = x x^(-1)$
    3. $(x^(-1))^(-1) = x$

    #proof[
      Let $y$ be a left inverse and $z$ a right inverse of $x$.
      Then $y = y(x z) = (y x)z = z$.
      Therefore, $y = z = x^(-1)$ is the unique two-sided inverse.
      Clearly $(x^(-1))^(-1) = x$ by definition.
    ]
  ]

  #definition(title: "Commutative Ring")[
    A ring $R$ is called commutative if its multiplication is commutative, i.e.,
    $
      x y = y x text(" for all ") x,y in R
    $
  ]

  #definition(title: "Division Ring and Field")[
    A ring $R$ is called a division ring if $R^times = R without {0}$ (i.e., every non-zero element is invertible).
    A commutative division ring is called a field.
    A subring of a field that is itself a field is called a subfield.
  ]

  #definition(title: "Integral Domain")[
    A non-zero commutative ring $R$ is called an integral domain if for all $x,y in R$:
    $
      x,y eq.not 0 arrow.double x y eq.not 0
    $
  ] <def:integral_domain>

  == Homomorphism & Isomorphism

  #definition(title: "Ring Homomorphism")[
    Let $f : R arrow R'$ be a mapping between rings. We call $f$ a ring homomorphism if:
    - $f(x + y) = f(x) + f(y)$
    - $f(x y) = f(x)f(y)$
    - $f(1_R) = 1_(R')$

    for all $x,y in R$. A homomorphism from a ring to itself is called an endomorphism.
  ]

  #definition(title: "Ring Isomorphism")[
    Let $f : R arrow R'$ be a ring homomorphism. We call $f$ a ring isomorphism if there exists a ring homomorphism $g : R' arrow R$ such that:
    $
      g compose f = "id"_R text(" and ") f compose g = "id"_(R')
    $
    In this case, $g$ is called the inverse of $f$, and we say $R$ and $R'$ are isomorphic.
  ]

  #proposition[
    If $f : R arrow R'$ is a ring homomorphism that is bijective as a set mapping, then $f$ is a ring isomorphism.

    #proof[
      Let $g : R' arrow R$ be the inverse of $f$ as a set mapping.
      We need to show $g$ is a ring homomorphism:
      - For addition: $g(x' + y') = g(f(g(x')) + f(g(y'))) = g(x') + g(y')$
      - For multiplication: $g(x'y') = g(f(g(x'))f(g(y'))) = g(x')g(y')$
      - For identity: $g(1_(R')) = g(f(1_R)) = 1_R$

      Therefore $g$ is a ring homomorphism and $f$ is an isomorphism.
    ]
  ]

  #proposition(title: "Chinese Remainder Theorem - Ring Version")[
    Let $N in bb(Z)_(gt.eq 1)$ factor as $N = n_1 dots.c n_k$ where $n_1,dots,n_k$ are pairwise coprime. Then there exists a ring isomorphism:
    $
      phi: bb(Z)\/ N bb(Z) arrow.r^tilde product_(i=1)^k bb(Z)\/ n_i bb(Z)
    $
    given by $[x]_N arrow.bar ([x]_(n_i))_(i=1)^k$

    #proof[
      1. *Well-defined:* If $x equiv y space (mod space N)$, then $x equiv y space (mod space n_i)$ for all $i$

      2. *Ring homomorphism:*
        - $phi([x]_N + [y]_N) = phi([x+y]_N) = ([x+y]_(n_i)) = ([x]_(n_i) + [y]_(n_i))$
        - $phi([x]_N[y]_N) = phi([x y]_N) = ([x y]_(n_i)) = ([x]_(n_i)[y]_(n_i))$

      3. *Injective:* If $phi([x]_N) = phi([y]_N)$, then $x equiv y space (mod space n_i)$ for all $i$.
        Since $n_i$ are coprime, $x equiv y space (mod space N)$

      4. *Surjective:* Given $([a_i]_(n_i))$, by CRT there exists $x$ with $x equiv a_i space (mod space n_i)$.
        Then $phi([x]_N) = ([a_i]_(n_i))$
    ]
  ]

  #example(title: "Application of Chinese Remainder Theorem")[
    Find $x$ satisfying the system of congruences:
    $
      x & equiv 2 space (mod space 3) \
      x & equiv 3 space (mod space 5) \
      x & equiv 2 space (mod space 7)
    $

    Solution:
    1. $N = 3 dot 5 dot 7 = 105$
    2. Find $M_i$:
      - $M_1 = 35$ (for mod 3)
      - $M_2 = 21$ (for mod 5)
      - $M_3 = 15$ (for mod 7)
    3. Find $y_i$ where $M_i y_i equiv 1 space (mod space n_i)$:
      - $35 y_1 equiv 1 space (mod space 3) arrow.double y_1 = 2$
      - $21 y_2 equiv 1 space (mod space 5) arrow.double y_2 = 1$
      - $15 y_3 equiv 1 space (mod space 7) arrow.double y_3 = 1$
    4. $x = (2 dot 35 dot 2 + 3 dot 21 dot 1 + 2 dot 15 dot 1) mod 105 = 23$

    Verify: $23 equiv 2 space (mod space 3)$, $23 equiv 3 space (mod space 5)$, $23 equiv 2 space (mod space 7)$
  ]

  == Polynomial Ring

  #definition(title: "Polynomial Ring")[
    Let $R$ be a non-zero ring. A polynomial in variable $X$ with coefficients in $R$ is defined as a formal sum:
    $
      f = sum_(n gt.eq 0) a_n X^n, quad a_n in R
    $
    where only finitely many $a_n$ are non-zero. Terms with $a_n = 0$ may be omitted. When emphasis on the variable is needed, we write $f(X)$. The set of all such polynomials is denoted $R[X]$.
  ]

  #definition(title: "Operations on Polynomials")[
    Addition of polynomials is defined term by term:
    $
      sum_(n gt.eq 0) a_n X^n + sum_(n gt.eq 0) b_n X^n := sum_(n gt.eq 0) (a_n + b_n)X^n
    $

    Multiplication is defined by convolution:
    $
      (sum_(n gt.eq 0) a_n X^n) dot (sum_(n gt.eq 0) b_n X^n) := sum_(n gt.eq 0) (sum_(h+k=n) a_h b_k)X^n
    $
  ]

  #proposition(title: "Ring Structure of Polynomials")[
    With the above operations, $R[X]$ forms a ring where:
    1. The zero polynomial is $0_(R[X])$
    2. The unit polynomial is the constant polynomial $1_(R[X])$ corresponding to $1_R$
    3. $R$ embeds as a subring of $R[X]$
    4. If $R$ is commutative, then $R[X]$ is also commutative
  ]

  -- TODO reading next time

  #lemma(title: "Degree Properties in Integral Domains")[
    Let $R$ be an integral domain. Then for all non-zero $f,g in R[X]$:
    $
      deg(f g) = deg f + deg g
    $
    Consequently:
    1. $R[X]$ is also an integral domain
    2. $R[X]^times = R^times$
  ] <lem:degree_properties_integral_domains>

  #definition(title: "Homogeneous Polynomials")[
    Let $f = sum_(a_1,dots,a_n gt.eq 0) c_(a_1,dots,a_n) X_1^(a_1) dots.c X_n^(a_n)$ be an element of $R[X_1,dots,X_n]$.

    $f$ is called homogeneous of degree $N$ if there exists $N in bb(Z)_(gt.eq 0)$ such that $c_(a_1,dots,a_n) eq.not 0$ implies $a_1 + dots.c + a_n = N$.
  ]

  #remark[
    This concept extends naturally to polynomial rings with infinitely many variables, as they can be written as unions of subrings with finitely many variables.
  ]

  #definition(title: "Polynomial Composition")[
    Let $R$ be a commutative ring. For $n,m in bb(Z)_(gt.eq 1)$, given:
    $
      f = sum_(a_1,dots,a_n gt.eq 0) c_(a_1,dots,a_n) X_1^(a_1) dots.c X_n^(a_n) in R[X_1,dots,X_n]
    $
    and $g_1,dots,g_n in R[Y_1,dots,Y_m]$

    Let $g := (g_1,dots,g_n) in R[Y_1,dots,Y_m]^n$. The composition is defined as:
    $
      f compose g := sum_(a_1,dots,a_n gt.eq 0) c_(a_1,dots,a_n) g_1^(a_1) dots.c g_n^(a_n) in R[Y_1,dots,Y_m]
    $
  ]

  #proposition(title: "Polynomial Ring Isomorphisms")[
    For any ring $R$, there exists a natural ring isomorphism:
    $
      R[X,Y] tilde.eq (R[X])[Y]
    $
    More generally, for any $n gt.eq 2$, there are ring isomorphisms:
    $
      R[X_1,dots,X_n] tilde.eq R[X_1,dots,X_(n-1)][X_n] tilde.eq dots.c tilde.eq R[X_1]dots.c[X_n]
    $

    #proof[
      Let's prove for $R[X,Y] tilde.eq (R[X])[Y]$. Define:
      $
        phi: R[X,Y] arrow (R[X])[Y]
      $
      by sending $sum_(i,j) a_(i j)X^i Y^j$ to $sum_j (sum_i a_(i j)X^i)Y^j$

      1. Ring homomorphism:
        - Addition: Clear from coefficients reorganization
        - Multiplication: Terms with same total degree in $Y$ combine

      2. Bijective:
        - Injective: Different polynomials map to different arrangements
        - Surjective: Any element in $(R[X])[Y]$ comes from rearranging terms

      The general case follows by induction on $n$.
    ]
  ]

  #corollary[
    If $R$ is an integral domain, then any polynomial ring $R[X,Y,dots]$ with any number of variables is also an integral domain, and $R[X,Y,dots]^times = R^times$.

    #proof[
      By induction on the number of variables:
      1. Base case: For $R[X]$, already proved in @lem:degree_properties_integral_domains
      2. Inductive step: Assume true for $n$ variables
      3. For $n+1$ variables, use isomorphism:
        $
          R[X_1,dots,X_(n+1)] tilde.eq (R[X_1,dots,X_n])[X_(n+1)]
        $
      4. By induction hypothesis, $R[X_1,dots,X_n]$ is an integral domain
      5. Apply one-variable case to get result
    ]
  ]

  #proposition(title: "Polynomial Division Algorithm")[
    For any polynomials $a,d in F[X]$ where $d eq.not 0$, there exist unique polynomials $q,r in F[X]$ such that:
    $
      a = d q + r quad text("with") quad deg(r) < deg(d)
    $
    where we define $deg(0) := -infinity$.

    #proof[
      *Existence:* By induction on $deg(a)$
      - If $deg(a) < deg(d)$: Take $q=0, r=a$
      - If $deg(a) gt.eq deg(d)$:
        - Let $c = "lc"(a)/"lc"(d)$ and $n = deg(a) - deg(d)$
        - Set $a_1 = a - d c X^n$
        - Note $deg(a_1) < deg(a)$
        - By induction: $a_1 = d q_1 + r$
        - Then $a = d(q_1 + c X^n) + r$

      *Uniqueness:* If $a = d q_1 + r_1 = d q_2 + r_2$, then:
      - $d(q_1 - q_2) = r_2 - r_1$
      - If $q_1 eq.not q_2$, then $deg(r_2 - r_1) gt.eq deg(d)$
      - But $deg(r_2 - r_1) < deg(d)$
      - Therefore $q_1 = q_2$ and $r_1 = r_2$
    ]
  ]

  #definition(title: "Root of Polynomial")[
    Let $f in F[X]$ and $a in F$. We say $a$ is a root of $f$ if $f(a) = 0$.

    More generally, for a commutative ring $R$, if $f in R[X]$ and $a in R$ satisfy $f(a) = 0$, then $a$ is called a root of $f$, or more precisely, a root of $f$ in $R$.
  ]

  #proposition(title: "Bound on Number of Roots")[
    Let $f in F[X] without {0}$. Then $f$ has at most $deg f$ distinct roots in $F$.

    #proof[
      By induction on $deg f$:
      - Base case: If $deg f = 0$, then $f$ is constant and non-zero, so has no roots

      - Inductive step: Let $a$ be a root of $f$
        - Then $X-a$ divides $f$, so $f = (X-a)g$ for some $g$
        - $deg g = deg f - 1$
        - Any root of $f$ different from $a$ must be a root of $g$
        - By induction, $g$ has at most $deg g$ distinct roots
        - Therefore $f$ has at most $1 + deg g = deg f$ distinct roots
    ]
  ]

  == Fractional Field to Rational Function Field

  #definition(title: "Rational Functions")[
    A rational function over $R$ is defined as a quotient $f/g$ where:
    - $f,g in R[X]$
    - $g$ is not the zero polynomial (i.e., $g eq.not 0_(R[X])$)
  ]

  #proposition(title: "Fraction Field")[
    Let $R$ be an integral domain. Then:
    1. $"Frac"(R)$ forms a field under the given operations
    2. The map $f arrow.bar [f,1]$ embeds $R$ as a subring of $"Frac"(R)$
  ]

  #proposition(title: "Universal Property of Fraction Field (MORE)")[
    Let $R$ be an integral domain, $R'$ a commutative ring, and $phi : R arrow R'$ a ring homomorphism such that $phi(R without {0}) subset (R')^times$. Then there exists a unique ring homomorphism $Phi : "Frac"(R) arrow R'$ making the following diagram commute:
    $
      cases(
        R arrow.r^phi R',
        R arrow.b,
        "Frac"(R) arrow.r^Phi R'
      )
    $
    Explicitly, $Phi(f\/g) = phi(f)phi(g)^(-1)$.
  ]

  #corollary[
    Let $F$ be a field containing an integral domain $R$ as a subring. If every element of $F$ can be expressed as $f g^(-1)$ where $f,g in R$ and $g eq.not 0$, then there exists a unique ring isomorphism $Phi : "Frac"(R) arrow F$ making the following diagram commute:
    $
      cases(
        R arrow.r^"inclusion" F,
        R arrow.b,
        "Frac"(R) arrow.r^(tilde Phi) F
      )
    $

    #proof[
      By universal property, there exists unique $Phi : "Frac"(R) arrow F$.
      - Injective: As composition of non-zero elements remains non-zero
      - Surjective: Every element in $F$ has form $f g^(-1)$ with $f,g in R$
      - Therefore $Phi$ is an isomorphism
    ]
  ]

  #definition(title: "Field of Rational Functions")[
    Let $F$ be a field. The field of fractions of $F[X,Y,dots]$ is called the field of rational functions in variables $X,Y,dots$, denoted $F(X,Y,dots)$. It contains $F[X,Y,dots]$ as a subring.

    Elements of $F(X,Y,dots)$ are called rational functions in variables $X,Y,dots$ with coefficients in $F$.
  ]

  #definition(title: "Degree of Rational Functions")[
    Let $F$ be a field. For any $h = f/g in F(X)$ where $h eq.not 0$, define:
    $
      deg h := deg f - deg g
    $
    Additionally, define $deg(0) := -infinity$.
  ]

  #corollary(title: "Bound on Roots in Integral Domain")[
    Let $R$ be an integral domain and $f in R[X] without {0}$. Then $f$ has at most $deg f$ distinct roots in $R$.

    #proof[
      Let $F = "Frac"(R)$ be the fraction field of $R$.
      Since $R$ is a subring of $F$, any root of $f$ in $R$ is also a root in $F$.
      By the previous proposition, $f$ has at most $deg f$ distinct roots in $F$.
      Therefore, $f$ has at most $deg f$ distinct roots in $R$.
    ]
  ] <cor:bound_on_roots_in_integral_domain>

  #proposition(title: "Function Evaluation Map")[
    Let $R$ be an integral domain and $n in bb(Z)_(gt.eq 1)$. The function evaluation map:
    $
      "Fcn" : R[X_1,dots,X_n] arrow {"functions " R^n arrow R}
    $
    is injective if and only if $R$ has infinitely many elements.
  ]

  #theorem(title: "Extension Principle for Algebraic Equations")[
    Let $R$ be an infinite integral domain, $f,g_1,dots,g_m in R[X_1,dots,X_n]$,
    where $g_1,dots,g_m$ are non-zero. If for all $(x_1,dots,x_n) in R^n$:
    $
      (g_1(x_1,dots,x_n) eq.not 0 and dots.c and g_m(x_1,dots,x_n) eq.not 0) arrow.double f(x_1,dots,x_n) = 0
    $
    then $f = 0$.

    #proof[
      By contradiction, assume $f eq.not 0$.
      1. Let $U = {x in R^n : g_1(x) eq.not 0,dots,g_m(x) eq.not 0}$
      2. Since $R$ is infinite and $g_i$ are non-zero, $U$ is non-empty
      3. By hypothesis, $f$ vanishes on $U$
      4. But $f eq.not 0$ implies $f$ can only vanish at finitely many points
      5. This contradicts $R$ being infinite
      Therefore $f = 0$.
    ]
  ]

  == Monoid Group

  #definition(title: "Monoid")[
    We say that $(S, *)$ is a monoid if the binary operation satisfies the associative law and has an identity element. That is,
    $
      forall x, y, z in S, quad x * (y * z) = (x * y) * z
    $
    and
    $
      exists e in S, forall x in S, quad e * x = x * e = x
    $
  ] <def:monoid>

  #definition(title: "Commutative Monoid")[
    We say that $(S, *)$ is a commutative monoid if it is a monoid and the operation satisfies the commutative law. That is,
    $
      forall x, y in S, quad x * y = y * x
    $
  ] <def:commutative_monoid>

  #proposition(title: "Uniqueness of Identity Element")[
    Let $(S, dot)$ be a monoid. Then the identity element is unique.

    #proof[
      Suppose that $e$ and $e'$ are both identity elements of $S$. Then
      $
        e = e dot e' = e'
      $
      so $e = e'$.
    ]
  ] <prop:uniqueness_of_identity_element>

  #proposition(title: "Expansion of Associative Law")[
    Let $x_1, dots, x_n, y_1, dots, y_m in S$. Then
    $
      x_1 dot x_2 dot dots x_n dot y_1 dot y_2 dot dots y_m = (x_1 dot x_2 dot dots x_n) dot (y_1 dot y_2 dot dots y_m)
    $

    #proof[
      We prove this by induction on $n$.

      *Base Case ($n = 1$):*
      When $n = 1$, the statement simplifies to:
      $
        x_1 dot y_1 dot y_2 dot dots y_m = x_1 dot (y_1 dot y_2 dot dots y_m)
      $
      This is clearly true by the associative property of multiplication.

      *Inductive Step:*
      Assume the statement holds for $n = k$, that is:
      $
        x_1 dot x_2 dot dots x_k dot y_1 dot y_2 dot dots y_m = (x_1 dot x_2 dot dots x_k) dot (y_1 dot y_2 dot dots y_m)
      $
      We need to show that the statement holds for $n = k + 1$. Consider:
      $
        x_1 dot x_2 dot dots x_k dot x_(k+1) dot y_1 dot y_2 dot dots y_m
      $
      By the associative property, we can regroup the terms as:
      $
        (x_1 dot x_2 dot dots x_k ) dot (x_(k+1) dot y_1 dot y_2 dot dots y_m)
      $
      Using the inductive hypothesis on the first $k$ terms, we have:
      $
        (x_1 dot x_2 dot dots x_k) dot x_(k+1) dot (y_1 dot y_2 dot dots y_m) = (x_1 dot x_2 dot dots x_k dot x_(k+1)) dot (y_1 dot y_2 dot dots y_m)
      $
      Thus, the statement holds for $n = k + 1$.
    ]
  ] <prop:expand_of_associative_law>

  #proposition[
    Let $x in S$ and $m,n in bb(N)$. Then
    $
      x^(m+n) = x^m dot x^n
    $

    #proof[
      We will prove this in three steps:

      *Step 1:* First, recall from @prop:expand_of_associative_law that for any elements in $S$:
      $
        x_1 dot x_2 dot dots x_n dot y_1 dot y_2 dot dots y_m = (x_1 dot x_2 dot dots x_n) dot (y_1 dot y_2 dot dots y_m)
      $

      *Step 2:* Now, consider the special case where all elements are equal to $x$:
      - Let $x_1 = x_2 = dots = x_m = x$
      - Let $y_1 = y_2 = dots = y_n = x$

      *Step 3:* By definition of exponentiation in a monoid:
      $
        x^(m+n) & = underbrace(x dot x dot dots x)_(m+n text(" times")) \
                & = (underbrace(x dot x dot dots x)_(m text(" times"))) dot (underbrace(x dot x dot dots x)_(n text(" times"))) \
                & = x^m dot x^n
      $

      Therefore, we have proved that $x^(m+n) = x^m dot x^n$ for all $x in S$ and $m,n in bb(N)$.
    ]
  ]

  #definition(title: "Submonoid")[
    Let $(S,dot)$ be a monoid. If $T subset S$, we say that $(T,dot)$ is a submonoid of $(S,dot)$ if:
    1. The identity element $e in T$
    2. $T$ is closed under multiplication, that is:
      $
        forall x,y in T, quad x dot y in T
      $
  ] <def:submonoid>

  #proposition[
    If $(T,dot)$ is a submonoid of $(S,dot)$, then $(T,dot)$ is a monoid.

    #proof[
      We need to verify two properties:
      1. The operation is associative in $T$:
        Since $T subset S$ and $dot$ is associative in $S$, it is also associative in $T$.

      2. $T$ has an identity element:
        By definition of submonoid, the identity element $e in T$.

      Therefore, $(T,dot)$ satisfies all properties of a monoid.
    ]
  ]

  #definition(title: "Monoid Homomorphism")[
    Let $(S,dot)$ and $(T,*)$ be monoids, and let $f : S arrow T$ be a mapping.
    We say $f$ is a monoid homomorphism if $f$ preserves multiplication and maps the identity element to the identity element. That is:
    1. For all $x,y in S$:
      $
        f(x dot y) = f(x) * f(y)
      $
    2. For the identity elements $e in S$ and $e' in T$:
      $
        f(e) = e'
      $
  ] <def:monoid_homomorphism>

  #remark[
    While a homomorphism preserves operations, an isomorphism represents complete structural equivalence. An isomorphism is first a *bijective mapping*, meaning it establishes a one-to-one correspondence between elements - essentially "relabeling" elements uniquely. Beyond being bijective, an isomorphism preserves operations under this relabeling, implying that the only difference between two structures (like monoids) is their labeling.
  ]

  #example(title: "Different Types of Monoid Maps")[
    Let's examine several maps between monoids:

    1. *A homomorphism that is not an isomorphism:*
      Consider $f: (bb(Z), +) arrow (bb(Z), +)$ defined by $f(n) = 2n$
      - Preserves operation: $f(a + b) = 2(a + b) = 2a + 2b = f(a) + f(b)$
      - Is injective: $f(a) = f(b) arrow.double 2a = 2b arrow.double a = b$
      - Not surjective: odd numbers are not in the image
      - Therefore: homomorphism but not isomorphism

    2. *Non-isomorphic homomorphism:*
      Consider $h: (bb(Z), +) arrow (bb(Z)_2, +)$ defined by $h(n) = n mod 2$
      - Preserves operation: $h(a + b) = (a + b) mod 2 = (a mod 2 + b mod 2) mod 2 = h(a) + h(b)$
      - Not injective: $h(0) = h(2) = 0$
      - Surjective: image is all of $bb(Z)_2$
      - Therefore: homomorphism but not isomorphism
  ]

  #definition(title: "Generated Submonoid")[
    Let $(S,dot)$ be a monoid and $A subset S$ be a subset. The submonoid generated by $A$, denoted by $angle.l A angle.r$, is defined as the intersection of all submonoids of $S$ containing $A$. That is:
    $
      angle.l A angle.r = sect {T subset S : T supset A, text(" $T$ is a submonoid")}
    $
  ]

  #proposition[
    Let $(S,dot)$ be a monoid and $A subset S$ be a subset. Then $angle.l A angle.r$ is also a submonoid. Therefore, it is the smallest submonoid containing $A$.

    #proof[
      We will prove this in two steps:

      *Step 1:* Show $angle.l A angle.r$ contains the identity element

      Let ${T_alpha}_(alpha in I)$ be the collection of all submonoids containing $A$,
      Each $T_alpha$ contains the identity $e$ (by definition of submonoid),
      Therefore $e in sect_(alpha in I) T_alpha = angle.l A angle.r$

      *Step 2:* Show closure under multiplication

      Let $x, y in angle.l A angle.r = sect_(alpha in I) T_alpha$,
      Then $x, y in T_alpha$ for all $alpha in I$
      Since each $T_alpha$ is a submonoid, $x dot y in T_alpha$ for all $alpha in I$,
      Therefore $x dot y in sect_(alpha in I) T_alpha = angle.l A angle.r$.
    ]
  ]

  #definition(title: "Monoid Isomorphism")[
    Let $(S,dot)$ and $(T,*)$ be monoids, and let $f : S arrow T$ be a mapping. We say $f$ is a monoid isomorphism if $f$ is bijective and a homomorphism. That is:
    1. $f$ is bijective (one-to-one and onto)
    2. For all $x,y in S$:
      $
        f(x dot y) = f(x) * f(y)
      $
    3. For the identity elements $e in S$ and $e' in T$:
      $
        f(e) = e'
      $
  ]

  #proposition[
    If $f : (S,dot) arrow (T,*)$ is a monoid isomorphism, then $f^(-1) : T arrow S$ is a monoid homomorphism. Therefore, $f^(-1)$ is also a monoid isomorphism.

    #proof[
      Since $f$ is an isomorphism, $f^(-1)$ exists and is bijective. We need to show:
      1. $f^(-1)$ preserves operation:
        $
          f^(-1)(a * b) & = f^(-1)(f(f^(-1)(a)) * f(f^(-1)(b))) \
                        & = f^(-1)(f(f^(-1)(a) dot f^(-1)(b))) \
                        & = f^(-1)(a) dot f^(-1)(b)
        $

      2. $f^(-1)$ preserves identity:
        $
          f^(-1)(e') = e text(" where $e'$ and $e$ are identity elements")
        $

      Therefore, $f^(-1)$ is both a homomorphism and bijective, making it an isomorphism.
    ]
  ]

  == Group

  #definition(title: "Invertible Element")[
    Let $(S,dot)$ be a monoid and $x in S$. We say $x$ is invertible if and only if
    $
      exists y in S, x dot y = y dot x = e
    $
    where $y$ is called the inverse of $x$, denoted as $x^(-1)$.
  ] <def:invertible_element>

  #proposition(title: "Uniqueness of Inverse")[
    Let $(S,dot)$ be a monoid. If $x in S$ is invertible, then its inverse is unique. That is, if $y,y' in S$ are both inverses of $x$, then $y = y'$.

    #proof[
      Let $y$ and $y'$ be inverses of $x$. Then:
      $
        y & = y dot e \
          & = y dot (x dot y') \
          & = (y dot x) dot y' \
          & = e dot y' \
          & = y'
      $
      Therefore, the inverse is unique.
    ]
  ] <prop:uniqueness_of_inverse>

  #definition(title: "Group")[
    Let $(G,dot)$ be a monoid. We say it is a group if every element in $G$ is invertible.

    Equivalently, if $dot$ is a binary operation on $G$, we say $(G,dot)$ is a group, or $G$ forms a group under $dot$, when this operation satisfies:
    1. Associativity: For all $x,y,z in G$
      $
        x dot (y dot z) = (x dot y) dot z
      $

    2. Identity element: There exists $e in G$ such that for all $x in G$
      $
        x dot e = e dot x = x
      $

    3. Inverse elements: For each $x in G$, there exists $y in G$ such that
      $
        x dot y = y dot x = e
      $
  ] <def:group>

  #proposition[
    Let $(G,dot)$ be a group and $x in G$. Then $(x^(-1))^(-1) = x$.

    #proof[
      Let $y = x^(-1)$. Then:
      $
        y dot x = x dot y = e
      $
      This shows that $x$ is the inverse of $y = x^(-1)$.
      Therefore, $(x^(-1))^(-1) = x$.
    ]
  ]

  #proposition(title: "Inverse of Product")[
    Let $(G,dot)$ be a group and $x,y in G$. Then $(x dot y)^(-1) = y^(-1) dot x^(-1)$.

    #proof[
      We will show that $y^(-1) dot x^(-1)$ is the inverse of $x dot y$:
      $
        (x dot y)(y^(-1) dot x^(-1)) & = x dot (y dot y^(-1)) dot x^(-1) \
                                     & = x dot e dot x^(-1) \
                                     & = x dot x^(-1) \
                                     & = e
      $
      Similarly, $(y^(-1) dot x^(-1))(x dot y) = e$.
      Therefore, $(x dot y)^(-1) = y^(-1) dot x^(-1)$.
    ]
  ]

  #definition(title: "Abelian Group")[
    Let $(G,dot)$ be a group. We say it is an abelian group, or commutative group, if the operation satisfies the commutative law:
    $
      forall x,y in G, quad x dot y = y dot x
    $
  ] <def:abelian_group>

  #lemma[
    Let $(S,dot)$ be a monoid and let $G$ be the subset of all invertible elements in $S$. Then $(G,dot)$ is a group.

    #proof[
      We need to verify three group axioms:
      1. Closure: If $x,y in G$, then $x dot y in G$ (as product of invertible elements is invertible)
      2. Identity: $e in G$ (as $e$ is invertible)
      3. Inverse: If $x in G$, then $x^(-1) in G$ (by definition of invertible elements)
      Associativity is inherited from $S$. Therefore, $(G,dot)$ is a group.
    ]
  ]

  #definition(title: "General Linear Group")[
    The group of $n times n$ invertible real matrices under matrix multiplication is called the general linear group of degree $n$ over the real numbers, denoted as $(G L(n,bb(R)),dot)$. Since a matrix is invertible if and only if its determinant is nonzero:
    $
      G L(n,bb(R)) = { A in M(n,bb(R)) : det(A) eq.not 0 }
    $
  ] <def:general_linear_group>

  #definition(title: "Special Linear Group")[
    The special linear group of degree $n$ over the real numbers is the group of $n times n$ real matrices with determinant exactly $1$ under matrix multiplication, denoted as $(S L(n,bb(R)),dot)$. That is:
    $
      S L(n,bb(R)) = { A in M(n,bb(R)) : det(A) = 1 }
    $
  ]

  #definition(title: "Subgroup")[
    Let $(G,dot)$ be a group and $H subset G$. We say $H$ is a subgroup of $G$, denoted as $H < G$, if it contains the identity element and is closed under multiplication and inverse operations. That is:
    1. $forall x,y in H, quad x dot y in H$ (closure under multiplication)
    2. $forall x in H, quad x^(-1) in H$ (closure under inverse)
    3. $e in H$ (contains identity)
  ] <def:subgroup>

  #proposition[
    Let $(G,dot)$ be a group. If $H$ is a subgroup of $G$, then $(H,dot)$ is also a group.

    #proof[
      Since $H$ is a subgroup:
      1. Associativity: Inherited from $G$
      2. Identity: $e in H$ by definition of subgroup
      3. Inverse: For all $x in H$, $x^(-1) in H$ by definition of subgroup
      4. Closure: For all $x,y in H$, $x dot y in H$ by definition of subgroup
      Therefore, $(H,dot)$ satisfies all group axioms.
    ]
  ]

  #proposition[
    For convenience, we can combine the first two conditions of a subgroup definition into one, reducing to two conditions:
    1. $forall x,y in H, quad x dot y^(-1) in H$
    2. $e in H$
    These conditions are equivalent to the original subgroup definition.

    #proof[
      $(arrow.double)$  $forall y in H$, $y^(-1) in H$, then the closure under multiplication,  $forall x,y,y^(-1) in H$, $x dot y^(-1) in H$

      $(arrow.l.double)$ $forall x,y in H$, $x dot y^(-1) in H$, let $x=e$, then have $forall y in H$, $y^(-1) in H$; so $forall x,y^(-1) in H$, $x dot (y^(-1))^(-1) in H$, then $x dot y in H$.
    ]
  ]

  #proposition[
    $(S L(n,bb(R)),dot)$ is a group.

    #proof[
      We verify the group axioms:
      1. Closure: If $A,B in S L(n,bb(R))$, then $det(A B) = det(A)det(B) = 1 dot 1 = 1$, so $A B in S L(n,bb(R))$

      2. Identity: The identity matrix $I_n in S L(n,bb(R))$ since $det(I_n) = 1$

      3. Inverse: If $A in S L(n,bb(R))$, then $det(A^(-1)) = 1/det(A) = 1$, so $A^(-1) in S L(n,bb(R))$

      4. Associativity: Inherited from matrix multiplication

      Therefore, $(S L(n,bb(R)),dot)$ is a group.
    ]
  ]

  #definition(title: "Group Homomorphism")[
    Let $(G,dot)$ and $(G',*)$ be groups, and let $f : G arrow G'$ be a mapping. We say $f$ is a group homomorphism if it preserves the operation, that is:
    $
      forall x,y in G, quad f(x dot y) = f(x) * f(y)
    $
  ]

  #proposition[
    Let $f : (G,dot) arrow (G',*)$ be a group homomorphism. Then:
    1. $f(e) = e'$ (preserves identity)
    2. $f(x^(-1)) = f(x)^(-1)$ (preserves inverses)

    #proof[
      1. For identity element:
        $
             f(e) * f(e) & = f(e dot e) = f(e) quad text("left multiply by ") f(e)^(-1) \
          therefore f(e) & = e'
        $
      2. For inverse elements:
        $
             f(x) * f(x^(-1)) & = f(x dot x^(-1)) = f(e) = e' quad text("left multiply by ") f(x)^(-1) \
          therefore f(x^(-1)) & = f(x)^(-1)
        $
    ]
  ]
]
