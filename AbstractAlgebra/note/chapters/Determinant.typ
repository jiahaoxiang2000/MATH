#import "@preview/theorion:0.3.2": *

#let determinant-content = [

  = Determinant

  == Permutations Introduction

  #definition[
    Let $X$ be a non-empty set. The set of permutations on $X$ is defined as
    $
      S_X := {sigma : X -> X | sigma text(" is a bijection")} .
    $
    It contains the identity mapping $"id" = "id"_X in S_X$. These permutations can be composed as functions, $(sigma, sigma') |-> sigma sigma'$, or inverted, $sigma |-> sigma^(-1)$, and the result still belongs to $S_X$.
  ]

  #definition[
    Fix $n in bb(Z)_(>= 1)$. For $1 <= i != j <= n$, the corresponding transposition $(i space j) in S_n$ is defined as the following permutation:
    $
      (i space j): quad k |-> cases(
        j\, quad & "if " k = i,
        i\, quad & "if " k = j,
        k\, quad & "if " k != i\, j.
      )
    $
    In other words, $(i space j)$ swaps $i$ and $j$, and leaves all other elements unchanged.
  ]

  #definition[
    Let $sigma in S_n$. The elements of the following set are called the inversions of $sigma$:
    $
      "Inv"_sigma := {(i, j) in bb(Z)^2 : 1 <= i < j <= n, sigma(i) > sigma(j)} .
    $
    The number of inversions of $sigma$ is defined as $ell(sigma) := |"Inv"_sigma|$.
  ]

  #proposition[
    Let $sigma in S_n$. Then there exists $ell in bb(Z)_(>= 0)$ and a sequence of transpositions $tau_1, ..., tau_ell in S_n$ such that
    $
      sigma = tau_1 dots tau_ell ;
    $
    when $ell = 0$, the product on the right is understood as the identity $"id"$. We call $ell$ the length of the above decomposition. Among all decompositions of $sigma$ into transpositions, the minimal possible length is $ell(sigma)$.
  ]

  #proposition[
    There exists a unique map $"sgn" : S_n -> {plus.minus 1}$ such that the following properties hold:
    + For all $sigma, xi in S_n$, we have $"sgn"(sigma xi) = "sgn"(sigma)"sgn"(xi)$,
    + If $tau in S_n$ is a transposition, then $"sgn"(tau) = -1$.

    The above map $"sgn"$ satisfies $"sgn"("id") = 1$ and $"sgn"(sigma^(-1)) = "sgn"(sigma)^(-1) = "sgn"(sigma)$. Its value can further be expressed in terms of the number of inversions as
    $
      "sgn"(sigma) = (-1)^(ell(sigma)) .
    $
  ]

  #definition[
    Let $sigma in S_n$. If there exists a sequence of transpositions $tau_1, ..., tau_ell$ such that $sigma = tau_1 dots tau_ell$, where $ell in bb(Z)_(>= 0)$ is even (respectively, odd), then $sigma$ is called an _even permutation_ (respectively, _odd permutation_).
  ]

  == A Characterization of a Class of Alternating Forms

  #definition[
    Let $V$ be a vector space over a field $F$. For every $m in bb(Z)_(>= 1)$, define
    $
      D_(V,m) := {D : V^m -> F | text("D satisfies the following properties D.1 and D.2")} .
    $
    + *D.1* For each $1 <= i <= m$,
      $
        D(..., v_i + v_i', ...) = D(..., v_i, ...) + D(..., v_i', ...),
      $
      $
        D(..., t v_i, ...) = t D(..., v_i, ...),
      $
      where $v_i, v_i' in V$ and $t in F$, and the ellipsis indicates that the other $m-1$ variables are fixed.
    + *D.2* If there exist $1 <= i < j <= m$ such that $v_i = v_j$, then
      $
        D(v_1, ..., v_m) = 0.
      $

    A map in $D_(V,m)$ is also called an $m$-linear alternating form on $V$.
  ]

  #lemma[
    Let $m in bb(Z)_(>= 1)$, $D in D_(V,m)$, and $sigma in S_m$. Then
    $
      D(v_(sigma^(-1)(1)), ..., v_(sigma^(-1)(m))) = "sgn"(sigma) D(v_1, ..., v_m),
    $
    where $"sgn" : S_m -> {plus.minus 1}$ is the sign map.
  ]

  #theorem[
    Let $V$ be a finite-dimensional vector space. Then $dim D_V = 1$. If $n := dim V >= 1$ and $e_1, ..., e_n$ is an ordered basis of $V$, denoted by $e$, then there exists a unique $D_e in D_V$ such that $D_e(e_1, ..., e_n) = 1$.
  ]

  == Definition of Determinant

  #definition[
    Let $V$ be an $n$-dimensional vector space, $n in bb(Z)_(>= 1)$. For each $T in "End"(V)$, define $det T in F$ to be the unique element such that
    $
      T^*(D) = (det T) dot D, quad D in D_V;
    $
    equivalently, for every $D in D_V$ and $(v_1, ..., v_n) in V^n$,
    $
      D(T v_1, ..., T v_n) = det T dot D(v_1, ..., v_n).
    $
    In the case of the zero vector space ($n = 0$), for $T = 0_V = "id"_V$, we define $det(T) := 1$.
  ]

  #theorem[
    The determinant has the following properties:
    + $det("id"_V) = 1$.
    + For $S, T in "End"(V)$, $det(S T) = det(S) det(T)$.
    + If $T$ is invertible, then $det T in F$ is also invertible, and $det(T^(-1)) = (det T)^(-1)$.
  ]

  #proposition[
    Let $T in "End"(V)$ and let $S : V tilde.equiv W$ be an isomorphism of finite-dimensional vector spaces. Then $S T S^(-1) in "End"(W)$ satisfies
    $
      det(S T S^(-1)) = det T.
    $
  ]

  #proposition[
    Let $V$ be an $n$-dimensional vector space (with $n >= 1$), and let $e_1, ..., e_n$ be an ordered basis of $V$, denoted by $e$. Let $D_e in D_V$. Then
    $
      det T = D_e(T e_1, ..., T e_n).
    $
  ]

  #proposition[
    Let $e$ be the standard ordered basis of $F^n$, $n in bb(Z)_(>= 1)$. In this way, each $A = (a_(i j))_(i,j) in M_(n times n)(F)$ is identified with an element of $"End"(F^n)$. The determinant of the matrix $A$ is defined as
    $
      det A := D_e(A e_1, ..., A e_n),
    $
    Then,
    $
      det A & = sum_(sigma in S_n) "sgn"(sigma) a_(sigma(1),1) dots a_(sigma(n),n) \
            & = sum_(sigma in S_n) "sgn"(sigma) a_(1,sigma(1)) dots a_(n,sigma(n)).
    $
  ]

  #definition[
    Let $1 <= i, j <= n$, where $n in bb(Z)_(>= 1)$. The $(i, j)$-th minor of a matrix $A in M_(n times n)(F)$ is defined as the determinant of the $(n-1) times (n-1)$ matrix $M_(i j)$ obtained by deleting the $i$-th row and $j$-th column from $A$. It is denoted by
    $
      M_(i j) := det M_(i j) in F.
    $
  ]

  == Cramer's Rule

  #proposition[
    Let $V$ be a finite-dimensional $F$-vector space. Then $T in "End"(V)$ is invertible if and only if $det T in F^times$.
  ]

  #corollary[
    Let $v_1, ..., v_n$ be elements of an $n$-dimensional $F$-vector space $V$ ($n in bb(Z)_(>= 1)$). Then the following statements are equivalent:
    + $v_1, ..., v_n$ are linearly dependent;
    + $D(v_1, ..., v_n) = 0$ for all $D in D_V$;
    + There exists an ordered basis $e_1, ..., e_n$ of $V$, denoted by $e$, such that $D_e(v_1, ..., v_n) = 0$.
  ]

  #definition[
    Let $n in bb(Z)_(>= 1)$. For $A = (a_(i j))_(i,j) in M_(n times n)(F)$, the classical adjugate matrix is defined as
    $
      A^upright("v") = (A_(j i))_(i,j) in M_(n times n)(F),
    $
    where
    $
      A_(i j) := (-1)^(i+j) M_(i j), quad 1 <= i, j <= n,
    $
    and $M_(i j)$ is the $(i,j)$-th minor of $A$.
  ]

  #theorem[
    For any $A in M_(n times n)(F)$, we have
    $
      A A^upright("v") = det A dot 1_(n times n) = A^upright("v") A.
    $
  ]

  #corollary(title: "Cramer's Rule")[
    Consider the system of $n$ linear equations over a field $F$:
    $
      cases(
        a_(1 1) X_1 + dots + a_(1 n) X_n = b_1,
        dots.v,
        a_(n 1) X_1 + dots + a_(n n) X_n = b_n
      )
    $
    Let the coefficient matrix $A = (a_(i j))_(i,j) in M_(n times n)(F)$ be regarded as a linear map from $F^n$ to $F^n$.
    + If the system is homogeneous, i.e., $b_1 = dots = b_n = 0$, then its solution set is $ker A$. In particular, the system has a nontrivial solution if and only if $det A = 0$.
    + When $(b_1, ..., b_n) in F^n$ is given, the system either has no solution, or its solution set is of the form
      $
        (x_1, ..., x_n) + ker A,
      $
      where $(x_1, ..., x_n) in F^n$ is any particular solution.
    + If $det A in F^times$, then for any $(b_1, ..., b_n) in F^n$, the system has a unique solution $(x_1, ..., x_n)$, where
      $
        x_j = (det mat(
          a_(1 1), dots, b_1, dots, a_(1 n);
          a_(2 1), dots, b_2, dots, a_(2 n);
          dots.v, , dots.v, , dots.v;
          a_(n 1), dots, b_n, dots, a_(n n)
        )) / (det mat(
          a_(1 1), dots, a_(1 j), dots, a_(1 n);
          a_(2 1), dots, a_(2 j), dots, a_(2 n);
          dots.v, , dots.v, , dots.v;
          a_(n 1), dots, a_(n j), dots, a_(n n)
        )), quad j = 1, ..., n,
      $
      where in the numerator, the $j$-th column of $A$ is replaced by the column vector $(b_1, ..., b_n)^T$.
  ]

  #remark[
    Although Cramer's rule provides an exact solution to a system of linear equations when the coefficient matrix is invertible, in practice the computational cost of evaluating determinants increases rapidly with $n$. Even when these determinants can be computed efficiently, Cramer's rule remains numerically unstable: since it involves division, when the denominator $det A$ is close to zero, even a *small perturbation can cause large changes* in $x_1, ..., x_n$. Therefore, the value of Cramer's rule lies mainly in its theoretical significance.
  ]

  == Characteristic Polynomial and the Cayley Hamilton Theorem

  #proposition[
    Let $T in "End"(V)$ be invertible. Then there exists a nonzero polynomial $g in F[X]$ such that $T^(-1) = g(T)$.
  ]

  #definition(title: "Characteristic Polynomial")[
    Let $A in M_(n times n)(F)$. We embed $F$ as a subfield of the field of rational functions $F(X)$, thereby constructing the matrix $X dot 1_(n times n) - A in M_(n times n)(F(X))$. The characteristic polynomial of $A$ is defined as
    $
      "Char"_A := det(X dot 1_(n times n) - A).
    $
  ]

  Using Kronecker's delta notation
  $
    delta_(i,j) := cases(
      1 "if" i = j,
      0 "if" i != j
    )
  $
  the explicit formula for the determinant gives
  $
    det(X dot 1_(n times n) - A) = sum_(sigma in S_n) "sgn"(sigma) product_(i=1)^n (delta_(i,sigma(i)) X - a_(i,sigma(i))).
  $
  The highest degree term in $X$ comes from the contribution of $sigma = "id"$, yielding $X^n$, so $deg "Char"_A = n$.

  #proposition[
    Let $P in M_(n times n)(F)$ be invertible. Then $"Char"_(P^(-1) A P) = "Char"_A$.
  ]

  #proposition[
    Transposition does not change the characteristic polynomial: for all $A in M_(n times n)(F)$, we have $"Char"_A = "Char"_(A^t)$.
  ]

  #proposition[
    For any $A in M_(m times n)(F)$ and $B in M_(n times m)(F)$, the following equality holds in $F[X]$:
    $
      X^n "Char"_(A B) = X^m "Char"_(B A).
    $
  ]

  #theorem(title: "A. Cayley, W. R. Hamilton")[
    Let $n in bb(Z)_(>= 1)$. For all $A in M_(n times n)(F)$, we have
    $
      "Char"_A (A) = 0_(n times n).
    $
    Similarly, for any finite-dimensional $F$-vector space $V$ and $T in "End"(V)$, we have
    $
      "Char"_T (T) = 0_V.
    $
  ]

  #corollary[
    Let $n >= 1$. For any $A in M_(n times n)(F)$ and any invertible matrix $P in M_(n times n)(F)$, we have
    $
      (P^(-1) A P)^upright("v") = P^(-1) A^upright("v") P.
    $
  ]

  #lemma[
    Let $A = (a_(i j))_(i,j) in M_(n times n)(F)$, and let the characteristic polynomial $"Char"_A in F[X]$ be written as
    $
      X^n + c_(n-1) X^(n-1) + dots + c_0,
    $
    then
    $
      - c_(n-1) = sum_(i=1)^n a_(i i).
    $
  ]

  #definition(title: "Trace")[
    For a matrix $A = (a_(i j))_(i,j) in M_(n times n)(F)$, its trace is defined as
    $
      "Tr"(A) := sum_(i=1)^n a_(i i).
    $
  ]

  #definition(title: "Invariant Subspace")[
    Given a linear operator $T in "End"(V)$, if a subspace $U subset V$ satisfies $T(U) subset U$, then $U$ is called a $T$-invariant subspace of $V$, or simply an invariant subspace.
  ]

  #proposition[
    Let $V$ be a finite-dimensional vector space over $F$, $T in "End"(V)$, and $U$ a $T$-invariant subspace of $V$. Then the linear map $overline(T) in "End"(V\/U)$ satisfies
    $
      "Char"_(T|_U) dot "Char"_(overline(T)) = "Char"_T.
    $
  ]

  #lemma[
    Let $C in M_(n times n)(F)$ and $1 <= k <= n$. In the polynomial $det(X dot 1_(n times n) + C) in F[X]$, the coefficient of the $X^(n-k)$ term is
    $
      sum_(I subset {1, ..., n}, |I| = k) det C mat(I; I),
    $
    where $C mat(I; I)$ denotes the principal submatrix of $C$ indexed by $I$.
  ]

]
