#import "command.typ": *

= Vector Spaces and Linear Mappings

  Broadly speaking, a vector space over a field $F$ refers to a set $V$ together with two operations:
  - Vector addition $+: V times V -> V$, denoted $(v_1, v_2) |-> v_1 + v_2$, satisfying associativity, commutativity, and the existence of inverses;
  - Scalar multiplication $dot: F times V -> V$, denoted $(t, v) |-> t dot v = t v$, satisfying associativity and distributivity over addition.

  If a mapping $T: V -> W$ between vector spaces satisfies the identities
  $
    T(v_1 + v_2) & = T(v_1) + T(v_2), \
          T(t v) & = t T(v),
  $
  then $T$ is called a linear mapping.

  == Introduction: Back to the System of Linear Equations

  $
      a_(11)X_1 + dots.c + a_(1n)X_n & = b_1 \
      a_(21)X_1 + dots.c + a_(2n)X_n & = b_2 \
                                     & dots.v \
    a_(m 1)X_1 + dots.c + a_(m n)X_n & = b_m
  $ <eq:linear-system-2>

  #definition[
    Consider a system of $n$ linear equations over a field $F$ in the form above. If $b_1 = dots.c = b_m = 0$, then the system is called homogeneous.
  ]

  Given $n,m in bb(Z)_(>=1)$ and a family of coefficients $(a_(i j))_(1 <= i <= m, 1 <= j <= n)$ where $a_(i j) in F$, define the mapping
  $
           T: F^n & -> F^m \
    (x_j)_(j=1)^n & |-> (sum_(j=1)^n a_(1j)x_j, ..., sum_(j=1)^n a_(m j)x_j).
  $

  #definition[
    Let $T: F^n -> F^m$ correspond to a homogeneous system of linear equations as described above. If $v_1, ..., v_h in F^n$ are all solutions of the system, and every solution $x in F^n$ can be uniquely expressed through addition and scalar multiplication as
    $ x = sum_(i=1)^h t_i v_i, quad t_1, ..., t_h in F, $
    where the tuple $(t_1, ..., t_h)$ is uniquely determined by $x$, then $v_1, ..., v_h$ is called a fundamental system of solutions for the homogeneous system.
  ]

  #proposition[
    Consider a homogeneous system of $n$ linear equations in the form above, where $bold(b) = 0$. If the reduced row echelon matrix obtained by elimination has $r$ pivot elements, then the corresponding homogeneous system has a fundamental system of solutions $v_1, ..., v_(n-r)$.
  ]

  == Vector Spaces

  #definition[
    A vector space over a field $F$, also called an $F$-vector space, is a tuple $(V, +, dot, 0_V)$ where $V$ is a set, $0_V in V$, and operations $+: V times V -> V$ and $dot: F times V -> V$ are written as $(u,v) |-> u + v$ and $(t,v) |-> t dot v$ respectively, satisfying the following conditions:

    1. Addition satisfies:
    - Associativity: $(u + v) + w = u + (v + w)$;
    - Identity element: $v + 0_V = v = 0_V + v$;
    - Commutativity: $u + v = v + u$;
    - Additive inverse: For every $v$, there exists $-v$ such that $v + (-v) = 0_V$.

    2. Scalar multiplication, often written as $t v$ instead of $t dot v$, satisfies:
    - Associativity: $s dot (t dot v) = (s t) dot v$;
    - Identity property: $1 dot v = v$, where $1$ is the multiplicative identity in $F$.

    3. Scalar multiplication distributes over addition:
    - First distributive property: $(s + t) dot v = s dot v + t dot v$;
    - Second distributive property: $s dot (u + v) = s dot u + s dot v$.

    Where $u, v, w$ (or $s, t$) represent arbitrary elements of $V$ (or $F$). When there is no risk of confusion, we denote $0_V$ simply as $0$, write $u + (-v)$ as $u - v$, and refer to the structure $(V, +, dot, 0)$ simply as $V$.
  ]

  #definition[
    Let $V$ be an $F$-vector space. If a subset $V_0$ of $V$ contains $0$ and is closed under addition and scalar multiplication, then $(V_0, +, dot, 0)$ is also an $F$-vector space, called a subspace of $V$.
  ]

  == Matrix & Calculate

  #definition[
    Let $m,n in bb(Z)_(>=1)$. An $m times n$ matrix over a field $F$ is a rectangular array
    $
      A = (a_(i j))_(1 <= i <= m, 1 <= j <= n) = mat(
        a_(11), dots.c, a_(1n);
        dots.v, dots.down, dots.v;
        a_(m 1), dots.c, a_(m n)
      ) = mat(dots.c, dots.c, a_(i j), dots.c, dots.c)
    $

    where $a_(i j) in F$ is called the $(i,j)$-entry or $(i,j)$-element of matrix $A$, with $i$ indicating the row and $j$ indicating the column. An $n times n$ matrix is called a square matrix of order $n$.

    We denote the set of all $m times n$ matrices over $F$ by $M_(m times n)(F)$.
  ]

  #proposition[
    The set $M_(m times n)(F)$ equipped with standard addition and scalar multiplication forms an $F$-vector space. The zero element is the zero matrix, and the additive inverse of a matrix $A = (a_(i j))_(i,j)$ is $-A = (-a_(i j))_(i,j)$.
  ]

  #definition(title: "Matrix Multiplication")[
    Matrix multiplication is a mapping defined as:
    $
      M_(m times n)(F) times M_(n times r)(F) & -> M_(m times r)(F) \
                                       (A, B) & |-> A B
    $

    If $A = (a_(i j))_(1 <= i <= m, 1 <= j <= n)$ and $B = (b_(j k))_(1 <= j <= n, 1 <= k <= r)$, then $A B = (c_(i k))_(1 <= i <= m, 1 <= k <= r)$, where:
    $ c_(i k) := sum_(j=1)^n a_(i j) b_(j k) = mat(a_(i 1), dots.c, a_(i n)) mat(b_(1k); dots.v; b_(n k)) $

    This represents the dot product of the $i$th row of $A$ with the $k$th column of $B$.
  ]

  #proposition[
    Matrix multiplication satisfies the following properties:
    - Associativity: $(A B) C = A (B C)$;
    - Distributivity: $A (B + C) = A B + A C$ and $(B + C) A = B A + C A$;
    - Linearity: $A (t B) = t (A B) = (t A) B$;

    where $t in F$ and matrices $A, B, C$ are arbitrary, provided their dimensions make these operations valid.
  ]

  == Bases & Dimensions

  #definition[
    Let $S$ be a subset of an $F$-vector space $V$.
    - If $angle.l S angle.r = V$, then $S$ is said to generate $V$, or $S$ is called a generating set of $V$.
    - A linear relation in $S$ is an equation of the form
      $ sum_(s in S) a_s s = 0 $
      This relation is called trivial if all coefficients $a_s$ are zero; otherwise, it is non-trivial. The set $S$ is linearly dependent if there exists a non-trivial linear relation among its elements; otherwise, $S$ is linearly independent.
    - If $S$ is a linearly independent generating set, then $S$ is called a basis of $V$.
  ]

  #lemma[
    For any subset $S$ of an $F$-vector space $V$, the following statements are equivalent:
    1. $S$ is a minimal generating set.
    2. $S$ is a basis.
    3. $S$ is a maximal linearly independent subset.
  ]

  #proof[
    Let's prove the equivalence by showing $(1) => (2)$, $(2) => (3)$, and $(3) => (1)$.

    $(1) => (2)$: If $S$ is a minimal generating set, then $angle.l S angle.r = V$. Suppose $S$ is not linearly independent. Then there exists some $s_0 in S$ that can be expressed as a linear combination of other elements in $S$. But this means $S without {s_0}$ still generates $V$, contradicting the minimality of $S$. Therefore, $S$ must be linearly independent, making it a basis.

    $(2) => (3)$: Let $S$ be a basis. Then $S$ is linearly independent and $angle.l S angle.r = V$. To show that $S$ is maximal, suppose we add any vector $v in.not S$ to form $S' = S union {v}$. Since $angle.l S angle.r = V$, we have $v in angle.l S angle.r$, meaning $v$ can be written as a linear combination of elements in $S$. Therefore, $S'$ must be linearly dependent, proving that $S$ is a maximal linearly independent set.

    $(3) => (1)$: Let $S$ be a maximal linearly independent set. If $angle.l S angle.r != V$, then there exists some $v in V without angle.l S angle.r$. The set $S union {v}$ would still be linearly independent, contradicting the maximality of $S$. Therefore $angle.l S angle.r = V$. Now suppose $S$ is not minimal. Then there exists a proper subset $S' subset S$ with $angle.l S' angle.r = V$. But this means some element in $S without S'$ can be expressed as a linear combination of elements in $S'$, making $S$ linearly dependent, which is a contradiction. Thus, $S$ is a minimal generating set.
  ]

  #proposition[
    Consider a family of $F$-vector spaces $V_i$, each with a given basis $B_i$, where $i$ ranges over a given index set $I$.
    Embed each $V_i$ as a subspace of the direct sum $plus.circle_(j in I) V_j$.
    Correspondingly, view each $B_i$ as a subset of $plus.circle_(j in I) V_j$.
    These subsets $B_i$ are pairwise disjoint, and $union.big_(i in I) B_i$ forms a basis for $plus.circle_(i in I) V_i$.
  ]

  #definition[
    Every $F$-vector space $V$ has a basis. In fact, any linearly independent subset of $V$ can be extended to a basis.

    Furthermore, all bases of $V$ have the same cardinality. This common cardinality is called the dimension of $V$, denoted by $dim_F V$ or simply $dim V$.
  ]

  #lemma[
    Let ${s_1,...,s_n}$ be a generating set for an $F$-vector space $V$. If $m > n$, then any collection of $m$ vectors $v_1,...,v_m in V$ is linearly dependent.
  ]

  == Linear Mappings

  #definition(title: "Linear Mapping")[
    Let $V$ and $W$ be $F$-vector spaces. A mapping $T: V -> W$ is called a linear mapping (also known as a linear transformation or linear operator) if it satisfies:
    $
      T(v_1 + v_2) & = T(v_1) + T(v_2), quad forall v_1, v_2 in V, \
            T(t v) & = t T(v), quad forall t in F, v in V.
    $
  ]

  #lemma[
    If $T: U -> V$ and $S: V -> W$ are linear mappings, then their composition $S compose T: U -> W$ is also a linear mapping.
  ]

  #proof[
    We need to verify that $S compose T$ satisfies the two defining properties of linear mappings:

    1. For any $u_1, u_2 in U$:
    $
      (S compose T)(u_1 + u_2) & = S(T(u_1 + u_2)) \
                               & = S(T(u_1) + T(u_2)) quad "(by linearity of" T")" \
                               & = S(T(u_1)) + S(T(u_2)) quad "(by linearity of" S")" \
                               & = (S compose T)(u_1) + (S compose T)(u_2)
    $

    2. For any $t in F$ and $u in U$:
    $
      (S compose T)(t u) & = S(T(t u)) \
                         & = S(t T(u)) quad "(by linearity of" T")" \
                         & = t S(T(u)) quad "(by linearity of" S")" \
                         & = t (S compose T)(u)
    $

    Therefore, $S compose T$ is a linear mapping.
  ]

  #definition[
    If a linear mapping $T: V -> W$ is both left and right invertible, it is called an invertible linear mapping or an isomorphism.

    In this case, there exists a unique linear mapping $T^(-1): W -> V$ such that $T^(-1) compose T = op("id")_V$ and $T compose T^(-1) = op("id")_W$. This mapping $T^(-1)$ is called the inverse of $T$; it is simultaneously the unique left inverse and the unique right inverse of $T$.
  ]

  #definition[
    Let $V$ and $W$ be $F$-vector spaces. Define $op("Hom")(V,W)$ as the set of all linear mappings from $V$ to $W$. Addition and scalar multiplication are defined by:
    $
      (T_1 + T_2)(v) & = T_1(v) + T_2(v) \
            (t T)(v) & = t dot T(v)
    $

    The zero element of $op("Hom")(V,W)$ is the zero mapping $0: V -> W$.
  ]

  == Linear Mappings to Matrix


  #definition[
    Let $V$ be an $F$-vector space. We denote $op("End")(V) := op("Hom")(V,V)$, whose elements are called endomorphisms of $V$.
  ]

  #corollary[
    Let $V$ be an $F$-vector space. Then $op("End")(V)$ forms a ring where addition is the addition of linear maps, and multiplication is the composition of linear maps $(S,T) |-> S T$. The zero element is the zero mapping, and the multiplicative identity is the identity mapping $op("id")_V$. Moreover, $op("End")(V)$ is the zero ring if and only if $V = {0}$.
  ]

  #theorem[
    Let $V$ and $W$ be finite-dimensional vector spaces with ordered bases $v_1,...,v_n$ and $w_1,...,w_m$ respectively, where $n,m in bb(Z)_(>=1)$. Then there exists a vector space isomorphism:
    $ cal(M): op("Hom")(V,W) arrow.l.r.double^(1:1) M_(m times n)(F) $
    mapping $T |-> (a_(i j))_(1 <= i <= m, 1 <= j <= n)$, where $(a_(i j))_(i,j) = cal(M)(T)$ is characterized by the property:
    $ T(v_j) = sum_(i=1)^m a_(i j) w_i, quad 1 <= j <= n. $
    Consequently, $dim op("Hom")(V,W) = dim V dot dim W$.
  ]

  #theorem[
    Let $U$, $V$, and $W$ be finite-dimensional vector spaces with ordered bases $u_1,...,u_r$, $v_1,...,v_n$, and $w_1,...,w_m$ respectively. The following diagram commutes:

    // Note: In Typst, we would typically use a different approach for commutative diagrams
    // This is a simplified representation
    $
          op("Hom")(V,W) times op("Hom")(U,V) & arrow("Map composition") op("Hom")(U,W) \
                                  M times M | & quad quad M \
      M_(m times n)(F) times M_(n times r)(F) & arrow("Matrix multiplication") M_(m times r)(F)
    $

    In other words, $M(S compose T) = M(S) dot M(T)$, where the left side represents composition of maps and the right side represents matrix multiplication.
  ]

  #definition[
    A matrix $A in M_(m times n)(F)$ is called left invertible (or right invertible) if there exists $B in M_(n times m)(F)$ such that $B A = 1_(n times n)$ (or $A B = 1_(m times m)$). Such a matrix $B$ is called a left inverse (or right inverse) of $A$.

    If $m = n$ and $A$ is both left and right invertible, then $A$ is called an invertible $n times n$ matrix. In this case, there exists a unique matrix $A^(-1) in M_(n times n)(F)$ such that $A^(-1) A = 1_(n times n) = A A^(-1)$. This matrix $A^(-1)$ serves simultaneously as both the unique left inverse and the unique right inverse of $A$.

    In other words, invertible matrices are precisely the invertible elements in the ring $M_(m times m)(F)$.
  ]

  == Transpose of a Matrix and Dual Spaces

  > NOTE: not clear understand Dual Space

  #definition[
    Let $R$ be a ring. For any $A = (a_(i j)) in M_(m times n)(R)$, the transpose of $A$, denoted $A^T$, is the $n times m$ matrix $(a_(j i))$. That is,
    $
      A = mat(
        a_(11), a_(12), dots.c, a_(1n);
        a_(21), a_(22), dots.c, a_(2n);
        dots.v, dots.v, dots.down, dots.v;
        a_(m 1), a_(m 2), dots.c, a_(m n)
      ) => A^T = mat(
        a_(11), a_(21), dots.c, a_(m 1);
        a_(12), a_(22), dots.c, a_(m 2);
        dots.v, dots.v, dots.down, dots.v;
        a_(1n), a_(2n), dots.c, a_(m n)
      )
    $
  ]

  #proposition[
    Let $A in M_(m times m)(F)$. Then $A$ is invertible if and only if $A^T$ is invertible. Moreover, in this case,
    $ (A^T)^(-1) = (A^(-1))^T. $
  ]

  #proof[
    Suppose $A$ is invertible, so $A^(-1) A = A A^(-1) = I$. Taking transposes, $(A^(-1))^T (A^T) = (A A^(-1))^T = I^T = I$, and $(A^T) (A^(-1))^T = (A^(-1) A)^T = I$. Thus, $A^T$ is invertible and $(A^T)^(-1) = (A^(-1))^T$.

    Conversely, if $A^T$ is invertible, the same argument applied to $A^T$ shows $A$ is invertible.
  ]

  #definition[
    Let $V$ be a vector space over a field $F$. The dual space of $V$, denoted $V^*$, is defined as
    $ V^* := op("Hom")(V, F), $
    the set of all linear functionals from $V$ to $F$.
  ]

  #definition[
    Let $T: V -> W$ be a linear map between vector spaces over $F$. The transpose (dual) map of $T$, denoted $T^T : W^* -> V^*$, is defined by
    $ T^T (lambda) = lambda compose T, quad forall lambda in W^*. $
    That is, for any $v in V$,
    $ (T^T (lambda))(v) = lambda(T(v)). $
  ]

  #proposition[
    Let $U, V, W$ be vector spaces over $F$, and let $T: U -> V$, $S: V -> W$ be linear maps. Then
    $ (S T)^T = T^T compose S^T in op("Hom")(W^*, U^*). $
  ]

  #proof[
    For any $lambda in W^*$ and $u in U$,
    $ ((S T)^T (lambda))(u) = lambda((S T)(u)) = lambda(S(T(u))) = (S^T (lambda))(T(u)) = (T^T (S^T (lambda)))(u). $
    Thus, $(S T)^T = T^T compose S^T$.
  ]

  #proposition[
    Let $V$ be a finite-dimensional vector space with basis $v_1, ..., v_n$. For each $1 <= i <= n$, define $v_i^* in V^*$ by
    $ v_i^* (sum_(j=1)^n x_j v_j) = x_i. $
    Then $v_1^*, ..., v_n^*$ form a basis of $V^*$, called the dual basis of $v_1, ..., v_n$.
  ]

  #proof[
    Each $v_i^*$ is linear, and for any $v_j$ we have $v_i^* (v_j) = delta_(i j)$. Any $f in V^*$ is determined by its values $f(v_j)$, so $f = sum_(i=1)^n f(v_i) v_i^*$. Thus, ${v_1^*, ..., v_n^*}$ is a basis for $V^*$.
  ]

  == Kernel, Image, and Gaussian Elimination


  #definition[
    Let $T: V -> W$ be a linear map between vector spaces. The *kernel* of $T$ is
    $ ker T := {v in V : T(v) = 0} = T^(-1)(0). $
    The *image* of $T$ is
    $ op("im") T := {w in W : exists v in V, T(v) = w}. $
  ]

  #proposition[
    Let $T: V -> W$ be a linear map. Then $ker T$ is a subspace of $V$, and $op("im") T$ is a subspace of $W$.
  ]

  #proof[
    For $ker T$:
    Let $u, v in ker T$ and $a, b in F$. Then $T(a u + b v) = a T(u) + b T(v) = a dot 0 + b dot 0 = 0$, so $a u + b v in ker T$. Thus, $ker T$ is a subspace of $V$.

    For $op("im") T$:
    Let $w_1, w_2 in op("im") T$, so $w_1 = T(v_1)$, $w_2 = T(v_2)$ for some $v_1, v_2 in V$. For $a, b in F$, $a w_1 + b w_2 = a T(v_1) + b T(v_2) = T(a v_1 + b v_2) in op("im") T$. Thus, $op("im") T$ is a subspace of $W$.
  ]

  #proposition[
    A linear map $T: V -> W$ is injective if and only if $ker T = {0}$.
  ]

  #theorem[
    Let $T: V -> W$ be a linear map between vector spaces, with $V$ finite-dimensional. Then
    $ dim V = dim (ker T) + dim (op("im") T). $
  ]

  #definition(title: "Rank")[
    Let $T: V -> W$ be a linear map between finite-dimensional vector spaces. The *rank* of $T$, denoted $op("rk")(T)$, is defined as
    $ op("rk")(T) := dim(op("im") T). $
    For a matrix $A in M_(m times n)(F)$, the rank $op("rk")(A)$ is defined as the rank of the associated linear map $T_A: F^n -> F^m$.
  ]

  #proposition[
    Let $A' in M_(m times n)(F)$ be the row echelon form of $A in M_(m times n)(F)$ obtained by elementary row operations. Then the rank of $A$, $op("rk")(A)$, equals the number $r$ of pivots (leading ones) in $A'$.
  ]

  #proof[
    Elementary row operations do not change the row space of $A$, so $op("rk")(A) = op("rk")(A')$. In row echelon form, the number of pivots equals the dimension of the row (or column) space, which is the rank.
  ]

  #proposition[
    Let $A in M_(m times m)(F)$. The following statements are equivalent:
    1. $A$ is invertible;
    2. For any column vector $v in F^m$, $A v = 0$ if and only if $v = 0$;
    3. $op("rk")(A) = m$;
    4. $A$ can be written as a product of elementary matrices.

    Therefore, $A in M_(m times m)(F)$ is invertible if and only if it is left invertible, if and only if it is right invertible.
  ]

  #proof[
    $(1) => (2)$: If $A$ is invertible and $A v = 0$, then $v = A^(-1) A v = A^(-1) 0 = 0$.

    $(2) => (3)$: If $A v = 0$ only for $v = 0$, the columns of $A$ are linearly independent, so $op("rk")(A) = m$.

    $(3) => (4)$: If $op("rk")(A) = m$, $A$ can be reduced to the identity matrix by elementary row operations, so $A$ is a product of elementary matrices.

    $(4) => (1)$: Elementary matrices are invertible, so their product $A$ is invertible.

    The equivalence of left and right invertibility for square matrices follows from these properties.
  ]

  == Change of Basis: Matrix Conjugation and Equivalence

  #lemma[
    The map $P_(bold(v))^(bold(v)'): F^n -> F^n$ defined by change of basis from $bold(v)$ to $bold(v)'$ is a vector space automorphism of $F^n$. Its inverse is $P_(bold(v)')^(bold(v))$.
  ]

  #proof[
    By definition, $P_(bold(v))^(bold(v)')$ is invertible, with $P_(bold(v)')^(bold(v))$ as its inverse, since changing from basis $bold(v)$ to $bold(v)'$ and then back recovers the original coordinates. Thus, $P_(bold(v))^(bold(v)')$ is an automorphism.
  ]

  #theorem[
    Let $V$ and $W$ be finite-dimensional vector spaces with ordered bases $bold(v), bold(v)'$ for $V$ and $bold(w), bold(w)'$ for $W$. For any $T in op("Hom")(V, W)$, we have
    $
      cal(M)_(bold(w)')^(bold(v)')(T) = P_(bold(w))^(bold(w)') cal(M)_(bold(w))^(bold(v))(T) P_(bold(v))^(bold(v)') = (P_(bold(w)')^(bold(w)))^(-1) cal(M)_(bold(w))^(bold(v))(T) P_(bold(v))^(bold(v)').
    $
  ]

  #definition(title: "Matrix Conjugation (Similarity)")[
    Let $bold(A), bold(B) in M_(n times n)(F)$. If there exists an invertible matrix $P in M_(n times n)(F)$ such that
    $ bold(B) = P^(-1) bold(A) P, $
    then $bold(A)$ and $bold(B)$ are called *conjugate* or *similar* matrices.
  ]

  #proposition[
    Conjugation is an equivalence relation on $M_(n times n)(F)$.
  ]

  #definition(title: "Matrix Equivalence")[
    Matrices $A, B in M_(m times n)(F)$ are called *equivalent* if there exist invertible matrices $Q in M_(m times m)(F)$ and $P in M_(n times n)(F)$ such that
    $ B = Q A P. $
  ]

  #proposition[
    Two matrices $A, B in M_(m times n)(F)$ are equivalent if and only if $op("rk")(A) = op("rk")(B)$.
  ]

  #theorem[
    For any matrix $A in M_(m times n)(F)$, the row rank of $A$ equals the column rank of $A$.
  ]

  #definition[
    A matrix $A in M_(m times n)(F)$ is called *full rank* if $op("rk")(A) = min{m, n}$.
  ]

  == Direct Sum Decomposition

  #definition[
    Let $V$ be a vector space over a field $F$, and let $(V_i)_(i in I)$ be a family of subspaces of $V$. The sum of these subspaces is defined as
    $ sum_(i in I) V_i := {sum_(i in I) v_i in V : v_i in V_i, "and only finitely many" v_i != 0}. $
    For finitely many subspaces, we write $V_1 + dots.c + V_n$ for their sum. By convention, the sum over the empty index set $I = emptyset$ is the zero subspace ${0}$.
  ]

  #proposition[
    Let $(V_i)_(i in I)$ be a family of subspaces of an $F$-vector space $V$, with $I != emptyset$. If for every $i in I$,
    $ V_i inter sum_(j != i) V_j = {0}, $
    then we denote $sum_(i in I) V_i$ by $plus.circle_(i in I) V_i$, called the (internal) *direct sum* of $(V_i)_(i in I)$, and each $V_i$ is called a *direct summand*.

    This condition holds if and only if the canonical map from the external direct sum $plus.circle_(i in I) V_i$ to $sum_(i in I) V_i$ is an isomorphism.
  ]

  #proposition[
    Let $V$ be a vector space over a field $F$, and $V_0 subset V$ any subspace. Then there exists a subspace $V_1 subset V$ such that
    $ V = V_0 plus.circle V_1. $
  ]

  #proof[
    Let ${v_1, ..., v_k}$ be a basis for $V_0$. Extend this to a basis ${v_1, ..., v_k, w_1, ..., w_m}$ for $V$. Let $V_1 = op("span"){w_1, ..., w_m}$. Then every $v in V$ can be uniquely written as $v = v_0 + v_1$ with $v_0 in V_0$, $v_1 in V_1$, so $V = V_0 plus.circle V_1$.
  ]

  == Block Matrix Operations

  #definition[
    Let $T: V -> W$ be a linear map, where $V = V_1 plus.circle dots.c plus.circle V_n$ and $W = W_1 plus.circle dots.c plus.circle W_m$ are direct sum decompositions. The matrix $A := M(T)$, with respect to these decompositions, can be partitioned into $m times n$ blocks as follows:
    $
      A = mat(
        A_(11), dots.c, A_(1n);
        dots.v, dots.down, dots.v;
        A_(m 1), dots.c, A_(m n)
      )
    $
    where $A_(i j) := M(T_(i j))$ is the matrix of the component map $T_(i j): V_j -> W_i$.

    A matrix $A$ with such a partition is called a *block matrix*, and each $A_(i j)$ is called its $(i,j)$-block.
  ]

  Let $V$ be a vector space over $F$ and $U$ a subspace. For any $v in V$, the equivalence class of $v$ modulo $U$ is denoted by
  $ v + U := {v + u : u in U}. $
  Such subsets are called *cosets* of $U$ in $V$, and $v$ is called a representative of the coset. We have $v + U = v' + U$ if and only if $v - v' in U$.

  == Quotient Spaces

  #definition(title: "Quotient Space")[
    Let $U$ be a subspace of an $F$-vector space $V$. Define the *quotient space*
    $ V\/U := {v + U : v in V} $
    as the set of all cosets of $U$ in $V$.

    On $V\/U$, define the following operations:
    - Addition: $(v_1 + U) + (v_2 + U) := (v_1 + v_2) + U$, for $v_1, v_2 in V$;
    - Scalar multiplication: $t(v + U) := (t v) + U$, for $t in F$, $v in V$;
    - Zero element: $0_(V\/U) := U = 0_V + U$ (the coset of $0$).

    With these operations, $(V\/U, +, dot, 0_(V\/U))$ is a vector space over $F$, called the *quotient space* of $V$ by $U$.
  ]

  #definition(title: "Cokernel")[
    Let $T: V -> W$ be a linear map. The *cokernel* of $T$ is defined as the quotient space of $W$ by the image of $T$:
    $ op("coker")(T) := W \/ op("im")(T). $
  ]

  #proposition[
    A linear map $T: V -> W$ is surjective if and only if $op("coker")(T) = {0}$.
  ]

  #proof[
    If $T$ is surjective, then $op("im")(T) = W$, so $W \/ op("im")(T) = W \/ W = {0}$.

    Conversely, if $op("coker")(T) = {0}$, then $W \/ op("im")(T) = {0}$, so $op("im")(T) = W$, i.e., $T$ is surjective.
  ]

  #proposition[
    Let $U$ be a subspace of a vector space $V$, and let $T: V -> W$ be a linear map.
    1. If $U subset ker(T)$, then there exists a unique linear map $overline(T): V\/U -> W$ such that the following diagram commutes:
      $
        V arrow.long_(T) W \
        q | quad overline(T) \
        V\/U
      $
      where $q: V -> V\/U$ is the quotient map. Explicitly, $overline(T)(v + U) = T(v)$.

    2. If $U = ker(T)$ and $W = op("im")(T)$, then $overline(T): V\/U -> W$ is an isomorphism of vector spaces.
  ]

  #proof[
    (1) If $U subset ker(T)$, then $T(v) = T(v')$ whenever $v - v' in U$, so $T$ is constant on cosets $v + U$. Thus, $overline(T)(v + U) := T(v)$ is well-defined and linear. Uniqueness follows since $q$ is surjective.

    (2) If $U = ker(T)$ and $W = op("im")(T)$, then $overline(T)$ is injective (since $ker(overline(T)) = {U}$) and surjective (since $T$ is surjective onto $W$), so it is an isomorphism.
  ]

  #proposition[
    Let $U$ be a subspace of $V$. Let $overline(V) := V\/U$, and let $q: V -> overline(V)$ be the quotient map. There is a bijection
    $ {W subset V : W "is a subspace", W supset U} <-> {overline(W) subset overline(V) : overline(W) "is a subspace"} $
    given by $W |-> overline(W) := q(W)$ and $overline(W) |-> W := q^(-1)(overline(W))$.

    This bijection has the following properties:
    - It is strictly order-preserving: $W_1 supset W_2$ if and only if $overline(W)_1 supset overline(W)_2$.
    - If $W$ corresponds to $overline(W)$, then there is a natural isomorphism
      $ V\/W tilde.equiv overline(V)\/overline(W), quad v + W |-> q(v) + overline(W). $
      If we write $overline(W) = W\/U$, this isomorphism can be viewed as
      $ V\/W tilde.equiv (V\/U)\/(W\/U). $
  ]

  #proposition[
    Let $V, W$ be subspaces of a vector space. Then there is a natural isomorphism
    $ V \/ (V inter W) tilde.equiv (V + W) \/ W $
    given by $v + (V inter W) |-> v + W$ for $v in V$.
  ]
