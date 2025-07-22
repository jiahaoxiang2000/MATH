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

  #example(title: "Composition of Invertible Maps")[
    Let us show that the composition of two left (or right) invertible mappings is again left (or right) invertible.

    #proof[
      Let $f: A → B$ and $f': B → C$ be left invertible mappings. Then:
      - Let $g$ be left inverse of $f$, so $g compose f = "id"_A$
      - Let $g'$ be left inverse of $f'$, so $g' compose f' = "id"_B$
      - Then for composition $f' compose f$:
        $
          (g compose g') compose (f' compose f) = g compose (g' compose f') compose f = g compose f = "id"_A
        $
      - Therefore $g compose g'$ is a left inverse of $f' compose f$

      The proof for right invertible mappings is similar.
    ]
  ]

  #proposition(title: "Injection and Left Inverse Equivalence")[
    For a mapping $f : A → B$ where $A$ is non-empty, the following are equivalent:
    1. $f$ is injective
    2. $f$ has a left inverse
    3. $f$ satisfies the left cancellation law

    Similarly, where $A$ is non-empty, the following are equivalent:
    1. $f$ is surjective
    2. $f$ has a right inverse
    3. $f$ satisfies the right cancellation law

    #proof[
      First, we prove the equivalence for injective properties:

      (1) $⇒$ (2): Assume $f$ is injective.
      $∀ b ∈ "Im"(f)$, $∃ a ∈ A$, $f(a) = b$.
      Define $g: B → A$ by $g(b) = a$ if $b ∈ "Im"(f)$, and arbitrary otherwise.
      Then $g compose f = "id"_A$, so $g$ is left inverse.

      (2) $⇒$ (3): Assume $g compose f = "id"_A$. If $f g_1 = f g_2$, then $g(f g_1) = g(f g_2) ⟺ (g f) g_1 = (g f) g_2 ⟺ g_1 = g_2$

      (3) $⇒$ (1): Assume left cancellation, $f g_1 = f g_2 ⇒ g_1 = g_2$.
      If $∀ a_1, a_2 ∈ A, f(a_1) = f(a_2)$, then $f(a_1) = f(a_2) ⇒ a_1 = a_2$.

      The proof for surjective properties is similar.
    ]
  ] <prop:inject_left_inverse_equal>

  #definition(title: "Invertible Mapping")[
    A mapping $f$ is called invertible if it is both left and right invertible. In this case, there exists a unique mapping $f^(-1): B → A$ such that:
    $
      f^(-1) compose f = "id"_A quad "and" quad f compose f^(-1) = "id"_B
    $
    This mapping $f^(-1)$ is called the inverse of $f$.
  ]

  #proposition(title: "Properties of Invertible Mappings")[
    Let $f : A → B$ be an invertible mapping. Then:
    1. $f^(-1) : B → A$ is also invertible, and $(f^(-1))^(-1) = f$
    2. If $g : B → C$ is also invertible, then the composition $g compose f : A → C$ is invertible, and
      $
        (g compose f)^(-1) = f^(-1) compose g^(-1)
      $

    #proof[
      1. Since $f compose f^(-1) = "id"_B$ and $f^(-1) compose f = "id"_A$,
        $f$ is both left and right inverse of $f^(-1)$, so $(f^(-1))^(-1) = f$

      2. For composition:
        $
          (f^(-1) compose g^(-1)) compose (g compose f) = f^(-1) compose (g^(-1) compose g) compose f = f^(-1) compose f = "id"_A
        $
        Similarly, $(g compose f) compose (f^(-1) compose g^(-1)) = "id"_C$
    ]
  ]

  #proposition(title: "Bijection and Invertibility")[
    A mapping $f$ is bijective if and only if it is invertible, in which case its inverse mapping is precisely the previously defined $f^(-1)$.

    #proof[
      There are easy to prove by the proposition above.

      ($⇒$) If $f$ is bijective: Being injective implies $f$ has a left inverse, Being surjective implies $f$ has a right inverse, Therefore $f$ is invertible.

      ($⇐$) If $f$ is invertible: Having left inverse implies $f$ is injective, Having right inverse implies $f$ is surjective, Therefore $f$ is bijective.
    ]
  ]

  #definition(title: "Preimage")[
    For a mapping $f : A → B$ and $b ∈ B$, we denote:
    $
      f^(-1)(b) := f^(-1)({b}) = {a ∈ A : f(a) = b}
    $
  ]

  #remark[
    Note that this notation $f^(-1)(b)$ represents the preimage of $b$ under $f$, which exists even when $f$ is not invertible.
  ]

  ---- *check on here, next time keep do it*

  == Product of Sets & Disjoint Union

  #definition(title: "Generalized Cartesian Product")[
    Using the language of mappings, we define:
    $
      product_(i ∈ I) A_i := {f : I → union.big_(i ∈ I) A_i | ∀ i ∈ I, f(i) ∈ A_i}
    $

    Henceforth, we may write $f(i)$ as $a_i$, so elements of $product_(i ∈ I) A_i$ can be reasonably denoted as $(a_i)_(i ∈ I)$.

    For any $i ∈ I$, there is a mapping $p_i : product_(j ∈ I) A_j → A_i$ defined by $p_i((a_j)_(j ∈ I)) = a_i$, called the $i$-th projection.
  ]

  #remark[
    For easy to understand, The $product_(i ∈ I) A_i$ as the three domain space, the $(a_i)_(i∈I)$ as the one point in the three domain space, the $p_i$ as the projection from the three domain space to the one point.
  ]

  #definition(title: "Disjoint Union and Partition")[
    Let set $A$ be the union of a family of subsets $(A_i)_(i ∈ I)$, and suppose these subsets are pairwise disjoint, that is:
    $
      ∀ i,j ∈ I, i ≠ j ⇒ A_i ∩ A_j = ∅
    $
    In this case, we say $A$ is the disjoint union of $(A_i)_(i ∈ I)$, or $(A_i)_(i ∈ I)$ is a partition of $A$, written as:
    $
      A = union.sq.big_(i ∈ I) A_i
    $
  ]

  == Structure of Order

  #definition(title: "Binary Relation")[
    A binary relation between sets $A$ and $B$ is any subset of $A times B$. Let $R subset A times B$ be a binary relation. Then for all $a ∈ A$ and $b ∈ B$, we use the notation:
    $
      a R b "to represent" (a,b) ∈ R
    $
    For convenience, when $A = B$, we call this a binary relation on $A$.
  ]

  #definition(title: "Order Relations")[
    Let $≼$ be a binary relation on set $A$. We call $≼$ a preorder and $(A,≼)$ a preordered set when:
    - Reflexivity: For all $a ∈ A$, $a ≼ a$
    - Transitivity: For all $a,b,c ∈ A$, if $a ≼ b$ and $b ≼ c$, then $a ≼ c$

    If it also satisfies:
    - Antisymmetry: For all $a,b ∈ A$, if $a ≼ b$ and $b ≼ a$, then $a = b$

    then $≼$ is called a partial order and $(A,≼)$ is called a partially ordered set.

    A partially ordered set $(A,≼)$ is called a totally ordered set or chain if any two elements $a,b ∈ A$ are comparable, that is, either $a ≼ b$ or $b ≼ a$ holds.
  ]

  #definition(title: "Order-Preserving Maps")[
    Let $f : A → B$ be a mapping between preordered sets. Then:
    - $f$ is called order-preserving if:
      $
        a ≼ a' ⇒ f(a) ≼ f(a') "for all" a,a' ∈ A
      $

    - $f$ is called strictly order-preserving if:
      $
        a ≼ a' ⟺ f(a) ≼ f(a') "for all" a,a' ∈ A
      $
  ]

  #definition(title: "Maximal, Minimal Elements and Bounds")[
    Let $(A,≼)$ be a partially ordered set.
    - An element $a_("max") ∈ A$ is called a maximal element of $A$ if: there exists no $a ∈ A$ such that $a ≻ a_("max")$

    - An element $a_("min") ∈ A$ is called a minimal element of $A$ if: there exists no $a ∈ A$ such that $a ≺ a_("min")$

    Furthermore, let $A'$ be a subset of $A$.
    - An element $a ∈ A$ is called an upper bound of $A'$ in $A$ if: for all $a' ∈ A'$, $a' ≼ a$

    - An element $a ∈ A$ is called a lower bound of $A'$ in $A$ if: for all $a' ∈ A'$, $a' ≽ a$
  ]

  #remark[
    we can use the tree structure to understand the maximal, minimal elements and bounds. the partial order like the link between the nodes, the maximal, minimal elements like the root nodes and leaf nodes.
  ]

  #definition(title: "Well-Ordered Set")[
    A totally ordered set $(A,≼)$ is called a well-ordered set if every non-empty subset $S ⊆ A$ has a minimal element.
  ]

  == Equivalence Relations and Quotient Sets

  #definition(title: "Equivalence Relation")[
    A binary relation $∼$ on set $A$ is called an equivalence relation if it satisfies:
    - Reflexivity: For all $a ∈ A$, $a ∼ a$
    - Symmetry: For all $a,b ∈ A$, if $a ∼ b$ then $b ∼ a$
    - Transitivity: For all $a,b,c ∈ A$, if $a ∼ b$ and $b ∼ c$ then $a ∼ c$
  ]

  #definition(title: "Equivalence Class")[
    Let $∼$ be an equivalence relation on set $A$. A non-empty subset $C subset A$ is called an equivalence class if:
    - Elements in $C$ are mutually equivalent: for all $x,y ∈ C$, $x ∼ y$
    - $C$ is closed under $∼$: for all $x ∈ C$ and $y ∈ A$, if $x ∼ y$ then $y ∈ C$

    If $C$ is an equivalence class and $a ∈ C$, then $a$ is called a representative element of $C$.
  ]

  #proposition(title: "Partition by Equivalence Classes")[
    Let $∼$ be an equivalence relation on set $A$. Then $A$ is the disjoint union of all its equivalence classes.

    #proof[
      Let ${C_i}_(i ∈ I)$ be the collection of all equivalence classes of $A$.
      1. First, $A = union.big_(i ∈ I) C_i$ since every element belongs to its equivalence class
      2. For any distinct equivalence classes $C_i$ and $C_j$:
        If $x ∈ C_i ∩ C_j$ and $x≠ ∅$, then $C_i = C_j$, this is a contradiction, so $C_i ∩ C_j = ∅$.
      3. Therefore, $A = union.sq.big_(i ∈ I) C_i$
    ]
  ]

  #definition(title: "Quotient Set")[
    Let $∼$ be an equivalence relation on a non-empty set $A$. The quotient set is defined as the following subset of the power set $cal(P)(A)$:
    $
      A\/∼ := {C subset A : C "is an equivalence class with respect to" ∼}
    $
    The quotient set comes with a quotient map $q: A → A\/∼$ that maps each $a ∈ A$ to its unique equivalence class.
  ]

  #remark[
    here the find the quotient set, we can use the boolean function symmetric for the equivalence relation, then we only travel the quotient set, which can reduce the travel space.
  ]

  #proposition(title: "Universal Property of Quotient Maps")[
    Let $∼$ be an equivalence relation on set $A$ and $q: A → A\/∼$ be the corresponding quotient map. If a mapping $f: A → B$ satisfies:
    $
      a ∼ a' ⇒ f(a) = f(a')
    $
    then there exists a unique mapping $overline(f): (A\/∼) → B$ such that:
    $
      overline(f) compose q = f
    $

    #proof[
      First, $overline(f)$ is well-defined: for any $c ∈ A\/∼$. Then:
      $
        overline(f)(c) := f(a), a = q^(-1)(c)
      $
      The proof of uniqueness: Assume $overline(f)$ and $overline(f)'$, then $overline(f) compose q = overline(f') compose q$, the $q$ is surjective, so $overline(f) = overline(f')$.
    ]
  ] <prop:universal_property_of_quotient_maps>

  #proposition(title: "Canonical Factorization")[
    For any mapping $f : A → B$, define an equivalence relation $∼_f$ on $A$ by:
    $
      a ∼_f a' ⟺ f(a) = f(a')
    $
    Then by the previous proposition, there exists a bijection:
    $
      overline(f) : (A\/∼_f) arrow.r^(1:1) "im"(f)
    $

    #proof[
      Let $q: A → A\/∼_f$ be the quotient map. By the universal property:
      1. Well-defined: If $[a] = [a']$, then $a ∼_f a'$, so $f(a) = f(a')$

      2. Injective: If $overline(f)([a]) = overline(f)([a'])$, then $f(a) = f(a')$,
        so $a ∼_f a'$, thus $[a] = [a']$

      3. Surjective: For any $b ∈ "im"(f)$, there exists $a ∈ A$
        with $f(a) = b$, so $overline(f)([a]) = b$

      Therefore, $overline(f)$ is a bijection between $A\/∼_f$ and $"im"(f)$.
    ]
  ]

  == Positive Integer to Rational Number

  #definition(title: "Integers as Quotient Set")[
    The set of integers $bb(Z)$ is defined as the quotient set of $bb(Z)_(≥ 0)^2$ under $∼$. We temporarily denote the equivalence class containing $(m,n)$ in $bb(Z)_(≥ 0)^2$ as $[m,n]$.
  ]

  #remark[
    the $∼$ relation is defined as $(m,n)∼(m',n')⟺ m+n'=m'+n ⟺ m-n=m'-n'$.
  ]

  #definition(title: "Operations on Integer Equivalence Classes")[
    For any elements $[m,n]$ and $[r,s]$ in $bb(Z)$, define:
    $
      [m,n] + [r,s] & := [m+r, n+s]         \
      [m,n] · [r,s] & := [m r+n s, n r+m s]
    $
    By convention, multiplication $x · y$ is often written simply as $x y$.
  ]

  #definition(title: "Total Order on Integers")[
    Define a total order $≤$ on $bb(Z)$ by:
    $
      x ≤ y ⟺ y-x ∈ bb(Z)_(≥ 0)
    $
  ]

  #definition(title: "Rational Numbers")[
    Define the set of rational numbers $bb(Q)$ as the quotient set of $bb(Z) times (bb(Z) without {0})$ under the equivalence relation:
    $
      (r,s) ∼ (r',s') ⟺ r s' = r' s
    $
    We temporarily denote the equivalence class containing $(r,s)$ as $[r,s]$. Through the mapping $x ↦ [x,1]$, we view $bb(Z)$ as a subset of $bb(Q)$.
  ]

  #definition(title: "Total Order and Absolute Value on ℚ")[
    Define a total order on $bb(Q)$ by:
    $
      [r,s] ≥ 0 & ⟺ r s ≥ 0 \
          x ≥ y & ⟺ x-y ≥ 0
    $

    For any $x ∈ bb(Q)$, its absolute value $|x|$ is defined as:
    $
      |x| = cases(
        x & "if" x ≥ 0,
        -x & "if" x < 0
      )
    $
  ]

  #proposition(title: "Multiplicative Inverses in ℚ")[
    Let $bb(Q)^times := bb(Q) without {0}$. For any $x ∈ bb(Q)^times$, there exists a unique $x^(-1) ∈ bb(Q)^times$ such that $x x^(-1) = 1$.

    #proof[
      For $x = [r,s] ∈ bb(Q)^times$, define $x^(-1) = [s,r]$ when $r > 0$ and $x^(-1) = [-s,-r]$ when $r < 0$.
      Then $x x^(-1) = 1$ and the uniqueness, here have the $x',x''$, then $x' x = 1 = x'' x$, the $x$ have the right inverse, so $x' = x''$.
    ]
  ]

  == Arithmetical

  #definition(title: "Integer Multiples and Divisibility")[
    For any $x ∈ bb(Z)$, define:
    $
      x bb(Z) := {x d : d ∈ bb(Z)}
    $
    which consists of all multiples of $x$.

    For $x,y ∈ bb(Z)$:
    - We say $x$ divides $y$, written $x|y$, if $y ∈ x bb(Z)$
    - Otherwise, we write $x ∤ y$
    - When $x|y$, we call $x$ a factor or divisor of $y$
  ]

  #proposition(title: "Division Algorithm")[
    For any integers $a,d ∈ bb(Z)$ where $d ≠ 0$, there exist unique integers $q,r ∈ bb(Z)$ such that:
    $
      a & = d q + r \
      0 & ≤ r < |d|
    $

    #proof[
      *Existence:* $∀ a,b,$ $∃ q∈ bb(Z)$, let exist $r = a - d q$ (here can use the modular equivalence relation), and $0≤ r<|d|$.

      *Uniqueness:*
      Suppose $a = d q_1 + r_1 = d q_2 + r_2$ with $0 ≤ r_1,r_2 < |d|$
      - Then $d(q_1 - q_2) = r_2 - r_1$
      - $|r_2 - r_1| < |d|$
      - Therefore $q_1 = q_2$ and $r_1 = r_2$
    ]
  ]

  #lemma(title: "Generator of Integer Ideals")[
    Let $I$ be a non-empty subset of $bb(Z)$ satisfying:
    1. If $x,y ∈ I$, then $x + y ∈ I$
    2. If $a ∈ bb(Z)$ and $x ∈ I$, then $a x ∈ I$

    Then there exists a unique $g ∈ bb(Z)_(≥ 0)$ such that $I = g bb(Z)$.

    #proof[
      If $I = {0}$, take $g = 0$. Otherwise, let $g$ be the smallest positive element in $I$.

      For any $x ∈ I$, by division algorithm:
      $
        x = g q + r "where" 0 ≤ r < g
      $

      Then $r = x - g q ∈ I$ by properties of $I$. By minimality of $g$, we must have $r = 0$.
      Therefore $x ∈ g bb(Z)$, so $I ⊆ g bb(Z)$.

      Since $g ∈ I$, we have $g bb(Z) ⊆ I$. Thus $I = g bb(Z)$.

      Uniqueness follows from the fact that $g$ must be the smallest positive element in $I$.
    ]
  ]

  #definition(title: "Greatest Common Divisor")[
    For any integers $a,b ∈ bb(Z)$, the greatest common divisor of $a$ and $b$, denoted $gcd(a, b)$, is the unique positive integer $d$ such that:
    - $d | a$ and $d | b$
    - For any $d' ∈ bb(Z)$, if $d' | a$ and $d' | b$, then $d' | d$
  ] <def:greatest_common_divisor>

  #proposition(title: "Bézout's Identity")[
    For integers $x_1,…,x_n$:
    $
      bb(Z) x_1 + ⋯ + bb(Z) x_n = gcd(x_1, …, x_n) bb(Z)
    $

    Consequently, $x_1,…,x_n$ are coprime if and only if there exist $a_1,…,a_n ∈ bb(Z)$ such that:
    $
      a_1 x_1 + ⋯ + a_n x_n = 1
    $

    #proof[
      We proceed by induction on $n$.

      For $n=2$: Let $d = gcd(x_1, x_2)$. By Euclidean algorithm, there exist $a_1,a_2 ∈ bb(Z)$ such that:
      $
        d = a_1 x_1 + a_2 x_2 ∈ bb(Z) x_1 + bb(Z) x_2
      $
      Therefore $d bb(Z) ⊆ bb(Z) x_1 + bb(Z) x_2$.

      Conversely, since $d|x_1$ and $d|x_2$, we have $bb(Z) x_1 + bb(Z) x_2 ⊆ d bb(Z)$.

      For $n > 2$: Let $g = gcd(x_1, …, x_(n-1))$. By induction:
      $
        bb(Z) x_1 + ⋯ + bb(Z) x_(n-1) = g bb(Z)
      $
      Then:
      $
        bb(Z) x_1 + ⋯ + bb(Z) x_n = g bb(Z) + bb(Z) x_n = gcd(g, x_n) bb(Z) = gcd(x_1, …, x_n) bb(Z)
      $

      The corollary follows directly since $gcd(x_1, …, x_n) = 1$ if and only if they are coprime.
    ]
  ] <prop:bezouts_identity>

  #definition(title: "Prime Numbers")[
    Let $p ∈ bb(Z) without {0,±1}$. We say $p$ is a prime element if its only divisors are $±1$ and $±p$.
    A positive prime element is called a prime number.
  ]

  #proposition(title: "Euclid's Lemma")[
    Let $p$ be a prime element. If $a,b ∈ bb(Z)$ such that $p|a b$, then either $p|a$ or $p|b$.

    #proof[
      If $p ∤ a$, then $gcd(p, a) = 1$ since $p$ is prime.
      By the previous proposition, there exist $x,y ∈ bb(Z)$ such that:
      $
        p x + a y = 1
      $
      Multiply both sides by $b$:
      $
        p b x + a b y = b
      $
      Since $p|a b$, $p b x + a b y ∈ p bb(Z)$, so $p|b$.
    ]
  ] <prop:euclids_lemma>

  #theorem(title: "Fundamental Theorem of Arithmetic")[
    Every non-zero integer $n ∈ bb(Z)$ has a prime factorization:
    $
      n = ± p_1^(a_1) ⋯ p_r^(a_r)
    $
    where $r ∈ bb(Z)_(≥ 0)$ (with the convention that the right side equals $±1$ when $r=0$), $p_1,…,p_r$ are distinct prime numbers, $a_1,…,a_r ∈ bb(Z)_(≥ 1)$, and this factorization is unique up to ordering.

    #proof[
      *Existence:* By induction on $|n|$
      - Base case: When $|n|=1$, take $r=0$
      - For $|n|>1$: Let $p$ be the smallest prime divisor of $n$
      - Then $n = p m$ where $|m| < |n|$
      - By induction, $m$ has prime factorization
      - Combine $p$ with $m$'s factorization

      *Uniqueness:* Suppose we have two factorizations:
      $
        p_1^(a_1) ⋯ p_r^(a_r) = q_1^(b_1) ⋯ q_s^(b_s)
      $
      - By Euclid's lemma, $p_1$ divides some $q_i$
      - Since both are prime, $p_1 = q_i$
      - Cancel and continue by induction
      - Therefore $r=s$ and factorizations are same up to ordering
    ]
  ]

  #remark[
    For a prime number $p$, we use the notation $p^a ∥ n$ to indicate that $p^a|n$ but $p^(a+1) ∤ n$ (i.e., $p^a$ is the exact power of $p$ dividing $n$).
  ]

  #corollary[
    Consider integers $n = ± product_(i=1)^r p_i^(a_i)$ and $m = ± product_(i=1)^r p_i^(b_i)$, where $p_1,…,p_r$ are distinct primes and $a_i,b_i ∈ bb(Z)_(≥ 0)$. Then:
    $
      gcd(n, m) = product_(i=1)^r p_i^(min{a_i,b_i}), quad "lcm"(n,m) = product_(i=1)^r p_i^(max{a_i,b_i})
    $
    Similar results hold for GCD and LCM of any number of positive integers.
  ]

  #theorem(title: "Euclid")[
    There are infinitely many prime numbers.

    #proof[
      Let $p_1,…,p_n$ be any finite collection of primes.
      Consider $N = p_1 ⋯ p_n + 1$.
      Any prime factor $p$ of $N$ must be different from all $p_i$ (since dividing $N$ by any $p_i$ leaves remainder 1).
      Therefore, no finite collection can contain all primes.
    ]
  ] <thm:euclid>

  == Congruence Relation

  #definition(title: "Congruence Relation")[
    Let $N ∈ bb(Z)$. Two integers $a,b ∈ bb(Z)$ are called congruent modulo $N$ if $N|(a-b)$. This relation is written as:
    $
      a ≡ b (mod N)
    $
  ]

  #definition(title: "Congruence Classes")[
    For a fixed $N ∈ bb(Z)$, we denote the quotient set of $bb(Z)$ under the equivalence relation modulo $N$ as $bb(Z)\/N bb(Z)$, or abbreviated as $bb(Z)\/N$. The equivalence classes are called congruence classes modulo $N$.
  ]

  #proposition(title: "Multiplicative Inverses Modulo N")[
    Let $N ∈ bb(Z)_(≥ 1)$. For any $x ∈ bb(Z)$:
    $
      (∃ y ∈ bb(Z), x y ≡ 1 (mod N)) ⟺ gcd(N, x) = 1
    $

    #proof[
      ($⇒$) If $x y ≡ 1 (mod N)$, then $x y = k N + 1$ for some $k ∈ bb(Z)$
      Therefore $x y - k N = 1$, showing $gcd(N, x) = 1$ by Bézout's identity.

      ($⇐$) If $gcd(N, x) = 1$, then by Bézout's identity:
      $∃ y,k ∈ bb(Z)$ such that $x y + k N = 1$
      Therefore $x y ≡ 1 (mod N)$
    ]
  ] <prop:multiplicative_inverses_modulo_n>

  #theorem(title: "Fermat's Little Theorem")[
    Let $p$ be a prime number. Then for all $x ∈ bb(Z)$:
    $
      gcd(p, x) = 1 ⇒ x^(p-1) ≡ 1 (mod p)
    $

    Consequently, for all $x ∈ bb(Z)$:
    $
      x^p ≡ x (mod p)
    $

    #proof[
      Consider the sequence $x, 2x, …, (p-1)x (mod p)$.
      When $gcd(p, x) = 1$, then by the previous proposition, $∃ y, x y ≡ 1 (mod p)$, then $x y, 2x y, …, (p-1)x y (mod p)$, these are all distinct and nonzero modulo $p$, thus they also mean for the $x, 2x, …, (p-1)x (mod p)$.
      Their product is congruent to $(p-1)! · x^(p-1)$.
      Therefore $(p-1)! · x^(p-1) ≡ (p-1)! (mod p)$.
      Since $gcd(p, (p-1)!) = 1$, we can cancel to get $x^(p-1) ≡ 1 (mod p)$ by the previous proposition to reduce the $(p-1)!$.
    ]
  ]

  #definition(title: "Euler's Totient Function")[
    For $n ∈ bb(Z)_(≥ 1)$, define $φ(n)$ as the number of positive integers not exceeding $n$ that are coprime to $n$.
  ]

  == Radix

  #definition(title: "Equipotent Sets")[
    Two sets $A$ and $B$ are called equipotent (or have the same cardinality) if there exists a bijection $f : A arrow.r^(1:1) B$. We denote this as $|A| = |B|$.
  ]

  #definition(title: "Cardinality Comparison")[
    For sets $A$ and $B$, if there exists an injection $f : A ↪ B$, we write $|A| ≤ |B|$.
    We write $|A| < |B|$ when $|A| ≤ |B|$ but $|A| ≠ |B|$.
  ]

  #proposition(title: "Pigeonhole Principle")[
    Let $A$ and $B$ be finite sets with the same cardinality. Then any injection (or surjection) $f : A → B$ is automatically a bijection.
  ]

  #proposition(title: "Characterization of Infinite Sets")[
    A set $A$ is infinite if and only if there exists an injection $bb(Z)_(≥ 0) ↪ A$.

    #proof[
      ($⇒$) If $A$ is infinite, by axiom of choice we can construct an injection.

      ($⇐$) If such injection exists, then $|A| ≥ |bb(Z)_(≥ 0)|$, so $A$ must be infinite.
    ]
  ]

  #definition(title: "Countable Sets")[
    Let $ℵ_0 := |bb(Z)_(≥ 0)|$. A set $A$ is called countable (or enumerable) if $|A| = ℵ_0$.
    A set $A$ is called at most countable if $|A| ≤ ℵ_0$, meaning $A$ is either finite or countable.
  ]

  #proposition(title: "Countability Properties")[
    The union and product of finitely many countable sets are countable. That is, if $A_1,…,A_n$ are countable sets, then:
    1. $union.big_(i=1)^n A_i$ is countable
    2. $product_(i=1)^n A_i$ is countable

    #proof[
      For union: Let $f_i: bb(Z)_(≥ 0) → A_i$ be bijections.
      Define $f: bb(Z)_(≥ 0) → union.big_(i=1)^n A_i$ by:
      $
        f(k) = f_i(m) "where" k = i n + m, 0 ≤ m < n
      $
      This is surjective as each element appears in some $A_i$.

      For product: Let $g_i: bb(Z)_(≥ 0) → A_i$ be bijections.
      Use Cantor's pairing function to construct bijection:
      $
        g: bb(Z)_(≥ 0) → product_(i=1)^n A_i
      $
      given by $g(k) = (g_1(k_1),…,g_n(k_n))$ where $k_i$ are obtained from $k$ by repeated pairing.
    ]
  ]

  #theorem(title: "Cantor's Theorem")[
    For any set $A$:
    $
      2^(|A|) = |cal(P)(A)| > |A|
    $
    where $cal(P)(A)$ is the power set of $A$.

    #proof[
      First show $|cal(P)(A)| ≥ 2^(|A|)$ by constructing characteristic function.
      Then prove $|cal(P)(A)| > |A|$ by diagonal argument:
      Assume $f: A → cal(P)(A)$ is surjective.
      Consider $B = {x ∈ A : x ∉ f(x)}$.
      Then $B ∈ cal(P)(A)$ but $B ≠ f(a)$ for any $a ∈ A$.
    ]
  ]

]

