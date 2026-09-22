import Mathlib.Data.Nat.Basic

/-!
# Advertised statement

This is the small, trusted surface a mathematical reader should audit. Prefer
ordinary Mathlib definitions, document every new definition precisely, and
state every headline claim here without hiding hypotheses or weakening the
informal result.
-/

/-
For our Delta paper:

Imports
  Mathlib pieces

Defs
  Delta* set
  BohrZero set
  Thick set
  Set of Bohr recurrence
  Delta set
  Family dual
  Family meet
  Family join

Theorems
  # Theorem A
    Let $S$ be a commutative semigroup, and let $A \subseteq S$.
    If $A$ is a $\Delta^*$ set, then for all thick sets $H \subseteq S$,
    there exists a \bohrzero{} set $B \subseteq S$ and a thick set
    $H' \subseteq H$ such that $A \cap H' = B \cap H'$.

  # Theorem B
    Let $S$ be a commutative semigroup, and let $A \subseteq S$.
    If for all thick sets $H \subseteq S$, the set $A \cap H$ is
    a set of Bohr recurrence, then for all thick sets $H \subseteq S$,
    the set $A \cap H$ is a $\Delta$ set.

  # Theorem C
      Let $(S, \cdot)$ be a semigroup, and denote by $\families(S) \subseteq
      \powerset(\powerset(S))$ the collection of Furstenberg families of $S$.
      Family meet ($\classcapdual$) and family join ($\classcap$), restricted
      to $\families(S)^2$, are associative, commutative, and monotone operators
      that, together with the family dual ($\ast$), satisfy the De Morgan-type laws
      (\family \classcap \familytwo)^* = \family^* \classcapdual \familytwo^*
      \qquad \text{ and } \qquad (\family \classcapdual \familytwo)^* = \family^*
      \classcap \familytwo^*.
-/

/-- Replace this toy statement and docstring with the result being submitted. -/
theorem PalomarTemplate.main_result (n : ℕ) : n + n = 2 * n := by
  sorry
