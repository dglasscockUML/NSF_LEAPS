import Mathlib.Algebra.Group.Semigroup
import Mathlib.Data.Set.Defs
import Mathlib.Analysis.Complex.Circle
import Mathlib.Combinatorics.Hindman
import Mathlib.Order.Filter.Ultrafilter.Defs

/-!
# Advertised statement

This module states the four main theorems of

  A. Blahodatna, L. Detmold, D. Glasscock and A. N. Le,
  "The local dynamical structure of Δ* sets via a new Furstenberg
  family algebra", arXiv:2610.10416,

together with the definitions they depend on. Each theorem carries the letter
it has in the introduction of that paper and is stated here without proof;
proofs are supplied in `Solution.lean` from the development in this repository.

## What is claimed

`DeltaTheoremA` and `DeltaTheoremB` are the main result and the dual
formulation the proof establishes: in an arbitrary commutative semigroup, a
Δ* set agrees with a Bohr_0 set on a thick subset of any prescribed thick set;
equivalently, a set that is a set of Bohr recurrence along every thick refinement
of some thick set is itself a Δ set. These generalize results of Bergelson,
Furstenberg, and Weiss and of Host and Kra from the integers to arbitrary commutative
semigroups. `DeltaTheoremC` gives a second instance of the same phenomenon: in
a countable commutative semigroup, a central* set agrees with an IP* set on a
thick subset of any prescribed thick set. `DeltaTheoremD` records the algebraic
properties of family meet, family join and the family dual on which the
reformulations rest.

## Conventions

Semigroups are discrete and are assumed to be non-empty.
Definitions are stated for a general `Semigroup`; commutativity and
countability are assumed only in the theorems that need them.

Bohr_0 sets are described via homomorphisms into `Fin d → Circle`, the
`d`-dimensional torus presented as a power of the unit circle in `ℂ`, rather
than as `ℝ^d / ℤ^d` as in the paper. No continuity is required of these
homomorphisms.

The multiplication on `Ultrafilter S` used by `isIP` and `isCentral` is
`Ultrafilter.mul`, defined in Mathlib.Combinatorics.Hindman and
introduced as a local instance below.
-/

/- # Definitions -/

namespace DeltaIntro

/-- A set `A` of a semigroup `S` is syndetic if there exists a finite set `F ⊆ S`
such that for all `s ∈ S`, there exists `f ∈ F` such that `f * s ∈ A`. -/
def isSyndetic
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∃ (F : Set S), F.Finite ∧ (∀ (s : S), ∃ f ∈ F, f * s ∈ A)

/-- A set `A` of a semigroup `S` is thick if it has nonempty intersection
with all syndetic subsets of `S` -/
def isThick
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∀ (B : Set S), isSyndetic B → (A ∩ B).Nonempty

/-- A set `A` of a semigroup `S` is a Delta set if there exist
`s_1, s_2, ... ∈ S` such that for all `1 ≤ i < j`, `s_j ∈ s_i A`. -/
def isDelta
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∃ (s : ℕ → S), ∀ (i j : ℕ), i < j → (s j) ∈ ((s i) * ·) '' A

/-- A set `A` of a semigroup `S` is Delta* if it has nonempty
intersection with all Delta subsets of `S` -/
def isDeltaStar
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∀ (B : Set S), isDelta B → (A ∩ B).Nonempty

/-- Denote by `U(1)` the unit circle in the complex plain as an abelian group.
A subset `A` of a semigroup `S` is Bohr_0 if there exists a
semigroup homomorphism `ϕ : S → U(1)^d` and an open set `U ⊆ U(1)^d`
containing `1` such that `A ⊇ ϕ ⁻¹ U`. -/
def isBohrZero
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop := ∃ (d : ℕ) (φ : S → (Fin d → Circle))
  (_ : ∀ (s t : S), φ (s * t) = (φ s) * (φ t)) (U : Set (Fin d → Circle))
  (_ : IsOpen U) (_ : 1 ∈ U),
  Set.preimage φ U ⊆ A

/-- A subset `A` of a semigroup `S` is a set of Bohr recurrence if
it has non-empty intersection with all Bohr_0 subsets of `S` -/
def isSetOfBohrRec
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∀ (B : Set S), isBohrZero B → (A ∩ B).Nonempty

attribute [local instance] Ultrafilter.mul

/-- A subset `A` of a semigroup `S` is an IP set if it is contained
in an idempotent ultrafilter. (See Hindman-Strauss Thm. 16.4.) -/
def isIP
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∃ (p : Ultrafilter S), (p * p = p) ∧ (A ∈ p)

/-- A set `A` of a semigroup `S` is IP* if it has nonempty
intersection with all IP subsets of `S` -/
def isIPStar
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∀ (B : Set S), isIP B → (A ∩ B).Nonempty

/-- A set `A` of a semigroup `S` is central if it is contained
in a minimal idempotent ultrafilter. (See Hindman-Strauss Def.
4.42 and Thm. 4.39.) -/
def isCentral
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∃ (p : Ultrafilter S),
  (p * p = p) ∧ (∀ (B : Set S), B ∈ p → isSyndetic {x : S | (x * ·) ⁻¹' B ∈ p}) ∧ (A ∈ p)

/-- A set `A` of a semigroup `S` is central* if it has nonempty
intersection with all central subsets of `S` -/
def isCentralStar
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∀ (B : Set S), isCentral B → (A ∩ B).Nonempty

/-- A collection `F` of subsets of `S` is a Furstenberg family if it is
upward closed: for all `A, B ⊆ S`, if `A ⊆ B` and `A ∈ F`, then `B ∈ F` -/
def isFamily
{S : Type*} [Nonempty S] (F : Set (Set S)) :
Prop :=
∀ (A B : Set S), A ⊆ B → A ∈ F → B ∈ F

/-- The family dual of a collection of subsets `F` of `S`
is the set `{ A ⊆ S : ∀ B ∈ F, A ∩ B ≠ ∅ }` -/
def familyDual
{S : Type*} [Nonempty S] (F : Set (Set S)) :
Set (Set S) :=
{A : Set S | ∀ B ∈ F, (A ∩ B).Nonempty}

/-- The family meet of two collections of subsets `F` and `G`
of `S` is the set `{ A ⊆ S : ∀ B ∈ familyDual F, A ∩ B ∈ G }` -/
def familyMeet
{S : Type*} [Nonempty S] (F G : Set (Set S)) :
Set (Set S) :=
{A : Set S | ∀ B ∈ familyDual F, A ∩ B ∈ G}

/-- The family join of two collections of subsets `F` and `G`
of `S` is the set `{ A ⊆ S : ∃ B ∈ F, ∃ C ∈ G, A = B ∩ C }` -/
def familyJoin
{S : Type*} [Nonempty S] (F G : Set (Set S)) :
Set (Set S) :=
{A : Set S | ∃ B ∈ F, ∃ C ∈ G, A = B ∩ C}

/- # Theorems -/

/-- # Theorem A
    Let `S` be a commutative semigroup and `A ⊆ S`.
    If `A` is a Delta* set, then for all thick sets `H ⊆ S`,
    there exists a Bohr_0 set `B ⊆ S` and a thick set `H' ⊆ S`,
    such that `A ∩ H' = B ∩ H'`. -/
theorem DeltaTheoremA
{S : Type*} [CommSemigroup S] [Nonempty S] :
∀ (A : Set S), isDeltaStar A →
  ∀ (H : Set S), isThick H →
    ∃ (B H' : Set S),
      (isBohrZero B) -- B is a Bohr_0 set
      ∧ (isThick H') -- H' is thick
      ∧ (H' ⊆ H) -- H' is contained in H
      ∧ (A ∩ H' = B ∩ H') :=-- A along H' is B along H'
by sorry


/-- # Theorem B
    Let `S` be a commutative semigroup and `A ⊆ S`.
    If there exists a thick set `H ⊆ S` such that for all thick sets
    `H' ⊆ H`, the set `A ∩ H'` is a set of Bohr recurrence,
    then the set `A` is a Delta set. -/
theorem DeltaTheoremB
{S : Type*} [CommSemigroup S] [Nonempty S] :
∀ (A : Set S),
  (∃ (H : Set S), isThick H
  ∧ (∀ (H' : Set S), H' ⊆ H → isThick H' → isSetOfBohrRec (A ∩ H'))) →
  isDelta A := by sorry


/-- # Theorem C
    Let `S` be a countable, commutative semigroup. If `A ⊆ S` is a `central*` set,
    then for all thick sets `H ⊆ S`, there exists an `IP*` set `B ⊆ S` and a thick
    set `H' ⊆ H` such that `A ∩ H' = B ∩ H'`. -/
theorem DeltaTheoremC
{S : Type*} [CommSemigroup S] [Nonempty S] [Countable S] :
∀ (A : Set S), isCentralStar A →
  ∀ (H : Set S), isThick H →
    ∃ (B H' : Set S),
      (isIPStar B) -- B is a IP*
      ∧ (isThick H') -- H' is thick
      ∧ (H' ⊆ H) -- H' is contained in H
      ∧ (A ∩ H' = B ∩ H') :=-- A along H' is B along H'
        by sorry

/-- # Theorem D
    Let `S` be a set. Family meet and family join, when restricted to
    the collection of families, are associative, commutative, and monotone
    operators that, together with the family dual, satisfy the DeMorgan-type
    laws `(F meet G)* = F* join G*` and `(F join G)* = F* meet G*`. -/
theorem DeltaTheoremD
{S : Type*} [Nonempty S] :
∀ (F G H I : Set (Set S)), isFamily F → isFamily G → isFamily H → isFamily I →
  -- closedness
  (isFamily (familyMeet F G)) ∧
  (isFamily (familyJoin F G)) ∧
  -- associativity
  familyMeet (familyMeet F G) H = familyMeet F (familyMeet G H) ∧
  familyJoin (familyJoin F G) H = familyJoin F (familyJoin G H) ∧
  -- commutativity
  familyMeet F G = familyMeet G F ∧
  familyJoin F G = familyJoin G F ∧
  -- monotonicity
  (F ⊆ H → G ⊆ I → familyMeet F G ⊆ familyMeet H I) ∧
  (F ⊆ H → G ⊆ I → familyJoin F G ⊆ familyJoin H I) ∧
  -- DeMorgan-type laws
  familyDual (familyMeet F G) = familyJoin (familyDual F) (familyDual G) ∧
  familyDual (familyJoin F G) = familyMeet (familyDual F) (familyDual G) := by sorry

end DeltaIntro
