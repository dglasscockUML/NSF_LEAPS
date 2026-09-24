import NSFLEAPS._08_Application.AP_Defs

/-!
# Main results in the Delta paper

Explain
-/

/- # Essential Definitions
For those definitions that are repeated, decide what to do ... -/

/- A set `A` of a semigroup `S` is thick if for all finite
subsets `F ⊆ S`, there exists `s ∈ S` such that `Fs ⊆ A` -/
-- def isThick
-- {S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
-- Prop :=
-- ∀ (F : Set S), F.Finite → ∃ s : S, (· * s) '' F ⊆ A

/- Denote by `U(1)` the unit circle in the complex plain as an abelian group.
A subset `A` of a semigroup `S`is Bohr_0 if there exists a
semigroup homomorphism `ϕ : S → U(1)^d` and an open set `U ⊆ U(1)^d`
containing `1` such that `A ⊇ ϕ ⁻¹ U`. -/
-- def isBohrZero
-- {S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
-- Prop := ∃ (d : ℕ) (φ : S → (Fin d → Circle))
--   (_ : ∀ (s t : S), φ (s * t) = (φ s) * (φ t)) (U : Set (Fin d → Circle))
--   (_ : IsOpen U) (_ : 1 ∈ U),
--   Set.preimage φ U ⊆ A

/-- Denote by `U(1)` the unit circle in the complex plain as an abelian group.
A subset `A` of a semigroup `S` is a set of Bohr recurrence if for all `d ∈ ℕ`,
all semigroup homomorphisms `φ : S → U(1)^d`, all open sets `U ⊆ U(1)^d`
containing `1`, there is `a ∈ A` such that `φ a ∈ U` -/
def isSetOfBohrRec
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∀ (d : ℕ) (φ : S → (Fin d → Circle))
  (_ : ∀ (s t : S), φ (s * t) = (φ s) * (φ t)) (U : Set (Fin d → Circle))
  (_ : IsOpen U) (_ : 1 ∈ U),
  ∃ (a : S) (_ : a ∈ A), φ a ∈ U

/- A set `A` of a semigroup `S` is a Delta set if there exist
`s_1, s_2, ... ∈ S` such that for all `1 ≤ i < j`, `s_j ∈ s_i A`. -/
-- def isDelta
-- {S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
-- Prop :=
-- ∃ (s : ℕ → S), ∀ (i j : ℕ), i < j → (s j) ∈ ((s i) * ·) '' A

/-- A set `A` of a semigroup `S` is Delta* if it has nonempty
intersection with all Delta subsets of `S` -/
def isDeltaStar
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∀ (B : Set S), isDelta B → (A ∩ B).Nonempty

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
      (isBohrZero B) ∧ (isThick H') ∧ (H' ⊆ H) ∧ (A ∩ H' = B ∩ H') := by sorry


/-- # Theorem B
    Let `S` be a commutative semigroup and `A ⊆ S`.
    If for all thick sets `H ⊆ S`, the set `A ∩ H` is a set of Bohr recurrence,
    then for all thick sets `H ⊆ S`, the set `A ∩ H` is a Delta set. -/
theorem DeltaTheoremB
{S : Type*} [CommSemigroup S] [Nonempty S] :
∀ (A : Set S),
  (∀ (H : Set S), isThick H → isSetOfBohrRec (A ∩ H)) →
    (∀ (H : Set S), isThick H → isDelta (A ∩ H)) := by sorry


/-- # Theorem C
    Let `S` be a semigroup. Family meet and family join, when restricted to
    the collection of families, are associative, commutative, and monotone
    operators that, together with the family dual, satisfy the DeMorgan-type
    laws `(F meet G)* = F* join G*` and `(F join G)* = F* meet G*`. -/
theorem DeltaTheoremC
{S : Type*} [Semigroup S] [Nonempty S] :
∀ (F G H I : Set (Set S)), isFamily F → isFamily G → isFamily H → isFamily I →
  -- closedness
  (isFamily (familyMeet F G)) ∧
  (isFamily (familyJoin F G)) ∧
  -- associativity
  familyMeet (familyMeet F G) H = familyMeet F (familyMeet F G) ∧
  familyJoin (familyJoin F G) H = familyJoin F (familyJoin F G) ∧
  -- commutativity
  familyMeet F G = familyMeet G F ∧
  familyJoin F G = familyJoin G F ∧
  -- monotonicity
  (F ⊆ H → G ⊆ I → familyMeet F G ⊆ familyMeet H I) ∧
  (F ⊆ H → G ⊆ I → familyJoin F G ⊆ familyJoin H I) ∧
  -- DeMorgan-type laws
  familyDual (familyMeet F G) = familyJoin (familyDual F) (familyDual G) ∧
  familyDual (familyJoin F G) = familyMeet (familyDual F) (familyDual G) := by sorry
