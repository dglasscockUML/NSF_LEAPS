import NSFLEAPS._08_Application.AP_Main

/-!
# Main results in the Delta paper

Explain
-/

/- # Essential Definitions
This is the minimal set of definitions necessary to state the
main theorems as they appear in the introduction.  Those definitions
that are commented out already appear upstream. Those definitions
that are new are simplified versions of those that appear upstream
and are quick to check in order to verify the statement of the main
theorems. -/

/- A set `A` of a semigroup `S` is thick if for all finite
subsets `F ⊆ S`, there exists `s ∈ S` such that `Fs ⊆ A` -/
/-
_def isThick_ APPEARS ALREADY UPSTREAM
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∀ (F : Set S), F.Finite → ∃ s : S, (· * s) '' F ⊆ A
-/

/- Denote by `U(1)` the unit circle in the complex plain as an abelian group.
A subset `A` of a semigroup `S` is Bohr_0 if there exists a
semigroup homomorphism `ϕ : S → U(1)^d` and an open set `U ⊆ U(1)^d`
containing `1` such that `A ⊇ ϕ ⁻¹ U`. -/
/-
_def isBohrZero_ APPEARS ALREADY UPSTREAM
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop := ∃ (d : ℕ) (φ : S → (Fin d → Circle))
  (_ : ∀ (s t : S), φ (s * t) = (φ s) * (φ t)) (U : Set (Fin d → Circle))
  (_ : IsOpen U) (_ : 1 ∈ U),
  Set.preimage φ U ⊆ A
-/

/-- A subset `A` of a semigroup `S` is a set of Bohr recurrence if
it has non-empty intersection with all Bohr_0 subsets of `S` -/
def isSetOfBohrRec
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∀ (B : Set S), isBohrZero B → (A ∩ B).Nonempty

/- A set `A` of a semigroup `S` is a Delta set if there exist
`s_1, s_2, ... ∈ S` such that for all `1 ≤ i < j`, `s_j ∈ s_i A`. -/
/-
_def isDelta_ APPEARS ALREADY UPSTREAM
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∃ (s : ℕ → S), ∀ (i j : ℕ), i < j → (s j) ∈ ((s i) * ·) '' A
-/

/-- A set `A` of a semigroup `S` is Delta* if it has nonempty
intersection with all Delta subsets of `S` -/
def isDeltaStar
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∀ (B : Set S), isDelta B → (A ∩ B).Nonempty

/-- A set `A` of a semigroup `S` is central* if it has nonempty
intersection with all central subsets of `S` -/
def isCentralStar
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∀ (B : Set S), isCentral B → (A ∩ B).Nonempty

/-- A set `A` of a semigroup `S` is IP* if it has nonempty
intersection with all IP subsets of `S` -/
def isIPStar
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∀ (B : Set S), isIP B → (A ∩ B).Nonempty

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

/- # Theorems
These are the theorems from the introduction.  Their short proofs
are possible by importing the full development and putting together
or calling the more detailed theorems from the body of the paper. -/

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
by
  intro A hA H hH
  have AinDeltaStarFam : A ∈ (deltaFamily S)* := by sorry
  have HinSyndeticStarFam : H ∈ (syndeticFamily S)* := by sorry
  obtain ⟨Hpre,hHpre,B,hB,capCondition⟩ := commDeltaStarImpliesLocallyBohrZero AinDeltaStarFam H HinSyndeticStarFam
  let H' := Hpre ∩ H
  have hH' : isThick H' := by sorry
  have H'inH : H' ⊆ H := by sorry
  have AcapH'isBcapH' : A ∩ H' = B ∩ H' := by sorry
  use B, H', hB, hH', H'inH, AcapH'isBcapH'

/-- # Theorem B
    Let `S` be a commutative semigroup and `A ⊆ S`.
    If there exists a thick set `H ⊆ S` such that for all thick sets
    `H' ⊆ H`, the set `A ∩ H'` is a set of Bohr recurrence,
    then the set `A` is a Delta set. -/
theorem DeltaTheoremB
{S : Type*} [CommSemigroup S] [Nonempty S] :
∀ (A : Set S),
  (∃ (H : Set S), isThick H
  ∧ (∀ (H' : Set S), H' ⊆ H → isThick H' → isSetOfBohrRec (A ∩ H))) →
  isDelta A := by sorry


  -- B \subseteq S$ and a thick set $H' \subseteq H$ such that $A \cap H' = B \cap H'$.

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
