import NSFLEAPS._08_Application.AP_Main

/-!
# Main results in the Delta paper

This file contains the statements and proofs of the main results from the introduction
section of the paper

`The local dynamical structure of \Delta^* sets via a new Furstenberg family algebra`
by Angelina Blahodatna, Lauren Detmold, Daniel Glasscock, and Anh N. Le.

This file imports the entire project development, which rests on Mathlib only via
the imports in the IM_Main.lean file.

There are three sections below, each in a new namespace called DeltaIntro:
  · Essential definitions
  · Translation lemmas
  · Theorems

The _essential definitions_ section contains the definitions required to audit the
statements of the main theorems.  Some definitions (like isSyndetic) is exist both in
the development upstream and here in the namespace DeltaIntro.  Note that Lean searches
the namespace first, then the root, so that below ``isSyndetic'' refers to
DeltaIntro.isSyndetic, whereas _root_.isSyndetic refers to the version of
``isSyndetic'' appearing in the development.

The _translation lemmas_ section contains lemmas that show, where necessary that the
definitions appearing here match those upstream in the development.

The _theorems_ section contains statements and proofs of the theorems that appear
in the introduction of the paper.

-/

namespace DeltaIntro

/- # Essential Definitions -/

/-- A set `A` of a semigroup `S` is syndetic if there exists a finite set `F ⊆ S`
such that for all `s ∈ S`, there exists `f ∈ F` such that `f * s ∈ A`. -/
def isSyndetic
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∃ (F : Set S), F.Finite ∧ (∀ (s : S), ∃ f ∈ F, f * s ∈ A)

/-- A set `A` of a semigroup `S` is thick if for all finite
subsets `F ⊆ S`, there exists `s ∈ S` such that `Fs ⊆ A` -/
-- *
def isThick
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∀ (B : Set S), isSyndetic B → (A ∩ B).Nonempty

/-- A set `A` of a semigroup `S` is a Delta set if there exist
`s_1, s_2, ... ∈ S` such that for all `1 ≤ i < j`, `s_j ∈ s_i A`. -/
-- *
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
-- *
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

/-- A subset `A` of a semigroup `S` is an IP set if it is contained
in an idempotent ultrafilter. (See Hindman-Strauss Thm. 16.4.) -/
def isIP
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∃ (p : Ultrafilter S) (_ : p * p = p), A ∈ p

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
∃ (p : Ultrafilter S) (_ : p * p = p)
  (_ : ∀ (B : Set S), B ∈ p → isSyndetic {x : S | (x * ·) ⁻¹' B ∈ p}),
    A ∈ p

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

/- # Translation lemmas -/

/-- A subset of a semigroup `S` is thick according to `isThick` defined above
if and only if it is `isThick` as defined according to the development -/
lemma thickIsSame
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
isThick A ↔ _root_.isThick A := by
  have : isThick A ↔ A ∈ (syndeticFamily S)* := by rfl
  rw [dualSyndeticThick] at this
  rw [this]
  rfl

/-- A subset of a semigroup `S` is central according to `isCentral` defined above
if and only if it is `isCentral` as defined according to the development -/
lemma centralIsSame
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
isCentral A ↔ _root_.isCentral A := by
  have ultraURCondition (p : Ultrafilter S) :
    isUniformlyRecurrent (ultrafilterSystem S) p ↔
      ∀ (B : Set S), B ∈ p → isSyndetic {x : S | (x * ·) ⁻¹' B ∈ p} := by
        unfold isUniformlyRecurrent
        constructor
        · intro hUR C hC
          let Cnhd := {q : Ultrafilter S | C ∈ q}
          have : Cnhd ∈ nhds p := by
            apply (TopologicalSpace.IsTopologicalBasis.mem_nhds_iff ultrafilterBasis_is_basis).mpr
            use Cnhd
            refine ⟨?_,?_,?_⟩
            · unfold ultrafilterBasis
              use C
            · exact hC
            · trivial
          specialize hUR Cnhd this
          have : visitTimeSet (ultrafilterSystem S) p Cnhd =
            {x | (fun x_1 ↦ x * x_1) ⁻¹' C ∈ p} := by rfl
          rwa [this] at hUR
        · intro hUR U Unhds
          apply (TopologicalSpace.IsTopologicalBasis.mem_nhds_iff
            ultrafilterBasis_is_basis).mp at Unhds
          obtain ⟨V, ⟨C,VisClosC⟩, pInV, VinU⟩ := Unhds
          simp only at VisClosC
          rw [←VisClosC] at pInV
          specialize hUR C pInV
          have : visitTimeSet (ultrafilterSystem S) p V =
            {x | (fun x_1 ↦ x * x_1) ⁻¹' C ∈ p} := by
              rw [←VisClosC]
              rfl
          rw [←this] at hUR
          have visitContained : visitTimeSet (ultrafilterSystem S) p V ⊆
            visitTimeSet (ultrafilterSystem S) p U := visitTimesMono
              (ultrafilterSystem S) p VinU
          apply syndeticIsMonotone (hAB := visitContained)
          exact hUR
  constructor
  · intro hA
    obtain ⟨p, pIdemp, pPreUR, Ainp⟩ := hA
    rw [←ultraURCondition p] at pPreUR
    use p, (ultrafilterMinimalIffUnifRec p).mpr pPreUR
  · intro hA
    obtain ⟨p, pPreUR, pIdemp, Ainp⟩ := hA
    apply (ultrafilterMinimalIffUnifRec p).mp at pPreUR
    rw [ultraURCondition p] at pPreUR
    use p

/- # Theorems -/

/- # Theorem A : Proved after Theorem B.  See below. -/

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
  isDelta A := by
  rintro A ⟨H, hH, hAH⟩
  apply (thickIsSame H).mp at hH
  -- by Lemma 3.8, `A ∈ ⋃_{H ∈ T} ((T∩H)* ⋏ dcT_Bohr0)`
  have hA : A ∈ Family.iUnion (fun (t : (thickFamily S).sets) ↦
      (capFamily (thickFamily S) t)* ⋏ setOfBohrRecurrenceFamily S) :=
    (Set.ext_iff.mp (iUnionCapFamilyDualDescription (thickFamily S) (thickFamily S)
      (setOfBohrRecurrenceFamily S)) A).mpr
      ⟨H, hH, fun H' hH' hH'H ↦ hAH H' hH'H ((thickIsSame H').mpr hH')⟩
  -- the condition of Theorem 5.4 for `F := dcT_Bohr0` and `G := Δ`
  have hFG : ∀ h ∈ thickFamily S,
      ((capFamily (thickFamily S) h)* ⋏ setOfBohrRecurrenceFamily S).sets ∩
        {C : Set S | isURSet C} ⊆ ((capFamily (thickFamily S) h)* ⋏ deltaFamily S).sets := by
    rintro h hh B ⟨hB, hBUR⟩
    -- 1. `(T∩h)* ⋏ dcT_Bohr0 ⊆ dcT_Bohr0`
    have hB1 : B ∈ setOfBohrRecurrenceFamily S := capThickDualMeetContained hh _ hB
    -- 2. Theorem 5.6: `dcT_Bohr0 ∩ {C ⊆ S : C is a UR set} ⊆ S ⋏ Δ`
    have hB2 : B ∈ syndeticFamily S ⋏ deltaFamily S := by
      refine (mem_famMeet (syndeticFamily S) (deltaFamily S) B).mpr fun T hT ↦ ?_
      rw [dualSyndeticThick] at hT
      exact commURSetsOfBohrRecurrenceAreDelta B (hBur := hBUR) (hBrec := hB1) T hT
    -- 3. `S = T* ⊆ (T∩h)*`, so `S ⋏ Δ ⊆ (T∩h)* ⋏ Δ`
    have hsub : syndeticFamily S ⊆ (capFamily (thickFamily S) h)* := by
      rw [← dualThickSyndetic]
      exact dualIsAntitone fun C hC ↦ thickIsMonotone hC Set.inter_subset_right
    exact familyMeetIsMonotonicSlot1 (deltaFamily S) hsub hB2
  -- by Theorem 5.4, `A ∈ ⋃_{H ∈ T} ((T∩H)* ⋏ Δ)`
  obtain ⟨⟨t, ht⟩, hAt⟩ := (Family.mem_iUnion _ A).mp
    (urContainmentSufficesForFamilyContainmentUpgrade _ _ hFG hA)
  -- and `(T∩t)* ⋏ Δ ⊆ Δ`
  exact capThickDualMeetContained ht (deltaFamily S) hAt

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
  have hAD : A ∈ (deltaFamily S)* := (mem_dual_star _ A).mpr fun C hC ↦ hA C hC
  -- by Theorem B and Lemma 3.8, `(T∩H)* ⋏ Bohr_0* ⊆ Δ`
  have hsub : (capFamily (thickFamily S) H)* ⋏ (bohrZeroFamily S)* ⊆ deltaFamily S :=
    fun B hB ↦ DeltaTheoremB B ⟨H, hH, fun H' hH'H hH' ↦ fun C hC ↦
      (mem_dual_star _ _).mp
        ((memberOfCapFamDualMeetH (thickFamily S) (bohrZeroFamily S)* B H).mp hB H'
        ((thickIsSame H').mp hH') hH'H) C hC⟩
  -- taking duals, `Δ* ⊆ ((T∩H)* ⋏ Bohr_0*)* = (T∩H) ⋎ Bohr_0`
  have hAJ : A ∈ capFamily (thickFamily S) H ⋎ bohrZeroFamily S := by
    have hA' := dualIsAntitone hsub hAD
    rwa [familyDeMorgan2, dualIsInvolutionOnFamilies, dualIsInvolutionOnFamilies] at hA'
  -- by Lemma 3.8, there is a thick `H' ⊆ H` and a Bohr_0 set `B` with `A ∩ H' = B ∩ H'`
  obtain ⟨H', hH', hH'H, B, hB, hAB⟩ :=
    (memberOfCapFamJoinH (thickFamily S) (bohrZeroFamily S) A H).mp hAJ
  exact ⟨B, H', hB, ((thickIsSame H').mpr hH'), hH'H, hAB⟩


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
        by
  intro A hA H hH
  have hAC : A ∈ (centralFamily S)* := (mem_dual_star _ A).mpr
    fun C hC ↦ hA C ((centralIsSame C).mpr hC)
  -- (5.3): `⋃_{H ∈ T} ((T∩H)* ⋏ IP) ⊆ C`
  have h53 : Family.iUnion (fun (t : (thickFamily S).sets) ↦
      (capFamily (thickFamily S) t)* ⋏ IPFamily S) ⊆ centralFamily S := by
    -- the condition of Theorem 5.4 for `F := IP` and `G := C`
    have hFG : ∀ h ∈ thickFamily S,
        ((capFamily (thickFamily S) h)* ⋏ IPFamily S).sets ∩ {C : Set S | isURSet C} ⊆
          ((capFamily (thickFamily S) h)* ⋏ centralFamily S).sets := by
      rintro h hh B ⟨hB, hBUR⟩
      -- by Lemma 5.2, `B = R(x, U)` for a point `x` in a minimal system and a clopen `U`
      obtain ⟨X, _, _, _, _, dSystem, hMin, x, U, hU, rfl⟩ := urSetIsRxU hBUR
      -- `R(x, U) ∩ H' ∈ IP` for all thick `H' ⊆ h`, so `R(x, U) ∩ H' ∈ C` for all thick `H' ⊆ h`
      refine (memberOfCapFamDualMeetH (thickFamily S) (centralFamily S) _ h).mpr
        fun H' hH' hH'h ↦ ?_
      exact preStrongIPIffStrongCentralInCountCommSemi hMin x hU h hh
        (fun G hGh hG ↦ (memberOfCapFamDualMeetH (thickFamily S) (IPFamily S) _ h).mp hB G hG hGh)
        H' hH'h hH'
    -- by Theorem 5.4, `D ∈ ⋃_{H ∈ T} ((T∩H)* ⋏ C)`, and `(T∩t)* ⋏ C ⊆ C`
    intro D hD
    obtain ⟨⟨t, ht⟩, hDt⟩ := (Family.mem_iUnion _ D).mp
      (urContainmentSufficesForFamilyContainmentUpgrade _ _ hFG hD)
    exact capThickDualMeetContained ht (centralFamily S) hDt
  -- in particular, `(T∩H)* ⋏ IP ⊆ C`
  have hsub : (capFamily (thickFamily S) H)* ⋏ IPFamily S ⊆ centralFamily S := fun B hB ↦
    h53 ((Family.mem_iUnion _ B).mpr ⟨⟨H, ((thickIsSame H).mp hH)⟩, hB⟩)
  -- taking duals, `C* ⊆ ((T∩H)* ⋏ IP)* = (T∩H) ⋎ IP*`
  have hAJ : A ∈ capFamily (thickFamily S) H ⋎ (IPFamily S)* := by
    have hA' := dualIsAntitone hsub hAC
    rwa [familyDeMorgan2, dualIsInvolutionOnFamilies] at hA'
  -- by Lemma 3.8, there is a thick `H' ⊆ H` and an IP* set `B` with `A ∩ H' = B ∩ H'`
  obtain ⟨H', hH', hH'H, B, hB, hAB⟩ :=
    (memberOfCapFamJoinH (thickFamily S) (IPFamily S)* A H).mp hAJ
  exact ⟨B, H', fun C hC ↦ (mem_dual_star _ B).mp hB C
    hC, ((thickIsSame H').mpr hH'), hH'H, hAB⟩


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
  familyDual (familyJoin F G) = familyMeet (familyDual F) (familyDual G) := by
  intro F G H I hF hG hH hI
  -- `F`, `G`, `H`, `I` as terms of type `Family S` (FA_Defs)
  let 𝓕 : Family S := ⟨F, fun A B hA hAB ↦ hF A B hAB hA⟩
  let 𝓖 : Family S := ⟨G, fun A B hA hAB ↦ hG A B hAB hA⟩
  let 𝓗 : Family S := ⟨H, fun A B hA hAB ↦ hH A B hAB hA⟩
  let 𝓘 : Family S := ⟨I, fun A B hA hAB ↦ hI A B hAB hA⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- closedness
  · -- `isFamily (familyMeet F G)`: `Family.famMeet` (FA_Defs)
    exact fun A B hAB hA ↦ (Family.famMeet 𝓕 𝓖).upward_closed A B hA hAB
  · -- `isFamily (familyJoin F G)`: `Family.famJoin` (FA_Defs)
    exact fun A B hAB hA ↦ (Family.famJoin 𝓕 𝓖).upward_closed A B hA hAB
  -- associativity
  · -- `familyMeet (familyMeet F G) H = familyMeet F (familyMeet G H)`:
      --`familyMeetIsAssociative` (FA_Main)
    exact congrArg Family.sets (familyMeetIsAssociative 𝓕 𝓖 𝓗).symm
  · -- `familyJoin (familyJoin F G) H = familyJoin F (familyJoin G H)`:
      --`familyJoinIsAssociative` (FA_Main)
    exact congrArg Family.sets (familyJoinIsAssociative 𝓕 𝓖 𝓗).symm
  -- commutativity
  · -- `familyMeet F G = familyMeet G F`: `familyMeetIsCommutative` (FA_Main)
    exact congrArg Family.sets (familyMeetIsCommutative 𝓕 𝓖)
  · -- `familyJoin F G = familyJoin G F`: `familyJoinIsCommutative` (FA_Main)
    exact congrArg Family.sets (familyJoinIsCommutative 𝓕 𝓖)
  -- monotonicity
  · -- `F ⊆ H → G ⊆ I → familyMeet F G ⊆ familyMeet H I`: `familyMeetIsMonotonic` (FA_Main)
    exact familyMeetIsMonotonic (F1 := 𝓕) (G1 := 𝓗) (F2 := 𝓖) (G2 := 𝓘)
  · -- `F ⊆ H → G ⊆ I → familyJoin F G ⊆ familyJoin H I`: `familyJoinIsMonotonic` (FA_Main)
    exact familyJoinIsMonotonic (F1 := 𝓕) (G1 := 𝓗) (F2 := 𝓖) (G2 := 𝓘)
  -- DeMorgan-type laws
  · -- `familyDual (familyMeet F G) = familyJoin (familyDual F) (familyDual G)`:
      --`familyDeMorgan2` (FA_Main)
    exact congrArg Family.sets (familyDeMorgan2 𝓕 𝓖)
  · -- `familyDual (familyJoin F G) = familyMeet (familyDual F) (familyDual G)`:
      --`familyDeMorgan1` (FA_Main)
    exact congrArg Family.sets (familyDeMorgan1 𝓕 𝓖)

end DeltaIntro
