import NSFLEAPS._06_Furstenberg_families.FF_Defs
import NSFLEAPS._07_RP.RP_Defs
import NSFLEAPS._08_Application.AP_Symbolic_system


section Theorems_needed_from_FA_Theorems
-- This section contains theorems from FA_Theorems which are not stated yet
-- I state them here to use for theorems in this file
-- After we state corresponding theorems in FA_Theorems, the statements in this
-- section will be removed

/-- For families F and G, we have F ⋏ G ⊆ F ∩ G -/
-- This theorem will be moved to FA_Theorems later
theorem familyMeetContainedInIntersection
{S : Type*} (F G : Family S) : F ⋏ G ⊆ F ∩ G := by
sorry

/-- Familymeet is monotone -/
-- We will move this theorem to FA_Theorems file later
theorem familyMeetIsMonotonic
{S : Type*} (F G H : Family S) (hGH : G ⊆ H) : F ⋏ G ⊆ F ⋏ H := by
sorry

/-- This lemma helps us unfold the definition of FamilyMeet -/
-- This may be redundant eventually.
-- But for now, I am struggling to unfold the definition of FamilyMeet, so I use this lemma
lemma unfoldFamMeet
{S : Type*} (F G : Family S) (A : Set S) : A ∈ F ⋏ G ↔ ∀ B ∈ F*, A ∩ B ∈ G := by
  sorry

/-- For families F, G, H, we have H* ⊆ F ⋏ (F* ⋎ G*) ↔ F ⋏ G ⊆ F ⋏ H -/
-- This theorem should be also in FA_Theorems. I state it here since it's needed for this section
-- and the corresponding theorem in FA_Theorems is not there yet
theorem familyLocalImplicationEquivalence
{S : Type*} (F G H : Family S) : H* ⊆ F ⋏ (F* ⋎ G*) ↔ F ⋏ G ⊆ F ⋏ H := by
sorry

end Theorems_needed_from_FA_Theorems

section Reduction_to_UR_sets

/-- A set `A ⊆ S` is uniformly recurrent if `1_A` is `S`-uniformly recurrent
in the symbolic system `{0,1}^S` -/
def isURSet
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
isUniformlyRecurrent (selfSymbolicSystem S) (indicator A)

/-- An UR set can be written as R(x, U) -/
theorem urSetIsRxU
{S : Type*} [Semigroup S] [Nonempty S] {A : Set S} (hA : isURSet A) :
∃ (U : Set (WithOne S → Bool)) (UClopen : IsClopen U) (UNonempty : U.Nonempty),
∃ (x : WithOne S → Bool) (xMin : isUniformlyRecurrent (monoidExtSymbolicSystem S) x),
A = visitTimeSet (monoidExtSymbolicSystem S) x U := by
simp
let U := {x : WithOne S → Bool | x none = true}
use U
constructor
· sorry
constructor
· sorry
let liftSet : Set S → Set (WithOne S) := fun A : Set S ↦ {s : WithOne S | ∃ t ∈ A, some t = s}
let A_wOne := liftSet A
classical
let x0 := fun (s : WithOne S) ↦ if s ∈ A_wOne then true else false
let x1 := fun (s : WithOne S) ↦ if s ∈ A_wOne ∪ {none} then true else false
have h1 : isUniformlyRecurrent (monoidExtSymbolicSystem S) x0 ∨ isUniformlyRecurrent (monoidExtSymbolicSystem S) x0 := by
  sorry
rcases h1 with hx0 | hx1
use x0
use hx0
ext s
constructor
intro hs
unfold visitTimeSet
simp
sorry
sorry
sorry

/-- Given a syndetic set `A` and a thick set `H`, there exists a
UR set `B` and a thick set `G` such that `A ∩ G = B ∩ G` -/
theorem syndSetIsUROnThickSet
{S : Type*} [Semigroup S] [Nonempty S]
(A : Set S) {hA : isSyndetic A}
(H : Set S) {hH : isThick H} :
∃ (B : Set S) (hB : isURSet B) (H' : Set S) (hH' : isThick H') (hHH' : H' ⊆ H),
A ∩ H' = B ∩ H' :=
by sorry

/-- If the containment `S ⋏ F ⊆ S ⋏ G` holds for UR sets, then it holds
for all sets. -/
theorem urContainmentSufficesForFamilyContainment
{S : Type*} [Semigroup S] [Nonempty S]
(F G : Family S)
{hFG : ∀ (B H : Set S), isURSet B → isThick H → B ∩ H ∈ F → B ∩ H ∈ G} :
(syndeticFamily S) ⋏ F ⊆ (syndeticFamily S) ⋏ G := by
intro A hA
have h0 : isSyndetic A := by
  have h01 : syndeticFamily S ⋏ F ⊆ syndeticFamily S ∩ F := by
    apply familyMeetContainedInIntersection
  have h02 : A ∈ syndeticFamily S ∩ F := by
    exact h01 hA
  have h03 : A ∈ syndeticFamily S := by
    exact h02.1
  simpa
have h1 : ∀ H : Set S, isThick H → A ∩ H ∈ G := by
  intro H hH
  have h11 : ∃ (B : Set S) (hB : isURSet B) (H' : Set S) (hH' : isThick H') (hHH' : H' ⊆ H),
  A ∩ H' = B ∩ H' := by
    apply syndSetIsUROnThickSet
    · exact h0
    exact hH
  obtain ⟨B, hB, H', hH', hHH', h2⟩ := h11
  have h12 : ∀ B ∈ (syndeticFamily S)*, A ∩ B ∈ F := by
    exact (unfoldFamMeet (syndeticFamily S) F A).mp hA
  have h13 : A ∩ H' ∈ F := by
    specialize h12 H'
    rw [dualSyndeticThick] at h12
    apply h12
    exact hH'
  have h14 : B ∩ H' ∈ F := by
    rw [<- h2]
    exact h13
  have h15 : B ∩ H' ∈ G := by
    apply hFG
    · exact hB
    · exact hH'
    exact h14
  have h16 : A ∩ H' ∈ G := by
    rw [h2]
    exact h15
  have h17 : A ∩ H' ⊆ A ∩ H := by
    apply Set.inter_subset_inter_right
    exact hHH'
  apply Family.upward_closed
  · exact h16
  exact h17
simp only [SetLike.mem_coe] at hA
simp only [SetLike.mem_coe]
have h2 : (syndeticFamily S)* = (thickFamily S) := by
  exact dualSyndeticThick
have h3 : (∀ H ∈ thickFamily S, A ∩ H ∈ G) → A ∈ syndeticFamily S⋏G := by
  rw [<- dualSyndeticThick]
  exact (unfoldFamMeet (syndeticFamily S) G A).mpr
apply h3
intro H hH2
specialize h1 H hH2
exact h1

end Reduction_to_UR_sets

section Delta_builder

/-- If (x, y) is in regional proximal relation in a minimal system X and V ∋ y,
then for all thick set H, R(x, V) ∩ H is a Delta set -/
theorem commVisitTimeSetForRPPairIsDelta
{S : Type*} [CommSemigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} {hMin : isMinimalSystem dSystem}
(x : X) {y : X}
(V : Set X) {hV : V ∈ nhds y} :
∀ (H : Set S), isThick H → isDelta ((visitTimeSet dSystem x V) ∩ H) :=
by sorry

end Delta_builder

section Dynamical_sets_of_bohr_recurrence

/-- If B is a set of Bohr recurrence and a uniformly recurrent set,
then for all thick set H, B ∩ H is a Δ set -/
theorem commURSetsOfBohrRecurrenceAreDelta
{S : Type*} [CommSemigroup S] [Nonempty S]
(B : Set S) {hBur : isURSet B} {hBrec : isSetOfBohrRecurrence B} :
∀ (H : Set S), isThick H → isDelta (B ∩ H) :=
by sorry

end Dynamical_sets_of_bohr_recurrence

section Application

/-- In a commutative semigroup, S ⋏ Δ = S ⋏ dcT_Bohr -/
theorem commSyndFamMeetDeltaIsSnydFamMeetSetOfBohrRecurrence
{S : Type*} [CommSemigroup S] [Nonempty S] :
syndeticFamily S ⋏ deltaFamily S = syndeticFamily S ⋏ setOfBohrRecurrenceFamily S:= by
have h1 : syndeticFamily S ⋏ deltaFamily S ⊆ syndeticFamily S ⋏ setOfBohrRecurrenceFamily S := by
  apply familyMeetIsMonotonic
  have h11 : deltaFamily S ⊆ deltaZeroFamily S := by
    exact deltaFamilyContainedInDeltaZeroFamily
  have h12 : deltaZeroFamily S ⊆ setOfBohrRecurrenceFamily S := by
    exact commDeltaZeroImpliesSetOfBohrRecurrence
  intro x hx
  exact h12 (h11 hx)
have h3 : ∀ (B H : Set S), isURSet B → isThick H →
B ∩ H ∈ setOfBohrRecurrenceFamily S → B ∩ H ∈ deltaFamily S := by
  intro B H hB hH hBH
  have h32 : isSetOfBohrRecurrence B := by
    have h33 : B ∩ H ⊆ B := by
      simp
    apply setOfBohrRecurrenceIsMonotone hBH h33
  apply commURSetsOfBohrRecurrenceAreDelta
  · exact hB
  · exact h32
  exact hH
have h2 : syndeticFamily S ⋏ setOfBohrRecurrenceFamily S ⊆ syndeticFamily S ⋏ deltaFamily S := by
  apply urContainmentSufficesForFamilyContainment
  exact h3
simpa using Set.Subset.antisymm h1 h2

/-- In a commutative semigroup, S ⋏ Δ = S ⋏ Δ_0 -/
theorem commSyndFamMeetDeltaIsSnydFamMeetDeltaZero
{S : Type*} [CommSemigroup S] [Nonempty S] :
syndeticFamily S ⋏ deltaFamily S = syndeticFamily S ⋏ deltaZeroFamily S := by
have h1 : syndeticFamily S ⋏ deltaFamily S ⊆ syndeticFamily S ⋏ deltaZeroFamily S := by
  apply familyMeetIsMonotonic
  exact deltaFamilyContainedInDeltaZeroFamily
have h2 : syndeticFamily S ⋏ deltaZeroFamily S ⊆
syndeticFamily S ⋏ setOfBohrRecurrenceFamily S := by
  apply familyMeetIsMonotonic
  exact commDeltaZeroImpliesSetOfBohrRecurrence
have h3 : syndeticFamily S ⋏ setOfBohrRecurrenceFamily S = syndeticFamily S ⋏ deltaFamily S := by
  rw [commSyndFamMeetDeltaIsSnydFamMeetSetOfBohrRecurrence]
have h4 : syndeticFamily S ⋏ deltaZeroFamily S ⊆ syndeticFamily S ⋏ deltaFamily S := by
  rw [<- h3]
  exact h2
simpa using Set.Subset.antisymm h1 h4

/-- In a commutative semigroup, Δ* ⊆ S ⋏ (T ⋎ dcS_Bohr) -/
theorem commDeltaStarImpliesLocallyBohrZero
{S : Type*} [CommSemigroup S] [Nonempty S] :
(deltaFamily S)* ⊆ syndeticFamily S ⋏ (thickFamily S ⋎ bohrZeroFamily S) := by
rw [<- dualSyndeticThick]
have h1 : syndeticFamily S ⋏ (bohrZeroFamily S)* ⊆ syndeticFamily S ⋏ deltaFamily S := by
  rw [commSyndFamMeetDeltaIsSnydFamMeetSetOfBohrRecurrence]
  rw [dualBohrZeroSetsOfBohrRecurrence]
  intro x hx
  exact hx
have h2 : (bohrZeroFamily S)** = bohrZeroFamily S := by
  apply dual_dual_smth_smth
rw [<- h2]
exact (familyLocalImplicationEquivalence (syndeticFamily S)
(bohrZeroFamily S)* (deltaFamily S)).mpr h1

end Application
