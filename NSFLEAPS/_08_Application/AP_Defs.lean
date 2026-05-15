import NSFLEAPS._06_Furstenberg_families.FF_Defs
import NSFLEAPS._07_RP.RP_Defs
import NSFLEAPS._08_Application.AP_Symbolic_system

section Reduction_to_UR_sets

/-- A set `A ⊆ S` is uniformly recurrent if `1_A` is `S`-uniformly recurrent
in the symbolic system `{0,1}^S` -/
def isURSet
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
isUniformlyRecurrent (selfSymbolicSystem S) (indicator A)

/-- The set corresponding to a uniformly recurrent point in symbolic space is a UR set -/
theorem urSetIsRxU
{S : Type*} [Semigroup S] [Nonempty S] {A : Set S} (hA : isURSet A) :
∃ (x : WithOne S → Bool) (xMin : isUniformlyRecurrent (monoidExtSymbolicSystem S) x)
(U : Set (WithOne S → Bool)) (UOpen : IsOpen U) (UNonempty : U.Nonempty),
A = visitTimeSet (monoidExtSymbolicSystem S) x U :=
by sorry

/-- Given a syndetic set `A` and a thick set `H`, there exists a
CRT set `B` and a thick set `G` such that `A ∩ G = B ∩ G` -/
theorem syndSetIsUROnThickSet
{S : Type*} [Semigroup S] [Nonempty S]
(A : Set S) {hA : isSyndetic A}
(H : Set S) {hH : isThick H} :
∃ (B : Set S) (hB : isURSet B) (G : Set S) (hG : isThick G),
A ∩ G = B ∩ G :=
by sorry

/-- If the containment `S ⋏ F ⊆ S ⋏ G` holds for UR sets, then it holds
for all sets. -/
theorem urContainmentSufficesForFamilyContainment
{S : Type*} [Semigroup S] [Nonempty S]
(F G : Family S)
{hFG : ∀ (B H : Set S), isURSet B → isThick H → B ∩ H ∈ F → B ∩ H ∈ G} :
(syndeticFamily S) ⋏ F ⊆ (syndeticFamily S) ⋏ G :=
by sorry

end Reduction_to_UR_sets

section Delta_builder

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
syndeticFamily S ⋏ deltaFamily S = syndeticFamily S ⋏ setOfBohrRecurrenceFamily S:=
by sorry


/-- In a commutative semigroup, S ⋏ Δ = S ⋏ Δ_0 -/
theorem commSyndFamMeetDeltaIsSnydFamMeetDeltaZero
{S : Type*} [CommSemigroup S] [Nonempty S] :
syndeticFamily S ⋏ deltaFamily S = syndeticFamily S ⋏ deltaZeroFamily S :=
by sorry

/-- For families F, G, H, we have H* ⊆ F ⋏ (F* ⋎ G*) ↔ F ⋏ G ⊆ F ⋏ H -/
theorem familyLocalImplicationEquivalence
{S : Type*} (F G H : Family S) : H* ⊆ F ⋏ (F* ⋎ G*) ↔ F ⋏ G ⊆ F ⋏ H := by
sorry

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
