import NSFLEAPS._06_Furstenberg_families.FF_Defs
import NSFLEAPS._07_RP.RP_Defs
import NSFLEAPS._08_Application.AP_Symbolic_system

section Reduction_to_CRT_sets

/-- A CRT set is a set that is equal to R(x,U) for U clopen. -/
def isCRTSet
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∃ (X : Type*) (_ : TopologicalSpace X) (_ : CompactSpace X) (_ : T2Space X) (_ : Nonempty X)
(dSystem : DynamicalSystem S X) (x : X) (U : Set X),
isUniformlyRecurrent dSystem x ∧ IsClopen U ∧ x ∈ U ∧ visitTimeSet dSystem x U = A

/-- The set corresponding to a uniformly recurrent point in symbolic space is a CRT set -/
theorem unifRecPtsInSymbolicSpaceAreCRTSets
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
isUniformlyRecurrent (symbolicSystem S) (indicator A) → isCRTSet A :=
by sorry

/-- Given a syndetic set `A` and a thick set `H`, there exists a
CRT set `B` and a thick set `G` such that `A ∩ G = B ∩ G` -/
theorem syndSetIsCRTOnThickSet
{S : Type*} [Semigroup S] [Nonempty S]
(A : Set S) {hA : isSyndetic A}
(H : Set S) {hH : isThick H} :
∃ (B : Set S) (G : Set S),
isCRTSet B ∧ isThick G ∧ (A ∩ G = B ∩ G) :=
by sorry

/-- If the containment `S ⋏ F ⊆ S ⋏ G` holds for CRT sets, then it holds
for all sets. -/
theorem crtContainmentSufficesForFamilyContainment
{S : Type*} [Semigroup S] [Nonempty S]
(F G : Family S)
{hFG : ∀ (B H : Set S), isCRTSet B → isThick H → B ∩ H ∈ F → B ∩ H ∈ G} :
((syndeticFamily S) ⋏ F) ⊆ ((syndeticFamily S) ⋏ G) :=
by sorry

end Reduction_to_CRT_sets

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

theorem commCRTSetsOfBohrRecurrenceAreDelta
{S : Type*} [CommSemigroup S] [Nonempty S]
(B : Set S) {hBcrt : isCRTSet B} {hBrec : isSetOfBohrRecurrence B} :
∀ (H : Set S), isThick H → isDelta (B ∩ H) :=
by sorry

end Dynamical_sets_of_bohr_recurrence

section Application

/-- In a commutative semigroup, S ⋏ Δ = S ⋏ dcT_Bohr -/
theorem commSyndFamMeetDeltaIsSnydFamMeetSetOfBohrRecurrence
{S : Type*} [CommSemigroup S] [Nonempty S] :
(syndeticFamily S) ⋏ (deltaFamily S) = (syndeticFamily S) ⋏ (setOfBohrRecurrenceFamily S) :=
by sorry


/-- In a commutative semigroup, S ⋏ Δ = S ⋏ Δ_0 -/
theorem commSyndFamMeetDeltaIsSnydFamMeetDeltaZero
{S : Type*} [CommSemigroup S] [Nonempty S] :
(syndeticFamily S) ⋏ (deltaFamily S) = (syndeticFamily S) ⋏ (deltaZeroFamily S) :=
by sorry

/-- In a commutative semigroup, Δ* ⊆ S ⋏ (T ⋎ dcS_Bohr) -/
theorem commDeltaStarImpliesLocallyBohrZero
{S : Type*} [CommSemigroup S] [Nonempty S] :
(deltaFamily S)* ⊆ ((syndeticFamily S) ⋏ ((thickFamily S) ⋎ (bohrZeroFamily S))) :=
by sorry


end Application
