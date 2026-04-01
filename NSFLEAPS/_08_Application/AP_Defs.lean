import NSFLEAPS._06_Furstenberg_families.FF_Defs
import NSFLEAPS._07_RP.RP_Defs

section Reduction

/-- A CRT set is a set that is equal to R(x,U) for U clopen. -/
def isCRTSet
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∃ (X : Type*) (_ : TopologicalSpace X) (_ : CompactSpace X) (_ : T2Space X) (_ : Nonempty X)
(dSystem : DS.DynamicalSystem S X) (x : X) (U : Set X),
DS.isUniformlyRecurrent dSystem x ∧ IsClopen U ∧ x ∈ U ∧ DS.visitTimeSet dSystem x U = A

/-- The set corresponding to a uniformly recurrent point in symbolic space is a CRT set -/
theorem unifRecPtsInSymbolicSpaceAreCRTSets
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
isUniformlyRecurrent (symbolicSystem S) (indicator A) → isCRTSet A



end Reduction

section Delta_builder

end Delta_builder

section Dynamical_sets_of_bohr_recurrence

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
