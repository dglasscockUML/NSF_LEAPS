import NSFLEAPS._04_Dynamical_systems.DS_Defs

/- This file is intended to keep the code describing the dynamical system {0,1}^S with the shift -/

/- funSpace S gives {0,1}^S as a compact Hausdorff space -/
/- def funSpace
(S : Type*) [Semigroup S] [Nonempty S] : -/


/-- symbolicSystem S is the dynamical system consisting of {0,1}^S with the natural S action -/
def symbolicSystem
(S : Type*) [Semigroup S] [Nonempty S] :
DynamicalSystem S (funSpace S) :=
by sorry

/-- indicator A gives the indicator function of A -/
def indicator
{S : Type*} [Semigroup S] [Nonempty S] :
Set S → funSpace S :=
by sorry
