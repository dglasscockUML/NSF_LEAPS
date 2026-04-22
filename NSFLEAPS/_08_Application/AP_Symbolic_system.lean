import NSFLEAPS._04_Dynamical_systems.DS_Defs

/- This file is intended to keep the code describing the dynamical system {0,1}^S with the shift -/

/- A general note: Bool is a type with terms `true` and `false`.
Apparently, Lean automatically gives it the discrete topology?
Then `S → Bool` has the product topology by association with `Bool^S`.
Since this is a product of compact, Hausdorff spaces, it is compact, Hausdorff.
Apparently Lean knows all of this automatically. -/

/-- `RightSemigroupAction S X` is ... -/
structure RightSemigroupAction
(S : Type*) [Semigroup S] (X : Type*) where
  map : X → S → X
  mapMult : ∀ s₁ s₂ x, map x (s₁ * s₂) = map (map x s₁) s₂


/-- symbolicSystem S is the dynamical system consisting of {0,1}^S with the natural S action -/
def symbolicSystem
(S : Type*) [Semigroup S] [Nonempty S]
(X : Type*) [Nonempty X]
(rightAction : RightSemigroupAction S X) :
DynamicalSystem S (X → Bool) := {
    map := fun (s : S) ↦ (fun (φ : X → Bool) ↦ (fun (x : X) ↦ φ (rightAction.map x s)))
    mapMult := by
        intro s1 s2 φ
        simp only [rightAction.mapMult]
    mapCont := by sorry
}

def basicRightAction
(S : Type*) [Semigroup S] [Nonempty S] :
RightSemigroupAction S S :=
by sorry

/-- symbolicSystem S is the dynamical system consisting of {0,1}^S with the natural S action -/
def selfSymbolicSystem
(S : Type*) [Semigroup S] [Nonempty S] :
DynamicalSystem S (S → Bool) :=
symbolicSystem S S (basicRightAction S)
/- {
    map := fun (s : S) ↦ (fun (φ : S → Bool) ↦ (fun (t : S) ↦ φ (t * s)))
    mapMult := by
        intro s1 s2 φ
        simp only [mul_assoc]
    mapCont := by sorry
} -/

def rightActionOfSOnMonoidExt
(S : Type*) [Semigroup S] [Nonempty S] :
RightSemigroupAction S (WithOne S) :=
by sorry

def monoidExtSymbolicSystem
(S : Type*) [Semigroup S] [Nonempty S] :
DynamicalSystem S ((WithOne S) → Bool) :=
symbolicSystem S (WithOne S) (rightActionOfSOnMonoidExt S)



/-- indicator `A` gives the indicator function of `A` -/
noncomputable
def indicator
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
S → Bool := by
classical
exact fun s => decide (s ∈ A)

/-- For a set `S`, a boolean value val, and `s ∈ S`, the cylinder set
`[value]_s` is the set of functions `S → Bool` whose value at `s` is `val` -/
def cylinderSet
{S : Type*} (val : Bool) (s : S) :
Set (S → Bool) :=
{f : S → Bool | f s = val}


/- def monoidExtension
(S : Type*) [Semigroup S] [Nonempty S] :
Monoid (WithOne S) := WithOne.instMonoid (α := S) -/
