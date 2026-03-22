import NSFLEAPS._01_Topology.TP_Defs
import NSFLEAPS._02_Semigroups.SG_Defs


/-- A semigroup action is an action by a semigroup `S` on a set `X` -/
structure SemigroupAction (S : Type*) [Semigroup S] (X : Type*) where
  toFun : S → X → X
  map_mult' : ∀ s₁ s₂ x, toFun (s₁ * s₂) x = toFun s₁ (toFun s₂ x)

/-- A (topological) dynamical system is a compact Hausdorff space `X` together
with an action by a (discrete) semigroup `S`. -/
structure DynamicalSystem (S : Type*) [Semigroup S]
(X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
extends SemigroupAction S X where
  cont' : ∀ s, Continuous (toFun s)

/-- The orbit of a point `x` under the action of a semigroup `S` is the
image of `S` under the map `s ↦ sx` -/
def DS.orbit {S} [Semigroup S] {X} (sAction : SemigroupAction S X) (x : X) :
Set X := (fun s ↦ sAction.toFun s x) '' (Set.univ : Set S)

/-- The orbit closure of a point `x` under the action of a semigroup `S` is the
closure of the image of `S` under the map `s ↦ sx` -/
def DS.orbitClosure {S} [Semigroup S] {X} [TopologicalSpace X]
(sAction : SemigroupAction S X) (x : X) :
Set X := closure (DS.orbit sAction x)

/-- Given a semigroup action of `S` on `X`, the diagonal semigroup action
of `S` on `X × X` is given by `s (x,y) = (sx,sy)` -/
def diagSemigroupAction {S} [Semigroup S] {X} (sAction : SemigroupAction S X) :
SemigroupAction S (X × X) := {
  toFun := fun s ↦ Prod.map (sAction.toFun s) (sAction.toFun s)
  map_mult' := by
    intro s t (x,y)
    simp only [Prod.map]
    simp only [sAction.map_mult']
}

-- Do we need: diagDynamicalSystem?

/-- When `S` acts on `X`, if `y` is in the orbit closure of `x` and `z` is
in the orbit closure of `y`, then `z` is in the orbit closure of `x`. -/
theorem orbitTransitivity {S} [Semigroup S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X]
{x y z : X} {dSystem : DynamicalSystem S X}
(hyx : y ∈ DS.orbitClosure dSystem.toSemigroupAction x)
(hzy : z ∈ DS.orbitClosure dSystem.toSemigroupAction y) :
 z ∈ DS.orbitClosure dSystem.toSemigroupAction x :=
 sorry
