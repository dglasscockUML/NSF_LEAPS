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
Set X := Set.range (fun s ↦ sAction.toFun s x)
-- '' (Set.univ : Set S)

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

-- Do we need: diagDynamicalSystem?  Wait.

/-- When `S` acts on `X`, if `y` is in the orbit closure of `x` and `z` is
in the orbit closure of `y`, then `z` is in the orbit closure of `x`. -/
theorem orbitTransitivity {S} [Semigroup S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X]
{dSystem : DynamicalSystem S X} {x y z : X}
(hyx : y ∈ DS.orbitClosure dSystem.toSemigroupAction x)
(hzy : z ∈ DS.orbitClosure dSystem.toSemigroupAction y) :
z ∈ DS.orbitClosure dSystem.toSemigroupAction x := by
  unfold DS.orbitClosure
  simp only [mem_closure_iff]
  intro U hU hzU
  unfold DS.orbitClosure at hzy
  simp only [mem_closure_iff] at hzy
  have UcapOrby : (U ∩ DS.orbit dSystem.toSemigroupAction y).Nonempty :=
    hzy U hU hzU
  rcases UcapOrby with ⟨u, hu1, hu2⟩
  unfold DS.orbit at hu2
  simp only [Set.range] at hu2
  rcases hu2 with ⟨s, hs⟩
  have yInsInvCapU : y ∈ (dSystem.toFun s) ⁻¹' U := by
    simp only [Set.preimage]
    simp only [← hs] at hu1
    exact hu1
  have isOpenInvU : IsOpen ((dSystem.toFun s) ⁻¹' U) :=
    IsOpen.preimage (dSystem.cont' s) hU
  unfold DS.orbitClosure at hyx
  simp only [mem_closure_iff] at hyx
  have invUcapOrby : (((dSystem.toFun s) ⁻¹' U) ∩ DS.orbit dSystem.toSemigroupAction x).Nonempty :=
    hyx ((dSystem.toFun s) ⁻¹' U) isOpenInvU yInsInvCapU
  rcases invUcapOrby with ⟨v, hv1, hv2⟩
  unfold DS.orbit at hv2
  simp only [Set.range] at hv2
  rcases hv2 with ⟨t, ht⟩
  have stxInU : dSystem.toFun (s * t) x ∈ U := by
    simp only [dSystem.map_mult']
    simp only [← ht] at hv1
    exact hv1
  simp only [DS.orbit]
  have stxInRange :
  dSystem.toFun (s * t) x ∈ Set.range fun s ↦ dSystem.toFun s x := by
    simp only [Set.range]
    use s * t
  use dSystem.toFun (s * t) x
  exact ⟨stxInU, stxInRange⟩

def DS.isInvariantSet {S} [Semigroup S] {X} (sAction : SemigroupAction S X)
(A : Set X) : Prop := ∀ (s : S)(x : X), x ∈ A → sAction.toFun s x ∈ A

/-- In dynamical system given by an action of a semigroup `S` on a space `X`,
the closure of an `S`-invariant set `A ⊆ X` is `S`-invariant -/
theorem closureOfInvIsInv {S} [Semigroup S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X]
{dSystem : DynamicalSystem S X} {A : Set X} (h : DS.isInvariantSet dSystem.toSemigroupAction A) :
DS.isInvariantSet dSystem.toSemigroupAction (closure A) := by sorry
-- Use imageClosureIsClosureImage from the topology file

/-- A sub (topological) dynamical system of a topological dynmical system given by
a semigroup `S` acting on `X` is a nonempty, compact, invariant subset of `X`
together with the action by `S`. -/
structure SubDynamicalSystem (S) [Semigroup S]
(X) [TopologicalSpace X] [CompactSpace X] [T2Space X]
{dSystem : DynamicalSystem S X} extends DynamicalSystem S X where
  carrier : Set X
  carrier_inv := DS.isInvariantSet dSystem.toSemigroupAction carrier
  carrier_nonempty := carrier.Nonempty
  carrier_compact := IsCompact carrier
