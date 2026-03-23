import NSFLEAPS._01_Topology.TP_Defs
import NSFLEAPS._02_Semigroups.SG_Defs


section Definitions

/-- A semigroup action is an action by a semigroup `S` on a set `X` -/
structure SemigroupAction (S : Type*) [Semigroup S] [Nonempty S]
(X : Type*) [Nonempty X] where
  toFun : S → X → X
  map_mult' : ∀ s₁ s₂ x, toFun (s₁ * s₂) x = toFun s₁ (toFun s₂ x)

/-- A (topological) dynamical system is a compact Hausdorff space `X` together
with an action by a (discrete) semigroup `S`. -/
structure DynamicalSystem (S : Type*) [Semigroup S] [Nonempty S]
(X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
extends SemigroupAction S X where
  cont' : ∀ s, Continuous (toFun s)

/-- The orbit of a point `x` under the action of a semigroup `S` is the
image of `S` under the map `s ↦ sx` -/
def DS.orbit {S} [Semigroup S] [Nonempty S]
{X} [Nonempty X] (sAction : SemigroupAction S X) (x : X) :
Set X := Set.range (fun s ↦ sAction.toFun s x)
-- '' (Set.univ : Set S)

/-- The orbit closure of a point `x` under the action of a semigroup `S` is the
closure of the image of `S` under the map `s ↦ sx` -/
def DS.orbitClosure {S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [Nonempty X]
(sAction : SemigroupAction S X) (x : X) :
Set X := closure (DS.orbit sAction x)

/-- Given a semigroup action of `S` on `X`, the diagonal semigroup action
of `S` on `X × X` is given by `s (x,y) = (sx,sy)` -/
def diagSemigroupAction {S} [Semigroup S] [Nonempty S]
{X} [Nonempty X] (sAction : SemigroupAction S X) :
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
theorem DS.orbitTransitivity {S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
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

/-- A subset `A ⊆ X` is `S`-invariant if `SA ⊆ A` -/
def DS.isInvariantSet {S} [Semigroup S] [Nonempty S]
{X} [Nonempty X] (sAction : SemigroupAction S X) (A : Set X) : Prop :=
∀ (s : S)(x : X), x ∈ A → sAction.toFun s x ∈ A

/-- In dynamical system given by an action of a semigroup `S` on a space `X`,
the closure of an `S`-invariant set `A ⊆ X` is `S`-invariant -/
theorem DS.closureOfInvIsInv {S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} {A : Set X} (h : DS.isInvariantSet dSystem.toSemigroupAction A) :
DS.isInvariantSet dSystem.toSemigroupAction (closure A) := by sorry
-- Use imageClosureIsClosureImage from the topology file

/-- The `S`-orbit closure of a point `x` is an `S`-invariant subset of `X` -/
theorem DS.orbClosIsInv {S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} {x : X} :
DS.isInvariantSet dSystem.toSemigroupAction (DS.orbitClosure dSystem.toSemigroupAction x) :=
by sorry

/-- A sub (topological) dynamical system of a topological dynmical system given by
a semigroup `S` acting on `X` is a nonempty, compact, invariant subset of `X`
together with the action by `S`. -/
def DS.isSubDynamicalSystem {S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (Z : Set X) : Prop :=
Z.Nonempty ∧ IsCompact Z ∧ T2Space Z ∧ DS.isInvariantSet dSystem.toSemigroupAction Z

/- Implemenetation note: SubDynamicalSystem is a class since given the parameters
(a dynamical system and a non-empty, compact, invariant set), it is canonically determined -/

/-- A sub (topological) dynamical system of a topological dynmical system given by
a semigroup `S` acting on `X` is a nonempty, compact, invariant subset of `X`
together with the action by `S`. -/
class SubDynamicalSystem {S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (Z : Set X) where
  carrier_inv : DS.isInvariantSet dSystem.toSemigroupAction Z
  carrier_nonempty := Z.Nonempty
  carrier_compact := IsCompact Z

-- Still working on this definition.  Not sure how to make lean see that
-- the compactness of Z will come from the assumption isSubDynamicalSystem dSystem Z
/-def DS.makeDynamicalSystemFromSub {S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (Z : Set X)
{hZ : isSubDynamicalSystem dSystem Z} : DynamicalSystem S Z := sorry

instance
    {S : Type*} [Semigroup S] [Nonempty S]
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
    {dSystem : DynamicalSystem S X} {Z : Set X}
    [sub : SubDynamicalSystem dSystem Z] : CompactSpace Z := sorry

instance
    {S : Type*} [Semigroup S] [Nonempty S]
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
    {dSystem : DynamicalSystem S X} {Z : Set X}
    [SubDynamicalSystem dSystem Z] : DynamicalSystem S Z :=-/


/-- The `S`-orbit closure of a point `x` is a sub dynamical system of `DynamicalSystem S X` -/
theorem DS.orbitClosureIsSubDynamicalSystem {S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (x : X) :
DS.isSubDynamicalSystem dSystem (DS.orbitClosure dSystem.toSemigroupAction x) := by
  unfold DS.isSubDynamicalSystem
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold DS.orbitClosure
    unfold DS.orbit
    --have nonemptyOrbit : (orbit dSystem.toSemigroupAction x).Nonempty := sorry
    exact Set.Nonempty.mono subset_closure (Set.range_nonempty (fun s ↦ dSystem.toFun s x))
  · exact IsClosed.isCompact (isClosed_closure)
  · infer_instance
  · exact DS.orbClosIsInv


/-- An intersection of `S`-invariant sets is `S`-invariant -/
theorem DS.InterOfInvIsInv {S} [Semigroup S] [Nonempty S]
{X} [Nonempty X] (sAction : SemigroupAction S X)
{i : Set (Set X)} (h : ∀ (A : Set X), A ∈ i → DS.isInvariantSet sAction A) :
DS.isInvariantSet sAction (⋂₀ i) := by
  intro s x hx
  rw [← Set.sInf_eq_sInter]
  simp only [sInf]
  intro A AinI
  rw [← Set.sInf_eq_sInter] at hx
  simp only [sInf] at hx
  have xinA : x ∈ A := hx A AinI
  unfold isInvariantSet at h
  exact h A AinI s x xinA

end Definitions


section Factor_maps_and_ICERS

end Factor_maps_and_ICERS



section Return_time_sets

/-- The set of times `s ∈ S` for which the point `x ∈ X` visits the set `U ⊆ X` -/
def DS.returnTimeSet (S) [Semigroup S] [Nonempty S]
{X} [Nonempty X] {sAction : SemigroupAction S X}
(x : X) (U : Set X) : Set S := (fun (s : S) ↦ sAction.toFun s x) ⁻¹' U

/-- The set of times `s ∈ S` for which the point `x ∈ X` visits the set `U ⊆ X` -/
def DS.setReturnTimeSet (S) [Semigroup S] [Nonempty S]
{X} [Nonempty X] {sAction : SemigroupAction S X}
(U V : Set X) : Set S := {s : S | (((sAction.toFun s) '' U) ∩ V).Nonempty}

theorem DS.visitsToPreimages {S} [Semigroup S] [Nonempty S]
{X} [Nonempty X] {sAction : SemigroupAction S X}
(x : X) (U : Set X) (s : S) :
(s * ·) ⁻¹' (DS.returnTimeSet S x U (sAction := sAction)) =
DS.returnTimeSet S x ((sAction.toFun s) ⁻¹' U) (sAction := sAction) :=
by sorry

end Return_time_sets



section Minimality

end Minimality



section Uniform_recurrence

end Uniform_recurrence



section Proximality

end Proximality



section Regional_proximality


end Regional_proximality


section Equicontinuity_and_regional_proximality


end Equicontinuity_and_regional_proximality


section Equicontinuous_structure_relation

end Equicontinuous_structure_relation
