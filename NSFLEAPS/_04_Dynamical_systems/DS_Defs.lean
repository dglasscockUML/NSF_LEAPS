import NSFLEAPS._01_Topology.TP_Defs
import NSFLEAPS._02_Semigroups.SG_Defs

import Mathlib.Topology.UniformSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.OfCompactT2

/- The following namespace line gives all definitions, theorems, etc... a prefix of `DS.` -/
-- DGG: I've decided not to use the namespace.  It probably won't be helpful for us.
--namespace DS

/- Sections are used for organizational purposes only.  See the `Outline` pane under `Explorer`. -/
section Structures

/-- A (topological) dynamical system is a compact Hausdorff space `X` together
with an action by a (discrete) semigroup `S`. -/
structure DynamicalSystem
(S : Type*) [Semigroup S] [Nonempty S]
(X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
where
  map : S → X → X
  mapMult : ∀ s₁ s₂ x, map (s₁ * s₂) x = map s₁ (map s₂ x)
  mapCont : ∀ s, Continuous (map s)

/-- Given dynamical systems of `S` on `X` and `T` on `Y`, the product system
of `S × T` on `X × Y` is given by `(s,t) (x,y) = (sx,ty)` -/
def prodDynamicalSystem
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemOne : DynamicalSystem S X)
{T : Type*} [Semigroup T] [Nonempty T]
{Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemTwo : DynamicalSystem T Y) :
DynamicalSystem (S × T) (X × Y):=
{
  map := fun ((s,t) : S × T) ↦ Prod.map (dSystemOne.map s) (dSystemTwo.map t)
  mapMult := by
    intro s t (x,y)
    simp only [Prod.map]
    simp only [dSystemOne.mapMult]
    simp only [dSystemTwo.mapMult]
  mapCont := by
    intro (s,t)
    exact Continuous.prodMap (dSystemOne.mapCont s) (dSystemTwo.mapCont t)
}

/-- Given dynamical systems of `S` on `X` and `Y`, the diagonal system
of `S` on `X × Y` is given by `s (x,y) = (sx,sy)` -/
def diagDynamicalSystem
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemX : DynamicalSystem S X)
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemY : DynamicalSystem S Y) :
DynamicalSystem S (X × Y) :=
{
  map := fun s ↦ Prod.map (dSystemX.map s) (dSystemY.map s)
  mapMult := by
    intro s t (x,y)
    simp only [Prod.map]
    simp only [dSystemX.mapMult]
    simp only [dSystemY.mapMult]
  mapCont := by
    intro s
    exact Continuous.prodMap (dSystemX.mapCont s) (dSystemY.mapCont s)
}

/- Given an action of `S` on `X` and a semigroup homomorphism `φ: T → S`,
we get an action of `T` on `X` by setting `tx = (φ t)x` -/
def homDynamicalSystem
{S} [Semigroup S] [Nonempty S]
{T} [Semigroup T] [Nonempty T]
(φ : T → S) [hSemiHom : SemigroupHom φ]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
DynamicalSystem T X :=
{
  map := fun (t : T) ↦ dSystem.map (φ t)
  mapMult := by
    intro t1 t2 x
    rewrite [hSemiHom.hom_prop]
    rewrite [dSystem.mapMult]
    rfl
  mapCont := fun (t : T) ↦ dSystem.mapCont (φ t)
}

/-- A dynamical system satisfies `isSurjectiveSystem` if all
elements of the acting semigroup act by surjections -/
def isSurjectiveSystem
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :=
∀ s : S, Function.Surjective (dSystem.map s)

/-- A dynamical system satisfies `homeoSystem` if all
elements of the acting semigroup act by homeomorphisms -/
def isHomeoSystem
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :=
∀ s : S, IsHomeomorph (dSystem.map s)

end Structures

section Invariant_sets

variable {S : Type*} [Semigroup S] [Nonempty S]
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]

/-- A subset `A ⊆ X` is `S`-invariant if `SA ⊆ A` -/
def isInvariantSet
(dSystem : DynamicalSystem S X) (A : Set X) :
Prop :=
∀ s : S, Set.MapsTo (dSystem.map s) A A


/-- In dynamical system given by an action of a semigroup `S` on a space `X`,
the closure of an `S`-invariant set `A ⊆ X` is `S`-invariant -/
theorem closureOfInvIsInv
{dSystem : DynamicalSystem S X} {A : Set X}
(h : isInvariantSet dSystem A) :
isInvariantSet dSystem (closure A) :=
by
intro s
have h1 : (dSystem.map s) '' (closure A) = closure ((dSystem.map s) '' A) := by
  apply imageClosureIsClosureImage
  apply dSystem.mapCont
have h2 : Set.MapsTo (dSystem.map s) (closure A) (closure ((dSystem.map s) '' A)) := by
  rw [← h1]
  intro x hx
  use x
have h3 : dSystem.map s '' A ⊆ A := by
  specialize h s
  intro y hy
  rcases hy with ⟨w, hw⟩
  obtain ⟨hw1, hw2⟩ := hw
  specialize h hw1
  rw [← hw2]
  exact h
have h4 : dSystem.map s '' closure A ⊆ closure A := by
  rw [h1]
  apply closure_mono
  exact h3
unfold Set.MapsTo
intro z hz
apply h4
exact ⟨z, hz, rfl⟩

/-- The predicate that the set `Z ⊆ X` is a nonempty, compact,
T2 subset that is invariant under the action `dSystem.map` -/
def isNonemptyCompactT2InvariantSubset
(dSystem : DynamicalSystem S X) (Z : Set X) :
Prop :=
Z.Nonempty ∧ IsCompact Z ∧ T2Space Z ∧ isInvariantSet dSystem Z

/-- An intersection of `S`-invariant sets is `S`-invariant -/
theorem intersectionOfInvIsInv
(dSystem : DynamicalSystem S X)
{i : Set (Set X)} (h : ∀ A ∈ i, isInvariantSet dSystem A) :
isInvariantSet dSystem (i.sInter) := by
  intro s x hx
  rw [← Set.sInf_eq_sInter]
  simp only [sInf]
  intro A AinI
  rw [← Set.sInf_eq_sInter] at hx
  simp only [sInf] at hx
  have xinA : x ∈ A := hx A AinI
  unfold isInvariantSet Set.MapsTo at h
  exact h A AinI s xinA

end Invariant_sets

section Orbits

variable {S : Type*} [Semigroup S] [Nonempty S]
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]

/-- The orbit of a point `x` under the action of a semigroup `S` is the
image of `S` under the map `s ↦ sx` -/
def orbit
(dSystem : DynamicalSystem S X) (x : X) :
Set X :=
Set.range (fun s ↦ dSystem.map s x)

/-- The orbit of a set `Z ⊆ X` under the action of a semigroup `S` is the
image of `S` under the map `s ↦ sx` -/
def setOrbit
(dSystem : DynamicalSystem S X) (Z : Set X) :
Set X :=
Set.range (fun ((s,z) : S × Z) ↦ dSystem.map s z)

/-- The orbit closure of a point `x` under the action of a semigroup `S` is the
closure of the image of `S` under the map `s ↦ sx` -/
def orbitClosure
(dSystem : DynamicalSystem S X) (x : X) :
Set X :=
closure (orbit dSystem x)

/-- The orbit closure of a set `Z ⊆ X` under the action of a semigroup `S` is the
closure of the image of `S` under the map `s ↦ sZ` -/
def setOrbitClosure
(dSystem : DynamicalSystem S X) (Z : Set X) :
Set X :=
closure (setOrbit dSystem Z)

/-- The inverse orbit of a set -/
def inverseSetOrbit
(dSystem : DynamicalSystem S X) (Z : Set X) :
Set X :=
⋃ (s : S), (dSystem.map s) ⁻¹' Z

/-- The orbit along a set A ⊆ S -/
def setOrbitAlongASet
(dSystem : DynamicalSystem S X) (A : Set S) (Z : Set X) :
Set X :=
⋃ (s : A), (dSystem.map s) '' Z

/-- The inverse orbit along a set A ⊆ S -/
def inverseSetOrbitAlongASet
(dSystem : DynamicalSystem S X) (A : Set S) (Z : Set X) :
Set X :=
⋃ (s : A), (dSystem.map s) ⁻¹' Z

/-- If A ⊆ B, then the orbit closure of A is subset of the orbit closure of B -/
lemma monotoneSetOrbitClosure
(dSystem : DynamicalSystem S X) (A : Set X) (B : Set X) (hAB : A ⊆ B) :
setOrbitClosure dSystem A ⊆ setOrbitClosure dSystem B := by
  have h1 : setOrbit dSystem A ⊆ setOrbit dSystem B := by
    unfold setOrbit
    simp only
    unfold Set.range
    intro z hz
    simp only [Prod.exists, Subtype.exists, exists_prop, Set.mem_setOf_eq] at hz
    rcases hz with ⟨s, a, ha1, ha2⟩
    simp only [Prod.exists, Subtype.exists, exists_prop, Set.mem_setOf_eq]
    use s
    use a
    constructor
    · apply hAB
      exact ha1
    · exact ha2
  apply closure_mono
  exact h1

/-- When `S` acts on `X`, if `y` is in the orbit closure of `x` and `z` is
in the orbit closure of `y`, then `z` is in the orbit closure of `x`. -/
theorem orbitTransitivity
{dSystem : DynamicalSystem S X} {x y z : X}
(hyx : y ∈ orbitClosure dSystem x)
(hzy : z ∈ orbitClosure dSystem y) :
z ∈ orbitClosure dSystem x :=
by
  unfold orbitClosure
  simp only [mem_closure_iff]
  intro U hU hzU
  unfold orbitClosure at hzy
  simp only [mem_closure_iff] at hzy
  have UcapOrby : (U ∩ orbit dSystem y).Nonempty :=
    hzy U hU hzU
  rcases UcapOrby with ⟨u, hu1, hu2⟩
  unfold orbit at hu2
  simp only [Set.range] at hu2
  rcases hu2 with ⟨s, hs⟩
  have yInsInvCapU : y ∈ (dSystem.map s) ⁻¹' U := by
    simp only [Set.preimage]
    simp only [← hs] at hu1
    exact hu1
  have isOpenInvU : IsOpen ((dSystem.map s) ⁻¹' U) :=
    IsOpen.preimage (dSystem.mapCont s) hU
  unfold orbitClosure at hyx
  simp only [mem_closure_iff] at hyx
  have invUcapOrby : (((dSystem.map s) ⁻¹' U) ∩ orbit dSystem x).Nonempty :=
    hyx ((dSystem.map s) ⁻¹' U) isOpenInvU yInsInvCapU
  rcases invUcapOrby with ⟨v, hv1, hv2⟩
  unfold orbit at hv2
  simp only [Set.range] at hv2
  rcases hv2 with ⟨t, ht⟩
  have stxInU : dSystem.map (s * t) x ∈ U := by
    simp only [dSystem.mapMult]
    simp only [← ht] at hv1
    exact hv1
  simp only [orbit]
  have stxInRange :
  dSystem.map (s * t) x ∈ Set.range fun s ↦ dSystem.map s x := by
    simp only [Set.range]
    use s * t
  use dSystem.map (s * t) x
  exact ⟨stxInU, stxInRange⟩

/-- The `S`-orbit closure of a point `x` is an `S`-invariant subset of `X` -/
theorem orbClosIsInv
{dSystem : DynamicalSystem S X} {x : X} :
isInvariantSet dSystem (orbitClosure dSystem x) := by
have h1 : (orbitClosure dSystem x) = closure (orbit dSystem x) := rfl
have h2 : isInvariantSet (dSystem) (orbit dSystem x) := by
  intro r y hy
  rcases hy with ⟨s, hs⟩
  have h3 : dSystem.map s x = y := hs
  rw [<- h3]
  have h4 : dSystem.map (r * s) x = dSystem.map r (dSystem.map s x):= by
    simpa using dSystem.mapMult r s x
  rewrite [<- h4]
  unfold orbit
  exact ⟨r*s, rfl⟩
rw [h1]
apply closureOfInvIsInv
apply h2

/-- The `S`-orbit closure of a point `x` is a sub dynamical system of `DynamicalSystem S X` -/
theorem orbitClosureIsNonemptyCompactT2InvariantSubset
(dSystem : DynamicalSystem S X) (x : X) :
isNonemptyCompactT2InvariantSubset dSystem (orbitClosure dSystem x) :=
by
  unfold isNonemptyCompactT2InvariantSubset
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold orbitClosure
    unfold orbit
    exact Set.Nonempty.mono subset_closure (Set.range_nonempty (fun s ↦ dSystem.map s x))
  · exact IsClosed.isCompact (isClosed_closure)
  · infer_instance
  · exact orbClosIsInv

/-- If `y` is in the orbit closure of `x`, then `(y,y)` is in
the orbit closure of `(x,x)` under the diagonal action -/
lemma diagonalOrbitVisits
{dSystem : DynamicalSystem S X} (x y : X) (hy : y ∈ orbitClosure dSystem x) :
(y,y) ∈ orbitClosure (diagDynamicalSystem dSystem dSystem) (x,x) :=
by
  unfold orbitClosure
  unfold orbitClosure at hy
  simp only [mem_closure_iff]
  simp only [mem_closure_iff] at hy
  intro U UOpen yyInU
  have symmNhd : ∃ V, IsOpen V ∧ y ∈ V ∧ V ×ˢ V ⊆ U :=
    exists_nhds_square (UOpen.mem_nhds yyInU)
  rcases symmNhd with ⟨V,VOpen,yInV,prodVInU⟩
  have orbitOfxVisitsV1 := hy V VOpen yInV
  rcases orbitOfxVisitsV1 with ⟨z,zInV,zInOrbit⟩
  have zzInU : (z,z) ∈ U := prodVInU ⟨zInV,zInV⟩
  have zzInOrbitxx : (z,z) ∈ orbit (diagDynamicalSystem dSystem dSystem) (x,x) :=
    by
      unfold orbit at zInOrbit
      rcases zInOrbit with ⟨s,sxIsz⟩
      use s
      unfold diagDynamicalSystem
      simp only [Prod.map_apply, Prod.mk.injEq, and_self]
      exact sxIsz
      --exact ⟨sxIsz,sxIsz⟩
  refine ⟨(z,z),?_⟩
  exact ⟨zzInU,zzInOrbitxx⟩

end Orbits

section Subsystems

/- Implemenetation note: SubDynamicalSystem is a class since given the parameters
(a dynamical system and a non-empty, compact, invariant set), it is canonically determined -/

/- A sub (topological) dynamical system of a topological dynmical system given by
a semigroup `S` acting on `X` is a nonempty, compact, invariant subset of `X`
together with the action by `S`.
def isSubDynamicalSystem
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (Z : Set X) :
Prop :=
Z.Nonempty ∧ IsCompact Z ∧ T2Space Z ∧ isInvariantSet dSystem.toSemigroupAction Z-/

-- UNHAPPY
/-- A sub (topological) dynamical system of a topological dynmical system given by
a semigroup `S` acting on `X` is a nonempty, compact, invariant subset of `X`
together with the action by `S`. -/
class SubDynamicalSystem
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (Z : Set X) where
  carrier_inv : isInvariantSet dSystem Z
  carrier_nonempty := Z.Nonempty
  carrier_compact := IsCompact Z

/- Given a system of `S` acting on `X` and a subset `Z` satisfying
 `isNonemptyCompactT2InvariantSubset dSystem Z`, create a term of type `DynamicalSystem S Z` -/
/-def fromSubsystemToSystem
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X)
{Z : Set X} [CompactSpace ↑Z] [Nonempty ↑Z]
(isSubsys : isNonemptyCompactT2InvariantSubset dSystem Z) :
DynamicalSystem S ↑Z :=
{
  toFun := by
    intro s ⟨z,hz⟩
    unfold isNonemptyCompactT2InvariantSubset at isSubsys
    unfold isInvariantSet at isSubsys
    rcases isSubsys with ⟨hNon,hCmct,hT2,hInv⟩
    exact ⟨(dSystem.toFun s z : X), hInv s z hz⟩
  map_mult' := by
    intro s t ⟨z,hz⟩
    sorry
  cont' := by sorry
}-/

/-- Given a system of `S` acting on `X` and a nonempty, compact, T2, invariant `Z ⊆ X`,
create a term of type `DynamicalSystem S ↑Z`, where note that `↑Z` is the type
corresponding to membership in `Z` (tuples of term of type `X` and proof of
membership in `Z`) -/
def fromNonemptyCompactT2InvariantSubsetToSystem
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X)
{Z : Set X} (isInv : isNonemptyCompactT2InvariantSubset dSystem Z) :
let _ : Nonempty ↥Z := (fun ⟨x, hx⟩ => ⟨⟨x, hx⟩⟩) isInv.1
let _ : CompactSpace ↥Z := isCompact_iff_compactSpace.mp isInv.2.1
DynamicalSystem S ↥Z :=
by
  letI : Nonempty ↥Z := (fun ⟨x, hx⟩ => ⟨⟨x, hx⟩⟩) isInv.1
  letI : CompactSpace ↥Z := isCompact_iff_compactSpace.mp isInv.2.1
  exact
  {
    map := (fun (s : S) ↦ Set.MapsTo.restrict (dSystem.map s) Z Z (isInv.2.2.2 s))
    mapMult := by
      intro s t ⟨z,hz⟩
      unfold Set.MapsTo.restrict Subtype.map
      simp only [dSystem.mapMult s]
    mapCont := by
      intro s
      exact Continuous.restrict (isInv.2.2.2 s) (dSystem.mapCont s)
  }

-- Still working on this definition.  Not sure how to make lean see that
-- the compactness of Z will come from the assumption isNonemptyCompactT2InvariantSubset dSystem Z
/-def makeDynamicalSystemFromSub {S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (Z : Set X)
{hZ : isNonemptyCompactT2InvariantSubset dSystem Z} : DynamicalSystem S Z := sorry

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

end Subsystems

section Relations_as_sets

/-- setToRelation sends a set `s : Set (X × X)` to a relation `X → X → Prop` -/
def setToRelation
{X : Type*} (s : Set (X × X)) :
X → X → Prop :=
fun x y => (x, y) ∈ s

-- We use Std.Refl, Std.Symm, and IsTrans before,
-- but these classes have been deprecated since March 2026
-- So I changed to Reflexive, Symmetric, and Transitive
/-- A set `s : Set (X × X)` is reflexive if for all `x : X`, `(x,x) ∈ s` -/
def isReflexive
{X : Type*} (s : Set (X × X)) :
Prop :=
Reflexive (setToRelation s)

/-- A set `s : Set (X × X)` is symmetric if for all `x y : X`, `(x,y) ∈ s → (y,x) ∈ s` -/
def isSymmetric
{X : Type*} (s : Set (X × X)) :
Prop :=
Symmetric (setToRelation s)

/-- A set `s : Set (X × X)` is transitive if for all `x y z : X`,
`(x,y) ∈ s ∧ (y,z) ∈ s → (x,z) ∈ s` -/
def isTransitive
{X : Type*} (s : Set (X × X)) :
Prop :=
Transitive (setToRelation s)

/-- A set `s : Set (X × X)` is an equivalence relation if it is reflexive, symmetric,
and transitive -/
def isEquivalenceRelation
{X : Type*} (s : Set (X × X)) :
Prop :=
Equivalence (setToRelation s)
--isReflexive s ∧ isSymmetric s ∧ isTransitive s

/-- A relation is an equivalence relation if, as a set, it is reflexive,
symmetric, and transitive -/
theorem equivalenceRelationSetForm
{X : Type*} (s : Set (X × X)) :
Equivalence (setToRelation s) ↔ isReflexive s ∧ isSymmetric s ∧ isTransitive s := by
constructor
· intro h
  rcases h with ⟨h1, h2, h3⟩
  constructor
  · exact h1
  constructor
  · intro x y hxy
    specialize h2 hxy
    exact h2
  intro x y z hxyz1 hxyz2
  specialize h3 hxyz1 hxyz2
  exact h3
intro h
rcases h with ⟨h1, h2, h3⟩
constructor
· exact h1
· intro x y hxy
  specialize h2 hxy
  exact h2
intro x y z hxyz1 hxyz2
exact h3 hxyz1 hxyz2

/- The following exists in Mathlib as an instance, but we have some friction
using that because of our treating relations as sets -/
/-- The quotient of a nonempty set by an equivalence relation is nonempty -/
theorem nonemptyQuotient
(X : Type*) [Nonempty X]
{I : Set (X × X)} (hIEquiv : Equivalence (setToRelation I)) :
Nonempty (Quotient ⟨setToRelation I, hIEquiv⟩) := by
have h1 : ∃ x : X, True := by
  simp
rcases h1 with ⟨x, hx⟩
let y := Quotient.mk ⟨setToRelation I, hIEquiv⟩ x
exact ⟨y⟩

end Relations_as_sets


section Factor_maps_and_ICERS

/- DGG: I am playing around with different definition structures in this section
until we land on one that works nicely. -/

-- Depracated in favor of isEquivariant
/- A map between the phase spaces of two dynamical systems is
interwining if `π ∘ s = s ∘ π`. (See MulActionHom for precedent) -/
/- def isIntertwining
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemX : DynamicalSystem S X)
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemY : DynamicalSystem S Y)
(π : X → Y) :
Prop :=
∀ x : X, ∀ s : S, π (dSystemX.map s x) = dSystemY.map s (π x) -/

/-- Given actions `S → X → X` and `S → Y → Y`, a map `π : X → Y` is
`S`-equivariant if it intertwines the actions -/
def isEquivariant
{S : Type*} [Semigroup S] {X Y : Type*}
(actionMapX : S → X → X) (actionMapY : S → Y → Y) (π : X → Y) :
Prop :=
∀ (s : S), (actionMapY s) ∘ π = π ∘ (actionMapX s)

/-- Given dynamical systems `X` and `Y`, a map `π : X → Y` is a factor map
if it is a continuous, equivariant surjection -/
def isFactorMap
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemX : DynamicalSystem S X)
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemY : DynamicalSystem S Y)
(π : X → Y) :
Prop :=
Continuous π ∧ Function.Surjective π ∧ isEquivariant dSystemX.map dSystemY.map π

/-- Given a map f : X → Y, the map relation is the subset of X × X
consisting of those points (x1,x2) such that f(x1) = f(x2) -/
def mapRelation
{X Y : Type*} (f : X → Y) :
Set (X × X) :=
(Prod.map f f) ⁻¹' (Set.diagonal Y)

/-- The definition of a dynamical system Y being a factor of a dynamical system X -/
def isFactor
{S} [Semigroup S] [Nonempty S]
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemY : DynamicalSystem S Y)
(dSystemX : DynamicalSystem S X) :
Prop :=
∃ (π : X → Y), isFactorMap dSystemX dSystemY π

set_option linter.unusedVariables false

/- The image of a nonempty, compact, T2, `S`-invariant set `Z ⊆ X` under
a continuous, intertwining map `π: X → Y` as a dynamical system -/
def imageDynamicalSystem
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemX : DynamicalSystem S X)
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemY : DynamicalSystem S Y)
(π : X → Y) {hπCont : Continuous π} {hπInt : isEquivariant dSystemX.map dSystemY.map π}
{Z : Set X} [CompactSpace ↑Z] [Nonempty ↑Z]
(hZisInv : isInvariantSet dSystemX Z) [CompactSpace ↑(π '' Z)] :
DynamicalSystem S ↑(π '' Z) :=
have hMapsto : ∀ s : S, Set.MapsTo (dSystemY.map s) (π '' Z) (π '' Z) := by
  intro s y hy
  simp only [Set.mem_image] at hy
  rcases hy with ⟨x, hx1, hx2⟩
  rw [<- hx2]
  unfold isEquivariant at hπInt
  specialize hπInt s
  have h1 : (dSystemY.map s ∘ π) x = (π ∘ dSystemX.map s) x := by
    apply congrFun
    exact hπInt
  have h2 : dSystemY.map s (π x) = π (dSystemX.map s x) := by
    exact h1
  rw [h2]
  simp only [Set.mem_image]
  use dSystemX.map s x
  constructor
  · unfold isInvariantSet at hZisInv
    specialize hZisInv s
    unfold Set.MapsTo at hZisInv
    specialize hZisInv hx1
    exact hZisInv
  · rfl
{
  map := fun s ↦ Set.MapsTo.restrict (dSystemY.map s) (π '' Z) (π '' Z) (hMapsto s)
  mapMult := by
    intro s1 s2 y
    apply Subtype.ext
    have hYMapMult := dSystemY.mapMult
    specialize hYMapMult s1 s2 y
    exact hYMapMult
  mapCont := by
    have hYCont := dSystemY.mapCont
    intro s
    specialize hYCont s
    apply Continuous.restrict
    exact hYCont
}

set_option linter.unusedVariables true

/- The image of a nonempty, compact, T2, `S`-invariant set `Z ⊆ X` under
a continuous, intertwining map `π: X → Y` is a nonempty, compact, T2,
`S`-invariant subset of `Y` -/
/- Depracated in favor of imageSystem -/
/- theorem contIntertwiningImageOfNonemptyComT2InvIsNonemptyComT2Inv
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemX : DynamicalSystem S X)
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemY : DynamicalSystem S Y)
(π : X → Y) {hπCont : Continuous π} {hπInt : isIntertwining dSystemX dSystemY π}
{Z : Set X} [CompactSpace ↑Z] [Nonempty ↑Z]
(hZisInv : isInvariantSet dSystemX Z) :
isNonemptyCompactT2InvariantSubset dSystemY (π '' Z)
:= by sorry -/

/-- The restriction of a continuous, intertwining map to a nonempty, compact,
T2, invariant subset `Z ⊆ X` is a factor map from `Z` as an `S`-system to its
image under the map as an `S`-system -/
theorem contIntertwineRestrictionIsFactorMap
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemX : DynamicalSystem S X)
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemY : DynamicalSystem S Y)
(π : X → Y) {hπCont : Continuous π} {hπInt : isEquivariant dSystemX.map dSystemY.map π}
{Z : Set X} [CompactSpace ↑Z] [Nonempty ↑Z]
(hZisInv : isNonemptyCompactT2InvariantSubset dSystemX Z) [CompactSpace ↑(π '' Z)] :
isFactorMap (fromNonemptyCompactT2InvariantSubsetToSystem dSystemX hZisInv)
(imageDynamicalSystem dSystemX dSystemY π (hπInt := hπInt) (hπCont := hπCont) hZisInv.2.2.2)
(Set.MapsTo.restrict π Z (π '' Z) (Set.mapsTo_image π Z)) := by
constructor
· apply Continuous.restrict
  exact hπCont
constructor
· simp only [Set.MapsTo.restrict_surjective_iff]
  apply Set.surjOn_image
unfold isEquivariant
intro s
specialize hπInt s
ext z
simp only [Function.comp_apply, Set.MapsTo.val_restrict_apply]
have hz1 : dSystemY.map s (π z) = π (dSystemX.map s z) := by
  apply congrFun hπInt
have h2 : π ↑((fromNonemptyCompactT2InvariantSubsetToSystem dSystemX hZisInv).map s z) =
  π (dSystemX.map s z) := by
  rfl
rw [h2, <- hz1]
unfold imageDynamicalSystem
simp

/-- Given a dynamical system `dSystem : DynamicalSystem S X`, an ICER
(for dSystem) is an invariant (under the diagonal action of `S`),
closed equivalence relation -/
def isICER
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (I : Set (X × X)) :
Prop :=
isInvariantSet (diagDynamicalSystem dSystem dSystem) I ∧ IsClosed I ∧
isEquivalenceRelation I

/- Testing this out -/
/- class ICER
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (I : Set (X × X)) where
  ICER_prop :=
    isInvariantSet (diagDynamicalSystem dSystem dSystem) I ∧
    IsClosed I ∧
    isEquivalenceRelation I -/

/-- An arbitrary intersection of ICERs (for a given system) is an ICER
(for that system) -/
theorem intersectionOfICERsIsICER
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) {c : Set (Set (X × X))}
(hc : ∀ (I : Set (X × X)), I ∈ c → isICER dSystem I) :
isICER dSystem (⋂₀ c) := by
have hc1 : ∀ I ∈ c, isInvariantSet (diagDynamicalSystem dSystem dSystem) I := by
  intro I hI
  specialize hc I hI
  rcases hc with ⟨hc1, hc2, hc3⟩
  exact hc1
have hc2 : ∀ I ∈ c, IsClosed I := by
  intro I hI
  specialize hc I hI
  rcases hc with ⟨hc1, hc2, hc3⟩
  exact hc2
have hc3 : ∀ I ∈ c, isEquivalenceRelation I := by
  intro I hI
  specialize hc I hI
  rcases hc with ⟨hc1, hc2, hc3⟩
  exact hc3
unfold isICER
constructor
· unfold isInvariantSet
  intro s x hx
  simp only [Set.mem_sInter]
  intro I hI
  simp only [Set.mem_sInter] at hx
  specialize hx I hI
  specialize hc1 I hI
  unfold isInvariantSet at hc1
  specialize hc1 s
  specialize hc1 hx
  exact hc1
constructor
· apply isClosed_sInter
  intro I hI
  specialize hc2 I hI
  exact hc2
unfold isEquivalenceRelation
apply (equivalenceRelationSetForm (⋂₀ c)).mpr
constructor
· intro x I hI
  specialize hc3 I hI
  rcases hc3 with ⟨hc3a, hc3b, hc3c⟩
  specialize hc3a x
  exact hc3a
constructor
· intro x y hxy I hI
  specialize hc3 I hI
  rcases hc3 with ⟨hc3a, hc3b, hc3c⟩
  specialize hxy I hI
  apply hc3b hxy
intro x y z hxy hyz I hI
specialize hxy I hI
specialize hyz I hI
specialize hc3 I hI
rcases hc3 with ⟨hc3a, hc3b, hc3c⟩
apply hc3c hxy hyz

/-- If `X` is a compact Hausdorff topological space and `I` is a closed
equivalence relation on `X^2`, then `X/I` is a Hausdorff topological space -/
theorem quotientOfCompactT2ByClosedIsT2
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{I : Set (X × X)} (hIClosed : IsClosed I)
(hIEquiv : Equivalence (setToRelation I)) :
T2Space (Quotient ⟨setToRelation I, hIEquiv⟩) := by
let f := Quotient.mk ⟨setToRelation I, hIEquiv⟩
have hfSurjective : Function.Surjective f := by
    exact Quot.mk_surjective
have hfCont : Continuous f := by
  exact continuous_quot_mk
have hfClosed : IsClosedMap f := by
  unfold IsClosedMap
  intro K hK
  have hPreImageRe : f ⁻¹' (f '' K) = Prod.fst '' ((Set.univ ×ˢ K) ∩ I) := by
    ext x
    constructor
    · intro hx
      simp only [Set.mem_preimage, Set.mem_image] at hx
      rcases hx with ⟨k, hk1, hk2⟩
      have hkx : (setToRelation I) k x := by
        apply (Equivalence.quot_mk_eq_iff hIEquiv k x).mp
        exact hk2
      have hxk : (setToRelation I) x k := by
        apply Equivalence.symmetric
        · exact hIEquiv
        · exact hkx
      have hxkRe : (x, k) ∈ I := by
        unfold setToRelation at hxk
        exact hxk
      simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and,
        Prod.exists, exists_and_right, exists_eq_right]
      use k
    · intro hx
      simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and,
        Prod.exists, exists_and_right, exists_eq_right] at hx
      rcases hx with ⟨k, hk1, hk2⟩
      simp only [Set.mem_preimage, Set.mem_image]
      use k
      constructor
      · exact hk1
      · simp only [f]
        apply (Equivalence.quot_mk_eq_iff hIEquiv k x).mpr
        apply Equivalence.symmetric
        · exact hIEquiv
        · unfold setToRelation
          exact hk2
  have hXKClosed : IsClosed ((Set.univ : Set X) ×ˢ K) := by
    exact IsClosed.prod isClosed_univ hK
  have hXKIClosed : IsClosed ((Set.univ ×ˢ K) ∩ I) := by
    apply IsClosed.inter
    · exact hXKClosed
    · exact hIClosed
  have hXKICompact : IsCompact ((Set.univ ×ˢ K) ∩ I) := by
    apply IsClosed.isCompact
    exact hXKIClosed
  have ffKCompact : IsCompact (f ⁻¹' (f '' K)) := by
    rw [hPreImageRe]
    apply IsCompact.image
    · exact hXKICompact
    · continuity
  have hPreImageClosed : IsClosed (f ⁻¹' (f '' K)) := by
    apply IsCompact.isClosed
    exact ffKCompact
  have hfQuotientMap : Topology.IsQuotientMap f := by
    simp only [f]
    exact isQuotientMap_quot_mk
  apply (Topology.IsQuotientMap.isClosed_preimage hfQuotientMap).mp
  exact hPreImageClosed
apply (t2Space_iff (Quotient ⟨setToRelation I, hIEquiv⟩)).mpr
intro z w hzw
let Ez := f ⁻¹' {z}
let Ew := f ⁻¹' {w}
have hEzClosed : IsClosed Ez := by
  specialize hfSurjective z
  rcases hfSurjective with ⟨a, ha⟩
  have hEzReDef : Ez = {x : X | (x, a) ∈ I} := by
    simp only [Ez]
    rw [<- ha]
    simp only [f]
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    apply Equivalence.quot_mk_eq_iff hIEquiv
  let g : X → X × X := fun x ↦ (x, a)
  have hEzReDef2 : Ez = g ⁻¹' I := by
    simp only [g]
    rw [hEzReDef]
    rfl
  have hgCont : Continuous g := by
    continuity
  rw [hEzReDef2]
  apply IsClosed.preimage
  · exact hgCont
  · exact hIClosed
have hEwClosed : IsClosed Ew := by
  specialize hfSurjective w
  rcases hfSurjective with ⟨a, ha⟩
  have hEwReDef : Ew = {x : X | (x, a) ∈ I} := by
    simp only [Ew]
    rw [<- ha]
    simp only [f]
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    apply Equivalence.quot_mk_eq_iff hIEquiv
  let g : X → X × X := fun x ↦ (x, a)
  have hgCont : Continuous g := by
    continuity
  have hEwReDef2 : Ew = g ⁻¹' I := by
    simp only [g]
    rw [hEwReDef]
    rfl
  rw [hEwReDef2]
  apply IsClosed.preimage
  · exact hgCont
  · exact hIClosed
have hEzwDisjoint : Disjoint Ez Ew := by
  simp only [Ez, Ew]
  apply Set.disjoint_left.mpr
  intro a ha
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  rw [ha]
  exact hzw
letI hXNormal : NormalSpace X := by infer_instance
have hEzwSeparated : SeparatedNhds Ez Ew := by
  exact normal_separation hEzClosed hEwClosed hEzwDisjoint
rcases hEzwSeparated with ⟨U, V, hU1, hV1, hU2, hV2, hUV⟩
let u := (f '' Uᶜ)ᶜ
let v := (f '' Vᶜ)ᶜ
use u
use v
constructor
· simp only [isOpen_compl_iff, u]
  unfold IsClosedMap at hfClosed
  specialize hfClosed Uᶜ
  have hUcClosed : IsClosed Uᶜ := by
    simp only [isClosed_compl_iff]
    exact hU1
  apply hfClosed hUcClosed
constructor
· simp only [isOpen_compl_iff, v]
  unfold IsClosedMap at hfClosed
  specialize hfClosed Vᶜ
  have hVcClosed : IsClosed Vᶜ := by
    simp only [isClosed_compl_iff]
    exact hV1
  apply hfClosed hVcClosed
constructor
· simp only [Set.mem_compl_iff, Set.mem_image, not_exists, not_and, u]
  intro x hx
  have hxEz : x ∉ Ez := by
    by_contra
    have hxU : x ∈ U := by
      apply hU2
      exact this
    exact hx hxU
  unfold Ez at hxEz
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hxEz
  exact hxEz
constructor
· simp only [Set.mem_compl_iff, Set.mem_image, not_exists, not_and, v]
  intro x hx
  have hxEw : x ∉ Ew := by
    by_contra
    have hxV : x ∈ V := by
      apply hV2
      exact this
    exact hx hxV
  unfold Ew at hxEw
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hxEw
  · exact hxEw
· simp only [u, v]
  by_contra
  have hNotDisjoint : ∃ y, y ∈ (f '' Uᶜ)ᶜ ∧ y ∈ (f '' Vᶜ)ᶜ := by
    apply Set.not_disjoint_iff.mp
    exact this
  rcases hNotDisjoint with ⟨y, hy1, hy2⟩
  simp only [Set.mem_compl_iff, Set.mem_image, not_exists, not_and] at hy1
  simp only [Set.mem_compl_iff, Set.mem_image, not_exists, not_and] at hy2
  specialize hfSurjective y
  rcases hfSurjective with ⟨a, ha⟩
  have haU : a ∈ U := by
    by_contra
    specialize hy1 a this
    exact hy1 ha
  have haV : a ∈ V := by
    by_contra
    specialize hy2 a this
    exact hy2 ha
  have hUVNotDisjoint : ¬ Disjoint U V := by
    apply Set.not_disjoint_iff.mpr
    use a
  exact hUVNotDisjoint hUV

/- instance {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{I : Set (X × X)} {hIClosed : IsClosed I}
{hIEquiv : Equivalence (setToRelation I)} :
T2Space (Quotient ⟨setToRelation I, hIEquiv⟩) :=
by sorry

instance {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{I : Set (X × X)} {hIClosed : IsClosed I}
{hIEquiv : Equivalence (setToRelation I)} :
CompactSpace (Quotient ⟨setToRelation I, hIEquiv⟩) :=
by infer_instance

instance {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{I : Set (X × X)} {hIClosed : IsClosed I}
{hIEquiv : Equivalence (setToRelation I)} :
Nonempty (Quotient ⟨setToRelation I, hIEquiv⟩) := nonemptyQuotient X hIEquiv -/

/-- Given a dynamical system of `S` acting on `X` and an ICER `I`,
the quotient dynamical system has phase space `X/I` with an `S` action
described by `s[x] = [sx]` -/
def quotientDynamicalSystem
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [hT2 : T2Space X] [hNonempty : Nonempty X]
(dSystem : DynamicalSystem S X)
{I : Set (X × X)} (hI : isICER dSystem I) :
let Y := Quotient ⟨setToRelation I, hI.2.2⟩
have : Nonempty Y :=
  nonemptyQuotient X hI.2.2
have : T2Space Y :=
  quotientOfCompactT2ByClosedIsT2 hI.2.1 hI.2.2
DynamicalSystem S (Quotient ⟨setToRelation I, hI.2.2⟩) := by
let Y := Quotient ⟨setToRelation I, hI.2.2⟩
have : Nonempty Y :=
  nonemptyQuotient X hI.2.2
have : T2Space Y :=
  quotientOfCompactT2ByClosedIsT2 hI.2.1 hI.2.2
unfold isICER at hI
rcases hI with ⟨hIInvariant, hIClosed, hIEquiv⟩
let π := Quotient.mk ⟨setToRelation I, hIEquiv⟩
let f : S → X → Y := fun s ↦ π ∘ (dSystem.map s)
have hRespect : ∀ s : S, ∀ x y : X, (setToRelation I) x y → (f s) x = (f s) y := by
  intro s x y hxy
  simp only [Function.comp_apply, f]
  apply (Equivalence.quot_mk_eq_iff hIEquiv (dSystem.map s x) (dSystem.map s y)).mpr
  unfold setToRelation
  unfold setToRelation at hxy
  unfold isInvariantSet at hIInvariant
  specialize hIInvariant s
  unfold Set.MapsTo at hIInvariant
  specialize hIInvariant hxy
  exact hIInvariant
exact
{
  map := fun s ↦ Quotient.lift (f s) (hRespect s)
  mapMult := by
    intro s1 s2 y
    simp only [f]
    refine Quotient.inductionOn y ?_
    intro x
    simp only [Quotient.lift]
    have hs12 : dSystem.map (s1 * s2) = (dSystem.map s1) ∘ (dSystem.map s2) := by
      ext t
      exact (dSystem.mapMult s1 s2 t)
    simp [hs12]
    rfl
  mapCont := by
    intro s
    apply Continuous.quotient_lift
    simp only [f]
    have hπCont : Continuous π := by
      exact continuous_quot_mk
    have hsCont : Continuous (dSystem.map s) := by
      exact (dSystem.mapCont s)
    exact Continuous.comp hπCont hsCont
}

-- (hT2 := quotientOfCompactT2ByClosedIsT2 hI.2.1 hI.2.2)
-- (hNonempty := nonemptyQuotient X hI.2.2)

-- The follow code is part of the debugging effort around quotientMapIsEquivariant
/- variable {S : Type*} [Semigroup S] [Nonempty S]
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [hT2 : T2Space X]
[hNonempty : Nonempty X]
variable (dSystem : DynamicalSystem S X)
variable {I : Set (X × X)} (hI : isICER dSystem I)

set_option pp.explicit true
#print quotientDynamicalSystem
#check quotientDynamicalSystem dSystem hI
#check (quotientDynamicalSystem dSystem hI).map -/

/- Given a dynamical system of `S` acting on `X` and an ICER `I`,
the quotient map `X → X/I` is S-equivariant -/
/- theorem quotientMapIsEquivariant
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X)
{I : Set (X × X)} (hI : isICER dSystem I) :
isEquivariant dSystem.map
(quotientDynamicalSystem dSystem hI).map
  (Quotient.mk ⟨setToRelation I, hI.2.2⟩) :=
by sorry -/


/-- Given a dynamical system of `S` acting on `X` and an ICER `I`,
the quotient map `X → X/I` is a factor map of S-systems -/
-- To fix this, could pass T2 and Nonempty arguments explicitly to isFactorMap
theorem quotientMapIsFactorMap
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X)
{I : Set (X × X)} (hI : isICER dSystem I) :
have : Nonempty (Quotient ⟨setToRelation I, hI.2.2⟩) :=
  nonemptyQuotient X hI.2.2
have : T2Space (Quotient ⟨setToRelation I, hI.2.2⟩) :=
  quotientOfCompactT2ByClosedIsT2 hI.2.1 hI.2.2
isFactorMap dSystem (quotientDynamicalSystem dSystem hI)
  (Quotient.mk ⟨setToRelation I, hI.2.2⟩) := by
rcases hI with ⟨hIInvariant, hIClosed, hIEquiv⟩
constructor
· apply continuous_quotient_mk'
constructor
· intro b
  have h1 : ∃ a : X, Quotient.mk ⟨setToRelation I, hIEquiv⟩ a = b := by
    apply Quotient.exists_rep
  obtain ⟨a, ha⟩ := h1
  use a
· intro s
  ext x
  simp
  rfl

/-- Given a continuous, equivariant map `π : X → Y` between two systems and
a nonempty, compact, T2, `S`-invariant set `A ⊆ X`, the image `πA` is nonempty,
compact, T2, `S`-invariant -/
theorem imageOfSubsystemIsSubsystem
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemX : DynamicalSystem S X)
{Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemY : DynamicalSystem S Y)
(π : X → Y) {hπ : Continuous π} {hEqui : isEquivariant dSystemX.map dSystemY.map π}
(A : Set X) {hA : isNonemptyCompactT2InvariantSubset dSystemX A} :
isNonemptyCompactT2InvariantSubset dSystemY (π '' A) := by
rcases hA with ⟨hA1, hA2, hA3, hA4⟩
constructor
· rcases hA1 with ⟨x, hx⟩
  have hx1 : π x ∈ π '' A := by
    use x
  exact ⟨π x, hx1⟩
constructor
· apply IsCompact.image hA2 hπ
constructor
· infer_instance
unfold isInvariantSet
intro s
unfold isInvariantSet at hA4
specialize hA4 s
unfold Set.MapsTo
intro y hy
rcases hy with ⟨x, hx1, hx2⟩
rw [<- hx2]
unfold isEquivariant at hEqui
specialize hEqui s
have hEquiSpec :  dSystemY.map s (π x) = π (dSystemX.map s x) := by
  apply congrFun hEqui
rw [hEquiSpec]
unfold Set.MapsTo at hA4
specialize hA4 hx1
simp only [Set.mem_image]
use (dSystemX.map s x)

end Factor_maps_and_ICERS

section Return_time_sets

variable {S : Type*} [Semigroup S] [Nonempty S]
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]

/-- The set of times `s ∈ S` for which the point `x ∈ X` visits the set `U ⊆ X` -/
def visitTimeSet
(dSystem : DynamicalSystem S X) (x : X) (U : Set X) :
Set S :=
(fun (s : S) ↦ dSystem.map s x) ⁻¹' U

/-- The set of times `s ∈ S` for which the point `x ∈ X` visits the set `U ⊆ X` -/
def setVisitTimeSet
(dSystem : DynamicalSystem S X) (U V : Set X) :
Set S :=
{s : S | (((dSystem.map s) '' U) ∩ V).Nonempty}

/-- The set of times `s ∈ S` for which the point `x ∈ X` visits the set
`s^{-1} U` is `s^{-1} R(x,U)` -/
theorem visitsToPreimages
(dSystem : DynamicalSystem S X) (x : X) (U : Set X) (s : S) :
(s * ·) ⁻¹' (visitTimeSet dSystem x U) =
visitTimeSet dSystem x ((dSystem.map s) ⁻¹' U) := by
have h1 : (s * ·) ⁻¹' (visitTimeSet dSystem x U)
⊆ visitTimeSet dSystem x ((dSystem.map s) ⁻¹' U) := by
  intro r hr
  have hr1 : s * r ∈ visitTimeSet dSystem x U := by
    simpa
  have hr2 : dSystem.map (s * r) x ∈ U := by
    simpa
  have hr21 : dSystem.map s (dSystem.map r x) = dSystem.map (s * r) x := by
    simp only [dSystem.mapMult s r x]
  have hr3 : dSystem.map r x ∈ dSystem.map s ⁻¹' U := by
    simp only [Set.mem_preimage]
    rw [hr21]
    apply hr2
  simpa
have h2 : visitTimeSet dSystem x ((dSystem.map s) ⁻¹' U) ⊆
(s * ·) ⁻¹' (visitTimeSet dSystem x U) := by
  intro r hr
  have hr1 : dSystem.map r x ∈ (dSystem.map s ⁻¹' U) := by
    simpa
  have hr2 : dSystem.map s (dSystem.map r x) ∈ U := by
    simpa
  have hr3 : dSystem.map s (dSystem.map r x) = dSystem.map (s * r) x := by
    simp only [dSystem.mapMult s r x]
  have hr4 : dSystem.map (s*r) x ∈ U := by
    rw [<- hr3]
    exact hr2
  apply hr4
exact subset_antisymm h1 h2

/-- The set `R(x,∩_i U_i)` is equal to `∩_i R(x,U_i)` -/
theorem visitToInter
{dSystem : DynamicalSystem S X}
(x : X) {I} (f : I → Set X) :
visitTimeSet dSystem x (⋂ i : I, f i) =
⋂ i : I, (visitTimeSet dSystem x (f i)) := by
have h1 : visitTimeSet dSystem x (⋂ i : I, f i) ⊆
⋂ i : I, (visitTimeSet dSystem x (f i)) := by
  intro s hs
  have h11 : dSystem.map s x ∈ (⋂ i : I, f i) := by
    exact hs
  have h12 : ∀ i : I, dSystem.map s x ∈ f i := by
    intro i
    apply h11
    simp
  simp only [Set.mem_iInter]
  apply h12
have h2 : ⋂ i : I, (visitTimeSet dSystem x (f i)) ⊆
visitTimeSet dSystem x (⋂ i : I, f i) := by
  intro s hs
  have h21 : ∀ i : I, s ∈ visitTimeSet dSystem x (f i) := by
    simpa using hs
  have h22 : ∀ i : I, dSystem.map s x ∈ f i := by
    apply h21
  have h23 : dSystem.map s x ∈ (⋂ i : I, f i) := by
    simpa using h22
  simpa
exact subset_antisymm h1 h2

/-- The set `R(x,∪_i U_i)` is equal to `∪_i R(x,U_i)` -/
theorem visitToUnion
{dSystem : DynamicalSystem S X}
(x : X) {I} (f : I → Set X) :
visitTimeSet dSystem x (⋃ i : I, f i) =
⋃ i : I, (visitTimeSet dSystem x (f i)) := by
have h1 : visitTimeSet dSystem x (⋃ i : I, f i) ⊆
⋃ i : I, (visitTimeSet dSystem x (f i)) := by
  intro s hs
  have h11 : dSystem.map s x ∈ (⋃ i : I, f i) := by
    exact hs
  have h12 : ∃ i : I, dSystem.map s x ∈ f i := by
    simpa using h11
  simp only [Set.mem_iUnion]
  apply h12
have h2 : ⋃ i : I, (visitTimeSet dSystem x (f i)) ⊆
visitTimeSet dSystem x (⋃ i : I, f i) := by
  intro s hs
  have h21 : ∃ i : I, s ∈ visitTimeSet dSystem x (f i) := by
    simpa using hs
  have h22 : ∃ i : I, dSystem.map s x ∈ f i := by
    apply h21
  have h23 : dSystem.map s x ∈ (⋃ i : I, f i) := by
    simpa using h22
  simpa
exact subset_antisymm h1 h2

/-- Given `U1 ⊆ U2`, `R(x,U1) ⊆ R(x,U2)` -/
theorem visitTimesMono
(dSystem : DynamicalSystem S X)
(x : X) {U V : Set X} (hMono : U ⊆ V) :
visitTimeSet dSystem x U ⊆ visitTimeSet dSystem x V := by
intro s hs
have h1 : dSystem.map s x ∈ U := by
  simpa using hs
have h2 : dSystem.map s x ∈ V := by
  apply hMono h1
simpa

/-- The time of visits of a point `(x,y)` to `U × V` under the diagonal action is
the intersection of `R(x,U)` and `R(y,V)` -/
theorem visitsToProductsUnderDiagonal
{Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemX : DynamicalSystem S X) (x : X) (U : Set X)
(dSystemY : DynamicalSystem S Y) (y : Y) (V : Set Y) :
visitTimeSet (diagDynamicalSystem dSystemX dSystemY) (x,y) (U ×ˢ V) =
(visitTimeSet dSystemX x U) ∩ (visitTimeSet dSystemY y V) := by
have h1 : visitTimeSet (diagDynamicalSystem dSystemX dSystemY) (x,y) (U ×ˢ V) ⊆
(visitTimeSet dSystemX x U) ∩ (visitTimeSet dSystemY y V) := by
  intro s hs
  simpa
have h2 : (visitTimeSet dSystemX x U) ∩ (visitTimeSet dSystemY y V) ⊆
visitTimeSet (diagDynamicalSystem dSystemX dSystemY) (x,y) (U ×ˢ V) := by
  simpa
exact subset_antisymm h1 h2

end Return_time_sets



section Minimality

variable {S : Type*} [Semigroup S] [Nonempty S]
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]

/-- An action of `S` on `X` is minimal if `X` is a minimal subset -/
def isMinimalSystem
(dSystem : DynamicalSystem S X) :
Prop :=
∀ Z : Set X,
isNonemptyCompactT2InvariantSubset dSystem Z → Z = Set.univ

/-- A subset `Y ⊆ X` is a minimal subset of `X` if it is minimal by containment
amongst all non-empty, compact, `S` invariant sets -/
def isMinimalSubset
(dSystem : DynamicalSystem S X) (Y : Set X) :
Prop :=
(isNonemptyCompactT2InvariantSubset dSystem Y) ∧
(∀ Z ⊆ Y, isNonemptyCompactT2InvariantSubset dSystem Z → Y = Z)

/-- Every system contains a minimal subset -/
theorem existsMinimalSubset
(dSystem : DynamicalSystem S X) :
∃ Y : Set X, isMinimalSubset dSystem Y := by
let C := {Z : Set X | isNonemptyCompactT2InvariantSubset dSystem Z}
have hChain : ∀ c ⊆ C, IsChain (· ⊆ ·) c → c.Nonempty → ∃ lb ∈ C, ∀ t ∈ c, lb ⊆ t := by
  intro c hc1 hc2 hc3
  let lb := c.sInter
  use lb
  constructor
  · simp only [Set.mem_setOf_eq, C]
    constructor
    · have hcDir : DirectedOn (· ⊇ ·) c := by
        unfold DirectedOn
        intro x hx y hy
        simp only
        unfold IsChain at hc2
        simp only at hc2
        specialize hc2 hx hy
        by_cases hxEqy : x = y
        · use x
          constructor
          · exact hx
          constructor
          · simp
          · rw [hxEqy]
        · have hxy1 : x ⊆ y ∨ y ⊆ x := by
            apply hc2 hxEqy
          rcases hxy1 with hP | hQ
          · use x
          · use y
      have hCNonempty : Nonempty c := by
        simp only [nonempty_subtype]
        rcases hc3 with ⟨a, ha⟩
        use a
      apply IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
      · exact hcDir
      · intro U hU
        have hUC : U ∈ C := by
          apply hc1
          exact hU
        simp only [Set.mem_setOf_eq, C] at hUC
        rcases hUC with ⟨hUC1, hUC2⟩
        exact hUC1
      · intro U hU
        have hUC : U ∈ C := by
          apply hc1
          exact hU
        simp only [Set.mem_setOf_eq, C] at hUC
        rcases hUC with ⟨hUC1, hUC2, hUC3⟩
        exact hUC2
      · intro U hU
        have hUC : U ∈ C := by
          apply hc1
          exact hU
        simp only [Set.mem_setOf_eq, C] at hUC
        rcases hUC with ⟨hUC1, hUC2, hUC3⟩
        apply IsCompact.isClosed
        exact hUC2
    constructor
    · have htClosed : ∀ t ∈ C, IsClosed t := by
        intro t ht
        apply IsCompact.isClosed
        simp only [Set.mem_setOf_eq, C] at ht
        rcases ht with ⟨ht1, ht2, ht3⟩
        exact ht2
      have hlbClosed : IsClosed lb := by
        simp only [lb]
        apply isClosed_sInter
        intro t ht
        have htC : t ∈ C := by
          apply hc1 ht
        specialize htClosed t
        apply htClosed htC
      apply IsClosed.isCompact
      exact hlbClosed
    constructor
    · infer_instance
    · apply intersectionOfInvIsInv
      intro t ht
      have htC : t ∈ C := by
        apply hc1 ht
      simp only [Set.mem_setOf_eq, C] at htC
      rcases htC with ⟨ht1, ht2, ht3, ht4⟩
      exact ht4
  · intro t ht
    simp only [lb]
    exact Set.sInter_subset_of_mem ht
have hXinS : Set.univ ∈ C := by
  simp only [Set.mem_setOf_eq, C]
  unfold isNonemptyCompactT2InvariantSubset
  constructor
  · simp
  constructor
  · exact isCompact_univ
  constructor
  · infer_instance
  · unfold isInvariantSet
    intro s
    simp
have hExistMin : ∃ m, m ⊆ Set.univ ∧ Minimal (· ∈ C) m := by
  apply zorn_superset_nonempty
  · exact hChain
  · exact hXinS
rcases hExistMin with ⟨Y, hY1, hY2⟩
use Y
unfold isMinimalSubset
constructor
· rcases hY2 with ⟨hY2a, hY2b⟩
  simp only [Set.mem_setOf_eq, C] at hY2a
  exact hY2a
· intro Z hZ1 hZ2
  unfold Minimal at hY2
  rcases hY2 with ⟨hY2a, hY2b⟩
  specialize hY2b hZ2
  have hYZ : Y ⊆ Z := by
    apply hY2b hZ1
  exact subset_antisymm hYZ hZ1

/- Depracated in favor of minimalSubsetIffMinimalSubsystem
/-- A minimal set, when made into a system, is a minimal system -/
theorem minimalSubsetIsMinimalSystem
(dSystem : DynamicalSystem S X)
{Y : Set X} [CompactSpace Y] [Nonempty Y]
(hMinSubset : isMinimalSubset dSystem Y) :
isMinimalSystem (fromNonemptyCompactT2InvariantSubsetToSystem dSystem (hMinSubset.1)) :=
by sorry -- UNHAPPY, WAIT TO TOUCH -/

/-- If Z is a subsystem of Y and Y is a subsystem of X, then Z is a subsystem of X -/
lemma subSystemOfSubsystem
(dSystem : DynamicalSystem S X)
{Y : Set X} [CompactSpace Y] [Nonempty Y]
(hYX : isNonemptyCompactT2InvariantSubset dSystem Y)
{Z : Set Y} [CompactSpace Z] [Nonempty Z]
(hZY : isNonemptyCompactT2InvariantSubset
(fromNonemptyCompactT2InvariantSubsetToSystem dSystem hYX) Z) :
isNonemptyCompactT2InvariantSubset dSystem (Subtype.val '' Z) := by
let dSystemY := fromNonemptyCompactT2InvariantSubsetToSystem dSystem hYX
have dYDef : dSystemY = fromNonemptyCompactT2InvariantSubsetToSystem dSystem hYX := by
  rfl
rw [<- dYDef] at hZY
obtain ⟨h1, h2, h3, h4⟩ := hZY
refine ⟨?_, ?_, ?_, ?_⟩
· simp only [Set.image_nonempty]
  exact h1
· apply h2.image continuous_subtype_val
· infer_instance
· intro s z hz
  obtain ⟨t, ht1, ht2⟩ := hz
  specialize h4 s ht1
  rw [<- ht2]
  have h20 : ∃ z ∈ Z, dSystemY.map s t = z := by
    simpa
  have h21 : dSystem.map s t.val ∈ Subtype.val '' Z := by
    refine ⟨dSystemY.map s t, h4, ?_⟩
    rfl
  exact h21

/-- A subset of a system X is a minimal subset iff it is a minimal subsystem -/
theorem minimalSubsetIffMinimalSubsystem
(dSystem : DynamicalSystem S X)
{Y : Set X} (preSubSystem : isNonemptyCompactT2InvariantSubset dSystem Y) :
letI : CompactSpace Y := isCompact_iff_compactSpace.mp (preSubSystem.2.1)
letI : Nonempty Y := by
  rcases preSubSystem.1 with ⟨y, hy⟩
  exact ⟨⟨y, hy⟩⟩
isMinimalSubset dSystem Y ↔
  isMinimalSystem (fromNonemptyCompactT2InvariantSubsetToSystem dSystem preSubSystem) := by
letI : CompactSpace Y := isCompact_iff_compactSpace.mp (preSubSystem.2.1)
letI : Nonempty Y := by
  rcases preSubSystem.1 with ⟨y, hy⟩
  exact ⟨⟨y, hy⟩⟩
let dSystemY := fromNonemptyCompactT2InvariantSubsetToSystem dSystem preSubSystem
have dYDef : dSystemY = fromNonemptyCompactT2InvariantSubsetToSystem dSystem preSubSystem := by
    trivial
constructor
· intro h1 Z hZ
  unfold isMinimalSubset at h1
  obtain ⟨hY1, hY2⟩ := h1
  specialize hY2 Z
  have hZY : Subtype.val '' Z ⊆ Y := by
    simp
  have hZY2 : Y = Subtype.val '' Z := by
    apply hY2
    · exact hZY
    rw [<- dYDef] at hZ
    have : Nonempty Z := by
      unfold isNonemptyCompactT2InvariantSubset at hZ
      obtain ⟨hZ1, hZ2, hZ3, hZ4⟩ := hZ
      obtain ⟨x, hx⟩ := hZ1
      exact ⟨x, hx⟩
    have : CompactSpace Z:= by
      unfold isNonemptyCompactT2InvariantSubset at hZ
      obtain ⟨hZ1, hZ2, hZ3, hZ4⟩ := hZ
      apply isCompact_iff_compactSpace.mp
      exact hZ2
    apply subSystemOfSubsystem
    rw [<- dYDef]
    exact hZ
  ext y
  constructor
  · intro hy
    trivial
  intro hy
  have hy3 : y.val ∈ Subtype.val '' Z := by
    simp only [<- hZY2, Subtype.coe_prop]
  obtain ⟨z, hz, hz_eq⟩ := hy3
  have hy4 : z = y := Subtype.ext hz_eq
  simpa [hy4] using hz
rw [<- dYDef]
intro hY5
unfold isMinimalSubset
constructor
· exact preSubSystem
intro Z hZ1 hZ2
unfold isMinimalSystem at hY5
let Z' := {y : Y | (y : X) ∈ Z}
specialize hY5 Z'
have hZ'1 : isNonemptyCompactT2InvariantSubset dSystemY Z' := by
  obtain ⟨hZ21, hZ22, hZ23, hZ24⟩ := hZ2
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hZ21
    have hzY : z ∈ Y := by
      exact hZ1 hz
    refine ⟨⟨z, hzY⟩, ?_⟩
    exact hz
  · have hy10 : {y : Y | (y : X) ∈ Z} = Subtype.val ⁻¹' Z := rfl
    simpa [hy10] using hZ22.preimage_continuous continuous_subtype_val
  · infer_instance
  · unfold isInvariantSet
    intro s
    specialize hZ24 s
    intro y hy
    have hyval : y.val ∈ Z := by
      simpa
    specialize hZ24 hyval
    simpa
have hZ'2 : Z' = Set.univ := by
  apply hY5
  exact hZ'1
ext y
constructor
· intro hy
  have hy7 : ⟨y, hy⟩ ∈ Z' := by
    have hy8 : (⟨y, hy⟩ : Y) ∈ Set.univ := by trivial
    rw [hZ'2]
    exact hy8
  exact hy7
intro hy
exact hZ1 hy

/-- A system is minimal if and only if for all points `x ∈ X`,
the `S`-orbit of `x` is dense -/
theorem minimalIffDenseOrbits
(dSystem : DynamicalSystem S X) :
isMinimalSystem dSystem ↔ ∀ x : X, Dense (orbit dSystem x) :=
by
  constructor
  · intro hIsMin x
    unfold isMinimalSystem at hIsMin
    have orbitIsDense : closure (orbit dSystem x) = Set.univ :=
      hIsMin (closure (orbit dSystem x)) (orbitClosureIsNonemptyCompactT2InvariantSubset dSystem x)
    simp only [← dense_iff_closure_eq] at orbitIsDense
    exact orbitIsDense
  · intro hDense Z subsysZ
    rcases subsysZ with ⟨hNon,hCmct,hT2,hInv⟩
    rcases hNon with ⟨z,hz⟩ -- Choose an element of Z with a proof of membership
    have orbitInZ : orbit dSystem z ⊆ Z := by
      unfold orbit
      unfold Set.range
      intro x hx
      unfold isInvariantSet Set.MapsTo at hInv
      rcases hx with ⟨s,hs⟩
      rewrite [← hs]
      exact hInv s hz
    have orbitClosInZ : closure (orbit dSystem z) ⊆ Z :=
      closure_minimal orbitInZ (IsCompact.isClosed hCmct)
    simp only [dense_iff_closure_eq] at hDense
    rewrite [hDense z] at orbitClosInZ
    exact Set.Subset.antisymm (Set.subset_univ Z) orbitClosInZ

/-- A useful corollary of `minimalIffDenseOrbits`: in a minimal system, the orbit
closure of every point is the whole space `X` -/
lemma minimalImpliesFullOrbitClosure
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) (x : X) :
orbitClosure dSystem x = Set.univ :=
dense_iff_closure_eq.mp ((minimalIffDenseOrbits dSystem).mp hMin x)

/-- A useful corollary of `minimalIffDenseOrbits`: in a minimal system, for
all points `x ∈ X` and all non-empty, open sets `U ⊆ X`, there exists `s ∈ S`
such that `sx ∈ U` -/
lemma minimalImpliesNonemptySetVisits
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem)
(x : X) {U : Set X} (UOpen : IsOpen U) (UNonempty : U.Nonempty) :
(visitTimeSet dSystem x U).Nonempty :=
by
  have xHasDenseOrbit := (minimalIffDenseOrbits dSystem).mp hMin x
  simp only [dense_iff_closure_eq] at xHasDenseOrbit
  rcases UNonempty with ⟨u,hu⟩
  apply superset_of_eq at xHasDenseOrbit
  have uinClosure := xHasDenseOrbit (Set.mem_univ u)
  simp only [mem_closure_iff] at uinClosure
  have orbitVisitsU := uinClosure U UOpen hu
  rcases orbitVisitsU with ⟨w,hw1,hw2⟩
  rcases hw2 with ⟨s,hs⟩
  simp only at hs
  use s
  unfold visitTimeSet
  simp only [← hs] at hw1
  exact hw1

/-- A factor of a minimal system is a minimal system -/
theorem factorOfMinimalIsMinimal
{dSystemX : DynamicalSystem S X} (hXMin : isMinimalSystem dSystemX)
{Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
{dSystemY : DynamicalSystem S Y} (hFactor : isFactor dSystemY dSystemX) :
isMinimalSystem dSystemY := by
have hY1 : ∀ y : Y, Dense (orbit dSystemY y) := by
  intro y
  obtain ⟨π, hπ1, hπ2, hπ3⟩ := hFactor
  have hY11 : ∃ x : X, π x = y := by
    apply hπ2
  obtain ⟨x, hx⟩ := hY11
  have hY2 : π '' (orbit dSystemX x) = orbit dSystemY y := by
    have hY21 : π '' (orbit dSystemX x) ⊆ orbit dSystemY y := by
      intro z hz
      have h7 : ∃ w ∈ orbit dSystemX x, π w = z:= by
        simpa [Set.image_eq] using hz
      obtain ⟨w, h1, hw2⟩ := h7
      have h8 : ∃ s : S, dSystemX.map s x = w:= by
        simpa using h1
      obtain ⟨s, hs⟩ := h8
      have h9 : π (dSystemX.map s x) = π w := by
        simp only [hs]
      rw [<- hw2, <- h9]
      have h10 : π (dSystemX.map s x) = (dSystemY.map s) (π x) := by
        specialize hπ3 s
        have h5 : ((dSystemY.map s) ∘ π) x = (π ∘ (dSystemX.map s)) x := by
          exact congrArg (fun f => f x) hπ3
        have h6 : dSystemY.map s (π x) = π (dSystemX.map s x) := by
          exact h5
        rw [h6]
      rw [<- hx, h10]
      unfold orbit
      simp
    have hY22 : orbit dSystemY y ⊆ π '' (orbit dSystemX x) := by
      intro z hz
      have hY221 : ∃ s : S, dSystemY.map s y = z := by
        unfold orbit at hz
        simpa
      obtain ⟨s, hs⟩ := hY221
      rw [<- hx] at hs
      have h4 : z = π (dSystemX.map s x) := by
        specialize hπ3 s
        have h5 : ((dSystemY.map s) ∘ π) x = (π ∘ (dSystemX.map s)) x := by
          exact congrArg (fun f => f x) hπ3
        have h6 : dSystemY.map s (π x) = π (dSystemX.map s x) := by
          exact h5
        rw [<- hs]
        apply h6
      simp only [Set.mem_image]
      use dSystemX.map s x
      constructor
      · unfold orbit
        simp
      rw [h4]
    apply subset_antisymm hY21 hY22
  have hY3 : Dense (orbit dSystemX x) := by
    have hY4 : ∀ (x : X), Dense (orbit dSystemX x) := by
      let dSystemZ := dSystemX
      apply minimalIffDenseOrbits at dSystemZ
      apply dSystemZ.mp
      exact hXMin
    specialize hY4 x
    exact hY4
  rw [<- hY2]
  apply DenseRange.dense_image
  · apply Function.Surjective.denseRange hπ2
  · apply hπ1
  apply hY3
simp only [minimalIffDenseOrbits]
exact hY1

/-- Image of a minimal invariant set under a continuous, equivariant map
is a minimal invariant set -/
lemma imageOfMinimalSetIsMinimal
{dSystemX : DynamicalSystem S X}
{Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
{dSystemY : DynamicalSystem S Y}
(π : X → Y) (hContinuous : Continuous π)
(hEquivariant : isEquivariant dSystemX.map dSystemY.map π)
(Z : Set X) (hZMinimal : isMinimalSubset dSystemX Z) :
isMinimalSubset dSystemY (π '' Z):= by
let hZ' := hZMinimal
rcases hZ' with ⟨hZInvariant, hZ2⟩
have hZInvariant' := hZInvariant
let dSystemZ := fromNonemptyCompactT2InvariantSubsetToSystem dSystemX hZInvariant
let W := π '' Z
have hWDef : W = π '' Z := by rfl
have hWSubsystem : isNonemptyCompactT2InvariantSubset dSystemY W := by
  apply imageOfSubsystemIsSubsystem
  · exact hContinuous
  · exact hEquivariant
  exact hZInvariant
let dSystemW := fromNonemptyCompactT2InvariantSubsetToSystem dSystemY hWSubsystem
rcases hZInvariant with ⟨hZ1, hZ2, hZ3⟩
have hZCompact : CompactSpace Z := by
  exact isCompact_iff_compactSpace.mp hZ2
have hZNonempty : Nonempty Z := by
  simp only [nonempty_subtype]
  exact hZ1
have hWCompact : CompactSpace W := by
  have hWIsCompact : IsCompact W := by
    exact IsCompact.image hZ2 hContinuous
  exact isCompact_iff_compactSpace.mp hWIsCompact
have hπW : ∀ x : Z, π x ∈ W := by
      intro x
      exact ⟨x, x.property, rfl⟩
let π' : Z → W := fun x ↦ ⟨π x, ⟨x, x.property, rfl⟩⟩
have hFactorMap : isFactorMap dSystemZ dSystemW π' := by
  unfold isFactorMap
  constructor
  · let π2 : Z → Y := fun x ↦ π x
    have hπ2Char : π2 = π ∘ Subtype.val := by
      simp only [π2]
      ext x
      simp
    have hπ2Continuous : Continuous π2 := by
      rw [hπ2Char]
      apply Continuous.comp
      · exact hContinuous
      exact continuous_subtype_val
    apply Continuous.subtype_mk
    simpa
  constructor
  · unfold Function.Surjective
    simp [π']
    simp only [hWDef]
    simp
  unfold isEquivariant
  intro s
  specialize hEquivariant s
  ext x
  have hF1 : (dSystemW.map s ∘ π') x = (dSystemW.map s) (π' x) := by
    simp
  have hF2 : (π' ∘ dSystemZ.map s) x = π' (dSystemZ.map s x) := by
    simp
  rw [hF1, hF2]
  have hF3 : (dSystemY.map s ∘ π) x = (π ∘ dSystemX.map s) x := by
    rw [hEquivariant]
  have hF4 : (dSystemY.map s) (π x) = π (dSystemX.map s x) := by
    exact hF3
  simpa
have hFactorZW : isFactor dSystemW dSystemZ := by
  unfold isFactor
  use π'
have hZMinimalSystem : isMinimalSystem dSystemZ := by
  apply (minimalSubsetIffMinimalSubsystem dSystemX hZInvariant').mp hZMinimal
have hWMinimalSystem : isMinimalSystem dSystemW := by
  apply factorOfMinimalIsMinimal hZMinimalSystem hFactorZW
apply (minimalSubsetIffMinimalSubsystem dSystemY hWSubsystem).mpr
exact hWMinimalSystem

/-- The set of times `U ⊆ X` visits `V ⊆ X`, `R(U,V)`, is equal
to `R(x,V) R(x,U)^{-1}` in minimal systems -/
theorem setVisitsAsQuotientSet
{dSystem : DynamicalSystem S X} (hMinimal : isMinimalSystem dSystem) (x : X) (U V : Set X)
(hUOpen : IsOpen U) (hVOpen : IsOpen V) :
setVisitTimeSet dSystem U V = ⋃ s ∈ visitTimeSet dSystem x U,
((· * s) ⁻¹' (visitTimeSet dSystem x V)) := by
have h1 : setVisitTimeSet dSystem U V ⊆ ⋃ s ∈ visitTimeSet dSystem x U,
((· * s) ⁻¹' (visitTimeSet dSystem x V)) := by
  intro r hr
  have hr1 : (dSystem.map r '' U ∩ V).Nonempty := by
    unfold setVisitTimeSet at hr
    simpa using hr
  have hr2 : (U ∩ dSystem.map r ⁻¹' V).Nonempty := by
    obtain ⟨v, hv1, hv2⟩ := hr1
    simp only [Set.mem_image] at hv1
    obtain ⟨u, hu1, hu2⟩ := hv1
    have hr3: u ∈ U ∩ dSystem.map r ⁻¹' V := by
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · exact hu1
      rw [hu2]
      exact hv2
    use u
  have hr3 : IsOpen (U ∩ dSystem.map r ⁻¹' V) := by
    have hr4: IsOpen (dSystem.map r ⁻¹' V) := by
      apply IsOpen.preimage (dSystem.mapCont r)
      exact hVOpen
    apply IsOpen.inter hUOpen hr4
  have hr4 : ∃ h : S, h ∈ visitTimeSet dSystem x (U ∩ (dSystem.map r) ⁻¹' V) := by
    apply minimalImpliesNonemptySetVisits hMinimal
    · apply hr3
    apply hr2
  obtain ⟨h, hh⟩ := hr4
  have hr5: h ∈ (visitTimeSet dSystem x U) ∩ (visitTimeSet dSystem x (dSystem.map r ⁻¹' V)) := by
    simpa only [visitToInter, hh]
  have hr6 : h ∈ (r * ·) ⁻¹' (visitTimeSet dSystem x V) := by
    simp only [visitsToPreimages]
    apply hr5.2
  have hr7 : r ∈ (· * h) ⁻¹' visitTimeSet dSystem x V := by
    simpa
  simp only [Set.mem_iUnion, Set.mem_preimage, exists_prop]
  use h
  constructor
  · apply hr5.1
  apply hr7
have h2 : ⋃ s ∈ visitTimeSet dSystem x U, ((· * s) ⁻¹' (visitTimeSet dSystem x V))
⊆ setVisitTimeSet dSystem U V := by
  intro r hr
  simp only [Set.mem_iUnion, Set.mem_preimage, exists_prop] at hr
  obtain ⟨s, hs1, hs2⟩ := hr
  have hs1a: dSystem.map s x ∈ U := by
    exact hs1
  have hs2a : dSystem.map (r * s) x ∈ V := by
    exact hs2
  have hs3 : dSystem.map (r * s) x ∈ dSystem.map r '' U := by
    have hs31 : dSystem.map r (dSystem.map s x) ∈ dSystem.map r '' U := by
      refine ⟨dSystem.map s x, hs1a, rfl⟩
    have hs32 : dSystem.map r (dSystem.map s x) = dSystem.map (r * s) x := by
      simp only [dSystem.mapMult]
    rw [<- hs32]
    exact hs31
  have h4 : (dSystem.map r '' U ∩ V).Nonempty := by
    exact ⟨dSystem.map (r * s) x, hs3, hs2a⟩
  unfold setVisitTimeSet
  exact h4
exact subset_antisymm h1 h2

end Minimality



section Uniform_recurrence

variable {S : Type*} [Semigroup S] [Nonempty S]
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]

/-- A point `x ∈ X` is uniformly recurrent if for all neighborhoods `U` of `x`
the set of visit times `R(x,U)` is a syndetic subset of `S` -/
def isUniformlyRecurrent
(dSystem : DynamicalSystem S X) (x : X) :
Prop :=
∀ U ∈ nhds x, isSyndetic (visitTimeSet dSystem x U)

/-- If `x ∈ X` is uniformly recurrent, then it belongs to its orbit closure -/
lemma URPointBelongsToOrbitClosure
(dSystem : DynamicalSystem S X) {x : X} (xUR : isUniformlyRecurrent dSystem x) :
x ∈ orbitClosure dSystem x := by
have h1 : ∀ U ∈ nhds x, (U ∩ orbit dSystem x).Nonempty := by
  intro U hU
  have h4 := xUR U hU
  have h2 : (visitTimeSet dSystem x U).Nonempty := by
    apply syndeticSetIsNonEmpty
    exact h4
  rcases h2 with ⟨s, hs⟩
  have h3 : dSystem.map s x ∈ U := by
    exact hs
  have h5 : dSystem.map s x ∈ orbit dSystem x := by
    unfold orbit
    simp
  exact ⟨dSystem.map s x, h3, h5⟩
apply mem_closure_iff.2
intro U hU1 hU2
have h61 : U ∈ nhds x := by
  apply IsOpen.mem_nhds hU1 hU2
have h62 := h1 U h61
exact h62

-- Next lemma is an upgrade of URPointBelongsToOrbitClosure
/-- A uniformly recurrent point belongs to its orbit closure along any thick set -/
lemma uniformRecurrentPointBelongToThickOrbit
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X)
(A : Set S) (hAThick : isThick A)
(x : X) (hxUR : isUniformlyRecurrent dSystem x) :
x ∈ closure (setOrbitAlongASet dSystem A {x}) := by
apply mem_closure_iff.mpr
intro U hU1 hU2
unfold isUniformlyRecurrent at hxUR
specialize hxUR U
have hUNeigh : U ∈ nhds x := by
  apply mem_nhds_iff.mpr
  use U
specialize hxUR hUNeigh
have hInterNonempty : ((visitTimeSet dSystem x U) ∩ A).Nonempty := by
  apply syndeticThickIntersect
  · exact hxUR
  · exact hAThick
rcases (Set.inter_nonempty.mp hInterNonempty) with ⟨s, hs1, hs2⟩
simp only [visitTimeSet, Set.mem_preimage] at hs1
apply Set.inter_nonempty.mpr
use dSystem.map s x
constructor
· exact hs1
· simp only [setOrbitAlongASet, Set.image_singleton, Set.iUnion_singleton_eq_range, Set.mem_range,
  Subtype.exists, exists_prop]
  use s

/-- If a point is uniformly recurrent in a subsystem, it is uniformly
recurrent in the system -/
lemma URInSubsystemImpliesURInSystem
(dSystem : DynamicalSystem S X) {Z : Set X}
(hZ : isNonemptyCompactT2InvariantSubset dSystem Z) (z : Z) :
letI : CompactSpace Z := isCompact_iff_compactSpace.mp (hZ.2.1)
letI : Nonempty Z := (fun ⟨y, hy⟩ ↦ ⟨⟨y, hy⟩⟩) hZ.1
isUniformlyRecurrent (fromNonemptyCompactT2InvariantSubsetToSystem dSystem hZ) z →
  isUniformlyRecurrent dSystem ↑z := by
intro hUniZ
unfold isUniformlyRecurrent
intro U hU
have hU1 : ∃ U1 ⊆ U, IsOpen U1 ∧ Subtype.val z ∈ U1 := by
  apply mem_nhds_iff.mp hU
rcases hU1 with ⟨U1, hU1a, hU1b, hU1c⟩
let V : Set Z := Subtype.val ⁻¹' U1
have hVOpen : IsOpen V := by
  apply IsOpen.preimage
  · continuity
  · exact hU1b
have hVContain : z ∈ V := by
  simp only [Set.mem_preimage, V]
  exact hU1c
have hVnhds : V ∈ nhds z := by
  apply mem_nhds_iff.mpr
  use V
unfold isUniformlyRecurrent at hUniZ
specialize hUniZ V hVnhds
unfold isSyndetic at hUniZ
rcases hUniZ with ⟨F, hF1, hF2⟩
use F
constructor
· exact hF1
· intro s
  specialize hF2 s
  rcases hF2 with ⟨f, hf1, hf2⟩
  use f
  constructor
  · exact hf1
  · simp only [visitTimeSet, Set.mem_preimage]
    simp only [visitTimeSet, Set.mem_preimage] at hf2
    simp only [Set.mem_preimage, V] at hf2
    have hGoal : dSystem.map (f * s) (Subtype.val z) ∈ U1 := by
      exact hf2
    apply hU1a
    exact hGoal

/-- In a minimal system, for all `x ∈ X` and all non-empty, open `U ⊆ X`
the set of visit times `R(x,U)` is syndetic -/
theorem minimalImpliesSyndeticVisits
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :
∀ x : X, ∀ U : Set X, U.Nonempty → IsOpen U →
isSyndetic (visitTimeSet dSystem x U) :=
by
  intro x U U_nonempty U_open
  rewrite [minimalIffDenseOrbits dSystem] at hMin
  unfold Dense orbit at hMin
  simp only [mem_closure_iff] at hMin
  rcases U_nonempty with ⟨u, elt_of_U⟩
  have all_y_map_into_U : ∀ y : X, ∃ s : S, dSystem.map s y ∈ U := by
    intro y
    have all_y_map_into_U_half : (U ∩ Set.range fun s ↦ dSystem.map s y).Nonempty :=
    hMin y u U U_open elt_of_U
    rcases all_y_map_into_U_half with ⟨u_two, u_two_in_image⟩
    rcases u_two_in_image.2 with ⟨s_witness, s_witness_info⟩
    simp at s_witness_info
    use s_witness
    simp only [s_witness_info]
    exact u_two_in_image.1
  let s_chooser : X → S := fun x : X => Classical.choose (all_y_map_into_U x)
  have s_chooser_property : ∀ x : X, dSystem.map (s_chooser x) x ∈ U := by
    intro x
    exact Classical.choose_spec (all_y_map_into_U x)
  let V_chooser : X → Set X := fun x : X => Set.preimage (dSystem.map (s_chooser x)) U
  have V_choice_has_x : ∀ x : X, x ∈ V_chooser x := by
    intro x
    unfold V_chooser
    exact s_chooser_property x
  have V_choice_open : ∀ x : X, IsOpen (V_chooser x) := by
    intro x
    have cts_s_chooser : Continuous (dSystem.map (s_chooser x)) := dSystem.mapCont (s_chooser x)
    unfold V_chooser
    exact Continuous.isOpen_preimage cts_s_chooser U U_open
  have V_choice_covers : Set.univ ⊆ Set.iUnion V_chooser := by
    intro x x_in_X
    unfold V_chooser
    simp only [Set.mem_iUnion, Set.mem_preimage]
    use x
    exact s_chooser_property x
  have finite_cover : ∃ (Y : Finset X), Set.univ ⊆ ⋃ y ∈ Y, V_chooser y :=
    IsCompact.elim_finite_subcover isCompact_univ V_chooser V_choice_open V_choice_covers
  rcases finite_cover with ⟨Y, cover_prop⟩
  have Yset_finite : (Y : Set X).Finite := Y.finite_toSet
  unfold isSyndetic
  use Set.image s_chooser (Y : Set X)
  have image_F_finite : (Set.image s_chooser (Y : Set X)).Finite :=
    Set.Finite.image s_chooser Yset_finite
  refine ⟨image_F_finite,?_⟩
  intro s
  have tofun_s_x_in_univ : dSystem.map s x ∈ Set.univ := by simp
  have tofun_s_x_cover : dSystem.map s x ∈ ⋃ y ∈ Y, V_chooser y := cover_prop tofun_s_x_in_univ
  rcases Set.mem_iUnion₂.mp tofun_s_x_cover with ⟨y, hyY, hxFy⟩
  have tofun_s_choose_tofun : dSystem.map (s_chooser y) (dSystem.map s x) ∈ U := by
    unfold V_chooser at hxFy
    exact hxFy
  have use_semigp_prop : dSystem.map ((s_chooser y) * s) x ∈ U := by
    simp only [dSystem.mapMult]
    exact tofun_s_choose_tofun
  have s_chooser_y_works : s_chooser y * s ∈ visitTimeSet dSystem x U := by
    unfold visitTimeSet
    exact use_semigp_prop
  have s_chooser_y_clear: s_chooser y ∈ s_chooser '' (Y : Set X) := by
    simp only [Set.mem_image, SetLike.mem_coe]
    use y
  use s_chooser y

/-- Every point in a minimal system is uniformly recurrent -/
theorem minimalImpliesUniformlyRecurrent
(dSystem : DynamicalSystem S X) {hMin : isMinimalSystem dSystem} :
∀ x : X, isUniformlyRecurrent dSystem x :=
by
  intro x U Unbhd
  simp only [mem_nhds_iff] at Unbhd
  rcases Unbhd with ⟨V, VinU, Vopen, Vhasx⟩
  have Vnonempty : V.Nonempty := Set.nonempty_of_mem Vhasx
  have goalforV : isSyndetic (visitTimeSet dSystem x V) :=
    minimalImpliesSyndeticVisits hMin x V Vnonempty Vopen
  exact syndeticIsMonotone goalforV (visitTimesMono dSystem x VinU)

/-- If a uniformly recurrent point visits a non-empty open set, then it
visits that set syndetically -/
lemma nonemptyVisitsOfURPointImpliesSyndetic
(dSystem : DynamicalSystem S X) {x : X} (xIsUR : isUniformlyRecurrent dSystem x)
{U : Set X} {UOpen : IsOpen U}
(hNonemptyVisit : (visitTimeSet dSystem x U).Nonempty) :
isSyndetic (visitTimeSet dSystem x U) := by
have h1 : ∃ s : S, dSystem.map s x ∈ U := by
  obtain ⟨s, hs⟩ := hNonemptyVisit
  use s
  unfold visitTimeSet at hs
  simpa
obtain ⟨s, hs⟩ := h1
have h2 : x ∈ (dSystem.map s) ⁻¹' U := by
  simpa using hs
let V := (dSystem.map s) ⁻¹' U
have h3 : IsOpen V := by
  have h31 : Continuous (dSystem.map s) := by
    apply dSystem.mapCont
  apply h31.isOpen_preimage U UOpen
have h4 : V ∈ nhds x := by
  unfold V
  apply h3.mem_nhds h2
have h5 : isSyndetic (visitTimeSet dSystem x V) := by
  unfold isUniformlyRecurrent at xIsUR
  specialize xIsUR V h4
  apply xIsUR
have h6 : (s * ·) '' visitTimeSet dSystem x V ⊆ visitTimeSet dSystem x U := by
  intro r hr
  have h61 : ∃ t : S, dSystem.map t x ∈ V ∧ r = s * t := by
    simp only [Set.mem_image] at hr
    obtain ⟨t, ht1, ht2⟩ := hr
    use t
    constructor
    · apply ht1
    rw [<- ht2]
  obtain ⟨t, ht⟩ := h61
  have h62 : dSystem.map r x ∈ U := by
    have h63 : dSystem.map r x = dSystem.map s (dSystem.map t x) := by
      rw [ht.2]
      simp only [dSystem.mapMult]
    have h64 : dSystem.map s (dSystem.map t x) ∈ U := by
      simpa using ht.1
    rw [h63]
    apply h64
  simpa using h62
have h7 : isSyndetic ((s * ·) '' visitTimeSet dSystem x V) := by
  apply shiftSyndeticIsSyndetic
  apply h5
apply syndeticIsMonotone h7 h6


/-- If Y is a closed subspace of X and A ⊆ Y, then the closure of A in Y is equal
to the closure of A in X -/
lemma subtype_closure_eq_of_isClosed
{X : Type*} [TopologicalSpace X] {Y : Set X} {A : Set Y} (hY : IsClosed Y) :
  closure (Subtype.val '' A) = Subtype.val '' (closure A) := by
  have h1 : Subtype.val '' (closure A) ⊆ closure (Subtype.val '' A) := by
    apply image_closure_subset_closure_image
    exact continuous_subtype_val
  have h2 : IsClosed (Subtype.val '' (closure A)) := by
    have h2a : IsClosed (closure A) := by
      simp
    apply IsClosed.isClosedMap_subtype_val
    · exact hY
    exact h2a
  have h3 : closure (Subtype.val '' (closure A)) = Subtype.val '' (closure A) := by
    simp
  have h4 : Subtype.val '' A ⊆ Subtype.val '' (closure A) := by
    simp only [Set.image_subset_iff, Subtype.val_injective, Set.preimage_image_eq]
    unfold closure
    simp
  have h5 : closure (Subtype.val '' A) ⊆ closure (Subtype.val '' (closure A)) := by
    apply closure_mono
    exact h4
  have h6 : closure (Subtype.val '' A) ⊆ Subtype.val '' (closure A) := by
    rw [<- h3]
    exact h5
  apply Set.Subset.antisymm h6 h1

/-- For any open set U, there exists an open set V ⊆ U and an entourage γ
such that for all a ∈ V, the ball B_γ(a) ⊆ U -/
-- This lemma is needed for Theorem "orbitClosureOfURPointIsMinimalSubset" below
lemma existEntourageGivenOpenSet
{X : Type*} [UniformSpace X] (U : Set X) (hUOpen : IsOpen U)
  (hUNonempty : U.Nonempty) :
  ∃ (V : Set X), V ⊆ U ∧ V.Nonempty ∧ IsOpen V ∧ ∃ γ : Set (X × X), γ ∈ uniformity X ∧
∀ a ∈ V, ∀ b : X, (a, b) ∈ γ → b ∈ U := by
rcases hUNonempty with ⟨x0, hx0⟩
have h1 : {p : X × X | p.1 = x0 → p.2 ∈ U} ∈ uniformity X := by
  apply isOpen_uniformity.mp
  · exact hUOpen
  exact hx0
let α := {p : X × X | p.1 = x0 → p.2 ∈ U}
have hαDef : α = {p : X × X | p.1 = x0 → p.2 ∈ U} := rfl
rw [<- hαDef] at h1
let B1 := {y : X | (x0, y) ∈ α}
have h2 : B1 ⊆ U := by
  intro y hy
  simp only [B1] at hy
  simp only [Set.mem_setOf_eq, forall_const, Set.setOf_mem_eq, α] at hy
  exact hy
have h3 : ∃ γ ∈ uniformity X, SetRel.comp γ γ ⊆ α := by
  apply comp_mem_uniformity_sets
  exact h1
have h31 : ∃ γ ∈ uniformity X, SetRel.IsSymm γ ∧ SetRel.comp γ γ ⊆ α := by
  let ⟨β, hβ1, hβ2⟩ := h3
  let ⟨γ, hγ1, hγ2, hγ3⟩ := symm_of_uniformity hβ1
  use γ
  constructor
  · exact hγ1
  constructor
  · exact hγ2
  have h31a : SetRel.comp γ γ ⊆ SetRel.comp β β := by
    intro a ha
    rcases ha with ⟨b, ha2, ha3⟩
    unfold SetRel.comp
    simp only [Set.mem_setOf_eq]
    use b
    constructor
    · apply hγ3
      exact ha2
    · apply hγ3
      exact ha3
  exact h31a.trans hβ2
rcases h31 with ⟨γ, hγ1, hγ2, hγ3⟩
let B2 := {y : X | (x0, y) ∈ γ}
have h4 : x0 ∈ B2 := by
  simp only [B2]
  apply mem_uniformity_of_eq
  · exact hγ1
  rfl
have h5 : B2 ∈ nhds x0 := by
  apply mem_nhds_uniformity_iff_right.mpr
  simp only [B2]
  have h5a : γ ⊆ {p : X × X| p.1 = x0 → (x0, p.2) ∈ γ} := by
    intro q hq
    simp only [Set.mem_setOf_eq]
    intro hq1
    rw [<- hq1]
    exact hq
  apply Filter.sets_of_superset
  · exact hγ1
  · exact h5a
let ⟨B3, hB31, hB32, hB34⟩ := mem_nhds_iff.mp h5
let V := B3 ∩ U
use V
constructor
· simp [V]
constructor
· simp only [V]
  have hB3Ux0 : x0 ∈ B3 ∩ U := by
    simp only [Set.mem_inter_iff]
    constructor
    · exact hB34
    · exact hx0
  exact ⟨x0, hB3Ux0⟩
constructor
· exact IsOpen.inter hB32 hUOpen
· use γ
  constructor
  · exact hγ1
  · intro a ha b hab
    simp only [V] at ha
    rcases ha with ⟨ha1, ha2⟩
    have ha3 : a ∈ B2 := by
      apply hB31
      exact ha1
    simp [B2] at ha3
    have hx0b : (x0, b) ∈ α := by
      unfold SetRel.comp at hγ3
      apply hγ3
      simp only [Set.mem_setOf_eq]
      use a
    simp only [Set.mem_setOf_eq, forall_const, α] at hx0b
    exact hx0b

/-- The orbit closure of a uniformly recurrent point is a minimal set -/
theorem orbitClosureOfURPointIsMinimalSubset
(dSystem : DynamicalSystem S X)
{x : X} (xisUR : isUniformlyRecurrent dSystem x) :
isMinimalSubset dSystem (orbitClosure dSystem x) := by
letI hXUniform : UniformSpace X := by
  apply uniformSpaceOfCompactR1
have h1 : ∀ U ∈ nhds x, (U ∩ orbit dSystem x).Nonempty := by
  intro U hU
  have h4 := xisUR U hU
  have h2 : (visitTimeSet dSystem x U).Nonempty := by
    apply syndeticSetIsNonEmpty
    exact h4
  rcases h2 with ⟨s, hs⟩
  have h3 : dSystem.map s x ∈ U := by
    exact hs
  have h5 : dSystem.map s x ∈ orbit dSystem x := by
    unfold orbit
    simp
  exact ⟨dSystem.map s x, h3, h5⟩
have h6 : x ∈ orbitClosure dSystem x := by
  apply mem_closure_iff.2
  intro U hU1 hU2
  have h61 : U ∈ nhds x := by
    apply IsOpen.mem_nhds hU1 hU2
  have h62 := h1 U h61
  exact h62
let Y := orbitClosure dSystem x
have Y_def : Y = orbitClosure dSystem x := by
  rfl
have xInY : x ∈ Y := by
  simpa
let x' : Y := ⟨x, xInY⟩
have hY : isNonemptyCompactT2InvariantSubset dSystem Y := by
  apply orbitClosureIsNonemptyCompactT2InvariantSubset
let dSystemY := fromNonemptyCompactT2InvariantSubsetToSystem dSystem hY
letI : CompactSpace Y := by
  apply isCompact_iff_compactSpace.mp
  exact hY.2.1
have hYNonempty: Nonempty Y := by
  apply hY.1.to_subtype
have hYUreturn : ∀ y : Y, ∀ U : Set Y,
IsOpen U → U.Nonempty → ∃ s : S,  dSystemY.map s y ∈ U := by
  intro y U hUOpen hUNonempty
  have h1 : ∃ V : Set Y, V ⊆ U ∧ V.Nonempty ∧ IsOpen V ∧ ∃ γ : Set (Y × Y), γ ∈ uniformity Y ∧
∀ a ∈ V, ∀ b : Y, (a, b) ∈ γ → b ∈ U := by
    apply existEntourageGivenOpenSet
    · exact hUOpen
    · exact hUNonempty
  obtain ⟨V, hV1, hV2, hV3, γ, hγ1, hγ2⟩ := h1
  rcases (isOpen_induced_iff.mp hV3) with ⟨V', hV'_open, hV_eq⟩
  have h12 : (V' ∩ Y).Nonempty := by
    rcases hV2 with ⟨x, hx⟩
    have h12a : Subtype.val '' V ⊆ V' := by
      simp only [Set.image_subset_iff]
      rw [hV_eq]
    have h12b : Subtype.val x ∈ V' := by
      apply h12a
      simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta,
        Subtype.coe_prop, exists_const]
      exact hx
    have h12c : Subtype.val x ∈ V' ∩ Y := by
      simpa
    exact ⟨Subtype.val x, h12c⟩
  have h11 : ∃ t : S, dSystem.map t x ∈ V' := by
    unfold orbitClosure at Y_def
    unfold orbit at Y_def
    rw [Y_def] at h12
    rcases h12 with ⟨z, hzV, hz_cl⟩
    have h111 : (V' ∩ orbit dSystem x).Nonempty := by
      apply mem_closure_iff.mp
      · exact hz_cl
      · exact hV'_open
      exact hzV
    rcases h111 with ⟨x1, hx1, hx2⟩
    unfold orbit at hx2
    rcases hx2 with ⟨t, ht⟩
    use t
    simp only [ht]
    exact hx1
  have h2 : ∃ t : S, dSystemY.map t x' ∈ V := by
    rcases h11 with ⟨t, ht⟩
    use t
    rw [<- hV_eq]
    simp only [Set.mem_preimage]
    exact ht
  rcases h2 with ⟨t, ht⟩
  have h3 : x' ∈ (dSystemY.map t) ⁻¹' V := by
    exact ht
  have h4 : isUniformlyRecurrent dSystemY x' := by
    intro V_Y hV_Y
    rcases (mem_nhds_iff.mp hV_Y) with ⟨V1_Y, hxV1, hV1_open, hV1_sub⟩
    rcases (isOpen_induced_iff.mp hV1_open) with ⟨V_X, hV'_open, hV_eq⟩
    have h4a : visitTimeSet dSystemY x' V1_Y = visitTimeSet dSystem x V_X := by
      ext s
      constructor
      · intro hs
        rw [<- hV_eq] at hs
        simpa
      intro hs
      have h4b : dSystem.map s x ∈ V_X := by
        exact hs
      have h4e :dSystemY.map s x' ∈ V1_Y := by
        rw [<- hV_eq]
        exact h4b
      exact h4e
    have h4f : isSyndetic (visitTimeSet dSystem x V_X) := by
      apply xisUR
      have h4g : Subtype.val '' V1_Y ⊆ V_X := by
        simp [hV_eq]
      have h4gg : x = Subtype.val x' := by
        rfl
      have h4h : x ∈ V_X := by
        apply h4g
        rw [h4gg]
        simp [hV1_sub]
      exact IsOpen.mem_nhds hV'_open h4h
    have h4i : isSyndetic (visitTimeSet dSystemY x' V1_Y) := by
      rw [h4a]
      exact h4f
    have h4j : visitTimeSet dSystemY x' V1_Y ⊆ visitTimeSet dSystemY x' V_Y := by
      apply visitTimesMono
      exact hxV1
    exact syndeticIsMonotone h4i h4j
  let Vt := dSystemY.map t ⁻¹' V
  have h42 : IsOpen Vt := by
    apply IsOpen.preimage
    · apply dSystemY.mapCont t
    exact hV3
  have h5 : isSyndetic (visitTimeSet dSystemY x' Vt) := by
    apply h4
    apply IsOpen.mem_nhds
    · exact h42
    simpa
  rcases h5 with ⟨F, hF1, hF2⟩
  have h50 : ∀ f ∈ F, Continuous (dSystemY.map (t * f)) := by
    intro f hf
    apply dSystemY.mapCont (t * f)
  have h51 : ∀ f ∈ F, UniformContinuous (dSystemY.map (t * f)) := by
    intro f hf
    specialize h50 f hf
    exact CompactSpace.uniformContinuous_of_continuous h50
  have h52 : ∀ f ∈ F, ∃ α ∈ uniformity Y,
    (Prod.map (dSystemY.map (t * f)) (dSystemY.map (t * f))) '' α ⊆ γ := by
    intro f hf
    specialize h51 f hf
    let α := {z : Y × Y | (dSystemY.map (t * f) z.1, dSystemY.map (t * f) z.2) ∈ γ}
    have h53 : α ∈ uniformity Y := by
      apply uniformContinuous_def.mp
      · exact h51
      exact hγ1
    use α
    constructor
    · exact h53
    intro w hw1
    rcases hw1 with ⟨u, hu1, hu2⟩
    unfold α at hu1
    rw [<- hu2]
    unfold Prod.map
    simp
    simpa
  choose φ hφ1 hφ2 using h52
  have h6 : ∃ α ∈ uniformity Y, ∀ f ∈ F,
  (Prod.map (dSystemY.map (t * f)) (dSystemY.map (t * f))) '' α ⊆ γ := by
    let α := ⋂ f, ⋂ (h : f ∈ F), φ f h
    use α
    constructor
    · let G := hF1.toFinset
      let ψ : S → Set (Y × Y) := fun f => ⋂ (h : f ∈ F), φ f h
      have hα3 : α = ⋂ f ∈ F, ψ f := by
        simp only [α, ψ]
        ext x
        constructor
        · intro hx
          simp at hx
          simp [hx]
        · intro hx
          simp only [Set.mem_iInter] at hx
          simp only [Set.mem_iInter]
          intro i hi
          specialize hx i hi hi
          exact hx
      have hα4 : α = ⋂ f ∈ (G : Set S), ψ f := by
        rw [hα3]
        simp [G]
      rw [hα4]
      classical
      refine Finset.induction_on G ?h_empty ?h_insert
      · simp
      intro a s has1 has2
      simp only [Finset.coe_insert, Set.mem_insert_iff, SetLike.mem_coe,
        Set.iInter_iInter_eq_or_left, Filter.inter_mem_iff, Filter.biInter_finset_mem]
      constructor
      · unfold ψ
        simp [hφ1]
      intro i hi
      unfold ψ
      simp [hφ1]
    · intro f hf
      have h6a : α ⊆ φ f hf := by
        simp only [α]
        intro x hx
        simp only [Set.mem_iInter] at hx
        specialize hx f hf
        exact hx
      have h6b : Prod.map (dSystemY.map (t * f)) (dSystemY.map (t * f)) '' α
        ⊆ Prod.map (dSystemY.map (t * f)) (dSystemY.map (t * f)) '' (φ f hf) := by
        exact Set.image_mono h6a
      have h6c : Prod.map (dSystemY.map (t * f)) (dSystemY.map (t * f)) '' (φ f hf)
        ⊆ γ := by
        specialize hφ2 f hf
        exact hφ2
      exact h6b.trans h6c
  rcases h6 with ⟨α, hα1, hα2⟩
  have h61 : ∃ W : Set Y, W ∈ nhds y ∧ IsOpen W ∧ ((closure W) ×ˢ (closure W) ⊆ α) := by
    apply openClosureProductInEntourage
    exact hα1
  have h61a : ∀ s : S, dSystem.map s x = Subtype.val (dSystemY.map s x') := by
    intro s
    rfl
  have h61b : orbit dSystem x = Subtype.val '' (orbit dSystemY x') := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨s, hs⟩
      specialize h61a s
      have h61b1 : dSystem.map s x = z := by
        exact hs
      rw [<- h61b1]
      rw [h61a]
      simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta,
        Subtype.coe_prop, exists_const]
      unfold orbit
      simp
    intro hz
    rcases hz with ⟨t, hz2, hz3⟩
    rcases hz2 with ⟨s, hs⟩
    rw [<- hz3]
    rw [<- hs]
    simp only
    unfold orbit
    simp only [Set.mem_range]
    use s
    specialize h61a s
    exact h61a
  have h61c : closure (orbit dSystem x) = closure (Subtype.val '' (orbit dSystemY x')) := by
    simp [h61b]
  have h61d : Y = closure (Subtype.val '' (orbit dSystemY x')) := by
    rw [<- h61c]
    exact Y_def
  have h61e : Y = Subtype.val '' (closure (orbit dSystemY x')) := by
    simp only [h61d]
    apply subtype_closure_eq_of_isClosed
    unfold orbitClosure at Y_def
    simp [Y_def]
  have h61f : closure (orbit dSystemY x') = Subtype.val ⁻¹' Y := by
    simp [h61e]
  have h62 : Set.univ = closure (orbit dSystemY x') := by
    simp [h61f]
  have h7 : ∃ s : S, (dSystemY.map s x', y) ∈ α := by
    rcases h61 with ⟨W, hW1, hW2, hW3⟩
    have h7a1 : Subtype.val y ∈ Y := by
      simp
    have h7a2 : (W ∩ orbit dSystemY x').Nonempty := by
      apply mem_closure_iff_nhds.mp
      · rw [<- h62]
        simp
      exact hW1
    have h7a : ∃ s : S, (dSystemY.map s x' ∈ W) := by
      rcases h7a2 with ⟨z, hz1, hz2⟩
      unfold orbit at hz2
      rcases hz2 with ⟨s, hs⟩
      use s
      have h7a3 : dSystemY.map s x' = z := by
        exact hs
      rw [h7a3]
      exact hz1
    have h7b : W ×ˢ W ⊆ α := by
      have h7b1 : W ⊆ closure W := by
        exact subset_closure
      have h7b2 : W ×ˢ W ⊆ closure W ×ˢ closure W := by
        simpa
      exact h7b2.trans hW3
    rcases h7a with ⟨s, hs⟩
    use s
    have h7c : y ∈ W := by
      rcases mem_nhds_iff.mp hW1 with ⟨Z, hZ1, hZ2, hZ3⟩
      apply hZ1
      exact hZ3
    have h7d : (dSystemY.map s x', y) ∈ W ×ˢ W := by
      exact ⟨hs, h7c⟩
    apply h7b
    exact h7d
  rcases h7 with ⟨s, hs⟩
  have h8 : ∃ f ∈ F, dSystemY.map (t * f * s) x' ∈ V := by
    specialize hF2 s
    rcases hF2 with ⟨f, hf1, hf2⟩
    use f
    constructor
    · exact hf1
    · unfold Vt at hf2
      unfold visitTimeSet at hf2
      simp only [dSystemY.mapMult]
      have h8a : dSystemY.map (f * s) x' ∈ (dSystemY.map t ⁻¹' V) := by
        exact hf2
      have h8b : dSystemY.map t (dSystemY.map (f * s) x') ∈ V := by
        exact h8a
      have h8c : dSystemY.map t (dSystemY.map (f * s) x')
      = dSystemY.map t (dSystemY.map f (dSystemY.map s x')):= by
        simp [dSystemY.mapMult]
      rw [<- h8c]
      exact h8b
  rcases h8 with ⟨f, hf1, hf2⟩
  have h9 : (dSystemY.map (t * f * s) x', dSystemY.map (t * f) y)
    = (dSystemY.map (t * f) (dSystemY.map s x'), dSystemY.map (t * f) y) := by
      simp [dSystemY.mapMult]
  have h10 : (dSystemY.map (t * f * s) x', dSystemY.map (t * f) y)
  ∈ (Prod.map (dSystemY.map (t * f)) (dSystemY.map (t * f))) '' α := by
    rw [h9]
    refine ⟨(dSystemY.map s x', y), hs, ?_⟩
    rfl
  have h11 : (dSystemY.map (t * f * s) x', dSystemY.map (t * f) y) ∈ γ := by
    specialize hα2 f hf1
    apply hα2
    exact h10
  have h12 : dSystemY.map (t * f) y ∈ U := by
    apply hγ2 (dSystemY.map (t * f * s) x') hf2
    exact h11
  use t * f
have hYDenseOrbit : ∀ y : Y, Dense (orbit dSystemY y) := by
  intro y
  apply dense_iff_inter_open.mpr
  specialize hYUreturn y
  intro U hU1 hU2
  specialize hYUreturn U hU1 hU2
  unfold orbit
  obtain ⟨s, hs⟩ := hYUreturn
  have hmore : dSystemY.map s y ∈ Set.range fun s ↦ dSystemY.map s y := by
    simp
  exact ⟨dSystemY.map s y, hs, hmore⟩
have hYMinimal : isMinimalSystem dSystemY := by
  simp only [minimalIffDenseOrbits]
  exact hYDenseOrbit
rw [<- Y_def]
rw [minimalSubsetIffMinimalSubsystem]
exact hYMinimal

/-- If `y` is in the orbit closure of a uniformly recurrent point `x`, then
`y` is uniformly recurrent -/
theorem inOrbitClosOfURPointImpliesUR
(dSystem : DynamicalSystem S X)
{x : X} (xisUR : isUniformlyRecurrent dSystem x)
{y : X} (yinOrbClos : y ∈ orbitClosure dSystem x) :
isUniformlyRecurrent dSystem y := by
let Y := orbitClosure dSystem x
have hY : isNonemptyCompactT2InvariantSubset dSystem Y := by
  apply orbitClosureIsNonemptyCompactT2InvariantSubset
have hYMinimal : isMinimalSubset dSystem Y := by
  apply orbitClosureOfURPointIsMinimalSubset
  exact xisUR
let dSystemY := fromNonemptyCompactT2InvariantSubsetToSystem dSystem hY
have : CompactSpace Y := by
  apply isCompact_iff_compactSpace.mp
  exact hY.2.1
have : Nonempty Y := by
  apply hY.1.to_subtype
have hdSystemY_Minimal : isMinimalSystem dSystemY := by
  rw [←minimalSubsetIffMinimalSubsystem]
  exact hYMinimal
unfold isUniformlyRecurrent
intro U' hU'
rw [mem_nhds_iff] at hU'
obtain ⟨U, hU, hU2, hyU⟩ := hU'
let V := U ∩ Y
have hyY: y ∈ Y := by
  unfold Y
  exact yinOrbClos
have hyV : y ∈ V := by
  unfold V
  exact ⟨hyU, hyY⟩
have hVY : V ⊆ Y := by
  unfold V
  simp
let V' := {y : Y | (y : X) ∈ V}
have hV'U : V' = (Subtype.val ⁻¹' U) := by
  unfold V' V Subtype.val
  simp
  rfl
have hV'open : IsOpen V' := by
  rw [hV'U]
  simpa using hU2.preimage continuous_subtype_val
have hyV' : ⟨y, hyY⟩ ∈ V' := by
  exact hyV
have hSynd1 : isSyndetic (visitTimeSet dSystemY ⟨y, hyY⟩ V' ) := by
  apply minimalImpliesSyndeticVisits
  · apply hdSystemY_Minimal
  · exact ⟨⟨y, hyY⟩, hyV'⟩
  exact hV'open
have hSyndetic : isSyndetic (visitTimeSet dSystem y V) := by
  obtain ⟨F, hF1, hF2⟩ := hSynd1
  unfold isSyndetic
  use F
  constructor
  · exact hF1
  intro s
  specialize hF2 s
  obtain ⟨f, hf1, hf2⟩ := hF2
  use f
  constructor
  · exact hf1
  simpa
obtain ⟨F, hF1, hF2⟩ := hSyndetic
unfold isSyndetic
use F
constructor
· apply hF1
intro s
have hF22 := hF2 s
obtain ⟨f, hf1, hf2⟩ := hF22
use f
constructor
· apply hf1
have hUV : V ⊆ U := by
  unfold V
  simp
unfold visitTimeSet
simp only [Set.mem_preimage]
have hV3 : dSystem.map (f * s) y ∈ V := by
  unfold visitTimeSet at hf2
  simp only [Set.mem_preimage] at hf2
  exact hf2
apply hU
apply hUV
exact hV3

/-- If y belongs to a minimal subset Y of dynamical system X, then y is uniformly recurrent -/
lemma inMinimalSubsetUR
{dSystemX : DynamicalSystem S X} {Y : Set X}
(hYMin : isMinimalSubset dSystemX Y)
{y : X} (hyInY : y ∈ Y) :
isUniformlyRecurrent dSystemX y := by
let hYMinCopy := hYMin
rcases hYMinCopy with ⟨hY1, hY2⟩
let dSystemY := fromNonemptyCompactT2InvariantSubsetToSystem dSystemX hY1
rcases hY1 with ⟨hY1a, hY1b, hY1c, hY1d⟩
have hYCompactSpace : CompactSpace Y := by
  apply isCompact_iff_compactSpace.mp
  exact hY1b
have hYNonempty : Nonempty Y := by
  apply Set.Nonempty.to_subtype
  exact hY1a
have hSystemYMin : isMinimalSystem dSystemY := by
  rw [<- minimalSubsetIffMinimalSubsystem]
  exact hYMin
let y' : Y := ⟨y, hyInY⟩
have hy'UniRec : isUniformlyRecurrent dSystemY y' := by
  apply minimalImpliesUniformlyRecurrent
  exact hSystemYMin
have hySubtypeval : y = Subtype.val y' := by
  rfl
rw [hySubtypeval]
rcases hYMin with ⟨hYInv, hYMin2⟩
apply URInSubsystemImpliesURInSystem dSystemX hYInv
have hdSystemYDef : dSystemY = fromNonemptyCompactT2InvariantSubsetToSystem dSystemX hYInv := by
  rfl
rw [<- hdSystemYDef]
exact hy'UniRec

/-- Preimage of a subsystem under a factor map is a subsystem -/
lemma preimageSubsystemIsSubsystem
{dSystemX : DynamicalSystem S X}
{Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
{dSystemY : DynamicalSystem S Y}
{π : X → Y}
(hπFactorMap : isFactorMap dSystemX dSystemY π)
(Z : Set Y) (hZInv : isNonemptyCompactT2InvariantSubset dSystemY Z) :
isNonemptyCompactT2InvariantSubset dSystemX (π ⁻¹' Z) := by
rcases hZInv with ⟨hZ1, hZ2, hZ3, hZ4⟩
rcases hπFactorMap with ⟨hπ1, hπ2, hπ3⟩
unfold isNonemptyCompactT2InvariantSubset
constructor
· apply Set.Nonempty.preimage
  · exact hZ1
  · exact hπ2
constructor
· apply IsClosed.isCompact
  apply IsClosed.preimage
  · exact hπ1
  · apply IsCompact.isClosed
    exact hZ2
constructor
· infer_instance
· unfold isInvariantSet
  intro s
  specialize hZ4 s
  intro x hx
  simp only [Set.mem_preimage] at hx
  specialize hZ4 hx
  unfold isEquivariant at hπ3
  simp only [Set.mem_preimage]
  specialize hπ3 s
  have hCompo : (dSystemY.map s ∘ π) x = (π ∘ dSystemX.map s) x := by
    apply congr_fun hπ3
  have hCompo1 : (dSystemY.map s ∘ π) x = dSystemY.map s (π x) := by
    simp
  have hCompo2 : (π ∘ dSystemX.map s) x = π (dSystemX.map s x) := by
    simp
  have hCompo3 : π (dSystemX.map s x) = dSystemY.map s (π x) := by
    rw [<- hCompo2, <- hCompo, hCompo1]
  rw [hCompo3]
  exact hZ4

/-- If π : X → Y is a factor map and y ∈ Y is uniformly recurrent, then there exists
uniformly recurrent point x ∈ X such that π x = y -/
theorem liftUniformRecurrentPoint
{dSystemX : DynamicalSystem S X}
{Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
{dSystemY : DynamicalSystem S Y}
{π : X → Y}
(hπFactorMap : isFactorMap dSystemX dSystemY π)
(y : Y) (hYUniRec : isUniformlyRecurrent dSystemY y) :
∃ x : X, π x = y ∧ isUniformlyRecurrent dSystemX x := by
let Z := orbitClosure dSystemY y
have hZInv : isNonemptyCompactT2InvariantSubset dSystemY Z := by
  apply orbitClosureIsNonemptyCompactT2InvariantSubset
have hZMin : isMinimalSubset dSystemY Z := by
  apply orbitClosureOfURPointIsMinimalSubset
  exact hYUniRec
have hyInZ : y ∈ Z := by
  apply URPointBelongsToOrbitClosure
  exact hYUniRec
let dSystemZ := fromNonemptyCompactT2InvariantSubsetToSystem dSystemY hZInv
let X1 := π ⁻¹' Z
have hX1Inv : isNonemptyCompactT2InvariantSubset dSystemX X1 := by
  apply preimageSubsystemIsSubsystem
  · exact hπFactorMap
  · exact hZInv
let dSystemX1 := fromNonemptyCompactT2InvariantSubsetToSystem dSystemX hX1Inv
have hX1Nonempty : Nonempty X1 := by
  rcases hX1Inv with ⟨hX1Nonempty, hX1Compact, hX13⟩
  apply Set.Nonempty.to_subtype hX1Nonempty
have hX1CompactSpace : CompactSpace X1 := by
  rcases hX1Inv with ⟨hX1Nonempty, hX1Compact, hX13⟩
  apply isCompact_iff_compactSpace.mp
  exact hX1Compact
have hExistW1 := existsMinimalSubset dSystemX1
rcases hExistW1 with ⟨W1, hW1⟩
let W : Set X := Subtype.val '' W1
have hWMin : isMinimalSubset dSystemX W := by
  rcases hW1 with ⟨hW1Inv, hW1Min⟩
  unfold isMinimalSubset
  have hW1InvCopy := hW1Inv
  rcases hW1InvCopy with ⟨hW1a, hW1b, hW1c, hW1d⟩
  have hW1Compact : CompactSpace W1 := by
    apply isCompact_iff_compactSpace.mp
    exact hW1b
  have hW1Nonempty : Nonempty W1 := by
    apply Set.Nonempty.to_subtype
    exact hW1a
  constructor
  · apply subSystemOfSubsystem dSystemX hX1Inv
    have hX1System : dSystemX1 =
      (fromNonemptyCompactT2InvariantSubsetToSystem dSystemX hX1Inv) := by
      rfl
    rw [<- hX1System]
    exact hW1Inv
  · intro M hMa hMb
    let M1 : Set X1 := Subtype.val ⁻¹' M
    have hW1W : W1 = Subtype.val ⁻¹' W := by
      simp [W]
    have hM1inW1 : M1 ⊆ W1 := by
      simp only [M1]
      simp only [hW1W]
      apply Set.preimage_mono hMa
    have hM1Inv : isNonemptyCompactT2InvariantSubset dSystemX1 M1 := by
      rcases hMb with ⟨hMb1, hMb2, hMb3, hMb4⟩
      simp only [M1]
      constructor
      · have hExistx := Set.nonempty_def.mp hMb1
        rcases hExistx with ⟨x, hx⟩
        simp only [Set.nonempty_def, Set.mem_preimage, Subtype.exists, exists_prop]
        use x
        constructor
        · have hWinX1 : W ⊆ X1 := by
            simp [W]
          apply hWinX1
          apply hMa hx
        · exact hx
      constructor
      · simp only [Subtype.isCompact_iff, Subtype.image_preimage_coe]
        apply IsCompact.inter
        · rcases hX1Inv with ⟨hX1a, hX1b, hX1c, hX1d⟩
          exact hX1b
        · exact hMb2
      constructor
      · infer_instance
      · unfold isInvariantSet
        intro s
        specialize hMb4 s
        intro y hy
        let x := Subtype.val y
        have hxM : x ∈ M := by
          exact hy
        specialize hMb4 hxM
        have hEqualThing : Subtype.val (dSystemX1.map s y) = dSystemX.map s x := by
          rfl
        simp only [Set.mem_preimage, hEqualThing]
        exact hMb4
    specialize hW1Min M1 hM1inW1 hM1Inv
    have hMSubtype : M = Subtype.val '' M1 := by
      simp only [Subtype.image_preimage_coe, Set.right_eq_inter, M1]
      have hWSubX1 : W ⊆ X1 := by
        simp [W]
      exact hMa.trans hWSubX1
    simp only [hMSubtype, Set.image_val_inj, W]
    exact hW1Min
have hImageMin : isMinimalSubset dSystemY (π '' W) := by
  rcases hπFactorMap with ⟨hπ1, hπ2, hπ3⟩
  apply imageOfMinimalSetIsMinimal π
  · exact hπ1
  · exact hπ3
  · exact hWMin
have hImageWSubset : π '' W ⊆ Z := by
  simp only [Set.image_subset_iff]
  have hX1Equi : X1 = π ⁻¹' Z := by
    rfl
  rw [<- hX1Equi]
  simp [W]
have hImageEqua : Z = π '' W := by
  unfold isMinimalSubset at hZMin
  rcases hZMin with ⟨hZ1, hZ2⟩
  rcases hImageMin with ⟨hπW1, hπW2⟩
  specialize hZ2 (π '' W) hImageWSubset hπW1
  exact hZ2
rw [hImageEqua] at hyInZ
simp only [Set.mem_image] at hyInZ
rcases hyInZ with ⟨x, hx1, hx2⟩
use x
constructor
· exact hx2
· exact inMinimalSubsetUR hWMin hx1

end Uniform_recurrence

section Minimality_and_UR_with_commutivity

/-- If a commutative semigroup `S` acts minimally, then it acts surjectively -/
theorem minimalCommActionIsSurjective
{S} [commSemi : CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :
isSurjectiveSystem dSystem :=
by
  intro s y
  let sX := (dSystem.map s) '' Set.univ
  have imageIsSubsystem : isNonemptyCompactT2InvariantSubset dSystem sX := by
    unfold isNonemptyCompactT2InvariantSubset
    refine ⟨?_ ,?_ ,?_ ,?_⟩
    · unfold sX
      rewrite [Set.image_nonempty (f := dSystem.map s)]
      exact Set.univ_nonempty
    · exact (IsCompact.image isCompact_univ (dSystem.mapCont s))
    · infer_instance
    · unfold isInvariantSet
      intro t x xinsX
      rcases xinsX with ⟨y, hy, imgyisx⟩
      simp only [← imgyisx]
      simp only [(dSystem.mapMult t s y).symm]
      simp only [commSemi.mul_comm t s]
      simp only [dSystem.mapMult s t y]
      have tyinUniv : dSystem.map t y ∈ Set.univ := Set.mem_univ (dSystem.map t y)
      unfold sX
      unfold Set.image
      use dSystem.map t y
  unfold isMinimalSystem at hMin
  have sXisX : sX = Set.univ := hMin sX imageIsSubsystem
  unfold sX at sXisX
  unfold Set.image at sXisX
  have yInUniv : y ∈ Set.univ := Set.mem_univ y
  rewrite [← sXisX] at yInUniv
  rcases yInUniv with ⟨a,ha1,ha2⟩
  use a

/-- If `S` is a commutative semigroup that acts minimally on `X`, then the set
of pairs `(x,y) ∈ X × X` that are uniformly recurrent under the diagonal action
is dense in `X × X` -/
theorem inMinCommSystemURPairsDense
{S} [commSemi : CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :
Dense {(x,y) : X × X | isUniformlyRecurrent (diagDynamicalSystem dSystem dSystem) (x,y)} := by
let A := {(x,y) : X × X | isUniformlyRecurrent (diagDynamicalSystem dSystem dSystem) (x,y)}
have hDefA : A = {(x,y) : X × X | isUniformlyRecurrent (diagDynamicalSystem dSystem dSystem) (x,y)}
  := by
  rfl
have hZ : ∃ Z : Set (X × X), isMinimalSubset (diagDynamicalSystem dSystem dSystem) Z := by
  apply existsMinimalSubset
have hFactor : isFactorMap (diagDynamicalSystem dSystem dSystem) dSystem Prod.fst := by
  unfold isFactorMap
  constructor
  · exact continuous_fst
  constructor
  · intro b
    have h1 : ∃ x : X, True := by
      simp
    rcases h1 with ⟨x, hx⟩
    use (b, x)
  unfold isEquivariant
  intro s
  ext z
  simp only [Function.comp_apply]
  unfold diagDynamicalSystem
  simp
rcases hZ with ⟨Z, hZ⟩
have hZDown : isNonemptyCompactT2InvariantSubset dSystem (Prod.fst '' Z) := by
  rcases hZ with ⟨hZ1, hZ2⟩
  apply imageOfSubsystemIsSubsystem (diagDynamicalSystem dSystem dSystem) (dSystem) Prod.fst
  · exact hZ1
  · exact continuous_fst
  rcases hFactor with ⟨hZDown1, hZDown2, hZDown3⟩
  exact hZDown3
have hZX : Prod.fst '' Z = Set.univ := by
  specialize hMin (Prod.fst '' Z) hZDown
  simp [hMin]
have hUV : ∀ U V : Set X, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
  ((U ×ˢ V) ∩ A).Nonempty := by
  intro U V hU1 hU2 hV1 hV2
  have h2 : ∃ z ∈ Z, z.1 ∈ U := by
    rcases hU2 with ⟨x, hx⟩
    have h2a : x ∈ Prod.fst '' Z := by
      rw [hZX]
      simp
    rcases h2a with ⟨z, hz1, hz2⟩
    use z
    constructor
    · exact hz1
    rw [hz2]
    exact hx
  rcases h2 with ⟨z, hz1, hz2⟩
  have h3 : ∃ s : S, dSystem.map s z.2 ∈ V := by
    have h3a : Dense (orbit dSystem z.2) := by
      apply (minimalIffDenseOrbits dSystem).mp hMin
    have h3b : (V ∩ (orbit dSystem z.2)).Nonempty := by
      apply dense_iff_inter_open.mp h3a
      · exact hV1
      exact hV2
    rcases h3b with ⟨x, hx1, hx2⟩
    unfold orbit at hx2
    rcases hx2 with ⟨s, hs⟩
    use s
    have h3c : x = dSystem.map s z.2 := by
      rw [<- hs]
    rw [<- h3c]
    exact hx1
  rcases h3 with ⟨s, hs⟩
  have h4 : (z.1, dSystem.map s z.2) ∈ U ×ˢ V := by
    simp only [Set.mem_prod]
    constructor
    · exact hz2
    exact hs
  have hZCC : IsCompact Z := by
    rcases hZ with ⟨hZ1, hZ2⟩
    rcases hZ1 with ⟨hZ3, hZ4, hZ5⟩
    exact hZ4
  let φ : X × X → X × X := fun (x, y) ↦ (x, dSystem.map s y)
  let Y := φ '' Z
  have hφEquivariant : isEquivariant (diagDynamicalSystem dSystem dSystem).map
    (diagDynamicalSystem dSystem dSystem).map φ := by
    unfold isEquivariant
    intro t
    funext w
    have hφ1: ((diagDynamicalSystem dSystem dSystem).map t ∘ φ) w
      = ((dSystem.map t w.1), dSystem.map (t * s) w.2) := by
      simp only [Function.comp_apply]
      have hφ1a : φ w = (w.1, dSystem.map s w.2) := by
        rfl
      rw [hφ1a]
      have hφ1b: (diagDynamicalSystem dSystem dSystem).map t (w.1, dSystem.map s w.2)
        = (dSystem.map t w.1, dSystem.map t (dSystem.map s w.2)) := by
        rfl
      rw [hφ1b]
      have hφ1c : dSystem.map t (dSystem.map s w.2) = dSystem.map (t * s) w.2 := by
        simp [dSystem.mapMult t s w.2]
      rw [hφ1c]
    have hφ2: (φ ∘ (diagDynamicalSystem dSystem dSystem).map t) w
      = ((dSystem.map t w.1), dSystem.map (s * t) w.2) := by
      simp only [Function.comp_apply]
      have hφ2a : (diagDynamicalSystem dSystem dSystem).map t w
        = (dSystem.map t w.1, dSystem.map t w.2) := by
        rfl
      rw [hφ2a]
      have hφ2b : φ (dSystem.map t w.1, dSystem.map t w.2)
        = (dSystem.map t w.1, dSystem.map s (dSystem.map t w.2)) := by
        rfl
      rw [hφ2b]
      simp [dSystem.mapMult]
    rw [hφ1, hφ2]
    have hts : t * s = s * t := by
      exact commSemi.mul_comm t s
    rw [hts]
  have hφContinuous : Continuous φ := by
    apply Continuous.prodMk
    · exact continuous_fst
    apply Continuous.comp
    · exact dSystem.mapCont s
    exact continuous_snd
  have hI : isNonemptyCompactT2InvariantSubset (diagDynamicalSystem dSystem dSystem) Y := by
    apply imageOfSubsystemIsSubsystem (diagDynamicalSystem dSystem dSystem)
      (diagDynamicalSystem dSystem dSystem) φ Z
    · exact hφContinuous
    · exact hφEquivariant
    rcases hZ with ⟨hZ1⟩
    exact hZ1
  have hYCompact0 : IsCompact Y := by
    exact IsCompact.image hZCC hφContinuous
  have hYCompact : CompactSpace Y := by
    exact isCompact_iff_compactSpace.mp hYCompact0
  have hYNonempty : Nonempty Y := by
    have hZN1 : φ z ∈ φ '' Z := by
      simp only [Set.mem_image, Prod.exists]
      use z.1
      use z.2
    exact ⟨φ z, hZN1⟩
  have hYMinSubset : isMinimalSubset (diagDynamicalSystem dSystem dSystem) Y := by
    apply imageOfMinimalSetIsMinimal
    · exact hφContinuous
    · exact hφEquivariant
    exact hZ
  let dSystemY := fromNonemptyCompactT2InvariantSubsetToSystem
    (diagDynamicalSystem dSystem dSystem) hI
  have hYMinimal : isMinimalSystem dSystemY := by
    apply (minimalSubsetIffMinimalSubsystem (diagDynamicalSystem dSystem dSystem) hI).mp
    exact hYMinSubset
  have hInclude : (z.1, dSystem.map s z.2) ∈ φ '' Z := by
    have hInclude1 : φ z = (z.1, dSystem.map s z.2) := by
      rfl
    rw [<- hInclude1]
    simp only [Set.mem_image, Prod.exists]
    use z.1
    use z.2
  have hUR1 : isUniformlyRecurrent dSystemY ⟨(z.1, dSystem.map s z.2), hInclude⟩ := by
    apply minimalImpliesUniformlyRecurrent
    exact hYMinimal
  have hUR2 : isUniformlyRecurrent (diagDynamicalSystem dSystem dSystem)
    (z.1, dSystem.map s z.2) := by
    intro U hU1
    let V := {y : φ '' Z | Subtype.val y ∈ U}
    have hV :  V ∈ nhds ⟨(z.1, dSystem.map s z.2), hInclude⟩ := by
      simp only [V]
      let w := (z.1, dSystem.map s z.2)
      have hw : w = (z.1, dSystem.map s z.2) := by
        rfl
      simp only [<- hw]
      simp only [<- hw] at hU1
      have hV1 : nhds ⟨w, hInclude⟩ = Filter.comap Subtype.val (nhds w) := by
        apply nhds_subtype
      rw [hV1]
      simp only [Filter.mem_comap]
      use U
      constructor
      · exact hU1
      rfl
    specialize hUR1 V hV
    exact hUR1
  have hFinal : (z.1, dSystem.map s z.2) ∈ A := by
    exact hUR2
  have hFinal2 : (z.1, dSystem.map s z.2) ∈ (U ×ˢ V) ∩ A := by
    exact ⟨h4, hFinal⟩
  exact ⟨(z.1, dSystem.map s z.2), hFinal2⟩
have hA : ∀ W : Set (X × X), IsOpen W → W.Nonempty → (W ∩ A).Nonempty := by
  intro W hW1 hW2
  have hA1 : ∃ U V : Set X, IsOpen U ∧ U.Nonempty ∧ IsOpen V ∧ V.Nonempty ∧  U ×ˢ V ⊆ W := by
    have hA1a : ∀ (a b : X), (a, b) ∈ W → ∃ (U V : Set X),
    IsOpen U ∧ IsOpen V ∧ a ∈ U ∧ b ∈ V ∧ U ×ˢ V ⊆ W := by
      apply isOpen_prod_iff.mp
      exact hW1
    rcases hW2 with ⟨z, hz⟩
    have hA1b : ∃ a b : X, (a, b) = z := by
      simp
    rcases hA1b with ⟨a, b, hab⟩
    have hA1c : (a, b) ∈ W := by
      rw [hab]
      exact hz
    specialize hA1a a b hA1c
    rcases hA1a with ⟨U, V, hU1, hV1, hU2, hV2, hUV1⟩
    have hU1' : U.Nonempty := by
      exact ⟨a, hU2⟩
    have hV1' : V.Nonempty := by
      exact ⟨b, hV2⟩
    use U
    use V
  rcases hA1 with ⟨U, V, hU1, hU2, hV1, hV2, hUV0⟩
  specialize hUV U V hU1 hU2 hV1 hV2
  have hA2 : (U ×ˢ V) ∩ A ⊆ W ∩ A := by
    apply Set.inter_subset_inter_left
    exact hUV0
  exact Set.Nonempty.mono hA2 hUV
rw [<- hDefA]
exact dense_iff_inter_open.mpr hA

/-- If A and B ⊆ S are thick then closure A U = closure B⁻¹ U for any open U ⊆ X × X -/
theorem forwardBackwardSetOrbClosCoincideInBronsSys
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X)
(hDense :
Dense {(x, y) : X × X | isUniformlyRecurrent (diagDynamicalSystem dSystem dSystem) (x, y)})
(A B : Set S) (hAThick : isThick A) (hBThick : isThick B)
(W : Set (X × X)) (hWOpen : IsOpen W) :
closure (setOrbitAlongASet (diagDynamicalSystem dSystem dSystem) A W)
= closure (inverseSetOrbitAlongASet (diagDynamicalSystem dSystem dSystem) B W) := by
apply Set.Subset.antisymm_iff.mpr
constructor
· intro z hz
  apply mem_closure_iff.mpr
  intro V hV1 hV2
  let hVA := mem_closure_iff.mp hz
  specialize hVA V hV1 hV2
  have hVExists := Set.inter_nonempty.mp hVA
  rcases hVExists with ⟨v, hv1, hv2⟩
  simp only [setOrbitAlongASet, Set.iUnion_coe_set, Set.mem_iUnion, Set.mem_image, Prod.exists,
    exists_prop] at hv2
  rcases hv2 with ⟨s, hs1, hs2⟩
  rcases hs2 with ⟨a, b, hab1, hab2⟩
  have hInterNonempty : (W ∩ (diagDynamicalSystem dSystem dSystem).map s ⁻¹' V).Nonempty := by
    apply Set.inter_nonempty.mpr
    use (a, b)
    constructor
    · exact hab1
    · simp only [Set.mem_preimage]
      rw [hab2]
      exact hv1
  have hIntOpen : IsOpen (W ∩ (diagDynamicalSystem dSystem dSystem).map s ⁻¹' V) := by
    apply IsOpen.inter
    · exact hWOpen
    · apply IsOpen.preimage
      · exact (diagDynamicalSystem dSystem dSystem).mapCont s
      · exact hV1
  have hEInter := dense_iff_inter_open.mp
    hDense (W ∩ (diagDynamicalSystem dSystem dSystem).map s ⁻¹' V)
    hIntOpen hInterNonempty
  have hExiOne := Set.inter_nonempty.mp hEInter
  rcases hExiOne with ⟨t, ht1, ht2⟩
  simp only [Prod.mk.eta, Set.mem_setOf_eq] at ht2
  let Bs := {b * s | b ∈ B}
  have hBsThick : isThick Bs := by
    unfold isThick
    intro F hF
    unfold isThick at hBThick
    specialize hBThick F hF
    rcases hBThick with ⟨t, ht⟩
    use t * s
    simp only [Set.image_subset_iff, Set.preimage_setOf_eq, Bs]
    simp only [Set.image_subset_iff] at ht
    intro f hf
    simp only [Set.mem_setOf_eq]
    specialize ht hf
    simp only [Set.mem_preimage] at ht
    use f * t
    constructor
    · exact ht
    · exact Semigroup.mul_assoc f t s
  have htInClosure : t ∈ closure
    (setOrbitAlongASet (diagDynamicalSystem dSystem dSystem) Bs {t}) := by
    apply uniformRecurrentPointBelongToThickOrbit
    · exact hBsThick
    · exact ht2
  have hInter2 := mem_closure_iff.mp htInClosure W hWOpen
  have htInW : t ∈ W := by
    let h := (Set.mem_inter_iff t W ((diagDynamicalSystem dSystem dSystem).map s ⁻¹' V)).mp ht1
    rcases h with ⟨h1, h2⟩
    exact h1
  specialize hInter2 htInW
  have hENew1 := Set.inter_nonempty.mp hInter2
  rcases hENew1 with ⟨x, hx1, hx2⟩
  simp only [setOrbitAlongASet, Set.image_singleton, Set.iUnion_singleton_eq_range, Set.mem_range,
    Subtype.exists, exists_prop] at hx2
  rcases hx2 with ⟨r, hr1, hr2⟩
  simp only [Set.mem_setOf_eq, Bs] at hr1
  rcases hr1 with ⟨b, hb1, hb2⟩
  have hAlmostGoal : (diagDynamicalSystem dSystem dSystem).map s t ∈
    V ∩ ((diagDynamicalSystem dSystem dSystem).map b) ⁻¹' W := by
    apply Set.mem_inter
    · apply Set.mem_preimage.mp
      let h := (Set.mem_inter_iff t W ((diagDynamicalSystem dSystem dSystem).map s ⁻¹' V)).mp ht1
      rcases h with ⟨h1, h2⟩
      exact h2
    · simp only [Set.mem_preimage]
      have hEq : (diagDynamicalSystem dSystem dSystem).map (b * s) t
        = (diagDynamicalSystem dSystem dSystem).map b
        ((diagDynamicalSystem dSystem dSystem).map s t) := by
        exact (diagDynamicalSystem dSystem dSystem).mapMult b s t
      rw [<- hEq, hb2, hr2]
      exact hx1
  let m := (diagDynamicalSystem dSystem dSystem).map s t
  apply Set.inter_nonempty.mpr
  use m
  constructor
  · simp only [m]
    apply Set.mem_of_mem_of_subset hAlmostGoal
    simp
  · unfold inverseSetOrbitAlongASet
    simp only [Set.iUnion_coe_set, Set.mem_iUnion, Set.mem_preimage, exists_prop]
    use b
    constructor
    · exact hb1
    · simp only [m]
      apply Set.mem_preimage.mp
      apply Set.mem_of_mem_of_subset hAlmostGoal
      simp
· intro z hz
  apply mem_closure_iff.mpr
  intro V hV1 hV2
  let hVA := mem_closure_iff.mp hz
  specialize hVA V hV1 hV2
  have hVExists := Set.inter_nonempty.mp hVA
  rcases hVExists with ⟨v, hv1, hv2⟩
  simp only [inverseSetOrbitAlongASet, Set.iUnion_coe_set, Set.mem_iUnion, Set.mem_preimage,
    exists_prop] at hv2
  rcases hv2 with ⟨s, hs1, hs2⟩
  have hNonempty : (V ∩ ((diagDynamicalSystem dSystem dSystem).map s) ⁻¹' W).Nonempty := by
    apply Set.inter_nonempty.mpr
    use v
    constructor
    · exact hv1
    · simp only [Set.mem_preimage]
      exact hs2
  have hInterOpen : IsOpen (V ∩ ((diagDynamicalSystem dSystem dSystem).map s) ⁻¹' W) := by
    apply IsOpen.inter
    · exact hV1
    · apply IsOpen.preimage
      · exact (diagDynamicalSystem dSystem dSystem).mapCont s
      · exact hWOpen
  have hEInter := dense_iff_inter_open.mp
    hDense (V ∩ ((diagDynamicalSystem dSystem dSystem).map s) ⁻¹' W)
    hInterOpen hNonempty
  have hExiOne := Set.inter_nonempty.mp hEInter
  rcases hExiOne with ⟨y, hy1, hy2⟩
  simp only [Prod.mk.eta, Set.mem_setOf_eq] at hy2
  let As := {a * s | a ∈ A}
  have hAsThick : isThick As := by
    unfold isThick
    intro F hF
    unfold isThick at hAThick
    specialize hAThick F hF
    rcases hAThick with ⟨t, ht⟩
    use t * s
    simp only [Set.image_subset_iff, Set.preimage_setOf_eq, As]
    simp only [Set.image_subset_iff] at ht
    intro f hf
    simp only [Set.mem_setOf_eq]
    specialize ht hf
    simp only [Set.mem_preimage] at ht
    use f * t
    constructor
    · exact ht
    · exact Semigroup.mul_assoc f t s
  have hyInClosure : y ∈ closure
    (setOrbitAlongASet (diagDynamicalSystem dSystem dSystem) As {y}) := by
    apply uniformRecurrentPointBelongToThickOrbit
    · exact hAsThick
    · exact hy2
  have hInter2 := mem_closure_iff.mp hyInClosure V hV1
  have hyInV : y ∈ V := by
    have h := (Set.mem_inter_iff y V ((diagDynamicalSystem dSystem dSystem).map s ⁻¹' W)).mp hy1
    rcases h with ⟨h1, h2⟩
    exact h1
  specialize hInter2 hyInV
  have hENew1 := Set.inter_nonempty.mp hInter2
  rcases hENew1 with ⟨x, hx1, hx2⟩
  simp only [setOrbitAlongASet, Set.image_singleton, Set.iUnion_singleton_eq_range, Set.mem_range,
    Subtype.exists, exists_prop] at hx2
  rcases hx2 with ⟨r, hr1, hr2⟩
  simp only [Set.mem_setOf_eq, As] at hr1
  rcases hr1 with ⟨a, ha1, ha2⟩
  have hIn1 : (diagDynamicalSystem dSystem dSystem).map (a * s) y ∈ V := by
    rw [ha2, hr2]
    exact hx1
  have hIn2 : (diagDynamicalSystem dSystem dSystem).map (a * s) y ∈
    setOrbitAlongASet (diagDynamicalSystem dSystem dSystem) A W := by
    simp only [setOrbitAlongASet, Set.iUnion_coe_set, Set.mem_iUnion, Set.mem_image, Prod.exists,
      exists_prop]
    use a
    constructor
    · exact ha1
    · let m :=  (diagDynamicalSystem dSystem dSystem).map s y
      use m.1
      use m.2
      constructor
      · simp only [Prod.mk.eta]
        simp only [m]
        have hInterExpandRight := Set.mem_of_mem_inter_right hy1
        simp only [Set.mem_preimage] at hInterExpandRight
        exact hInterExpandRight
      · simp only [Prod.mk.eta]
        simp only [m]
        rw [(diagDynamicalSystem dSystem dSystem).mapMult a s y]
  apply Set.inter_nonempty.mpr
  use (diagDynamicalSystem dSystem dSystem).map (a * s) y

end Minimality_and_UR_with_commutivity

section Proximality

variable {S : Type*} [Semigroup S] [Nonempty S]
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]

/-- Points `x` and `y` are proximal under the semigroup action of `S` on `X`
if for all neighborhoods `α` of the diagonal in `X × X`, there exists `s ∈ S`
such that `(sx, sy) ∈ α` -/
def proximal
(dSystem : DynamicalSystem S X) (x y : X) :
Prop :=
∀ α ∈ nhdsSet (Set.diagonal X), ∃ (s : S), (dSystem.map s x, dSystem.map s y) ∈ α

/-- In a minimal action of `S` on `X`, if `x` and `y` are proximal, then
the `S`-orbit closure (under the diagonal action) of `(x,y)` contains the diagonal of `X` -/
theorem minSystemOrbitClosProxPairContainsDiag
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem)
{x y : X} (hProx : proximal dSystem x y) :
Set.diagonal X ⊆
orbitClosure (diagDynamicalSystem dSystem dSystem) (x,y) :=
by
  unfold proximal at hProx
  unfold Set.diagonal
  intro z hz
  let diagSemiAct := (diagDynamicalSystem dSystem dSystem)
  let orb := orbit diagSemiAct (x,y)
  have orbMeetsNhdDiag : ∀ α ∈ nhdsSet (Set.diagonal X), (α ∩ orb).Nonempty := by
    intro α αNhd
    rcases (hProx α αNhd) with ⟨s, hs⟩
    have proxResultInorb : (dSystem.map s x, dSystem.map s y) ∈ orb := by
      use s
      rfl
    exact Set.nonempty_of_mem ⟨hs, proxResultInorb⟩
  let orbClos := orbitClosure diagSemiAct (x,y)
  have orbClosMeetsDiag : (Set.diagonal X ∩ orbClos).Nonempty :=
    by exact closureIntersect orbMeetsNhdDiag
  rcases orbClosMeetsDiag with ⟨w, hw⟩
  have diagInOrbofw : z ∈ orbitClosure diagSemiAct w := by
    unfold orbitClosure
    simp only [mem_closure_iff]
    intro W WOpen zInW
    have WisNhd : W ∈ nhds (z.1,z.1) := by
      rewrite [mem_nhds_iff]
      nth_rw 2 [hz] -- Rewrite only the second instance of z.1 to a z.2
      use W
    simp only [mem_nhds_prod_iff] at WisNhd
    rcases WisNhd with ⟨U, Unhd, V, Vnhd, UtimesVinW⟩
    have UcapVnhd : U ∩ V ∈ nhds z.1 := Filter.inter_mem Unhd Vnhd
    have orbw1VisitsUcapV : ∃ (s : S), dSystem.map s w.1 ∈ U ∩ V := by
      rewrite [mem_nhds_iff] at UcapVnhd
      rcases UcapVnhd with ⟨E, EinUcapV, Eopen, z1inE⟩
      rewrite [minimalIffDenseOrbits] at hMin
      specialize hMin w.1
      apply Dense.inter_open_nonempty at hMin
      specialize hMin E Eopen (Set.nonempty_of_mem z1inE)
      rcases hMin with ⟨k,hk,hk2⟩
      unfold orbit Set.range at hk2
      rcases hk2 with ⟨s, hs⟩
      change dSystem.map s w.1 = k at hs
      apply (EinUcapV) at hk
      rewrite [hs.symm] at hk
      use s
    rcases orbw1VisitsUcapV with ⟨s, hs⟩
    have orbwVisitsW : (dSystem.map s w.1, dSystem.map s w.2) ∈ W := by
      have orbwVisitsUV : (dSystem.map s w.1, dSystem.map s w.2) ∈ U ×ˢ V := by
        constructor
        · change dSystem.map s w.1 ∈ U
          exact Set.inter_subset_left hs
        · change dSystem.map s w.2 ∈ V
          rewrite [← hw.1]
          exact Set.inter_subset_right hs
      exact UtimesVinW orbwVisitsUV
    have orbwinOrb : (dSystem.map s w.1, dSystem.map s w.2) ∈ orbit diagSemiAct w := by
      change (diagDynamicalSystem dSystem dSystem).map s w ∈ orbit diagSemiAct w
      use s
    exact Set.nonempty_of_mem ⟨orbwVisitsW, orbwinOrb⟩
  exact orbitTransitivity hw.2 diagInOrbofw

/-- If `π : X → Y` is a factor map of `S`-systems and `(x,y)` is a proximal
pair in `X`, then `(π x, π y)` is a proximal pair in `Y` -/
theorem imageOfProxByFactorIsProx
{dSystem : DynamicalSystem S X}
{Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
{dSystemY : DynamicalSystem S Y}
{π : X → Y} (hπ : isFactorMap dSystem dSystemY π)
{x y : X} (hProx : proximal dSystem x y) :
proximal dSystemY (π x) (π y) := by
unfold proximal
intro α hα
let β := (Prod.map π π) ⁻¹' α
have h1 : β ∈ nhdsSet (Set.diagonal X) := by
  --unfold nhdsSet
  --unfold nhdsSet at hα
  rcases hπ with ⟨hπ1, hπ2, hπ3⟩
  simp only [β]
  apply mem_nhdsSet_iff_exists.mpr
  apply mem_nhdsSet_iff_exists.mp at hα
  rcases hα with ⟨V, hα2, hα3, hα4⟩
  let U := Prod.map π π ⁻¹' V
  use U
  constructor
  · apply IsOpen.preimage
    · apply Continuous.prodMap
      · exact hπ1
      exact hπ1
    exact hα2
  constructor
  · simp only [U]
    have h11 : Prod.map π π '' (Set.diagonal X) ⊆ Set.diagonal Y := by
      intro z hz
      simp only [Set.mem_image, Set.mem_diagonal_iff, Prod.exists, Prod.map_apply,
        exists_eq_left'] at hz
      unfold Set.diagonal
      rcases hz with ⟨hz1, hz2⟩
      rw [<- hz2]
      simp
    simp at h11
    have h12 : Prod.map π π ⁻¹' Set.diagonal Y ⊆ Prod.map π π ⁻¹' V := by
      apply Set.preimage_mono
      exact hα3
    exact h11.trans h12
  simp only [U]
  apply Set.preimage_mono
  exact hα4
specialize hProx β h1
obtain ⟨s, hs⟩ := hProx
use s
have h21 : (dSystemY.map s ∘ π) x = (π ∘ dSystem.map s) x := by
  rcases hπ with ⟨hπ1, hπ2, hπ3⟩
  unfold isEquivariant at hπ3
  specialize hπ3 s
  rw [hπ3]
have h22 : dSystemY.map s (π x) = (dSystemY.map s ∘ π) x := by
  rfl
have h23 : π (dSystem.map s  x) = (π ∘ dSystem.map s) x := by
  rfl
have h24 : dSystemY.map s (π x) = π (dSystem.map s  x) := by
  simpa
have h31 : (dSystemY.map s ∘ π) y = (π ∘ dSystem.map s) y := by
  unfold isFactorMap at hπ
  rcases hπ with ⟨hπ1, hπ2, hπ3⟩
  unfold isEquivariant at hπ3
  specialize hπ3 s
  rw [hπ3]
have h322 : dSystemY.map s (π y) = (dSystemY.map s ∘ π) y := by
  rfl
have h33 : π (dSystem.map s  y) = (π ∘ dSystem.map s) y := by
  rfl
have h34 : dSystemY.map s (π y) = π (dSystem.map s y) := by
  simpa
rw [h24, h34]
have h4 :  (π (dSystem.map s x), π (dSystem.map s y))
= (Prod.map π π) ((dSystem.map s x), (dSystem.map s y)) := by
  rfl
rw [h4]
simpa

end Proximality

section Regional_proximality_basics

/-- The regionally proximal relation for a dynamical system, as type `Set (X × X)` -/
def RP
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
Set (X × X) :=
⋂ α ∈ nhdsSet (Set.diagonal X),
closure (inverseSetOrbit (diagDynamicalSystem dSystem dSystem) α)

/-- The regionally proximal relation is symmetric -/
theorem RPisSymmetric
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
isSymmetric (RP dSystem) := sorry

/-- The regionally proximal relation is invariant under the diagonal
action by `S`, provided that `S` is commutative -/
theorem RPInCommSemiIsInvariant
{S : Type*} [CommSemigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
isInvariantSet (diagDynamicalSystem dSystem dSystem) (RP dSystem) := sorry

/-- The regionally proximal relation is closed -/
theorem RPisClosed
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
IsClosed (RP dSystem) := sorry

/-- If `SX` is dense in `X` (a basic nondegeneracy criterion), then `RP` is reflexive -/
theorem RPisReflexive
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
isReflexive (RP dSystem) := sorry


/-- For `π : X → Y` a factor map of systems, `(π ⊗ π) RP_X ⊆ RP_Y` -/
theorem imageOfRPIsInRP
{S : Type*} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemX : DynamicalSystem S X)
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemY : DynamicalSystem S Y)
(π : X → Y) {hπ : isFactorMap dSystemX dSystemY π} :
(Prod.map π π) '' (RP dSystemX) ⊆ RP dSystemY := by sorry


/-- A pair `(x,y) ∈ RP` if and only if orbit closure of open
neighborhoods of `(x,y)` intersect the diagonal -/
theorem inRPiffForwardUOrbitClosHitsDiag
{S : Type*} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemX : DynamicalSystem S X) (z : X × X) :
z ∈ RP dSystemX ↔ ∀ (U : Set (X × X)), IsOpen U → z ∈ U → (Set.diagonal X ∩
  setOrbitClosure (diagDynamicalSystem dSystemX dSystemX) U).Nonempty := by sorry


/-- The backward regionally proximal relation for a dynamical system, as type `Set (X × X)` -/
def RPM
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
Set (X × X) :=
⋂ α ∈ nhdsSet (Set.diagonal X),
setOrbitClosure (diagDynamicalSystem dSystem dSystem) α

/-- The backward regionally proximal relation is symmetric -/
theorem RPMisSymmetric
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
isSymmetric (RPM dSystem) := by
unfold isSymmetric
unfold Symmetric
intro x y hxy
unfold RPM at hxy
unfold RPM
unfold setToRelation
simp only [Set.mem_iInter]
unfold setToRelation at hxy
simp only [Set.mem_iInter] at hxy
intro V hV
let U := Prod.swap '' V
have hUDef : U = Prod.swap '' V := by rfl
have hVfU : V = Prod.swap '' U := by
  simp only [U]
  ext t
  constructor
  · simp only [Set.mem_image, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq, ↓existsAndEq,
    true_and, exists_eq_right]
    intro ht
    use t.2, t.1
  · intro ht
    simp only [Set.mem_image, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq, ↓existsAndEq, true_and,
      exists_eq_right] at ht
    rcases ht with ⟨a, b, hab1, hab2⟩
    rw [<- hab2]
    exact hab1
have hU : U ∈ nhdsSet (Set.diagonal X) := by
  have hV1 : ∃ W : Set (X × X), IsOpen W ∧ Set.diagonal X ⊆ W ∧ W ⊆ V := by
    apply mem_nhdsSet_iff_exists.mp
    exact hV
  rcases hV1 with ⟨W, hW1, hW2, hW3⟩
  have hWProdOpen : IsOpen (Prod.swap '' W) := by
    have hWProdOpen1 : Prod.swap '' W = Prod.swap ⁻¹' W := by
      ext x
      constructor
      · intro hx
        simp only [Set.mem_image, Prod.exists, Prod.swap_prod_mk] at hx
        rcases hx with ⟨a, b, ha, hb⟩
        rw [<- hb]
        simpa
      · intro hx
        simp at hx
        simp only [Set.mem_image, Prod.exists, Prod.swap_prod_mk]
        have : (x.2, x.1) ∈ W := by
          simpa
        use x.2
        use x.1
    rw [hWProdOpen1]
    apply IsOpen.preimage
    · apply continuous_swap
    exact hW1
  have hWProdDiag : Set.diagonal X ⊆ Prod.swap '' W := by
    intro z hz
    have hz1 : z.1 = z.2 := by
      simpa
    have hz2 : z ∈ W := by
      apply hW2
      exact hz
    have hz3 : z = (z.1, z.1) := by
      have hz3a : z = (z.1, z.2) := rfl
      rw [hz3a]
      rw [hz1]
    have hz4 : (z.1, z.1) ∈ W := by
      rw [<- hz3]
      exact hz2
    simp only [Set.mem_image, Prod.exists, Prod.swap_prod_mk]
    use z.2
    use z.1
    constructor
    · rw [<- hz1]
      exact hz4
    rfl
  have hWProdContained : Prod.swap '' W ⊆ U := by
    rw [hUDef]
    exact Set.image_mono hW3
  apply mem_nhdsSet_iff_exists.mpr
  use Prod.swap '' W
specialize hxy U hU
have hGoal : ∀ A ∈ nhds (x, y), ∃ u ∈ U, ∃ s : S,
(diagDynamicalSystem dSystem dSystem).map s (u.1, u.2) ∈ A := by
  intro A hA
  have hGoal1 : ∃ o ⊆ A, IsOpen o ∧ (x, y) ∈ o := by
    exact mem_nhds_iff.mp hA
  rcases hGoal1 with ⟨o, ho1, ho2, ho3⟩
  have hGoal2 : (o ∩ setOrbit (diagDynamicalSystem dSystem dSystem) U).Nonempty := by
    apply mem_closure_iff.mp hxy
    · exact ho2
    exact ho3
  rcases hGoal2 with ⟨z, hz1, hz2⟩
  have hGoal3 : ∃ u ∈ U, ∃ s, (diagDynamicalSystem dSystem dSystem).map s (u.1, u.2) = z := by
    simp only [Prod.mk.eta, Prod.exists]
    rcases hz2 with ⟨t, hz2b⟩
    rw [<- hz2b]
    simp only
    use (t.2).val.1
    use (t.2).val.2
    simp
  rcases hGoal3 with ⟨u, hu, s, hus⟩
  use u
  constructor
  · exact hu
  use s
  rw [hus]
  apply ho1
  exact hz1
have hCor : ∀ B ∈ nhds (y, x), ∃ v ∈ V, ∃ s : S,
(diagDynamicalSystem dSystem dSystem).map s (v.1, v.2) ∈ B := by
  intro B hB
  let A := Prod.swap '' B
  have hAB : B = Prod.swap '' A := by
    simp only [A]
    ext t
    constructor
    · simp only [Set.mem_image, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq, ↓existsAndEq,
      true_and, exists_eq_right]
      intro ht
      use t.2, t.1
    · intro ht
      simp only [Set.mem_image, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq, ↓existsAndEq,
        true_and, exists_eq_right] at ht
      rcases ht with ⟨a, b, hab1, hab2⟩
      rw [<- hab2]
      exact hab1
  have hAfromB : A ∈ nhds (x, y) := by
    apply mem_nhds_iff.mp at hB
    rcases hB with ⟨W, hW1, hW2, hW3⟩
    apply mem_nhds_iff.mpr
    use Prod.swap '' W
    constructor
    · simp only [Set.image_subset_iff, A]
      have hB1 : Prod.swap ⁻¹' (Prod.swap '' B) = B := by
        ext x
        simp
      rw [hB1]
      exact hW1
    constructor
    · have hW20 : Prod.swap '' W = Prod.swap ⁻¹' W := by
        ext x
        constructor
        · intro hx
          simp only [Set.mem_image, Prod.exists, Prod.swap_prod_mk] at hx
          rcases hx with ⟨a, b, ha, hb⟩
          rw [<- hb]
          simpa
        · intro hx
          simp at hx
          simp only [Set.mem_image, Prod.exists, Prod.swap_prod_mk]
          have : (x.2, x.1) ∈ W := by
            simpa
          use x.2
          use x.1
      rw [hW20]
      apply IsOpen.preimage
      · apply continuous_swap
      exact hW2
    simpa
  specialize hGoal A hAfromB
  rcases hGoal with ⟨u, hu, s, hs⟩
  use (u.2, u.1)
  constructor
  · rw [hVfU]
    simp [hu]
  simp only
  use s
  have hCor1 : (dSystem.map s u.1, dSystem.map s u.2) ∈ A := by
    simpa
  have hCor2 : (dSystem.map s u.2, dSystem.map s u.1) ∈ B := by
    rw [hAB]
    simpa
  simpa
apply mem_closure_iff.mpr
intro W hW1 hW2
have hWNei : W ∈ nhds (y, x) := by
  apply mem_nhds_iff.mpr
  use W
specialize hCor W hWNei
rcases hCor with ⟨v, hv, s, hs⟩
have hW1 : (diagDynamicalSystem dSystem dSystem).map s (v.1, v.2)
∈ setOrbit (diagDynamicalSystem dSystem dSystem) V := by
  simp only [Prod.mk.eta]
  unfold setOrbit
  simp only [Set.mem_range, Prod.exists, Subtype.exists, exists_prop]
  use s
  use v.1
  use v.2
exact ⟨(diagDynamicalSystem dSystem dSystem).map s (v.1, v.2), hs, hW1⟩

/-- The backward regionally proximal relation is invariant under the diagonal
action by `S` -/
theorem RPMisInvariant
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
isInvariantSet (diagDynamicalSystem dSystem dSystem) (RPM dSystem) := by
have h1 : ∀ α ∈ nhdsSet (Set.diagonal X), isInvariantSet (diagDynamicalSystem dSystem dSystem)
  (setOrbit (diagDynamicalSystem dSystem dSystem) α) := by
  intro α hα
  unfold isInvariantSet
  intro s y hy
  rcases hy with ⟨t, ht⟩
  have hy1 : ∃ r : S, ∃ z ∈ α, y = (diagDynamicalSystem dSystem dSystem).map r z := by
    use t.1
    use t.2
    constructor
    · simp
    simp only [ht]
  rcases hy1 with ⟨r, z, hrz1, hrz2⟩
  rw [hrz2]
  have h2 : (diagDynamicalSystem dSystem dSystem).map s
    ((diagDynamicalSystem dSystem dSystem).map r z)
    = (diagDynamicalSystem dSystem dSystem).map (s * r) z := by
    rw [(diagDynamicalSystem dSystem dSystem).mapMult s r z]
  rw [h2]
  unfold setOrbit
  simp only [Set.mem_range, Prod.exists, Subtype.exists, exists_prop]
  use s * r
  use z.1
  use z.2
have h2 : ∀ α ∈ nhdsSet (Set.diagonal X),
isInvariantSet (diagDynamicalSystem dSystem dSystem) (setOrbitClosure
(diagDynamicalSystem dSystem dSystem) α) := by
  intro α hα
  apply closureOfInvIsInv
  specialize h1 α hα
  exact h1
unfold RPM
let C := {setOrbitClosure (diagDynamicalSystem dSystem dSystem) α | α ∈ nhdsSet (Set.diagonal X)}
have h3 : (⋂ α ∈ nhdsSet (Set.diagonal X), setOrbitClosure (diagDynamicalSystem dSystem dSystem) α)
= C.sInter := by
  ext t
  constructor
  · intro ht
    simp only [Set.mem_iInter] at ht
    simp only [Set.mem_sInter]
    intro p hp
    rcases hp with ⟨q, hq, hpq⟩
    specialize ht q hq
    rw [<- hpq]
    exact ht
  · intro ht
    simp only [Set.mem_sInter] at ht
    simp only [Set.mem_iInter]
    intro p hp
    have h4 : setOrbitClosure (diagDynamicalSystem dSystem dSystem) p ∈ C := by
      unfold C
      simp only [Set.mem_setOf_eq]
      use p
    specialize ht (setOrbitClosure (diagDynamicalSystem dSystem dSystem) p) h4
    exact ht
rw [h3]
apply intersectionOfInvIsInv
intro A hA
rcases hA with ⟨B, hB, hAB⟩
specialize h2 B hB
rw [<- hAB]
exact h2

/-- The backward regionally proximal relation is closed -/
theorem RPMisClosed
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
IsClosed (RPM dSystem) := by
apply isClosed_iInter
intro U
apply isClosed_iInter
intro hU
exact isClosed_closure

/-- If `SX` is dense in `X` (a basic nondegeneracy criterion), then `RPM` is reflexive -/
theorem RPMisReflexiveIfNondegen
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X)
(hNondegen : setOrbitClosure dSystem Set.univ = Set.univ) :
isReflexive (RPM dSystem) := by
unfold isReflexive
unfold Reflexive
intro x
unfold RPM
unfold setToRelation
simp only [Set.mem_iInter]
intro U hU
have hUDiag1 : ∃ W : Set (X × X), IsOpen W ∧ Set.diagonal X ⊆ W ∧ W ⊆ U := by
  apply mem_nhdsSet_iff_exists.mp
  exact hU
rcases hUDiag1 with ⟨hU1, hU2, hU3, hU4⟩
have hUDiag2 : Set.diagonal X ⊆ U := by
  exact hU3.trans hU4
have h1 : ∀ o : Set X, IsOpen o → x ∈ o → (o ∩ setOrbit dSystem Set.univ).Nonempty := by
  apply mem_closure_iff.mp
  unfold setOrbitClosure at hNondegen
  rw [hNondegen]
  simp
have h2 : ∀ o : Set X, IsOpen o → x ∈ o → ∃ s : S, ∃ y : X, dSystem.map s y ∈ o := by
  intro o ho1 ho2
  specialize h1 o ho1 ho2
  rcases h1 with ⟨z, h1a, h1b⟩
  rcases h1b with ⟨t, ht⟩
  use t.1
  use t.2
  have h11p : z = dSystem.map t.1 t.2 := by
    rw [<- ht]
  rw [<- h11p]
  exact h1a
have hGoal0 : ∀ u : Set (X × X), IsOpen u → (x, x) ∈ u
→ (u ∩ setOrbit (diagDynamicalSystem dSystem dSystem) (Set.diagonal X)).Nonempty := by
  intro u hu1 hu2
  have hG01 : ∃ u1 u2 : Set X, IsOpen u1 ∧ IsOpen u2 ∧ x ∈ u1 ∧ x ∈ u2 ∧ u1 ×ˢ u2 ⊆ u := by
    apply isOpen_prod_iff.mp
    · exact hu1
    exact hu2
  rcases hG01 with ⟨u1, u2, hu1, hu2, hu11, hu12, hu3⟩
  let v := u1 ∩ u2
  have hv1 : IsOpen v := by
    exact IsOpen.inter hu1 hu2
  have hv2 : x ∈ v := by
    simp only [Set.mem_inter_iff, v]
    constructor
    · exact hu11
    exact hu12
  specialize h2 v hv1 hv2
  rcases h2 with ⟨s, y, hsy⟩
  use (dSystem.map s y, dSystem.map s y)
  constructor
  · have huv0 : v ⊆ u1 := by
      simp [v]
    have huv1 : v ⊆ u2 := by
      simp [v]
    have huv2 : v ×ˢ v ⊆ u1 ×ˢ u2 := by
      apply Set.prod_mono
      · exact Set.inter_subset_left
      exact huv1
    have huv3 : v ×ˢ v ⊆ u := by
      exact huv2.trans hu3
    have huv4 : (dSystem.map s y, dSystem.map s y) ∈ v ×ˢ v := by
      simp only [Set.mem_prod, and_self]
      exact hsy
    apply huv3
    exact huv4
  have hDiag : (dSystem.map s y, dSystem.map s y)
  = (diagDynamicalSystem dSystem dSystem).map s (y, y) := by
    rfl
  rw [hDiag]
  unfold setOrbit
  simp
have hGoal1 : (x, x) ∈ setOrbitClosure (diagDynamicalSystem dSystem dSystem) (Set.diagonal X) := by
  apply mem_closure_iff.mpr
  exact hGoal0
have hGoal2 : setOrbitClosure (diagDynamicalSystem dSystem dSystem) (Set.diagonal X)
⊆ setOrbitClosure (diagDynamicalSystem dSystem dSystem) U := by
  unfold setOrbitClosure
  apply closure_mono
  apply Set.subset_def.mpr
  intro z hz
  unfold setOrbit at hz
  rcases hz with ⟨t, ht1⟩
  rw [<- ht1]
  unfold setOrbit
  simp only [Set.mem_range, Prod.exists, Subtype.exists, exists_prop]
  use t.1
  use t.2.val.1
  use t.2.val.2
  constructor
  · have ht12 : (t.2.val.1, t.2.val.2) ∈ Set.diagonal X := by
      simp
    apply hUDiag2
    exact ht12
  rfl
apply hGoal2
exact hGoal1

--DGG we may not use this lemma any more!
/- A minimal system satisfies the non-degeneracy condition required to conclude
that `RPM` is reflexive -/
/-
lemma minimalImpliesNondegen
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :
setOrbitClosure dSystem Set.univ = Set.univ := by
unfold setOrbitClosure
rcases (inferInstance : Nonempty X) with ⟨x⟩
have xDenseOrbit : Dense (orbit dSystem x) := (minimalIffDenseOrbits dSystem).mp hMin x
have xOrbitAll : closure (orbit dSystem x) = Set.univ := xDenseOrbit.closure_eq
have xOrbitInSetOrbit : orbit dSystem x ⊆ setOrbit dSystem Set.univ := by
  apply Set.subset_def.mpr
  intro y hy
  rcases hy with ⟨z, hz1⟩
  rw [<- hz1]
  unfold setOrbit
  simp
apply Set.Subset.antisymm
· simp
nth_rw 1 [<- xOrbitAll]
apply closure_mono
exact xOrbitInSetOrbit
-/

-- DGG: I updated the statement here to match the paper, but the proof now
-- needs to be updated.
/-- A pair `(x,y) ∈ RPM` if and only if inverse orbit closures open
neighborhoods of `(x,y)` intersect the diagonal -/
theorem inRPMiffBackwardUOrbitClosHitsDiag
{S : Type*} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemX : DynamicalSystem S X) (z : X × X) :
z ∈ RPM dSystemX ↔ ∀ (U : Set (X × X)), IsOpen U → z ∈ U → (Set.diagonal X ∩ closure
  (inverseSetOrbit (diagDynamicalSystem dSystemX dSystemX) U)).Nonempty := by
constructor
· intro hzRP U hUOpen hUContz
  unfold RPM at hzRP
  have hzInEach := Set.mem_sInter.mp hzRP
  simp only [Set.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff, Set.mem_iInter] at hzInEach
  have hUα : ∀ α ∈ nhdsSet (Set.diagonal X),
    ((setOrbit (diagDynamicalSystem dSystemX dSystemX) α) ∩ U).Nonempty := by
    intro α hα
    specialize hzInEach α hα
    unfold setOrbitClosure at hzInEach
    simp only [Set.inter_comm]
    apply mem_closure_iff_nhds.mp hzInEach
    exact hUOpen.mem_nhds hUContz
  have hUEv : ∀ α ∈ nhdsSet (Set.diagonal X),
    (α ∩ (inverseSetOrbit (diagDynamicalSystem dSystemX dSystemX) U)).Nonempty := by
    intro α hα
    specialize hUα α hα
    simp only [Set.inter_nonempty, Prod.exists] at hUα
    rcases hUα with ⟨a, b, hab1, hab2⟩
    simp only [setOrbit, Set.mem_range, Prod.exists, Subtype.exists, exists_prop] at hab1
    rcases hab1 with ⟨s, x, y, hxy1, hxy2⟩
    apply Set.inter_nonempty.mpr
    use (x, y)
    constructor
    · exact hxy1
    · simp only [inverseSetOrbit, Set.mem_iUnion, Set.mem_preimage]
      use s
      rw [hxy2]
      exact hab2
  apply Set.not_disjoint_iff_nonempty_inter.mp
  by_contra hContra
  let α := (closure (inverseSetOrbit (diagDynamicalSystem dSystemX dSystemX) U))ᶜ
  have hαNhds : α ∈ nhdsSet (Set.diagonal X) := by
    apply mem_nhdsSet.mpr
    use α
    constructor
    · simp
    constructor
    · apply isOpen_compl_iff.mpr
      apply isClosed_closure
    · apply Disjoint.subset_compl_right
      exact hContra
  specialize hUEv α hαNhds
  have hαInverseInter : Disjoint α (inverseSetOrbit (diagDynamicalSystem dSystemX dSystemX) U) := by
    apply Set.subset_compl_iff_disjoint_right.mp
    simp only [Set.compl_subset_compl, α]
    apply subset_closure
  have hαNotDisjoint : ¬ Disjoint α (inverseSetOrbit (diagDynamicalSystem dSystemX dSystemX) U) := by
    apply Set.not_disjoint_iff_nonempty_inter.mpr
    exact hUEv
  exact hαNotDisjoint hαInverseInter
· sorry

lemma inRPMiffBackwardUOrbitClosInterNeighDiag
{S : Type*} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemX : DynamicalSystem S X) (z : X × X) :
z ∈ RPM dSystemX ↔ ∀ (U α : Set (X × X)), IsOpen U → z ∈ U → IsOpen α → Set.diagonal X ⊆ α → (α ∩
  (inverseSetOrbit (diagDynamicalSystem dSystemX dSystemX) U)).Nonempty := by
sorry

/-- A point `(x,y)` belongs to `RPM` iff there exists `w ∈ X` and an ultrafilter `F` on
`X × X × S` whose pushforward under `(x,y,s) ↦ (x,y,sx,sy)` limits to `(w,w,x,y)` -/
theorem xyInRPMIffUltraToSomewwxy
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (x y : X) :
⟨x,y⟩ ∈ RPM dSystem ↔ ∃ (w : X) (F : Ultrafilter ((X × X) × S)),
    Filter.Tendsto (fun (⟨a,s⟩ : (X × X) × S) ↦ (a, (diagDynamicalSystem dSystem dSystem).map s a))
      F (nhds ⟨⟨w,w⟩,⟨x,y⟩⟩) := by
let φ := fun (⟨a,s⟩ : (X × X) × S) ↦ (a, (diagDynamicalSystem dSystem dSystem).map s a)
constructor
· intro hAssumption
  have hMapPrep : ∀ Z ∈ nhds (x, y), ∀ α ∈ nhdsSet (Set.diagonal X), ∃ t : (X × X) × S,
    φ t ∈ α ×ˢ Z := by
    intro Z hZ α hα
    have hRP := (inRPMiffBackwardUOrbitClosInterNeighDiag dSystem (x, y)).mp hAssumption
    rcases (mem_nhds_iff.mp hZ) with ⟨Z', hZ'1, hZ'2, hZ'3⟩
    rcases (mem_nhdsSet.mp hα) with ⟨α', hα'1, hα'2, hα'3⟩
    specialize hRP Z' α' hZ'2 hZ'3 hα'2 hα'3
    rcases Set.inter_nonempty.mp hRP with ⟨z, hz1, hz2⟩
    simp only [inverseSetOrbit, Set.mem_iUnion, Set.mem_preimage] at hz2
    rcases hz2 with ⟨s, hs⟩
    use (z, s)
    simp only [Set.mem_prod]
    constructor
    · simp only [φ]
      apply hα'1
      exact hz1
    · simp only [φ]
      apply hZ'1
      exact hs
  choose ψ hψ1 hψ2 using hMapPrep
  sorry
· intro hAssumption
  have hφDef : φ = fun (⟨a,s⟩ : (X × X) × S) ↦
    (a, (diagDynamicalSystem dSystem dSystem).map s a) := by
    rfl
  rw [<- hφDef] at hAssumption
  apply (inRPMiffBackwardUOrbitClosInterNeighDiag dSystem (x, y)).mpr
  intro Z α hZOpen hxy hαOpen hαDiag
  simp only [Filter.Tendsto] at hAssumption
  rcases hAssumption with ⟨w, F, hwF⟩
  have hNhds : α ×ˢ Z ∈ nhds ((w, w), (x, y)) := by
    apply prod_mem_nhds
    · apply mem_nhds_iff.mpr
      use α
      constructor
      · simp
      constructor
      · exact hαOpen
      · apply hαDiag
        simp
    · apply mem_nhds_iff.mpr
      use Z
  have hPreimage : φ ⁻¹' (α ×ˢ Z) ∈ F := by
    apply hwF
    exact hNhds
  have hNonempty : (φ ⁻¹' (α ×ˢ Z)).Nonempty := by
    apply Ultrafilter.nonempty_of_mem hPreimage
  have hExist := Set.nonempty_def.mp hNonempty
  rcases hExist with ⟨t, ht⟩
  simp only [Set.mem_preimage, Set.mem_prod] at ht
  simp only [φ] at ht
  rcases ht with ⟨ht1, ht2⟩
  apply Set.inter_nonempty.mpr
  use t.1
  constructor
  · exact ht1
  · simp only [inverseSetOrbit, Set.mem_iUnion, Set.mem_preimage]
    use t.2

/-- For `π : X → Y` a factor map of systems, `(π ⊗ π) RPM_X ⊆ RPM_Y` -/
theorem imageOfRPMIsInRPM
{S : Type*} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemX : DynamicalSystem S X)
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemY : DynamicalSystem S Y)
(π : X → Y) {hπ : isFactorMap dSystemX dSystemY π} :
(Prod.map π π) '' (RPM dSystemX) ⊆ RPM dSystemY := by
rcases hπ with ⟨hπ1, hπ2, hπ3⟩
have h0 : Set.range π = Set.univ := by
    unfold Function.Surjective at hπ2
    ext y
    constructor
    · simp
    intro hy
    specialize hπ2 y
    rcases hπ2 with ⟨a, ha⟩
    rw [<- ha]
    simp
have h1 : ∀ β ∈ nhdsSet (Set.diagonal Y),
  ∃ α ∈ nhdsSet (Set.diagonal X), (Prod.map π π) '' α = β := by
  intro β hβ
  let α := (Prod.map π π) ⁻¹' β
  use α
  constructor
  · have h1a : ∃ u ⊆ β, IsOpen u ∧ Set.diagonal Y ⊆ u := by
      apply mem_nhdsSet.mp hβ
    rcases h1a with ⟨u, hu1, hu2, hu3⟩
    apply mem_nhdsSet.mpr
    let v := (Prod.map π π) ⁻¹' u
    use v
    constructor
    · apply Set.preimage_mono
      exact hu1
    constructor
    · apply IsOpen.preimage
      · apply Continuous.prodMap
        · exact hπ1
        exact hπ1
      exact hu2
    have h1a1 : (Prod.map π π) '' Set.diagonal X ⊆ Set.diagonal Y := by
      intro t ht
      rcases ht with ⟨p, hp1, hp2⟩
      unfold Set.diagonal at hp1
      have hp3 : p.1 = p.2 := by
        exact hp1
      simp only [Set.mem_diagonal_iff]
      unfold Prod.map at hp2
      have ht1 : (π p.1, π p.2) = (t.1, t.2) := by
        exact hp2
      rw [hp3] at ht1
      have ht2 : π p.2 = t.1 := by
        have ht2a : π p.2 = Prod.fst (π p.2, π p.2) := by simp
        have ht2b : t.1 = Prod.fst (t.1, t.2) := by simp
        rw [ht2a, ht2b]
        rw [ht1]
      have ht3 : π p.2 = t.2 := by
        have ht3a : π p.2 = Prod.snd (π p.2, π p.2) := by simp
        have ht3b : t.2 = Prod.snd (t.1, t.2) := by simp
        rw [ht3a, ht3b]
        rw [ht1]
      rw [<- ht2, ht3]
    have h1b : Set.diagonal X ⊆ (Prod.map π π) ⁻¹' (Set.diagonal Y) := by
      simp only [Set.image_subset_iff] at h1a1
      exact h1a1
    simp only [v]
    have h1c : (Prod.map π π) ⁻¹' (Set.diagonal Y) ⊆ Prod.map π π ⁻¹' u := by
      apply Set.preimage_mono hu3
    exact h1b.trans h1c
  apply Set.image_preimage_eq_iff.mpr
  simp
  simp [h0]
have h2 : (Prod.map π π) '' RPM dSystemX ⊆ ⋂ α ∈ nhdsSet (Set.diagonal X),
(Prod.map π π) '' (setOrbitClosure (diagDynamicalSystem dSystemX dSystemX) α) := by
  let P := {α : Set (X × X) | α ∈ nhdsSet (Set.diagonal X)}
  let c : P → Set (X × X) := fun α ↦ setOrbitClosure (diagDynamicalSystem dSystemX dSystemX) α
  have h2a : RPM dSystemX = Set.iInter c := by
    unfold RPM
    unfold Set.iInter
    simp
    rfl
  have h2b : RPM dSystemX = ⋂ (i : P), c i := by
    unfold RPM
    simp
    rfl
  have h2c : ⋂ α ∈ nhdsSet (Set.diagonal X), Prod.map π π ''
    setOrbitClosure (diagDynamicalSystem dSystemX dSystemX) α =
    ⋂ (i : P), Prod.map π π '' (c i) := by
    simp
    rfl
  rw [h2b, h2c]
  exact Set.image_iInter_subset c (Prod.map π π)
have h3 : ∀ α ∈ nhdsSet (Set.diagonal X), (Prod.map π π) ''
  (setOrbitClosure (diagDynamicalSystem dSystemX dSystemX) α)
  ⊆ closure ((Prod.map π π) '' (setOrbit (diagDynamicalSystem dSystemX dSystemX) α)) := by
  intro α hα
  unfold setOrbitClosure
  apply image_closure_subset_closure_image
  apply Continuous.prodMap
  · exact hπ1
  exact hπ1
have h4 : ⋂ α ∈ nhdsSet (Set.diagonal X),
  (Prod.map π π) '' (setOrbitClosure (diagDynamicalSystem dSystemX dSystemX) α) ⊆
  ⋂ α ∈ nhdsSet (Set.diagonal X),
  closure ((Prod.map π π) '' (setOrbit (diagDynamicalSystem dSystemX dSystemX) α)) := by
  simp only [Set.subset_iInter_iff]
  intro i hi
  specialize h3 i hi
  have h4a :  ⋂ α ∈ nhdsSet (Set.diagonal X), Prod.map π π ''
    setOrbitClosure (diagDynamicalSystem dSystemX dSystemX) α
    ⊆ Prod.map π π '' setOrbitClosure (diagDynamicalSystem dSystemX dSystemX) i := by
    intro t ht
    simp only [Set.mem_iInter, Set.mem_image, Prod.exists, Prod.map_apply] at ht
    specialize ht i hi
    rcases ht with ⟨a, b, hab1, hab2⟩
    rw [<- hab2]
    simp only [Set.mem_image, Prod.exists, Prod.map_apply, Prod.mk.injEq]
    use a
    use b
  have h4b : Prod.map π π '' setOrbitClosure (diagDynamicalSystem dSystemX dSystemX) i
    ⊆ closure (Prod.map π π '' setOrbit (diagDynamicalSystem dSystemX dSystemX) i) := by
    unfold setOrbitClosure
    apply image_closure_subset_closure_image
    apply Continuous.prodMap
    · exact hπ1
    exact hπ1
  exact h4a.trans h4b
have h5prep : ∀ α ∈ nhdsSet (Set.diagonal X), (Prod.map π π) ''
  (setOrbit (diagDynamicalSystem dSystemX dSystemX) α)
  = setOrbit (diagDynamicalSystem dSystemY dSystemY) (Prod.map π π '' α) := by
  intro α hα
  unfold setOrbit
  ext z1
  constructor
  · intro hz1
    rcases hz1 with ⟨z2, hz3, hz4⟩
    simp only [Set.mem_range, Prod.exists, Subtype.exists, exists_prop] at hz3
    rcases hz3 with ⟨s, a, b, hab1, hab2⟩
    have h5prep1 : z1 = (π (dSystemX.map s a), π (dSystemX.map s b)) := by
      rw [<- hz4, <- hab2]
      rfl
    have h5prep2 : z1 = (dSystemY.map s (π a), dSystemY.map s (π b)) := by
      unfold isEquivariant at hπ3
      specialize hπ3 s
      have h5prep2a : ∀ x : X, (dSystemY.map s ∘ π) x = (π ∘ dSystemX.map s) x := by
        rw [<- hπ3]
        simp
      have h5prep2b : ∀ x : X, dSystemY.map s (π x) = π (dSystemX.map s x) := by
        intro x
        specialize h5prep2a x
        exact h5prep2a
      rw [h5prep1]
      simp only [Prod.mk.injEq]
      constructor
      · specialize h5prep2b a
        rw [h5prep2b]
      · specialize h5prep2b b
        rw [h5prep2b]
    rw [h5prep2]
    simp only [Set.mem_range, Prod.exists, Subtype.exists, Set.mem_image, Prod.map_apply,
      exists_prop, Prod.mk.injEq, ↓existsAndEq, and_true]
    use s
    use a
    use b
    constructor
    · exact hab1
    rfl
  intro hz1
  simp only [Set.mem_range, Prod.exists, Subtype.exists, Set.mem_image, Prod.map_apply, exists_prop,
    Prod.mk.injEq, ↓existsAndEq, and_true] at hz1
  rcases hz1 with ⟨s, a, b, hab1, hab2⟩
  have h5prep3 : z1 = (dSystemY.map s (π a), dSystemY.map s (π b)) := by
    rw [<- hab2]
    rfl
  have h5prep4 : z1 = (π (dSystemX.map s a), π (dSystemX.map s b)) := by
    specialize hπ3 s
    have h5prep3a : ∀ x : X, (dSystemY.map s ∘ π) x = (π ∘ dSystemX.map s) x := by
      rw [<- hπ3]
      simp
    have h5prep3b : ∀ x : X, dSystemY.map s (π x) = π (dSystemX.map s x) := by
      intro x
      specialize h5prep3a x
      exact h5prep3a
    rw [h5prep3]
    simp only [Prod.mk.injEq]
    constructor
    · specialize h5prep3b a
      exact h5prep3b
    specialize h5prep3b b
    exact h5prep3b
  rw [h5prep4]
  simp only [Set.mem_image, Set.mem_range, Prod.exists, Subtype.exists, exists_prop, Prod.map_apply,
    Prod.mk.injEq]
  use dSystemX.map s a
  use dSystemX.map s b
  constructor
  · use s
    use a
    use b
    constructor
    · exact hab1
    rfl
  constructor
  · rfl
  rfl
have h5 : ⋂ α ∈ nhdsSet (Set.diagonal X),
  closure ((Prod.map π π) '' (setOrbit (diagDynamicalSystem dSystemX dSystemX) α))
    ⊆ ⋂ α ∈ nhdsSet (Set.diagonal X), setOrbitClosure
    (diagDynamicalSystem dSystemY dSystemY) ((Prod.map π π) '' α) := by
  unfold setOrbitClosure
  simp only [Set.subset_iInter_iff]
  intro i hi
  specialize h5prep i hi
  rw [<- h5prep]
  intro y hy
  simp only [Set.mem_iInter] at hy
  specialize hy i hi
  exact hy
have h6 : ⋂ α ∈ nhdsSet (Set.diagonal X), setOrbitClosure
  (diagDynamicalSystem dSystemY dSystemY) ((Prod.map π π) '' α)
  ⊆ RPM dSystemY := by
  intro y hy
  simp only [Set.mem_iInter] at hy
  unfold RPM
  simp only [Set.mem_iInter]
  intro β hβ
  specialize h1 β hβ
  rcases h1 with ⟨α, hα1, hα2⟩
  specialize hy α hα1
  rw [hα2] at hy
  exact hy
exact ((h2.trans h4).trans h5).trans h6

-- lemma commMinOrbContainDiagonalForward
-- {S : Type*} [CommSemigroup S] [Nonempty S]
-- {X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
-- (dSystemX : DynamicalSystem S X) {hMin : isMinimalSystem dSystemX}
-- (z : X × X) (hzRP : z ∈ RP dSystemX)
-- (U : Set (X × X)) (hUz : U ∈ nhds z) :
-- Set.diagonal X ⊆ setOrbitClosure (diagDynamicalSystem dSystemX dSystemX) U := by
-- sorry

end Regional_proximality_basics

section Regional_proximality_in_min_comm_systems

/-- In minimal systems with a commutative acting semigroup, `RP = RPM` -/
theorem forwardEqualsBackwardRPInMinCommSystem
{S : Type*} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) {hMin : isMinimalSystem dSystem} :
RP dSystem = RPM dSystem := by sorry

--Instead of moveInside, can we not use imageClosureIsClosureImage from TP_Defs?
--This lemma really has nothing to do with commutative semigroups, right?
/-- For any `s ∈ S`, `s closure U ⊆ closure s U` -/
lemma moveInside
{S : Type*} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemX : DynamicalSystem S X)
(U : Set X) (s : S) :
(dSystemX.map s) '' closure U ⊆ closure (dSystemX.map s '' U) := by
intro x hx
simp only [Set.mem_image] at hx
rcases hx with ⟨v, hv1, hv2⟩
apply mem_closure_iff.mpr
intro W hW1 hW2
have hNeigh : v ∈ (dSystemX.map s) ⁻¹' W := by
  simp only [Set.mem_preimage]
  rw [hv2]
  exact hW2
have hPreWOpen : IsOpen ((dSystemX.map s) ⁻¹' W) := by
  apply IsOpen.preimage
  · exact dSystemX.mapCont s
  · exact hW1
have hGoal : ((dSystemX.map s) ⁻¹' W ∩ U).Nonempty := by
  apply mem_closure_iff.mp hv1
  · exact hPreWOpen
  · exact hNeigh
let hExist := Set.inter_nonempty.mp hGoal
rcases hExist with ⟨t, ht1, ht2⟩
simp only [Set.mem_preimage] at ht1
apply Set.inter_nonempty.mpr
use dSystemX.map s t
constructor
· exact ht1
· simp only [Set.mem_image]
  use t

-- DGG: I updated the statement of the theorem, but now the proof needs to be fixed.

/-- If a point `z ∈ X × X` is in `RPM`, then for every neighborhood `U` of `z`,
the closure of `S⁻¹U` contains the diagonal of `X × X` -/
theorem inMinCommxyInRPIffNhdOrbitClosContainsDiag
{S : Type*} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemX : DynamicalSystem S X) {hMin : isMinimalSystem dSystemX}
(z : X × X) :
(z ∈ RPM dSystemX ↔ ∀ (U : Set (X × X)), IsOpen U → z ∈ U → Set.diagonal X ⊆
  closure (inverseSetOrbit (diagDynamicalSystem dSystemX dSystemX) U))
∧
(z ∈ RPM dSystemX ↔ ∀ (U : Set (X × X)), IsOpen U → z ∈ U → Set.diagonal X ⊆
  setOrbitClosure (diagDynamicalSystem dSystemX dSystemX) U)
∧
(z ∈ RP dSystemX ↔ ∀ (U : Set (X × X)), IsOpen U → z ∈ U → Set.diagonal X ⊆
  closure (inverseSetOrbit (diagDynamicalSystem dSystemX dSystemX) U))
∧
(z ∈ RP dSystemX ↔ ∀ (U : Set (X × X)), IsOpen U → z ∈ U → Set.diagonal X ⊆
  setOrbitClosure (diagDynamicalSystem dSystemX dSystemX) U) := by
have RPMwithInvOrbit : z ∈ RPM dSystemX ↔ ∀ (U : Set (X × X)), IsOpen U → z ∈ U → Set.diagonal X ⊆
  closure (inverseSetOrbit (diagDynamicalSystem dSystemX dSystemX) U) := by
  constructor
  · intro hzRP U hUOpen hUContz
    let Z := closure (inverseSetOrbit (diagDynamicalSystem dSystemX dSystemX) U)
    have hZInvariant : ∀ s : S, (diagDynamicalSystem dSystemX dSystemX).map s '' Z ⊆ Z := by
      intro s
      let W := ⋃ t : S, (diagDynamicalSystem dSystemX dSystemX).map (t * s) ⁻¹' U
      have hZsubW : Z ⊆ closure W := by
        have hSThick : isThick (Set.univ : Set S) := by
          unfold isThick
          intro F hF
          have hSNonempty : Nonempty S := by
            infer_instance
          let s := Nonempty.some hSNonempty
          use s
          simp
        let Ss := {t * s | t : S}
        have hSsThick : isThick (Ss) := by
          unfold isThick
          intro F hF
          simp only [Set.image_subset_iff, Set.preimage_setOf_eq, Ss]
          use s
          have hEquaN : Set.univ ⊆ {a | ∃ t, t * s = a * s} := by
            intro u hu
            simp
          have hFUniv : F ⊆ Set.univ := by
            simp
          exact hFUniv.trans hEquaN
        have hSEqua1 : closure
          (setOrbitAlongASet (diagDynamicalSystem dSystemX dSystemX) (Set.univ : Set S) U)
          = closure
          (inverseSetOrbitAlongASet (diagDynamicalSystem dSystemX dSystemX) (Set.univ : Set S) U)
          := by
          apply forwardBackwardSetOrbClosCoincideInBronsSys
          · apply inMinCommSystemURPairsDense
            exact hMin
          · exact hSThick
          · exact hSThick
          · exact hUOpen
        have hSEqua2 : closure
          (setOrbitAlongASet (diagDynamicalSystem dSystemX dSystemX) (Set.univ : Set S) U)
          = closure (inverseSetOrbitAlongASet (diagDynamicalSystem dSystemX dSystemX) Ss U) := by
          apply forwardBackwardSetOrbClosCoincideInBronsSys
          · apply inMinCommSystemURPairsDense
            exact hMin
          · exact hSThick
          · exact hSsThick
          · exact hUOpen
        have hSEqua3 : Z = closure
          (inverseSetOrbitAlongASet (diagDynamicalSystem dSystemX dSystemX) (Set.univ : Set S) U)
          := by
          simp only [Z]
          apply Set.Subset.antisymm_iff.mpr
          constructor
          · apply closure_mono
            unfold inverseSetOrbit
            unfold inverseSetOrbitAlongASet
            simp
          · apply closure_mono
            unfold inverseSetOrbit
            unfold inverseSetOrbitAlongASet
            simp
        have hSEqua4 : closure W = closure
          (inverseSetOrbitAlongASet (diagDynamicalSystem dSystemX dSystemX) Ss U) := by
          unfold inverseSetOrbitAlongASet
          simp only [Set.coe_setOf, Set.mem_setOf_eq, W, Ss]
          apply Set.Subset.antisymm_iff.mpr
          constructor
          · apply closure_mono
            intro z hz
            simp only [Set.mem_iUnion, Set.mem_preimage] at hz
            rcases hz with ⟨r, hr⟩
            simp only [Set.mem_iUnion, Set.mem_preimage, Subtype.exists, exists_prop,
              exists_exists_eq_and]
            use r
          · apply closure_mono
            intro z hz
            simp only [Set.mem_iUnion, Set.mem_preimage, Subtype.exists, exists_prop,
              exists_exists_eq_and] at hz
            rcases hz with ⟨r, hr⟩
            simp only [Set.mem_iUnion, Set.mem_preimage]
            use r
        have hZequalW : Z = closure W := by
          rw [hSEqua3, hSEqua4, <- hSEqua2, <- hSEqua1]
        rw [hZequalW]
      have hsZsubsW : (diagDynamicalSystem dSystemX dSystemX).map s '' Z
        ⊆ (diagDynamicalSystem dSystemX dSystemX).map s '' closure W := by
        intro z hz
        simp only [Set.mem_image, Prod.exists] at hz
        rcases hz with ⟨a, b, hab1, hab2⟩
        simp only [Set.mem_image, Prod.exists]
        use a
        use b
        constructor
        · apply hZsubW hab1
        · exact hab2
      have hMovesIn : (diagDynamicalSystem dSystemX dSystemX).map s '' closure W ⊆
        closure ((diagDynamicalSystem dSystemX dSystemX).map s '' W) := by
        apply moveInside
      have hMovesIn1 : (diagDynamicalSystem dSystemX dSystemX).map s '' W
        = ⋃ t : S, (diagDynamicalSystem dSystemX dSystemX).map s ''
        (((diagDynamicalSystem dSystemX dSystemX).map (t * s)) ⁻¹' U) := by
        simp only [W]
        apply Set.image_iUnion
      have hMovesIn2 : closure ((diagDynamicalSystem dSystemX dSystemX).map s '' W)
        = closure (⋃ t : S, (diagDynamicalSystem dSystemX dSystemX).map s ''
        (((diagDynamicalSystem dSystemX dSystemX).map (t * s)) ⁻¹' U)) := by
        rw [hMovesIn1]
      have hMovesIn3 : closure (⋃ t : S, (diagDynamicalSystem dSystemX dSystemX).map s ''
        (((diagDynamicalSystem dSystemX dSystemX).map (t * s)) ⁻¹' U))
        ⊆ Z := by
        simp only [Z]
        unfold inverseSetOrbit
        apply closure_mono
        apply Set.iUnion_mono
        intro t z hz
        simp only [Set.mem_image, Set.mem_preimage, Prod.exists] at hz
        rcases hz with ⟨a, b, hab1, hab2⟩
        simp only [Set.mem_preimage]
        have hEqu : (diagDynamicalSystem dSystemX dSystemX).map (t * s) (a, b)
          = (diagDynamicalSystem dSystemX dSystemX).map t
            ((diagDynamicalSystem dSystemX dSystemX).map s (a, b)) := by
          exact (diagDynamicalSystem dSystemX dSystemX).mapMult t s (a, b)
        rw [hEqu] at hab1
        rw [hab2] at hab1
        exact hab1
      have hsWsubZ : (diagDynamicalSystem dSystemX dSystemX).map s '' closure W ⊆ Z := by
        rw [hMovesIn2] at hMovesIn
        exact hMovesIn.trans hMovesIn3
      exact hsZsubsW.trans hsWsubZ
    have hZInterDiag : (Set.diagonal X ∩ Z).Nonempty := by
      simp only [Z]
      apply (inRPMiffBackwardUOrbitClosHitsDiag dSystemX z).mp hzRP U hUOpen hUContz
    have hZClosed : IsClosed Z := by
      apply isClosed_closure
    let hExistz := Set.inter_nonempty.mp hZInterDiag
    rcases hExistz with ⟨z, hz1, hz2⟩
    let W := {(diagDynamicalSystem dSystemX dSystemX).map s z | s : S}
    have hWinZ : W ⊆ Z := by
      intro t ht
      simp only [Set.mem_setOf_eq, W] at ht
      rcases ht with ⟨s, hst⟩
      rw [<- hst]
      specialize hZInvariant s
      rw [<- Set.mapsTo_iff_image_subset] at hZInvariant
      specialize hZInvariant hz2
      exact hZInvariant
    have hClosureWinZ : closure W ⊆ Z := by
      apply closure_minimal
      · exact hWinZ
      · exact hZClosed
    have hWinDiag : W ⊆ Set.diagonal X := by
      simp only [W]
      intro t ht
      simp only [Set.mem_setOf_eq] at ht
      rcases ht with ⟨s, hs⟩
      rw [<- hs]
      simp only [Set.mem_diagonal_iff]
      simp only [diagDynamicalSystem, Prod.map_fst, Prod.map_snd]
      simp only [Set.mem_diagonal_iff] at hz1
      rw [hz1]
    have hEveryPoint : ∀ t ∈ Set.diagonal X, ∀ U ∈ nhds t, (U ∩ W).Nonempty := by
      intro t ht U hU
      have hUNeigh := mem_nhds_prod_iff.mp hU
      rcases hUNeigh with ⟨U1, hU1, U2, hU2, hU12⟩
      let V := U1 ∩ U2
      simp only [Set.mem_diagonal_iff] at ht
      simp only [Set.mem_diagonal_iff] at hz1
      rw [<- ht] at hU2
      have hUNeight : V ∈ nhds t.1 := by
        simp only [mem_nhds_iff]
        simp only [mem_nhds_iff] at hU1
        simp only [mem_nhds_iff] at hU2
        rcases hU1 with ⟨W1, hW1a, hW1b, hW1c⟩
        rcases hU2 with ⟨W2, hW2a, hW2b, hW2c⟩
        use W1 ∩ W2
        constructor
        · apply Set.inter_subset_inter hW1a hW2a
        constructor
        · apply IsOpen.inter hW1b hW2b
        · simp only [Set.mem_inter_iff]
          constructor
          · exact hW1c
          · exact hW2c
      have hExists : ∃ s : S, dSystemX.map s z.1 ∈ V := by
        let hVExpand := mem_nhds_iff.mp hUNeight
        rcases hVExpand with ⟨V1, hV1a, hV1b, hV1c⟩
        have hV1Nonempty: V1.Nonempty := by
          apply Set.nonempty_of_mem hV1c
        have hVisit := minimalImpliesNonemptySetVisits hMin z.1 hV1b hV1Nonempty
        unfold visitTimeSet at hVisit
        simp only [Set.nonempty_def, Set.mem_preimage] at hVisit
        rcases hVisit with ⟨s, hs⟩
        use s
        apply hV1a
        exact hs
      rcases hExists with ⟨s, hs⟩
      simp only [Set.inter_nonempty, Prod.exists]
      use dSystemX.map s z.1
      use dSystemX.map s z.1
      constructor
      · apply hU12
        simp only [Set.mem_prod]
        constructor
        · have hVU1 : V ⊆ U1 := by
            apply Set.inter_subset_left
          apply hVU1
          exact hs
        · have hVU2 : V ⊆ U2 := by
            apply Set.inter_subset_right
          apply hVU2
          exact hs
      · simp only [Set.mem_setOf_eq, W]
        use s
        simp only [diagDynamicalSystem]
        simp only [Prod.map, Prod.mk.injEq, true_and]
        rw [hz1]
    have hWClosureContDiag : Set.diagonal X ⊆ closure W := by
      intro t ht
      specialize hEveryPoint t ht
      apply mem_closure_iff_nhds.mpr
      exact hEveryPoint
    exact hWClosureContDiag.trans hClosureWinZ
  · sorry -- follows immediately from inRPMiffBackwardUOrbitClosHitsDiag
refine ⟨?_, ?_, ?_, ?_⟩
· exact RPMwithInvOrbit
/- The remaining three statements can be derived easily from forwardBackwardSetOrbClosCoincideInBronsSys,
forwardEqualsBackwardRPInMinCommSystem, and RPMwithInvOrbit -/
· sorry
· sorry
· sorry


/-- For `π : X → Y` a factor map of minimal systems with a commutative
acting semigroup, `RPM_Y ⊆ (π ⊗ π) RPM_X` and `RP_Y ⊆ (π ⊗ π) RP_X` -/
theorem commMinRPIsInImageOfRP
{S : Type*} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemX : DynamicalSystem S X) {hMin : isMinimalSystem dSystemX}
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemY : DynamicalSystem S Y)
(π : X → Y) {hπ : isFactorMap dSystemX dSystemY π} :
RPM dSystemY ⊆ (Prod.map π π) '' (RPM dSystemX)
∧
RP dSystemY ⊆ (Prod.map π π) '' (RP dSystemX) := by
have goalRPM : RPM dSystemY ⊆ (Prod.map π π) '' (RPM dSystemX) := by
  have hYMin : isMinimalSystem dSystemY := by
    have hYFactorX : isFactor dSystemY dSystemX := by
      unfold isFactor
      use π
    exact factorOfMinimalIsMinimal hMin hYFactorX
  unfold isFactorMap at hπ
  rcases hπ with ⟨hπCont, hπSurj, hπEquiv⟩
  have hComplement : ((Prod.map π π) '' (RPM dSystemX))ᶜ ⊆ (RPM dSystemY)ᶜ := by
    intro z hz
    let H := (Prod.map π π) ⁻¹' {z}
    have hHCompact : IsCompact H := by
      apply IsCompact.preimage_continuous
      · simp
      · apply Continuous.prodMap
        · exact hπCont
        · exact hπCont
    have hfH : ∀ f ∈ H, f ∉ RPM dSystemX := by
      intro f hf
      by_contra
      have hf1 : (Prod.map π π) f ∈ (Prod.map π π) '' RPM dSystemX := by
        simp only [Set.mem_image, Prod.exists, Prod.map_apply]
        use f.1
        use f.2
        constructor
        · exact this
        · rfl
      simp only [Set.mem_preimage, Set.mem_singleton_iff, H] at hf
      rw [<- hf] at hz
      exact hz hf1
    have hHS : ∀ f ∈ H, ∃ αf Vf : Set (X × X), Set.diagonal X ⊆ αf ∧ IsOpen αf
      ∧ f ∈ Vf ∧ IsOpen Vf ∧
      Disjoint (⋃ (s : S), (Prod.map (dSystemX.map s) (dSystemX.map s)) ⁻¹' Vf) αf := by
      intro f hfInH
      specialize hfH f hfInH
      unfold RPM at hfH
      have hExistDisj : ∃ αf Vf : Set (X × X), Set.diagonal X ⊆ αf ∧ IsOpen αf
        ∧ f ∈ Vf ∧ IsOpen Vf ∧
        Disjoint Vf (⋃ (s : S), ((Prod.map (dSystemX.map s) (dSystemX.map s)) '' αf)) := by
        have hExistOneα : ∃ αf : Set (X × X), αf ∈ nhdsSet (Set.diagonal X) ∧
          f ∉ setOrbitClosure (diagDynamicalSystem dSystemX dSystemX) αf := by
          by_contra hContra
          simp only [not_exists, not_and, not_not] at hContra
          have hfIn :  f ∈ ⋂ α ∈ nhdsSet (Set.diagonal X),
            setOrbitClosure (diagDynamicalSystem dSystemX dSystemX) α := by
            apply Set.mem_sInter.mpr
            simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff, Set.mem_iInter]
            intro a ha
            specialize hContra a ha
            exact hContra
          exact hfH hfIn
        rcases hExistOneα with ⟨αf1, hαf1a, hαf2a⟩
        have hαfExOpen := mem_nhdsSet.mp hαf1a
        rcases hαfExOpen with ⟨αf, hαf1, hαf2, hαf3⟩
        use αf
        by_contra hContra
        simp only [Mathlib.Tactic.Push.not_exists] at hContra
        simp only [Set.disjoint_iUnion_right, not_and, not_forall] at hContra
        have hfInOrbitClosure : f ∈ setOrbitClosure (diagDynamicalSystem dSystemX dSystemX) αf := by
          unfold setOrbitClosure
          simp only [mem_closure_iff]
          intro Vf hVf1 hVf2
          specialize hContra Vf hαf3 hαf2 hVf2 hVf1
          rcases hContra with ⟨s, hs⟩
          simp only [Set.not_disjoint_iff] at hs
          rcases hs with ⟨z, hz1, hz2⟩
          simp only [Set.inter_nonempty_iff_exists_right]
          use z
          constructor
          · simp only [setOrbit, Set.mem_range, Prod.exists, Subtype.exists, exists_prop]
            simp only [Set.mem_image, Prod.exists, Prod.map_apply] at hz2
            use s
            exact hz2
          · exact hz1
        have hαSubset : setOrbitClosure (diagDynamicalSystem dSystemX dSystemX) αf
          ⊆ setOrbitClosure (diagDynamicalSystem dSystemX dSystemX) αf1 := by
          unfold setOrbitClosure
          apply closure_mono
          unfold setOrbit
          simp only
          intro z hz
          simp only [Set.mem_range, Prod.exists, Subtype.exists, exists_prop] at hz
          rcases hz with ⟨s, a, b, hs1, hs2⟩
          simp only [Set.mem_range, Prod.exists, Subtype.exists, exists_prop]
          use s
          use a
          use b
          constructor
          · apply hαf1
            exact hs1
          · exact hs2
        have hfOrbit :  f ∈ setOrbitClosure (diagDynamicalSystem dSystemX dSystemX) αf1 := by
          exact hαSubset hfInOrbitClosure
        exact hαf2a hfOrbit
      rcases hExistDisj with ⟨αf, Vf, hDiag, hOpenα, hfInVf, hOpenVf, hDisjoint⟩
      use αf
      use Vf
      constructor
      · exact hDiag
      constructor
      · exact hOpenα
      constructor
      · exact hfInVf
      constructor
      · exact hOpenVf
      · by_contra hContra
        simp only [Set.disjoint_iUnion_left, not_forall] at hContra
        rcases hContra with ⟨s, hsContra⟩
        have hSomething : ∃ w : X × X, w ∈ (Prod.map (dSystemX.map s) (dSystemX.map s) ⁻¹' Vf)
          ∧ w ∈ αf := by
          apply Set.not_disjoint_iff.mp
          exact hsContra
        rcases hSomething with ⟨w, hw1, hw2⟩
        simp at hw1
        have hw2Next : Prod.map (dSystemX.map s) (dSystemX.map s) w ∈
          Prod.map (dSystemX.map s) (dSystemX.map s) '' αf := by
          apply Set.mem_image_of_mem
          exact hw2
        simp only [Set.disjoint_iUnion_right] at hDisjoint
        specialize hDisjoint s
        have hNotDisjoint : ¬ Disjoint Vf (Prod.map (dSystemX.map s) (dSystemX.map s) '' αf) := by
          apply Set.not_disjoint_iff.mpr
          use Prod.map (dSystemX.map s) (dSystemX.map s) w
        exact hNotDisjoint hDisjoint
    choose α V hαConta hαOpen hVConta hVOpen hαVDisj using hHS
    have hfCover : H ⊆ ⋃ f : X × X, ⋃ (h : f ∈ H), V f h := by
      intro t ht
      specialize hVConta t ht
      simp only [Set.mem_iUnion, Prod.exists]
      use t.1
      use t.2
      use ht
    have hHCompact : IsCompact H := by
      apply IsClosed.isCompact
      apply IsClosed.preimage
      · apply Continuous.prodMap
        · exact hπCont
        · exact hπCont
      · simp
    let NVee : H → Set (X × X) := fun f ↦ V f.1 f.2
    have hFiniteCover : ∃ F ⊆ H, F.Finite ∧
      H ⊆ ⋃ f : X × X, ⋃ (h1 : f ∈ H), ⋃ (_ : f ∈ F), V f h1 := by
      have hCoverNew : H ⊆ ⋃ f : H, NVee f := by
        simp only [Set.iUnion_coe_set]
        exact hfCover
      have hFiniteSubCase : ∃ G : Finset H, H ⊆ ⋃ f ∈ G, NVee f := by
        apply IsCompact.elim_finite_subcover
        · exact hHCompact
        · simp [NVee]
          simp [hVOpen]
        · exact hCoverNew
      rcases hFiniteSubCase with ⟨G, hG⟩
      let F : Set (X × X) := Subtype.val '' (G : Set H)
      use F
      constructor
      · simp [F]
      constructor
      · simp only [F]
        apply Set.Finite.image
        simp
      simp only [Set.iUnion_coe_set, NVee] at hG
      simp only [Set.mem_image, SetLike.mem_coe, Subtype.exists, exists_and_right, exists_eq_right,
        Set.iUnion_exists, F]
      intro h hhH
      simp only [Set.subset_def] at hG
      specialize hG h hhH
      simp only [Set.mem_iUnion, exists_prop, Prod.exists] at hG
      rcases hG with ⟨a1, a2, a3, a4, a5⟩
      simp only [Set.mem_iUnion, exists_prop, exists_and_right, exists_and_left, Prod.exists]
      use a1
      use a2
      use ⟨a3, a4⟩
      use a3
    rcases hFiniteCover with ⟨F, hFinH, hFfinite, hHSub⟩
    have hExistOpen : ∃ U : Set (Y × Y), IsOpen U ∧ z ∈ U ∧
      (Prod.map π π) ⁻¹' U ⊆ ⋃ f : X × X, ⋃ (h1 : f ∈ H), ⋃ (h2 : f ∈ F), V f h1 := by
      apply existOpenNeighborhoodPreImageContainedIn
      · apply Continuous.prodMap
        · exact hπCont
        · exact hπCont
      · apply isOpen_sUnion
        intro t ht
        simp only [Set.mem_range, Prod.exists] at ht
        rcases ht with ⟨a, b, hab⟩
        rw [<- hab]
        apply isOpen_sUnion
        intro t1 ht1
        simp only [Set.mem_range] at ht1
        rcases ht1 with ⟨a1, ha1⟩
        rw [<- ha1]
        apply isOpen_sUnion
        intro t2 ht2
        simp only [Set.mem_range, exists_prop] at ht2
        rcases ht2 with ⟨a2, ha2⟩
        rw [<- ha2]
        specialize hVOpen (a, b) a1
        exact hVOpen
      · have hHDef : H = (Prod.map π π) ⁻¹' {z} := by
          rfl
        rw [<- hHDef]
        exact hHSub
    rcases hExistOpen with ⟨U, hU1, hU2, hU3⟩
    let β := ⋂ f : X × X, ⋂ (hfH : f ∈ H), ⋂ (hfF : f ∈ F), α f hfH
    let Nα : F → Set (X × X) := fun f ↦ α f.1 (hFinH f.2)
    have hβRedefined : β = ⋂ (f : X × X ) (hfF : f ∈ F), α f (hFinH hfF) := by
      ext z
      constructor
      · intro hz
        simp only [Set.mem_iInter, Prod.forall, β] at hz
        simp only [Set.mem_iInter, Prod.forall]
        intro a b hab
        specialize hz a b (hFinH hab) hab
        exact hz
      · intro hz
        simp only [Set.mem_iInter, Prod.forall] at hz
        simp only [Set.mem_iInter, Prod.forall, β]
        intro a b habH habF
        specialize hz a b habF
        exact hz
    have hβRedefined2 : β = ⋂ f : F, Nα f := by
      rw [hβRedefined]
      ext z
      constructor
      · intro hz
        simp only [Set.iInter_coe_set, Set.mem_iInter, Prod.forall]
        simp only [Set.mem_iInter, Prod.forall] at hz
        intro a b hab
        specialize hz a b hab
        exact hz
      · intro hz
        simp only [Set.iInter_coe_set, Set.mem_iInter, Prod.forall] at hz
        simp only [Set.mem_iInter, Prod.forall]
        intro a b hab
        specialize hz a b hab
        exact hz
    have hβOpen : IsOpen β := by
      rw [hβRedefined2]
      apply Set.Finite.isOpen_sInter
      · have hFFinite : Finite F := by
          apply Set.Finite.to_subtype
          exact hFfinite
        apply Set.finite_range
      · intro t ht
        simp only [Set.mem_range, Subtype.exists, Prod.exists] at ht
        rcases ht with ⟨a, b, hab1, hab2⟩
        rw [<- hab2]
        simp only [Nα]
        specialize hαOpen (a, b) (hFinH hab1)
        exact hαOpen
    have hβContaDiag : Set.diagonal X ⊆ β := by
      apply Set.subset_sInter
      intro t1 ht1
      simp only [Set.mem_range, Prod.exists] at ht1
      rcases ht1 with ⟨a1, b1, hab1⟩
      rw [<- hab1]
      apply Set.subset_sInter
      intro t2 ht2
      simp only [Set.mem_range] at ht2
      rcases ht2 with ⟨a2, ha2⟩
      rw [<- ha2]
      apply Set.subset_sInter
      intro t3 ht3
      simp only [Set.mem_range, exists_prop] at ht3
      rcases ht3 with ⟨a3, ha3⟩
      rw [<- ha3]
      specialize hαConta (a1, b1)
      have ha1b1H : (a1, b1) ∈ H := by
        apply hFinH
        exact a3
      specialize hαConta ha1b1H
      exact hαConta
    have hDisjointβ0 : ∀ (f : X × X) (hfH : f ∈ H) (hfF : f ∈ F), Disjoint
      (⋃ (s : S), Prod.map (dSystemX.map s) (dSystemX.map s) ⁻¹' V f hfH) β := by
      intro f hfH hfF
      have hβSub : β ⊆ α f hfH := by
        intro z hz
        simp only [Set.mem_iInter, Prod.forall, β] at hz
        specialize hz f.1 f.2 hfH hfF
        exact hz
      apply Set.disjoint_of_subset_right hβSub
      specialize hαVDisj f hfH
      exact hαVDisj
    have hDisjoinβ : Disjoint (⋃ f : X × X, ⋃ (hfH : f ∈ H), ⋃ (hfF : f ∈ F), ⋃ (s : S),
      Prod.map (dSystemX.map s) (dSystemX.map s) ⁻¹' V f hfH) β := by
      apply Set.disjoint_sUnion_left.mpr
      intro t1 ht1
      simp only [Set.mem_range, Prod.exists] at ht1
      rcases ht1 with ⟨a, b, hab⟩
      rw [<- hab]
      apply Set.disjoint_sUnion_left.mpr
      intro t2 ht2
      simp only [Set.mem_range] at ht2
      rcases ht2 with ⟨ha2, hb2⟩
      rw [<- hb2]
      apply Set.disjoint_sUnion_left.mpr
      intro t3 ht3
      simp only [Set.mem_range, exists_prop] at ht3
      rcases ht3 with ⟨ha3, hb3⟩
      rw [<- hb3]
      specialize hDisjointβ0 (a, b) ha2 ha3
      exact hDisjointβ0
    have hβSubset : ((Prod.map π π) ⁻¹' ⋃ (s : S),
      (Prod.map (dSystemY.map s) (dSystemY.map s)) ⁻¹' U) ⊆
      (⋃ f : X × X, ⋃ (hfH : f ∈ H), ⋃ (hfF : f ∈ F), ⋃ (s : S),
      Prod.map (dSystemX.map s) (dSystemX.map s) ⁻¹' V f hfH) := by
      have hβSubset1 : ⋃ (s : S), (Prod.map (dSystemX.map s) (dSystemX.map s)) ⁻¹'
        (⋃ f : X × X, ⋃ (hfH : f ∈ H), ⋃ (hfF : f ∈ F), V f hfH) ⊆
        (⋃ f : X × X, ⋃ (hfH : f ∈ H), ⋃ (hfF : f ∈ F), ⋃ (s : S),
        Prod.map (dSystemX.map s) (dSystemX.map s) ⁻¹' V f hfH) := by
        intro z hz
        simp only [Set.preimage_iUnion, Set.mem_iUnion, Set.mem_preimage, exists_prop,
          exists_and_left, Prod.exists] at hz
        rcases hz with ⟨s, x, y, hxy1, t, ht⟩
        simp only [Set.mem_iUnion, Set.mem_preimage, exists_prop, exists_and_left, Prod.exists]
        use x
        use y
        constructor
        · exact hxy1
        · use t
          use s
      have hβSubset2 : ⋃ s : S, Prod.map (dSystemX.map s) (dSystemX.map s) ⁻¹'
        ((Prod.map π π) ⁻¹' U) ⊆
        ⋃ (s : S), Prod.map (dSystemX.map s) (dSystemX.map s) ⁻¹'
        (⋃ f : X × X, ⋃ (hfH : f ∈ H), ⋃ (hfF : f ∈ F), V f hfH) := by
        apply Set.sUnion_subset
        intro w hw
        simp only [Set.mem_range] at hw
        rcases hw with ⟨s, hs⟩
        rw [<- hs]
        have hβSubsub : Prod.map (dSystemX.map s) (dSystemX.map s) ⁻¹' ((Prod.map π π) ⁻¹' U) ⊆
          Prod.map (dSystemX.map s) (dSystemX.map s) ⁻¹'
          (⋃ f, ⋃ (hfH : f ∈ H), ⋃ (_ : f ∈ F), V f hfH) := by
          apply Set.preimage_mono
          exact hU3
        have hβSubsub2 : Prod.map (dSystemX.map s) (dSystemX.map s) ⁻¹'
          (⋃ f, ⋃ (hfH : f ∈ H), ⋃ (_ : f ∈ F), V f hfH) ⊆
          ⋃ (s : S), Prod.map (dSystemX.map s) (dSystemX.map s) ⁻¹'
          (⋃ f : X × X, ⋃ (hfH : f ∈ H), ⋃ (hfF : f ∈ F), V f hfH) := by
          apply Set.subset_sUnion_of_mem
          simp
        exact hβSubsub.trans hβSubsub2
      have hβSubset3 : ⋃ s : S, (Prod.map π π) ⁻¹'
        (Prod.map (dSystemY.map s) (dSystemY.map s) ⁻¹'U) ⊆
        ⋃ s : S, Prod.map (dSystemX.map s) (dSystemX.map s) ⁻¹'
        ((Prod.map π π) ⁻¹' U) := by
        apply Set.sUnion_subset
        intro t ht
        simp only [Set.mem_range] at ht
        rcases ht with ⟨s, hs⟩
        rw [<- hs]
        have hβSub0 : Prod.map π π ⁻¹' (Prod.map (dSystemY.map s) (dSystemY.map s) ⁻¹' U)
          ⊆ Prod.map (dSystemX.map s) (dSystemX.map s) ⁻¹' (Prod.map π π ⁻¹' U) := by
          intro z hz
          simp only [Set.mem_preimage]
          simp only [Set.mem_preimage] at hz
          simp only [Prod.map]
          simp only [Prod.map] at hz
          have hEq1 : π (dSystemX.map s z.1) = dSystemY.map s (π z.1) := by
            unfold isEquivariant at hπEquiv
            specialize hπEquiv s
            have hEq1a : (dSystemY.map s ∘ π) (z.1) = (π ∘ dSystemX.map s) (z.1) := by
              apply congr_fun
              exact hπEquiv
            have hEq1b : π (dSystemX.map s z.1) = (π ∘ dSystemX.map s) (z.1) := by
              simp
            have hEq1c : dSystemY.map s (π z.1) = (dSystemY.map s ∘ π) (z.1) := by
              simp
            rw [hEq1b, hEq1c, hEq1a]
          have hEq2 : π (dSystemX.map s z.2) = dSystemY.map s (π z.2) := by
            unfold isEquivariant at hπEquiv
            specialize hπEquiv s
            have hEq2a : (dSystemY.map s ∘ π) (z.2) = (π ∘ dSystemX.map s) (z.2) := by
              apply congr_fun
              exact hπEquiv
            have hEq2b : π (dSystemX.map s z.2) = (π ∘ dSystemX.map s) (z.2) := by
              simp
            have hEq2c : dSystemY.map s (π z.2) = (dSystemY.map s ∘ π) (z.2) := by
              simp
            rw [hEq2b, hEq2c, hEq2a]
          rw [hEq1, hEq2]
          exact hz
        have hβSub1 : Prod.map (dSystemX.map s) (dSystemX.map s) ⁻¹' (Prod.map π π ⁻¹' U)
          ⊆  ⋃ s, Prod.map (dSystemX.map s) (dSystemX.map s) ⁻¹' (Prod.map π π ⁻¹' U) := by
          apply Set.subset_sUnion_of_mem
          simp
        exact hβSub0.trans hβSub1
      have hβSubset4 : Prod.map π π ⁻¹' ⋃ s, Prod.map (dSystemY.map s) (dSystemY.map s) ⁻¹' U
        ⊆ ⋃ s : S, (Prod.map π π) ⁻¹' (Prod.map (dSystemY.map s) (dSystemY.map s) ⁻¹'U) := by
        intro z hz
        simp only [Set.preimage_iUnion, Set.mem_iUnion, Set.mem_preimage] at hz
        rcases hz with ⟨s, hs⟩
        simp only [Set.mem_iUnion, Set.mem_preimage]
        use s
      exact ((hβSubset4.trans hβSubset3).trans hβSubset2).trans hβSubset1
    have hDisjointβ10 : Disjoint ((Prod.map π π) ⁻¹' ⋃ (s : S),
      (Prod.map (dSystemY.map s) (dSystemY.map s)) ⁻¹' U) β := by
      apply Set.disjoint_of_subset_left hβSubset
      exact hDisjoinβ
    have hDisjointβ11 : Disjoint (⋃ (s : S), (Prod.map (dSystemY.map s) (dSystemY.map s)) ⁻¹' U)
      ((Prod.map π π) '' β) := by
      by_contra hContra
      have hExistInBoth : ∃ z, z ∈ (⋃ (s : S), (Prod.map (dSystemY.map s) (dSystemY.map s)) ⁻¹' U)
        ∧ z ∈ (Prod.map π π) '' β := by
        apply Set.not_disjoint_iff.mp hContra
      rcases hExistInBoth with ⟨z, hz1, hz2⟩
      simp only [Set.mem_image, Prod.exists, Prod.map_apply] at hz2
      rcases hz2 with ⟨a, b, hab1, hab2⟩
      have hab3 : (a, b) ∈ (Prod.map π π) ⁻¹' ((⋃ (s : S),
        (Prod.map (dSystemY.map s) (dSystemY.map s)) ⁻¹' U)) := by
        simp only [Set.mem_preimage]
        have hab4 : Prod.map π π (a, b) = z := by
          rw [<- hab2]
          simp
        rw [hab4]
        exact hz1
      have hNotDisjoint : ¬ Disjoint (Prod.map π π ⁻¹' ⋃ s,
        Prod.map (dSystemY.map s) (dSystemY.map s) ⁻¹' U) β := by
        apply Set.not_disjoint_iff.mpr
        use (a, b)
      exact hNotDisjoint hDisjointβ10
    have hExistZ : ∃ (Z : Set Y), Z.Nonempty ∧ IsOpen Z ∧ ((Z ×ˢ Z) ⊆ ((Prod.map π π) '' β)) := by
      apply openProductInEntourageImage
      · exact hπCont
      · exact hπSurj
      · apply mem_nhdsSet.mpr
        use β
    rcases hExistZ with ⟨Z, hZNonempty, hZOpen, hZConta⟩
    have hDisjointZ : Disjoint ((⋃ s, Prod.map
      (dSystemY.map s) (dSystemY.map s) ⁻¹' U)) (Z ×ˢ Z) := by
      apply Set.disjoint_of_subset_right
      · exact hZConta
      · exact hDisjointβ11
    by_contra hContra
    have hzInRP : z ∈ RPM dSystemY := by
      simp only [Set.mem_compl_iff, not_not] at hContra
      exact hContra
    have hContainDiag : Set.diagonal Y ⊆ closure
      (inverseSetOrbit (diagDynamicalSystem dSystemY dSystemY) U) := by
      apply (inMinCommxyInRPIffNhdOrbitClosContainsDiag dSystemY z (hMin := hYMin)).1.mp
      · exact hzInRP
      · exact hU1
      · exact hU2
    have hDisjointInverse : Disjoint
      (inverseSetOrbit (diagDynamicalSystem dSystemY dSystemY) U) (Z ×ˢ Z) := by
      unfold inverseSetOrbit
      exact hDisjointZ
    have hZZOpen : IsOpen (Z ×ˢ Z) := by
      apply IsOpen.prod
      · exact hZOpen
      · exact hZOpen
    have hZCompClosed : IsClosed (Z ×ˢ Z)ᶜ := by
      apply IsOpen.isClosed_compl hZZOpen
    have hInverseSubset : inverseSetOrbit (diagDynamicalSystem dSystemY dSystemY) U ⊆ (Z ×ˢ Z)ᶜ
      := by
      apply Disjoint.subset_compl_right hDisjointInverse
    have hInverseClosureSubset : closure
      (inverseSetOrbit (diagDynamicalSystem dSystemY dSystemY) U) ⊆ (Z ×ˢ Z)ᶜ := by
      apply closure_minimal hInverseSubset hZCompClosed
    have hDiagContainedCompl : Set.diagonal Y ⊆ (Z ×ˢ Z)ᶜ := by
      exact hContainDiag.trans hInverseClosureSubset
    have hDiagDisjointZ : Disjoint (Set.diagonal Y) (Z ×ˢ Z) := by
      apply Set.subset_compl_iff_disjoint_right.mp hDiagContainedCompl
    have hZContainz := Set.nonempty_def.mp hZNonempty
    rcases hZContainz with ⟨z, hz⟩
    have hNotDisjoint : ¬ Disjoint (Set.diagonal Y) (Z ×ˢ Z) := by
      apply Set.not_disjoint_iff.mpr
      use (z, z)
      constructor
      · unfold Set.diagonal
        simp
      · simp only [Set.mem_prod, and_self]
        exact hz
    exact hNotDisjoint hDiagDisjointZ
  exact Set.compl_subset_compl.mp hComplement
refine ⟨?_, ?_⟩
· exact goalRPM
/- The remaining statement can be derived easily from
forwardEqualsBackwardRPInMinCommSystem and goalRPM -/
· sorry

end Regional_proximality_in_min_comm_systems

section Equicontinuity_and_regional_proximality

variable {S} [Semigroup S] [Nonempty S]
variable {X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]

instance : UniformSpace X := uniformSpaceOfCompactR1

/-- A dynamical system `dSystem` is equicontinuous if the family of maps
given by `dSystem.map` is uniformly equicontinuous -/
def isEquicontinuousSystem
(dSystem : DynamicalSystem S X) :
Prop :=
UniformEquicontinuous dSystem.map

-- We create the next definitions because Lean has trouble understanding
-- that the uniformity structure
-- from product space coming from uniformSpaceOfCompactR1 is the same
-- as the one coming from instUniformSpaceProd
def isEquicontinuousProductSystem
(dSystemX : DynamicalSystem S X)
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemY : DynamicalSystem S Y) :
Prop :=
UniformEquicontinuous (diagDynamicalSystem dSystemX dSystemY).map

def isEquicontinuousSubSystem
(dSystem : DynamicalSystem S X)
{Z : Set X} [CompactSpace Z] [Nonempty Z]
(hZ : isNonemptyCompactT2InvariantSubset dSystem Z) :
Prop :=
UniformEquicontinuous (fromNonemptyCompactT2InvariantSubsetToSystem dSystem hZ).map

/-- If `dSystem` and `dSystemY` are equicontinuous dynamical systems, then the
diagonal action of `S` on `X × Y` is an equicontinuous dynamical system -/
theorem diagSystemOfEquiSystemsIsEquiSystem
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
{dSystemX : DynamicalSystem S X} (hXEqui : isEquicontinuousSystem dSystemX)
{dSystemY : DynamicalSystem S Y} (hYEqui : isEquicontinuousSystem dSystemY) :
isEquicontinuousProductSystem dSystemX dSystemY := by
intro β hβ
simp only [Filter.Eventually]
have h1 : ∃ βX ∈ uniformity X, ∃ βY ∈ uniformity Y, entourageProd βX βY ⊆ β := by
  apply entourageProd_subset
  exact hβ
rcases h1 with ⟨βX, hβX, βY, hβY, hβXY⟩
specialize hXEqui βX hβX
simp only [Filter.Eventually] at hXEqui
specialize hYEqui βY hβY
simp only [Filter.Eventually] at hYEqui
let αX := {x : X × X | ∀ (i : S), (dSystemX.map i x.1, dSystemX.map i x.2) ∈ βX}
let αY := {y : Y × Y | ∀ (i : S), (dSystemY.map i y.1, dSystemY.map i y.2) ∈ βY}
let αXY :=  {z : (X × Y) × (X × Y) | ∀ (i : S), ((diagDynamicalSystem dSystemX dSystemY).map i z.1,
  (diagDynamicalSystem dSystemX dSystemY).map i z.2) ∈ β}
have αXYDef : αXY =  {z : (X × Y) × (X × Y) | ∀ (i : S),
  ((diagDynamicalSystem dSystemX dSystemY).map i z.1,
  (diagDynamicalSystem dSystemX dSystemY).map i z.2) ∈ β} := by
    rfl
have hαX : αX ∈ uniformity X := by
  simpa
have hαY : αY ∈ uniformity Y := by
  simpa
have hαXY : entourageProd αX αY ⊆ αXY := by
  intro z hz s
  rcases hz with ⟨p1, p2⟩
  have hα3 : ((diagDynamicalSystem dSystemX dSystemY).map s z.1,
    (diagDynamicalSystem dSystemX dSystemY).map s z.2) ∈ entourageProd βX βY := by
    simp only [mem_entourageProd]
    constructor
    · have hα4 : ((diagDynamicalSystem dSystemX dSystemY).map s z.1).1 = dSystemX.map s z.1.1 := by
        rfl
      have hα5 : ((diagDynamicalSystem dSystemX dSystemY).map s z.2).1 = dSystemX.map s z.2.1 :=
        rfl
      simp only [hα4, hα5]
      specialize p1 s
      exact p1
    have hα6 : ((diagDynamicalSystem dSystemX dSystemY).map s z.1).2 = dSystemY.map s z.1.2 := by
      rfl
    have hα7 : ((diagDynamicalSystem dSystemX dSystemY).map s z.2).2 = dSystemY.map s z.2.2 := by
      rfl
    simp only [hα6, hα7]
    specialize p2 s
    exact p2
  apply hβXY
  exact hα3
rw [<- αXYDef]
have hαXY2 : entourageProd αX αY ∈ uniformity (X × Y) := by
  apply entourageProd_mem_uniformity
  · exact hαX
  exact hαY
exact Filter.mem_of_superset hαXY2 hαXY

/-- If `dSystem` is an equicontinuous dynamical system and `Z ⊆ X` is a
nonempty, closed, `S`-invariant set, then `Z` is an equicontinuous
dynamical system -/
theorem subsystemOfEquicontinuousIsEquicontinuous
{dSystem : DynamicalSystem S X} (hXEqui : isEquicontinuousSystem dSystem)
{Z : Set X} [CompactSpace Z] [Nonempty Z]
(hZ : isNonemptyCompactT2InvariantSubset dSystem Z) :
isEquicontinuousSubSystem dSystem hZ :=
letI : UniformSpace X := uniformSpaceOfCompactR1
by
unfold isEquicontinuousSystem at hXEqui
have h1 : UniformEquicontinuousOn dSystem.map Z := by
  apply UniformEquicontinuous.uniformEquicontinuousOn
  exact hXEqui
intro α hα
unfold UniformEquicontinuous at hXEqui
unfold UniformEquicontinuousOn at h1
have h2init : uniformity (Z) = Filter.comap (fun (q : Subtype Z × Subtype Z)
  => (Subtype.val q.1, Subtype.val q.2)) (uniformity X) := by
  exact uniformity_subtype
have h2 : ∃ β ∈ uniformity X, (Prod.map Subtype.val Subtype.val) ⁻¹' β ⊆ α:= by
  simp only [h2init, Filter.mem_comap] at hα
  rcases hα with ⟨γ, hγ1, hγ2⟩
  use γ
  constructor
  · exact hγ1
  exact hγ2
rcases h2 with ⟨β, hβ1, hβ2⟩
specialize hXEqui β hβ1
let γ := {z : X × X | ∀ s : S, (dSystem.map s z.1, dSystem.map s z.2) ∈ β}
have h3 : γ ∈ uniformity X := by
  simp only [γ]
  exact hXEqui
let ZdSys := fromNonemptyCompactT2InvariantSubsetToSystem dSystem hZ
let δ := {z : (Z × Z) | ∀ s : S, (ZdSys.map s z.1, ZdSys.map s z.2) ∈ α}
have h4 : (Prod.map Subtype.val Subtype.val) ⁻¹' γ  ∈ uniformity Z := by
  simp only [uniformity_subtype]
  use γ
  constructor
  · exact h3
  rfl
have h5 : (Prod.map Subtype.val Subtype.val) ⁻¹' γ ⊆ δ:= by
  simp only [δ]
  simp only [γ]
  intro z hz
  simp only [Set.mem_setOf_eq]
  simp only [Set.preimage_setOf_eq, Prod.map_fst, Prod.map_snd, Set.mem_setOf_eq] at hz
  intro s
  specialize hz s
  let θ : Set (↑Z × ↑Z) := (Prod.map Subtype.val Subtype.val) ⁻¹' β
  have h51 : (ZdSys.map s z.1, ZdSys.map s z.2) ∈ θ := by
    simpa
  have h52 : θ ⊆ α := by
    simpa
  apply h52
  exact h51
have h6 : (Prod.map Subtype.val Subtype.val) ⁻¹' γ ∈ uniformity Z := by
  exact h4
have hGoal : δ ∈ uniformity Z := by
  exact Filter.mem_of_superset h6 h5
exact hGoal


/- This instance makes lean recognize a compact, Hausdorff space as a uniform space -/
-- This seems unnecessary.  Typeclass is finding it properly.
/- def quotientIsUniformSpace
(dSystem : DynamicalSystem S X)
{I : Set (X × X)} (hI : isICER dSystem I) :
UniformSpace (Quotient ⟨setToRelation I, hI.2.2⟩) :=
by sorry -/

/-- An ICER `I` on `X` is equicontinuous if
the quotient system `X/I` is equicontinuous -/
def isEquicontinuousICER
(dSystem : DynamicalSystem S X) [UniformSpace X]
{I : Set (X × X)} (hI : isICER dSystem I) :
Prop :=
by
  have : Nonempty (Quotient ⟨setToRelation I, hI.2.2⟩) :=
  nonemptyQuotient X hI.2.2
  have : T2Space (Quotient ⟨setToRelation I, hI.2.2⟩) :=
  quotientOfCompactT2ByClosedIsT2 hI.2.1 hI.2.2
  exact isEquicontinuousSystem (quotientDynamicalSystem dSystem hI)

/-- A dynamical system on `X` which acts by surjections is equicontinuous if and only
if the regionally proximal relation is contained in the diagonal of `X × X` -/
theorem equicontinuousIffRPTrivialIfSurjective
(dSystem : DynamicalSystem S X)
(hSurject : isSurjectiveSystem dSystem) :
RP dSystem ⊆ Set.diagonal X ↔ isEquicontinuousSystem dSystem := by sorry

/-- A dynamical system on `X` is equicontinuous if and only if the
backward regionally proximal relation is contained in the diagonal of `X × X` -/
theorem equicontinuousIffRPMTrivial
(dSystem : DynamicalSystem S X) :
RPM dSystem ⊆ Set.diagonal X ↔ isEquicontinuousSystem dSystem := by
constructor
· intro h1
  unfold isEquicontinuousSystem
  unfold UniformEquicontinuous
  simp only [Filter.Eventually]
  intro α hαUniformity
  have hαNhdsDiag : α ∈ nhdsSet (Set.diagonal X) := by
    simp only [nhdsSet_diagonal_eq_uniformity]
    exact hαUniformity
  have hαContDiag : Set.diagonal X ⊆ α := by
    have hα1 := mem_nhdsSet.mp hαNhdsDiag
    rcases hα1 with ⟨U, hU1, hU2, hU3⟩
    exact hU3.trans hU1
  have hRPα : RPM dSystem ⊆ α := by
    exact h1.trans hαContDiag
  unfold RPM at hRPα
  have hα0 : ∃ α0 ⊆ α, IsOpen α0 ∧ Set.diagonal X ⊆ α0 := by
    apply mem_nhdsSet.mp hαNhdsDiag
  rcases hα0 with ⟨α0, hα01, hα02, hα03⟩
  have hRPα0 : RPM dSystem ⊆ α0 := by
    exact h1.trans hα03
  have hGoalPrep0 : ∃ F : Finset (Set (X × X)), (∀ β ∈ F, β ∈ uniformity X) ∧
    Disjoint (⋂ β ∈ F, setOrbitClosure (diagDynamicalSystem dSystem dSystem) β) α0ᶜ := by
    unfold RPM at hRPα0
    have h1 : ∃ F : Finset {β : Set (X × X) | β ∈ nhdsSet (Set.diagonal X)},
      α0ᶜ ∩ (⋂ β ∈ F, setOrbitClosure (diagDynamicalSystem dSystem dSystem) β) = ∅ := by
      apply IsCompact.elim_finite_subfamily_closed
      · apply IsClosed.isCompact
        apply IsOpen.isClosed_compl
        exact hα02
      · intro i
        unfold setOrbitClosure
        apply isClosed_closure
      · have hDisjoint :  Disjoint α0ᶜ (⋂ β ∈ nhdsSet (Set.diagonal X),
          setOrbitClosure (diagDynamicalSystem dSystem dSystem) β) := by
          apply Set.subset_compl_iff_disjoint_left.mp
          simp only [compl_compl]
          exact hRPα0
        apply Disjoint.inter_eq
        intro x hx1 hx2
        specialize hDisjoint hx1
        have hxthis: x ≤ ⋂ β ∈ nhdsSet (Set.diagonal X), setOrbitClosure
          (diagDynamicalSystem dSystem dSystem) β := by
          simp only [Set.le_eq_subset, Set.subset_iInter_iff]
          simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.le_eq_subset, Set.subset_iInter_iff,
            Subtype.forall] at hx2
          exact hx2
        apply hDisjoint hxthis
    rcases h1 with ⟨G, hG⟩
    let F : Finset (Set (X × X)) := G.map ⟨Subtype.val, Subtype.val_injective⟩
    use F
    constructor
    · intro β hβ
      have hβN : β ∈ nhdsSet (Set.diagonal X) := by
        rw [Finset.mem_map] at hβ
        simp only [Set.mem_setOf_eq, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right,
          exists_eq_right] at hβ
        rcases hβ with ⟨hx1, hx2⟩
        exact hx1
      simp only [nhdsSet_diagonal_eq_uniformity] at hβN
      exact hβN
    · simp only [Set.disjoint_left, Set.mem_iInter, Set.mem_compl_iff, not_not, Prod.forall]
      intro a b hi
      have hGnew : Disjoint (⋂ β ∈ G, setOrbitClosure
        (diagDynamicalSystem dSystem dSystem) β) α0ᶜ := by
        apply Set.disjoint_iff_inter_eq_empty.mpr
        have hGNew2 : (⋂ β ∈ G, setOrbitClosure
          (diagDynamicalSystem dSystem dSystem) ↑β) ∩ α0ᶜ = ∅ := by
          rw [Set.inter_comm]
          exact hG
        exact hGNew2
      simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.disjoint_left, Set.mem_iInter, Subtype.forall,
        Set.mem_compl_iff, not_not, Prod.forall] at hGnew
      specialize hGnew a b
      apply hGnew
      intro a1 ha1 ha2
      specialize hi a1
      apply hi
      simp only [Set.coe_setOf, Set.mem_setOf_eq, Finset.mem_map, Function.Embedding.coeFn_mk,
        Subtype.exists, exists_and_right, exists_eq_right, F]
      use ha1
  have hGoalPrep : ∃ F : Finset (Set (X × X)), (∀ β ∈ F, β ∈ uniformity X) ∧
    (⋂ β ∈ F, setOrbitClosure (diagDynamicalSystem dSystem dSystem) β ⊆ α0) := by
    rcases hGoalPrep0 with ⟨F, hF1, hF2⟩
    use F
    constructor
    · exact hF1
    · apply Set.disjoint_compl_right_iff_subset.mp
      exact hF2
  have hGoal : ∃ F : Finset (Set (X × X)), (∀ β ∈ F, β ∈ uniformity X) ∧
    (⋂ β ∈ F, setOrbitClosure (diagDynamicalSystem dSystem dSystem) β ⊆ α):= by
    rcases hGoalPrep with ⟨F, hF1, hF2⟩
    use F
    constructor
    · exact hF1
    · exact hF2.trans hα01
  rcases hGoal with ⟨F, hF1, hF2⟩
  let γ := ⋂ β ∈ F, β
  have hGoal2 : setOrbitClosure (diagDynamicalSystem dSystem dSystem) γ ⊆
    (⋂ β ∈ F, setOrbitClosure (diagDynamicalSystem dSystem dSystem) β) := by
    unfold γ
    simp only [Set.subset_iInter_iff]
    intro ρ hρ
    apply monotoneSetOrbitClosure
    intro z hz
    simp only [Set.mem_iInter] at hz
    specialize hz ρ
    apply hz hρ
  have hGoal3 : setOrbitClosure (diagDynamicalSystem dSystem dSystem) γ ⊆ α := by
    exact hGoal2.trans hF2
  have hGoal4 : γ ∈ uniformity X := by
    unfold γ
    simp only [Filter.biInter_finset_mem]
    exact hF1
  let θ := {z : X × X | ∀ (s : S), (dSystem.map s z.1, dSystem.map s z.2) ∈ α}
  have hθDef : θ = {z : X × X | ∀ (s : S), (dSystem.map s z.1, dSystem.map s z.2) ∈ α} := by
    rfl
  rw [<- hθDef]
  have hγθ : γ ⊆ θ := by
    unfold θ
    intro z hz
    simp only [Set.mem_setOf_eq]
    intro s
    have h1 : setOrbit (diagDynamicalSystem dSystem dSystem) γ ⊆
      setOrbitClosure (diagDynamicalSystem dSystem dSystem) γ := by
      unfold setOrbitClosure
      apply subset_closure
    have hGoal3Cor : setOrbit (diagDynamicalSystem dSystem dSystem) γ ⊆ α := by
      exact h1.trans hGoal3
    unfold setOrbit at hGoal3Cor
    simp only at hGoal3Cor
    unfold Set.range at hGoal3Cor
    simp only [Prod.exists, Subtype.exists, exists_prop] at hGoal3Cor
    have h2 : (dSystem.map s z.1, dSystem.map s z.2) ∈
      {x | ∃ a a_1 b, (a_1, b) ∈ γ ∧ (diagDynamicalSystem dSystem dSystem).map a (a_1, b) = x} := by
      simp only [Set.mem_setOf_eq]
      use s
      use z.1
      use z.2
      constructor
      · exact hz
      · rfl
    apply hGoal3Cor
    exact h2
  exact Filter.mem_of_superset hGoal4 hγθ
· intro h1 t ht1
  by_contra ht2
  have h2prep : ∃ β ∈ nhdsSet (Set.diagonal X), t ∉ closure β := by
    have h2prep2 : SeparatedNhds {t} (Set.diagonal X) := by
      apply normal_separation
      · simp
      · apply t2_iff_isClosed_diagonal.mp
        simpa
      · simp [ht2]
    rcases h2prep2 with ⟨U, V, hU1, hV1, hU2, hV2, hUV⟩
    let β := Uᶜ
    use β
    constructor
    · apply mem_nhdsSet.mpr
      use V
      constructor
      · unfold β
        apply Disjoint.subset_compl_right
        exact disjoint_comm.mp hUV
      constructor
      · exact hV1
      · exact hV2
    have hβClosed : IsClosed β := by
      unfold β
      simpa
    have hβClosure : closure β = β := by
      apply IsClosed.closure_eq
      exact hβClosed
    rw [hβClosure]
    unfold β
    simp only [Set.mem_compl_iff, not_not]
    apply hU2
    simp
  have h2 : ∃ β ∈ uniformity X, t ∉ closure β := by
    rcases h2prep with ⟨β, hβ1, hβ2⟩
    use β
    constructor
    · simp only [nhdsSet_diagonal_eq_uniformity] at hβ1
      exact hβ1
    · exact hβ2
  rcases h2 with ⟨β, hβ1, hβ2⟩
  let α := {z : X × X | ∀ s : S, (dSystem.map s z.1, dSystem.map s z.2) ∈ β}
  have hα1 : α ∈ uniformity X := by
    unfold isEquicontinuousSystem at h1
    unfold UniformEquicontinuous at h1
    specialize h1 β hβ1
    exact h1
  letI hXUniform : UniformSpace X := by
      apply uniformSpaceOfCompactR1
  have hα2 : α ∈ nhdsSet (Set.diagonal X) := by
    simp only [nhdsSet_diagonal_eq_uniformity]
    exact hα1
  have hα3 : setOrbit (diagDynamicalSystem dSystem dSystem) α ⊆ β := by
    unfold setOrbit
    simp only
    simp only [Set.coe_setOf, Set.mem_setOf_eq, α]
    intro w hw
    simp only [Set.mem_range, Prod.exists, Subtype.exists, exists_prop] at hw
    rcases hw with ⟨s, a, b, hs1, hs2, hs3⟩
    specialize hs1 s
    have hDiag : (diagDynamicalSystem dSystem dSystem).map s (a, b)
      = (dSystem.map s a, dSystem.map s b) := by
      rfl
    rw [hDiag]
    exact hs1
  have hα4 : setOrbitClosure (diagDynamicalSystem dSystem dSystem) α ⊆ closure β := by
    unfold setOrbitClosure
    apply closure_mono
    exact hα3
  have hα5 : t ∉ setOrbitClosure (diagDynamicalSystem dSystem dSystem) α := by
    intro htFalse
    have htFalse2 : t ∈ closure β := by
      apply hα4
      exact htFalse
    exact hβ2 htFalse2
  unfold RPM at ht1
  simp only [Set.mem_iInter] at ht1
  specialize ht1 α hα2
  exact hα5 ht1

end Equicontinuity_and_regional_proximality

section Equicontinuity_and_regional_proximality_with_S_commutative

/- Note the following generalizes equicontinuousIffRPTrivial by
applying the following to the identity map --/
/- I added [CommSemigroup S] later.  So in the following theorems,
we have both [Semigroup S] and [CommSemigroup S].  This is probably
not best practice.  Consider reducing the scope to not use the global
variables. -/
/- This is indeed a problem. When I apply commMinRPIsInImageOfRP in
minimalFactorEquicontinuousIffRPInFactorRelation,
Lean cannot parse it. So I had to separate into a new section where we
don't assume S is Semigroup, but a Commutative Semigroup -/

/-- A factor `π : X → Y` of a minimal system is equicontinuous
iff `RP_X ⊆ R_π` -/
theorem minimalFactorEquicontinuousIffRPInFactorRelation
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) {hMin : isMinimalSystem dSystem}
{Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemY : DynamicalSystem S Y)
{π : X → Y} (hFactorMap : isFactorMap dSystem dSystemY π) :
(RPM dSystem ⊆ mapRelation π ↔ isEquicontinuousSystem dSystemY)
∧
(RP dSystem ⊆ mapRelation π ↔ isEquicontinuousSystem dSystemY) := by
have RPMgoal : RPM dSystem ⊆ mapRelation π ↔ isEquicontinuousSystem dSystemY := by
  constructor
  · intro h1
    unfold mapRelation at h1
    have h1recast : Prod.map π π '' RPM dSystem ⊆ Set.diagonal Y := by
      simp [h1]
    have h2 : RPM dSystemY ⊆ Prod.map π π '' RPM dSystem := by
      apply (commMinRPIsInImageOfRP dSystem dSystemY π (hπ := hFactorMap) (hMin := hMin)).1
    have h3 : RPM dSystemY ⊆ Set.diagonal Y := by
      exact h2.trans h1recast
    exact (equicontinuousIffRPMTrivial dSystemY).mp h3
  · intro h1
    unfold mapRelation
    have h2 : RPM dSystemY ⊆ Set.diagonal Y := by
      exact (equicontinuousIffRPMTrivial dSystemY).mpr h1
    have h3 : Prod.map π π '' RPM dSystem ⊆ RPM dSystemY := by
      apply imageOfRPMIsInRPM dSystem dSystemY
      exact hFactorMap
    have hGoal : Prod.map π π '' RPM dSystem ⊆ Set.diagonal Y := by
      exact h3.trans h2
    simp only [Set.image_subset_iff] at hGoal
    exact hGoal
refine ⟨?_, ?_⟩
· exact RPMgoal
/- The remaining statement can be derived easily from
forwardEqualsBackwardRPInMinCommSystem and RPMgoal -/
· sorry

/-- An ICER `I` of a minimal system `X` is equicontinuous iff `RP ⊆ I` -/
theorem minimalICEREquicontinuousIffRPInICER
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem)
{I : Set (X × X)} (hI : isICER dSystem I) :
(isEquicontinuousICER dSystem hI ↔ RPM dSystem ⊆ I)
∧
(isEquicontinuousICER dSystem hI ↔ RP dSystem ⊆ I) := by
have hQuotientNonempty:  Nonempty (Quotient ⟨setToRelation I, hI.2.2⟩) :=
    nonemptyQuotient X hI.2.2
have hQuotientT2 : T2Space (Quotient ⟨setToRelation I, hI.2.2⟩) :=
    quotientOfCompactT2ByClosedIsT2 hI.2.1 hI.2.2
have hFactorMap : isFactorMap dSystem (quotientDynamicalSystem dSystem hI)
    (Quotient.mk ⟨setToRelation I, hI.2.2⟩) := by
    apply quotientMapIsFactorMap
have RPMgoal : isEquicontinuousICER dSystem hI ↔ RPM dSystem ⊆ I := by
  constructor
  · intro h1
    have h3 : RPM dSystem ⊆ mapRelation (Quotient.mk ⟨setToRelation I, hI.2.2⟩) := by
      apply (minimalFactorEquicontinuousIffRPInFactorRelation dSystem
        (quotientDynamicalSystem dSystem hI) hFactorMap).1.mpr
      · exact h1
      · exact hMin
    have h4 : mapRelation (Quotient.mk ⟨setToRelation I, hI.2.2⟩) ⊆ I := by
      intro t ht
      unfold mapRelation at ht
      · simp only [Set.mem_preimage, Set.mem_diagonal_iff, Prod.map_fst, Prod.map_snd] at ht
        have h4a : (setToRelation I) t.1 t.2 := by
          exact Quotient.eq.mp ht
        unfold setToRelation at h4a
        exact h4a
    exact h3.trans h4
  · intro h1
    unfold isEquicontinuousICER
    have h2 : I ⊆ mapRelation (Quotient.mk ⟨setToRelation I, hI.2.2⟩) := by
      intro t ht
      have h2a : (setToRelation I) t.1 t.2 := by
        unfold setToRelation
        exact ht
      apply Quotient.eq.mpr h2a
    apply (minimalFactorEquicontinuousIffRPInFactorRelation dSystem
      (quotientDynamicalSystem dSystem hI) hFactorMap).1.mp
    · exact h1.trans h2
    · exact hMin
refine ⟨?_, ?_⟩
· exact RPMgoal
/- The remaining statement can be derived easily from
forwardEqualsBackwardRPInMinCommSystem and RPMgoal -/
· sorry

end Equicontinuity_and_regional_proximality_with_S_commutative

section Equicontinuous_structure_relation

/-- The set of ICERS of a dynamical system -/
def setOfICERS
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
Set (Set (X × X)) :=
{I : Set (X × X) | isICER dSystem I}

/-- The set of equicontinuous ICERS of a dynamical system -/
def setOfEquicontinuousICERS
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
Set (Set (X × X)) :=
fun (I : Set (X × X)) ↦ ∃ (h : I ∈ setOfICERS dSystem), isEquicontinuousICER dSystem h

/-- The equicontinuous structure relation of a dynamical system is the
intersection of all equicontinuous ICERS of the system -/
def equiStructureRelation
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
Set (X × X) :=
⋂₀ (setOfEquicontinuousICERS dSystem)

/-- The equicontinuous structure relation of a dynamical system is an ICER -/
theorem equiStructureRelationIsICER
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
isICER dSystem (equiStructureRelation dSystem) := by
apply intersectionOfICERsIsICER
intro I hI
unfold setOfEquicontinuousICERS at hI
unfold setOfICERS at hI
rcases hI with ⟨hI1, hI2⟩
exact hI1

/-- The equicontinuous structure relation of a dynamical system is an
equicontinuous ICER -/
theorem equiStructureRelationIsEquiICER
{S : Type*} [CommSemigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (hMin : isMinimalSystem dSystem) :
isEquicontinuousICER dSystem (equiStructureRelationIsICER dSystem) := by
apply (minimalICEREquicontinuousIffRPInICER hMin (equiStructureRelationIsICER dSystem)).1.mpr
unfold equiStructureRelation
simp only [Set.subset_sInter_iff]
intro I hI
unfold setOfEquicontinuousICERS at hI
rcases hI with ⟨hI1, hI2⟩
unfold setOfICERS at hI1
simp only [Set.mem_setOf_eq] at hI1
apply (minimalICEREquicontinuousIffRPInICER hMin hI1).1.mp
exact hI2

end Equicontinuous_structure_relation

--end DS
