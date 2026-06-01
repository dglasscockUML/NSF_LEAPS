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
isInvariantSet dSystem (⋂₀ i) := by
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
by sorry

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
(Set.MapsTo.restrict π Z (π '' Z) (Set.mapsTo_image π Z)) :=
by sorry

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
isICER dSystem (⋂₀ c) :=
by sorry

/-- If `X` is a compact Hausdorff topological space and `I` is a closed
equivalence relation on `X^2`, then `X/I` is a Hausdorff topological space -/
theorem quotientOfCompactT2ByClosedIsT2
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{I : Set (X × X)} (hIClosed : IsClosed I)
(hIEquiv : Equivalence (setToRelation I)) :
T2Space (Quotient ⟨setToRelation I, hIEquiv⟩) :=
by sorry

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
have : Nonempty (Quotient ⟨setToRelation I, hI.2.2⟩) :=
  nonemptyQuotient X hI.2.2
have : T2Space (Quotient ⟨setToRelation I, hI.2.2⟩) :=
  quotientOfCompactT2ByClosedIsT2 hI.2.1 hI.2.2
DynamicalSystem S (Quotient ⟨setToRelation I, hI.2.2⟩) := by
have : Nonempty (Quotient ⟨setToRelation I, hI.2.2⟩) :=
  nonemptyQuotient X hI.2.2
have : T2Space (Quotient ⟨setToRelation I, hI.2.2⟩) :=
  quotientOfCompactT2ByClosedIsT2 hI.2.1 hI.2.2
exact
{
  map := by sorry
  mapMult := by sorry
  mapCont := by sorry
}

-- (hT2 := quotientOfCompactT2ByClosedIsT2 hI.2.1 hI.2.2)
-- (hNonempty := nonemptyQuotient X hI.2.2)

-- The follow code is part of the debugging effort around quotientMapIsEquivariant
/- variable {S : Type*} [Semigroup S] [Nonempty S]
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [hT2 : T2Space X] [hNonempty : Nonempty X]
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
  (Quotient.mk ⟨setToRelation I, hI.2.2⟩) :=
by sorry

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
isNonemptyCompactT2InvariantSubset dSystemY (π '' A) :=
by sorry

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
∃ Y : Set X, isMinimalSubset dSystem Y :=
by sorry

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
{Y : Set X} [CompactSpace Y] [Nonempty Y]
(preSubSystem : isNonemptyCompactT2InvariantSubset dSystem Y) :
isMinimalSubset dSystem Y ↔
  isMinimalSystem (fromNonemptyCompactT2InvariantSubsetToSystem dSystem preSubSystem) := by
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

/-- Image of a minimal system under a continuous, equivariant map is a minimal invariant set -/
lemma imageOfMinimalSetIsMinimal
{dSystemX : DynamicalSystem S X}
{Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
{dSystemY : DynamicalSystem S Y}
(π : X → Y) (hContinuous : Continuous π)
(hEquivariant : isEquivariant dSystemX.map dSystemY.map π)
(Z : Set X) (hZMinimal : isMinimalSubset dSystemX Z) :
isMinimalSubset dSystemY (π '' Z):= by
  sorry

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

/-- The orbit closure of a uniformly recurrent point is a minimal set -/
theorem orbitClosureOfURPointIsMinimalSubset
(dSystem : DynamicalSystem S X)
{x : X} (xisUR : isUniformlyRecurrent dSystem x) :
isMinimalSubset dSystem (orbitClosure dSystem x) := by
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
have : CompactSpace Y := by
  apply isCompact_iff_compactSpace.mp
  exact hY.2.1
have hYNonempty: Nonempty Y := by
  apply hY.1.to_subtype
have hYUreturn : ∀ y : Y, ∀ U : Set Y,
IsOpen U → U.Nonempty → ∃ s : S,  dSystemY.map s y ∈ U := by
  intro y U hUOpen hUNonempty
  haveI h0 : UniformSpace Y := by
    sorry
  have h1 : ∃ V : Set Y, V ⊆ U ∧ V.Nonempty ∧ IsOpen V ∧ ∃ γ : Set (Y × Y), γ ∈ uniformity Y ∧
∀ a ∈ V, ∀ b : Y, (a, b) ∈ γ → b ∈ U := by
    sorry
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
    have h51a : CompactSpace Y := by
      infer_instance
    -- exact CompactSpace.uniformContinuous_of_continuous h50
    sorry
  have h6 : ∃ α ∈ uniformity Y, ∀ f ∈ F,
  (Prod.map (dSystemY.map (t * f)) (dSystemY.map (t * f))) '' α ⊆ γ := by
    sorry
  rcases h6 with ⟨α, hα1, hα2⟩
  have h61 : ∃ W : Set Y, W ∈ nhds y ∧ IsOpen W ∧ ((closure W) ×ˢ (closure W) ⊆ α) := by
    -- exact openClosureProductInEntourage y α
    sorry
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
  rw [<- minimalSubsetIffMinimalSubsystem]
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

end Uniform_recurrence

section Minimality_and_UR_with_commutivity

/-- If a commutative semigroup `S` acts minimally, then it acts surjectively -/
theorem minimalCommActionIsSurjective
{S} [commSemi : CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :
∀ s : S, Function.Surjective (dSystem.map s) :=
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
proximal dSystemY (π x) (π y) :=
by sorry

end Proximality

section Regional_proximality

/-- The regionally proximal relation for a dynamical system, as type `Set (X × X)` -/
def RP
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
Set (X × X) :=
⋂ α ∈ nhdsSet (Set.diagonal X),
setOrbitClosure (diagDynamicalSystem dSystem dSystem) α

/-- The regionally proximal relation is symmetric -/
theorem RPisSymmetric
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
isSymmetric (RP dSystem) :=
by sorry

/-- The regionally proximal relation is invariant under the diagonal
action by `S` -/
theorem RPisInvariant
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
isInvariantSet (diagDynamicalSystem dSystem dSystem) (RP dSystem) :=
by sorry

/-- The regionally proximal relation is closed -/
theorem RPisClosed
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
IsClosed (RP dSystem) :=
by sorry

/-- If `SX` is dense in `X` (a basic nondegeneracy criterion), then `RP` is reflexive -/
theorem RPisReflexiveIfNondegen
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X)
(hNondegen : setOrbitClosure dSystem Set.univ = Set.univ) :
isReflexive (RP dSystem) :=
by sorry

/-- A minimal system satisfies the non-degeneracy condition required to conclude
that `RP` is reflexive -/
lemma minimalImpliesNondegen
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :
setOrbitClosure dSystem Set.univ = Set.univ :=
by
    unfold setOrbitClosure
    rcases (inferInstance : Nonempty X) with ⟨x⟩
    have xDenseOrbit : Dense (orbit dSystem x) := (minimalIffDenseOrbits dSystem).mp hMin x
    have xOrbitAll : closure (orbit dSystem x) = Set.univ := xDenseOrbit.closure_eq
    have xOrbitInSetOrbit : orbit dSystem x ⊆ setOrbit dSystem Set.univ := by sorry
    sorry

/-- A point `(x,y)` belongs to `RP` iff there exists `w ∈ X` and an ultrafilter `F` on
`X × X × S` whose pushforward under `(x,y,s) ↦ (x,y,sx,sy)` limits to `(w,w,x,y)` -/
theorem xyInRPIffUltraToSomewwxy
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (x y : X) :
⟨x,y⟩ ∈ RP dSystem ↔ ∃ (w : X) (F : Ultrafilter ((X × X) × S)),
    Filter.Tendsto (fun (⟨a,s⟩ : (X × X) × S) ↦ (a, (diagDynamicalSystem dSystem dSystem).map s a))
      F (nhds ⟨⟨w,w⟩,⟨x,y⟩⟩) :=
by sorry

/-- For `π : X → Y` a factor map of systems, `(π ⊗ π) RP_X ⊆ RP_Y` -/
theorem imageOfRPIsInRP
{S : Type*} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemX : DynamicalSystem S X)
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemY : DynamicalSystem S Y)
(π : X → Y) {hπ : isFactorMap dSystemX dSystemY π} :
(Prod.map π π) '' (RP dSystemX) ⊆ RP dSystemY :=
by sorry

/-- For `π : X → Y` a factor map of minimal systems with a commutative
acting semigroup, `RP_Y ⊆ (π ⊗ π) RP_X` -/
theorem commMinRPIsInImageOfRP
{S : Type*} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemX : DynamicalSystem S X) {hMin : isMinimalSystem dSystemX}
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemY : DynamicalSystem S Y)
(π : X → Y) {hπ : isFactorMap dSystemX dSystemY π} :
RP dSystemY ⊆ (Prod.map π π) '' (RP dSystemX) :=
by sorry

end Regional_proximality



section Equicontinuity_and_regional_proximality

variable {S} [Semigroup S] [Nonempty S]
variable {X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]

/- This instance makes lean recognize a compact, Hausdorff space as a uniform space -/
instance : UniformSpace X := uniformSpaceOfCompactR1

/-- A dynamical system `dSystem` is equicontinuous if the family of maps
given by `dSystem.map` is uniformly equicontinuous -/
def isEquicontinuousSystem
(dSystem : DynamicalSystem S X) :
Prop :=
UniformEquicontinuous dSystem.map

/-- If `dSystem` and `dSystemY` are equicontinuous dynamical systems, then the
diagonal action of `S` on `X × Y` is an equicontinuous dynamical system -/
theorem diagSystemOfEquiSystemsIsEquiSystem
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
{dSystemX : DynamicalSystem S X} (hXEqui : isEquicontinuousSystem dSystemX)
{dSystemY : DynamicalSystem S Y} (hYEqui : isEquicontinuousSystem dSystemY) :
isEquicontinuousSystem (diagDynamicalSystem dSystemX dSystemY) :=
by sorry

/-- If `dSystem` is an equicontinuous dynamical system and `Z ⊆ X` is a
nonempty, closed, `S`-invariant set, then `Z` is an equicontinuous
dynamical system -/
theorem subsystemOfEquicontinuousIsEquicontinuous
{dSystem : DynamicalSystem S X} (hXEqui : isEquicontinuousSystem dSystem)
{Z : Set X} [CompactSpace Z] [Nonempty Z]
(hZ : isNonemptyCompactT2InvariantSubset dSystem Z) :
isEquicontinuousSystem (fromNonemptyCompactT2InvariantSubsetToSystem dSystem hZ) :=
by sorry

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
(dSystem : DynamicalSystem S X)
{I : Set (X × X)} (hI : isICER dSystem I) :
Prop :=
by
  have : Nonempty (Quotient ⟨setToRelation I, hI.2.2⟩) :=
  nonemptyQuotient X hI.2.2
  have : T2Space (Quotient ⟨setToRelation I, hI.2.2⟩) :=
  quotientOfCompactT2ByClosedIsT2 hI.2.1 hI.2.2
  exact isEquicontinuousSystem (quotientDynamicalSystem dSystem hI)

/-- A dynamical system on `X` is equicontinuous if and only if the
regionally proximal relation is contained in the diagonal of `X × X` -/
theorem equicontinuousIffRPTrivial
(dSystem : DynamicalSystem S X) :
RP dSystem ⊆ Set.diagonal X ↔ isEquicontinuousSystem dSystem :=
by sorry

/- Note the following generalizes equicontinuousIffRPTrivial by
applying the following to the identity map -/
/-- A factor `π : X → Y` of a minimal system is equicontinuous
iff `RP_X ⊆ R_π` -/
theorem minimalFactorEquicontinuousIffRPInFactorRelation
(dSystem : DynamicalSystem S X) {hMin : isMinimalSystem dSystem}
{Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemY : DynamicalSystem S Y)
{π : X → Y} (hFactorMap : isFactorMap dSystem dSystemY π) :
RP dSystem ⊆ mapRelation π ↔ isEquicontinuousSystem dSystemY :=
by sorry

/-- An ICER `I` of a minimal system `X` is equicontinuous iff `RP ⊆ I` -/
theorem minimalICEREquicontinuousIffRPInICER
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem)
{I : Set (X × X)} (hI : isICER dSystem I) :
isEquicontinuousICER dSystem hI ↔ RP dSystem ⊆ I :=
by sorry

end Equicontinuity_and_regional_proximality

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
isICER dSystem (equiStructureRelation dSystem) :=
by sorry

/-- The equicontinuous structure relation of a dynamical system is an
equicontinuous ICER -/
theorem equiStructureRelationIsEquiICER
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
isEquicontinuousICER dSystem (equiStructureRelationIsICER dSystem) :=
by sorry



end Equicontinuous_structure_relation

--end DS
