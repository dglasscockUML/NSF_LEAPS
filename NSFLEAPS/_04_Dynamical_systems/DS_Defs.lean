import NSFLEAPS._01_Topology.TP_Defs
import NSFLEAPS._02_Semigroups.SG_Defs

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

/-- The predicate that the set `Z ⊆ X` is a nonempty, compact, T2 subset that is
invariant under the action `dSystem.map` -/
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

-- UNHAPPY
/-- Given a system of `S` acting on `X` and a nonempty, compact, T2, invariant `Z ⊆ X`,
create a term of type `DynamicalSystem S ↑Z`, where note that `↑Z` is the type
corresponding to membership in `Z` (tuples of term of type `X` and proof of
membership in `Z`) -/
def fromNonemptyCompactT2InvariantSubsetToSystem
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X)
{Z : Set X} [CompactSpace ↑Z] [Nonempty ↑Z]
(isInv : isInvariantSet dSystem Z) :
DynamicalSystem S ↑Z :=
{
  map := (fun (s : S) ↦ Set.MapsTo.restrict (dSystem.map s) Z Z (isInv s))
  mapMult := by
    intro s t ⟨z,hz⟩
    unfold Set.MapsTo.restrict Subtype.map
    simp only [dSystem.mapMult s]
  mapCont := by
    intro s
    exact Continuous.restrict (isInv s) (dSystem.mapCont s)
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


section Factor_maps_and_ICERS

/- DGG: I am playing around with different definition structures in this section
until we land on one that works nicely. -/

/-- The definition of a dynamical system Y being a factor of a dynamical system X -/
def isFactor
{S} [Semigroup S] [Nonempty S]
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemY : DynamicalSystem S Y)
(dSystemX : DynamicalSystem S X) :
Prop :=
∃ F : X → Y, Continuous F ∧ Function.Surjective F ∧
(∀ x : X, ∀ s : S, F (dSystemX.map s x) = dSystemY.map s (F (x)))

def isFactorMap
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemX : DynamicalSystem S X)
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemY : DynamicalSystem S Y)
(π : X → Y) :
Prop :=
Continuous π ∧ Function.Surjective π ∧
(∀ x : X, ∀ s : S, π (dSystemX.map s x) = dSystemY.map s (π x))



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
visitTimeSet dSystem x ((dSystem.map s) ⁻¹' U) :=
by sorry

/-- The set of times `U ⊆ X` visits `V ⊆ X`, `R(U,V)`, is equal
to `R(x,V) R(x,U)^{-1}` -/
theorem setVisitsAsQuotientSet
{dSystem : DynamicalSystem S X} (x : X) (U V : Set X) :
setVisitTimeSet dSystem U V = ⋃ s ∈ visitTimeSet dSystem x U,
((· * s) ⁻¹' (visitTimeSet dSystem x V)) :=
by sorry

/-- The set `R(x,∩_i U_i)` is equal to `∩_i R(x,U_i)` -/
theorem visitToInter
{dSystem : DynamicalSystem S X}
(x : X) {I} (f : I → Set X) :
visitTimeSet dSystem x (⋂ i : I, f i) =
⋂ i : I, (visitTimeSet dSystem x (f i)) :=
by sorry

/-- The set `R(x,∪_i U_i)` is equal to `∪_i R(x,U_i)` -/
theorem visitToUnion
{dSystem : DynamicalSystem S X}
(x : X) {I} (f : I → Set X) :
visitTimeSet dSystem x (⋃ i : I, f i) =
⋃ i : I, (visitTimeSet dSystem x (f i)) :=
by sorry

/-- Given `U1 ⊆ U2`, `R(x,U1) ⊆ R(x,U2)` -/
theorem visitTimesMono
(dSystem : DynamicalSystem S X)
(x : X) {U V : Set X} (hMono : U ⊆ V) :
visitTimeSet dSystem x U ⊆ visitTimeSet dSystem x V :=
by sorry

/-- The time of visits of a point `(x,y)` to `U × V` under the diagonal action is
the intersection of `R(x,U)` and `R(y,V)`  -/
theorem visitsToProductsUnderDiagonal
{Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemX : DynamicalSystem S X) (x : X) (U : Set X)
(dSystemY : DynamicalSystem S Y) (y : Y) (V : Set Y) :
visitTimeSet (diagDynamicalSystem dSystemX dSystemY) (x,y) (U ×ˢ V) =
(visitTimeSet dSystemX x U) ∩ (visitTimeSet dSystemY y V) :=
by sorry

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

/-- A minimal set, when made into a system, is a minimal system -/
theorem minimalSubsetIsMinimalSystem
(dSystem : DynamicalSystem S X)
{Y : Set X} [CompactSpace Y] [Nonempty Y]
(hMinSubset : isMinimalSubset dSystem Y) :
isMinimalSystem (fromNonemptyCompactT2InvariantSubsetToSystem dSystem (hMinSubset.1.2.2.2)) :=
by sorry -- UNHAPPY, WAIT TO TOUCH

/-- A system is minimal if and only if for all points `x ∈ X`, the `S`-orbit of
`x` is dense -/
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
(dSystem : DynamicalSystem S X) {hMin : isMinimalSystem dSystem} :
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
    minimalImpliesSyndeticVisits (hMin := hMin) dSystem x V Vnonempty Vopen
  exact syndeticIsMonotone goalforV (visitTimesMono dSystem x VinU)

/-- The orbit closure of a uniformly recurrent point is a minimal set -/
theorem orbitClosureOfURPointIsMinimalSubset
(dSystem : DynamicalSystem S X)
{x : X} (xisUR : isUniformlyRecurrent dSystem x) :
isMinimalSubset dSystem (orbitClosure dSystem x) :=
by sorry

/-- If `y` is in the orbit closure of a uniformly recurrent point `x`, then
`y` is uniformly recurrent -/
theorem inOrbitClosOfURPointImpliesUR
(dSystem : DynamicalSystem S X)
{x : X} (xisUR : isUniformlyRecurrent dSystem x)
{y : X} (yinOrbClos : y ∈ orbitClosure dSystem x) :
isUniformlyRecurrent dSystem y :=
by sorry

end Uniform_recurrence

section temp_minimality_with_S_commutative

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
Dense {(x,y) : X × X | isUniformlyRecurrent (diagDynamicalSystem dSystem dSystem) (x,y)} :=
by sorry

end temp_minimality_with_S_commutative

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



end Proximality



section Regional_proximality

/-- The regionally proximal relation for a dynamical system -/
def RP
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
Set (X × X) :=
⋂ α ∈ nhdsSet (Set.diagonal X),
setOrbitClosure (diagDynamicalSystem dSystem dSystem) α

-- UNHAPPY
def setToRel
{X} (s : Set (X × X)) :
X → X → Prop :=
fun x y => (x, y) ∈ s

theorem RPisSymm
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
Std.Symm (setToRel (RP dSystem)) :=
by sorry

theorem RPisTrans
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
IsTrans X (setToRel (RP dSystem)) :=
by sorry

theorem RPisReflexIfNondegen
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X)
(hNondegen : setOrbitClosure dSystem Set.univ = Set.univ) :
Std.Refl (setToRel (RP dSystem)) :=
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


end Equicontinuity_and_regional_proximality


section Equicontinuous_structure_relation

end Equicontinuous_structure_relation

--end DS
