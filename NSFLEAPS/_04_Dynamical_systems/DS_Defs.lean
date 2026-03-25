import NSFLEAPS._01_Topology.TP_Defs
import NSFLEAPS._02_Semigroups.SG_Defs

/- The following namespace line gives all definitions, theorems, etc... a prefix of `DS.` -/
namespace DS

/- Sections are used for organizational purposes only.  See the `Outline` pane under `Explorer`. -/
section Definitions

/-- A semigroup action is an action by a semigroup `S` on a set `X` -/
structure SemigroupAction
(S : Type*) [Semigroup S] [Nonempty S] (X : Type*) [Nonempty X] where
  toFun : S → X → X
  map_mult' : ∀ s₁ s₂ x, toFun (s₁ * s₂) x = toFun s₁ (toFun s₂ x)

/-- A (topological) dynamical system is a compact Hausdorff space `X` together
with an action by a (discrete) semigroup `S`. -/
structure DynamicalSystem
(S : Type*) [Semigroup S] [Nonempty S]
(X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
extends SemigroupAction S X where
  cont' : ∀ s, Continuous (toFun s)

/-- The orbit of a point `x` under the action of a semigroup `S` is the
image of `S` under the map `s ↦ sx` -/
def orbit
{S} [Semigroup S] [Nonempty S] {X} [Nonempty X]
(sAction : SemigroupAction S X) (x : X) :
Set X := Set.range (fun s ↦ sAction.toFun s x)
-- '' (Set.univ : Set S)

/-- The orbit closure of a point `x` under the action of a semigroup `S` is the
closure of the image of `S` under the map `s ↦ sx` -/
def orbitClosure
{S} [Semigroup S] [Nonempty S] {X} [TopologicalSpace X] [Nonempty X]
(sAction : SemigroupAction S X) (x : X) :
Set X :=
closure (orbit sAction x)

/-- Given semigroup actions of `S` on `X` and `Y`, the diagonal semigroup
action of `S` on `X × Y` is given by `s (x,y) = (sx,sy)` -/
def diagSemigroupAction
{S} [Semigroup S] [Nonempty S]
{X Y} [Nonempty X] [Nonempty Y]
(sActionX : SemigroupAction S X)
(sActionY : SemigroupAction S Y) :
SemigroupAction S (X × Y) :=
{
  toFun := fun s ↦ Prod.map (sActionX.toFun s) (sActionY.toFun s)
  map_mult' := by
    intro s t (x,y)
    simp only [Prod.map]
    simp only [sActionX.map_mult']
    simp only [sActionY.map_mult']
}

/-- Given dynamical systems of `S` on `X` and `Y`, the diagonal system
of `S` on `X × Y` is given by `s (x,y) = (sx,sy)` -/
def diagDynamicalSystem
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemX : DynamicalSystem S X)
(dSystemY : DynamicalSystem S Y) :
DynamicalSystem S (X × Y) :=
{
  toFun := fun s ↦ Prod.map (dSystemX.toFun s) (dSystemY.toFun s)
  map_mult' := by
    intro s t (x,y)
    simp only [Prod.map]
    simp only [dSystemX.map_mult']
    simp only [dSystemY.map_mult']
  cont' := by
    intro s
    exact Continuous.prodMap (dSystemX.cont' s) (dSystemY.cont' s)
}

-- Do we need: diagDynamicalSystem?  Wait.

/-- When `S` acts on `X`, if `y` is in the orbit closure of `x` and `z` is
in the orbit closure of `y`, then `z` is in the orbit closure of `x`. -/
theorem orbitTransitivity
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} {x y z : X}
(hyx : y ∈ orbitClosure dSystem.toSemigroupAction x)
(hzy : z ∈ orbitClosure dSystem.toSemigroupAction y) :
z ∈ orbitClosure dSystem.toSemigroupAction x :=
by
  unfold orbitClosure
  simp only [mem_closure_iff]
  intro U hU hzU
  unfold orbitClosure at hzy
  simp only [mem_closure_iff] at hzy
  have UcapOrby : (U ∩ orbit dSystem.toSemigroupAction y).Nonempty :=
    hzy U hU hzU
  rcases UcapOrby with ⟨u, hu1, hu2⟩
  unfold orbit at hu2
  simp only [Set.range] at hu2
  rcases hu2 with ⟨s, hs⟩
  have yInsInvCapU : y ∈ (dSystem.toFun s) ⁻¹' U := by
    simp only [Set.preimage]
    simp only [← hs] at hu1
    exact hu1
  have isOpenInvU : IsOpen ((dSystem.toFun s) ⁻¹' U) :=
    IsOpen.preimage (dSystem.cont' s) hU
  unfold orbitClosure at hyx
  simp only [mem_closure_iff] at hyx
  have invUcapOrby : (((dSystem.toFun s) ⁻¹' U) ∩ orbit dSystem.toSemigroupAction x).Nonempty :=
    hyx ((dSystem.toFun s) ⁻¹' U) isOpenInvU yInsInvCapU
  rcases invUcapOrby with ⟨v, hv1, hv2⟩
  unfold orbit at hv2
  simp only [Set.range] at hv2
  rcases hv2 with ⟨t, ht⟩
  have stxInU : dSystem.toFun (s * t) x ∈ U := by
    simp only [dSystem.map_mult']
    simp only [← ht] at hv1
    exact hv1
  simp only [orbit]
  have stxInRange :
  dSystem.toFun (s * t) x ∈ Set.range fun s ↦ dSystem.toFun s x := by
    simp only [Set.range]
    use s * t
  use dSystem.toFun (s * t) x
  exact ⟨stxInU, stxInRange⟩

/-- A subset `A ⊆ X` is `S`-invariant if `SA ⊆ A` -/
def isInvariantSet
{S} [Semigroup S] [Nonempty S] {X} [Nonempty X]
(sAction : SemigroupAction S X) (A : Set X) :
Prop :=
∀ (s : S)(x : X), x ∈ A → sAction.toFun s x ∈ A

/-- In dynamical system given by an action of a semigroup `S` on a space `X`,
the closure of an `S`-invariant set `A ⊆ X` is `S`-invariant -/
theorem closureOfInvIsInv
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} {A : Set X}
(h : isInvariantSet dSystem.toSemigroupAction A) :
isInvariantSet dSystem.toSemigroupAction (closure A) :=
by sorry
-- Use imageClosureIsClosureImage from the topology file

/-- The `S`-orbit closure of a point `x` is an `S`-invariant subset of `X` -/
theorem orbClosIsInv
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} {x : X} :
isInvariantSet dSystem.toSemigroupAction (orbitClosure dSystem.toSemigroupAction x) :=
by sorry
-- Use closureOfInvIsInv

/-- A sub (topological) dynamical system of a topological dynmical system given by
a semigroup `S` acting on `X` is a nonempty, compact, invariant subset of `X`
together with the action by `S`. -/
def isSubDynamicalSystem
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (Z : Set X) :
Prop :=
Z.Nonempty ∧ IsCompact Z ∧ T2Space Z ∧ isInvariantSet dSystem.toSemigroupAction Z

/- Implemenetation note: SubDynamicalSystem is a class since given the parameters
(a dynamical system and a non-empty, compact, invariant set), it is canonically determined -/

/-- A sub (topological) dynamical system of a topological dynmical system given by
a semigroup `S` acting on `X` is a nonempty, compact, invariant subset of `X`
together with the action by `S`. -/
class SubDynamicalSystem
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (Z : Set X) where
  carrier_inv : isInvariantSet dSystem.toSemigroupAction Z
  carrier_nonempty := Z.Nonempty
  carrier_compact := IsCompact Z

/-- Given a system of `S` acting on `X` and a subset `Z` satisfying
 `isSubDynamicalSystem dSystem Z`, create a term of type `DynamicalSystem S Z` -/
def fromSubSystemToSystem
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X)
{Z : Set X} [CompactSpace ↑Z] [Nonempty ↑Z]
(isSubsys : isSubDynamicalSystem dSystem Z) :
DynamicalSystem S ↑Z :=
{
  toFun := by
    intro s ⟨z,hz⟩
    unfold isSubDynamicalSystem at isSubsys
    unfold isInvariantSet at isSubsys
    rcases isSubsys with ⟨hNon,hCmct,hT2,hInv⟩
    exact ⟨(dSystem.toFun s z : X), hInv s z hz⟩
  map_mult' := by
    intro s t ⟨z,hz⟩
    sorry
  cont' := by sorry
}


-- Still working on this definition.  Not sure how to make lean see that
-- the compactness of Z will come from the assumption isSubDynamicalSystem dSystem Z
/-def makeDynamicalSystemFromSub {S} [Semigroup S] [Nonempty S]
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
theorem orbitClosureIsSubDynamicalSystem
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (x : X) :
isSubDynamicalSystem dSystem (orbitClosure dSystem.toSemigroupAction x) :=
by
  unfold isSubDynamicalSystem
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold orbitClosure
    unfold orbit
    --have nonemptyOrbit : (orbit dSystem.toSemigroupAction x).Nonempty := sorry
    exact Set.Nonempty.mono subset_closure (Set.range_nonempty (fun s ↦ dSystem.toFun s x))
  · exact IsClosed.isCompact (isClosed_closure)
  · infer_instance
  · exact orbClosIsInv


/-- An intersection of `S`-invariant sets is `S`-invariant -/
theorem InterOfInvIsInv
{S} [Semigroup S] [Nonempty S] {X} [Nonempty X]
(sAction : SemigroupAction S X)
{i : Set (Set X)} (h : ∀ (A : Set X), A ∈ i → isInvariantSet sAction A) :
isInvariantSet sAction (⋂₀ i) := by
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
def visitTimeSet
{S} [Semigroup S] [Nonempty S] {X} [Nonempty X]
(sAction : SemigroupAction S X) (x : X) (U : Set X) :
Set S :=
(fun (s : S) ↦ sAction.toFun s x) ⁻¹' U

/-- The set of times `s ∈ S` for which the point `x ∈ X` visits the set `U ⊆ X` -/
def setVisitTimeSet
{S} [Semigroup S] [Nonempty S] {X} [Nonempty X]
(sAction : SemigroupAction S X) (U V : Set X) :
Set S :=
{s : S | (((sAction.toFun s) '' U) ∩ V).Nonempty}

/-- The set of times `s ∈ S` for which the point `x ∈ X` visits the set
`s^{-1} U` is `s^{-1} R(x,U)` -/
theorem visitsToPreimages
{S} [Semigroup S] [Nonempty S] {X} [Nonempty X]
(sAction : SemigroupAction S X) (x : X) (U : Set X) (s : S) :
(s * ·) ⁻¹' (visitTimeSet sAction x U) =
visitTimeSet sAction x ((sAction.toFun s) ⁻¹' U) :=
by sorry

/-- The set of times `U ⊆ X` visits `V ⊆ X`, `R(U,V)`, is equal
to `R(x,V) R(x,U)^{-1}` -/
theorem setVisitsAsQuotientSet
{S} [Semigroup S] [Nonempty S]
{X} [Nonempty X] {sAction : SemigroupAction S X} (x : X) (U V : Set X) :
setVisitTimeSet sAction U V = ⋃ s ∈ visitTimeSet sAction x U,
((· * s) ⁻¹' (visitTimeSet sAction x V)) :=
by sorry

/-- The set `R(x,∩_i U_i)` is equal to `∩_i R(x,U_i)` -/
theorem visitToInter
{S} [Semigroup S] [Nonempty S]
{X} [Nonempty X] {sAction : SemigroupAction S X}
(x : X) {I} (f : I → Set X) :
visitTimeSet sAction x (⋂ i : I, f i) =
⋂ i : I, (visitTimeSet sAction x (f i)) :=
by sorry

/-- The set `R(x,∪_i U_i)` is equal to `∪_i R(x,U_i)` -/
theorem visitToUnion
{S} [Semigroup S] [Nonempty S]
{X} [Nonempty X] {sAction : SemigroupAction S X}
(x : X) {I} (f : I → Set X) :
visitTimeSet sAction x (⋃ i : I, f i) =
⋃ i : I, (visitTimeSet sAction x (f i)) :=
by sorry

/-- Given `U1 ⊆ U2`, `R(x,U1) ⊆ R(x,U2)` -/
theorem visitTimesMono
{S} [Semigroup S] [Nonempty S]
{X} [Nonempty X] (sAction : SemigroupAction S X)
(x : X) {U V : Set X} (hMono : U ⊆ V) :
visitTimeSet sAction x U ⊆ visitTimeSet sAction x V :=
by sorry

/-- The time of visits of a point `(x,y)` to `U × V` under the diagonal action is
the intersection of `R(x,U)` and `R(y,V)`  -/
theorem visitsToProd {S} [Semigroup S] [Nonempty S]
{X Y} [Nonempty X] [Nonempty Y]
(sActionX : SemigroupAction S X) (x : X) (U : Set X)
(sActionY : SemigroupAction S Y) (y : Y) (V : Set Y) :
visitTimeSet (diagSemigroupAction sActionX sActionY) (x,y) (U ×ˢ V) =
(visitTimeSet sActionX x U) ∩ (visitTimeSet sActionY y V) :=
by sorry

end Return_time_sets



section Minimality

/-- An action of `S` on `X` is minimal if `X` is a minimal subset -/
def isMinimalSystem
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
Prop :=
∀ Z : Set X, isSubDynamicalSystem dSystem Z → Z = (Set.univ (α := X))

/-- A subset `Y ⊆ X` is a minimal subset of `X` if it is minimal by containment
amongst all non-empty, compact, `S` invariant sets -/
def isMinimalSubset
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (Y : Set X) :
Prop :=
(isSubDynamicalSystem dSystem Y) ∧
(∀ Z : Set X, Z ⊆ Y → isSubDynamicalSystem dSystem Z → Y = Z)

/-- Every system contains a minimal subset -/
theorem existsMinimalSubset
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
∃ Y : Set X, isMinimalSubset dSystem Y :=
by sorry

/-- A minimal set, when made into a system, is a minimal system -/
theorem minimalSubsetIsMinimalSystem
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X)
{Y : Set X} [CompactSpace Y] [Nonempty Y]
(hMinSubset : isMinimalSubset dSystem Y) :
isMinimalSystem (fromSubSystemToSystem dSystem (hMinSubset.1)) :=
by sorry

/-- A system is minimal if and only if for all points `x ∈ X`, the `S`-orbit of
`x` is dense -/
theorem minimalIffDenseOrbits
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
isMinimalSystem dSystem ↔ ∀ x : X, Dense (orbit dSystem.toSemigroupAction x) :=
by
  constructor
  · intro hIsMin x
    unfold isMinimalSystem at hIsMin
    have orbitIsDense : closure (orbit dSystem.toSemigroupAction x) = Set.univ :=
      hIsMin (closure (orbit dSystem.toSemigroupAction x)) (orbitClosureIsSubDynamicalSystem dSystem x)
    simp only [← dense_iff_closure_eq] at orbitIsDense
    exact orbitIsDense
  · intro hDense Z subsysZ
    rcases subsysZ with ⟨hNon,hCmct,hT2,hInv⟩
    rcases hNon with ⟨z,hz⟩ -- Choose an element of Z with a proof of membership
    have orbitInZ : orbit dSystem.toSemigroupAction z ⊆ Z := by
      unfold orbit
      unfold Set.range
      intro x hx
      unfold isInvariantSet at hInv
      rcases hx with ⟨s,hs⟩
      rewrite [← hs]
      exact hInv s z hz
    have orbitClosInZ : closure (orbit dSystem.toSemigroupAction z) ⊆ Z :=
      closure_minimal orbitInZ (IsCompact.isClosed hCmct)
    simp only [dense_iff_closure_eq] at hDense
    rewrite [hDense z] at orbitClosInZ
    exact Set.Subset.antisymm (Set.subset_univ Z) orbitClosInZ

/-- If a commutative semigroup `S` acts minimally, then it acts surjectively -/
theorem minimalCommActionIsSurjective
{S} [commSemi : CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [csX : CompactSpace X] [T2Space X] [nonX : Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :
∀ s : S, Function.Surjective (dSystem.toFun s) :=
by
  intro s y
  let sX := (dSystem.toFun s) '' Set.univ
  have imageIsSubsystem : isSubDynamicalSystem dSystem sX := by
    unfold isSubDynamicalSystem
    refine ⟨?_ ,?_ ,?_ ,?_⟩
    · unfold sX
      rewrite [Set.image_nonempty (f := dSystem.toFun s)]
      exact Set.univ_nonempty
    · exact (IsCompact.image csX.isCompact_univ (dSystem.cont' s))
    · infer_instance
    · unfold isInvariantSet
      intro t x xinsX
      rcases xinsX with ⟨y, hy, imgyisx⟩
      simp only [← imgyisx]
      simp only [(dSystem.map_mult' t s y).symm]
      simp only [commSemi.mul_comm t s]
      simp only [dSystem.map_mult' s t y]
      have tyinUniv : dSystem.toFun t y ∈ Set.univ := Set.mem_univ (dSystem.toFun t y)
      unfold sX
      unfold Set.image
      use dSystem.toFun t y
  unfold isMinimalSystem at hMin
  have sXisX : sX = Set.univ := hMin sX imageIsSubsystem
  unfold sX at sXisX
  unfold Set.image at sXisX
  have yInUniv : y ∈ Set.univ := Set.mem_univ y
  rewrite [← sXisX] at yInUniv
  rcases yInUniv with ⟨a,ha1,ha2⟩
  use a

-- Continuous.isProperMap
-- IsProperMap.isClosedMap
-- IsCompact.image: continuous image of compact is compact
-- isCompact.isClosed: compact implies closed


end Minimality



section Uniform_recurrence

-- mem_of_mem_nhds : U ∈ 𝓝 x → x ∈ U
-- IsOpen.mem_nhds : IsOpen U → x ∈ U → U ∈ 𝓝 x

/-- An action of `S` on `X` is minimal if `X` is a minimal subset -/
def isUniformlyRecurrent
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (x : X) :
Prop :=
∀ U ∈ nhds x, isSyndetic (visitTimeSet dSystem.toSemigroupAction x U)

/-- In a minimal system, for all `x ∈ X` and all non-empty, open `U ⊆ X`
the set of visit times `R(x,U)` is syndetic -/
theorem minimalImpliesSyndeticVisits
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) {hMin : isMinimalSystem dSystem} :
∀ x : X, ∀ U : Set X, U.Nonempty → IsOpen U →
isSyndetic (visitTimeSet dSystem.toSemigroupAction x U) :=
by
  intro x U U_nonempty U_open
  rewrite [minimalIffDenseOrbits dSystem] at hMin
  unfold Dense orbit at hMin
  simp only [mem_closure_iff] at hMin
  rcases U_nonempty with ⟨u, elt_of_U⟩
  have all_y_map_into_U : ∀ y : X, ∃ s : S, dSystem.toFun s y ∈ U := by
    intro y
    have all_y_map_into_U_half : (U ∩ Set.range fun s ↦ dSystem.toFun s y).Nonempty :=
    hMin y u U U_open elt_of_U
    rcases all_y_map_into_U_half with ⟨u_two, u_two_in_image⟩
    rcases u_two_in_image.2 with ⟨s_witness, s_witness_info⟩
    simp at s_witness_info
    use s_witness
    simp only [s_witness_info]
    exact u_two_in_image.1
  let s_chooser : X → S := fun x : X => Classical.choose (all_y_map_into_U x)
  have s_chooser_property : ∀ x : X, dSystem.toFun (s_chooser x) x ∈ U := by
    intro x
    exact Classical.choose_spec (all_y_map_into_U x)
  let V_chooser : X → Set X := fun x : X => Set.preimage (dSystem.toFun (s_chooser x)) U
  have V_choice_has_x : ∀ x : X, x ∈ V_chooser x := by
    intro x
    unfold V_chooser
    exact s_chooser_property x
  have V_choice_open : ∀ x : X, IsOpen (V_chooser x) := by
    intro x
    have cts_s_chooser : Continuous (dSystem.toFun (s_chooser x)) := dSystem.cont' (s_chooser x)
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
  have tofun_s_x_in_univ : dSystem.toFun s x ∈ Set.univ := by simp
  have tofun_s_x_cover : dSystem.toFun s x ∈ ⋃ y ∈ Y, V_chooser y := cover_prop tofun_s_x_in_univ
  rcases Set.mem_iUnion₂.mp tofun_s_x_cover with ⟨y, hyY, hxFy⟩
  have tofun_s_choose_tofun : dSystem.toFun (s_chooser y) (dSystem.toFun s x) ∈ U := by
    unfold V_chooser at hxFy
    exact hxFy
  have use_semigp_prop : dSystem.toFun ((s_chooser y) * s) x ∈ U := by
    simp only [dSystem.map_mult']
    exact tofun_s_choose_tofun
  have s_chooser_y_works : s_chooser y * s ∈ visitTimeSet dSystem.toSemigroupAction x U := by
    unfold visitTimeSet
    exact use_semigp_prop
  have s_chooser_y_clear: s_chooser y ∈ s_chooser '' (Y : Set X) := by
    simp only [Set.mem_image, SetLike.mem_coe]
    use y
  use s_chooser y


/-- In a minimal system, every point is uniformly recurrent -/
theorem minimalImpliesUniformlyRecurrent
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) {hMin : isMinimalSystem dSystem} :
∀ x : X, isUniformlyRecurrent dSystem x :=
by
  intro x U Unbhd
  simp only [mem_nhds_iff] at Unbhd
  rcases Unbhd with ⟨V, VinU, Vopen, Vhasx⟩
  have Vnonempty : V.Nonempty := Set.nonempty_of_mem Vhasx
  have goalforV : isSyndetic (visitTimeSet dSystem.toSemigroupAction x V) :=
    minimalImpliesSyndeticVisits (hMin := hMin) dSystem x V Vnonempty Vopen
  exact syndeticIsMonotone goalforV (visitTimesMono dSystem.toSemigroupAction x VinU)

/- The orbit closure of a uniformly recurrent point is a minimal system -/
/- theorem orbitClosureOfURPointIsMinimal
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X)
{x : X} (xisUR : isUniformlyRecurrent dSystem x) :
isMinimalSystem (fromSubSystemToSystem dSystem (orbitClosureIsSubDynamicalSystem dSystem x)) -/

--orbitClosureIsSubDynamicalSystem
--fromSubSystemToSystem

theorem inMinCommSystemURPairsDense
{S} [commSemi : CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [csX : CompactSpace X] [T2Space X] [nonX : Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :
Dense {(x,y) : X × X | isUniformlyRecurrent (diagDynamicalSystem dSystem dSystem) (x,y)} :=
by sorry

end Uniform_recurrence



section Proximality

end Proximality



section Regional_proximality


end Regional_proximality


section Equicontinuity_and_regional_proximality


end Equicontinuity_and_regional_proximality


section Equicontinuous_structure_relation

end Equicontinuous_structure_relation

end DS
