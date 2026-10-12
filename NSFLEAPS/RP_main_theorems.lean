module

public import NSFLEAPS._08_Application.AP_Main

/-!
# Main results in the RP paper

This file contains the statements and proofs of the main results from the introduction
section of the paper

`The regionally proximal relation for commutative semigroup actions`
by Angelina Blahodatna, Lauren Detmold, Daniel Glasscock, and Anh N. Le.

This file imports the entire project development, which rests on Mathlib only via
the imports in the IM_Main.lean file.

There are three sections below:
  · Essential definitions
  · Translation lemmas
  · Theorems

The _essential definitions_ section contains commented copies or simplifications of
the definitions required to audit the statements of the main theorems.  A definition
with `Intro` appended is one that has been simplified in this file; its original
form can be found in the development upstream.

The _translation lemmas_ section contains lemmas that connect the simplified
definitions in this file with their analogues in the full development. The statements
and proofs of these lemmas do not need to be audited in order to audit the
statements of the main theorems.

The _theorems_ section contains statements and proofs of the theorems that appear
in the introduction of the paper.

-/

public section

namespace RPIntro

/- # Essential Definitions -/

/-- A (topological) dynamical system is a compact Hausdorff space `X` together
with an action by a (discrete) semigroup `S`. -/
structure DynamicalSystem
(S : Type*) [Semigroup S] [Nonempty S]
(X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
where
  map : S → X → X
  mapMult : ∀ s₁ s₂ x, map (s₁ * s₂) x = map s₁ (map s₂ x)
  mapCont : ∀ s, Continuous (map s)

/-- Given an action of `S` on `X` and a semigroup homomorphism `φ: T → S`,
we get an action of `T` on `X` by setting `tx = (φ t)x` -/
@[expose] def homDynamicalSystem
{S} [Semigroup S] [Nonempty S]
{T} [Semigroup T] [Nonempty T]
(φ : MulHom T S)
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
DynamicalSystem T X :=
{
  map := fun (t : T) ↦ dSystem.map (φ.toFun t)
  mapMult := by
    intro t1 t2 x
    rw [φ.map_mul']
    rw [dSystem.mapMult]
  mapCont := fun (t : T) ↦ dSystem.mapCont (φ t)
}

/-- Given a dynamical system, an ICER is a closed equivalence relation on X that
is invariant under the diagonal action of `S` -/
structure ICER
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) extends Setoid X where
  isClosed : IsClosed {p : X × X | p.1 ≈ p.2}
  isInvariant : ∀ (s : S), Set.MapsTo (Prod.map (dSystem.map s) (dSystem.map s))
    {p : X × X | p.1 ≈ p.2} {p : X × X | p.1 ≈ p.2}

/-- The set form of the relation underlying an ICER -/
@[expose] def ICERToSet
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (I : ICER dSystem) :
Set (X × X) :=
{x : X × X | I.r x.1 x.2}

/-- The quotient of `X` by an ICER on `X` -/
@[expose] def ICERQuotient
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (I : ICER dSystem) :=
Quotient I.toSetoid

/-- The quotient map `X → X/I` for an ICER `I` on `X` -/
@[expose] def ICERQuotientMap
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (I : ICER dSystem) :=
Quotient.mk I.toSetoid

/-- Instance giving that `ICERQuotient` is nonempty -/
instance
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} {I : ICER dSystem} :
Nonempty (ICERQuotient I) := by
  change Nonempty (Quotient I.toSetoid)
  obtain ⟨x⟩ := ‹Nonempty X›
  exact ⟨Quotient.mk' (s := I.toSetoid) x⟩

/-- Instance giving the topology on `ICERQuotient` -/
instance
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} {I : ICER dSystem} :
TopologicalSpace (ICERQuotient I) := by
  change TopologicalSpace (Quotient I.toSetoid)
  exact @instTopologicalSpaceQuotient X I.toSetoid inferInstance

/-- Instance giving that `ICERQuotient` is compact -/
instance
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} {I : ICER dSystem} :
CompactSpace (ICERQuotient I) := by
  change CompactSpace (Quotient I.toSetoid)
  exact Quotient.compactSpace

/-- Instance giving that `ICERQuotient` is T2 -/
instance
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} {I : ICER dSystem} :
T2Space (ICERQuotient I) := by
  unfold ICERQuotient
  exact (quotientByCERIsCompactHausdorff (R := I.r) I.iseqv I.isClosed).2

/-- Given a dynamical system of `S` acting on `X` and an ICER `I`,
the quotient dynamical system has phase space `X/I` with an `S` action
described by `s[x] = [sx]` -/
@[expose] def quotientDynamicalSystem
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [hT2 : T2Space X] [hNonempty : Nonempty X]
{dSystem : DynamicalSystem S X} (I : ICER dSystem) :
DynamicalSystem S (ICERQuotient I) :=
  {
    map := by
      have hRespect : ∀ (s : S), ∀ (x y : X),
         ⟨x,y⟩ ∈ ICERToSet I →
          (ICERQuotientMap I) (dSystem.map s x) = (ICERQuotientMap I) (dSystem.map s y) := by
            intro s x y hxy
            exact (Equivalence.quot_mk_eq_iff I.iseqv (dSystem.map s x) (dSystem.map s y)).mpr
              (I.isInvariant s hxy)
      exact fun s ↦ Quotient.lift ((ICERQuotientMap I) ∘ (dSystem.map s)) (hRespect s)
    mapMult := by
      intro s1 s2 y
      refine Quotient.inductionOn y ?_
      intro x
      have hs12 : dSystem.map (s1 * s2) = (dSystem.map s1) ∘ (dSystem.map s2) := by
        ext t
        exact (dSystem.mapMult s1 s2 t)
      simp only [hs12]
      rfl
    mapCont := by
      intro s
      apply Continuous.quotient_lift
      exact Continuous.comp continuous_quot_mk (dSystem.mapCont s)
  }

/-- A dynamical system satisfies `homeoSystem` if all
elements of the acting semigroup act by homeomorphisms -/
@[expose] def isHomeoSystem
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :=
∀ s : S, IsHomeomorph (dSystem.map s)

/-- An action of `S` on `X` is minimal if every point has a dense `S`-orbit -/
@[expose] def isMinimalSystem
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
Prop :=
∀ (x : X), Dense (Set.range (fun (s : S) ↦ dSystem.map s x))

/-- A dynamical system `dSystem` is equicontinuous if the family of maps
given by `dSystem.map` is uniformly equicontinuous -/
@[expose] def isEquicontinuousSystem
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
Prop :=
∀ (α : Set (X × X)), IsOpen α → Set.diagonal X ⊆ α →
  ∃ (β : Set (X × X)) (_ : IsOpen β) (_ : Set.diagonal X ⊆ β),
    ∀ (s : S), (fun (x : X × X) ↦
      ⟨dSystem.map s x.1, dSystem.map s x.2⟩) '' β ⊆ α

/-- The regionally proximal relation, as a subset of `X × X` -/
@[expose] def RP
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
Set (X × X) :=
⋂ α ∈ nhdsSet (Set.diagonal X),
  closure (⋃ (s : S), (fun (x : X × X) ↦
    ⟨dSystem.map s x.1, dSystem.map s x.2⟩) ⁻¹' α)

/-- The backward regionally proximal relation, as a subset of `X × X` -/
@[expose] def RPM
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
Set (X × X) :=
⋂ α ∈ nhdsSet (Set.diagonal X),
  closure (⋃ (s : S), (fun (x : X × X) ↦
    ⟨dSystem.map s x.1, dSystem.map s x.2⟩) '' α)

/-- The equicontinuous structure relation of a dynamical system is the
intersection of all equicontinuous ICERS of the system -/
@[expose] def equiStructureRelation
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
Set (X × X) :=
⋂₀ {I : Set (X × X) |
  ∃ (IC : ICER dSystem),
    I = ICERToSet IC ∧
    isEquicontinuousSystem (quotientDynamicalSystem IC)
  }

/-- Given dynamical systems `X` and `Y`, a map `π : X → Y` is a factor map
if it is a continuous, `S`-equivariant surjection -/
@[expose] def isFactorMap
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemX : DynamicalSystem S X)
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemY : DynamicalSystem S Y)
(π : X → Y) :
Prop :=
Continuous π
∧
Function.Surjective π
∧
∀ (s : S), (dSystemY.map s) ∘ π = π ∘ (dSystemX.map s)

/-- Given dynamical systems `X` and `Y`, a map `π : X → Y` is an isomorphism
if it is an `S`-equivariant homeomorphism -/
@[expose] def isIsomorphism
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemX : DynamicalSystem S X)
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemY : DynamicalSystem S Y)
(π : X → Y) :
Prop :=
IsHomeomorph π
∧
∀ (s : S), (dSystemY.map s) ∘ π = π ∘ (dSystemX.map s)

/-- Dynamical systems `X` and `Y` are isomorphic if there exists a map `π : X → Y`
that is an isomorphism -/
@[expose] def isIsomorphic
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemX : DynamicalSystem S X)
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemY : DynamicalSystem S Y) :
Prop :=
∃ (ξ : X → Y), isIsomorphism dSystemX dSystemY ξ

/-- A map `π : X → Y` is the largest equicontinuous factor of `X` if for all
equicontinuous factors `ρ : X → Z`, there exists a factor map `ξ : Y → Z`
such that `ρ = ξ ∘ π`. -/
@[expose] def isLargestEquiFactor
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemX : DynamicalSystem S X)
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemY : DynamicalSystem S Y)
(π : X → Y) :
Prop :=
(∀ (Z : Type*) [TopologicalSpace Z] [CompactSpace Z] [T2Space Z] [Nonempty Z],
  ∀ (dSystemZ : DynamicalSystem S Z) (_ : isEquicontinuousSystem dSystemZ),
  ∀ (ρ : X → Z) (_ : isFactorMap dSystemX dSystemZ ρ) ,
  ∃ (ξ : Y → Z) (_ : isFactorMap dSystemY dSystemZ ξ), ρ = ξ ∘ π)

/- The Grothendieck group of a non-empty, commutative semigroup `S` is
the Grothendieck group of the Monoid extension of `S` -/
@[expose] def groGroup
(S : Type*) [CommSemigroup S] [Nonempty S] :=
  Algebra.GrothendieckGroup (WithOne S)

/- `groGroup` is made reducible so that `groGroup S` and `Algebra.GrothendieckGroup (WithOne S)`
are interchangeable during type class synthesis.  This only adds an attribute; the definition
above is unchanged. -/
attribute [reducible] groGroup

/-- Instance giving that `groGroup S` is a commutative group -/
instance
(S : Type*) [CommSemigroup S] [Nonempty S] :
CommGroup (groGroup S) := Algebra.GrothendieckGroup.instCommGroup

/-- The homomorphism from `S` into groGroup `S`, as a `MulHom` structure -/
@[expose] def groGroupHom
{S : Type*} [CommSemigroup S] [nonEmpty : Nonempty S] :
MulHom S (groGroup S) :=
{
  toFun := Algebra.GrothendieckGroup.of ∘ WithOne.coe
  map_mul' := by
    intro s t
    change Algebra.GrothendieckGroup.of (s * t : WithOne S) = (Algebra.GrothendieckGroup.of
      (s : WithOne S)) * (Algebra.GrothendieckGroup.of (t : WithOne S))
    rfl
}


/- # Translation lemmas -/

/-- Given a dynamical system as defined above, give a dynamical system as
defined in the development -/
@[expose] def dSystemToRootdSystem
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
_root_.DynamicalSystem S X := {
  map := dSystem.map
  mapMult := dSystem.mapMult
  mapCont := dSystem.mapCont
}

/-- Given a dynamical system as defined in the development, give a
dynamical system as defined above -/
@[expose] def rootdSystemTodSystem
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : _root_.DynamicalSystem S X) :
DynamicalSystem S X := {
  map := dSystem.map
  mapMult := dSystem.mapMult
  mapCont := dSystem.mapCont
}

/- isMinimalSystem is the same as _root_.isMinimalSystem -/
-- lemma isFactorMapIsSame
-- {S : Type*} [Semigroup S] [Nonempty S]
-- {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
-- (dSystemX : DynamicalSystem S X)
-- {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
-- (dSystemY : DynamicalSystem S Y) (π : X → Y) :
-- isFactorMap dSystemX dSystemY π ↔
--   _root_.isFactorMap (dSystemToRootdSystem dSystemX) (dSystemToRootdSystem dSystemY) π :=
-- by rfl

/-- isMinimalSystem is the same as _root_.isMinimalSystem -/
lemma minimalIsSame
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
isMinimalSystem dSystem ↔ _root_.isMinimalSystem (dSystemToRootdSystem dSystem) :=
  (minimalIffDenseOrbits (dSystemToRootdSystem dSystem)).symm

/-- RP is the same as _root_.RP, version 1 -/
lemma RPSameFromIntroToRoot
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
RP dSystem = _root_.RP (dSystemToRootdSystem dSystem) := rfl

/-- RP is the same as _root_.RP, version 2 -/
lemma RPSameFromRootToIntro
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : _root_.DynamicalSystem S X) :
RP (rootdSystemTodSystem dSystem) = _root_.RP dSystem := rfl

/-- RPM is the same as _root_.RPM -/
lemma RPMSame
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
RPM dSystem = _root_.RPM (dSystemToRootdSystem dSystem) :=
  by
    unfold RPM _root_.RPM setOrbitClosure setOrbit
    unfold diagDynamicalSystem Prod.map dSystemToRootdSystem
    apply Set.iInter_congr; intro α
    apply Set.iInter_congr; intro hα
    apply congrArg closure; ext x
    constructor
    · intro hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨s,a,ha,hax⟩ := hx
      use ⟨s,⟨a,ha⟩⟩
    · intro hx
      obtain ⟨⟨s,a⟩,hsa⟩ := hx
      simp only at hsa
      rw [Set.mem_iUnion]
      use s, ⟨a.1.1,a.1.2⟩
      exact ⟨a.2,hsa⟩

/-- isEquicontinuousSystem is the same as _root_.isEquicontinuousSystem -/
lemma EquiSystemSame
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
isEquicontinuousSystem dSystem ↔ _root_.isEquicontinuousSystem (dSystemToRootdSystem dSystem) :=
by rfl

/-- equiStructureRelation is the same as _root_.equiStructureRelation -/
lemma EquiStructureSame
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
equiStructureRelation dSystem = _root_.equiStructureRelation (dSystemToRootdSystem dSystem) := by
  apply congrArg Set.sInter
  ext x
  constructor
  · intro hx
    obtain ⟨IC, xIsIC, ICisEqui⟩ := hx
    rw [xIsIC]
    use ⟨IC.isInvariant, IC.isClosed, IC.iseqv⟩
    unfold isEquicontinuousICER
    exact (EquiSystemSame (quotientDynamicalSystem IC)).mp ICisEqui
  · intro hx
    obtain ⟨⟨xIsInv, xIsClosed, xIsEquiv⟩, xICERisEqui⟩ := hx
    let IC : ICER dSystem :=
      {
        r := setToRelation x
        iseqv := xIsEquiv
        isClosed := xIsClosed
        isInvariant := xIsInv
      }
    use IC, by rfl
    unfold isEquicontinuousICER at xICERisEqui
    exact (EquiSystemSame (quotientDynamicalSystem IC)).mpr xICERisEqui

/-- quotientDynamicalSystem is isomorphic to _root_.quotientDynamicalSystem -/
lemma QuotSameViaIsom
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X}
{I : Set (X × X)} (hI : isICER (dSystemToRootdSystem dSystem) I)
(J : ICER dSystem) (IisJ : ICERToSet J = I) :
let Y := Quotient ⟨setToRelation I, hI.2.2⟩
let dSystemY := _root_.quotientDynamicalSystem (dSystemToRootdSystem dSystem) hI
let π := Quotient.mk ⟨setToRelation I, hI.2.2⟩
let Z := ICERQuotient J
let dSystemZ := quotientDynamicalSystem J
have : Nonempty Y := nonemptyQuotient X hI.2.2
have : T2Space Y := quotientOfCompactT2ByClosedIsT2 hI.2.1 hI.2.2
∃ (ψ : Z → Y),
isIsomorphism dSystemZ (rootdSystemTodSystem dSystemY) ψ
∧
π = ψ ∘ (ICERQuotientMap J) :=
by
  subst IisJ
  obtain ⟨JIsInv, JIsClosed, JIsEquiv⟩ := hI
  intro Y dSystemY π Z dSystemZ _ _
  use id
  refine ⟨⟨IsHomeomorph.id, ?_⟩, rfl⟩
  intro s
  rfl


/- # Theorems -/

/-- # Theorem A
  Let `S` be a commutative semigroup and `X` be a minimal `S`-system.
  A factor `π : X → Y` is equicontinuous if and
  only if `RP ⊆ {(x,y) ∈ X^2 | π x = π y}`. -/
theorem RPTheoremA
{S : Type*} [CommSemigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (hMin : isMinimalSystem dSystem)
{Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemY : DynamicalSystem S Y)
{π : X → Y} (hFactorMap : isFactorMap dSystem dSystemY π) :
RP dSystem ⊆ { ⟨x,y⟩ : X × X | π x = π y } ↔ isEquicontinuousSystem dSystemY := by
  let rdSystem := dSystemToRootdSystem dSystem
  have rhMin : _root_.isMinimalSystem rdSystem := (minimalIsSame dSystem).mp hMin
  let rdSystemY := dSystemToRootdSystem dSystemY
  -- have rhFactorMap : _root_.isFactorMap rdSystem rdSystemY π :=
  --   (isFactorMapIsSame dSystem dSystemY π).mp hFactorMap
  have : _root_.RP rdSystem ⊆ { ⟨x,y⟩ : X × X | π x = π y } ↔
    _root_.isEquicontinuousSystem rdSystemY :=
      (minimalFactorEquicontinuousIffRPInFactorRelation
        rdSystem rhMin rdSystemY hFactorMap).2
  rw [←(RPSameFromIntroToRoot dSystem)] at this
  rw [←(EquiSystemSame dSystemY)] at this
  exact this

/-- # Theorem B
  Let `S` be a commutative semigroup and `X` be a minimal `S`-system.
  The regionally proximal relation coincides with the equicontinuous
  structure relation: `RP = S_eq`. In particular, `RP` is a closed,
  `S`-invariant equivalence relation. Moreover, the quotient `X → X/RP`
  is the largest equicontinuous factor of `X`, in the sense that if
  `ξ : X → Y` is an equicontinuous factor of `X`, then there exists
  a factor map `ρ : X/RP → Y` of `S`-systems. -/
theorem RPTheoremB
{S : Type*} [CommSemigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :
-- RP = S_eq
RP dSystem = equiStructureRelation dSystem
∧
-- RPX is an ICER and X / RP is the largest equicontinuous factor
(∃ (I : ICER dSystem), RP dSystem = ICERToSet I ∧
  isLargestEquiFactor dSystem (quotientDynamicalSystem I) (ICERQuotientMap I)) :=
by
  let rdSystem := dSystemToRootdSystem dSystem
  have rhMin : _root_.isMinimalSystem rdSystem := (minimalIsSame dSystem).mp hMin
  constructor
  · have := RPisEquiStructureRelation rhMin
    rw [←(RPSameFromIntroToRoot dSystem)] at this
    rw [←(EquiStructureSame dSystem)] at this
    exact this
  · have equiIsRPIntro : _root_.equiStructureRelation
      (dSystemToRootdSystem dSystem) = RP dSystem := by
        have := (RPisEquiStructureRelation rhMin).symm
        rw [←(RPSameFromIntroToRoot dSystem)] at this
        exact this
    let E := _root_.equiStructureRelation (dSystemToRootdSystem dSystem)
    let hE := equiStructureRelationIsICER rdSystem
    let F := RP dSystem
    have hF : isICER (dSystemToRootdSystem dSystem) F := by
      rw [equiIsRPIntro] at hE
      exact hE
    let I : ICER dSystem :=
      {
        r := setToRelation F
        iseqv := hF.2.2
        isClosed := hF.2.1
        isInvariant := hF.1
      }
    have hFishE : ICERToSet I = E := by
      have : ICERToSet I = F := by rfl
      unfold F at this
      rw [←equiIsRPIntro] at this
      exact this
    use I, by rfl
    intro V _ _ _ _ dSystemV VEqui ρ ρFactor
    let rdSystemV := dSystemToRootdSystem dSystemV
    obtain ⟨ξpre, ξpreFactor, ρIsξpreCircQuotmk⟩ :=
      equiStructFactorIsLargestEquiFactor rdSystem V rdSystemV ρ ρFactor VEqui
    obtain ⟨ψ, hψ1, hψ2⟩ := QuotSameViaIsom hE I hFishE
    use ξpre ∘ ψ
    let Y := Quotient ⟨setToRelation E, hE.2.2⟩
    have : Nonempty Y := nonemptyQuotient X hE.2.2
    have : T2Space Y := quotientOfCompactT2ByClosedIsT2 hE.2.1 hE.2.2
    have hψ1Factor : _root_.isFactorMap (dSystemToRootdSystem (quotientDynamicalSystem I))
      (_root_.quotientDynamicalSystem rdSystem hE) ψ := by
        unfold _root_.isFactorMap
        refine ⟨?_,?_,?_⟩
        · exact hψ1.1.continuous
        · exact hψ1.1.bijective.2
        · exact hψ1.right
    have factorComp : _root_.isFactorMap (dSystemToRootdSystem (quotientDynamicalSystem I))
      rdSystemV (ξpre ∘ ψ) := compositionOfFactorMapsIsFactorMap hψ1Factor ξpreFactor
    use factorComp
    rw [Function.comp_assoc ξpre ψ (ICERQuotientMap I)]
    rw [←hψ2]
    exact ρIsξpreCircQuotmk


/-- Using Theorem B, provided `S` is commutative and `dSystem` is minimal,
`RPICER` is the regionally proximal relation as an `ICER` structure -/
@[expose] def RPICER
{S : Type*} [CommSemigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :
ICER dSystem :=
{
  r := fun (x : X) ↦ (⟨x, ·⟩ ∈ RP dSystem)
  iseqv := by
    obtain ⟨I,RPisICERSet,-⟩ := (RPTheoremB hMin).2
    rw [RPisICERSet]
    unfold ICERToSet
    simp only [Set.mem_ofPred_eq]
    exact I.iseqv
  isClosed := by
    change IsClosed (RP dSystem)
    obtain ⟨I,RPisICERSet,-⟩ := (RPTheoremB hMin).2
    rw [RPisICERSet]
    exact I.isClosed
  isInvariant := by
    change ∀ (s : S), Set.MapsTo (Prod.map (dSystem.map s) (dSystem.map s))
      (RP dSystem) (RP dSystem)
    obtain ⟨I,RPisICERSet,-⟩ := (RPTheoremB hMin).2
    rw [RPisICERSet]
    exact I.isInvariant
}

/-- # Theorem C
  Let `S` be a commutative semigroup and `X` be a minimal `S`-system.
  The regionally proximal relation and the backward regionally
  proximal relation coincide: `RP = RP^-`. -/
theorem RPTheoremC
{S : Type*} [CommSemigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (hMin : isMinimalSystem dSystem) :
RP dSystem = RPM dSystem := by
  let rdSystem := dSystemToRootdSystem dSystem
  have rhMin : _root_.isMinimalSystem rdSystem := (minimalIsSame dSystem).mp hMin
  have RPisRPM := forwardEqualsBackwardRPInMinCommSystem rdSystem rhMin
  rw [←(RPSameFromIntroToRoot dSystem)] at RPisRPM
  rw [←RPMSame dSystem] at RPisRPM
  exact RPisRPM

/-- # Theorem D
  Let `S` and `T` be commutative semigroups.  Let `X` be both a minimal
  `S`-system and a minimal `T`-system.  If the actions of `S` and `T` commute,
  then `RP_S = RP_T`. -/
theorem RPTheoremD
{S : Type*} [CommSemigroup S] [Nonempty S]
{T : Type*} [CommSemigroup T] [Nonempty T]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystemS : DynamicalSystem S X} (hMinS : isMinimalSystem dSystemS)
{dSystemT : DynamicalSystem T X} (hMinT : isMinimalSystem dSystemT)
(hCommActions : ∀ (s : S) (t : T),
  (dSystemS.map s) ∘ (dSystemT.map t) = (dSystemT.map t) ∘ (dSystemS.map s)) :
RP dSystemS = RP dSystemT := by
  let rdSystemS := dSystemToRootdSystem dSystemS
  let rdSystemT := dSystemToRootdSystem dSystemT
  have rhMinS : _root_.isMinimalSystem rdSystemS := (minimalIsSame dSystemS).mp hMinS
  have rhMinT : _root_.isMinimalSystem rdSystemT := (minimalIsSame dSystemT).mp hMinT
  have RPisSame := forTwoMinCommActionsRPsAreSame rhMinS rhMinT hCommActions
  rw [←(RPSameFromIntroToRoot dSystemS)] at RPisSame
  rw [←(RPSameFromIntroToRoot dSystemT)] at RPisSame
  exact RPisSame

/-- # Theorems E & F
  Let `S` be a commutative semigroup and `X` be a minimal `S`-system.
  There exists a minimal `S`-system `W` on which `S` acts by homeomorphism
  and a factor map `π : W → X` with the property that for all extensions
  `ξ : V → X` of `S`-systems in which `S` acts on `V` by homeomorphisms, there
  exists a factor map `ρ : V → W` such that `ξ = π ∘ ρ`.
  Moreover, the following `S`-systems are the same up to isomorphism:
  · `X / RP_{X,S}`, the largest equicontinuous factor of the `S`-system `X`;
  · `W / RP_{W,S}`, the largest equicontinuous factor of the natural
      extension `W` of `X` as an `S`-system; and
  · `W / RP_{W,Gr(S)}`, the largest equicontinuous factor of the
      natural extension `W` of `X` as a `Gr(S)`-system, made
      into an `S`-system via the homomorphism `i_Gr(S) : S \to Gr(S)`. -/
theorem RPTheoremsEandF
{S : Type u} [CommSemigroup S] [Nonempty S]
{X : Type v} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystemX : DynamicalSystem S X} (hMinX : isMinimalSystem dSystemX) :
∃ (W : Type (max u v)) (_ : TopologicalSpace W)
  (_ : CompactSpace W) (_ : T2Space W) (_ : Nonempty W),
∃ (dSystemGW : DynamicalSystem (groGroup S) W) (minGroSys : isMinimalSystem dSystemGW),
/- The system `dSystemSW` is the `S`-system whose existence is stipulated in the statement
of the theorem.  It is the homomorphism system of `dSystemWG` via `groGroupHom`. -/
let dSystemSW := homDynamicalSystem groGroupHom dSystemGW
∃ (π : W → X) (_ : isFactorMap dSystemSW dSystemX π),
-- 1. The system `dSystemSW` is minimal
∃ (minHomSys : isMinimalSystem dSystemSW),
-- 2. The semigroup `S` acts by homeomorphisms on the system `dSystemSW`
isHomeoSystem dSystemSW
∧
-- 3. `W → X` is smallest extension on which `S` acts by homeomorphisms
(∀ (V : Type*) [TopologicalSpace V] [CompactSpace V] [T2Space V] [Nonempty V],
  ∀ (dSystemV : DynamicalSystem S V) (_ : isHomeoSystem dSystemV),
  ∀ (ρ : V → X) (_ : isFactorMap dSystemV dSystemX ρ),
  ∃ (ξ : V → W) (_ : isFactorMap dSystemV dSystemSW ξ), ρ = π ∘ ξ)
∧
let XmodRPSystem := quotientDynamicalSystem (RPICER hMinX)
let GWmodRPSystem := homDynamicalSystem groGroupHom
  (quotientDynamicalSystem (RPICER minGroSys))
let SWmodRPSystem := quotientDynamicalSystem (RPICER minHomSys)
-- 4. The systems `W / RP_{W,S}` and `X / RP_{X,S}` are isomorphic
isIsomorphic SWmodRPSystem XmodRPSystem
∧
-- 5. The systems `W / RP_{W,S}` and `W / RP_{W,G}` are isomorphic
isIsomorphic SWmodRPSystem GWmodRPSystem
  := by
  let rdSystemX := dSystemToRootdSystem dSystemX
  have rhMinX : _root_.isMinimalSystem rdSystemX := (minimalIsSame dSystemX).mp hMinX
  have hSurject := minimalCommActionIsSurjective rhMinX
  have : Nonempty ↑(natExtSet rdSystemX) := natExtSetIsNonemptyInstance (hSurject := hSurject)
  have hWMin := natExtSystemIsMinimal rhMinX
  have hWGrMin := natExtGroSystemIsMinimal rhMinX
  refine ⟨natExtSet rdSystemX, inferInstance, inferInstance, inferInstance, this,
    rootdSystemTodSystem (natExtGroSystem hSurject), (minimalIffDenseOrbits _).mp hWGrMin, ?_⟩
  intro dSystemSW
  -- 1. The system `dSystemSW` is minimal: proved by providing (minimalIffDenseOrbits _).mp hWMin
  refine ⟨natExtFactorMap rdSystemX, natExtFactorMapIsFactorMap hSurject,
    (minimalIffDenseOrbits _).mp hWMin, ?_, ?_, ?_⟩
  -- 2. `S` acts by homeomorphisms, since `s` acts as `groGroupHom s`, which is invertible
  · intro s
    let G := natExtGroSystem hSurject
    let g := groGroupHom s
    refine (Homeomorph.mk ⟨G.map g, G.map g⁻¹, ?_, ?_⟩ (G.mapCont g)
      (G.mapCont g⁻¹)).isHomeomorph
    · intro φ
      apply Subtype.ext
      funext h
      exact congrArg φ.1 (inv_mul_cancel_right h g)
    · intro φ
      apply Subtype.ext
      funext h
      exact congrArg φ.1 (mul_inv_cancel_right h g)
  -- 3. universal property of the natural extension
  · intro V _ _ _ _ dSystemV hHomeoV ρ ρFactor
    let rdSystemV := dSystemToRootdSystem dSystemV
    exact natExtUniversalProperty hSurject V rdSystemV ρ ρFactor hHomeoV
  -- 4. and 5.
  · intro XmodRPSystem GWmodRPSystem SWmodRPSystem
    have hX : ∀ s, XmodRPSystem.map s = (maxEquiFactor rhMinX).map s := by
      intro s
      funext q
      refine Quotient.inductionOn (s := RPSetoid rhMinX) q ?_
      intro x
      exact (maxEquiFactorMap rhMinX s x).symm
    have hSW : ∀ s, SWmodRPSystem.map s = (maxEquiFactor hWMin).map s := by
      intro s
      funext q
      refine Quotient.inductionOn (s := RPSetoid hWMin) q ?_
      intro w
      exact (maxEquiFactorMap hWMin s w).symm
    have hGW : ∀ s, GWmodRPSystem.map s =
        (homDynamicalSystem groGroupHom (rootdSystemTodSystem (maxEquiFactor hWGrMin))).map s := by
      intro s
      funext q
      refine Quotient.inductionOn (s := RPSetoid hWGrMin) q ?_
      intro w
      exact (maxEquiFactorMap hWGrMin (groGroupHom s) w).symm
    obtain ⟨ξ, ξHomeo, ξEquiv⟩ := maxEquiFactorOfNatExtIsoMaxEquiFactor rhMinX
    obtain ⟨ζ, ζHomeo, ζEquiv⟩ := maxEquiFactorOfNatExtIsoGroMaxEquiFactor rhMinX
    refine ⟨⟨ξ, ξHomeo, ?_⟩, ⟨ζ, ζHomeo, ?_⟩⟩
    · intro s
      rw [hX s, hSW s]
      exact ξEquiv s
    · intro s
      rw [hGW s, hSW s]
      exact ζEquiv s

end RPIntro

end
