import NSFLEAPS._08_Application.AP_Main

/-!
# Main results in the RP paper

Explain
-/

/- # Essential Definitions and Lemmas
For those definitions that are repeated, decide what to do ... -/

/- A (topological) dynamical system is a compact Hausdorff space `X` together
with an action by a (discrete) semigroup `S`. -/
-- _structure DynamicalSystem_ APPEARS ALREADY UPSTREAM
-- (S : Type*) [Semigroup S] [Nonempty S]
-- (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
-- where
--   map : S → X → X
--   mapMult : ∀ s₁ s₂ x, map (s₁ * s₂) x = map s₁ (map s₂ x)
--   mapCont : ∀ s, Continuous (map s)

/-- Given an action of `S` on `X` and a semigroup homomorphism `φ: T → S`,
we get an action of `T` on `X` by setting `tx = (φ t)x` -/
def homDynamicalSystemIntro -- See homDynamicalSystem upstream
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

lemma compactT2ByClosedIsCompactT2 --see quotientByCERIsCompactHausdorff
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{R : X → X → Prop} (hEquiv : Equivalence R)
(hClosed : IsClosed {p : X × X | R p.1 p.2}) :
Nonempty (Quotient ⟨R, hEquiv⟩)
∧
CompactSpace (Quotient ⟨R, hEquiv⟩)
∧
T2Space (Quotient ⟨R, hEquiv⟩) := by sorry

lemma compactT2ByClosedIsCompactT2Set --see quotientByCERIsCompactHausdorff
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{I : Set (X × X)}
(IEquiv : Equivalence (fun (x : X) ↦ (⟨x,·⟩ ∈ I)))
(IClosed : IsClosed I) :
let XmodI := Quotient ⟨fun (x : X) ↦ (⟨x,·⟩ ∈ I), IEquiv⟩
Nonempty XmodI
∧
CompactSpace XmodI
∧
T2Space XmodI := by sorry

/-- Given a dynamical system of `S` acting on `X` and an ICER `I`,
the quotient dynamical system has phase space `X/I` with an `S` action
described by `s[x] = [sx]` -/
def quotientDynamicalSystemIntro
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [hT2 : T2Space X] [hNonempty : Nonempty X]
(dSystem : DynamicalSystem S X)
{I : Set (X × X)}
(IEquiv : Equivalence (fun (x : X) ↦ (⟨x,·⟩ ∈ I)))
(IClosed : IsClosed I)
(IInvariant : ∀ (s : S), Set.MapsTo (Prod.map (dSystem.map s) (dSystem.map s)) I I) :
let Y := Quotient ⟨setToRelation I, hI.2.2⟩
have : Nonempty Y := nonemptyQuotient X hI.2.2
have : T2Space Y := quotientOfCompactT2ByClosedIsT2 hI.2.1 hI.2.2
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

/-- A dynamical system `dSystem` is equicontinuous if the family of maps
given by `dSystem.map` is uniformly equicontinuous -/
def isEquicontinuousSystemIntro -- see isEquicontinuousSystem upstream
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
Prop :=
∀ (α : Set (X × X)), IsOpen α → Set.diagonal X ⊆ α →
  ∃ (β : Set (X × X)) (_ : IsOpen β) (_ : Set.diagonal X ⊆ β),
    ∀ (s : S), (fun (x : X × X) ↦
      ⟨dSystem.map s x.1, dSystem.map s x.2⟩) '' β ⊆ α

/-- The regionally proximal relation for a dynamical system, as type `Set (X × X)` -/
def RPIntro -- See RP upstream
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
Set (X × X) :=
⋂ α ∈ nhdsSet (Set.diagonal X),
  closure (⋃ (s : S), (fun (x : X × X) ↦
    ⟨dSystem.map s x.1, dSystem.map s x.2⟩) ⁻¹' α)


/-- The backward regionally proximal relation for a dynamical system, as type `Set (X × X)` -/
def RPMIntro -- See RPM upstream
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
Set (X × X) :=
⋂ α ∈ nhdsSet (Set.diagonal X),
  closure (⋃ (s : S), (fun (x : X × X) ↦
    ⟨dSystem.map s x.1, dSystem.map s x.2⟩) '' α)

/-- The equicontinuous structure relation of a dynamical system is the
intersection of all equicontinuous ICERS of the system -/
def equiStructureRelationIntro
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
Set (X × X) :=
⋂₀ {I : Set (X × X) |
  ∃ (IClosed : IsClosed I)
  (IEqui : Equivalence (fun x y => (x, y) ∈ I))
  (IInvariant : (∀ (s : S) (x y : X), ⟨x,y⟩ ∈ I →
    ⟨dSystem.map s x, dSystem.map s y⟩ ∈ I)),
  isEquicontinuousSystemIntro (quotientSystem dSystem RPEquiv RPClosed RPInv)
  }

/-

isFactorMap
isHomeoSystem
isIsomorphism
isIsomorphic (exists isomorphism)
isLargestEquiFactor

groGroup
instance: groGroup is an abelian group
groGroupHom
groGroupHomIsSemigroupHom

 -/

--  def isSmallestHomeoExtension
--  {S : Type*} [CommSemigroup S] [Nonempty S]
-- {W : Type*} [TopologicalSpace W] [CompactSpace W] [T2Space W] [Nonempty W]
-- (dSystemW : DynamicalSystem S W)
-- {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
-- (dSystemX : DynamicalSystem S X)
-- (π : W → X) :
-- Prop :=
--   isHomeoSystem dSystemW ∧
--   isFactorMap dSystemW dSystemX π ∧
--   ∀ (V : Type*) [TopologicalSpace V] [CompactSpace V] [T2Space V] [Nonempty V],
--   ∀ (dSystemV : DynamicalSystem S V),
--   ∀ (ρ : V → X) (_ : isFactorMap dSystemV dSystemX ρ) (_ : isHomeoSystem dSystemV),
--   ∃ (ξ : V → W) (_ : isFactorMap dSystemV dSystemW ξ), ρ = π ∘ ξ


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
RP dSystem ⊆ { ⟨x,y⟩ : X × X | π x = π y } ↔ isEquicontinuousSystem dSystemY :=
  (minimalFactorEquicontinuousIffRPInFactorRelation dSystem hMin dSystemY hFactorMap).2


/-- # Theorem B Part I
  Let `S` be a commutative semigroup and `X` be a minimal `S`-system.
  The regionally proximal relation coincides with the equicontinuous
  structure relation: `RP = S_eq`. In particular, `RP` is a closed,
  `S`-invariant equivalence relation. -/
theorem RPTheoremBPartI
{S : Type*} [CommSemigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (hMin : isMinimalSystem dSystem) :
RP dSystem = equiStructureRelation dSystem -- RP = S_eq
∧ Equivalence (fun x y => (x, y) ∈ RP dSystem) -- RP is an equivalence relation
∧ IsClosed (RP dSystem) -- RP is closed
∧ (∀ (s : S) (x y : X), ⟨x,y⟩ ∈ RP dSystem →
  ⟨dSystem.map s x, dSystem.map s y⟩ ∈ RP dSystem) -- RP is `S`-invariant
:= by sorry

/-
Further essential defs

quotientSystem (may not need to define in generality, only need for quotient by RP)
RPQuotient (eats proof of minimality of a commutative system, gives quotient set, like RPSetoid)
RPQuotientSystem (the dSystem resulting from it)

 -/

-- use quotientSystem with the fact that RP is an ICE from Part I.
/- # Theorem B Part II
Let `S` be a commutative semigroup and `X` be a minimal `S`-system.
The quotient `X → X/RP` is the largest equicontinuous factor of `X`,
in the sense that if `ξ : X → Y` is an equicontinuous factor of `X`, then
there exists a factor map `ρ : X/RP → Y` of `S`-systems -/
-- theorem RPTheoremBPartII
-- {S : Type*} [CommSemigroup S] [Nonempty S]
-- {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
-- (dSystem : DynamicalSystem S X) (hMin : isMinimalSystem dSystem) :
-- (∀ (Y : Type*) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y],
--   ∀ (dSystemY : DynamicalSystem S Y) (_ : isEquicontinuousSystem dSystemY),
--   ∀ (ρ : X → Y) (_ : isFactorMap dSystemX dSystemY ρ) ,
--   ∃ (ξ : R → Y) (_ : isFactorMap dSystemR dSystemY ξ), ρ = ξ ∘ π) := by sorry


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
(dSystem : DynamicalSystem S X) (hMin : isMinimalSystem dSystem) :
RP dSystem = equiStructureRelation dSystem -- RP = S_eq
∧
-- RP is an equivalence relation
(∃ (RPEquiv : Equivalence (fun x y => (x, y) ∈ RP dSystem)),
-- RP is closed
∃ (RPClosed : IsClosed (RP dSystem)),
-- RP is `S`-invariant
∃ (RPInv : (∀ (s : S) (x y : X), ⟨x,y⟩ ∈ RP dSystem →
  ⟨dSystem.map s x, dSystem.map s y⟩ ∈ RP dSystem)),
let XmodRP := quotientSet dSystem RPEquiv RPClosed RPInv
let dSystemXmodRP := quotientSystem dSystem RPEquiv RPClosed RPInv
(∀ (Y : Type*) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y],
  ∀ (dSystemY : DynamicalSystem S Y) (_ : isEquicontinuousSystem dSystemY),
  ∀ (ρ : X → Y) (_ : isFactorMap dSystemX dSystemY ρ) ,
  ∃ (ξ : XmodRP → Y) (_ : isFactorMap dSystemXmodRP dSystemY ξ), ρ = ξ ∘ π))
:= by sorry


/-- # Theorem C
  Let `S` be a commutative semigroup and `X` be a minimal `S`-system.
  The regionally proximal relation and the backward regionally
  proximal relation coincide: `RP = RP^-`. -/
theorem RPTheoremC
{S : Type*} [CommSemigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (hMin : isMinimalSystem dSystem) :
RP dSystem = RPM dSystem :=
  forwardEqualsBackwardRPInMinCommSystem dSystem hMin


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
RP dSystemS = RP dSystemT :=
  forTwoMinCommActionsRPsAreSame hMinS hMinT hCommActions


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
{S : Type*} [CommSemigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystemX : DynamicalSystem S X} (hMinX : isMinimalSystem dSystemX) :
∃ (W : Type*) (_ : TopologicalSpace W) (_ : CompactSpace W) (_ : T2Space W) (_ : Nonempty W),
∃ (dSystemGW : DynamicalSystem (groGroup S) W) (minGroSys : isMinimalSystem dSystemGW),
-- dSystemSW is the S-system whose existence is stipulated in the theorem
-- statement.  It is the homomorphism system of dSystemWG via groGroupHom
let dSystemSW := homDynamicalSystem groGroupHom dSystemGW
∃ (π : W → X) (_ : isFactorMap dSystemSW dSystemX π),
-- 1. hom system is minimal
∃ (minHomSys : isMinimalSystem dSystemSW),
-- 2. hom system is homeo
isHomeoSystem dSystemSW
∧
-- 3. hom system is smallest homeo extension
(∀ (V : Type*) [TopologicalSpace V] [CompactSpace V] [T2Space V] [Nonempty V],
  ∀ (dSystemV : DynamicalSystem S V) (_ : isHomeoSystem dSystemV),
  ∀ (ρ : V → X) (_ : isFactorMap dSystemV dSystemX ρ),
  ∃ (ξ : V → W) (_ : isFactorMap dSystemV dSystemSW ξ), ρ = π ∘ ξ)
∧
-- dSystemGWmodRP is W / RP_{W,G} (as G-systems) made into an S-system
let dSystemGWmodRP := homDynamicalSystem groGroupHom (RPQuotientSystem minGroSys)
-- dSystemSWmodRP is W / RP_{W,S} (as S-systems)
let dSystemSWmodRP := RPQuotientSystem minHomSys
-- dSystemXmodRP is X / RP_{X,S} (as S-systems)
let dSystemXmodRP := RPQuotientSystem hMinX
-- W / RP_{W,S} and X / RP_{X,S} are isomorphic
isIsomorphic dSystemSWmodRP dSystemXmodRP
∧
-- W / RP_{W,S} and W / RP_{W,G} are isomorphic
isIsomorphic dSystemSWmodRP dSystemGWmodRP
  := by sorry

-- theorem RPTheoremsEandF
-- {S : Type*} [CommSemigroup S] [Nonempty S]
-- {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
-- {dSystemX : DynamicalSystem S X} (hMinX : isMinimalSystem dSystemX) :
-- ∃ (W : Type*) (_ : TopologicalSpace W) (_ : CompactSpace W) (_ : T2Space W) (_ : Nonempty W),
-- ∃ (dSystemW : DynamicalSystem S W) (_ : isMinimalSystem dSystemW) (_ : isHomeoSystem dSystemW),
-- ∃ (π : W → X) (_ : isFactorMap dSystemW dSystemX π),
-- ∃ (G : Type*) (_ : CommGroup G) (_ : Nonempty G),
-- ∃ (dSystemWG : DynamicalSystem G W),
-- ∃ (φ : S → G) (_ : SemigroupHom φ), --Change SemigroupHom to Mathlib version
-- (dSystemW)
-- -- exists abelian group G, an action of G on W making W a G-system, an a
-- -- homomorphism i: S → G st.
-- -- 1. dSystemW is the hom system
-- ∧
-- -- 2. universal property of W as the smallest homeo system extension
-- (∀ (V : Type*) [TopologicalSpace V] [CompactSpace V] [T2Space V] [Nonempty V],
--   ∀ (dSystemV : DynamicalSystem S V) (_ : isHomeoSystem dSystemV),
--   ∀ (ρ : V → X) (_ : isFactorMap dSystemV dSystemX ρ),
--   ∃ (ξ : V → W) (_ : isFactorMap dSystemV dSystemW ξ), ρ = π ∘ ξ)
-- ∧
-- -- 3. there is a map W / RP_{W,S} → X / RP_{X,S} that is an isomorphism
-- (∃ ξ : Quotient (RPSetoid (natExtSystemIsMinimal hMin)) → Quotient (RPSetoid hMin),
--     isIsomorphism (maxEquiFactor (natExtSystemIsMinimal hMin)) (maxEquiFactor hMin) ξ)
-- ∧
-- -- 4. there is a map W / RP_{W,S} → W / RP_{W,G} that is an isomorphism
-- (∃ ζ : Quotient (RPSetoid (natExtSystemIsMinimal hMin))
--      → Quotient (RPSetoid (natExtGroSystemIsMinimal hMin)),
--     isIsomorphism (maxEquiFactor (natExtSystemIsMinimal hMin))
--       (homDynamicalSystem groGroupHom (maxEquiFactor (natExtGroSystemIsMinimal hMin))) ζ)
--  := by sorry


-- challenge in theorem F
/- # Theorem F
  Let `S` be a commutative semigroup, `X` be a minimal `S`-system,
  and `π : W → X` be the natural extension (as constructed in the proof of
  RPTheoremE). The following `S`-systems are the same up to isomorphism:
  · `X / RP_{X,S}`, the largest equicontinuous factor of the `S`-system `X`;
  · `W / RP_{W,S}`, the largest equicontinuous factor of the natural
      extension `W` of `X` as an `S`-system; and
  · `W / RP_{W,Gr(S)}`, the largest equicontinuous factor of the
      natural extension `W` of `X` as a `Gr(S)`-system, made
      into an `S`-system via the homomorphism `i_Gr(S) : S \to Gr(S)`. -/
-- theorem RPTheoremF
-- {S : Type*} [CommSemigroup S] [Nonempty S]
-- {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
-- (dSystem : DynamicalSystem S X) (hMin : isMinimalSystem dSystem) :
-- 1+1=2 := by sorry


/- **Theorem E.**  For a minimal system `X` with natural extension `π : W → X`, the three
`S`-systems

1. `X / RP_X`, the largest equicontinuous factor of `X`;
2. `W / RP_{W,S}`, the largest equicontinuous factor of `W` as an `S`-system;
3. `W / RP_{W,Gr(S)}`, the largest equicontinuous factor of `W` as a `Gr(S)`-system, made
   into an `S`-system via `groGroupHom`,

are the same up to isomorphism. -/
-- theorem theoremE
-- {S} [CommSemigroup S] [Nonempty S]
-- {X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
-- {dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :
-- letI : Nonempty ↑(natExtSet dSystem) :=
--   natExtSetIsNonemptyInstance (hSurject := minimalCommActionIsSurjective hMin)
-- (∃ ξ : Quotient (RPSetoid (natExtSystemIsMinimal hMin)) → Quotient (RPSetoid hMin),
--     isIsomorphism (maxEquiFactor (natExtSystemIsMinimal hMin)) (maxEquiFactor hMin) ξ)
-- ∧
-- (∃ ζ : Quotient (RPSetoid (natExtSystemIsMinimal hMin))
--      → Quotient (RPSetoid (natExtGroSystemIsMinimal hMin)),
--     isIsomorphism (maxEquiFactor (natExtSystemIsMinimal hMin))
--       (homDynamicalSystem groGroupHom (maxEquiFactor (natExtGroSystemIsMinimal hMin))) ζ) :=
-- ⟨maxEquiFactorOfNatExtIsoMaxEquiFactor hMin, maxEquiFactorOfNatExtIsoGroMaxEquiFactor hMin⟩
