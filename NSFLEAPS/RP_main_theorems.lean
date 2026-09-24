import NSFLEAPS._08_Application.AP_Defs

/-!
# Main results in the RP paper

Explain
-/

/- # Essential Definitions
For those definitions that are repeated, decide what to do ... -/

/- For challenge file later

dSystem
isEquicontinuousSystem
RP
RPM
equicontinuousStructureRelation
isFactorMap

 -/

 def isSmallestHomeoExtension
 {S : Type*} [CommSemigroup S] [Nonempty S]
{W : Type*} [TopologicalSpace W] [CompactSpace W] [T2Space W] [Nonempty W]
(dSystemW : DynamicalSystem S W)
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystemX : DynamicalSystem S X)
(π : W → X) :
Prop :=
  isHomeoSystem dSystemW ∧
  isFactorMap dSystemW dSystemX π ∧
  ∀ (V : Type*) [TopologicalSpace V] [CompactSpace V] [T2Space V] [Nonempty V],
  ∀ (dSystemV : DynamicalSystem S V),
  ∀ (ρ : V → X) (_ : isFactorMap dSystemV dSystemX ρ) (_ : isHomeoSystem dSystemV),
  ∃ (ξ : V → W) (_ : isFactorMap dSystemV dSystemW ξ), ρ = π ∘ ξ


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


/-- # Theorem B
  Let `S` be a commutative semigroup and `X` be a minimal `S`-system.
  The regionally proximal relation coincides with the equicontinuous
  structure relation: `RP = S_eq`. In particular, `RP` is an equivalence relation,
  and the quotient `X → X/RP` is the largest equicontinuous factor of `X`. -/
theorem RPTheoremB
{S : Type*} [CommSemigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (hMin : isMinimalSystem dSystem) :
RP dSystem = equiStructureRelation dSystem -- RP = S_eq
∧ Equivalence (fun x y => (x, y) ∈ RP dSystem) -- RP is an equivalence relation
--∧ isLargestEquiFactor (quotMap) -- quotient map is the largest equicontinuous factor
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

/-- # Theorem E
  Let `S` be a commutative semigroup and `X` be a minimal `S`-system.
  There exists a minimal `S`-system `W` on which `S` acts by homeomorphism
  and a factor map `π : W → X` with the property that for all extensions
  `ξ : V → X` of `S`-systems in which `S` acts on `V` by homeomorphisms, there
  exists a factor map `ρ : V → W` such that `ξ = π ∘ ρ`. -/
theorem RPTheoremE
{S : Type*} [CommSemigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystemX : DynamicalSystem S X} (hMinX : isMinimalSystem dSystemX) :
∃ (W : Type*) (_ : TopologicalSpace W) (_ : CompactSpace W) (_ : T2Space W) (_ : Nonempty W),
∃ (dSystemW : DynamicalSystem S W) (_ : isMinimalSystem dSystemW) (_ : isHomeoSystem dSystemW),
∃ (π : W → X) (_ : isFactorMap dSystemW dSystemX π),
∀ (V : Type*) [TopologicalSpace V] [CompactSpace V] [T2Space V] [Nonempty V],
  ∀ (dSystemV : DynamicalSystem S V),
  ∀ (ρ : V → X) (_ : isFactorMap dSystemV dSystemX ρ) (_ : isHomeoSystem dSystemV),
  ∃ (ξ : V → W) (_ : isFactorMap dSystemV dSystemW ξ), ρ = π ∘ ξ := by sorry
-- use the grothendieck group construction.  see in particular natExtOfMinimalCommSystem

/-- # Theorem F
  Let `S` be a commutative semigroup, `X` be a minimal `S`-system,
  and `π : W → X` be the natural extension (as constructed in the proof of
  RPTheoremE). The following `S`-systems are the same up to isomorphism:
  · `X / RP_{X,S}`, the largest equicontinuous factor of the `S`-system `X`;
  · `W / RP_{W,S}`, the largest equicontinuous factor of the natural
      extension `W` of `X` as an `S`-system; and
  · `W / RP_{W,Gr(S)}`, the largest equicontinuous factor of the
      natural extension `W` of `X` as a `Gr(S)`-system, made
      into an `S`-system via the homomorphism `i_Gr(S) : S \to Gr(S)`. -/
theorem RPTheoremF
{S : Type*} [CommSemigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (hMin : isMinimalSystem dSystem) :
1+1=2 := by sorry


/-- **Theorem E.**  For a minimal system `X` with natural extension `π : W → X`, the three
`S`-systems

1. `X / RP_X`, the largest equicontinuous factor of `X`;
2. `W / RP_{W,S}`, the largest equicontinuous factor of `W` as an `S`-system;
3. `W / RP_{W,Gr(S)}`, the largest equicontinuous factor of `W` as a `Gr(S)`-system, made
   into an `S`-system via `groGroupHom`,

are the same up to isomorphism.  Both isomorphisms are stated with (2) as the source. -/
theorem theoremE
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :
letI : Nonempty ↑(natExtSet dSystem) :=
  natExtSetIsNonemptyInstance (hSurject := minimalCommActionIsSurjective hMin)
(∃ ξ : Quotient (RPSetoid (natExtSystemIsMinimal hMin)) → Quotient (RPSetoid hMin),
    isIsomorphism (maxEquiFactor (natExtSystemIsMinimal hMin)) (maxEquiFactor hMin) ξ)
∧
(∃ ζ : Quotient (RPSetoid (natExtSystemIsMinimal hMin))
     → Quotient (RPSetoid (natExtGroSystemIsMinimal hMin)),
    isIsomorphism (maxEquiFactor (natExtSystemIsMinimal hMin))
      (homDynamicalSystem groGroupHom (maxEquiFactor (natExtGroSystemIsMinimal hMin))) ζ) :=
⟨maxEquiFactorOfNatExtIsoMaxEquiFactor hMin, maxEquiFactorOfNatExtIsoGroMaxEquiFactor hMin⟩
