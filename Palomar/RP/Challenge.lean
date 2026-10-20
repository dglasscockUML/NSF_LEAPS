module

public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

/-!
# Advertised statement

This module states the six main theorems of

  A. Blahodatna, L. Detmold, D. Glasscock and A. N. Le,
  "The regionally proximal relation for commutative semigroup
  actions", arXiv:2610.10397,

together with the definitions they depend on. Each theorem carries the letter
it has in the introduction of that paper and is stated here without proof;
proofs are supplied in `Solution.lean` from the development in this repository.

## What is claimed

Theorem A states that for a commutative semigroup S and a minimal S-system X,
a factor is equicontinuous exactly when RP is contained in the relation it
induces.

Theorem B states that RP and Seq coincide; in particular RP is a
closed, S-invariant equivalence relation and X -> X/RP is the largest
equicontinuous factor of X.

Theorem C states that RP coincides with the backward regionally proximal
relation RP^-, the second natural generalization of regional proximality
from groups to semigroups; the two differ in general for semigroup actions,
already for S = (N,+).

Theorem D states that commuting minimal actions of two commutative semigroups
on the same space induce the same regionally proximal relation.

Theorems E and F concern natural extensions. Theorem E constructs, for any
minimal action of a commutative semigroup, a smallest extension on which the
semigroup acts by homeomorphisms: a minimal S-system W and a factor map
W -> X through which every extension of X by homeomorphisms factors. The
construction goes through the Grothendieck group of S and requires no
cancellativity assumption. Theorem F identifies the largest equicontinuous
factor of X with that of its natural extension W, both as an S-system and as
a Gr(S)-system.

## Conventions

Semigroups are discrete and assumed nonempty. Phase spaces are assumed
nonempty, compact and Hausdorff. These hypotheses appear as typeclass
arguments on every definition and theorem below rather than being assumed
globally. Commutativity is assumed only in the theorems, not in the
definitions.

A dynamical system is bundled as a structure carrying the action map together
with its multiplicativity and continuity. The regionally proximal relation
and its backward counterpart are defined as subsets of X x X rather than as
Setoid instances, since neither is an equivalence relation without the
hypotheses of Theorem B. An ICER is a closed, invariant equivalence relation,
presented as a Setoid together with those two properties; the compact
Hausdorff structure on the quotient of a system by an ICER is established
below, because the statements of Theorems B, E and F depend on it.

The regionally proximal relation has classically been defined only for group
actions. The definition used here, for actions of a general semigroup, is the
one adopted by Auslander and Dai and by Dai and Xiao; it agrees with the
classical relation whenever the acting semigroup is a group, so nothing is
lost relative to the classical setting. It is not the only natural
generalization: following instead de Vries's group-action definition gives
the backward regionally proximal relation `RPM`, written `RP⁻` in the paper.
For semigroup actions the two differ in general, already for `S = (ℕ, +)`,
which is what gives `RPTheoremC` its content.

The Lean proof of the T2Space (ICERQuotient I) instance below was rendered
by a model from an English proof written by the authors.

The Grothendieck group of a commutative semigroup S is taken to be the
Grothendieck group of the monoid WithOne S, which requires no cancellativity
assumption on S.
-/

public section

namespace RPIntro

/- # Definitions -/

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

/-- Toward `instT2SpaceICERQuotient`, `ICERQuotientMapClosed` shows that
the image of a closed set under the quotient map is closed -/
theorem ICERQuotientMapClosed
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} {I : ICER dSystem} :
∀ K : Set X, IsClosed K → IsOpen (Quotient.mk I.toSetoid '' K)ᶜ :=
  fun K hK ↦ by
    rw [← isQuotientMap_quotient_mk'.isOpen_preimage, Set.preimage_compl, isOpen_compl_iff]
    convert (((hK.isCompact.prod isCompact_univ).inter_right I.isClosed).image
      continuous_snd).isClosed using 1
    ext x
    constructor
    · rintro ⟨a, haK, hEq⟩
      exact ⟨(a, x), ⟨⟨haK, Set.mem_univ x⟩, Quotient.eq.mp hEq⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨⟨haK, -⟩, hab⟩, rfl⟩
      exact ⟨a, haK, Quotient.eq.mpr hab⟩

/-- Toward `instT2SpaceICERQuotient`, `ICERQuotientT2Space` gives that `ICERQuotient I`
is a Hausdorff space -/
theorem ICERQuotientT2Space
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} {I : ICER dSystem} :
T2Space (ICERQuotient I) := by
  change T2Space (Quotient I.toSetoid)
  refine ⟨fun a b hab ↦ ?_⟩
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Quotient.mk_surjective b
  -- separate the (compact, disjoint) fibres in `X`, then push forward
  have hF : ∀ c : X, IsCompact {y | I.r y c} := fun c ↦
    (I.isClosed.preimage (continuous_id.prodMk continuous_const)).isCompact
  obtain ⟨U, V, hU, hV, haU, hbV, hUV⟩ := SeparatedNhds.of_isCompact_isCompact (hF a) (hF b)
    (Set.disjoint_left.2 fun y hya hyb ↦ hab (Quotient.sound (I.trans (I.symm hya) hyb)))
  refine ⟨_, _, ICERQuotientMapClosed _ hU.isClosed_compl,
    ICERQuotientMapClosed _ hV.isClosed_compl,
    fun h ↦ Exists.elim h (fun y hy ↦ hy.1 (haU (Quotient.exact hy.2))),
    fun h ↦ Exists.elim h (fun y hy ↦ hy.1 (hbV (Quotient.exact hy.2))),
      Set.disjoint_left.2 fun q hqU hqV ↦ ?_⟩
  obtain ⟨y, rfl⟩ := Quotient.mk_surjective q
  exact hqV ⟨y, Set.disjoint_left.1 hUV (not_not.1 fun h ↦ hqU ⟨y, h, rfl⟩), rfl⟩

/-- Instance giving that `ICERQuotient` is Hausdorff -/
instance ICERQuotientT2SpaceInst
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} {I : ICER dSystem} :
T2Space (ICERQuotient I) := ICERQuotientT2Space

/-- Toward describing quotient systems, quotientLiftRespects shows that if
`[x]_I = [y]_I`, then `[sx]_I = [sy]_I` -/
theorem quotientLiftRespects
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [hT2 : T2Space X] [hNonempty : Nonempty X]
{dSystem : DynamicalSystem S X} (I : ICER dSystem) (s : S) :
    ∀ x y : X, ⟨x, y⟩ ∈ ICERToSet I →
      ICERQuotientMap I (dSystem.map s x) = ICERQuotientMap I (dSystem.map s y) := by
        intro x y hxy
        exact (Equivalence.quot_mk_eq_iff I.iseqv (dSystem.map s x) (dSystem.map s y)).mpr
          (I.isInvariant s hxy)

/-- Toward describing quotient systems, quotientSystemMap defines the action by `S` on the
quotient -/
@[expose] def quotientSystemMap
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [hT2 : T2Space X] [hNonempty : Nonempty X]
{dSystem : DynamicalSystem S X} (I : ICER dSystem) :
    S → ICERQuotient I → ICERQuotient I :=
  fun s ↦ Quotient.lift (ICERQuotientMap I ∘ dSystem.map s) (quotientLiftRespects I s)

/-- Toward describing quotient systems, quotientSystemMapMult shows that quotientSystemMap
is an action of S on `ICERQuotient I` -/
theorem quotientSystemMapMult
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [hT2 : T2Space X] [hNonempty : Nonempty X]
{dSystem : DynamicalSystem S X} (I : ICER dSystem) :
∀ (s₁ s₂ : S) (y : ICERQuotient I),
  (quotientSystemMap I) (s₁ * s₂) y = (quotientSystemMap I) s₁ ((quotientSystemMap I) s₂ y) :=
    by
      intro s1 s2 y
      refine Quotient.inductionOn y ?_
      intro x
      have hs12 : dSystem.map (s1 * s2) = (dSystem.map s1) ∘ (dSystem.map s2) := by
        ext t
        exact (dSystem.mapMult s1 s2 t)
      unfold quotientSystemMap
      simp only [hs12]
      rfl

/-- Toward describing quotient systems, quotientSystemMapCont shows that quotientSystemMap
is continuous -/
theorem quotientSystemMapCont
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [hT2 : T2Space X] [hNonempty : Nonempty X]
{dSystem : DynamicalSystem S X} (I : ICER dSystem) :
∀ (s : S), Continuous (quotientSystemMap I s) :=
  by
    intro s
    apply Continuous.quotient_lift
    exact Continuous.comp continuous_quot_mk (dSystem.mapCont s)

/-- Given a dynamical system of `S` acting on `X` and an ICER `I`,
the quotient dynamical system has phase space `X/I` with an `S` action
described by `s[x] = [sx]` -/
@[expose] def quotientDynamicalSystem
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [hT2 : T2Space X] [hNonempty : Nonempty X]
{dSystem : DynamicalSystem S X} (I : ICER dSystem) :
DynamicalSystem S (ICERQuotient I) :=
  { map := quotientSystemMap I
    mapMult := quotientSystemMapMult I
    mapCont := quotientSystemMapCont I }

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

/-- The regionally proximal relation of a dynamical system, as a subset of
`X × X`: the intersection, over all neighbourhoods `α` of the diagonal, of
the closure of the union over `s ∈ S` of the preimages of `α` under
`s × s`.

Equivalently, `(x, y) ∈ RP` when for every neighbourhood `U` of `x`, every
neighbourhood `V` of `y` and every neighbourhood `α` of the diagonal, there
are `x' ∈ U`, `y' ∈ V` and `s ∈ S` with `(s x', s y') ∈ α`.

The relation is classically defined only for group actions. This is the
semigroup-action definition adopted by Auslander and Dai and by Dai and
Xiao, and it agrees with the classical relation when `S` is a group. See
`RPM` for the other natural generalization.

References:
J. Auslander and X. Dai, *Minimality, distality and equicontinuity for
semigroup actions on compact Hausdorff spaces*, Discrete Contin. Dyn. Syst.
39(8):4647–4711, 2019.
X. Dai and Z. Xiao, *Equicontinuity, uniform almost periodicity, and
regionally proximal relation for topological semiflows*, Topology Appl.
231:35–49, 2017. -/
@[expose] def RP
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
Set (X × X) :=
⋂ α ∈ nhdsSet (Set.diagonal X),
  closure (⋃ (s : S), (fun (x : X × X) ↦
    ⟨dSystem.map s x.1, dSystem.map s x.2⟩) ⁻¹' α)

/-- The backward regionally proximal relation, as a subset of `X × X`:
as `RP`, but with the images of `α` under `s × s` in place of the
preimages.

This is the second natural generalization of the classical relation to
semigroup actions, obtained by following the group-action definition in
de Vries. For group actions `RP` and `RPM` coincide; for semigroup actions
they differ in general, already for `S = (ℕ, +)`. `RPTheoremC` records that
they nevertheless agree when `S` is commutative and the action is minimal. -/
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
RP dSystem ⊆ { ⟨x,y⟩ : X × X | π x = π y } ↔
  isEquicontinuousSystem dSystemY := sorry

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
(∃ (I : ICER dSystem),
  RP dSystem = ICERToSet I
  ∧
  isFactorMap dSystem (quotientDynamicalSystem I) (ICERQuotientMap I)
  ∧
  (∀ (Z : Type*) [TopologicalSpace Z] [CompactSpace Z] [T2Space Z] [Nonempty Z],
    ∀ (dSystemZ : DynamicalSystem S Z) (_ : isEquicontinuousSystem dSystemZ),
    ∀ (ρ : X → Z) (_ : isFactorMap dSystem dSystemZ ρ),
    ∃ (ξ : (ICERQuotient I) → Z)
      (_ : isFactorMap (quotientDynamicalSystem I) dSystemZ ξ),
        ρ = ξ ∘ (ICERQuotientMap I))) := sorry

/-- # Theorem C
  Let `S` be a commutative semigroup and `X` be a minimal `S`-system.
  The regionally proximal relation and the backward regionally
  proximal relation coincide: `RP = RP^-`. -/
theorem RPTheoremC
{S : Type*} [CommSemigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (hMin : isMinimalSystem dSystem) :
RP dSystem = RPM dSystem := sorry

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
RP dSystemS = RP dSystemT := sorry

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
    have := (RPTheoremB.{u_1,u_2,0} hMin).2
    obtain ⟨I,RPisICERSet,-,-⟩ := (RPTheoremB.{u_1,u_2,0} hMin).2
    rw [RPisICERSet]
    unfold ICERToSet
    simp only [Set.mem_ofPred_eq]
    exact I.iseqv
  isClosed := by
    change IsClosed (RP dSystem)
    obtain ⟨I,RPisICERSet,-,-⟩ := (RPTheoremB.{u_1,u_2,0} hMin).2
    rw [RPisICERSet]
    exact I.isClosed
  isInvariant := by
    change ∀ (s : S), Set.MapsTo (Prod.map (dSystem.map s) (dSystem.map s))
      (RP dSystem) (RP dSystem)
    obtain ⟨I,RPisICERSet,-,-⟩ := (RPTheoremB.{u_1,u_2,0} hMin).2
    rw [RPisICERSet]
    exact I.isInvariant
}

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
isIsomorphic SWmodRPSystem GWmodRPSystem := sorry

end RPIntro

end
