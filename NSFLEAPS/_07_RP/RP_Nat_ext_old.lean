import NSFLEAPS._07_RP.RP_Defs

/-! This is a module docstring -/

/-- One inclusion of `forTwoMinCommActionsRPsAreSame`, for the backward regionally proximal
relation.  This is stated separately only so that it can be applied twice, once with the
roles of `S` and `T` exchanged; `S` and `T` live in different universes, so the symmetry
step cannot be carried out inside a single proof. -/
theorem RPMSubsetOfRPMForTwoMinCommActions
{S} [CommSemigroup S] [Nonempty S]
{T} [CommSemigroup T] [Nonempty T]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystemS : DynamicalSystem S X} (hMinS : isMinimalSystem dSystemS)
{dSystemT : DynamicalSystem T X} (hMinT : isMinimalSystem dSystemT)
(hCommActions : ∀ (s : S) (t : T),
  (dSystemS.map s) ∘ (dSystemT.map t) = (dSystemT.map t) ∘ (dSystemS.map s)) :
RPM dSystemS ⊆ RPM dSystemT := by
  -- The actions of `S` and of `T` commute pointwise.
  have hcomm : ∀ (σ : S) (τ : T) (w : X),
      dSystemS.map σ (dSystemT.map τ w) = dSystemT.map τ (dSystemS.map σ w) := by
    intro σ τ w
    simpa using congrFun (hCommActions σ τ) w
  intro z hz
  apply (inRPMiffBackwardUOrbitClosInterNeighDiag dSystemT z).mpr
  -- Let `α` be a neighborhood of the diagonal and `W` an open neighborhood of `z`.
  intro W α hWOpen hWz hαOpen hαDiag
  -- Since `z ∈ RPM dSystemS`, some `s ∈ S` satisfies `s⁻¹ W ∩ α ≠ ∅`.
  obtain ⟨⟨x₀, y₀⟩, hp₀α, hp₀orb⟩ :=
    (inRPMiffBackwardUOrbitClosInterNeighDiag dSystemS z).mp hz W α hWOpen hWz hαOpen hαDiag
  simp only [inverseSetOrbit, Set.mem_iUnion, Set.mem_preimage] at hp₀orb
  obtain ⟨s, hs⟩ := hp₀orb
  -- `G = α ∩ s⁻¹ W` is open and contains `(x₀, y₀)`.
  have hGOpen : IsOpen (α ∩ ((diagDynamicalSystem dSystemS dSystemS).map s) ⁻¹' W) :=
    hαOpen.inter (hWOpen.preimage ((diagDynamicalSystem dSystemS dSystemS).mapCont s))
  have hp₀G : (x₀, y₀) ∈ α ∩ ((diagDynamicalSystem dSystemS dSystemS).map s) ⁻¹' W :=
    ⟨hp₀α, hs⟩
  -- Choose non-empty open `U`, `V` with `U × V ⊆ s⁻¹ W ∩ α`.
  obtain ⟨U, V, hUOpen, hVOpen, hx₀U, hy₀V, hUV⟩ := isOpen_prod_iff.mp hGOpen x₀ y₀ hp₀G
  -- Since `S` acts minimally, some `l ∈ S` gives `Y = U ∩ l⁻¹ V ≠ ∅`.
  obtain ⟨l, hl⟩ := minimalImpliesNonemptySetVisits hMinS x₀ hVOpen ⟨y₀, hy₀V⟩
  simp only [visitTimeSet, Set.mem_preimage] at hl
  have hYOpen : IsOpen (U ∩ (dSystemS.map l) ⁻¹' V) :=
    hUOpen.inter (hVOpen.preimage (dSystemS.mapCont l))
  have hYNonempty : (U ∩ (dSystemS.map l) ⁻¹' V).Nonempty := ⟨x₀, hx₀U, hl⟩
  -- The action of `s` is surjective, so `s⁻¹ Y ≠ ∅`.
  obtain ⟨y₁, hy₁⟩ := hYNonempty
  obtain ⟨a₀, ha₀⟩ := minimalCommActionIsSurjective hMinS s y₁
  have hsa₀ : dSystemS.map s a₀ ∈ U ∩ (dSystemS.map l) ⁻¹' V := by rw [ha₀]; exact hy₁
  -- Since `T` acts minimally, some `t ∈ T` gives `s⁻¹ Y ∩ t⁻¹ Y ≠ ∅`, witnessed by `a₀`.
  obtain ⟨t, ht⟩ := minimalImpliesNonemptySetVisits hMinT a₀ hYOpen ⟨y₁, hy₁⟩
  simp only [visitTimeSet, Set.mem_preimage] at ht
  -- The point `(s a₀, l s a₀)` lies in `α` and is carried into `W` by `t`.
  refine ⟨(dSystemS.map s a₀, dSystemS.map l (dSystemS.map s a₀)), ?_, ?_⟩
  · exact (hUV (Set.mk_mem_prod hsa₀.1 hsa₀.2)).1
  · simp only [inverseSetOrbit, Set.mem_iUnion, Set.mem_preimage]
    refine ⟨t, ?_⟩
    -- `t` moves the point onto the `s`-image of `(t a₀, l t a₀) ∈ U × V`.
    have hbW := (hUV (Set.mk_mem_prod ht.1 ht.2)).2
    have h1 : dSystemT.map t (dSystemS.map s a₀) = dSystemS.map s (dSystemT.map t a₀) :=
      (hcomm s t a₀).symm
    have h2 : dSystemT.map t (dSystemS.map l (dSystemS.map s a₀))
        = dSystemS.map s (dSystemS.map l (dSystemT.map t a₀)) := by
      calc dSystemT.map t (dSystemS.map l (dSystemS.map s a₀))
          = dSystemS.map l (dSystemT.map t (dSystemS.map s a₀)) := (hcomm l t _).symm
        _ = dSystemS.map l (dSystemS.map s (dSystemT.map t a₀)) := by rw [h1]
        _ = dSystemS.map (l * s) (dSystemT.map t a₀) := (dSystemS.mapMult l s _).symm
        _ = dSystemS.map (s * l) (dSystemT.map t a₀) := by rw [mul_comm]
        _ = dSystemS.map s (dSystemS.map l (dSystemT.map t a₀)) := dSystemS.mapMult s l _
    have hgoal : (diagDynamicalSystem dSystemT dSystemT).map t
        (dSystemS.map s a₀, dSystemS.map l (dSystemS.map s a₀))
        = (diagDynamicalSystem dSystemS dSystemS).map s
        (dSystemT.map t a₀, dSystemS.map l (dSystemT.map t a₀)) := by
      simp only [diagDynamicalSystem, Prod.map_apply, Prod.mk.injEq]
      exact ⟨h1, h2⟩
    rw [hgoal]
    exact hbW

/-- When `X` is both a minimal S and T system and actions commute, `RP_S = RP_T` -/
theorem forTwoMinCommActionsRPsAreSame
{S} [CommSemigroup S] [Nonempty S]
{T} [CommSemigroup T] [Nonempty T]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystemS : DynamicalSystem S X} (hMin : isMinimalSystem dSystemS)
{dSystemT : DynamicalSystem T X} (hMinT : isMinimalSystem dSystemT)
(hCommActions : ∀ (s : S) (t : T),
  (dSystemS.map s) ∘ (dSystemT.map t) = (dSystemT.map t) ∘ (dSystemS.map s)) :
RP dSystemS = RP dSystemT := by
  -- Both systems are minimal with a commutative acting semigroup, so `RP = RPM` for each.
  rw [forwardEqualsBackwardRPInMinCommSystem dSystemS (hMin := hMin),
    forwardEqualsBackwardRPInMinCommSystem dSystemT (hMin := hMinT)]
  -- By the symmetry of `S` and `T` it suffices to prove one inclusion.
  apply Set.Subset.antisymm
  · exact RPMSubsetOfRPMForTwoMinCommActions hMin hMinT hCommActions
  · exact RPMSubsetOfRPMForTwoMinCommActions hMinT hMin fun t s => (hCommActions s t).symm

/-- The Grothendieck group of a non-empty, commutative semigroup `S` is
the Grothendieck group of the Monoid extension of `S` -/
def groGroup
(S : Type*) [CommSemigroup S] [Nonempty S] :=
  Algebra.GrothendieckGroup (WithOne S)

/- WithOne S is a CommMonoid (Lean already knows this) -/
-- instance
-- (S : Type*) [CommSemigroup S] [Nonempty S] :
-- CommMonoid (WithOne S) := by infer_instance

/-- `groGroup S` is a commutative group -/
instance
(S : Type*) [CommSemigroup S] [Nonempty S] :
CommGroup (groGroup S) := Algebra.GrothendieckGroup.instCommGroup

/- `groGroup S` is nonempty (Lean already knows this) -/
-- instance
-- (S : Type*) [CommSemigroup S] [Nonempty S] :
-- Nonempty (groGroup S) := by infer_instance

/-- The map from a non-empty, commutative semigroup `S` into its
Grothendieck group `groGroup S` -/
def groGroupHom
{S : Type*} [CommSemigroup S] [nonEmpty : Nonempty S] :
S → groGroup S :=
  Algebra.GrothendieckGroup.of ∘ WithOne.coe

/-- The image of the semigroup `S` in its Grothendieck group -/
def imageOfSemiInGG
{S : Type*} [CommSemigroup S] [Nonempty S] :
Set (groGroup S) :=
groGroupHom '' Set.univ

/-- The map `groGroupHom` is a semigroup homomorphism -/
theorem groGroupHomIsSemigroupHom
(S : Type*) [CommSemigroup S] [Nonempty S] :
∀ (s t : S), groGroupHom (s * t) = (groGroupHom s) * (groGroupHom t) :=
  by sorry

/-- Instance for `groGroupHom` being a semigroup homomorphism -/
instance
(S : Type*) [CommSemigroup S] [nonEmpty : Nonempty S] :
SemigroupHom (groGroupHom (nonEmpty := nonEmpty)) :=
{
  hom_prop := groGroupHomIsSemigroupHom S
}

def rightSetShift
{S : Type*} [Semigroup S]
(F : Set S) (s : S) :
Set S :=
(fun (t : S) ↦ t * s) '' F

/-- The image of `S` under `groGroupHom` generates `groGroup S` -/
theorem imageOfSIsThickInGroGroup
(S : Type*) [CommSemigroup S] [Nonempty S] :
∀ (F : Set (groGroup S)), F.Finite →
  ∃ (s : S), rightSetShift F (groGroupHom s) ⊆ imageOfSemiInGG :=
  by sorry

/-- Necessary condition for image of two elements of `S`
to be equal under `groGroupHom` -/
theorem groGroupHomIncidenceCondition
{S : Type*} [CommSemigroup S] [Nonempty S] {s t : S} :
groGroupHom s = groGroupHom t ↔ ∃ (r : S), s * r = t * r :=
by sorry

/- The only reason to state the following theorem is to have it match
how we've written it in the paper.  But curiously, I cannot
prove theGrothendieckGroupExists as it is stated now, because note
that the theorem is a function of a universe level metavariable for G.
Of course, I want to use G := groGroup S, but in the case that u_2,
the universe level metavariable for G, is smaller than that of u_1,
the metavariable for S, I cannot use groGroup S.  And, in fact, there
likely is not a ``smaller complexity'' such group...!  So, as stated
I don't believe that Lean will allow us to verify theGrothendieckGroupExists.
-/
/-- The Grothendieck group of a semigroup and its basic properties -/
theorem theGrothendieckGroupExists
{S : Type*} [CommSemigroup S] [Nonempty S] :
∃ (G : Type*) (_ : CommGroup G), ∃ (i : S → G),
(∀ (s t : S), i (s * t) = (i s) * (i t))
∧
(∀ (F : Set G), F.Finite → ∃ (s : S), rightSetShift F (i s) ⊆ i '' Set.univ)
∧
(∀ (s t : S), i s = i t ↔ ∃ (r : S), r * s = r * t) :=
by sorry


/-- If `S` acts surjectively on `X` and `groGroupHom s = groGroupHom t`, then
`s` and `t` act in the same way on `X` -/
theorem surjectiveActionsFactorThroughGroGroupHom
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hSurject : isSurjectiveSystem dSystem)
{s t : S} :
groGroupHom s = groGroupHom t → dSystem.map s = dSystem.map t :=
by
  intro homsEqual
  obtain ⟨r, hr⟩ := groGroupHomIncidenceCondition.mp homsEqual
  ext x
  obtain ⟨y, hy⟩ := hSurject r x
  calc
    dSystem.map s x = dSystem.map s (dSystem.map r y) := by rw [← hy]
    _ = dSystem.map (s * r) y := by rw [dSystem.mapMult]
    _ = dSystem.map (t * r) y := by rw [← hr]
    _ = dSystem.map t (dSystem.map r y) := by rw [dSystem.mapMult]
    _ = dSystem.map t x := by rw [hy]


/-- If `S` acts by homeomorphisms, `groGroupDynamicalSystem` is the
dynamical system gotten by defining the action of `groGroup S`
on `X` in the natural way, possible by `surjectiveActionsFactorThroughGroGroupHom` -/
def groGroupDynamicalSystem
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hHomeo : isHomeoSystem dSystem) :
DynamicalSystem (groGroup S) X :=
by sorry


/-- If `S` acts by homeomorphisms, `DynamicalSystem S X` is the same as
the `homDynamicalSystem` of `groGroupDynamicalSystem` via `groGroupHom` -/
theorem homDSofGroGroupDSIsOriginalSystem
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hHomeo : isHomeoSystem dSystem) :
dSystem = homDynamicalSystem (groGroupHom) (groGroupDynamicalSystem hHomeo) :=
by sorry

/-- If `S` acts by homeomorphisms, then `RP` for the original action is the
same as `RP` for the extended action, `groGroupDynamicalSystem` -/
theorem extendedActionRPisActionRP
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hHomeo : isHomeoSystem dSystem) :
RP dSystem = RP (groGroupDynamicalSystem hHomeo) :=
by sorry


def natExtSet
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
Set ((groGroup S) → X) :=
{ φ : (groGroup S) → X | ∀ (g : groGroup S) (s : S), φ ((groGroupHom s) * g) = dSystem.map s (φ g)}

theorem natExtSetIsCompact
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
IsCompact (natExtSet dSystem) :=
by sorry

instance
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} :
CompactSpace ↑(natExtSet dSystem) := isCompact_iff_compactSpace.mp (natExtSetIsCompact dSystem)

theorem natExtSetIsNonempty
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) {hSurject : isSurjectiveSystem dSystem} :
Set.Nonempty (natExtSet dSystem) :=
by sorry

theorem natExtSetIsNonemptyInstance
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hSurject : isSurjectiveSystem dSystem) :
Nonempty ↑(natExtSet dSystem) := by sorry

def natExtGroSystem
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hSurject : isSurjectiveSystem dSystem) :
letI : Nonempty ↑(natExtSet dSystem) := natExtSetIsNonemptyInstance (hSurject := hSurject)
DynamicalSystem (groGroup S) (natExtSet dSystem) :=
by sorry

def natExtSystem
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hSurject : isSurjectiveSystem dSystem) :
letI : Nonempty ↑(natExtSet dSystem) := natExtSetIsNonemptyInstance (hSurject := hSurject)
DynamicalSystem S (natExtSet dSystem) :=
by sorry

def natExtFactorMap
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
(natExtSet dSystem) → X := fun (φ : natExtSet dSystem) ↦ φ.1 1

theorem natExtFactorMapIsFactorMap
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hSurject : isSurjectiveSystem dSystem) :
letI : Nonempty ↑(natExtSet dSystem) := natExtSetIsNonemptyInstance (hSurject := hSurject)
isFactorMap (natExtSystem hSurject) dSystem (natExtFactorMap dSystem) :=
by sorry


theorem natExtUniversalProperty
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hSurject : isSurjectiveSystem dSystem) :
letI : Nonempty ↑(natExtSet dSystem) := natExtSetIsNonemptyInstance (hSurject := hSurject)
∀ (V : Type*) [TopologicalSpace V] [CompactSpace V] [T2Space V] [Nonempty V],
∀ (dSystemV : DynamicalSystem S V),
∀ (ρ : V → X) (ρIsFactor : isFactorMap dSystemV dSystem ρ) (hHomeoV : isHomeoSystem dSystemV),
∃ (ξ : V → natExtSet dSystem) (ξIsFactor : isFactorMap dSystemV (natExtSystem hSurject) ξ),
ρ = (natExtFactorMap dSystem) ∘ ξ := by sorry


theorem natExtFactorMapIsIsomIfHomeoAction
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hHomeo : isHomeoSystem dSystem) :
letI : Nonempty ↑(natExtSet dSystem) :=
  natExtSetIsNonemptyInstance (hSurject := homeoSystemIsSurjectiveSystem hHomeo)
isIsomorphism (natExtSystem (homeoSystemIsSurjectiveSystem hHomeo)) dSystem (natExtFactorMap dSystem) :=
by sorry


theorem natExtMinimalIffSystemIsMinimal
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hSurject : isSurjectiveSystem dSystem) :
letI : Nonempty ↑(natExtSet dSystem) :=   natExtSetIsNonemptyInstance (hSurject := hSurject)
isMinimalSystem dSystem ↔ isMinimalSystem (natExtSystem hSurject) :=
by sorry

-- DGG: This is supposed to be Corollary 6.8.
-- DGG: Not sure how to formulate this in Lean.  Probably not important.
-- theorem natExtForMinCommutativeActions
-- {S} [CommSemigroup S] [Nonempty S]
-- {X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
-- {dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :

theorem pullBackOfRPThruNatExtFactorIsRP
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :
letI : Nonempty ↑(natExtSet dSystem) :=
  natExtSetIsNonemptyInstance (hSurject := minimalCommActionIsSurjective hMin)
Set.preimage (Prod.map (natExtFactorMap dSystem) (natExtFactorMap dSystem)) (RP dSystem) =
  RP (natExtSystem (minimalCommActionIsSurjective hMin)) :=
by sorry
