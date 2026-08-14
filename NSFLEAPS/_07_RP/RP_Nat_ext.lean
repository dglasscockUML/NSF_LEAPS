import NSFLEAPS._07_RP.RP_Defs

/-- When `X` is both a minimal S and T system and actions commute, `RP_S = RP_T` -/
theorem forTwoMinCommActionsRPsAreSame
{S} [CommSemigroup S] [Nonempty S]
{T} [CommSemigroup T] [Nonempty T]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystemS : DynamicalSystem S X} (hMin : isMinimalSystem dSystemS)
{dSystemT : DynamicalSystem T X} (hMinT : isMinimalSystem dSystemT)
(hCommActions : ∀ (s : S) (t : T),
  (dSystemS.map s) ∘ (dSystemT.map t) = (dSystemT.map t) ∘ (dSystemS.map s)) :
RP dSystemS = RP dSystemT := by sorry

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


/- Example use of calc
  have qxx : qx = x :=
    calc
      qx = q_px := by unfold q_px ; rw [hpFix]
      _ = qp_x := by unfold q_px ; rw [←(ultraAction dSystem).mapMult]
      _ = ux := by unfold qp_x ; rw [qpu]
      _ = u_px := by unfold ux ; unfold u_px ; rw [hpFix]
      _ = up_x := by unfold u_px ; rw [←(ultraAction dSystem).mapMult]
      _ = px := by unfold up_x ; rw [upp]
      _ = x := by unfold px ; rw [hpFix]

-/

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
