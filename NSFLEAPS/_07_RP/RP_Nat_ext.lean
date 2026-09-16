import NSFLEAPS._07_RP.RP_Defs
import NSFLEAPS._01_Topology.TP_Cylinders
import Mathlib.Algebra.Group.WithOne.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer

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

/- `groGroup` is made reducible so that `groGroup S` and `Algebra.GrothendieckGroup (WithOne S)`
are interchangeable during type class synthesis.  This only adds an attribute; the definition
above is unchanged. -/
attribute [reducible] groGroup

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

/-- `Algebra.GrothendieckGroup.of`, viewed as a map from `WithOne S` into `groGroup S` -/
def groGroupOf
{S : Type*} [CommSemigroup S] [Nonempty S] :
WithOne S → groGroup S :=
Algebra.GrothendieckGroup.of

/-- `groGroupOf` is a monoid homomorphism -/
lemma groGroupOfMul
{S : Type*} [CommSemigroup S] [Nonempty S] (a b : WithOne S) :
groGroupOf (a * b) = (groGroupOf a) * (groGroupOf b) :=
map_mul Algebra.GrothendieckGroup.of a b

/-- `groGroupHom` is the restriction of `groGroupOf` to `S` -/
lemma groGroupHomEqOf
{S : Type*} [CommSemigroup S] [Nonempty S] (s : S) :
groGroupHom s = groGroupOf (s : WithOne S) := rfl

/-- `groGroupOf` written using `Localization.mk` -/
lemma groGroupOfEqMk
{S : Type*} [CommSemigroup S] [Nonempty S] (a : WithOne S) :
groGroupOf a = Localization.mk a 1 :=
(Localization.mk_one_eq_monoidOf_mk a).symm

/-- Case analysis on `WithOne S` -/
lemma withOneCases
{α : Type*} (u : WithOne α) :
u = 1 ∨ ∃ a : α, u = (a : WithOne α) :=
WithOne.cases_on u (Or.inl rfl) (fun a => Or.inr ⟨a, rfl⟩)

/-- The map `groGroupHom` is a semigroup homomorphism -/
theorem groGroupHomIsSemigroupHom
(S : Type*) [CommSemigroup S] [Nonempty S] :
∀ (s t : S), groGroupHom (s * t) = (groGroupHom s) * (groGroupHom t) := by
  intro s t
  rw [groGroupHomEqOf, groGroupHomEqOf, groGroupHomEqOf, WithOne.coe_mul, groGroupOfMul]

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

/-- Necessary condition for image of two elements of `S`
to be equal under `groGroupHom` -/
theorem groGroupHomIncidenceCondition
{S : Type*} [CommSemigroup S] [Nonempty S] {s t : S} :
groGroupHom s = groGroupHom t ↔ ∃ (r : S), s * r = t * r := by
  have hkey : groGroupHom s = groGroupHom t ↔
      ∃ c : (⊤ : Submonoid (WithOne S)),
        (c : WithOne S) * (s : WithOne S) = (c : WithOne S) * (t : WithOne S) :=
    Submonoid.LocalizationMap.eq_iff_exists
      (Localization.monoidOf (⊤ : Submonoid (WithOne S)))
  rw [hkey]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨r₀⟩ := ‹Nonempty S›
    obtain ⟨cv, hcv⟩ := c
    have hc' : cv * (s : WithOne S) = cv * (t : WithOne S) := hc
    rcases withOneCases cv with rfl | ⟨a, rfl⟩
    · rw [one_mul, one_mul, WithOne.coe_inj] at hc'
      exact ⟨r₀, by rw [hc']⟩
    · rw [← WithOne.coe_mul, ← WithOne.coe_mul, WithOne.coe_inj] at hc'
      exact ⟨a, by rw [mul_comm s a, mul_comm t a]; exact hc'⟩
  · rintro ⟨r, hr⟩
    refine ⟨⟨(r : WithOne S), Submonoid.mem_top _⟩, ?_⟩
    change (r : WithOne S) * (s : WithOne S) = (r : WithOne S) * (t : WithOne S)
    rw [← WithOne.coe_mul, ← WithOne.coe_mul, WithOne.coe_inj, mul_comm r s, mul_comm r t]
    exact hr

/-- Every element of `groGroup S` is a quotient of two elements of `WithOne S` -/
lemma groGroupIsQuotient
{S : Type*} [CommSemigroup S] [Nonempty S] (g : groGroup S) :
∃ a c : WithOne S, g = groGroupOf a * (groGroupOf c)⁻¹ := by
  have key : ∀ x : Algebra.GrothendieckGroup (WithOne S),
      ∃ a c : WithOne S, x = Localization.mk a 1 * (Localization.mk c 1)⁻¹ := by
    intro x
    induction x using Localization.ind with
    | _ y =>
      obtain ⟨a, c⟩ := y
      refine ⟨a, (c : WithOne S), ?_⟩
      rw [Algebra.GrothendieckGroup.inv_mk, Localization.mk_mul]
      simp
  obtain ⟨a, c, hac⟩ := key g
  refine ⟨a, c, ?_⟩
  rw [groGroupOfEqMk, groGroupOfEqMk]
  exact hac

/-- Multiplying an element of `WithOne S` by an element of `S` lands in the image of `S` -/
lemma withOneMulCoe
{S : Type*} [CommSemigroup S] (u : WithOne S) (r : S) :
∃ b : S, (b : WithOne S) = u * (r : WithOne S) := by
  rcases withOneCases u with rfl | ⟨a, rfl⟩
  · exact ⟨r, by rw [one_mul]⟩
  · exact ⟨a * r, by rw [WithOne.coe_mul]⟩

/-- The image of `S` in `groGroup S` is closed under right multiplication by `groGroupHom` -/
lemma imageOfSemiInGGMulSelf
{S : Type*} [CommSemigroup S] [Nonempty S] {g : groGroup S}
(hg : g ∈ imageOfSemiInGG) (b : S) :
g * groGroupHom b ∈ imageOfSemiInGG := by
  obtain ⟨a, -, rfl⟩ := hg
  exact ⟨a * b, Set.mem_univ _, groGroupHomIsSemigroupHom S a b⟩

/-- Every single element of `groGroup S` can be shifted into the image of `S`.
This is the one-element case of `imageOfSIsThickInGroGroup`. -/
lemma existsShiftIntoImageOfSemiInGG
{S : Type*} [CommSemigroup S] [Nonempty S] (g : groGroup S) :
∃ b : S, g * groGroupHom b ∈ imageOfSemiInGG := by
  obtain ⟨r₀⟩ := ‹Nonempty S›
  obtain ⟨a, c, rfl⟩ := groGroupIsQuotient g
  obtain ⟨b, hb⟩ := withOneMulCoe c r₀
  obtain ⟨u, hu⟩ := withOneMulCoe a r₀
  refine ⟨b, u, Set.mem_univ _, ?_⟩
  rw [groGroupHomEqOf, groGroupHomEqOf, hb, hu, groGroupOfMul, groGroupOfMul,
    mul_assoc, ← mul_assoc (groGroupOf c)⁻¹, inv_mul_cancel, one_mul]

/-- The image of `S` under `groGroupHom` generates `groGroup S` -/
theorem imageOfSIsThickInGroGroup
(S : Type*) [CommSemigroup S] [Nonempty S] :
∀ (F : Set (groGroup S)), F.Finite →
  ∃ (s : S), rightSetShift F (groGroupHom s) ⊆ imageOfSemiInGG := by
  intro F hF
  induction F, hF using Set.Finite.induction_on with
  | empty =>
    obtain ⟨r₀⟩ := ‹Nonempty S›
    exact ⟨r₀, by simp [rightSetShift]⟩
  | @insert g F' hgF hF' ih =>
    obtain ⟨s', hs'⟩ := ih
    obtain ⟨b, hb⟩ := existsShiftIntoImageOfSemiInGG (g * groGroupHom s')
    refine ⟨s' * b, ?_⟩
    rintro x ⟨f, hf, rfl⟩
    change f * groGroupHom (s' * b) ∈ imageOfSemiInGG
    have hrw : f * groGroupHom (s' * b) = (f * groGroupHom s') * groGroupHom b := by
      rw [groGroupHomIsSemigroupHom, mul_assoc]
    rw [hrw]
    rcases hf with hf | hf
    · rw [hf]; exact hb
    · exact imageOfSemiInGGMulSelf (hs' ⟨f, hf, rfl⟩) b

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


/-! ### Theorem 6.3: the action of the Grothendieck group

When `S` acts by homeomorphisms, the maps `f_s` all commute, so the subgroup of `X ≃ₜ X` that
they generate is commutative.  The universal property of the Grothendieck group then extends
the action of `S` to an action of `groGroup S`, which is what the paper constructs by hand.
-/

/-- When `S` acts by homeomorphisms, the homeomorphism of `X` given by `s` -/
noncomputable def actionHomeo
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hHomeo : isHomeoSystem dSystem) (s : S) :
X ≃ₜ X :=
IsHomeomorph.homeomorph (dSystem.map s) (hHomeo s)

@[simp] lemma actionHomeoApply
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hHomeo : isHomeoSystem dSystem) (s : S) (x : X) :
actionHomeo hHomeo s x = dSystem.map s x := rfl

/-- `actionHomeo` turns multiplication in `S` into composition of homeomorphisms -/
lemma actionHomeoMul
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hHomeo : isHomeoSystem dSystem) (s t : S) :
actionHomeo hHomeo (s * t) = actionHomeo hHomeo s * actionHomeo hHomeo t :=
Homeomorph.ext (fun x ↦ dSystem.mapMult s t x)

/-- The subgroup of `X ≃ₜ X` generated by the action of `S` -/
noncomputable def actionSubgroup
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hHomeo : isHomeoSystem dSystem) :
Subgroup (X ≃ₜ X) :=
Subgroup.closure (Set.range (actionHomeo hHomeo))

/-- The generators of `actionSubgroup` commute, because `S` is commutative -/
lemma actionSubgroupGensComm
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hHomeo : isHomeoSystem dSystem) :
∀ f ∈ Set.range (actionHomeo hHomeo), ∀ g ∈ Set.range (actionHomeo hHomeo), f * g = g * f := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
  rw [← actionHomeoMul, ← actionHomeoMul, mul_comm]

open scoped IsMulCommutative in
/-- Hence `actionSubgroup` is a commutative group -/
noncomputable instance actionSubgroupCommGroup
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hHomeo : isHomeoSystem dSystem) :
CommGroup ↥(actionSubgroup hHomeo) :=
  have : IsMulCommutative ↥(actionSubgroup hHomeo) :=
    Subgroup.isMulCommutative_closure (actionSubgroupGensComm hHomeo)
  inferInstance

/-- `actionHomeo`, viewed as a semigroup homomorphism into `actionSubgroup` -/
noncomputable def actionMulHom
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hHomeo : isHomeoSystem dSystem) :
S →ₙ* ↥(actionSubgroup hHomeo) :=
{
  toFun := fun s ↦ ⟨actionHomeo hHomeo s, Subgroup.subset_closure ⟨s, rfl⟩⟩
  map_mul' := fun s t ↦ Subtype.ext (actionHomeoMul hHomeo s t)
}

/-- The extension of the action of `S` to `groGroup S`, via the universal property
of the Grothendieck group -/
noncomputable def groGroupHomeoHom
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hHomeo : isHomeoSystem dSystem) :
groGroup S →* ↥(actionSubgroup hHomeo) :=
Algebra.GrothendieckGroup.lift (WithOne.lift (actionMulHom hHomeo))

/-- The extended action restricts to the original action along `groGroupHom` -/
lemma groGroupHomeoHomApplyHom
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hHomeo : isHomeoSystem dSystem) (s : S) :
groGroupHomeoHom hHomeo (groGroupHom s) = actionMulHom hHomeo s := by
  have h : (Algebra.GrothendieckGroup.lift (WithOne.lift (actionMulHom hHomeo))).comp
      Algebra.GrothendieckGroup.of = WithOne.lift (actionMulHom hHomeo) :=
    Equiv.symm_apply_apply Algebra.GrothendieckGroup.lift (WithOne.lift (actionMulHom hHomeo))
  have h2 := DFunLike.congr_fun h ((s : WithOne S))
  exact h2.trans (WithOne.lift_coe (actionMulHom hHomeo) s)

/-- If `S` acts by homeomorphisms, `groGroupDynamicalSystem` is the
dynamical system gotten by defining the action of `groGroup S`
on `X` in the natural way, possible by `surjectiveActionsFactorThroughGroGroupHom` -/
noncomputable def groGroupDynamicalSystem
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hHomeo : isHomeoSystem dSystem) :
DynamicalSystem (groGroup S) X :=
{
  map := fun g x ↦ ((groGroupHomeoHom hHomeo g : X ≃ₜ X)) x
  mapMult := by
    intro g₁ g₂ x
    simp only [map_mul, Subgroup.coe_mul, Homeomorph.mul_apply]
  mapCont := fun g ↦ (groGroupHomeoHom hHomeo g : X ≃ₜ X).continuous
}

/-- Two dynamical systems with the same action map are equal -/
lemma dynamicalSystemEq
{S} [Semigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{d₁ d₂ : DynamicalSystem S X} (h : d₁.map = d₂.map) :
d₁ = d₂ := by
  obtain ⟨m₁, hm₁, hc₁⟩ := d₁
  obtain ⟨m₂, hm₂, hc₂⟩ := d₂
  subst h
  rfl

/-- If `S` acts by homeomorphisms, `DynamicalSystem S X` is the same as
the `homDynamicalSystem` of `groGroupDynamicalSystem` via `groGroupHom` -/
theorem homDSofGroGroupDSIsOriginalSystem
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hHomeo : isHomeoSystem dSystem) :
dSystem = homDynamicalSystem (groGroupHom) (groGroupDynamicalSystem hHomeo) := by
  refine dynamicalSystemEq ?_
  funext s x
  change dSystem.map s x = ((groGroupHomeoHom hHomeo (groGroupHom s) : X ≃ₜ X)) x
  rw [groGroupHomeoHomApplyHom]
  rfl

/-- The extended action restricted along `groGroupHom` is the original action -/
lemma groGroupDynamicalSystemApplyHom
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hHomeo : isHomeoSystem dSystem) (s : S) (x : X) :
(groGroupDynamicalSystem hHomeo).map (groGroupHom s) x = dSystem.map s x := by
  change ((groGroupHomeoHom hHomeo (groGroupHom s) : X ≃ₜ X)) x = dSystem.map s x
  rw [groGroupHomeoHomApplyHom]
  rfl

/-- The `S`-orbit of a point is contained in its `groGroup S`-orbit -/
lemma orbitSubsetGroGroupOrbit
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hHomeo : isHomeoSystem dSystem) (x : X) :
orbit dSystem x ⊆ orbit (groGroupDynamicalSystem hHomeo) x := by
  rintro z ⟨s, rfl⟩
  exact ⟨groGroupHom s, groGroupDynamicalSystemApplyHom hHomeo s x⟩

/-- If the `S`-action is minimal then so is the extended `groGroup S`-action -/
lemma groGroupSystemMinimalOfMinimal
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hHomeo : isHomeoSystem dSystem)
(hMin : isMinimalSystem dSystem) :
isMinimalSystem (groGroupDynamicalSystem hHomeo) := by
  rw [minimalIffDenseOrbits]
  intro x
  exact Dense.mono (orbitSubsetGroGroupOrbit hHomeo x)
    ((minimalIffDenseOrbits dSystem).mp hMin x)

/-- The actions of `S` and of `groGroup S` on `X` commute -/
lemma groGroupActionCommutes
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hHomeo : isHomeoSystem dSystem) :
∀ (s : S) (g : groGroup S),
  (dSystem.map s) ∘ ((groGroupDynamicalSystem hHomeo).map g)
    = ((groGroupDynamicalSystem hHomeo).map g) ∘ (dSystem.map s) := by
  intro s g
  funext x
  change dSystem.map s ((groGroupDynamicalSystem hHomeo).map g x)
      = (groGroupDynamicalSystem hHomeo).map g (dSystem.map s x)
  rw [← groGroupDynamicalSystemApplyHom hHomeo s ((groGroupDynamicalSystem hHomeo).map g x),
    ← groGroupDynamicalSystemApplyHom hHomeo s x,
    ← (groGroupDynamicalSystem hHomeo).mapMult,
    ← (groGroupDynamicalSystem hHomeo).mapMult, mul_comm]

/-- Unconditionally, `RP` for the original action is contained in `RP` for the extended
action: the `groGroup S`-orbit of a set contains its `S`-orbit. -/
theorem RPSubsetExtendedActionRP
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hHomeo : isHomeoSystem dSystem) :
RP dSystem ⊆ RP (groGroupDynamicalSystem hHomeo) := by
  intro z hz
  simp only [RP, Set.mem_iInter] at hz ⊢
  intro α hα
  refine closure_mono ?_ (hz α hα)
  intro w hw
  simp only [inverseSetOrbit, Set.mem_iUnion, Set.mem_preimage] at hw ⊢
  obtain ⟨s, hs⟩ := hw
  refine ⟨groGroupHom s, ?_⟩
  have h1 : (diagDynamicalSystem (groGroupDynamicalSystem hHomeo)
      (groGroupDynamicalSystem hHomeo)).map (groGroupHom s) w
      = (diagDynamicalSystem dSystem dSystem).map s w := by
    change ((groGroupDynamicalSystem hHomeo).map (groGroupHom s) w.1,
        (groGroupDynamicalSystem hHomeo).map (groGroupHom s) w.2)
      = (dSystem.map s w.1, dSystem.map s w.2)
    rw [groGroupDynamicalSystemApplyHom, groGroupDynamicalSystemApplyHom]
  rw [h1]
  exact hs

/-- If `S` acts by homeomorphisms, then `RP` for the original action is the
same as `RP` for the extended action, `groGroupDynamicalSystem`.

DGG/CLAUDE: **the hypothesis `hMin` was added.**  This statement is Corollary 6.4 of the
paper, whose proof reads "Apply Theorem D, noting that `S` and `Gr(S)` are commutative
semigroups whose actions commute and are minimal".  Theorem D is
`forTwoMinCommActionsRPsAreSame`, which requires *both* actions to be minimal, so minimality
of the `S`-system is genuinely needed and is indeed assumed in Corollary 6.4.  Without it only
the inclusion `RPSubsetExtendedActionRP` above is available: the reverse inclusion would
require replacing an arbitrary `g = i(t)i(s)⁻¹ ∈ Gr(S)` by an element of `S`, which is exactly
what minimality buys via Theorem D. -/
theorem extendedActionRPisActionRP
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hHomeo : isHomeoSystem dSystem)
(hMin : isMinimalSystem dSystem) :
RP dSystem = RP (groGroupDynamicalSystem hHomeo) :=
forTwoMinCommActionsRPsAreSame hMin (groGroupSystemMinimalOfMinimal hHomeo hMin)
  (groGroupActionCommutes hHomeo)


def natExtSet
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
Set ((groGroup S) → X) :=
{ φ : (groGroup S) → X | ∀ (g : groGroup S) (s : S), φ ((groGroupHom s) * g) = dSystem.map s (φ g)}

/-- `natExtSet` is closed: it is cut out by continuous equations -/
theorem natExtSetIsClosed
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
IsClosed (natExtSet dSystem) := by
  have heq : natExtSet dSystem = ⋂ (g : groGroup S), ⋂ (s : S),
      {φ : groGroup S → X | φ ((groGroupHom s) * g) = dSystem.map s (φ g)} := by
    ext φ
    simp only [natExtSet, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [heq]
  refine isClosed_iInter fun g ↦ isClosed_iInter fun s ↦ ?_
  exact isClosed_eq (continuous_apply _) ((dSystem.mapCont s).comp (continuous_apply g))

theorem natExtSetIsCompact
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
IsCompact (natExtSet dSystem) :=
(natExtSetIsClosed dSystem).isCompact

instance
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} :
CompactSpace ↑(natExtSet dSystem) := isCompact_iff_compactSpace.mp (natExtSetIsCompact dSystem)

/-! ### Theorem 6.5: the natural extension is non-empty and `natExtFactorMap` is onto -/

/-- The explicit construction in the proof of Theorem 6.5: for a *finite* set `F` of
constraints there is a function satisfying them whose value at the identity is any
prescribed `x`.

Write `h = i(s₀)⁻¹`, where `s₀` is supplied by `imageOfSIsThickInGroGroup`, so that every
`g ∈ F` is of the form `i(r)h`, and pick `y` with `s₀ y = x`.  The function is
`φ(g) = r y` if `g = i(r)h`, and `y` otherwise.  Note that `g = i(r)h` is the same as
`g * i(s₀) = i(r)`, which is how the condition is phrased below; stating it this way avoids
the case analysis of the paper for `φ(h) = y`, which is never actually needed. -/
theorem natExtSetFiniteApprox
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hSurject : isSurjectiveSystem dSystem)
(x : X) (F : Set (groGroup S)) (hF : F.Finite) :
∃ φ : groGroup S → X,
  (∀ g ∈ F, ∀ s : S, φ (groGroupHom s * g) = dSystem.map s (φ g)) ∧ φ 1 = x := by
  classical
  obtain ⟨s₀, hs₀⟩ := imageOfSIsThickInGroGroup S F hF
  obtain ⟨y, hy⟩ := hSurject s₀ x
  set φ : groGroup S → X := fun g ↦
    if hg : ∃ t : S, g * groGroupHom s₀ = groGroupHom t then dSystem.map hg.choose y else y
    with hφ
  have key : ∀ (g : groGroup S) (t : S), g * groGroupHom s₀ = groGroupHom t →
      φ g = dSystem.map t y := by
    intro g t hgt
    have hex : ∃ t : S, g * groGroupHom s₀ = groGroupHom t := ⟨t, hgt⟩
    have h1 : groGroupHom hex.choose = groGroupHom t := by
      rw [← hex.choose_spec, hgt]
    simp only [hφ, hex, ↓reduceDIte]
    rw [surjectiveActionsFactorThroughGroGroupHom hSurject h1]
  refine ⟨φ, ?_, ?_⟩
  · intro g hg u
    obtain ⟨r, -, hr⟩ := hs₀ ⟨g, hg, rfl⟩
    have hr' : groGroupHom r = g * groGroupHom s₀ := hr
    have h2 : (groGroupHom u * g) * groGroupHom s₀ = groGroupHom (u * r) := by
      rw [mul_assoc, ← hr', groGroupHomIsSemigroupHom]
    rw [key _ _ h2, key g r hr'.symm, dSystem.mapMult]
  · rw [key 1 s₀ (one_mul _), hy]

/-- Theorem 6.5: every point of `X` is the value at the identity of some element of
`natExtSet`.  The finitely many constraints of `natExtSetFiniteApprox` cut out closed
subsets of the compact space `groGroup S → X` with the finite intersection property. -/
theorem natExtSetExistsWithValue
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hSurject : isSurjectiveSystem dSystem) (x : X) :
∃ φ ∈ natExtSet dSystem, φ 1 = x := by
  classical
  set Z : groGroup S → Set (groGroup S → X) := fun g ↦
    {φ | (∀ s : S, φ (groGroupHom s * g) = dSystem.map s (φ g)) ∧ φ 1 = x} with hZ
  have hZclosed : ∀ g, IsClosed (Z g) := by
    intro g
    have h1 : Z g =
        (⋂ s : S, {φ : groGroup S → X | φ (groGroupHom s * g) = dSystem.map s (φ g)})
          ∩ {φ : groGroup S → X | φ 1 = x} := by
      ext φ
      simp only [hZ, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [h1]
    refine IsClosed.inter (isClosed_iInter fun s ↦ ?_)
      (isClosed_eq (continuous_apply 1) continuous_const)
    exact isClosed_eq (continuous_apply _) ((dSystem.mapCont s).comp (continuous_apply g))
  have hZne : ∀ u : Finset (groGroup S), (⋂ g ∈ u, Z g).Nonempty := by
    intro u
    obtain ⟨φ, hφ1, hφ2⟩ := natExtSetFiniteApprox hSurject x (↑u) u.finite_toSet
    refine ⟨φ, ?_⟩
    simp only [Set.mem_iInter]
    intro g hg
    exact ⟨fun s ↦ hφ1 g hg s, hφ2⟩
  have hall : (⋂ g, Z g).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    obtain ⟨u, hu⟩ := isCompact_univ.elim_finite_subfamily_closed Z hZclosed
      (by simp [hcon])
    obtain ⟨φ, hφ⟩ := hZne u
    exact (Set.disjoint_left.mp hu (Set.mem_univ φ)) hφ
  obtain ⟨φ, hφ⟩ := hall
  simp only [Set.mem_iInter] at hφ
  exact ⟨φ, fun g s ↦ (hφ g).1 s, (hφ 1).2⟩

theorem natExtSetIsNonempty
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) {hSurject : isSurjectiveSystem dSystem} :
Set.Nonempty (natExtSet dSystem) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨φ, hφ, -⟩ := natExtSetExistsWithValue hSurject x
  exact ⟨φ, hφ⟩

theorem natExtSetIsNonemptyInstance
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hSurject : isSurjectiveSystem dSystem) :
Nonempty ↑(natExtSet dSystem) :=
Set.Nonempty.to_subtype (natExtSetIsNonempty dSystem (hSurject := hSurject))

/-- Right translation by `g` preserves `natExtSet` -/
lemma natExtSetTranslateMem
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (g : groGroup S) (φ : natExtSet dSystem) :
(fun h ↦ φ.1 (h * g)) ∈ natExtSet dSystem := by
  intro g' s
  change φ.1 ((groGroupHom s * g') * g) = dSystem.map s (φ.1 (g' * g))
  rw [mul_assoc]
  exact φ.2 (g' * g) s

def natExtGroSystem
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hSurject : isSurjectiveSystem dSystem) :
letI : Nonempty ↑(natExtSet dSystem) := natExtSetIsNonemptyInstance (hSurject := hSurject)
DynamicalSystem (groGroup S) (natExtSet dSystem) :=
letI : Nonempty ↑(natExtSet dSystem) := natExtSetIsNonemptyInstance (hSurject := hSurject)
{
  map := fun g φ ↦ ⟨fun h ↦ φ.1 (h * g), natExtSetTranslateMem g φ⟩
  mapMult := by
    intro g₁ g₂ φ
    apply Subtype.ext
    funext h
    exact congrArg φ.1 (by rw [mul_assoc])
  mapCont := by
    intro g
    apply Continuous.subtype_mk
    exact continuous_pi fun h ↦ (continuous_apply (h * g)).comp continuous_subtype_val
}

def natExtSystem
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hSurject : isSurjectiveSystem dSystem) :
letI : Nonempty ↑(natExtSet dSystem) := natExtSetIsNonemptyInstance (hSurject := hSurject)
DynamicalSystem S (natExtSet dSystem) :=
letI : Nonempty ↑(natExtSet dSystem) := natExtSetIsNonemptyInstance (hSurject := hSurject)
homDynamicalSystem (groGroupHom) (natExtGroSystem hSurject)

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
isFactorMap (natExtSystem hSurject) dSystem (natExtFactorMap dSystem) := by
  have : Nonempty ↑(natExtSet dSystem) := natExtSetIsNonemptyInstance (hSurject := hSurject)
  refine ⟨(continuous_apply 1).comp continuous_subtype_val, ?_, ?_⟩
  · intro x
    obtain ⟨φ, hφ, hφ1⟩ := natExtSetExistsWithValue hSurject x
    exact ⟨⟨φ, hφ⟩, hφ1⟩
  · intro s
    funext φ
    change dSystem.map s (φ.1 1) = φ.1 (1 * groGroupHom s)
    have h := φ.2 1 s
    rw [mul_one] at h
    rw [one_mul, ← h]


/-- The extended `groGroup S`-action is again by homeomorphisms -/
lemma groGroupDynamicalSystemIsHomeo
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hHomeo : isHomeoSystem dSystem) :
isHomeoSystem (groGroupDynamicalSystem hHomeo) :=
fun g ↦ (groGroupHomeoHom hHomeo g : X ≃ₜ X).isHomeomorph

/-- The identity of `groGroup S` acts trivially -/
lemma groGroupDynamicalSystemOne
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hHomeo : isHomeoSystem dSystem) (x : X) :
(groGroupDynamicalSystem hHomeo).map 1 x = x := by
  change ((groGroupHomeoHom hHomeo 1 : X ≃ₜ X)) x = x
  rw [map_one]
  rfl

/-- Theorem 6.6: the natural extension is the smallest extension on which `S` acts by
homeomorphisms.  Given `ρ : V → X` with `S` acting on `V` by homeomorphisms, extend the
action of `S` on `V` to `groGroup S` and put `ξ v = fun g ↦ ρ (g v)`. -/
theorem natExtUniversalProperty
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hSurject : isSurjectiveSystem dSystem) :
letI : Nonempty ↑(natExtSet dSystem) := natExtSetIsNonemptyInstance (hSurject := hSurject)
∀ (V : Type*) [TopologicalSpace V] [CompactSpace V] [T2Space V] [Nonempty V],
∀ (dSystemV : DynamicalSystem S V),
∀ (ρ : V → X) (_ : isFactorMap dSystemV dSystem ρ) (_ : isHomeoSystem dSystemV),
∃ (ξ : V → natExtSet dSystem) (_ : isFactorMap dSystemV (natExtSystem hSurject) ξ),
ρ = (natExtFactorMap dSystem) ∘ ξ := by
  classical
  have : Nonempty ↑(natExtSet dSystem) := natExtSetIsNonemptyInstance (hSurject := hSurject)
  intro V _ _ _ _ dSystemV ρ ρIsFactor hHomeoV
  obtain ⟨hρcont, hρsurj, hρequiv⟩ := ρIsFactor
  have hρS : ∀ (s : S) (v : V), ρ (dSystemV.map s v) = dSystem.map s (ρ v) :=
    fun s v ↦ (congrFun (hρequiv s) v).symm
  set GV := groGroupDynamicalSystem hHomeoV with hGV
  -- `ξ v` lands in `natExtSet`
  have hξmem : ∀ v : V, (fun g ↦ ρ (GV.map g v)) ∈ natExtSet dSystem := by
    intro v g s
    change ρ (GV.map (groGroupHom s * g) v) = dSystem.map s (ρ (GV.map g v))
    rw [GV.mapMult, groGroupDynamicalSystemApplyHom, hρS]
  set ξ : V → natExtSet dSystem := fun v ↦ ⟨fun g ↦ ρ (GV.map g v), hξmem v⟩ with hξ
  have hξcont : Continuous ξ :=
    Continuous.subtype_mk (continuous_pi fun g ↦ hρcont.comp (GV.mapCont g)) _
  -- `ξ` has dense range, and its range is closed, so it is onto
  have hdense : Dense (Set.range ξ) := by
    rw [dense_iff_inter_open]
    rintro U hUopen ⟨φ, hφU⟩
    obtain ⟨U', hU'open, hU'eq⟩ := isOpen_induced_iff.mp hUopen
    subst hU'eq
    have hU'nhds : U' ∈ nhds (φ.1) := hU'open.mem_nhds hφU
    rw [nhds_pi, Filter.mem_pi] at hU'nhds
    obtain ⟨I, hIfin, Wf, hWf, hWfU⟩ := hU'nhds
    obtain ⟨s₀, hs₀⟩ := imageOfSIsThickInGroGroup S I hIfin
    have hchoice : ∀ f : groGroup S, ∃ r : S,
        f ∈ I → groGroupHom r = f * groGroupHom s₀ := by
      intro f
      by_cases hf : f ∈ I
      · obtain ⟨r, -, hr⟩ := hs₀ ⟨f, hf, rfl⟩
        exact ⟨r, fun _ ↦ hr⟩
      · obtain ⟨r₀⟩ := ‹Nonempty S›
        exact ⟨r₀, fun h ↦ absurd h hf⟩
    choose sf hsf using hchoice
    set h₀ : groGroup S := (groGroupHom s₀)⁻¹ with hh₀
    have hfEq : ∀ f ∈ I, groGroupHom (sf f) * h₀ = f := by
      intro f hf
      rw [hsf f hf, hh₀, mul_assoc, mul_inv_cancel, mul_one]
    obtain ⟨w, hw⟩ := hρsurj (φ.1 h₀)
    obtain ⟨v, hv⟩ := (groGroupDynamicalSystemIsHomeo hHomeoV h₀).surjective w
    refine ⟨ξ v, ?_, ⟨v, rfl⟩⟩
    apply hWfU
    intro f hf
    have hfv : GV.map f v = dSystemV.map (sf f) (GV.map h₀ v) := by
      conv_lhs => rw [← hfEq f hf]
      rw [GV.mapMult, groGroupDynamicalSystemApplyHom]
    have hkey : (ξ v).1 f = φ.1 f := by
      change ρ (GV.map f v) = φ.1 f
      rw [hfv, hρS, hv, hw, ← φ.2 h₀ (sf f), hfEq f hf]
    rw [hkey]
    exact mem_of_mem_nhds (hWf f)
  have hξsurj : Function.Surjective ξ := by
    have hclosed : IsClosed (Set.range ξ) := (isCompact_range hξcont).isClosed
    have : Set.range ξ = Set.univ := by
      rw [← hclosed.closure_eq, hdense.closure_eq]
    exact Set.range_eq_univ.mp this
  refine ⟨ξ, ⟨hξcont, hξsurj, ?_⟩, ?_⟩
  · intro s
    funext v
    apply Subtype.ext
    funext g
    change ρ (GV.map (g * groGroupHom s) v) = ρ (GV.map g (dSystemV.map s v))
    rw [GV.mapMult, groGroupDynamicalSystemApplyHom]
  · funext v
    change ρ v = ρ (GV.map 1 v)
    rw [groGroupDynamicalSystemOne]


/-- Every value of an element of `natExtSet` is determined, up to the action of a single
element of `S`, by its value at the identity -/
lemma natExtSetValueDetermined
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (g : groGroup S) :
∃ (b r : S), ∀ χ : natExtSet dSystem,
  dSystem.map b (χ.1 g) = dSystem.map r (χ.1 1) := by
  obtain ⟨b, hb⟩ := existsShiftIntoImageOfSemiInGG g
  obtain ⟨r, -, hr⟩ := hb
  refine ⟨b, r, fun χ ↦ ?_⟩
  have h1 : χ.1 (groGroupHom b * g) = dSystem.map b (χ.1 g) := χ.2 g b
  have h2 : χ.1 (groGroupHom r * 1) = dSystem.map r (χ.1 1) := χ.2 1 r
  rw [mul_one] at h2
  rw [← h1, ← h2, mul_comm, ← hr]

/-- Theorem 6.6 (last part): if `S` acts by homeomorphisms then the natural extension is
already isomorphic to `X`.  Rather than going through the universal property, note directly
that `s₀ (φ g) = r (φ 1)` pins down `φ g` because `s₀` acts injectively. -/
theorem natExtFactorMapIsIsomIfHomeoAction
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hHomeo : isHomeoSystem dSystem) :
letI : Nonempty ↑(natExtSet dSystem) :=
  natExtSetIsNonemptyInstance (hSurject := homeoSystemIsSurjectiveSystem hHomeo)
isIsomorphism (natExtSystem (homeoSystemIsSurjectiveSystem hHomeo))
  dSystem (natExtFactorMap dSystem) := by
    have hSurject := homeoSystemIsSurjectiveSystem hHomeo
    have : Nonempty ↑(natExtSet dSystem) := natExtSetIsNonemptyInstance (hSurject := hSurject)
    obtain ⟨hcont, hsurj, hequiv⟩ := natExtFactorMapIsFactorMap hSurject
    refine ⟨?_, hequiv⟩
    rw [isHomeomorph_iff_continuous_isClosedMap_bijective]
    refine ⟨hcont, hcont.isClosedMap, ⟨?_, hsurj⟩⟩
    intro φ ψ hφψ
    apply Subtype.ext
    funext g
    obtain ⟨b, r, hbr⟩ := natExtSetValueDetermined (dSystem := dSystem) g
    have h3 : φ.1 1 = ψ.1 1 := hφψ
    have h4 : dSystem.map b (φ.1 g) = dSystem.map b (ψ.1 g) := by
      rw [hbr φ, hbr ψ, h3]
    exact (hHomeo b).injective h4


/-- Theorem 6.7: the natural extension is minimal exactly when the system is -/
theorem natExtMinimalIffSystemIsMinimal
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hSurject : isSurjectiveSystem dSystem) :
letI : Nonempty ↑(natExtSet dSystem) :=   natExtSetIsNonemptyInstance (hSurject := hSurject)
isMinimalSystem dSystem ↔ isMinimalSystem (natExtSystem hSurject) := by
  classical
  have : Nonempty ↑(natExtSet dSystem) := natExtSetIsNonemptyInstance (hSurject := hSurject)
  constructor
  · -- `X` minimal implies the natural extension is minimal
    intro hMin
    rw [minimalIffDenseOrbits]
    intro φ
    rw [dense_iff_inter_open]
    rintro U hUopen ⟨ψ, hψU⟩
    obtain ⟨U', hU'open, hU'eq⟩ := isOpen_induced_iff.mp hUopen
    subst hU'eq
    have hU'nhds : U' ∈ nhds (ψ.1) := hU'open.mem_nhds hψU
    rw [nhds_pi, Filter.mem_pi] at hU'nhds
    obtain ⟨I, hIfin, V, hV, hVU⟩ := hU'nhds
    -- shift the finitely many relevant coordinates into the image of `S`
    obtain ⟨s₀, hs₀⟩ := imageOfSIsThickInGroGroup S I hIfin
    have hchoice : ∀ f : groGroup S, ∃ r : S,
        f ∈ I → groGroupHom r = f * groGroupHom s₀ := by
      intro f
      by_cases hf : f ∈ I
      · obtain ⟨r, -, hr⟩ := hs₀ ⟨f, hf, rfl⟩
        exact ⟨r, fun _ ↦ hr⟩
      · obtain ⟨r₀⟩ := ‹Nonempty S›
        exact ⟨r₀, fun h ↦ absurd h hf⟩
    choose sf hsf using hchoice
    set h₀ : groGroup S := (groGroupHom s₀)⁻¹ with hh₀
    have hfEq : ∀ f ∈ I, groGroupHom (sf f) * h₀ = f := by
      intro f hf
      rw [hsf f hf, hh₀, mul_assoc, mul_inv_cancel, mul_one]
    -- the finitely many constraints define a non-empty open subset of `X`
    set Y : Set X := ⋂ f ∈ I, (dSystem.map (sf f)) ⁻¹' (interior (V f)) with hY
    have hYopen : IsOpen Y := by
      refine hIfin.isOpen_biInter fun f _ ↦ ?_
      exact isOpen_interior.preimage (dSystem.mapCont (sf f))
    have hYne : (ψ.1 h₀) ∈ Y := by
      simp only [hY, Set.mem_iInter, Set.mem_preimage]
      intro f hf
      have hkey : ψ.1 (groGroupHom (sf f) * h₀) = dSystem.map (sf f) (ψ.1 h₀) := ψ.2 h₀ (sf f)
      rw [hfEq f hf] at hkey
      rw [← hkey]
      exact mem_interior_iff_mem_nhds.mpr (hV f)
    -- minimality of `X` moves `φ h₀` into `Y`
    obtain ⟨t, ht⟩ := minimalImpliesNonemptySetVisits hMin (φ.1 h₀) hYopen ⟨_, hYne⟩
    simp only [visitTimeSet, Set.mem_preimage] at ht
    refine ⟨(natExtSystem hSurject).map t φ, ?_, ⟨t, rfl⟩⟩
    apply hVU
    intro f hf
    have hshift : f * groGroupHom t = groGroupHom (sf f * t) * h₀ := by
      rw [groGroupHomIsSemigroupHom, mul_assoc, mul_comm (groGroupHom t) h₀,
        ← mul_assoc, hfEq f hf]
    have hval : ((natExtSystem hSurject).map t φ).1 f = φ.1 (f * groGroupHom t) := rfl
    rw [hval, hshift, φ.2 h₀ (sf f * t), dSystem.mapMult]
    simp only [hY, Set.mem_iInter, Set.mem_preimage] at ht
    exact interior_subset (ht f hf)
  · -- the natural extension is a factor of which `X` is a factor
    intro hWMin
    exact factorOfMinimalIsMinimal hWMin
      ⟨natExtFactorMap dSystem, natExtFactorMapIsFactorMap hSurject⟩

/-- Corollary: for a minimal system over a commutative semigroup, the natural extension
`π : W → X` exists (Theorem 6.5), satisfies the universal property (Theorem 6.6), and is
itself minimal (Theorem 6.7).

The only thing to check is that the hypothesis `isSurjectiveSystem dSystem` of those three
results is met, which is `minimalCommActionIsSurjective`. -/
theorem natExtOfMinimalCommSystem
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :
let hSurject := minimalCommActionIsSurjective hMin
letI : Nonempty ↑(natExtSet dSystem) := natExtSetIsNonemptyInstance (hSurject := hSurject)
isFactorMap (natExtSystem hSurject) dSystem (natExtFactorMap dSystem) ∧
(∀ (V : Type*) [TopologicalSpace V] [CompactSpace V] [T2Space V] [Nonempty V],
  ∀ (dSystemV : DynamicalSystem S V),
  ∀ (ρ : V → X) (_ : isFactorMap dSystemV dSystem ρ) (_ : isHomeoSystem dSystemV),
  ∃ (ξ : V → natExtSet dSystem) (_ : isFactorMap dSystemV (natExtSystem hSurject) ξ),
  ρ = (natExtFactorMap dSystem) ∘ ξ) ∧
isMinimalSystem (natExtSystem hSurject) := by
  intro hSurject
  exact ⟨natExtFactorMapIsFactorMap hSurject, natExtUniversalProperty hSurject,
    (natExtMinimalIffSystemIsMinimal hSurject).mp hMin⟩

/-! ### Theorem 6.9

Theorem 6.9 has two halves: the equality `(π × π)⁻¹ RP_X = RP_W`
(`pullBackOfRPThruNatExtFactorIsRP`), and the resulting isomorphism `W / RP_W ≅ X / RP_X`
(`maxEquiFactorOfNatExtIsoMaxEquiFactor`).  For the second we first package "the quotient by
`RP`", that is, the largest equicontinuous factor of a minimal system.
-/

/-- Claim 1 in the proof of Theorem 6.9: two elements of the natural extension that are
regionally proximal at the identity are regionally proximal at every coordinate.

The point is that `b (φ g) = r (φ 1)` for a single pair `b, r ∈ S` independent of `φ`
(`natExtSetValueDetermined`), so `b (φ g, ψ g) = r (φ 1, ψ 1) ∈ RP` by invariance of `RP`,
and then Theorem 5.7 (`RPIsStrongSInvariant`) removes the `b`. -/
theorem natExtRPAtAllCoordinates
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem)
(φ ψ : natExtSet dSystem) (h : (φ.1 1, ψ.1 1) ∈ RP dSystem) (g : groGroup S) :
(φ.1 g, ψ.1 g) ∈ RP dSystem := by
  obtain ⟨b, r, hbr⟩ := natExtSetValueDetermined (dSystem := dSystem) g
  have hinv : (diagDynamicalSystem dSystem dSystem).map r (φ.1 1, ψ.1 1) ∈ RP dSystem :=
    RPInCommSemiIsInvariant dSystem r h
  have heq : (diagDynamicalSystem dSystem dSystem).map b (φ.1 g, ψ.1 g)
      = (diagDynamicalSystem dSystem dSystem).map r (φ.1 1, ψ.1 1) := by
    change (dSystem.map b (φ.1 g), dSystem.map b (ψ.1 g))
      = (dSystem.map r (φ.1 1), dSystem.map r (ψ.1 1))
    rw [hbr φ, hbr ψ]
  rw [(RPIsStrongSInvariant hMin).1]
  simp only [inverseSetOrbit, Set.mem_iUnion, Set.mem_preimage]
  exact ⟨b, heq ▸ hinv⟩

/-- The `groGroup S`-action on the natural extension is by surjections -/
lemma natExtGroSystemMapSurjective
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hSurject : isSurjectiveSystem dSystem) :
letI : Nonempty ↑(natExtSet dSystem) := natExtSetIsNonemptyInstance (hSurject := hSurject)
∀ g : groGroup S, Function.Surjective ((natExtGroSystem hSurject).map g) := by
  have : Nonempty ↑(natExtSet dSystem) := natExtSetIsNonemptyInstance (hSurject := hSurject)
  intro g ψ
  refine ⟨(natExtGroSystem hSurject).map g⁻¹ ψ, ?_⟩
  rw [← (natExtGroSystem hSurject).mapMult, mul_inv_cancel]
  exact Subtype.ext (funext fun k ↦ congrArg ψ.1 (mul_one k))

/-- Evaluation at any `h ∈ groGroup S` maps the natural extension onto `X`.  This is the
paper's observation that `π ∘ h` is surjective. -/
lemma natExtEvalSurjective
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hSurject : isSurjectiveSystem dSystem) (h : groGroup S) :
letI : Nonempty ↑(natExtSet dSystem) := natExtSetIsNonemptyInstance (hSurject := hSurject)
Function.Surjective (fun χ : ↑(natExtSet dSystem) ↦ χ.1 h) := by
  have : Nonempty ↑(natExtSet dSystem) := natExtSetIsNonemptyInstance (hSurject := hSurject)
  intro x
  obtain ⟨χ, hχ⟩ := (natExtFactorMapIsFactorMap hSurject).2.1 x
  obtain ⟨η, hη⟩ := natExtGroSystemMapSurjective hSurject h χ
  refine ⟨η, ?_⟩
  have h1 : χ.1 1 = η.1 h := by
    rw [← hη]
    exact congrArg η.1 (one_mul h)
  change η.1 h = x
  rw [← h1]
  exact hχ

/-- **Theorem 6.9**, first half: the regionally proximal relation of the natural extension is
the pullback along `π × π` of the regionally proximal relation of `X`.

The inclusion `RP_W ⊆ (π × π)⁻¹ RP_X` is the general fact `imageOfRPIsInRP` about factor maps.
The reverse inclusion is the substantial one and follows the paper.  Given a neighbourhood `α`
of the diagonal of `W` and an open `𝒰 ∋ (φ, ψ)`, both are first replaced by *cylinder*
neighbourhoods (`existsCylinderSubsetNhdsSetDiagonal` and `existsProdCylinderSubsetNhds`),
which constrain only finitely many coordinates `F ⊆ groGroup S`.  Theorem 6.1 supplies `s₀`
with `F · i(s₀) ⊆ i(S)`; writing `h₀ = i(s₀)⁻¹` and `f = i(s_f) h₀`, every coordinate `χ(f)`
equals `s_f (χ(h₀))`.  Regional proximality of `(φ(h₀), ψ(h₀))`, which is
`natExtRPAtAllCoordinates`, then produces the required pair, lifted back to `W` by
`natExtEvalSurjective`. -/
theorem pullBackOfRPThruNatExtFactorIsRP
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :
letI : Nonempty ↑(natExtSet dSystem) :=
  natExtSetIsNonemptyInstance (hSurject := minimalCommActionIsSurjective hMin)
Set.preimage (Prod.map (natExtFactorMap dSystem) (natExtFactorMap dSystem)) (RP dSystem) =
  RP (natExtSystem (minimalCommActionIsSurjective hMin)) := by
  have hSurject := minimalCommActionIsSurjective hMin
  have : Nonempty ↑(natExtSet dSystem) := natExtSetIsNonemptyInstance (hSurject := hSurject)
  refine Set.Subset.antisymm ?_ ?_
  · -- `(π × π)⁻¹ RP_X ⊆ RP_W`, the substantial inclusion
    classical
    intro z hz
    have hzRP : (z.1.1 1, z.2.1 1) ∈ RP dSystem := hz
    simp only [RP, Set.mem_iInter]
    intro α hα
    rw [mem_closure_iff]
    intro 𝒰 h𝒰open h𝒰z
    -- replace `α` and `𝒰` by cylinder neighbourhoods, constraining finitely many coordinates
    obtain ⟨F₁, α₀, hα₀open, hα₀diag, hcyl⟩ :=
      existsCylinderSubsetNhdsSetDiagonal (natExtSetIsClosed dSystem) hα
    obtain ⟨F₂, A, B, hF₂fin, hA, hB, hprod⟩ :=
      existsProdCylinderSubsetNhds (h𝒰open.mem_nhds h𝒰z)
    -- shift the finitely many relevant coordinates into the image of `S`
    have hFfin : ((↑F₁ : Set (groGroup S)) ∪ F₂).Finite := F₁.finite_toSet.union hF₂fin
    obtain ⟨s₀, hs₀⟩ := imageOfSIsThickInGroGroup S _ hFfin
    have hchoice : ∀ f : groGroup S, ∃ r : S,
        f ∈ (↑F₁ : Set (groGroup S)) ∪ F₂ → groGroupHom r = f * groGroupHom s₀ := by
      intro f
      by_cases hf : f ∈ (↑F₁ : Set (groGroup S)) ∪ F₂
      · obtain ⟨r, -, hr⟩ := hs₀ ⟨f, hf, rfl⟩
        have hr' : groGroupHom r = f * groGroupHom s₀ := hr
        exact ⟨r, fun _ ↦ hr'⟩
      · obtain ⟨r₀⟩ := ‹Nonempty S›
        exact ⟨r₀, fun h ↦ absurd h hf⟩
    choose sf hsf using hchoice
    set h₀ : groGroup S := (groGroupHom s₀)⁻¹ with hh₀
    have hfEq : ∀ f ∈ (↑F₁ : Set (groGroup S)) ∪ F₂, groGroupHom (sf f) * h₀ = f := by
      intro f hf
      rw [hsf f hf, hh₀, mul_assoc, mul_inv_cancel, mul_one]
    have hEval : ∀ (χ : ↑(natExtSet dSystem)) (f : groGroup S),
        f ∈ (↑F₁ : Set (groGroup S)) ∪ F₂ → χ.1 f = dSystem.map (sf f) (χ.1 h₀) := by
      intro χ f hf
      have hx := χ.2 h₀ (sf f)
      rw [hfEq f hf] at hx
      exact hx
    -- the corresponding open sets downstairs in `X`
    have h𝒫open : IsOpen (⋂ f ∈ F₂, (dSystem.map (sf f)) ⁻¹' (interior (A f))) :=
      hF₂fin.isOpen_biInter fun f _ ↦ isOpen_interior.preimage (dSystem.mapCont (sf f))
    have h𝒬open : IsOpen (⋂ f ∈ F₂, (dSystem.map (sf f)) ⁻¹' (interior (B f))) :=
      hF₂fin.isOpen_biInter fun f _ ↦ isOpen_interior.preimage (dSystem.mapCont (sf f))
    have h𝒜open : IsOpen (⋂ f ∈ (↑F₁ : Set (groGroup S)),
        ((diagDynamicalSystem dSystem dSystem).map (sf f)) ⁻¹' α₀) :=
      F₁.finite_toSet.isOpen_biInter fun f _ ↦
        hα₀open.preimage ((diagDynamicalSystem dSystem dSystem).mapCont (sf f))
    have h𝒜diag : Set.diagonal X ⊆ ⋂ f ∈ (↑F₁ : Set (groGroup S)),
        ((diagDynamicalSystem dSystem dSystem).map (sf f)) ⁻¹' α₀ := by
      rintro ⟨x, y⟩ hxy
      have hxy' : x = y := hxy
      subst hxy'
      simp only [Set.mem_iInter, Set.mem_preimage]
      intro f _
      exact hα₀diag (rfl : dSystem.map (sf f) x = dSystem.map (sf f) x)
    have h𝒫mem : z.1.1 h₀ ∈ ⋂ f ∈ F₂, (dSystem.map (sf f)) ⁻¹' (interior (A f)) := by
      simp only [Set.mem_iInter, Set.mem_preimage]
      intro f hf
      rw [← hEval z.1 f (Set.mem_union_right _ hf)]
      exact mem_interior_iff_mem_nhds.mpr (hA f)
    have h𝒬mem : z.2.1 h₀ ∈ ⋂ f ∈ F₂, (dSystem.map (sf f)) ⁻¹' (interior (B f)) := by
      simp only [Set.mem_iInter, Set.mem_preimage]
      intro f hf
      rw [← hEval z.2 f (Set.mem_union_right _ hf)]
      exact mem_interior_iff_mem_nhds.mpr (hB f)
    -- regional proximality of `z` at the coordinate `h₀` (Claim 1)
    have hRPh₀ := natExtRPAtAllCoordinates hMin z.1 z.2 hzRP h₀
    simp only [RP, Set.mem_iInter] at hRPh₀
    have hRP' := hRPh₀ _ (mem_nhdsSet.mpr ⟨_, subset_rfl, h𝒜open, h𝒜diag⟩)
    rw [mem_closure_iff] at hRP'
    obtain ⟨w, hw, hworb⟩ := hRP' _ (h𝒫open.prod h𝒬open) (Set.mk_mem_prod h𝒫mem h𝒬mem)
    simp only [inverseSetOrbit, Set.mem_iUnion, Set.mem_preimage] at hworb
    obtain ⟨s, hs⟩ := hworb
    -- lift `w` back to the natural extension along evaluation at `h₀`
    obtain ⟨η, hη⟩ := natExtEvalSurjective hSurject h₀ w.1
    obtain ⟨ρ, hρ⟩ := natExtEvalSurjective hSurject h₀ w.2
    have hη' : η.1 h₀ = w.1 := hη
    have hρ' : ρ.1 h₀ = w.2 := hρ
    refine ⟨(η, ρ), ?_, ?_⟩
    · refine hprod (η, ρ) ?_ ?_
      · intro f hf
        rw [hEval η f (Set.mem_union_right _ hf), hη']
        have h1 := hw.1
        simp only [Set.mem_iInter, Set.mem_preimage] at h1
        exact interior_subset (h1 f hf)
      · intro f hf
        rw [hEval ρ f (Set.mem_union_right _ hf), hρ']
        have h2 := hw.2
        simp only [Set.mem_iInter, Set.mem_preimage] at h2
        exact interior_subset (h2 f hf)
    · simp only [inverseSetOrbit, Set.mem_iUnion, Set.mem_preimage]
      refine ⟨s, hcyl ?_⟩
      intro f hf
      have hfF : f ∈ (↑F₁ : Set (groGroup S)) ∪ F₂ :=
        Set.mem_union_left _ (Finset.mem_coe.mpr hf)
      have hshift : f * groGroupHom s = groGroupHom (sf f * s) * h₀ := by
        rw [groGroupHomIsSemigroupHom, mul_assoc, mul_comm (groGroupHom s) h₀, ← mul_assoc,
          hfEq f hfF]
      have hco : ∀ (χ : ↑(natExtSet dSystem)) (c : X), χ.1 h₀ = c →
          ((natExtSystem hSurject).map s χ).1 f = dSystem.map (sf f) (dSystem.map s c) := by
        intro χ c hc
        change χ.1 (f * groGroupHom s) = _
        rw [hshift, χ.2 h₀ (sf f * s), dSystem.mapMult, hc]
      simp only [Set.mem_iInter, Set.mem_preimage] at hs
      change (((natExtSystem hSurject).map s η).1 f,
        ((natExtSystem hSurject).map s ρ).1 f) ∈ α₀
      rw [hco η w.1 hη', hco ρ w.2 hρ']
      exact hs f (Finset.mem_coe.mpr hf)
  · -- `RP_W ⊆ (π × π)⁻¹ RP_X`: `imageOfRPIsInRP` carries `RP` forward along the factor map
    intro z hz
    exact imageOfRPIsInRP (natExtSystem hSurject) dSystem (natExtFactorMap dSystem)
      (hπ := natExtFactorMapIsFactorMap hSurject) ⟨z, hz, rfl⟩


/-- The setoid on `X` given by the regionally proximal relation of a minimal system -/
abbrev RPSetoid
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :
Setoid X :=
⟨setToRelation (RP dSystem), (RPisICER hMin).2.2⟩

instance RPQuotientNonempty
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :
Nonempty (Quotient (RPSetoid hMin)) :=
nonemptyQuotient X (RPisICER hMin).2.2

instance RPQuotientT2
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :
T2Space (Quotient (RPSetoid hMin)) :=
quotientOfCompactT2ByClosedIsT2 (RPisICER hMin).2.1 (RPisICER hMin).2.2

/-- The largest equicontinuous factor `X / RP_X` of a minimal system `X` -/
noncomputable def maxEquiFactor
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :
DynamicalSystem S (Quotient (RPSetoid hMin)) :=
quotientDynamicalSystem dSystem (RPisICER hMin)

/-- The quotient map `X → X / RP_X` is a factor map onto the largest equicontinuous factor -/
lemma maxEquiFactorQuotientIsFactorMap
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :
isFactorMap dSystem (maxEquiFactor hMin) (Quotient.mk (RPSetoid hMin)) :=
quotientMapIsFactorMap dSystem (RPisICER hMin)

@[simp] lemma maxEquiFactorMap
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) (s : S) (x : X) :
(maxEquiFactor hMin).map s (Quotient.mk (RPSetoid hMin) x)
  = Quotient.mk (RPSetoid hMin) (dSystem.map s x) :=
congrFun ((maxEquiFactorQuotientIsFactorMap hMin).2.2 s) x

/-- Shorthand for the forward direction of `natExtMinimalIffSystemIsMinimal` (Theorem 6.7):
the natural extension of a minimal system is a minimal `S`-system.

This carries no content of its own; it exists only because
`(natExtMinimalIffSystemIsMinimal (minimalCommActionIsSurjective hMin)).mp hMin` appears
inside the *statements* below, where spelling it out in full is unreadable.  Contrast
`natExtGroSystemIsMinimal`, which is a genuinely different fact: it concerns the
`groGroup S`-system `natExtGroSystem`, not the `S`-system `natExtSystem`, so it is not an
instance of Theorem 6.7. -/
abbrev natExtSystemIsMinimal
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :
letI : Nonempty ↑(natExtSet dSystem) :=
  natExtSetIsNonemptyInstance (hSurject := minimalCommActionIsSurjective hMin)
isMinimalSystem (natExtSystem (minimalCommActionIsSurjective hMin)) :=
(natExtMinimalIffSystemIsMinimal (minimalCommActionIsSurjective hMin)).mp hMin

/-- **Theorem 6.9**, second half: `W / RP_W` is isomorphic to `X / RP_X`, via `[w] ↦ [π w]`.

Well-definedness of the map is the inclusion `RP_W ⊆ (π × π)⁻¹ RP_X` and its injectivity is
the reverse inclusion, so both halves of `pullBackOfRPThruNatExtFactorIsRP` are used. -/
theorem maxEquiFactorOfNatExtIsoMaxEquiFactor
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :
letI : Nonempty ↑(natExtSet dSystem) :=
  natExtSetIsNonemptyInstance (hSurject := minimalCommActionIsSurjective hMin)
∃ ξ : Quotient (RPSetoid (natExtSystemIsMinimal hMin)) → Quotient (RPSetoid hMin),
  isIsomorphism (maxEquiFactor (natExtSystemIsMinimal hMin)) (maxEquiFactor hMin) ξ := by
  have hSurject := minimalCommActionIsSurjective hMin
  have : Nonempty ↑(natExtSet dSystem) := natExtSetIsNonemptyInstance (hSurject := hSurject)
  have hWMin := natExtSystemIsMinimal hMin
  obtain ⟨hπcont, hπsurj, hπequiv⟩ := natExtFactorMapIsFactorMap hSurject
  have hTh69 := pullBackOfRPThruNatExtFactorIsRP hMin
  -- well-definedness is the inclusion `RP_W ⊆ (π × π)⁻¹ RP_X` of Theorem 6.9
  have hwell : ∀ a b : ↥(natExtSet dSystem), (a, b) ∈ RP (natExtSystem hSurject) →
      Quotient.mk (RPSetoid hMin) (natExtFactorMap dSystem a)
        = Quotient.mk (RPSetoid hMin) (natExtFactorMap dSystem b) := by
    intro a b hab
    apply Quotient.sound
    rw [← hTh69] at hab
    exact hab
  refine ⟨Quotient.lift
    (fun w ↦ Quotient.mk (RPSetoid hMin) (natExtFactorMap dSystem w)) hwell, ?_, ?_⟩
  · -- a continuous bijection from a compact space to a Hausdorff space
    rw [isHomeomorph_iff_continuous_isClosedMap_bijective]
    have hcont : Continuous (Quotient.lift (s := RPSetoid hWMin)
        (fun w ↦ Quotient.mk (RPSetoid hMin) (natExtFactorMap dSystem w)) hwell) :=
      continuous_quot_lift hwell (continuous_quot_mk.comp hπcont)
    refine ⟨hcont, hcont.isClosedMap, ?_, ?_⟩
    · -- injectivity is the reverse inclusion of Theorem 6.9
      intro q₁ q₂ h
      induction q₁ using Quotient.inductionOn with | _ a =>
      induction q₂ using Quotient.inductionOn with | _ b =>
      apply Quotient.sound
      have h1 : (natExtFactorMap dSystem a, natExtFactorMap dSystem b) ∈ RP dSystem :=
        Quotient.exact h
      change (a, b) ∈ RP (natExtSystem hSurject)
      rw [← hTh69]
      exact h1
    · intro q
      induction q using Quotient.inductionOn with | _ x =>
      obtain ⟨w, hw⟩ := hπsurj x
      subst hw
      exact ⟨Quotient.mk _ w, rfl⟩
  · intro s
    funext q
    induction q using Quotient.inductionOn with | _ w =>
    change (maxEquiFactor hMin).map s (Quotient.mk (RPSetoid hMin) (natExtFactorMap dSystem w))
      = Quotient.lift _ hwell ((maxEquiFactor hWMin).map s (Quotient.mk (RPSetoid hWMin) w))
    rw [maxEquiFactorMap, maxEquiFactorMap]
    have he := congrFun (hπequiv s) w
    simp only [Function.comp_apply] at he
    rw [he]
    rfl

/-! ### Theorem E

Theorem E identifies three `S`-systems: `X / RP_X`, `W / RP_{W,S}` and `W / RP_{W,Gr(S)}`.
The first two are identified by Theorem 6.9 above, so what remains is to identify
`W / RP_{W,S}` with `W / RP_{W,Gr(S)}`; this rests on Theorem D applied to the two commuting
actions on `W`.
-/

/-- The natural extension of a minimal system is a minimal `groGroup S`-system -/
lemma natExtGroSystemIsMinimal
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :
letI : Nonempty ↑(natExtSet dSystem) :=
  natExtSetIsNonemptyInstance (hSurject := minimalCommActionIsSurjective hMin)
isMinimalSystem (natExtGroSystem (minimalCommActionIsSurjective hMin)) := by
  have hSurject := minimalCommActionIsSurjective hMin
  have : Nonempty ↑(natExtSet dSystem) := natExtSetIsNonemptyInstance (hSurject := hSurject)
  have hWMin : isMinimalSystem (natExtSystem hSurject) :=
    (natExtMinimalIffSystemIsMinimal hSurject).mp hMin
  rw [minimalIffDenseOrbits]
  intro φ
  refine Dense.mono ?_ ((minimalIffDenseOrbits (natExtSystem hSurject)).mp hWMin φ)
  rintro z ⟨s, rfl⟩
  exact ⟨groGroupHom s, rfl⟩

/-- The `S`-action and the `groGroup S`-action on the natural extension commute -/
lemma natExtActionsCommute
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hSurject : isSurjectiveSystem dSystem) :
letI : Nonempty ↑(natExtSet dSystem) := natExtSetIsNonemptyInstance (hSurject := hSurject)
∀ (s : S) (g : groGroup S),
  ((natExtSystem hSurject).map s) ∘ ((natExtGroSystem hSurject).map g)
    = ((natExtGroSystem hSurject).map g) ∘ ((natExtSystem hSurject).map s) := by
  have : Nonempty ↑(natExtSet dSystem) := natExtSetIsNonemptyInstance (hSurject := hSurject)
  intro s g
  funext φ
  change (natExtGroSystem hSurject).map (groGroupHom s) ((natExtGroSystem hSurject).map g φ)
    = (natExtGroSystem hSurject).map g ((natExtGroSystem hSurject).map (groGroupHom s) φ)
  rw [← (natExtGroSystem hSurject).mapMult, ← (natExtGroSystem hSurject).mapMult, mul_comm]

/-- Theorem D applied to the natural extension: its regionally proximal relation as an
`S`-system and as a `groGroup S`-system agree -/
lemma natExtRPEqGroRP
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :
letI : Nonempty ↑(natExtSet dSystem) :=
  natExtSetIsNonemptyInstance (hSurject := minimalCommActionIsSurjective hMin)
RP (natExtSystem (minimalCommActionIsSurjective hMin))
  = RP (natExtGroSystem (minimalCommActionIsSurjective hMin)) := by
  have hSurject := minimalCommActionIsSurjective hMin
  have : Nonempty ↑(natExtSet dSystem) := natExtSetIsNonemptyInstance (hSurject := hSurject)
  exact forTwoMinCommActionsRPsAreSame
    ((natExtMinimalIffSystemIsMinimal hSurject).mp hMin)
    (natExtGroSystemIsMinimal hMin)
    (natExtActionsCommute hSurject)

/-- Theorem E, (2) is isomorphic to (3): the largest equicontinuous factor of `W` as an
`S`-system is the largest equicontinuous factor of `W` as a `groGroup S`-system, viewed as
an `S`-system via `groGroupHom`.  The two relations are equal by Theorem D, so the identity
descends to the isomorphism. -/
theorem maxEquiFactorOfNatExtIsoGroMaxEquiFactor
{S} [CommSemigroup S] [Nonempty S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem) :
letI : Nonempty ↑(natExtSet dSystem) :=
  natExtSetIsNonemptyInstance (hSurject := minimalCommActionIsSurjective hMin)
∃ ζ : Quotient (RPSetoid (natExtSystemIsMinimal hMin))
    → Quotient (RPSetoid (natExtGroSystemIsMinimal hMin)),
  isIsomorphism (maxEquiFactor (natExtSystemIsMinimal hMin))
    (homDynamicalSystem groGroupHom (maxEquiFactor (natExtGroSystemIsMinimal hMin))) ζ := by
  have hSurject := minimalCommActionIsSurjective hMin
  have : Nonempty ↑(natExtSet dSystem) := natExtSetIsNonemptyInstance (hSurject := hSurject)
  have hWMin := natExtSystemIsMinimal hMin
  have hWGrMin := natExtGroSystemIsMinimal hMin
  have hRPeq := natExtRPEqGroRP hMin
  have hwell : ∀ a b : ↥(natExtSet dSystem), (a, b) ∈ RP (natExtSystem hSurject) →
      Quotient.mk (RPSetoid hWGrMin) a = Quotient.mk (RPSetoid hWGrMin) b := by
    intro a b hab
    apply Quotient.sound
    rw [hRPeq] at hab
    exact hab
  refine ⟨Quotient.lift (fun w ↦ Quotient.mk (RPSetoid hWGrMin) w) hwell, ?_, ?_⟩
  · rw [isHomeomorph_iff_continuous_isClosedMap_bijective]
    have hcont : Continuous (Quotient.lift (s := RPSetoid hWMin)
        (fun w ↦ Quotient.mk (RPSetoid hWGrMin) w) hwell) :=
      continuous_quot_lift hwell continuous_quot_mk
    refine ⟨hcont, hcont.isClosedMap, ?_, ?_⟩
    · intro q₁ q₂ h
      induction q₁ using Quotient.inductionOn with | _ a =>
      induction q₂ using Quotient.inductionOn with | _ b =>
      apply Quotient.sound
      have h1 : (a, b) ∈ RP (natExtGroSystem hSurject) := Quotient.exact h
      change (a, b) ∈ RP (natExtSystem hSurject)
      rw [hRPeq]
      exact h1
    · intro q
      induction q using Quotient.inductionOn with | _ w =>
      exact ⟨Quotient.mk _ w, rfl⟩
  · intro s
    funext q
    induction q using Quotient.inductionOn with | _ w =>
    change (maxEquiFactor hWGrMin).map (groGroupHom s) (Quotient.mk (RPSetoid hWGrMin) w)
      = Quotient.lift _ hwell ((maxEquiFactor hWMin).map s (Quotient.mk (RPSetoid hWMin) w))
    rw [maxEquiFactorMap, maxEquiFactorMap]
    rfl

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
