import NSFLEAPS._03_Family_algebra.FA_Theorems
import NSFLEAPS._05_Ultrafilters.UF_Defs
import NSFLEAPS._06_Furstenberg_families.FF_CXX

section Abstract_results

/-- If `R(x,U) ∈ F` and `F` is a partition regular family, then there exists
`y ∈ U` such that for all neighborhoods `V ∋ y`, `R(x,V) ∈ F` -/
theorem visitTimeConcentrationForPRFamily
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X)
(x : X) (U : Set X) {hU : IsClosed U}
(F : Family S) {hF : isPRFamily F} :
visitTimeSet dSystem x U ∈ F →
∃ (y : X), y ∈ U ∧ (∀ (V : Set X), V ∈ nhds y → visitTimeSet dSystem x V ∈ F) := by
contrapose
intro h1
simp only [not_exists, not_and, not_forall] at h1
have hU1 : IsCompact U := by
  apply hU.isCompact
have h2 : ∀ y ∈ U, ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ visitTimeSet dSystem x W ∉ F := by
  intro y hy
  specialize h1 y hy
  obtain ⟨V, hV1, hV2⟩ := h1
  rcases (mem_nhds_iff.mp hV1) with ⟨W, hUsub, hUopen, hyU⟩
  use W
  constructor
  · exact hUopen
  constructor
  · exact hyU
  by_contra h
  have hUV_visitTime : visitTimeSet dSystem x W ⊆ visitTimeSet dSystem x V := by
    apply visitTimesMono
    exact hUsub
  have hV3 : visitTimeSet dSystem x V ∈ F := by
    apply F.upward_closed (visitTimeSet dSystem x W)
    · apply h
    · apply hUV_visitTime
  exact hV2 hV3
choose f hf using h2
let g : U → Set X := fun y ↦ f y y.2
have hgOpen : ∀ y : U, IsOpen (g y) := by
  simp only [Subtype.forall, g]
  intro y hy
  specialize hf y hy
  exact hf.1
have hExistFin : ∃ G : Finset U, U ⊆ ⋃ y ∈ G, g y := by
  apply IsCompact.elim_finite_subcover
  · exact hU1
  · exact hgOpen
  · intro x hxU
    simp only [Set.iUnion_coe_set, Set.mem_iUnion]
    use x
    use hxU
    simp only [g]
    specialize hf x hxU
    exact hf.2.1
rcases hExistFin with ⟨G, hG⟩
have hSub : visitTimeSet dSystem x U ⊆ ⋃ y : G, visitTimeSet dSystem x (g y) := by
  simp only [visitTimeSet]
  intro s hs
  simp only [Set.mem_preimage] at hs
  simp only [Set.mem_iUnion, Set.mem_preimage, Subtype.exists, exists_prop]
  have hSub1 := hG hs
  simp only [Set.iUnion_coe_set, Set.mem_iUnion, exists_prop] at hSub1
  rcases hSub1 with ⟨t, ht1, ht2, ht3⟩
  use t
  use ht1
have hNo : ∀ y : G, visitTimeSet dSystem x (g y) ∉ F := by
  intro y
  simp only [g]
  specialize hf y y.1.2
  exact hf.2.2
by_contra hContra
have hGCard : G.card > 0 := by
  simp
  sorry
have hIn : ⋃ y : G, visitTimeSet dSystem x (g y) ∈ F := by
  apply F.upward_closed (visitTimeSet dSystem x U) (⋃ y : G, visitTimeSet dSystem x (g y))
  · exact hContra
  · exact hSub
have hExistOne : ∃ y : G, visitTimeSet dSystem x (g y) ∈ F := by
  unfold isPRFamily at hF
  specialize hF (⋃ y : G, visitTimeSet dSystem x (g y)) hIn ⟨G.card, hGCard⟩
  sorry
rcases hExistOne with ⟨y, hy⟩
specialize hNo y
exact hNo hy

end Abstract_results

section Syndetic_and_thick_sets

/-- The family of syndetic subsets of a semigroup -/
def syndeticFamily
(S : Type*) [Semigroup S] [Nonempty S] : Family S :=
{
  sets := {A : Set S | isSyndetic A}
  upward_closed := by
    intro A B hA hAB
    exact syndeticIsMonotone hA hAB
}

/-- The family of thick subsets of a semigroup -/
def thickFamily
(S : Type*) [Semigroup S] [Nonempty S] : Family S :=
{
  sets := {A : Set S | isThick A}
  upward_closed := by
    intro A B hA hAB
    exact thickIsMonotone hA hAB
}

/-- A set is thick iff its complement is not syndetic -/
theorem thickIffComplementNotSyndetic
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
isThick A ↔ ¬isSyndetic Aᶜ := by
constructor
-- prove the only if direction
· intro hA
  by_contra hAc
  obtain ⟨F, hF1, hF2⟩ := hAc
  specialize hA F hF1
  obtain ⟨s, hs⟩ := hA
  specialize hF2 s
  have h1 : ∀ f ∈ F, f * s ∈ A := by
    intro f hf0
    apply hs
    exact ⟨f, hf0, rfl⟩
  obtain ⟨f, hf1, hf2⟩ := hF2
  specialize h1 f hf1
  exact hf2 h1
-- prove the if direction
· contrapose
  intro hA_nThick
  have hA1 : ¬ (∀ F : Set S, F.Finite → ∃ s : S, (· * s) '' F ⊆ A) := by
    exact hA_nThick
  have hA4 : ∃ F : Set S, (F.Finite ∧ ∀ s : S, ¬(· * s) '' F ⊆ A) := by
    push_neg at hA1
    exact hA1
  obtain ⟨F, hF1, hF2⟩ := hA4
  use F
  constructor
  · apply hF1
  · intro s
    specialize hF2 s
    have hA5 : ((fun x ↦ x * s) '' F ∩ Aᶜ).Nonempty := by
      simpa [Set.subset_def, Set.ext_iff] using hF2
    simpa using hA5

/-- The families of syndetic sets and thick sets are dual -/
-- This used to work but something happens upstream now dualEquivForm no longer work
-- Need to fix
theorem dualSyndeticThick
{S : Type*} [Semigroup S] [Nonempty S] :
(syndeticFamily S)* = (thickFamily S) :=
by sorry
  -- ext A
  -- have dualEquivForm : ((syndeticFamily S)*).sets = {A : Set S | Aᶜ ∉ syndeticFamily S} :=
  --   famDualAlt (syndeticFamily S)
  -- rw [dualEquivForm]
  -- change A ∈ {A | Aᶜ ∉ (syndeticFamily S).sets} ↔ A ∈ (thickFamily S).sets
  -- unfold syndeticFamily
  -- unfold thickFamily
  -- simp only [Set.mem_setOf_eq]
  -- exact Iff.symm (thickIffComplementNotSyndetic A)

/-- Dual of thick family is syndetic family -/
theorem dualThickSyndetic
{S : Type*} [Semigroup S] [Nonempty S] :
(thickFamily S)* = (syndeticFamily S) := by
rw [<- dualSyndeticThick]
sorry
--apply dual_dual_smth_smth

/-- If A is a thick set and K is a finite set of a semigroup S,
then ⋂ k ∈ K, (k * ·) ⁻¹' A is thick -/
theorem inverseDilateCapOfThickIsThick
{S} [Semigroup S] [Nonempty S]
(A : Set S) {hA : isThick A}
(K : Set S) {KIsFinite : K.Finite} :
isThick (⋂ k ∈ K, (k * ·) ⁻¹' A) := by
intro F hF
let E := (⋃ k ∈ K, (k * ·) '' F)
have hFinite: ∀ k ∈ K, ((k * ·) '' F).Finite := by
  intro k hk
  apply hF.image (k * ·)
have hEFinite: E.Finite := by
  apply KIsFinite.biUnion hFinite
specialize hA E hEFinite
obtain ⟨s, hs⟩ := hA
use s
intro a ha
simp only [Set.mem_iInter]
intro i hi
simp only [Set.mem_preimage]
obtain ⟨b, hb1, hb2⟩ := ha
have hb3 : b * s = a:= by
  simp only at hb2
  exact hb2
rw [<- hb3]
apply hs
unfold E
simp only [Set.mem_image, Set.mem_iUnion, exists_prop, exists_exists_and_exists_and_eq_and]
use i
simp only [hi, true_and]
use b
simp only [hb1, true_and]
apply Semigroup.mul_assoc

-- I changed the hypothesis of this theorem from Semigroup S to Monoid S.
-- The purpose is to have access to Finset.prod function ∏ which is only available for Monoid
-- We may weaken the hypothesis to Semigroup later by using WithOne function
theorem commDilateCapOfThickIsThick
{S} [CommMonoid S] [Nonempty S]
(A : Set S) {hA : isThick A}
(K : Set S) {KIsFinite : K.Finite} :
isThick (⋂ k ∈ K, (k * ·) '' A) := by
intro F hF
let p : S := ∏ x ∈ KIsFinite.toFinset, x
classical
let f : S → S := fun k ↦ ∏ x ∈ KIsFinite.toFinset.erase k, x
let Q := ⋂ x ∈ f '' K, (x * ·) ⁻¹' A
have hqThick : isThick (Q) := by
  apply inverseDilateCapOfThickIsThick
  · exact hA
  exact KIsFinite.image f
specialize hqThick F hF
obtain ⟨s, hs⟩ := hqThick
use p * s
intro b hb
obtain ⟨a, ha1, ha2⟩ := hb
have hb2 : b = a * (p * s) := by
  rw [<- ha2]
-- redefine the goal
have goal_redefined: ∀ k ∈ K, b ∈ (fun x ↦ k * x) '' A := by
  intro k hk
  have ha_in_Q : a * s ∈ Q := by
    exact hs ⟨a, ha1, rfl⟩
  have hQ : ∀ q ∈ Q, ∀ x ∈ f '' K, x * q ∈ A := by
    unfold Q
    simp
  specialize hQ (a * s) ha_in_Q
  specialize hQ (f k) ⟨k, hk, rfl⟩
  have hk1 : k ∈ KIsFinite.toFinset := by
    simpa using hk
  have hp : k * f (k) = p := by
    classical
    simpa using (Finset.mul_prod_erase (s := KIsFinite.toFinset) (f := fun x => x) hk1)
  rw [<- hp] at hb2
  have hb_rewrite: b = k * ((f k) * (a * s)) := by
    simp [hb2, mul_comm, mul_left_comm, mul_assoc]
  simp only [Set.mem_image]
  use ((f k) * (a * s))
  constructor
  · exact hQ
  rw [hb_rewrite]
-- finishing the proof
simpa [Set.mem_iInter] using goal_redefined

/-- This instance makes the semigroup structure on βS "canonical" by
making it available to typeclass inference -/
instance
{S : Type*} [Semigroup S] : Semigroup (Ultrafilter S) :=
  Ultrafilter.semigroup

/-- The closure in `βS` of a thick subset of a semigroup `S`
contains a minimal left ideal -/
theorem thickClosureContainsIdeal
{S : Type*} [Semigroup S] [Nonempty S]
{H : Set S} (hH : isThick H) :
∃ (L : Set (Ultrafilter S)),
isMinLeftIdeal L ∧ L ⊆ closure ((pure : S → Ultrafilter S) '' H) :=
by sorry

/-- The closure in `βS` of a syndetic subset of a semigroup `S`
has non-empty intersection with every left ideal -/
theorem syndeticClosureMeetsEveryIdeal
{S : Type*} [Semigroup S] [Nonempty S]
{A : Set S} (hA : isSyndetic A) :
∀ (L : Set (Ultrafilter S)),
isLeftIdeal L → (L ∩ closure ((pure : S → Ultrafilter S) '' A)).Nonempty :=
by sorry

/-- If `H ⊆ S` is thick, there exists a minimal idempotent `p ∈ βS` such that
for all finite `F ⊆ S`, `∩ f ∈ F, f⁻¹H ∈ p` -/
theorem minIdempotentWitnessesShiftIntersectionLargeness
{S : Type*} [Semigroup S] [Nonempty S]
(H : Set S) {hH : isThick H} :
∃ (p : Ultrafilter S), isMinimalUltrafilter p ∧ p * p = p ∧
∀ (F : Set S), F.Finite → (⋂ f ∈ F, (leftMult f) ⁻¹' H) ∈ p :=
by sorry


end Syndetic_and_thick_sets


section Delta_sets

/-- A set `A ⊆ S` is Delta_0 if for all `n`, there exist `s_1, ..., s_n ∈ S`
such that for all `1 ≤ i < j ≤ k`, `s_j ∈ s_i A` -/
def isDeltaZero
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∀ (k : ℕ), ∃ (s : Fin k → S), ∀ (i j : Fin k), i < j → (s j) ∈ ((s i) * ·) '' A

/-- If `A ⊆ S` is Delta_0 and `A ⊆ B`, then `B` is Delta_0. -/
theorem deltaZeroIsMonotone
{S : Type*} [Semigroup S] [Nonempty S]
{A B : Set S} (hA : isDeltaZero A) (hAB : A ⊆ B) :
isDeltaZero B := by
intro k
specialize hA k
obtain ⟨s, hs⟩ := hA
use s
intro i j hij
specialize hs i j hij
simp only [Set.mem_image] at hs
obtain ⟨x, hx1, hx2⟩ := hs
simp only [Set.mem_image]
use x
constructor
· exact hAB hx1
· exact hx2

/-- The family of Delta_0 subsets of a semigroup -/
def deltaZeroFamily
(S : Type*) [Semigroup S] [Nonempty S] : Family S :=
{
  sets := {A : Set S | isDeltaZero A}
  upward_closed := by
    intro A B hA hAB
    exact deltaZeroIsMonotone hA hAB
}

/-- A set `A ⊆ S` is Delta if there exist `s_1, s_2, ... ∈ S`
such that for all `1 ≤ i < j`, `s_j ∈ s_i A` -/
def isDelta
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∃ (s : ℕ → S), ∀ (i j : ℕ), i < j → (s j) ∈ ((s i) * ·) '' A

/-- If `A ⊆ S` is Delta and `A ⊆ B`, then `B` is Delta. -/
theorem deltaIsMonotone
{S : Type*} [Semigroup S] [Nonempty S]
{A B : Set S} (hA : isDelta A) (hAB : A ⊆ B) :
isDelta B := by
obtain ⟨s, hs⟩ := hA
use s
intro i j hij
specialize hs i j hij
simp only [Set.mem_image] at hs
obtain ⟨x, hx1, hx2⟩ := hs
simp only [Set.mem_image]
use x
constructor
· exact hAB hx1
· exact hx2

/-- The family of Delta subsets of a semigroup -/
def deltaFamily
(S : Type*) [Semigroup S] [Nonempty S] : Family S :=
{
  sets := {A : Set S | isDelta A}
  upward_closed := by
    intro A B hA hAB
    exact deltaIsMonotone hA hAB
}

/-- In a semigroup S, Delta sets are Delta_0 -/
theorem deltaFamilyContainedInDeltaZeroFamily
{S : Type*} [Semigroup S] [Nonempty S] :
deltaFamily S ⊆ deltaZeroFamily S := by
intro A hA
obtain ⟨x, hx⟩ := hA
simp only [SetLike.mem_coe]
have reduce_goal: isDeltaZero A → A ∈ deltaZeroFamily S := by
  intro hA2
  simpa
apply reduce_goal
unfold isDeltaZero
intro k
let s : Fin k → S := fun i ↦ x (i)
use s
intro i j hij
specialize hx i j hij
simpa

end Delta_sets

section dcS_sets

/-- A subset `A` of a semigroup `S` is a dcS set (dynamically central syndetic)
if there exists a minimal ultrafilter `p` and an open set `U ⊆ βS` containing `p`
such that the times of visits of `p` to `U` is contained in `A` -/
def isdcSSet
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∃ (p : Ultrafilter S) (_ : isMinimalUltrafilter p),
∃ (U : Set (Ultrafilter S)) (_ : IsOpen U) (_ : p ∈ U),
visitTimeSet (ultrafilterSystem S) p U ⊆ A

/-- The property of being a `dcS` set is upward closed -/
theorem dcSIsMonotone
{S : Type*} [Semigroup S] [Nonempty S]
{A B : Set S} (hA : isdcSSet A) (hAB : A ⊆ B) :
isdcSSet B := by
obtain ⟨p, hp, U, hU1, hU2, hU3⟩ := hA
use p
use hp
use U
use hU1
use hU2
exact Set.Subset.trans hU3 hAB

/-- The family of `dcS` sets -/
def dcSFamily
{S : Type*} [Semigroup S] [Nonempty S] :
Family S :=
{
  sets := {A : Set S | isdcSSet A}
  upward_closed := by
    intro A B hA hAB
    exact dcSIsMonotone hA hAB
}

/-- If a set `A ⊆ S` is a `dcS` set, then it contains the times of
returns of a point to a neighborhood of itself in a minimal `S`-system.
(Note that the compact Hausdorff space `X` has the same type as `S`.) -/
theorem isdcSSetImpliesVisitsFromCompactHausdorffSpace
{S : Type u} [Semigroup S] [Nonempty S] (A : Set S) :
isdcSSet A → ∃ (X : Type u) (_ : TopologicalSpace X)
(_ : CompactSpace X) (_ : T2Space X) (_ : Nonempty X)
(dSystem : DynamicalSystem S X) (_ : isMinimalSystem dSystem)
(x : X) (U : Set X) (_ : x ∈ U) (_ : IsOpen U),
visitTimeSet dSystem x U ⊆ A := by
  intro hdcSA
  obtain ⟨p, hp, U, hU1, hU2, hU3⟩ := hdcSA
  let X := orbitClosure (ultrafilterSystem S) p
  have Xprops := orbitClosureIsNonemptyCompactT2InvariantSubset (ultrafilterSystem S) p
  use X
  use inferInstance
  letI csX : CompactSpace ↑X := isCompact_iff_compactSpace.mp Xprops.2.1
  use csX
  use inferInstance
  letI nonX : Nonempty ↑X := Set.Nonempty.coe_sort Xprops.1
  use nonX
  let dSystem := fromNonemptyCompactT2InvariantSubsetToSystem (ultrafilterSystem S) Xprops
  use dSystem
  have XisMinSubset := orbitClosureOfURPointIsMinimalSubset
    (ultrafilterSystem S) ((ultrafilterMinimalIffUnifRec p).mp hp)
  have dSystemIsMin : isMinimalSystem dSystem :=
    (minimalSubsetIffMinimalSubsystem (ultrafilterSystem S) Xprops).mp XisMinSubset
  use dSystemIsMin
  have pinX : p ∈ X :=
    URPointBelongsToOrbitClosure (ultrafilterSystem S) ((ultrafilterMinimalIffUnifRec p).mp hp)
  use ⟨p, pinX⟩
  let V : Set ↑X := {x : ↑X | x.1 ∈ U}
  have Vnonempty : V.Nonempty := by
    use ⟨p, pinX⟩
    exact hU2
  use V
  use by exact hU2
  have Vopen : IsOpen V := by
    simpa [V] using hU1.preimage continuous_subtype_val
  use Vopen
  have visitInVisit : visitTimeSet dSystem ⟨p, pinX⟩ V ⊆
    visitTimeSet (ultrafilterSystem S) p U := by
      intro s hs
      unfold visitTimeSet at hs
      unfold visitTimeSet
      exact Set.mem_preimage.mpr hs
  exact Set.Subset.trans visitInVisit hU3

/-- If a set `A ⊆ S` contains the times of returns of a `UR` point to a
neighborhood of itself in an `S`-system, then it is a `dcS` set.
(Note that there are two universe-level metavariables here, one for `S`
and the other for `X`.) -/
theorem returnTimesImpliesdcS
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
(∃ (X : Type*) (_ : TopologicalSpace X)
(_ : CompactSpace X) (_ : T2Space X) (_ : Nonempty X)
(dSystem : DynamicalSystem S X) (x : X) (_ : isUniformlyRecurrent dSystem x)
(U : Set X) (_ : x ∈ U) (_ : IsOpen U),
visitTimeSet dSystem x U ⊆ A) → isdcSSet A := by
  intro hA
  obtain ⟨X,_,_,_,_,dSystem,x,xUR,U,xInU,Uopen,AhasVisits⟩ := hA
  let Z := orbitClosure dSystem x
  have xInZ := URPointBelongsToOrbitClosure dSystem xUR
  let V : Set ↑Z := {z : ↑Z | z.1 ∈ U}
  have Vnonempty : V.Nonempty := by
    use ⟨x, xInZ⟩
    exact xInU
  have Vopen : IsOpen V := by
    simpa [V] using Uopen.preimage continuous_subtype_val
  have Zpresystem : isNonemptyCompactT2InvariantSubset dSystem Z :=
    orbitClosureIsNonemptyCompactT2InvariantSubset dSystem x
  let dSystemZ := fromNonemptyCompactT2InvariantSubsetToSystem dSystem Zpresystem
  let _ : Nonempty ↥Z := (fun ⟨x, xInZ⟩ => ⟨⟨x, xInZ⟩⟩) Zpresystem.1
  let _ : CompactSpace ↥Z := isCompact_iff_compactSpace.mp Zpresystem.2.1
  have hZmin : isMinimalSystem dSystemZ := (minimalSubsetIffMinimalSubsystem
    dSystem Zpresystem).mp (orbitClosureOfURPointIsMinimalSubset dSystem xUR)
  have := (minimalIffDenseOrbits dSystemZ).mp hZmin ⟨x,xInZ⟩
  let fmap := fun p ↦ (ultraAction dSystemZ).map p ⟨x,xInZ⟩
  have uFactorMap : isFactorMap (ultrafilterSystem S) dSystemZ fmap :=
    ultraFactorMap dSystemZ ((minimalIffDenseOrbits dSystemZ).mp hZmin ⟨x,xInZ⟩)
  obtain ⟨p,hp,pUR⟩ :=liftUniformRecurrentPoint
    uFactorMap ⟨x,xInZ⟩ (minimalImpliesUniformlyRecurrent dSystemZ (hMin := hZmin) ⟨x,xInZ⟩)
  use p
  use (ultrafilterMinimalIffUnifRec p).mpr pUR
  use fmap ⁻¹' V
  use Continuous.isOpen_preimage uFactorMap.1 V Vopen
  have fmappinV : fmap p ∈ V := by
    rw [hp]
    exact xInU
  use fmappinV
  have preimageVisits := visitTimesThruFactorMap uFactorMap p V
  rw [hp] at preimageVisits
  rw [preimageVisits]
  exact AhasVisits

end dcS_sets

section central_sets

/-- A subset `A` of a semigroup `S` is a central set if it belongs to a
minimal idempotent ultrafilter on `S` -/
def isCentral
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∃ (p : Ultrafilter S) (_ : isMinimalUltrafilter p) (_ : p * p = p), A ∈ p

/-- The property of being a `central` set is upward closed -/
theorem centralIsMonotone
{S : Type*} [Semigroup S] [Nonempty S]
{A B : Set S} (hA : isCentral A) (hAB : A ⊆ B) :
isCentral B := by
obtain ⟨p, hp, hip, rest⟩ := hA
use p
use hp
use hip
exact Filter.mem_of_superset rest hAB

/-- The family of `central` sets -/
def centralFamily
{S : Type*} [Semigroup S] [Nonempty S] :
Family S :=
{
  sets := {A : Set S | isCentral A}
  upward_closed := by
    intro A B hA hAB
    exact centralIsMonotone hA hAB
}

/- The following theorems taken together show that TFAE:
  1. A is central
  2. A = R(x,U), where x is proximal to an S-uniformly recurrent point in the open set U
  3. A contains the intersection of a dcS set with a thick set -/

/-- If `A ⊆ S` is central, then `A = R(x,U)` where `x` is proximal
to an `S`-uniformly recurrent point in the open set `U` -/
theorem centralSetsAreVisitsOfPtToProxURPoint
{S : Type u} [Semigroup S] [Nonempty S] (A : Set S) :
isCentral A → ∃ (X : Type u) (_ : TopologicalSpace X)
(_ : CompactSpace X) (_ : T2Space X) (_ : Nonempty X)
(dSystem : DynamicalSystem S X) (x y : X) (_ : isUniformlyRecurrent dSystem y)
(_ : proximal dSystem x y) (U : Set X) (_ : y ∈ U) (_ : IsOpen U),
visitTimeSet dSystem x U = A := by
  intro hA
  obtain ⟨p,pMin,pIdemp,Ainp⟩ := hA
  letI : SemigroupHom (WithOne.coe : S → WithOne S) :=
  {
    hom_prop := fun s1 s2 ↦ WithOne.coe_mul s1 s2
  }
  let dSystemMS := homDynamicalSystem (WithOne.coe : S → WithOne S) (ultrafilterSystem (WithOne S))
  let de := (pure : WithOne S → Ultrafilter (WithOne S)) (1 : WithOne S)
  let pde := (ultraAction dSystemMS).map p de
  have deProxpde : proximal dSystemMS de pde := pointAndUltraImageAreProximal dSystemMS de pIdemp
  have pdeIsUR : isUniformlyRecurrent dSystemMS pde :=
    minUltraImageIsUniformlyRecurrent dSystemMS de pMin
  let iAbar := {q : Ultrafilter (WithOne S) | WithOne.coe '' A ∈ q}
  have visitsToiAisA : visitTimeSet dSystemMS de iAbar = A := by
    ext s
    calc
      s ∈ visitTimeSet dSystemMS de iAbar ↔ dSystemMS.map s de ∈ iAbar := Eq.to_iff rfl
      _ ↔ (pure : WithOne S → Ultrafilter (WithOne S)) (WithOne.coe s) ∈ iAbar := by
        have : dSystemMS.map s de = pure ↑s := by
          unfold de dSystemMS
          exact Ultrafilter.eq_of_le fun ⦃U⦄ a ↦ a
        rw [this]
      _ ↔ WithOne.coe s ∈ WithOne.coe '' A := by
        unfold iAbar
        exact Set.MapsTo.mem_iff (fun ⦃x⦄ a ↦ a) fun ⦃x⦄ a ↦ a
      _ ↔ s ∈ A := Function.Injective.mem_set_image WithOne.coe_injective
  have sufficient := visitTimeSetInUltraImpliesUltraActInClosure dSystemMS de iAbar p
  have iAbarclosed : iAbar = closure iAbar := by
    have := ultrafilter_isClosed_basic (WithOne.coe '' A)
    exact (closure_eq_iff_isClosed.mpr this).symm
  have iAbaropen : IsOpen iAbar := ultrafilter_isOpen_basic (WithOne.coe '' A)
  rw [←iAbarclosed] at sufficient
  have pdeIniAbar : pde ∈ iAbar := by
    apply sufficient
    rw [visitsToiAisA]
    exact Ainp
  use Ultrafilter (WithOne S)
  use by infer_instance
  use by infer_instance
  use by infer_instance
  use by infer_instance
  use dSystemMS
  use de
  use pde
  use pdeIsUR
  use deProxpde
  use iAbar

/-- If `A = R(x,U)` where `x` is proximal to an `S`-uniformly
recurrent point in the open set `U`, then `A` contains `dcS` intersect `thick` -/
theorem visitsOfPtToProxURPointAredcSCapThick
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
(∃ (X : Type*) (_ : TopologicalSpace X)
(_ : CompactSpace X) (_ : T2Space X) (_ : Nonempty X)
(dSystem : DynamicalSystem S X) (x y : X) (_ : isUniformlyRecurrent dSystem y)
(_ : proximal dSystem x y) (U : Set X) (_ : y ∈ U) (_ : IsOpen U),
visitTimeSet dSystem x U = A) → (∃ (B : Set S) (_ : isdcSSet B),
∃ (H : Set S) (_ : isThick H), B ∩ H ⊆ A) := by
  intro hA
  obtain ⟨X,Xts,Xcs,Xt2,Xnon,dSystem,x,y,yIsUR,xyProx,U,yInU,UIsOpen,visitTimesIsA⟩ := hA
  obtain ⟨V,VIsOpen,yInV,α,αIsOpen,αContainsDiag,VαProp⟩ := nbhdOfDiagForcesOtherSetContainment yInU
  let yToV := visitTimeSet dSystem y V
  use yToV
  have yToVisdcS : isdcSSet yToV := by
    apply returnTimesImpliesdcS
    use X, Xts, Xcs, Xt2, Xnon, dSystem, y, yIsUR, V, yInV, VIsOpen
  use yToVisdcS
  let xyToα := visitTimeSet (diagDynamicalSystem dSystem dSystem) ⟨x,y⟩ α
  use xyToα
  have xyToαThick : isThick xyToα :=
    proxPairVisitsDiagAlongThickSet dSystem xyProx α αIsOpen αContainsDiag
  use xyToαThick
  let xToU := visitTimeSet dSystem x U
  have visitContainment : yToV ∩ xyToα ⊆ xToU := by
    intro s ⟨hs1,hs2⟩
    apply VαProp (dSystem.map s x) (dSystem.map s y)
    · exact hs2
    · exact hs1
  rw [←visitTimesIsA]
  exact visitContainment

/-- A `dcS` subset of `S` belongs to a syndetic, idempotent filter on `S` -/
lemma dcSBelongsToSyndeticIdempotentFilter
{S : Type*} [Semigroup S] [Nonempty S] {A : Set S} (hA : isdcSSet A) :
∃ (F : Set (Set S)) (_ : F.Nonempty)
(_ : ∀ (A B : Set S), A ∈ F → B ∈ F → A ∩ B ∈ F)
(_ : ∀ (A B : Set S), A ∈ F → A ⊆ B → B ∈ F)
(_ : ∀ (A : Set S), A ∈ F → isSyndetic A)
(_ : ∀ (A : Set S), A ∈ F → {s : S | (s * ·) ⁻¹' A ∈ F} ∈ F),
A ∈ F := by --Define F to be up-closure of all R(x,U), where V is open nbhd of p
  obtain ⟨p,pMin,U,UOpen,pInU,visitsInA⟩ := hA
  let F := {B : Set S | ∃ (V : Set (Ultrafilter S)) (_ : IsOpen V)
    (_ : p ∈ V), visitTimeSet (ultrafilterSystem S) p V ⊆ B}
  use F
  have AinF : A ∈ F := by
    use U
  use Set.nonempty_of_mem AinF
  have Ffilt : ∀ (A B : Set S), A ∈ F → B ∈ F → A ∩ B ∈ F := by
    intro A B hA hB
    obtain ⟨V1,V1Open,pInV1,visitsInA⟩ := hA
    obtain ⟨V2,V2Open,pInV2,visitsInB⟩ := hB
    let V := V1 ∩ V2
    have Vopen : IsOpen V := by
      exact IsOpen.inter V1Open V2Open
    have pinV : p ∈ V := by
      exact Set.mem_inter pInV1 pInV2
    have interrw : (visitTimeSet (ultrafilterSystem S) p V1) ∩
      (visitTimeSet (ultrafilterSystem S) p V2) =
        visitTimeSet (ultrafilterSystem S) p V := by
          exact Eq.symm (Set.Subset.antisymm (fun ⦃a⦄ a_1 ↦ a_1) fun ⦃a⦄ a_1 ↦ a_1)
    have easy : (visitTimeSet (ultrafilterSystem S) p V1) ∩
      (visitTimeSet (ultrafilterSystem S) p V2) ⊆ A ∩ B := by
        exact Set.inter_subset_inter visitsInA visitsInB
    rw [interrw] at easy
    use V
  use Ffilt
  have Fup : ∀ (A B : Set S), A ∈ F → A ⊆ B → B ∈ F := by
    intro A B hA hAB
    obtain ⟨V,VOpen,pInV,visitsInA⟩ := hA
    use V
    use VOpen
    use pInV
    use subset_trans visitsInA hAB
  use Fup
  have Fsynd : ∀ A ∈ F, isSyndetic A := by
    intro A hA
    obtain ⟨V,VOpen,pInV,visitsInA⟩ := hA
    have pUR := (ultrafilterMinimalIffUnifRec p).mp pMin
    specialize pUR V (IsOpen.mem_nhds VOpen pInV)
    exact syndeticIsMonotone pUR visitsInA
  use Fsynd
  have Fidemp : ∀ A ∈ F, {s | (fun x ↦ s * x) ⁻¹' A ∈ F} ∈ F := by
    intro A hA
    obtain ⟨V,VOpen,pInV,visitsInA⟩ := hA
    have visitsinF : visitTimeSet (ultrafilterSystem S) p V ∈ F := by use V
    have visitsInpreset : visitTimeSet (ultrafilterSystem S) p V ⊆
      {s | (fun x ↦ s * x) ⁻¹' A ∈ F} := by
        intro s hs
        simp only [Set.mem_setOf_eq]
        let invV := ((ultrafilterSystem S).map s) ⁻¹' V
        have invVopen : IsOpen invV := by
          exact Continuous.isOpen_preimage ((ultrafilterSystem S).mapCont s) V VOpen
        have pininvV : p ∈ invV := by
          exact Set.mem_preimage.mpr hs
        use invV, invVopen, pininvV
        rw [← visitsToPreimages (ultrafilterSystem S) p V s]
        exact Set.preimage_mono visitsInA
    exact Fup (visitTimeSet (ultrafilterSystem S) p V)
      {s | (fun x ↦ s * x) ⁻¹' A ∈ F} visitsinF visitsInpreset
  use Fidemp

/-- Sets of the form `dcS` intersect `thick` are central -/
theorem dcSCapThickIsCentral
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
(∃ (B : Set S) (_ : isdcSSet B),
∃ (H : Set S) (_ : isThick H), B ∩ H ⊆ A) → isCentral A := by
  intro iA
  obtain ⟨B,BisdcS,H,HisThick,BcapHinA⟩ := iA
  obtain ⟨F,FNonempty,FFilter,FUpclosed,Fsyndetic,Fidemp,BinF⟩ :=
    dcSBelongsToSyndeticIdempotentFilter BisdcS
  let Fclos := ⋂ (A ∈ F), {p : Ultrafilter S | A ∈ p}
  have FclosClosed : IsClosed Fclos := by
    refine isClosed_biInter ?_
    intro A hA
    exact ultrafilter_isClosed_basic A
  have FclosCompact : IsCompact Fclos := IsClosed.isCompact FclosClosed
  have Fsubsemi : isSubsemigroup Fclos := by
    intro p hp q hq
    unfold Fclos
    apply Set.mem_iInter.mpr
    intro A hA hA2
    simp only [Set.mem_range, exists_prop] at hA2
    rw [←hA2.2]
    specialize Fidemp A hA2.1
    apply (ultraProductDescription p q A).mpr
    have : ∀ (s : S), (fun x ↦ s * x) ⁻¹' A ∈ F → (fun x ↦ s * x) ⁻¹' A ∈ q := by
      intro s hs
      unfold Fclos at hq
      have := Set.mem_iInter.mp hq ((fun x ↦ s * x) ⁻¹' A)
      have := Set.mem_iInter.mp this hs
      exact this
    have h9 : {s | (fun x ↦ s * x) ⁻¹' A ∈ F} ⊆ {s | (fun x ↦ s * x) ⁻¹' A ∈ q} := by
      exact Set.setOf_subset_setOf_of_imp this
    have h10 : {s | (fun x ↦ s * x) ⁻¹' A ∈ q} ∈ F := FUpclosed
      {s | (fun x ↦ s * x) ⁻¹' A ∈ F} {s | (fun x ↦ s * x) ⁻¹' A ∈ q} Fidemp h9
    have := Set.mem_iInter.mp hp {s | (fun x ↦ s * x) ⁻¹' A ∈ q}
    exact Set.mem_iInter.mp this h10
  obtain ⟨L,LminIdeal,LinHclos⟩ := thickClosureContainsIdeal HisThick
  let FcapL := Fclos ∩ L
  let FcapL2 := L ∩ Fclos
  have FcapL2nonempety : FcapL2.Nonempty := by
    unfold FcapL2 Fclos
    apply IsCompact.inter_iInter_nonempty
    · exact minimalLeftIdealCompact LminIdeal
    · intro A
      refine isClosed_iInter ?_
      intro AinF
      exact ultrafilter_isClosed_basic A
    · intro FiniteSubsetS
      let C := ⋂ i ∈ FiniteSubsetS, ⋂ (_ : i ∈ F), i
      let filterF : Filter S :=
      {
        sets := F
        univ_sets := by -- F is nonempty together with upclosed.
          obtain ⟨a,ha⟩ := FNonempty
          exact FUpclosed a Set.univ ha (Set.subset_univ a)
        sets_of_superset := by --FUpclosed
          intro x y hx hxy
          exact FUpclosed x y hx hxy
        inter_sets := by -- FFilter
          intro x y hx hy
          exact FFilter x y hx hy
      }
      have CinF : C ∈ F := by
        apply (Filter.mem_sets (f := filterF)).mpr
        unfold C
        refine (Filter.biInter_finset_mem (f := filterF) FiniteSubsetS).2 ?_
        intro i hi
        refine (Filter.iInter_mem (f := filterF)).2 ?_
        intro hiF
        apply Filter.mem_sets.mp
        exact hiF
      have hC : {p | C ∈ p} ⊆ -- NOTE: THIS IS AN EQUALITY BUT REVERSE IS NOT NEEDED AND IS ANNOYING
        ⋂ i ∈ FiniteSubsetS, ⋂ (_ : i ∈ F), {p : Ultrafilter S | i ∈ p} := by
          intro p
          simp only [Set.mem_iInter, Set.mem_setOf_eq]
          intro hp G hG GinF
          have : ⋂ i ∈ FiniteSubsetS, ⋂ (_ : i ∈ F), i ⊆ G := by
            apply Set.iInter_subset_of_subset G
            exact
              Set.iInter₂_subset_of_subset hG (FUpclosed G G GinF fun ⦃a⦄ a_1 ↦ a_1) fun ⦃a⦄ a_1 ↦
                a_1
          exact Filter.mem_of_superset hp this
      have : isSyndetic C := Fsyndetic C CinF
      have hsubset : (L ∩ {p | C ∈ p}) ⊆
        (L ∩ ⋂ i ∈ FiniteSubsetS, ⋂ (_ : i ∈ F), {p | i ∈ p}) := by
          exact Set.inter_subset_inter (fun ⦃a⦄ a_1 ↦ a_1) hC
      apply Set.Nonempty.mono (ht := hsubset)
      have rwclospure :
        closure ((pure : S → Ultrafilter S) '' C) = {p | C ∈ p} := by
          rw [superset_antisymm_iff]
          constructor
          · intro p hp
            rw [TopologicalSpace.IsTopologicalBasis.mem_closure_iff ultrafilterBasis_is_basis]
            intro U hU pinU
            obtain ⟨E,hE⟩ := hU
            have CcapEinp : C ∩ E ∈ p := by
              rw [←hE] at pinU
              simp only [Set.mem_setOf_eq] at pinU
              simp only [Set.mem_setOf_eq] at hp
              exact Filter.inter_mem hp pinU
            obtain ⟨t,htC,htE⟩ := Ultrafilter.nonempty_of_mem CcapEinp
            have ptinU : pure t ∈ U := by
              rw [←hE]
              exact Set.mem_setOf.mpr htE
            have ptinC : pure t ∈ (pure : S → Ultrafilter S) '' C := by
              exact Set.mem_image_of_mem pure htC
            use pure t
            exact ⟨ptinU,ptinC⟩
          · apply closure_minimal
            · intro d hd
              obtain ⟨s,hs1,hs2⟩ := hd
              exact Set.mem_of_eq_of_mem (id (Eq.symm hs2)) hs1
            · exact ultrafilter_isClosed_basic C
      rw [←rwclospure]
      exact syndeticClosureMeetsEveryIdeal this L LminIdeal.1
  have FcapLnonempty : FcapL.Nonempty := Set.inter_nonempty_iff_exists_right.mpr FcapL2nonempety
  have FcapLcompact : IsCompact FcapL := by
    have := minimalLeftIdealCompact LminIdeal
    exact IsCompact.inter_left this FclosClosed
  have FcapLsubsemi: isSubsemigroup FcapL := by
    intro p hp q hq
    refine ⟨?_,?_⟩
    · exact Fsubsemi p hp.1 q hq.1
    · have := LminIdeal.1.2 p
      apply this
      exact Set.mem_image_of_mem (fun x ↦ p * x) hq.2
  obtain ⟨p,pInFcapL,pIdemp⟩ := compactSubsemigroupContainsIdempotent FcapL
    (hTsemi := FcapLsubsemi) (hTcompact := FcapLcompact) (hTnonempty := FcapLnonempty)
  have BcapHinp : B ∩ H ∈ p := by
    have := Set.mem_iInter.mp pInFcapL.1 B
    have BinP := Set.mem_iInter.mp this BinF
    have pinHclos : p ∈ closure (pure '' H) := LinHclos pInFcapL.2
    have HinP : H ∈ p := by
      exact (memClosurePureIff H p).mp pinHclos
    exact Filter.inter_mem BinP HinP
  have Ainp : A ∈ p := by
    exact Filter.mem_of_superset BcapHinp BcapHinA
  have pMin : isMinimalUltrafilter p := by
    use L
    constructor
    · exact LminIdeal
    · exact pInFcapL.2
  use p, pMin, pIdemp


end central_sets

section Bohr_prelims

/- ChatGPT helped me write the following -/

theorem existsTwoSidedInvInCompactSubmonoid
{T : Type*} [Monoid T] [TopologicalSpace T] [T2Space T] [ContinuousMul T]
(S : Submonoid T) (hSComp : IsCompact (S : Set T))
(hSIdemp : ∀ (x : S), x * x = x → x = 1) :
∀ (x : S), ∃ (y : S), (x * y = 1) ∧ (y * x = 1) := by sorry

noncomputable
def invFromCompactSubmonoid
{T : Type*} [Monoid T] [TopologicalSpace T] [T2Space T] [ContinuousMul T]
(S : Submonoid T) (hSComp : IsCompact (S : Set T))
(hSIdemp : ∀ (x : S), x * x = x → x = 1) :
Inv S :=
{
  inv x :=
  Classical.choose
    (existsTwoSidedInvInCompactSubmonoid S hSComp hSIdemp x)
}

noncomputable
def groupFromCompactSubmonoid
{T : Type*} [Monoid T] [TopologicalSpace T] [T2Space T] [ContinuousMul T]
(S : Submonoid T) (hSComp : IsCompact (S : Set T))
(hSIdemp : ∀ (x : S), x * x = x → x = 1) :
Group S := by
letI : Inv S := invFromCompactSubmonoid S hSComp hSIdemp
exact Group.ofLeftAxioms
  mul_assoc
  one_mul
  (by
    intro x
    exact
      (Classical.choose_spec
        (existsTwoSidedInvInCompactSubmonoid S hSComp hSIdemp x)).2)

-- Should this be theorem or instance?
theorem groupFromCompactSubmonoidHasContinuousInv
{T : Type*} [Monoid T] [TopologicalSpace T] [T2Space T] [ContinuousMul T]
(S : Submonoid T) (hSComp : IsCompact (S : Set T))
(hSIdemp : ∀ (x : S), x * x = x → x = 1) :
letI : Group S := groupFromCompactSubmonoid S hSComp hSIdemp
ContinuousInv S := by sorry


theorem groupFromCompactSubmonoidIsTopologicalGroup
{T : Type*} [Monoid T] [TopologicalSpace T] [T2Space T] [ContinuousMul T]
(S : Submonoid T) (hSComp : IsCompact (S : Set T))
(hSIdemp : ∀ (x : S), x * x = x → x = 1) :
letI : Group S := groupFromCompactSubmonoid S hSComp hSIdemp
IsTopologicalGroup S := by sorry



/-
theorem hausGroupSuffCondition
{T : Type*} [Monoid T] [TopologicalSpace T] [T2Space T]
{topSemi : Continuous fun (⟨s,t⟩ : T × T) ↦ s * t}
{S : Set T} [CompactSpace S] {subSemi : ∀ (s t : T), s ∈ S → t ∈ S → s * t ∈ S} :
1 ∈ S → (∀ (s : T), s ∈ S → s * s = s → s = 1) →
-/
-- IsCompact S ∧ IsT2Space S ∧
-- formulate: "is compact Hausdorff topological group with identity 1"

-- theorem: if A ⊆ C(X,X) consists of surjections, then so does its closure

-- theorem: if S ⊆ C(X,X) is a subsemigroup, then so is its closure

-- theorem: if S ⊆ C(X,X) is a subsemigroup and consists of surjections,
-- then any idempotent it contains is equal to Id_X

-- def: given S ⊆ C(X,X) is a subsemigroup consists of surjections with,
-- overline S compact, get group (overline S) with 1 = id_X

-- theorem: if the maps in A ⊆ C(X,X) commute, then the maps in its closure commute

-- def: given S ⊆ C(X,X) is a commutative subsemigroup consists of surjections with,
-- overline S compact, get commgroup (overline S)

-- theorem: given S ⊆ C(X,X) is a commutative subsemigroup consists of surjections with,
-- overline S compact, get ContinuousInv (overline S)

-- theorem: given S ⊆ C(X,X) is a commutative subsemigroup consists of surjections with,
-- overline S compact, get IsTopologicalGroup (overline S)

noncomputable
def commGroupFromSurjectiveSubsemiOfCXX
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{S : Set (ContinuousMap.End X)}
(hSsurject : ∀ (ϕ : (ContinuousMap.End X)), ϕ ∈ S → Function.Surjective ϕ)
(hSsubsemi : Subsemigroup (ContinuousMap.End X))
(hScomm : ∀ (ϕ ψ : (ContinuousMap.End X)), ϕ ∈ S → ψ ∈ S → ϕ * ψ = ψ * ϕ)
(hScompactclos : IsCompact (closure S)) :
CommGroup (closure S) := by sorry

theorem isTopologicalGroupFromSurjectiveSubsemiOfCXX
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{S : Set (ContinuousMap.End X)}
(hSsurject : ∀ (ϕ : (ContinuousMap.End X)), ϕ ∈ S → Function.Surjective ϕ)
(hSsubsemi : Subsemigroup (ContinuousMap.End X))
(hScomm : ∀ (ϕ ψ : (ContinuousMap.End X)), ϕ ∈ S → ψ ∈ S → ϕ * ψ = ψ * ϕ)
(hScompactclos : IsCompact (closure S)) :
letI : CommGroup (closure S) := commGroupFromSurjectiveSubsemiOfCXX hSsurject hSsubsemi hScomm hScompactclos
IsTopologicalGroup (closure S) := by sorry

end Bohr_prelims


section Bohr_sets

/-- A subset `A ⊆ S` is Bohr_0 if there exists a semigroup homomorphism
`ϕ : S → T^d` and an open set `U ⊆ T^d` containing `0` such that `A ⊇ ϕ ⁻¹ U`. -/
def isBohrZero
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop := ∃ (d : ℕ) (φ : S → (Fin d → UnitAddCircle))
  (_ : ∀ (s t : S), φ (s * t) = (φ s) + (φ t)) (U : Set (Fin d → UnitAddCircle))
  (_ : IsOpen U) (_ : 0 ∈ U),
  Set.preimage φ U ⊆ A

/-- If `A ⊆ S` is Bohr_0 and `A ⊆ B`, then `B` is Bohr_0. -/
theorem bohrZeroIsMonotone
{S : Type*} [Semigroup S] [Nonempty S]
{A B : Set S} (hA : isBohrZero A) (hAB : A ⊆ B) :
isBohrZero B := by
unfold isBohrZero
unfold isBohrZero at hA
rcases hA with ⟨k, φ, h1, h2, h3, h4, h5⟩
use k
use φ
use h1
use h2
use h3
use h4
apply Set.Subset.trans h5 hAB

/-- The family of Bohr_0 subsets of a semigroup -/
def bohrZeroFamily
(S : Type*) [Semigroup S] [Nonempty S] : Family S :=
{
  sets := {A : Set S | isBohrZero A}
  upward_closed := by
    intro A B hA hAB
    exact bohrZeroIsMonotone hA hAB
}

/-- The `d`-torus acting on itself.  Note that UnitAddCircle is AddCommGroup,
but we require that the acting semigroup in DynamicalSystem is multiplicative,
hence the conversion -/
def torusDynamicalSystem
(d : ℕ) :
DynamicalSystem (Multiplicative (Fin d → UnitAddCircle)) (Fin d → UnitAddCircle) :=
by sorry

theorem torusDSIsEquicontinuous
(d : ℕ) :
isEquicontinuousSystem (torusDynamicalSystem d) :=
by sorry

theorem dynamicalBohrZeroCharacterization
{S : Type*} [CommSemigroup S] [Nonempty S] (A : Set S) :
isBohrZero A ↔ ∃ (X : Type*) (_ : TopologicalSpace X)
(_ : CompactSpace X) (_ : T2Space X) (_ : Nonempty X)
(dSystem : DynamicalSystem S X) (_ : isEquicontinuousSystem dSystem)
(_ : isMinimalSystem dSystem) (x : X) (U : Set X) (xInU : x ∈ U) (_ : IsOpen U),
visitTimeSet dSystem x U ⊆ A :=
by
  constructor
  · intro hBZA
    obtain ⟨d,φ,φHom,U,UisOpen,zeroInU,preimageUinA⟩ := hBZA
    let ψ : S → Multiplicative (Fin d → UnitAddCircle) := fun (s : S) ↦ φ s
    letI : SemigroupHom ψ := by sorry -- use φHom
    let homTorusDS := homDynamicalSystem ψ (torusDynamicalSystem d)
    have homTorusDSisEqui := homSystemOfEquicontinuousSystemIsEquicontinuous ψ (torusDSIsEquicontinuous d)
    let x : Fin d → UnitAddCircle := 0
    let X := orbitClosure (homDynamicalSystem ψ (torusDynamicalSystem d)) x
    let V := {z : X | z.1 ∈ U}
    have orbClosPresystem := orbitClosureIsNonemptyCompactT2InvariantSubset homTorusDS x
    let dSystem := fromNonemptyCompactT2InvariantSubsetToSystem homTorusDS orbClosPresystem
    letI : CompactSpace ↑(orbitClosure homTorusDS x) := by sorry
    letI : Nonempty ↑(orbitClosure homTorusDS x) := by sorry
    have xInX : x ∈ X := by sorry -- A UR point is in its orbit closure
    have hMin : isMinimalSystem dSystem := by sorry -- orbit closure of UR point is minimal
    have hEqui : isEquicontinuousSystem dSystem := by sorry --
    have VisOpen : IsOpen V := by sorry -- V is relatively open in X
    have xInV : ⟨x,xInX⟩ ∈ V := by sorry
    have visitTimesxToVinA : visitTimeSet dSystem ⟨x,xInX⟩ V ⊆ A := by sorry
    use ULift X
    sorry
  · sorry

/- A set `A ⊆ S` is Bohr_0 if there exists a minimal, equicontinuous
action of `S` on a compact, Hausdorff space `X`, a point `x ∈ X` and
a neighborhood `U` of `x` such that `R(x,U) ⊆ A` -/
/-
def isBohrZero_old
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
--∃ (n : ℕ), ∃ (X : Type n), 1+1=2
∃ (X : Type*) (_ : TopologicalSpace X)
(_ : CompactSpace X) (_ : T2Space X) (_ : Nonempty X)
(dSystem : DynamicalSystem S X) (_ : isEquicontinuousSystem dSystem)
(x : X) (U : Set X) (_ : IsOpen U),
visitTimeSet dSystem x U ⊆ A
-/

/-
def isBohrZerov2_old
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S)
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (_ : isEquicontinuousSystem dSystem) :
Prop :=
∃ (x : X) (U : Set X) (_ : IsOpen U),
visitTimeSet dSystem x U ⊆ A
-/

-- The family of Bohr_0 subsets of a semigroup
/- def bohrZeroFamily
(S : Type*) [Semigroup S] [Nonempty S] : Family S :=
{
  sets := {A : Set S | ∃ (X : Type*) (_ : TopologicalSpace X)
(_ : CompactSpace X) (_ : T2Space X) (_ : Nonempty X)
(dSystem : DynamicalSystem S X) (_ : isEquicontinuousSystem dSystem)
(x : X) (U : Set X) (_ : IsOpen U),
visitTimeSet dSystem x U ⊆ A}
  upward_closed := by
    intro A B hA hAB
    exact bohrZeroIsMonotone hA hAB
}
-/

/-- A set `A ⊆ S` is a set of Bohr recurrence if for all minimal, equicontinuous
actions of `S` on a compact, Hausdorff space `X`, all points `x ∈ X` and
all neighborhoods `U` of `x`, `A ∩ R(x,U) ≠ ∅` -/
def isSetOfBohrRecurrence
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
by sorry

/-- If `A ⊆ S` is a set of Bohr recurrence and `A ⊆ B`, then `B`
is a set of Bohr recurrence. -/
theorem setOfBohrRecurrenceIsMonotone
{S : Type*} [Semigroup S] [Nonempty S]
{A B : Set S} (hA : isSetOfBohrRecurrence A) (hAB : A ⊆ B) :
isSetOfBohrRecurrence B :=
by sorry

/-- The family of Bohr_0 subsets of a semigroup -/
def setOfBohrRecurrenceFamily
(S : Type*) [Semigroup S] [Nonempty S] : Family S :=
{
  sets := {A : Set S | isSetOfBohrRecurrence A}
  upward_closed := by
    intro A B hA hAB
    exact setOfBohrRecurrenceIsMonotone hA hAB
}

theorem bohrZeroiffCompNotSetOfRec
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
isSetOfBohrRecurrence A ↔ ¬(isBohrZero Aᶜ) :=
  by sorry
  -- This should be easy logical consequence of the definitions

/-- The families of Bohr_0 sets and sets of Bohr recurrence are dual -/
-- Something happens upstream regarding "dualEquivForm" that the proof no longer work
-- Need to fix
theorem dualBohrZeroSetsOfBohrRecurrence
{S : Type*} [Semigroup S] [Nonempty S] :
(bohrZeroFamily S)* = (setOfBohrRecurrenceFamily S) :=
by sorry
  -- ext A
  -- have dualEquivForm : ((bohrZeroFamily S)*).sets = {A : Set S | Aᶜ ∉ bohrZeroFamily S} :=
  --   famDualAlt (bohrZeroFamily S)
  -- rw [dualEquivForm]
  -- change A ∈ {A | Aᶜ ∉ (bohrZeroFamily S).sets} ↔ A ∈ (setOfBohrRecurrenceFamily S).sets
  -- unfold bohrZeroFamily
  -- unfold setOfBohrRecurrenceFamily
  -- simp only [Set.mem_setOf_eq]
  -- exact Iff.symm (bohrZeroiffCompNotSetOfRec A)

/- In a commutative semigroup, the family of Bohr_0 sets is a filter -/
theorem commBohrZeroFamilyIsFilter
{S : Type*} [CommSemigroup S] [Nonempty S] :
isFilterFamily (bohrZeroFamily S) :=
by sorry

/- In a commutative semigroup, the family of sets of Bohr
recurrence is partition regular -/
theorem commSetOfBohrRecurrenceFamilyIsPR
{S : Type*} [CommSemigroup S][Nonempty S] :
isPRFamily (setOfBohrRecurrenceFamily S) :=
by sorry

/-- In a commutative semigroup, a Delta_0 set is a set of Bohr recurrence -/
theorem commDeltaZeroImpliesSetOfBohrRecurrence
{S : Type*} [CommSemigroup S] [Nonempty S] :
deltaZeroFamily S ⊆ setOfBohrRecurrenceFamily S :=
by sorry


end Bohr_sets
