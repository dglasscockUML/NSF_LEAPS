import NSFLEAPS._03_Family_algebra.FA_Theorems
import NSFLEAPS._05_Ultrafilters.UF_Defs

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
simp at h1
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
    apply h
    apply hUV_visitTime
  exact hV2 hV3
choose f hf using h2
sorry

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

/-- The ultrafilter closure of a thick subset of a semigroup
contains a minimal left ideal -/
theorem thickClosureContainsIdeal
{S : Type*} [Semigroup S] [Nonempty S]
(H : Set S) {hH : isThick H} :
∃ (L : Set (Ultrafilter S)),
isMinLeftIdeal L ∧ L ⊆ closure ((pure : S → Ultrafilter S) '' H) :=
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
(dSystem : DynamicalSystem S X) (x : X) (xUR : isUniformlyRecurrent dSystem x)
(U : Set X) (_ : x ∈ U) (_ : IsOpen U),
visitTimeSet dSystem x U ⊆ A) → isdcSSet A := by sorry
/- Rewrite this proof.  It was originally for minimal systems.  Now I want
it for UR points.
  intro hA
  obtain ⟨X,_,_,_,_,dSystem,hMin,x,U,xInU,Uopen,AhasVisits⟩ := hA
  let fmap := fun p ↦ (ultraAction dSystem).map p x
  have uFactorMap : isFactorMap (ultrafilterSystem S) dSystem fmap :=
    ultraFactorMap dSystem ((minimalIffDenseOrbits dSystem).mp hMin x)
  obtain ⟨p,hp,pUR⟩ :=liftUniformRecurrentPoint
    uFactorMap x (minimalImpliesUniformlyRecurrent dSystem (hMin := hMin) x)
  use p
  use (ultrafilterMinimalIffUnifRec p).mpr pUR
  use fmap ⁻¹' U
  use Continuous.isOpen_preimage uFactorMap.1 U Uopen
  have fmappinU : fmap p ∈ U := by
    rw [hp]
    exact xInU
  use fmappinU
  have preimageVisits := visitTimesThruFactorMap uFactorMap p U
  rw [hp] at preimageVisits
  rw [preimageVisits]
  exact AhasVisits
-/

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
(dSystem : DynamicalSystem S X) (x y : X) (hy : isUniformlyRecurrent dSystem y)
(hprox : proximal dSystem x y) (U : Set X) (yInU : y ∈ U) (_ : IsOpen U),
visitTimeSet dSystem x U ⊆ A := by sorry


/-- If `A = R(x,U)` where `x` is proximal to an `S`-uniformly
recurrent point in the open set `U`, then `A` contains `dcS` intersect `thick` -/
theorem visitsOfPtToProxURPointAredcSCapThick
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
(∃ (X : Type*) (_ : TopologicalSpace X)
(_ : CompactSpace X) (_ : T2Space X) (_ : Nonempty X)
(dSystem : DynamicalSystem S X) (x y : X) (_ : isUniformlyRecurrent dSystem y)
(_ : proximal dSystem x y) (U : Set X) (_ : y ∈ U) (_ : IsOpen U),
visitTimeSet dSystem x U ⊆ A) → (∃ (B : Set S) (_ : isdcSSet B),
∃ (H : Set S) (_ : isThick H), B ∩ H ⊆ A) := by
  intro hA
  obtain ⟨X,Xts,Xcs,Xt2,Xnon,dSystem,x,y,yIsUR,xyProx,U,yInU,UIsOpen,visitTimesInA⟩ := hA
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
  exact Set.Subset.trans visitContainment visitTimesInA


/-- Sets of the form `dcS` intersect `thick` are central -/
theorem dcSCapThickIsCentral
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
(∃ (B : Set S) (_ : isdcSSet B),
∃ (H : Set S) (_ : isThick H), B ∩ H ⊆ A) → isCentral A := by sorry


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

-- def compactCommSubsemiOfCXXIsSubmonoid
-- {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
-- {S : Subsemigroup }


/-
theorem hausGroupSuffCondition
{T : Type*} [Monoid T] [TopologicalSpace T] [T2Space T]
{topSemi : Continuous fun (⟨s,t⟩ : T × T) ↦ s * t}
{S : Set T} [CompactSpace S] {subSemi : ∀ (s t : T), s ∈ S → t ∈ S → s * t ∈ S} :
1 ∈ S → (∀ (s : T), s ∈ S → s * s = s → s = 1) →
-/
-- IsCompact S ∧ IsT2Space S ∧
-- formulate: "is compact Hausdorff topological group with identity 1"


end Bohr_prelims


section Bohr_sets

def isBohrZero
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop := ∃ (k : ℕ) (φ : S → (Fin k → UnitAddCircle))
  (_ : ∀ (s t : S), φ (s * t) = (φ s) + (φ t)) (U : Set (Fin k → UnitAddCircle))
  (_ : IsOpen U) (_ : 0 ∈ U),
  Set.preimage φ U ⊆ A

/-- If `A ⊆ S` is Bohr_0 and `A ⊆ B`, then `B` is Bohr_0. -/
theorem bohrZeroIsMonotone
{S : Type*} [Semigroup S] [Nonempty S]
{A B : Set S} (hA : isBohrZero A) (hAB : A ⊆ B) :
isBohrZero B := by
sorry

/-- The family of Bohr_0 subsets of a semigroup -/
def bohrZeroFamily
(S : Type*) [Semigroup S] [Nonempty S] : Family S :=
{
  sets := {A : Set S | isBohrZero A}
  upward_closed := by
    intro A B hA hAB
    exact bohrZeroIsMonotone hA hAB
}


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
    unfold isBohrZero at hBZA
    -- X will be type Set (Fin k → UnitAddCircle)
    -- This type will be in Type, so in Type u_2 ??
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
