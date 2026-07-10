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

-- The definition of syndetic (`isSyndetic`) is in the _02_Semigroups file

/-- A set `A ⊆ S` is thick if for all finite subsets `F ⊆ S`,
there exists `s ∈ S` such that `Fs ⊆ A` -/
def isThick
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∀ F : Set S, F.Finite → ∃ s : S, (· * s) '' F ⊆ A

/-- If `A ⊆ S` is thick and `A ⊆ B`, then `B` is thick. -/
theorem thickIsMonotone
{S : Type*} [Semigroup S] [Nonempty S]
{A B : Set S} (hSA : isThick A) (hAB : A ⊆ B) :
isThick B :=
by
  intro F FFinite
  specialize hSA F FFinite
  rcases hSA with ⟨s,hSA⟩
  use s
  exact hSA.trans hAB

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


section Bohr_sets

/-- A set `A ⊆ S` is Bohr_0 if there exists a minimal, equicontinuous
action of `S` on a compact, Hausdorff space `X`, a point `x ∈ X` and
a neighborhood `U` of `x` such that `R(x,U) ⊆ A` -/
def isBohrZero
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
--∃ (n : ℕ), ∃ (X : Type n), 1+1=2
∃ (X : Type*) (_ : TopologicalSpace X)
(_ : CompactSpace X) (_ : T2Space X) (_ : Nonempty X)
(dSystem : DynamicalSystem S X) (_ : isEquicontinuousSystem dSystem)
(x : X) (U : Set X) (_ : IsOpen U),
visitTimeSet dSystem x U ⊆ A

def isBohrZerov2
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S)
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (_ : isEquicontinuousSystem dSystem) :
Prop :=
∃ (x : X) (U : Set X) (_ : IsOpen U),
visitTimeSet dSystem x U ⊆ A

/- theorem [Semigroup S] : \exists X : Type*,
\forall A : Set S, \forall Y : Type*, isBohrZero X A \iff isBohrZero Y A -/

/-- If `A ⊆ S` is Bohr_0 and `A ⊆ B`, then `B` is Bohr_0. -/
theorem bohrZeroIsMonotone
{S : Type*} [Semigroup S] [Nonempty S]
{A B : Set S} (hA : isBohrZero A) (hAB : A ⊆ B) :
isBohrZero B := by
sorry

-- The family of Bohr_0 subsets of a semigroup
/- def bohrZeroFamily
(S : Type*) [Semigroup S] [Nonempty S] : Family S :=
{
  sets := {A : Set S | isBohrZero A}
  upward_closed := by
    intro A B hA hAB
    exact bohrZeroIsMonotone hA hAB
} -/

-- The family of Bohr_0 subsets of a semigroup
def bohrZeroFamily
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
