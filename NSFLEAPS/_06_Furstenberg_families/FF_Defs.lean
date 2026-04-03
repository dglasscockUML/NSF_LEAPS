import NSFLEAPS._03_Family_algebra.FA_Theorems -- Family_algebra has two files.  We need to import the later one.
import NSFLEAPS._04_Dynamical_systems.DS_Defs

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

-- There is an easier way to do this one (and others like it).
-- Prove: A syndetic iff Aᶜ is not thick.
-- Then: apply thm_equiv_dual_formulation.
/-- Syndetic and thick families are dual -/
theorem dualSyndeticThick
{S : Type*} [Semigroup S] [Nonempty S] :
(syndeticFamily S)* = (thickFamily S) :=
by
  ext A
  constructor
  · contrapose
    intro AnotThick
    unfold thickFamily at AnotThick
    simp only [Set.mem_setOf_eq] at AnotThick
    unfold isThick at AnotThick
    simp only [Set.image_subset_iff, not_forall, not_exists] at AnotThick
    rcases AnotThick with ⟨F,FFinite,AnotThick⟩
    have AcompIsSyndetic : isSyndetic Aᶜ := by
      unfold isSyndetic
      use F
      constructor
      · exact FFinite
      · intro s
        specialize AnotThick s
        simp only [Set.not_subset] at AnotThick
        exact AnotThick
    --simp only [↑thm_equiv_dual_formulation]
    --simp only [Set.mem_setf_eq, not_not]
    --exact AcompIsSyndetic
    sorry

  · intro AisThick B BisSyndetic
    unfold thickFamily isThick at AisThick
    unfold syndeticFamily isSyndetic at BisSyndetic
    rcases BisSyndetic with ⟨F, Ffinite, BisSyndetic⟩
    specialize AisThick F Ffinite
    rcases AisThick with ⟨s, sMapsFintoA⟩
    specialize BisSyndetic s
    rcases BisSyndetic with ⟨f,fInF,fTimessinB⟩
    have fstarsInImage : f * s ∈ (fun x ↦ x * s) '' F := by
      exact Set.mem_image_of_mem (fun x ↦ x * s) fInF
    exact Set.nonempty_of_mem ⟨sMapsFintoA fstarsInImage, fTimessinB⟩

/-- Image of a syndetic set under a surjective semigroup homomorphism is syndetic -/
theorem surjImgOfSyndeticIsSyndetic
{S} [Semigroup S] [Nonempty S]
{T} [Semigroup T] [Nonempty T]
(φ : S → T) [hSemiHom : SemigroupHom φ] {hSurj : Function.Surjective φ}
(A : Set S) {hA : isSyndetic A} :
isSyndetic (φ '' A) := by
obtain ⟨F, hF1, hF2⟩ := hA
use φ '' F
constructor
· apply hF1.image φ
intro t
obtain ⟨s, hs⟩ := hSurj t
specialize hF2 s
obtain ⟨e, he1, he2⟩ := hF2
use φ (e)
constructor
· simp only [Set.mem_image]
  · use e
rw [<- hs]
rw [<- hSemiHom.hom_prop]
simp only [Set.mem_image]
use e * s

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

theorem commDilateCapOfThickIsThick
{S} [CommSemigroup S] [Nonempty S]
(A : Set S) {hA : isThick A}
(K : Set S) {KIsFinite : K.Finite} :
isThick (⋂ k ∈ K, (k * ·) '' A) :=
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
isDeltaZero B :=
by sorry

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
isDelta B :=
by sorry

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
deltaFamily S ⊆ deltaZeroFamily S :=
by sorry

end Delta_sets


section Bohr_sets

/-- A set `A ⊆ S` is Bohr_0 if there exists a minimal, equicontinuous
action of `S` on a compact, Hausdorff space `X`, a point `x ∈ X` and
a neighborhood `U` of `x` such that `R(x,U) ⊆ A` -/
def isBohrZero
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop := sorry
/- ∃ (X : Type*) (_ : TopologicalSpace X) (_ : CompactSpace X) (_ : T2Space X) (_ : Nonempty X)
(dSystem : DynamicalSystem S X) (_ : isEquicontinuousSystem dSystem)
(x : X) (U : Set X) (_ : IsOpen U),
visitTimeSet dSystem x U ⊆ A
 -/
/-- If `A ⊆ S` is Bohr_0 and `A ⊆ B`, then `B` is Bohr_0. -/
theorem bohrZeroIsMonotone
{S : Type*} [Semigroup S] [Nonempty S]
{A B : Set S} (hA : isBohrZero A) (hAB : A ⊆ B) :
isBohrZero B :=
by sorry

-- The family of Bohr_0 subsets of a semigroup
def bohrZeroFamily
(S : Type*) [Semigroup S] [Nonempty S] : Family S :=
{
  sets := {A : Set S | isBohrZero A}
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
isBohrZero A ↔ ¬ (isSetOfBohrRecurrence Aᶜ) :=
  by sorry
  -- This should be easy logical consequence of the definitions

/-- The families of Bohr_0 sets and sets of Bohr recurrence are dual -/
theorem dualBohrZeroSetsOfBohrRecurrence
{S : Type*} [Semigroup S] [Nonempty S] :
(bohrZeroFamily S)* = (setOfBohrRecurrenceFamily S) :=
  by sorry
  -- Combine thm_equiv_dual_formulation and bohrZeroiffCompNotSetOfRec

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
