import NSFLEAPS._00_Imports.IM_Base

/-! This is a module docstring. -/

-- We may want to assume [Nonempty S] throughout, but I've not implemented that yet.

structure SemigroupLeftIdeal
(S : Type*) [Semigroup S] where
  carrier : Set S
  nonempty' : carrier.Nonempty
  mul_closed' (s : S) {x : S} : x ∈ carrier → s * x ∈ carrier

/-- isLeftIdeal is the predicate that `L` is a left ideal of a semigroup `S` -/
def isLeftIdeal
{S : Type*} [Semigroup S] (L : Set S) :
Prop :=
L.Nonempty ∧ (∀ (s : S), ((fun x ↦ s * x) '' L ⊆ L))

/-- A non-empty intersection of left ideals of a semigroup `S` is a left ideal -/
theorem nonemptyInterOfLeftIdealsIsLeftIdeal
{S : Type*} [Semigroup S]
{i : Set (Set S)} (h : ∀ (L : Set S), L ∈ i → isLeftIdeal L) :
(⋂₀ i).Nonempty → isLeftIdeal (⋂₀ i) :=
by
  intro hNonempty
  constructor
  · exact hNonempty
  · intro s
    simp only [Set.image]
    intro x hx
    rcases hx with ⟨a, ha1, ha2⟩
    simp only [← ha2]
    have inAllL : ∀ L ∈ i, s * a ∈ L := by
      intro L LinI
      have multsImageInL : (fun x ↦ s * x) '' L ⊆ L := by exact (h L LinI).2 s
      have sTimesainImage : s * a ∈ (fun x ↦ s * x) '' L := by
        simp only [Set.image]
        rw [← Set.sInf_eq_sInter] at ha1
        simp only [sInf] at ha1
        have aInL : a ∈ L := ha1 L LinI
        use a
      exact multsImageInL sTimesainImage
    rw [← Set.sInf_eq_sInter]
    simp only [sInf]
    intro L LinI
    exact inAllL L LinI

/-- isMinLeftIdeal is the predicate that `L` is a minimal left ideal of a semigroup `S` -/
def isMinLeftIdeal
{S : Type*} [Semigroup S] (L : Set S) :
Prop :=
isLeftIdeal L ∧ (∀ (M : Set S), isLeftIdeal M → M ⊆ L → M = L)


/-- isSubsemigroup is the predicate that `T` is a subsemigroup of a semigroup `S` -/
def isSubsemigroup
{S : Type*} [Semigroup S] (T : Set S) :
Prop :=
∀ s ∈ T, ∀ t ∈ T, s * t ∈ T

/- Definition of syndetic from Hindman-Strauss, Def. 4.38
Why I used finite sets instead of finsets:
Building a finset requires a proof of dupliates, which is annoying
We don't care about possible duplicates, so finite sets are enough -/

/-- A subset A of a semigroup S is syndetic if there is a finite subset F of S such that
every element of S can be multiplied on the left by F to land in A -/
def isSyndetic
{S : Type*} [Semigroup S] (A : Set S) :
Prop :=
∃ F : Set S, F.Finite ∧ (∀ s : S, ∃ f ∈ F, f * s ∈ A)

/-- If `A ⊆ S` is syndetic and `A ⊆ B`, then `B` is syndetic. -/
theorem syndeticIsMonotone
{S : Type*} [Semigroup S]
{A B : Set S} (hSA : isSyndetic A) (hAB : A ⊆ B) :
isSyndetic B :=
by
  unfold isSyndetic at hSA
  rcases hSA with ⟨F, Ffinite, hF⟩
  use F
  constructor
  · exact Ffinite
  · intro s
    rcases (hF s) with ⟨f, finF, fsinA⟩
    use f
    constructor
    · exact finF
    · exact hAB fsinA

/- Still not sure we want to pursue this route,
but it would make sense to define class Syndetic as follows. -/
class Syndetic
{S : Type*} [Semigroup S] (A : Set S) where
  syndetic_prop : ∃ F : Set S, F.Finite ∧ (∀ s : S, ∃ f ∈ F, f * s ∈ A)

/-- If `A ⊆ S` is syndetic and `A ⊆ B`, then `B` is syndetic. -/
theorem syndeticIsMonotonev2
{S : Type*} [Semigroup S]
{A B : Set S} [hSA : Syndetic A] (hAB : A ⊆ B) :
Syndetic B :=
by
  rcases hSA.syndetic_prop with ⟨F, Ffinite, hF⟩
  use F
  constructor
  · exact Ffinite
  · intro s
    rcases (hF s) with ⟨f, finF, fsinA⟩
    use f
    constructor
    · exact finF
    · exact hAB fsinA


class SemigroupHom
{S T} [Semigroup S] [Semigroup T] (φ : S → T) where
  hom_prop : ∀ (s1 s2 : S), φ (s1 * s2) = (φ s1) * (φ s2)

/- A semigroup action is an action by a semigroup `S` on a set `X` -/
/-structure SemigroupAction
(S : Type*) [Semigroup S] [Nonempty S]
(X : Type*) [Nonempty X] where
  toFun : S → X → X
  map_mult' : ∀ s₁ s₂ x, toFun (s₁ * s₂) x = toFun s₁ (toFun s₂ x)-/

/-- Image of a syndetic set under a surjective semigroup homomorphism is syndetic -/
theorem surjImgOfSyndeticIsSyndetic
{S} [Semigroup S] [Nonempty S]
{T} [Semigroup T] [Nonempty T]
(φ : S → T) [hSemiHom : SemigroupHom φ] (hSurj : Function.Surjective φ)
{A : Set S} (hA : isSyndetic A) :
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

/-- Shift of a syndetic set is syndetic -/
lemma shiftSyndeticIsSyndetic
{S} [Semigroup S] [Nonempty S]
{A : Set S} (hA : isSyndetic A)
{s : S} : isSyndetic ((s * · ) '' A) := by
  obtain ⟨F, hF1, hF2⟩ := hA
  unfold isSyndetic
  let E :=  (s * ·) '' F
  use E
  constructor
  · apply Set.Finite.image
    apply hF1
  intro r
  specialize hF2 r
  obtain ⟨f, hf1, hf2⟩ := hF2
  use s * f
  constructor
  · unfold E
    simp only [Set.mem_image]
    use f
  simp only [Set.mem_image]
  use f * r
  constructor
  · exact hf2
  simp only [mul_assoc]

/-- A syndetic set in a semigroup is not empty -/
lemma syndeticSetIsNonEmpty {S} [Semigroup S] [hSNonempty : Nonempty S]
{A : Set S} (hA : isSyndetic A) : A.Nonempty := by
  rcases hSNonempty with ⟨s⟩
  obtain ⟨F, hF1, hF2⟩ := hA
  specialize hF2 s
  obtain ⟨f, hf1, hf2⟩ := hF2
  exact ⟨f * s, hf2⟩

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

/-- Every syndetic set and every thick set intersects -/
lemma syndeticThickIntersect
{S : Type*} [Semigroup S] [Nonempty S]
(A B : Set S)
(hASyndetic : isSyndetic A)
(hBThick : isThick B) :
(A ∩ B).Nonempty := by
  unfold isSyndetic at hASyndetic
  unfold isThick at hBThick
  rcases hASyndetic with ⟨F, hF1, hF2⟩
  specialize hBThick F hF1
  rcases hBThick with ⟨s, hs⟩
  specialize hF2 s
  rcases hF2 with ⟨f, hf1, hf2⟩
  apply Set.inter_nonempty.mpr
  use f * s
  constructor
  · exact hf2
  · have hIn : f * s ∈ (fun x ↦ x * s) '' F := by
      simp only [Set.mem_image]
      use f
    apply hs hIn

/-- If H is thick, then Ht is thick for all t ∈ S -/
theorem rightTransOfThickIsThick
{S : Type*} [Semigroup S] [Nonempty S]
{H : Set S} (hHThick : isThick H) (t : S) :
isThick {h * t | h ∈ H} := by
  unfold isThick
  unfold isThick at hHThick
  intro F hF
  specialize hHThick F hF
  rcases hHThick with ⟨s, hs⟩
  use s * t
  intro a ha
  simp only [Set.mem_image] at ha
  rcases ha with ⟨f, hf1, hf2⟩
  simp only [Set.mem_ofPred_eq]
  simp only [Set.image_subset_iff] at hs
  have h1 := Set.mem_of_subset_of_mem hs hf1
  simp only [Set.mem_preimage] at h1
  use f * s
  constructor
  · exact h1
  · rw [<- hf2]
    exact Semigroup.mul_assoc f s t

/-- A thick set contains its own shift witnesses: for every finite `F ⊆ S` there is
`s ∈ H` with `F s ⊆ H`.  Apply thickness to `F s₁ ∪ {s₁}` for any `s₁`, obtaining `s₂` with
`F s₁ s₂ ⊆ H` and `s₁ s₂ ∈ H`; then `s = s₁ s₂` works. -/
lemma thickSetShiftWitnessInSet
{S : Type*} [Semigroup S] [Nonempty S] {H : Set S} (hH : isThick H)
{F : Set S} (hF : F.Finite) :
∃ s ∈ H, (· * s) '' F ⊆ H := by
  obtain ⟨s₁⟩ := ‹Nonempty S›
  obtain ⟨s₂, hs₂⟩ := hH (((· * s₁) '' F) ∪ {s₁})
    ((hF.image _).union (Set.finite_singleton s₁))
  refine ⟨s₁ * s₂, hs₂ ⟨s₁, Set.mem_union_right _ rfl, rfl⟩, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  have h1 : f * s₁ * s₂ ∈ H := hs₂ ⟨f * s₁, Set.mem_union_left _ ⟨f, hf, rfl⟩, rfl⟩
  rwa [mul_assoc] at h1

/-- Lemma (delta sets in thick sets), part 1: if `H` is thick then for every `k` there are
`s 0, …, s (k-1)` with `s i ∈ H * s j` whenever `i < j`.

The sequence is built by induction, maintaining the extra invariant that every `s i` lies in
`H`.  To extend a sequence of length `n`, take `u ∈ H` with `(range s) * u ⊆ H`, replace each
`s i` by `s i * u` and append `u`: old connectors survive because `(h * s j) * u =
h * (s j * u)`, and the connector to the new last term is `s i` itself, which lies in `H` by
the invariant. -/
theorem thickSetContainsLeftDeltaSequence
{S : Type*} [Semigroup S] [Nonempty S] {H : Set S} (hH : isThick H) (k : ℕ) :
∃ s : Fin k → S, ∀ i j : Fin k, i < j → ∃ h ∈ H, s i = h * s j := by
  classical
  suffices hmain : ∀ n : ℕ, ∃ s : ℕ → S,
      (∀ i, i < n → s i ∈ H) ∧ (∀ i j, i < j → j < n → ∃ h ∈ H, s i = h * s j) by
    obtain ⟨s, -, hs⟩ := hmain k
    exact ⟨fun i ↦ s (i : ℕ), fun i j hij ↦ hs (i : ℕ) (j : ℕ) hij j.isLt⟩
  intro n
  induction n with
  | zero =>
    obtain ⟨s₀⟩ := ‹Nonempty S›
    exact ⟨fun _ ↦ s₀, fun i hi ↦ absurd hi (Nat.not_lt_zero i),
      fun i j _ hj ↦ absurd hj (Nat.not_lt_zero j)⟩
  | succ n ih =>
    obtain ⟨s, hsH, hsconn⟩ := ih
    obtain ⟨u, huH, hu⟩ := thickSetShiftWitnessInSet hH ((Set.finite_Iio n).image s)
    set s' : ℕ → S := fun i ↦ if i < n then s i * u else u with hs'def
    have hlt : ∀ i, i < n → s' i = s i * u := fun i h ↦ by simp [hs'def, h]
    have hge : ∀ i, ¬ i < n → s' i = u := fun i h ↦ by simp [hs'def, h]
    refine ⟨s', ?_, ?_⟩
    · intro i _
      by_cases h : i < n
      · rw [hlt i h]
        exact hu ⟨s i, ⟨i, h, rfl⟩, rfl⟩
      · rw [hge i h]
        exact huH
    · intro i j hij hj
      by_cases hjn : j < n
      · obtain ⟨h, hhH, hh⟩ := hsconn i j hij hjn
        exact ⟨h, hhH, by rw [hlt i (lt_trans hij hjn), hlt j hjn, hh, mul_assoc]⟩
      · have hin : i < n := by omega
        exact ⟨s i, hsH i hin, by rw [hlt i hin, hge j hjn]⟩

/-- Lemma (delta sets in thick sets), part 2: if `H` is thick then for every `k` there are
`s 0, …, s (k-1)` with `s j ∈ s i * H` whenever `i < j`.

Here the sequence grows at the right-hand end, so the invariant carries the connectors `c i`
from each earlier term to the current last term.  Extending by `u ∈ H` with
`(range c) * u ⊆ H` replaces `c i` by `c i * u` and adds `u` as the connector from the old
last term. -/
theorem thickSetContainsRightDeltaSequence
{S : Type*} [Semigroup S] [Nonempty S] {H : Set S} (hH : isThick H) (k : ℕ) :
∃ s : Fin k → S, ∀ i j : Fin k, i < j → ∃ h ∈ H, s j = s i * h := by
  classical
  suffices hmain : ∀ n : ℕ, ∃ (s : ℕ → S) (c : ℕ → S),
      (∀ i, i < n → c i ∈ H ∧ s n = s i * c i) ∧
      (∀ i j, i < j → j ≤ n → ∃ h ∈ H, s j = s i * h) by
    obtain ⟨s, -, -, hs⟩ := hmain k
    exact ⟨fun i ↦ s (i : ℕ), fun i j hij ↦ hs (i : ℕ) (j : ℕ) hij (le_of_lt j.isLt)⟩
  intro n
  induction n with
  | zero =>
    obtain ⟨s₀⟩ := ‹Nonempty S›
    exact ⟨fun _ ↦ s₀, fun _ ↦ s₀, fun i hi ↦ absurd hi (Nat.not_lt_zero i),
      fun i j hij hj ↦ absurd (lt_of_lt_of_le hij hj) (Nat.not_lt_zero i)⟩
  | succ n ih =>
    obtain ⟨s, c, hlast, hconn⟩ := ih
    obtain ⟨u, huH, hu⟩ := thickSetShiftWitnessInSet hH ((Set.finite_Iio n).image c)
    set s' : ℕ → S := fun i ↦ if i = n + 1 then s n * u else s i with hs'def
    set c' : ℕ → S := fun i ↦ if i < n then c i * u else u with hc'def
    have hs'eq : ∀ i, i ≠ n + 1 → s' i = s i := fun i h ↦ by simp [hs'def, h]
    have hs'last : s' (n + 1) = s n * u := by simp [hs'def]
    have hc'lt : ∀ i, i < n → c' i = c i * u := fun i h ↦ by simp [hc'def, h]
    have hc'n : c' n = u := by simp [hc'def]
    have hc'H : ∀ i, i < n + 1 → c' i ∈ H := by
      intro i hi
      by_cases hin : i < n
      · rw [hc'lt i hin]
        exact hu ⟨c i, ⟨i, hin, rfl⟩, rfl⟩
      · have hieq : i = n := by omega
        rw [hieq, hc'n]
        exact huH
    have hstep : ∀ i, i < n + 1 → s' (n + 1) = s' i * c' i := by
      intro i hi
      by_cases hin : i < n
      · rw [hs'last, hs'eq i (by omega), hc'lt i hin, (hlast i hin).2, mul_assoc]
      · have hieq : i = n := by omega
        rw [hs'last, hs'eq i (by omega), hieq, hc'n]
    refine ⟨s', c', fun i hi ↦ ⟨hc'H i hi, hstep i hi⟩, ?_⟩
    intro i j hij hj
    by_cases hjn1 : j = n + 1
    · rw [hjn1]
      exact ⟨c' i, hc'H i (by omega), hstep i (by omega)⟩
    · obtain ⟨h, hhH, hh⟩ := hconn i j hij (by omega)
      exact ⟨h, hhH, by rw [hs'eq j hjn1, hs'eq i (by omega), hh]⟩

/-- The right quotient set `A B⁻¹ = {s | ∃ b ∈ B, s * b ∈ A}` -/
def rightQuotientSet
{S : Type*} [Semigroup S] (A B : Set S) :
Set S :=
{s | ∃ b ∈ B, s * b ∈ A}

/-- The left quotient set `A⁻¹ B = {s | ∃ a ∈ A, a * s ∈ B}` -/
def leftQuotientSet
{S : Type*} [Semigroup S] (A B : Set S) :
Set S :=
{s | ∃ a ∈ A, a * s ∈ B}

-- DGG: this is proven a number of times in our files and repeats syndeticThickIntersect above.
-- Consolidate.
/-- A set is syndetic exactly when it meets every thick set.  One direction is
`syndeticThickIntersect`; for the other, if `A` is not syndetic then `Aᶜ` is thick. -/
lemma syndeticIffMeetsEveryThickSet
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
isSyndetic A ↔ ∀ H : Set S, isThick H → (A ∩ H).Nonempty := by
  constructor
  · intro hA H hH
    exact syndeticThickIntersect A H hA hH
  · intro h
    by_contra hnot
    have hthick : isThick Aᶜ := by
      intro F hF
      unfold isSyndetic at hnot
      push Not at hnot
      obtain ⟨t, ht⟩ := hnot F hF
      refine ⟨t, ?_⟩
      rintro _ ⟨f, hf, rfl⟩
      exact ht f hf
    obtain ⟨x, hxA, hxAc⟩ := h Aᶜ hthick
    exact hxAc hxA

/-- Lemma (syndeticity of quotient sets): for every finite cover `S = ⋃ i, C i`, the set
`⋃ i, C i (C i)⁻¹` is syndetic.  Only the covering property of a partition is used. -/
theorem unionOfRightQuotientSetsIsSyndetic
{S : Type*} [Semigroup S] [Nonempty S] {k : ℕ} (C : Fin k → Set S)
(hcover : ∀ s : S, ∃ i, s ∈ C i) :
isSyndetic (⋃ i, rightQuotientSet (C i) (C i)) := by
  classical
  rw [syndeticIffMeetsEveryThickSet]
  intro H hH
  obtain ⟨s, hs⟩ := thickSetContainsLeftDeltaSequence hH (k + 1)
  choose f hf using fun i : Fin (k + 1) ↦ hcover (s i)
  obtain ⟨m, n, hmn, hfmn⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  rcases lt_or_gt_of_ne hmn with hlt | hlt
  · obtain ⟨h, hhH, hh⟩ := hs m n hlt
    exact ⟨h, Set.mem_iUnion.mpr ⟨f m, s n, hfmn ▸ hf n, hh ▸ hf m⟩, hhH⟩
  · obtain ⟨h, hhH, hh⟩ := hs n m hlt
    exact ⟨h, Set.mem_iUnion.mpr ⟨f n, s m, hfmn ▸ hf m, hh ▸ hf n⟩, hhH⟩

/-- Lemma (syndeticity of quotient sets): for every finite cover `S = ⋃ i, C i`, the set
`⋃ i, (C i)⁻¹ C i` is syndetic.  Only the covering property of a partition is used. -/
theorem unionOfLeftQuotientSetsIsSyndetic
{S : Type*} [Semigroup S] [Nonempty S] {k : ℕ} (C : Fin k → Set S)
(hcover : ∀ s : S, ∃ i, s ∈ C i) :
isSyndetic (⋃ i, leftQuotientSet (C i) (C i)) := by
  classical
  rw [syndeticIffMeetsEveryThickSet]
  intro H hH
  obtain ⟨s, hs⟩ := thickSetContainsRightDeltaSequence hH (k + 1)
  choose f hf using fun i : Fin (k + 1) ↦ hcover (s i)
  obtain ⟨m, n, hmn, hfmn⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  rcases lt_or_gt_of_ne hmn with hlt | hlt
  · obtain ⟨h, hhH, hh⟩ := hs m n hlt
    exact ⟨h, Set.mem_iUnion.mpr ⟨f m, s m, hf m, hh ▸ (hfmn ▸ hf n)⟩, hhH⟩
  · obtain ⟨h, hhH, hh⟩ := hs n m hlt
    exact ⟨h, Set.mem_iUnion.mpr ⟨f n, s n, hf n, hh ▸ (hfmn ▸ hf m)⟩, hhH⟩
