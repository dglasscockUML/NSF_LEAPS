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
