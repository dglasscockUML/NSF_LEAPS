import NSFLEAPS._00_Imports.IM_Base

-- We may want to assume [Nonempty S] throughout, but I've not implemented that yet.

structure SemigroupLeftIdeal (S) [Semigroup S] where
  carrier : Set S
  nonempty' : carrier.Nonempty
  mul_closed' (s : S) {x : S} : x ∈ carrier → s * x ∈ carrier

/-- isLeftIdeal is the predicate that `L` is a left ideal of a semigroup `S` -/
def isLeftIdeal {S} [Semigroup S] (L : Set S) : Prop :=
L.Nonempty ∧ (∀ (s : S), ((fun x ↦ s * x) '' L ⊆ L))

/-- A non-empty intersection of left ideals of a semigroup `S` is a left ideal -/
theorem nonemptyInterOfLeftIdealsIsLeftIdeal {S} [Semigroup S]
{i : Set (Set S)} (h : ∀ (L : Set S), L ∈ i → isLeftIdeal L) :
(⋂₀ i).Nonempty → isLeftIdeal (⋂₀ i) := by
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
def isMinLeftIdeal {S} [Semigroup S] (L : Set S) : Prop :=
isLeftIdeal L ∧ (∀ (M : Set S), isLeftIdeal M → M ⊆ L → M = L)



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

/- Still not sure we want to pursue this route, but it would make sense to define class Syndetic as follows. -/
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
