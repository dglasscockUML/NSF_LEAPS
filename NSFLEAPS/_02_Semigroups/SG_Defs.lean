import NSFLEAPS._00_Imports.IM_Base

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
