import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.Nat.Defs

-- Definition of syndetic from Hindman-Strauss, Def. 4.38
def syndetic {G : Type} [AddSemigroup G] (A : Set G) : Prop :=
  ∃ F : Finset G, ∀ g : G, ∃ f ∈ F, f + g ∈ A

def thick {G : Type} [AddSemigroup G] (A : Set G) : Prop :=
  ∀ F : Finset G, ∃ g : G, ∀ f ∈ F, f + g ∈ A

theorem evens_are_syndetic : syndetic {n : ℕ | Even n} := by
  unfold syndetic
  refine ⟨{0, 1}, ?_⟩
  intro g
  have even_or_odd : Even g ∨ Odd g := Nat.even_or_odd g
  cases even_or_odd with
  | inl h1 =>
      refine ⟨0, ?_⟩
      constructor
      · simp
      · simpa using h1
  | inr h2 =>
      refine ⟨1, ?_⟩
      have h3 : Even (1+g) := Odd.one_add h2
      constructor
      · simp
      · simpa using h3

theorem syndetic_intersects_thick {G : Type} [AddSemigroup G] :
  ∀ A B : Set G, syndetic A → thick B → (A ∩ B).Nonempty := by
  intro A B synd_A thick_B
  unfold syndetic at synd_A
  unfold thick at thick_B
  rcases synd_A with ⟨F, synd_A_two⟩
  have thick_B_two := thick_B F
  rcases thick_B_two with ⟨g, thick_B_three⟩
  have synd_A_three := synd_A_two g
  rcases synd_A_three with ⟨f,synd_A_four⟩
  have f_in_F : f ∈ F := synd_A_four.1
  have f_plus_g_in_B : f + g ∈ B := thick_B_three f f_in_F
  exact ⟨(f + g), ⟨synd_A_four.2, f_plus_g_in_B⟩⟩
  --have f_plus_g_in_A_cap_B : f + g ∈ A ∩ B := by exact ⟨(f + g) ⟨synd_A_four.2 f_plus_g_in_B⟩⟩

--class syndetic (G : Type)[Semigroup G] where
  --sets : Set (Set G)
