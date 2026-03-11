import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations

def dual (F : Set (Set α)) : Set (Set α) :=
  {A | ∀ B ∈ F, (A ∩ B).Nonempty}
  --fun A : Set α => ∀ B ∈ F, (A ∩ B).Nonempty

def upclosed (F : Set (Set α)) : Prop :=
  ∀ A B : Set α, A ∈ F → A ⊆ B → B ∈ F

theorem dual_is_upclosed (F : Set (Set α)) : upclosed (dual F) := by
  unfold upclosed dual
  intro A B A_in_dual A_in_B C C_in_F
  simp only [Set.mem_setOf_eq] at A_in_dual
  have A_cap_C_nonempty : (A ∩ C).Nonempty := A_in_dual C C_in_F
  have A_cap_C_in_B_cap_C : A ∩ C ⊆ B ∩ C := Set.inter_subset_inter_left C A_in_B
  exact Set.Nonempty.mono A_cap_C_in_B_cap_C A_cap_C_nonempty


--- new thing here too


-- new thing after installing git graph extension from Anh
