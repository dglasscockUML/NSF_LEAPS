import Mathlib.Topology.Basic

def IsUpwardClosed {α : Type*} (S : Set α) (F : Set (Set α)) : Prop :=
  ∀ {A B}, A ∈ F → B ⊆ S → A ⊆ B → B ∈ F
--  ∀ A ∈ F, ∀ B ⊆ S, A ⊆ B → B ∈ F

structure Family {α : Type*} (S : Set α) where
  sets : Set (Set α)
  mem_subset : ∀ {A}, A ∈ sets → A ⊆ S
  upward_closed: IsUpwardClosed S sets

theorem empty_is_upward_closed {α : Type*} (S : Set α) : IsUpwardClosed S ∅ := by
  unfold IsUpwardClosed
  intro A B x y z
  exact x

-- something here....

--- here is what Anh wrote

- anh number 2
