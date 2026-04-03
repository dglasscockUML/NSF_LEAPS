import NSFLEAPS._00_Imports.IM_Base

/- These imports have been moved to _00_Imports.IM_Base
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Operations
import Init.PropLemmas
import Mathlib.Data.Finset.Empty
When ready, delete me.
-/

--class defs
class HasFamDual (T : Type _) where
  famDual : T → T
class HasFamJoin (T : Type _) where
  famJoin : T → T → T
class HasFamMeet (T : Type _) where
  famMeet : T → T → T

--operators
postfix:max "*" => HasFamDual.famDual
infixr:50 "⋎" => HasFamJoin.famJoin -- dont like 2 with max precedence
infixr:50 "⋏" => HasFamMeet.famMeet

def upwardClosed (F : Set (Set α)) : Prop :=
  ∀ (A B : Set α), A ∈ F → A ⊆ B → B ∈ F

def partitionRegularTwoSets (F : Set (Set α)) : Prop :=
  ∀ A ∈ F, ∀ (c : α → Fin 2), ∃ i : Fin 2, {x ∈ A| c x = i} ∈ F

--family structures
structure Family (α : Type*) where
  sets : Set (Set α)
  upward_closed : upwardClosed sets

-- instance {α} : Coe (Family α) (Set (Set α)) where
--   coe F := F.sets
instance {α} : SetLike (Family α) (Set α) where
  coe F := F.sets
  coe_injective' := by
    intro F G h
    cases F; cases G; cases h; rfl

instance {α} : HasSubset (Family α) where
  Subset F G := (F : Set (Set α)) ⊆ (G : Set (Set α))

instance {α} : Inter (Family α) where
  inter F G := ⟨(F : Set (Set α)) ∩ (G : Set (Set α)), by
    intro A B hA hAB
    obtain ⟨hAF, hAG⟩ := hA
    exact ⟨F.upward_closed A B hAF hAB, G.upward_closed A B hAG hAB⟩⟩

instance {α} : Union (Family α) where
  union F G := ⟨(F : Set (Set α)) ∪ (G : Set (Set α)), by
    intro A B hA hAB
    obtain hAF | hAG := hA
    · exact Or.inl (F.upward_closed A B hAF hAB)
    · exact Or.inr (G.upward_closed A B hAG hAB)⟩


def isIntersectionClosed (F : Set (Set α)) : Prop :=
  (∀ {A B : Set α}, A ∈ F → B ∈ F → A ∩ B ∈ F) -- closed under ∩

def isFilterFamily (F : Family α) : Prop :=
  (∀ {A B : Set α}, A ∈ F → B ∈ F → A ∩ B ∈ F)

structure PRFamily (α : Type) extends Family α where
  partition_regular : partitionRegularTwoSets sets

structure FilterFamily (α : Type) extends Family α where
  filter : isIntersectionClosed sets

def fullCollection (α : Type _) : Set (Set α) :=
  Set.powerset (Set.univ : Set α)

def fullFam (α : Type _) : Family α := {
  sets := fullCollection α,
  upward_closed := by
    intro A B hA hAB
    unfold fullCollection
    simp [Set.powerset] at hA ⊢
}
def emptyFam (α : Type _) : Family α := {
  sets := ∅,
  upward_closed := by
    intro A B hA hAB
    simp at hA
}


--dual definitions
def famDual (F : Set (Set α)) : Set (Set α) :=
  { A : Set α | ∀ (B : Set α), B ∈ F → (A ∩ B).Nonempty}

def Family.famDual (fam : Family α) : Family α :=
{ sets := _root_.famDual fam.sets,
  upward_closed := by
    intro A B hA hAB C hCF
    -- prove B ∈ dual S fam.
    have hAint : (A ∩ C).Nonempty :=
      hA C hCF
    rcases hAint with ⟨x, hxA, hxC⟩
    exact ⟨x, hAB hxA, hxC⟩
}
def isPRTwoSets (F : Family α) : Prop :=
  ∀ A ∈ F.sets, ∀ (c : α → Fin 2), ∃ i : Fin 2, {x ∈ A| c x = i} ∈ F.sets
/- def PRFamily.famDual (fam : PRFamily α) : PRFamily α :=
{
  sets := _root_.famDual fam.sets,
  upward_closed := by
    intro A B hA hAB C hCF
    -- prove B ∈ dual S fam.
    have hAint : (A ∩ C).Nonempty :=
      hA C hCF
    rcases hAint with ⟨x, hxA, hxC⟩
    exact ⟨x, hAB hxA, hxC⟩
  partition_regular := by sorry -- need to get rid of this sorry
    -- prove ∃ i : Fin 2, {x ∈ A| c x = i} ∈ dual S fam.
} -/

instance : HasFamDual (Family α) where
  famDual := @Family.famDual α
instance : HasFamDual (Set (Set α)) where
  famDual := _root_.famDual
--instance : HasFamDual (PRFamily α) where
 -- famDual := @PRFamily.famDual α
-- ⋎ definitions
open Classical in
noncomputable def famJoin (F G : Set (Set α)) : Set (Set α) :=
  if F = ∅ then G
  else if G = ∅ then F
  else { h | ∃ A ∈ F, ∃ B ∈ G, h = A ∩ B }
--F ⋏ G = {A ⊆ S: ∀ B ∈ F*, A ∩ B ∈ G} if both not P(S),
--if F = P(S), then G, if G = P(S) then F

open Classical in
noncomputable def Family.famJoin (famA famB : Family α) : Family α :=
{
  sets := _root_.famJoin famA.sets famB.sets,
  upward_closed := by
    intro A B hA hAB
    -- prove B ∈ famMeet famA famB
    unfold _root_.famJoin at hA ⊢
    split_ifs at hA ⊢ with hF hG
    · exact famB.upward_closed A B hA hAB
    · exact famA.upward_closed A B hA hAB
    · rcases hA with ⟨C, hCF, D, hDG, hAeq⟩
      -- C ∩ D = A ⊆ B, so B ⊆ (C ∪ B) and B ⊆ (D ∪ B).
      have hC' : (B ∪ C) ∈ famA.sets := famA.upward_closed C (B ∪ C) hCF Set.subset_union_right
      have hD' : (B ∪ D) ∈ famB.sets := famB.upward_closed D (B ∪ D) hDG Set.subset_union_right
      -- Now, (B ∪ C) ∩ (B ∪ D) = B ∪ (C ∩ D) = B ∪ A = B, so B ∈ famMeet famA famB.
      have hsub : C ∩ D ⊆ B := by simpa [hAeq] using hAB
      have hB : B = (B ∪ C) ∩ (B ∪ D) := by
        calc B = B ∪ (C ∩ D) := by exact (Set.union_eq_left.mpr hsub).symm
        _ = (B ∪ C) ∩ (B ∪ D) := by simp [Set.union_inter_distrib_left]
      exact ⟨B ∪ C, hC', B ∪ D, hD', hB⟩
}

noncomputable instance : HasFamJoin (Set (Set α))  where
  famJoin := _root_.famJoin
noncomputable instance : HasFamJoin (Family α) where
  famJoin := @Family.famJoin α

-- ⋏ definitions
open Classical in
noncomputable def famMeet (F G : Set (Set α)) : Set (Set α) :=
  if F = fullCollection α then G
  else if G = fullCollection α then F
  else { (A : Set α)| ∀ B ∈ F*, A ∩ B ∈ G }

open Classical in
noncomputable def Family.famMeet (famA famB : Family α) : Family α := {
  sets := _root_.famMeet famA.sets famB.sets,
  upward_closed := by
    intro A B hA hAB
    -- prove B ∈ famMeet famA famB
    unfold _root_.famMeet at hA ⊢
    split_ifs at hA ⊢ with hF hG
    · exact famB.upward_closed A B hA hAB
    · exact famA.upward_closed A B hA hAB
    · intro C hCF
      have hBCmem : B ∩ C ∈ famB.sets :=
        famB.upward_closed (A ∩ C) (B ∩ C) (hA C hCF)
        (Set.inter_subset_inter hAB (Set.Subset.refl C))
      exact hBCmem
}

instance : HasFamMeet (Set (Set α))  where
  famMeet := _root_.famMeet
noncomputable instance : HasFamMeet (Family α) where
  famMeet := @Family.famMeet α


