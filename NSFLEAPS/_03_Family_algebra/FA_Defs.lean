import NSFLEAPS._00_Imports.IM_Main

/-!
# Furstenberg family structure objects

This file defines the objects that capture Furstenberg families
and their basic properties.  It also establishes notation for the family
dual, meet, and join operators.
-/

section Family_structure

def upwardClosed {α : Type*} (F : Set (Set α)) : Prop :=
  ∀ (A B : Set α), A ∈ F → A ⊆ B → B ∈ F

/-- A term of type `Family α` is an upward closed
collection of subsets of `α` -/
structure Family (α : Type*) where
  sets : Set (Set α)
  upward_closed : upwardClosed sets

-- instance : Coe (Family α) (Set (Set α)) :=
--   ⟨Family.sets⟩
instance {α} : SetLike (Family α) (Set α) where
  coe := Family.sets
  coe_injective := by
    intro F G h
    cases F; cases G
    congr

@[ext]
lemma Family.ext {α : Type*} {F G : Family α} (h : ∀ (A : Set α), A ∈ F ↔ A ∈ G) : F = G :=
  SetLike.ext h

-- instance {α} : SetLike (Family α) (Set α) where
--   coe F := F.sets
--   coe_injective' := by
--     intro F G h
--     cases F; cases G; cases h; rfl

instance {α : Type*} : HasSubset (Family α) where
  Subset F G := (F : Set (Set α)) ⊆ (G : Set (Set α))

instance {α : Type*} : Inter (Family α) where
  inter F G := ⟨(F : Set (Set α)) ∩ (G : Set (Set α)), by
    intro A B hA hAB
    obtain ⟨hAF, hAG⟩ := hA
    exact ⟨F.upward_closed A B hAF hAB, G.upward_closed A B hAG hAB⟩⟩

instance {α : Type*} : Union (Family α) where
  union F G := ⟨(F : Set (Set α)) ∪ (G : Set (Set α)), by
    intro A B hA hAB
    obtain hAF | hAG := hA
    · exact Or.inl (F.upward_closed A B hAF hAB)
    · exact Or.inr (G.upward_closed A B hAG hAB)⟩

def Family.iInter
{α ι : Type*} (F : ι → Family α) : Family α :=
  ⟨⋂ i, (F i).sets, by
    intro A B hA hAB
    rw [Set.mem_iInter] at hA ⊢
    intro i
    exact (F i).upward_closed A B (hA i) hAB⟩

def Family.iUnion
{α ι : Type*} (F : ι → Family α) : Family α :=
  ⟨⋃ i, (F i).sets, by
    intro A B hA hAB
    rw [Set.mem_iUnion] at hA ⊢
    obtain ⟨i, hi⟩ := hA
    exact ⟨i, (F i).upward_closed A B hi hAB⟩⟩

@[simp]
theorem Family.mem_iInter
{α ι : Type*} (F : ι → Family α) (A : Set α) :
    A ∈ (Family.iInter F).sets ↔ ∀ i, A ∈ (F i).sets :=
  Set.mem_iInter

@[simp]
theorem Family.mem_iUnion
{α ι : Type*} (F : ι → Family α) (A : Set α) :
    A ∈ (Family.iUnion F).sets ↔ ∃ i, A ∈ (F i).sets :=
  Set.mem_iUnion

/-- Given a family `F` and a set `A`, `capFamily F A` is the family of
sets `B` for which `B ∩ A ∈ F` -/
def capFamily
{α : Type*} (F : Family α) (A : Set α) :
Family α :=
{
  sets := {B : Set α | A ∩ B ∈ F}
  upward_closed := by
    intro C D hC CinD
    exact F.2 (A ∩ C) (A ∩ D) hC (Set.inter_subset_inter_right A CinD)
}

lemma Family.rfl {α : Type*} (F : Family α) : F ⊆ F := by
  intro A hA
  exact hA

end Family_structure

section Empty_and_full_families

/-- The full collection is the set of all subsets of `α` -/
def fullCollection (α : Type*) : Set (Set α) :=
  Set.powerset (Set.univ : Set α)

/-- The full family is the family whose underlying set is
the full collection -/
def fullFam (α : Type*) : Family α := {
  sets := fullCollection α,
  upward_closed := by
    intro A B hA hAB
    unfold fullCollection
    simp [Set.powerset] at hA ⊢
}

/-- The empty family is the family whose underlying set is
the empty set -/
def emptyFam (α : Type*) : Family α := {
  sets := ∅,
  upward_closed := by
    intro A B hA hAB
    simp at hA
}

/-- An equivalent condition to show that a family is non-empty -/
lemma notEmptyFam
{α : Type*} (F : Family α) :
F ≠ emptyFam α ↔ F.sets.Nonempty :=
by sorry

end Empty_and_full_families

section Filters_and_PR_Families

/-- A family is a filter if it is not the empty family and if it
is closed under intersections -/
def isFilterFamilyv2 {α : Type*} (F : Family α) : Prop :=
  (F ≠ emptyFam α) ∧ (∀ {A B : Set α}, A ∈ F → B ∈ F → A ∩ B ∈ F)

/-- A family is partition regular (PR) if it is not the full
family and if the union of two sets belonging to the family
implies that at least one of the sets belongs to the family -/
def isPRFamilyv2 {α : Type*} (F : Family α) : Prop :=
  (F ≠ fullFam α) ∧ (∀ A B : Set α, A ∪ B ∈ F → ((A ∈ F) ∨ (B ∈ F)))


end Filters_and_PR_Families

section Old_filter_and_pr

def isIntersectionClosed {α : Type*} (F : Set (Set α)) : Prop :=
  (∀ {A B : Set α}, A ∈ F → B ∈ F → A ∩ B ∈ F) -- closed under ∩

def isFilterFamily {α : Type*} (F : Family α) : Prop :=
  (∀ {A B : Set α}, A ∈ F → B ∈ F → A ∩ B ∈ F)

def isPRTwoSets {α : Type*} (F : Family α) : Prop :=
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


-- def infiniteSets (α : Type*) : Family α where
--   sets := {s | s.Infinite}
--   upward_closed := by
--     intro A B hA hAB
--     exact hA.mono hAB

-- theorem infinite_is_PR (α : Type*) [Infinite α] :
--   isPRFamily (infiniteSets α) := by
--   intro A hA n c
--   -- at least one color must appear infinitely often
--   simp [infiniteSets]
--   exact Finite.exists_infinite_fiber A c hA

def partitionRegularTwoSets {α : Type*} (F : Set (Set α)) : Prop :=
  ∀ A ∈ F, ∀ (c : α → Fin 2), ∃ i : Fin 2, {x ∈ A| c x = i} ∈ F

-- want to define pr for beyond two sets
def PartitionRegular {α : Type*} (F : Family α) : Prop := --rewrite this to not use ℕ **
  sorry--∀ A ∈ F, ∀ n : ℕ, ∀ (c : A → Fin n), ∃ (i : Fin n), {x | c x = i} ∈ F

def isPRFamily {α : Type*} (F : Family α) : Prop :=
  ∀ A ∈ F, ∀ (n : ℕ+), ∀ (c : α → Fin n), ∃ (i : Fin n), {x ∈ A | c x = i} ∈ F



structure PRFamily (α : Type) extends Family α where
  partition_regular : partitionRegularTwoSets sets

structure FilterFamily (α : Type) extends Family α where
  filter : isIntersectionClosed sets



end Old_filter_and_pr

section Dual_Join_Meet_Classes_and_Operators

/- Classes associated with the family dual, join, and meet operators -/
class HasFamDual (T : Type _) where
  famDual : T → T
class HasFamJoin (T : Type _) where
  famJoin : T → T → T
class HasFamMeet (T : Type _) where
  famMeet : T → T → T

/- The family dual, join, and meet operator symbols -/
postfix:max "*" => HasFamDual.famDual
infixr:80 "⋎" => HasFamJoin.famJoin -- dont like 2 with max precedence
infixr:80 "⋏" => HasFamMeet.famMeet
--infixr:80 "~" => HasFamJoinnew.newFamJoin -- dont like 2 with max precedence
--infixr:80 "!" => HasFamMeetnew.newFamMeet

end Dual_Join_Meet_Classes_and_Operators

section Dual

/-- The family dual defined at the level of collections:
famDual F = { A | ∀ B ∈ F, A ∩ B ≠ ∅ } -/
def famDual {α : Type*} (F : Set (Set α)) : Set (Set α) :=
  { A : Set α | ∀ (B : Set α), B ∈ F → (A ∩ B).Nonempty}

/-- The family dual of a family as a term of type Family α -/
def Family.famDual {α : Type*} (fam : Family α) : Family α :=
{ sets := _root_.famDual fam.sets,
  upward_closed := by
    intro A B hA hAB C hCF
    -- prove B ∈ dual S fam.
    have hAint : (A ∩ C).Nonempty :=
      hA C hCF
    rcases hAint with ⟨x, hxA, hxC⟩
    exact ⟨x, hAB hxA, hxC⟩
}

lemma mem_famDual {α : Type*} (F : Set (Set α)) (A : Set α) :
  A ∈ famDual F ↔ ∀ B ∈ F, (A ∩ B).Nonempty := by rfl


instance {α : Type*} : HasFamDual (Family α) where
  famDual := @Family.famDual α

instance {α : Type*} : HasFamDual (Set (Set α)) where
  famDual := _root_.famDual
--instance : HasFamDual (PRFamily α) where
 -- famDual := @PRFamily.famDual α
-- ⋎ definitions

lemma mem_dual_star {α : Type*} (F : Family α) (A : Set α) :
    A ∈ F* ↔ ∀ B ∈ F, (A ∩ B).Nonempty := Iff.rfl

end Dual

section Join

/-- The family join defined at the level of collections:
famJoin F G = {C | ∃ A ∈ F, ∃ B ∈ G, C = A ∩ B} -/
def famJoin {α : Type*} (F G : Set (Set α)) : Set (Set α) :=
  { C | ∃ A ∈ F, ∃ B ∈ G, C = A ∩ B }

/-- The family join of families as a term of type Family α -/
def Family.famJoin {α : Type*} (famA famB : Family α) : Family α :=
{
  sets := _root_.famJoin famA.sets famB.sets,
  upward_closed := by
    intro A B hA hAB
    unfold _root_.famJoin at hA ⊢
    rcases hA with ⟨C, hCF, D, hDG, hAeq⟩
    have hC' : (B ∪ C) ∈ famA.sets := famA.upward_closed C (B ∪ C) hCF Set.subset_union_right
    have hD' : (B ∪ D) ∈ famB.sets := famB.upward_closed D (B ∪ D) hDG Set.subset_union_right
    have hsub : C ∩ D ⊆ B := by simpa [hAeq] using hAB
    have hB : B = (B ∪ C) ∩ (B ∪ D) := by
      calc B = B ∪ (C ∩ D) := by exact (Set.union_eq_left.mpr hsub).symm
      _ = (B ∪ C) ∩ (B ∪ D) := by simp [Set.union_inter_distrib_left]
    exact ⟨B ∪ C, hC', B ∪ D, hD', hB⟩
}
lemma mem_famJoin {α : Type*} (F G : Set (Set α)) (A : Set α) :
  A ∈ famJoin F G ↔ (∃ B ∈ F, ∃ C ∈ G, A = B ∩ C) := by
  rfl
instance {α : Type*} : HasFamJoin (Set (Set α))  where
  famJoin := _root_.famJoin

noncomputable instance {α : Type*} : HasFamJoin (Family α) where
  famJoin := @Family.famJoin α

end Join

section Meet

/-- The family meet defined at the level of collections:
famMeet F G = { A | ∀ B ∈ F*, A ∩ B ∈ G } -/
def famMeet {α : Type*} (F G : Set (Set α)) : Set (Set α) :=
  { A : Set α | ∀ B ∈ F*, A ∩ B ∈ G }

/-- The family meet of families as a term of type Family α -/
def Family.famMeet {α : Type*} (famA famB : Family α) : Family α := {
  sets := _root_.famMeet famA.sets famB.sets,
  upward_closed := by
    intro A B hA hAB
    unfold _root_.famMeet at hA ⊢
    intro C hCF
    have hBCmem : B ∩ C ∈ famB.sets :=
      famB.upward_closed (A ∩ C) (B ∩ C) (hA C hCF)
      (Set.inter_subset_inter hAB (Set.Subset.refl C))
    exact hBCmem
}

lemma mem_famMeet {α : Type*} (F G : Family α) (A : Set α) :
  A ∈ famMeet F G ↔ (∀ B ∈ F*, A ∩ B ∈ G) := by
  rfl

instance {α : Type*} : HasFamMeet (Set (Set α))  where
  famMeet := _root_.famMeet

instance {α : Type*} : HasFamMeet (Family α) where
  famMeet := @Family.famMeet α

end Meet
