import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Operations
import Init.PropLemmas
import Mathlib.Data.Finset.Empty

--class defs
class HasDual (T : Type _) where
  dual : T → T
class HasClassCap (T : Type _) where --not sure if we want to rename to famJoin
  classCap : T → T → T
class HasClassCapDual (T : Type _) where --not sure if we want to rename to famMeet
  classCapDual : T → T → T

--operators
postfix:max "*" => HasDual.dual
infixr:50 "⋎" => HasClassCap.classCap -- dont like 2 with maxprecedence
infixr:50 "⋏" => HasClassCapDual.classCapDual

def dual (F : Set (Set α)) : Set (Set α) :=
  { A : Set α | ∀ (B : Set α), B ∈ F → (A ∩ B).Nonempty}

def UpwardClosed (F : Set (Set α)) : Prop :=
  ∀ (A B : Set α), A ∈ F → A ⊆ B → B ∈ F

def PartitionRegularTwoSets (F : Set (Set α)) : Prop :=
  ∀ A ∈ F, ∀ (c : α → Fin 2), ∃ i : Fin 2, {x ∈ A| c x = i} ∈ F

def properSet (A S : Set α) : Prop :=
  A ⊆ S → A ≠ ∅ → A ≠ S
def properFam (S : Set α) (F : Set (Set α)) : Prop :=
  Set.powerset S ≠ F → F ≠ ∅

--fmaily structures
structure Family (α : Type) where
  F : Set (Set α)
  upward_closed : UpwardClosed F
def isfilterFamily (Fam : Family α) : Prop :=
  (∀ {A B : Set α}, A ∈ Fam.F → B ∈ Fam.F → A ∩ B ∈ Fam.F) -- closed under ∩
def isPRTwoSets (F : Family α) : Prop :=
  ∀ A ∈ F.F, ∀ (c : α → Fin 2), ∃ i : Fin 2, {x ∈ A| c x = i} ∈ F.F

structure PRFamily (α : Type) extends Family α where
  partition_regular : isPRTwoSets {F, upward_closed}

structure FilterFamily (α : Type) extends Family α where
  filter : isfilterFamily {F, upward_closed}

def capFam (F G : Set (Set α)) : Set (Set α) :=
  { H | ∃ A ∈ F, ∃ B ∈ G, H = A ∩ B }

def fullFam (α : Type _) : Family α := {
  F := Set.powerset (Set.univ : Set α),
  upward_closed := by
    intro A B hA hAB
    simp [Set.powerset] at hA ⊢
}
def emptyFam (α : Type _) : Family α := {
  F := ∅,
  upward_closed := by
    intro A B hA hAB
    simp at hA
}

--dual definitions
def Family.dual (fam : Family α) : Family α :=
{ F := _root_.dual fam.F,
  upward_closed := by
    intro A B hA hAB C hCF
    -- prove B ∈ dual S fam.
    have hAint : (A ∩ C).Nonempty :=
      hA C hCF
    rcases hAint with ⟨x, hxA, hxC⟩
    exact ⟨x, hAB hxA, hxC⟩
}

instance : HasDual (Family α) where
  dual := @Family.dual α
instance : HasDual (Set (Set α)) where
  dual := _root_.dual

-- ⋎ definitions
open Classical in
noncomputable def classCap (F G : Set (Set α)) : Set (Set α) :=
  if F = ∅ then G
  else if G = ∅ then F
  else { h | ∃ A ∈ F, ∃ B ∈ G, h = A ∩ B }
--F ⋏ G = {A ⊆ S: ∀ B ∈ F*, A ∩ B ∈ G} if both not P(S),
--if F = P(S), then G, if G = P(S) then F

open Classical in
noncomputable def Family.classCap (famA famB : Family α) : Family α :=
{
  F := _root_.classCap famA.F famB.F,
  upward_closed := by
    intro A B hA hAB
    -- prove B ∈ classCap famA famB
    unfold _root_.classCap at hA ⊢
    split_ifs at hA ⊢ with hF hG
    · exact famB.upward_closed A B hA hAB
    · exact famA.upward_closed A B hA hAB
    · rcases hA with ⟨C, hC, D, hD, hAeq⟩
      sorry
      --B = ((B ∪ C) ∈ fam A) ∩ ((B ∪ D) ∈ fam B)
}

instance : HasClassCap (Set (Set α))  where
  classCap := _root_.classCap
noncomputable instance : HasClassCap (Family α) where
  classCap := @Family.classCap α

-- ⋏ definitions
open Classical in
noncomputable def classCapDual (F G : Set (Set α)) : Set (Set α) :=
  if F = Set.powerset (Set.univ : Set α) then G
  else if G = Set.powerset (Set.univ :Set α) then F
  else { (A : Set α)| ∀ B ∈ F*, A ∩ B ∈ G }

open Classical in
noncomputable def Family.classCapDual (famA famB : Family α) : Family α := {
  F := _root_.classCapDual famA.F famB.F,
  upward_closed := by
    intro A B hA hAB
    -- prove B ∈ classCapDual famA famB
    unfold _root_.classCapDual at hA ⊢
    split_ifs at hA ⊢ with hF hG
    · exact famB.upward_closed A B hA hAB
    · exact famA.upward_closed A B hA hAB
    · intro C hCF
      have hBCmem : B ∩ C ∈ famB.F :=
        famB.upward_closed (A ∩ C) (B ∩ C) (hA C hCF)
        (Set.inter_subset_inter hAB (Set.Subset.refl C))
      unfold _root_.dual at hBCmem
      exact hBCmem
}

instance : HasClassCapDual (Set (Set α))  where
  classCapDual := _root_.classCapDual
noncomputable instance : HasClassCapDual (Family α) where
  classCapDual := @Family.classCapDual α
