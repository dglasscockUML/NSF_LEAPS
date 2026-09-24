import NSFLEAPS._03_Family_algebra.FA_Defs

/-!
# Furstenberg family theorems

This file develops the main abstract theorems governing the algebra
of Furstenberg families.
-/

section Dual

theorem famDualAlt
{α : Type*} (F : Family α) :
F* = {A : Set α | Aᶜ ∉ F} :=
  by
  -- {A | ∀ B ∈ F.sets, (A ∩ B).Nonempty} = {A | Aᶜ ∉ F.sets}
  -- set equality proof -> prove 2 directions
  ext A
  constructor
  · -- dual -> complement not in F
    intro AinDual
    by_contra h
    have AcinF : Aᶜ ∈ F.sets := by
      change ¬ (Aᶜ ∉ F.sets) at h
      push Not at h
      exact h
    have AnAc := AinDual Aᶜ AcinF
    rcases AnAc with ⟨x, xinA, xinAc⟩
    rw [Set.mem_compl_iff] at xinAc
    exact xinAc xinA
  · -- complement not in F -> dual
    intro AcninF B BinF
    by_contra hEmpty
    have hsubset : B ⊆ Aᶜ := by
      intro x xinB
      by_contra xninAc
      have xinA : x ∈ A := by
        rw [Set.mem_compl_iff] at xninAc
        push Not at xninAc
        exact xninAc
      have : x ∈ A ∩ B := ⟨xinA, xinB⟩
      have : (A ∩ B).Nonempty := ⟨x, this⟩
      contradiction
    have : Aᶜ ∈ F.sets :=
      F.upward_closed B Aᶜ BinF hsubset
    exact AcninF this
 --complement of A in S not in F

lemma mem_dual_alt
{α : Type*} {F : Family α} {A : Set α} :
A ∈ F* ↔ Aᶜ ∉ F :=
  Set.ext_iff.mp (famDualAlt F) A

theorem dualIsInvolutionOnFamilies
{α : Type*} (F : Family α) :
F** = F := by
  ext A
  rw [mem_dual_alt]      -- 'A ∈ F**'
  rw [mem_dual_alt]      -- 'Aᶜ ∈ F*' inside the negation
  rw [compl_compl]
  push Not
  rfl

--DGG: I commented out the following theorem.  Not properly formulated,
--and we won't need it anyways.
--maybe funky
-- theorem thm_dual_is_bijection_on_fams (dual : Family α → Family α)
--   (h : ∀ (F : Family α), dual (dual F) = F) : Function.Bijective dual :=
--   by
--   constructor
--   · -- injective
--     intro F G hFG
--     have := congrArg dual hFG
--     simpa [h F, h G] using this
--   · -- surjective
--     intro F
--     use dual F
--     exact h F

theorem dualIsAntitone
{α : Type*} {F G : Family α} :
F ⊆ G → G* ⊆ F* :=
 by
  intro h A hAinF
  rw [famDualAlt] at hAinF
  rw [famDualAlt]
  simp only [Set.mem_ofPred_eq] at hAinF ⊢
  intro hAcinG
  apply hAinF
  exact h hAcinG

end Dual



section DeMorgan

--∀ (B : Set α), B ∈ F → (A ∩ B).Nonempty
theorem familyDeMorgan1
{α : Type*} (F G : Family α) :
(F ⋎ G)* = (F* ⋏ G*) :=
by
  ext A
  let BinFuG := ∀ B ∈ F ⋎ G, A ∩ B ≠ ∅
  let CDinter := ∀ C ∈ F, ∀ D ∈ G, A ∩ C ∩ D ≠ ∅
  let CinterAinGdual := ∀ C ∈ F, A ∩ C ∈ (G*)
  let goalR := A ∈ F* ⋏ G*
  have equiv23 : BinFuG ↔ CDinter := by
    constructor
    · intro h C hC D hD
      have h_inter := h (C ∩ D) ⟨C, hC, D, hD, rfl⟩
      rwa [Set.inter_assoc]
    · intro h B hB
      rcases hB with ⟨B, hB, D, hD, rfl⟩
      have h_ne := h B hB D hD
      rwa [←Set.inter_assoc]
  have equiv34 : CDinter ↔ CinterAinGdual := by
    constructor
    · intro h C hC D hD
      exact Set.nonempty_iff_ne_empty.mpr (h C hC D hD)
    · intro h C hC D hD
      exact Set.nonempty_iff_ne_empty.mp (h C hC D hD)
  have equiv45 : CinterAinGdual ↔ goalR := by
    constructor
    · intro h C hC B hB
      change C ∈ F** at hC
      rw [dualIsInvolutionOnFamilies] at hC
      exact h C hC B hB
    · intro h C hC B hB
      change ∀ B ∈ F**, A ∩ B ∈ G* at h
      rw [dualIsInvolutionOnFamilies] at h
      exact h C hC B hB
  have final_equiv : (∀ B ∈ F ⋎ G, A ∩ B ≠ ∅) ↔ A ∈ F* ⋏ G* :=
    Iff.trans (Iff.trans equiv23 equiv34) equiv45
  change (∀ B ∈ ↑F ⋎ ↑G, (A ∩ B).Nonempty) ↔ A ∈ (↑F)* ⋏ (↑G)*
  simp_rw [Set.nonempty_iff_ne_empty]
  exact final_equiv

theorem familyDeMorgan2
{α : Type*} (F G : Family α) :
(F ⋏ G)* = (F* ⋎ G*) :=
  by
  -- h : (F* ⋎ G*)* = F** ⋏ G**
  have h := familyDeMorgan1 F* G*
  repeat rw [dualIsInvolutionOnFamilies] at h
  rw [← h]
  rw [dualIsInvolutionOnFamilies]

end DeMorgan



section Join


theorem familyJoinIsAssociative
{α : Type*} (F G H : Family α) :
(F ⋎ (G ⋎ H)) = ((F ⋎ G) ⋎ H) :=
  by
    ext A
    constructor
    · intro h
      rcases h with ⟨X, hX, Y, ⟨W, hW, Z, hZ, rfl⟩, rfl⟩
      refine ⟨X ∩ W, ⟨X, hX, W, hW, rfl⟩, Z, hZ, ?_⟩
      exact (Set.inter_assoc X W Z).symm
    · intro h
      rcases h with ⟨Y, ⟨X, hX, W, hW, rfl⟩, Z, hZ, rfl⟩
      refine ⟨X, hX, W ∩ Z, ⟨W, hW, Z, hZ, rfl⟩, ?_⟩
      exact (Set.inter_assoc X W Z)

theorem familyJoinIsCommutative
{α : Type*} (F G : Family α) :
F ⋎ G = G ⋎ F :=
  by
    ext A
    change (∃ B ∈ F.sets, ∃ C ∈ G.sets, A = B ∩ C) ↔ (∃ B ∈ G.sets, ∃ C ∈ F.sets, A = B ∩ C)
    constructor
    · intro h
      rcases h with ⟨C, hC, D, hD, rfl⟩
      exact ⟨D, hD, C, hC, Set.inter_comm C D⟩
    · intro h
      rcases h with ⟨D, hD, C, hC, rfl⟩
      exact ⟨C, hC, D, hD, Set.inter_comm D C⟩

theorem familyJoinIsMonotonic
{α : Type*} {F1 G1 F2 G2 : Family α} :
F1 ⊆ G1 → F2 ⊆ G2 → (F1 ⋎ F2) ⊆ (G1 ⋎ G2) :=
  by sorry

theorem familyJoinIsMonotonicSlot1
{α : Type*} {F G : Family α} (H : Family α) :
F ⊆ G → (F ⋎ H) ⊆ (G ⋎ H) :=
  by
  intro h_sub A hA
  change A ∈ { h | ∃ A ∈ F.sets, ∃ B ∈ H.sets, h = A ∩ B } at hA
  change A ∈ { h | ∃ A ∈ G.sets, ∃ B ∈ H.sets, h = A ∩ B }
  rcases hA with ⟨C, hC, D, hD, rfl⟩
  have hC_in_G : C ∈ G.sets := h_sub hC
  exact ⟨C, hC_in_G, D, hD, rfl⟩

theorem familyJoinIsMonotonicSlot2
{α : Type*} (F : Family α) {G H : Family α} :
G ⊆ H → (F ⋎ G) ⊆ (F ⋎ H) := by
  intro GinH
  exact familyJoinIsMonotonic (Family.rfl F) GinH




theorem familyContainedInFamilyJoin
{α : Type*} (F G : Family α) :
G ≠ emptyFam α → F ⊆ (F ⋎ G) :=
  by
  intro h A hA
  sorry


theorem emptyFamilyJoinCondition
{α : Type*} (F G : Family α) :
F ⋎ G = emptyFam α ↔ F = emptyFam α ∨ G = emptyFam α :=
by sorry

theorem fullFamilyJoinCondition
{α : Type*} (F G : Family α) :
F ⋎ G = fullFam α ↔ ¬(F ⊆ G*) :=
by sorry


end Join


section Meet

theorem familyMeetIsAssociative
{α : Type*} (F G H : Family α) :
(F ⋏ (G ⋏ H)) = ((F ⋏ G) ⋏ H) :=
  by
  nth_rw 1 [← dualIsInvolutionOnFamilies (F ⋏ (G ⋏ H))]
  rw [familyDeMorgan2]
  rw [familyDeMorgan2]
  rw [familyJoinIsAssociative]
  repeat rw [familyDeMorgan1]
  repeat rw [dualIsInvolutionOnFamilies]


theorem familyMeetIsCommutative
{α : Type*} (F G : Family α) :
F ⋏ G = G ⋏ F :=
  by
  have h_dual_meet : F** ⋏ G** = G** ⋏ F** := by
      ext A
      rw [← familyDeMorgan1 (F*) (G*)]
      rw [← familyDeMorgan1 (G*) (F*)]
      rw [familyJoinIsCommutative (F*) (G*)]
  simp_rw [dualIsInvolutionOnFamilies] at h_dual_meet
  exact h_dual_meet

lemma mem_famMeetv2 {α : Type*} (F G : Family α) (A : Set α) :
  A ∈ F ⋏ G ↔ (∀ B ∈ G*, A ∩ B ∈ F) := by sorry
  -- use commutativity, then mem_famMeet


theorem familyMeetIsMonotonic
{α : Type*} {F1 G1 F2 G2 : Family α} :
F1 ⊆ G1 → F2 ⊆ G2 → (F1 ⋏ F2) ⊆ (G1 ⋏ G2) :=
  by sorry

-- can derive from familyMeetIsMonotonic
theorem familyMeetIsMonotonicSlot1
{α : Type*} {F G : Family α} (H : Family α) :
F ⊆ G → (F ⋏ H) ⊆ (G ⋏ H) :=
  by
    intro hFG S hS
    change S ∈ { h | ∀ A ∈ F*, S ∩ A ∈ H } at hS
    change S ∈ { h | ∀ A ∈ G*, S ∩ A ∈ H }
    intro A hAinGstar
    have hAinFstar : A ∈ F* := by
      sorry
    exact hS A hAinFstar

theorem familyMeetIsMonotonicSlot2
{α : Type*} (F : Family α) {G H : Family α} :
G ⊆ H → (F ⋏ G) ⊆ (F ⋏ H) := by
  intro GinH
  exact familyMeetIsMonotonic (Family.rfl F) GinH


theorem familyMeetContainedInIntersection
{α : Type*} (F G : Family α) :
G ≠ fullFam α → F ⋏ G ⊆ F :=
  by sorry


theorem fullFamilyMeetCondition
{α : Type*} (F G : Family α) :
F ⋏ G = fullFam α ↔ F = fullFam α ∨ G = fullFam α := by
  change Family.famMeet F G = fullFam α ↔ F = fullFam α ∨ G = fullFam α
  constructor
  · intro h
    sorry
  · intro h
    sorry

theorem emptyFamilyMeetCondition
{α : Type*} (F G : Family α) :
F ⋏ G = emptyFam α ↔ ¬(F* ⊆ G) :=
by sorry

end Meet

section Filters_and_PR

theorem familyIsIdempotentForMeetIffPR
{α : Type*} (F : Family α) :
  F ⋏ F = F ↔ (isPRFamilyv2 F ∨ F = fullFam α) := by sorry
-- H* ⊆ F ⋏ (F* ⋎ G*) ↔ F ⋏ G ⊆ F ⋏ H
-- H* ⊆ (F ⋏ ((F* ⋎ G*)))** ↔ F ⋏ G ⊆ F ⋏ H
-- H* ⊆ (F* ⋎ (F* ⋎ G*)\*)* ↔ F ⋏ G ⊆ F ⋏ H
-- H* ⊆ (F* ⋎ (F ⋏ G)**)* ↔ F ⋏ G ⊆ F ⋏ H
-- H* ⊆ (F* ⋎ (F ⋏ G))* ↔ F ⋏ G ⊆ F ⋏ H
--familyLocalImplicationEquivalence

-- theorem familyIsIdempotentForMeetIffPRnew
-- {α : Type*} (F : Family α) :
-- F ⋏ F = F ↔ isPRFamily F := by
--   constructor
--   · intro h
--     unfold isPRFamily
--     intro A hA n c
--     sorry
--   · intro h
--     unfold isPRFamily at h
--     sorry

theorem familyIsIdempotentForJoinIffFilter
{α : Type*} (F : Family α) :
  F ⋎ F = F ↔ (isFilterFamilyv2 F ∨ F = emptyFam α) := by sorry


-- Can we prove this as familyIsPRIffDualIsFilter below instead?
-- theorem thm_familyIsPRIffDualIsFilter
-- {α : Type*} (F : Family α) :
-- isIntersectionClosed (F.sets)* ↔
--   partitionRegularTwoSets (F.sets) :=
--   by sorry

/- extendedFilterPRDuality in the paper is gotten by combining
familyIsPRIffDualIsFilter, dualFFilterIffFMeetDualFIsDualF,
FJoinDualFIsFIffFMeetDualFIsDualF, and ifFMeetDualFIsDualFAndNonemptyThenDualFInF -/

theorem familyIsPRIffDualIsFilter
{α : Type*} (F : Family α) :
isFilterFamilyv2 F ↔ isPRFamilyv2 (F*) := by sorry

theorem dualFFilterIffFMeetDualFIsDualF
{α : Type*} (F : Family α) :
isFilterFamilyv2 (F*) ↔ F ⋏ F* = F* := by sorry

theorem FJoinDualFIsFIffFMeetDualFIsDualF
{α : Type*} (F : Family α) :
F ⋎ F* = F ↔ F ⋏ F* = F* := by sorry

theorem ifFMeetDualFIsDualFAndNonemptyThenDualFInF
{α : Type*} (F : Family α) :
F ≠ emptyFam α → F ⋏ F* = F* → F* ⊆ F := by sorry


theorem meetOfFamilyAndDualIsFilter
{α : Type*} (F : Family α) :
isFilterFamily (F ⋏ F*) := /- DGG: can we prove "isFilterFamilyv2 (F ⋏ F*) instead"-/
 by
 unfold isFilterFamily
 intro A B hAinFFstar hBinFFstar
 change ∀ C ∈ F*, A ∩ C ∈ F* at hAinFFstar
 change ∀ C ∈ F*, B ∩ C ∈ F* at hBinFFstar
 change ∀ C ∈ F*, (A ∩ B) ∩ C ∈ F* at ⊢
 intro C hC
 have hBC : B ∩ C ∈ F* := hBinFFstar C hC
 have hABC : A ∩ (B ∩ C) ∈ F* := hAinFFstar (B ∩ C) hBC
 simpa [Set.inter_assoc]

theorem joinOfFamilyAndDualIsPR
{α : Type*} (F : Family α) :
isPRTwoSets (F ⋎ F*) := /- DGG: can we prove "isPRFamilyv2 (F ⋎ F*) instead"-/
by
  rw [isPRTwoSets]
  intro A hA c
  have h_decomp : ∃ B ∈ F.sets, ∃ C ∈ (F*).sets, A = B ∩ C := by sorry
  rcases h_decomp with ⟨B, hB, C, hC, rfl⟩
  by_cases h0 : {x ∈ B | c x = 0} ∈ F.sets
  · use 0
    have h_goal : {x ∈ B ∩ C | c x = 0} ∈ (F ⋎ F*).sets := by
      sorry
    exact h_goal
  · use 1
    sorry


end Filters_and_PR

section PartialModAndConsequences

theorem familyPartialModularity
{α : Type*} (F G H : Family α) :
(F ⋎ (G ⋏ H)) ⊆ (F ⋎ G) ⋏ H := by sorry


theorem familyPartialDistributivity
{α : Type*} (F G H : Family α) :
(F ⋏ G) ⋎ (F ⋏ H) ⊆ F ⋏ (G ⋎ H) := by sorry

theorem familyAbsorptionAdjacent
{α : Type*} (F G : Family α) :
F ⊆ (F ⋎ G) ⋏ G* := by sorry
  -- intro A hA
  -- change A ∈ (F ⋎ G) ⋏ G* at ⊢
  -- change A ∈ F at hA
  -- have hAinFG : A ∈ F ⋎ G := by
  --   change A ∈ famJoin F G
  --   unfold _root_.famJoin
  --   simp_all only [SetLike.mem_coe, Set.mem_setOf_eq]
  --   sorry
  -- have hAinGstar : A ∈ G* := by
  --   intro B hBinG
  --   sorry
  -- exact ⟨hAinFG, hAinGstar⟩

--familyUsefulIdentity
theorem familyUsefulIdentity
{α : Type*} (F G H : Family α) :
F ⋎ G ⊆ H ↔ F ⊆ H ⋏ G* := by sorry

theorem familyLocalImplicationEquivalence
{α : Type*} (F G H : Family α) :
H* ⊆ F ⋏ (F* ⋎ G*) ↔ F ⋏ G ⊆ F ⋏ H :=
by
  nth_rw 1 [← dualIsInvolutionOnFamilies (F ⋏ (F* ⋎ G*))]
  rw [familyDeMorgan2]
  rw [familyDeMorgan1]
  repeat rw [dualIsInvolutionOnFamilies]
  rw [← familyDeMorgan2]
  have step : H* ⊆ F⋏(F⋏G)* ↔ ((H* ⊆ F) ∧ (H* ⊆ (F ⋏ G)*)) := by sorry
  rw [step]
  constructor
  · intro h
    have h2 : H* ⊆ (F ⋏ G)* := h.2
    have h_anti := dualIsAntitone h2
    rw [dualIsInvolutionOnFamilies, dualIsInvolutionOnFamilies] at h_anti
    intro A hA
    have hmono : (F ⋏ G) ⋏ F ⊆ H ⋏ F :=
      familyMeetIsMonotonicSlot1 F h_anti
    have h2 : (F ⋏ G) ⋏ F = F ⋏ G := by
      rw [←familyMeetIsAssociative]
      rw [familyMeetIsCommutative G F]
      rw [familyMeetIsAssociative]
      sorry
    have h3 : H ⋏ F = F ⋏ H := by
      rw [familyMeetIsCommutative]
    have h4 : F ⋏ G ⊆ F ⋏ H := by
      rw [← h2]
      rw [←h3]
      exact hmono
    exact h4 hA
  · intro h
    rw [←step] at ⊢
    rw [familyDeMorgan2]

    sorry
  /- classical
  constructor
  · intro h A hAinFG
    rw [famDualAlt] at h
    have h1 : A ∈ F ⋏ G := by
      exact hAinFG
    have h2 : A ∈ F := by
      exact h1.left
    have h3 : A ∈ G := by
      exact h1.right
    have h4 : A ∈ F* ⋎ G* := by
      constructor
      · intro hFstar
        exact Or.inl hFstar
      · intro hGstar
        exact Or.inr hGstar
    have h5 : A ∈ F ⋏ (F* ⋎ G*) := by
      constructor
      · exact h2
      · exact h4
    have h6 : Aᶜ ∉ H := by
      intro hHstar
      have : A ∈ H* := by
        rw [famDualAlt]
        exact hHstar
      exact h this
    exact sorry -/



end PartialModAndConsequences

section Unused_Or_still_to_sort

theorem thm_familySetDeMorganLaw1
{α : Type*} (F G : Family α) :
(F ∪ G)* = (F* ∩ G*) :=
 by
  ext A
  constructor
  · intro h
    have AinFdual : A ∈ F* := by
      rw [mem_dual_alt]
      rw [mem_dual_alt] at h
      -- if Aᶜ ∉  F ∪ G, then Aᶜ ∉ F
      intro a
      apply h
      exact Or.inl a
    have AinGdual : A ∈ G* := by
      rw [mem_dual_alt]
      rw [mem_dual_alt] at h
      -- if Aᶜ ∉  F ∪ G, then Aᶜ ∉ G
      intro a
      apply h
      exact Or.inr a
    exact ⟨AinFdual, AinGdual⟩
  · intro h B BinFuG
    rcases h with ⟨a, b⟩
    specialize a B
    specialize b B
    rcases BinFuG with i | j
    · exact a i
    · exact b j


/-Proof. Apply Theorem 3.18 to F∗ and G∗ to see that (F∗ ∪ G∗)∗ = (F∗)∗ ∩ (G∗)∗. By
Theorem 3.14, we have that (F∗ ∪ G∗)∗ = F ∩ G. Taking the dual and again and using
Theorem 3.14 again, we see F∗ ∪ G∗ = (F ∩ G)∗, as desired.-/
theorem thm_familySetDeMorganLaw2
{α : Type*} (F G : Family α) :
(F ∩ G)* = (F* ∪ G*) :=
 by
  have ugdualdual : (F* ∪ G*)* = F ∩ G := by
    rw [thm_familySetDeMorganLaw1]
    repeat rw [dualIsInvolutionOnFamilies]
  rw [← ugdualdual]
  rw [dualIsInvolutionOnFamilies]


end Unused_Or_still_to_sort

--thm_family_equal_to_dual_iff_ultrafilter
--theorem thm_family_equal_to_dual_iff_ultrafilter (F : Family α) : F* = F ↔ UltrafilterFamily F :=
 -- by sorry



--thm_classcap_idempotent_at_filters
--theorem thm_familyJoinIdempotentAtFilter

--thm_family_classcapdual_is_family don't need
--theorem thm_family_classcapdual_is_family (F : Family α) : Family (F ⋎ F*) :=
--  by sorry




--(F G : Set (Set α)) : Set (Set α) :=
--  { (A : Set α)| ∀ B ∈ F*, A ∩ B ∈ G }
