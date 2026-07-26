import NSFLEAPS._03_Family_algebra.FA_Defs

theorem famDualAlt {α} (F : Family α) :
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
      push_neg at h
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
        push_neg at xninAc
        exact xninAc
      have : x ∈ A ∩ B := ⟨xinA, xinB⟩
      have : (A ∩ B).Nonempty := ⟨x, this⟩
      contradiction
    have : Aᶜ ∈ F.sets :=
      F.upward_closed B Aᶜ BinF hsubset
    exact AcninF this
 --complement of A in S not in F

/- @[simp]
lemma dual_sets (F : Family α) :
  (F* : Set (Set α)) = {A : Set α | Aᶜ ∉ F} :=
by
  simpa using thm_equiv_dual_formulation (F := F) -/

-- #check famDualAlt
/-have dualEquivForm : (F*).sets = {A : Set S | Aᶜ ∉ syndeticFamily S} :=
    thm_equiv_dual_formulation (F)
  rw [dualEquivForm]-/
-- @[simp]
-- theorem Family.coe_sets (F : Family α) :
--     (↑F : Set (Set α)) = F.sets :=
--   rfl

lemma mem_dual_alt {F : Family α} {A : Set α} : A ∈ F* ↔ Aᶜ ∉ F :=
  Set.ext_iff.mp (famDualAlt F) A

theorem thm_dual_is_involution (F : Family α) : F** = F := by
  ext A
  rw [mem_dual_alt]      -- 'A ∈ F**'
  rw [mem_dual_alt]      -- 'Aᶜ ∈ F*' inside the negation
  rw [compl_compl]
  push_neg
  rfl

--maybe funky
theorem thm_dual_is_bijection_on_fams (dual : Family α → Family α)
  (h : ∀ (F : Family α), dual (dual F) = F) : Function.Bijective dual :=
  by
  constructor
  · -- injective
    intro F G hFG
    have := congrArg dual hFG
    simpa [h F, h G] using this
  · -- surjective
    intro F
    use dual F
    exact h F

theorem thm_dual_is_antitone (F G : Family α) : F ⊆ G → G* ⊆ F* :=
 by
  intro h A hAinF
  rw [famDualAlt] at hAinF
  rw [famDualAlt]
  simp only [Set.mem_setOf_eq] at hAinF ⊢
  intro hAcinG
  apply hAinF
  exact h hAcinG

theorem thm_familyIsPRIffDualIsFilter (P : Family α) : isIntersectionClosed (P.sets)* ↔
  partitionRegularTwoSets (P.sets) :=
  by sorry


--thm_family_equal_to_dual_iff_ultrafilter
--theorem thm_family_equal_to_dual_iff_ultrafilter (F : Family α) : F* = F ↔ UltrafilterFamily F :=
 -- by sorry

--thm_de_morgan_union_v1

--∀ (B : Set α), B ∈ F → (A ∩ B).Nonempty
/-Proof. We consider three cases.
Case 1: F = ∅. In this case,
• F ⋎ G = G, by definition
• F∗ = P(S)
• F∗ ⋏ G∗ = P(S) ⋏ G∗ = G∗, by definition
Therefore,
(F ⋎ G)∗ = G∗ = F∗ ⋏ G∗,
as desired.
Case 2: G = ∅. In this case, we follow the analogous argument. (Alternatively, we could
use the fact that ⋎ and ⋏ are commutative.)
Case 3: F̸ = ∅ and G̸ = ∅. In the following list, each statement is equivalent to the one
that follows it.
1. A ∈ (F ⋎ G)∗
– definition
2. for all B ∈ F ⋎ G, A ∩ B̸ = ∅
– definition
3. for all C ∈ F and D ∈ G, A ∩ C ∩ D ≠ ∅
– definition
4. for all C ∈ F, A ∩ C ∈ G∗
– definition
5. A ∈ F∗ ⋏ G∗-/
theorem thm_de_morgan_union_v1new (F G : Family α) : (Family.newFamJoin F G)* =
(Family.newFamMeet F* G*) :=
by
  ext A
  let BinFuG := ∀ B ∈ newFamJoin F G, A ∩ B ≠ ∅
  let CDinter := ∀ C ∈ F, ∀ D ∈ G, A ∩ C ∩ D ≠ ∅
  let CinterAinGdual := ∀ C ∈ F, A ∩ C ∈ (G*)
  let goalR := A ∈ newFamMeet F* G*
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
      rw [thm_dual_is_involution] at hC
      exact h C hC B hB
    · intro h C hC B hB
      change ∀ B ∈ F**, A ∩ B ∈ G* at h
      rw [thm_dual_is_involution] at h
      exact h C hC B hB
  have final_equiv : (∀ B ∈ newFamJoin F G, A ∩ B ≠ ∅) ↔ A ∈ newFamMeet F* G* :=
    Iff.trans (Iff.trans equiv23 equiv34) equiv45
  change (∀ B ∈ newFamJoin ↑F ↑G, (A ∩ B).Nonempty) ↔ A ∈ newFamMeet (↑F)* (↑G)*
  simp_rw [Set.nonempty_iff_ne_empty]
  exact final_equiv

theorem thm_de_morgan_union_v1 (F G : Family α) : (F ⋎ G)* = (F* ⋏ G*) :=
  by
  ext A
  let BinFuG := ∀ B ∈ F ⋎ G, A ∩ B = ∅
  let CDinter := ∀ C ∈ F, ∀ D ∈ G, A ∩ C ∩ D = ∅
  let CinterAinGdual := ∀ C ∈ F, A ∩ C ∈ (G*)
  let goalR := A ∈ F* ⋏ G*
  have equiv23 : BinFuG ↔ CDinter := by
    simp_all only [BinFuG, CDinter]
    apply Iff.intro
    · intro h C hC D hD
      specialize h (C ∩ D)
      have hCDinFuG : C ∩ D ∈ F ⋎ G := by
        change C ∩ D ∈ famJoin F G
        unfold _root_.famJoin
        split_ifs with hF hG
        · have h_false : C ∈ F := hC
          rw [Set.ext_iff] at hF
          have h_memF := (hF C).mp hC
          exact False.elim h_memF
        · have h_false : C ∈ F := hC
          rw [Set.ext_iff] at hG
          have h_memG := (hG D).mp hD
          exact False.elim h_memG
        · exact ⟨C, hC, D, hD, rfl⟩
      rw [Set.inter_assoc]
      exact h hCDinFuG
    · intro h B hBinFuG
      by_cases hF : F.sets = ∅
      change B ∈ famJoin F G at hBinFuG
      unfold _root_.famJoin at hBinFuG
      split_ifs at hBinFuG with hF hG
      · -- If F is empty, B ∈ ∅ is a contradiction
        rw [Set.ext_iff] at hF
        have h_memF := (hF B).mp sorry
        exact False.elim h_memF
      -- assuming F ⋎ G reduces to ∅ here, hBinFuG is False/Empty
        --exact False.elim hBinFuG
      · -- If G is empty, B ∈ ∅ is a contradiction
        rw [Set.ext_iff] at hG
        have h_memG := (hG B).mp sorry
        exact False.elim h_memG
      · -- Main case: B = C ∩ D for some C ∈ F, D ∈ G
        rcases hBinFuG with ⟨C, hC, D, hD, rfl⟩
        have h_goal := h C hC D hD
        rw [←Set.inter_assoc]
        exact h_goal
      · sorry
  have equiv34 : CDinter ↔ CinterAinGdual := by
    simp_all only [CDinter, CinterAinGdual]
    apply Iff.intro
    · intro h C hC
      rw [mem_dual_alt]
      intro hG
      sorry

    · intro h C hC D hD
      have h_goal := h C hC
      specialize h_goal D hD
      rw [Set.inter_assoc] at h_goal
      sorry
  have equiv24 : BinFuG ↔ CinterAinGdual := by exact Iff.trans equiv23 equiv34
  have equiv45 : CinterAinGdual ↔ goalR := by sorry
  have equiv25 : BinFuG ↔ goalR := by exact Iff.trans equiv24 equiv45
  sorry

  /- constructor
  · intro h
    rw [mem_dual_alt] at h
    exact goalR
  · intro h
    rw [mem_dual_alt]
    have h_complement : Aᶜ ∉ F ⋎ G := by sorry
    exact h_complement -/

--thm_de_morgan_union_v2
/- A ∈ (F ∪ G)∗
– definition
2. for all B ∈ F ∪ G, A ∩ B̸ = ∅
– logic
3. for all B ∈ F, A ∩ B̸ = ∅ and for all B ∈ G, A ∩ B̸ = ∅
– definition
4. A ∈ F∗ and A ∈ G∗
– logic
5. A ∈ F∗ ∩ G∗
-/
theorem thm_familySetDeMorganLaw1 (F G : Family α) : (F ∪ G)* = (F* ∩ G*) :=
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
theorem thm_familySetDeMorganLaw2 (F G : Family α) : (F ∩ G)* = (F* ∪ G*) :=
 by
  have ugdualdual : (F* ∪ G*)* = F ∩ G := by
    rw [thm_familySetDeMorganLaw1]
    repeat rw [thm_dual_is_involution]
  rw [← ugdualdual]
  rw [thm_dual_is_involution]

--thm_de_morgan_v1_dual
theorem thm_de_morgan_v1_dual (F G : Family α) : (F ⋏ G)* = (F* ⋎ G*) :=
  by
  -- h : (F* ⋎ G*)* = F** ⋏ G**
  have h := thm_de_morgan_union_v1 F* G*
  repeat rw [thm_dual_is_involution] at h
  rw [← h]
  rw [thm_dual_is_involution]
--todo
theorem thm_familyJoinContainsUnion (F G : Family α) : (F ∪ G) ⊆ (F ⋎ G)  :=
  by
  intro h union
  change h ∈ famJoin F G
  unfold _root_.famJoin
  split_ifs with hF hG
  · cases union with
    | inl hFmem =>
      rw [hF] at hFmem
      exact False.elim hFmem
    | inr hGmem =>
      exact hGmem
  · cases union with
    | inl hFmem =>
      exact hFmem
    | inr hGmem =>
      rw [hG] at hGmem
      exact False.elim hGmem
  · sorry

-- need to define what a subset of Fam is
theorem thm_familyJoinContainsUnionnew (F G : Family α) : (F ∪ G) ⊆ (Family.newFamJoin F G)  :=
  by
  intro h union
  change ∃ A ∈ F, ∃ B ∈ G, h = A ∩ B
  simp_all only [SetLike.mem_coe]
  sorry
--thm_classcap_commutative
theorem thm_familyJoinIsCommutative (F G : Family α) : (F ⋎ G) = (G ⋎ F) :=
  by
    ext A
    constructor
    · intro h
      change A ∈ famJoin F G at h
      change A ∈ famJoin G F
      unfold _root_.famJoin at h ⊢
      split_ifs at h ⊢ with hF hG
      · simp_all only [Set.mem_empty_iff_false]
      · simp_all only [SetLike.mem_coe]
      · simp_all only [SetLike.mem_coe]
      simp_all only [SetLike.mem_coe, Set.mem_setOf_eq]
      obtain ⟨w, h⟩ := h
      obtain ⟨left, right⟩ := h
      obtain ⟨w_1, h⟩ := right
      obtain ⟨left_1, right⟩ := h
      subst right
      apply Exists.intro
      · apply And.intro
        · exact left_1
        · apply Exists.intro
          · apply And.intro
            · exact left
            · ext x : 1
              simp_all only [Set.mem_inter_iff]
              apply Iff.intro
              · intro a
                simp_all only [and_self]
              · intro a
                simp_all only [and_self]
    · intro h
      change A ∈ famJoin G F at h
      change A ∈ famJoin F G
      unfold _root_.famJoin at h ⊢
      split_ifs at h ⊢ with hG hF
      · simp_all only [Set.mem_empty_iff_false]
      · simp_all only [SetLike.mem_coe]
      · simp_all only [SetLike.mem_coe]
      simp_all only [SetLike.mem_coe, Set.mem_setOf_eq]
      obtain ⟨w, h⟩ := h
      obtain ⟨left, right⟩ := h
      obtain ⟨w_1, h⟩ := right
      obtain ⟨left_1, right⟩ := h
      subst right
      apply Exists.intro
      · apply And.intro
        · exact left_1
        · apply Exists.intro
          · apply And.intro
            · exact left
            · ext x : 1
              simp_all only [Set.mem_inter_iff]
              apply Iff.intro
              · intro a
                simp_all only [and_self]
              · intro a
                simp_all only [and_self]

theorem thm_familyJoinIsCommutativenew (F G : Family α) : (Family.newFamJoin F G) =
(Family.newFamJoin G F) :=
  by
    ext A
    unfold Family.newFamJoin _root_.newFamJoin
    change (∃ B ∈ F.sets, ∃ C ∈ G.sets, A = B ∩ C) ↔ (∃ B ∈ G.sets, ∃ C ∈ F.sets, A = B ∩ C)
    constructor
    · intro h
      rcases h with ⟨C, hC, D, hD, rfl⟩
      exact ⟨D, hD, C, hC, Set.inter_comm C D⟩
    · intro h
      rcases h with ⟨D, hD, C, hC, rfl⟩
      exact ⟨C, hC, D, hD, Set.inter_comm D C⟩

--thm_classcap_associative
 /- For all F, G, H ∈
P(P(S)),
(F ⋎ G) ⋎ H = F ⋎ (G ⋎ H).
Proof. Let F, G, H ∈ P(P(S)). We must show that
(F ⋎ G) ⋎ H = F ⋎ (G ⋎ H).
If F = ∅ or G = ∅ or H = ∅, it is quick to check that this equality holds. Therefore, we will
assume F, G, H̸ = ∅.
Since F, G̸ = ∅,
F ⋎ G = {A ∩ B : A ∈ F, B ∈ G}.
Similarly, since G, H̸ = ∅,
G ⋎ H = {A ∩ B : A ∈ G, B ∈ H}.
Let X ⊆ S. Each line is equivalent to the one that follows it.
1. X ∈ (F ⋎ G) ⋎ H
2. there exists A ∈ (F ⋎ G) and B ∈ H such that X = A ∩ B
3. there exists C ∈ F, D ∈ G, and B ∈ H such that X = (C ∩ D) ∩ B
4. there exists C ∈ F, D ∈ G, and B ∈ H such that X = C ∩ (D ∩ B)
5. there exists C ∈ F and E ∈ G ⋎ H such that X = C ∩ E
6. X ∈ F ⋎ (G ⋎ H)
Therefore, (F ⋎ G) ⋎ H = F ⋎ (G ⋎ H), as desired. -/
#print Family
#check (· ⋎ ·)
lemma famJoin_empty_left (F : Set (Set α)) :
    famJoin (∅ : Set (Set α)) F = F := by
  simp [famJoin]

lemma famJoin_empty_right (F : Set (Set α)) :
    famJoin F (∅ : Set (Set α)) = F := by
  simp only [famJoin, ↓reduceIte, ite_eq_right_iff]
  intro h
  exact h.symm

theorem thm_familyJoinIsAssociativenew (F G H : Family α) : (Family.newFamJoin F (Family.newFamJoin G H))
= (Family.newFamJoin (Family.newFamJoin F G) H) :=
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
theorem thm_familyJoinIsAssociative (F G H : Family α) : (F ⋎ (G ⋎ H)) = ((F ⋎ G) ⋎ H) :=
  by
    ext A
    constructor
    · intro h
      change A ∈ F ⋎ (G ⋎ H) at h
      sorry
    · intro h
      sorry
--thm_classcap_monotone
theorem thm_familyJoinIsMonotone (F G H : Family α) : F ⊆ G → (F ⋎ H) ⊆ (G ⋎ H) :=
  by sorry
theorem thm_familyJoinIsMonotonenew (F G H : Family α) : F ⊆ G →
(Family.newFamJoin F  H)⊆ (Family.newFamJoin G H) :=
  by
  intro h_sub A hA
  unfold Family.newFamJoin _root_.newFamJoin at hA ⊢
  change A ∈ { h | ∃ A ∈ F.sets, ∃ B ∈ H.sets, h = A ∩ B } at hA
  change A ∈ { h | ∃ A ∈ G.sets, ∃ B ∈ H.sets, h = A ∩ B }
  rcases hA with ⟨C, hC, D, hD, rfl⟩
  have hC_in_G : C ∈ G.sets := h_sub hC
  exact ⟨C, hC_in_G, D, hD, rfl⟩

--thm_family_classcap_dual_is_partition_regular
theorem thm_familyJoinIsPartitionRegular (F : Family α) : isPRTwoSets (F ⋎ F*) :=
  by sorry

--thm_classcap_idempotent_at_filters

--thm_family_classcapdual_is_family don't need
--theorem thm_family_classcapdual_is_family (F : Family α) : Family (F ⋎ F*) :=
--  by sorry

--thm_classcapdual_contained_in_intersection ***
theorem thm_familyMeetIsContainedInIntersection (F G : Family α) : (F ⋏ G) ⊆ (F ∩ G) :=
  by sorry


--thm_classcapdual_commutative
theorem thm_familyMeetIsCommutative (F G : Family α) : (F ⋏ G) = (G ⋏ F) :=
  by sorry

theorem thm_familyMeetIsCommutativenew (F G : Family α) : (Family.newFamMeet F G) =
(Family.newFamMeet G F) :=
  by
  have h_dual_meet : Family.newFamMeet F** G** = Family.newFamMeet G** F** := by
      ext A
      rw [← thm_de_morgan_union_v1new (F*) (G*)]
      rw [← thm_de_morgan_union_v1new (G*) (F*)]
      rw [thm_familyJoinIsCommutativenew (F*) (G*)]
  simp_rw [thm_dual_is_involution] at h_dual_meet
  exact h_dual_meet

--thm_classcapdual_associative
theorem thm_familyMeetIsAssociative (F G H : Family α) : (F ⋏ (G ⋏ H)) = ((F ⋏ G) ⋏ H) :=
  by sorry
theorem thm_familyMeetIsAssociativenew (F G H : Family α) : (Family.newFamMeet F (Family.newFamMeet G H))
= (Family.newFamMeet (Family.newFamMeet F G) H) :=
  by
  sorry




--thm_classcapdual_monotone ***
theorem thm_familyMeetIsMonotone (F G H : Family α) : F ⊆ G → (F ⋏ H) ⊆ (G ⋏ H) :=
  by sorry
--thm_family_classcapdual_dual_is_filter &&&&&&&&& WORK ON THIS
theorem thm_familyMeetIsFilter (F : Family α) : isFilterFamily (F ⋏ F*) :=
  by
  unfold isFilterFamily
  intro A B hAinFFstar hBinFFstar
  change A ∩ B ∈ _root_.famMeet F F* at ⊢
  change A ∈ _root_.famMeet F F* at hAinFFstar
  change B ∈ _root_.famMeet F F* at hBinFFstar
  unfold _root_.famMeet at hAinFFstar hBinFFstar ⊢
  split_ifs at hAinFFstar hBinFFstar ⊢ with hF hFstar hG hGstar
  · change A ∈ F* at hAinFFstar
    change B ∈ F* at hBinFFstar
    change A ∩ B ∈ F* at ⊢
    rw [mem_dual_alt] at hAinFFstar hBinFFstar ⊢
    intro h
    rw [Set.compl_inter] at h
    change Aᶜ ∈ SetLike.coe F → False at hAinFFstar
    rw [hF] at hAinFFstar
    unfold fullCollection at hAinFFstar
    exact hAinFFstar (Set.subset_univ Aᶜ)
  · change A ∈ F at hAinFFstar
    change B ∈ F at hBinFFstar
    change A ∩ B ∈ F
    sorry
  · intro A hA B hB
    sorry

theorem thm_familyMeetIsFilterNew (F : Family α) : isFilterFamily (Family.newFamMeet F F*) :=
 by
 unfold isFilterFamily
 intro A B hAinFFstar hBinFFstar
 /- change A ∈ newFamMeet F F* at hAinFFstar
 change B ∈ newFamMeet F F* at hBinFFstar
 change A ∩ B ∈ newFamMeet F F* at ⊢
 unfold newFamMeet at hAinFFstar hBinFFstar ⊢ -/
 change ∀ C ∈ F*, A ∩ C ∈ F* at hAinFFstar
 change ∀ C ∈ F*, B ∩ C ∈ F* at hBinFFstar
 change ∀ C ∈ F*, (A ∩ B) ∩ C ∈ F* at ⊢
 intro C hC
 have hBC : B ∩ C ∈ F* := hBinFFstar C hC
 have hABC : A ∩ (B ∩ C) ∈ F* := hAinFFstar (B ∩ C) hBC
 simpa [Set.inter_assoc]

--(F G : Set (Set α)) : Set (Set α) :=
--  { (A : Set α)| ∀ B ∈ F*, A ∩ B ∈ G }
-- F ⋏ F = F ↔ isPRFamily F
theorem thm_familyMeetIsIdempotentAtPRFamilies (F : Family α) :
  F ⋏ F = F ↔ isPRFamily F := by sorry
--
--thm_combo_algebra_statement_one
theorem thm_combo_algebra_statement_one (F G H : Family α) : H* ⊆ F ⋏ (F* ⋎ G*) ↔ F ⋏ G ⊆ F ⋏ H :=
by
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
