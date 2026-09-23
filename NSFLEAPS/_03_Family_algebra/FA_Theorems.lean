import NSFLEAPS._03_Family_algebra.FA_Defs

/-! This is a module docstring -/

section Dual

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

-- dualIsInvolutionOnFamilies
theorem thm_dual_is_involution (F : Family α) : F** = F := by
  ext A
  rw [mem_dual_alt]      -- 'A ∈ F**'
  rw [mem_dual_alt]      -- 'Aᶜ ∈ F*' inside the negation
  rw [compl_compl]
  push Not
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

-- dualIsAntitone
theorem thm_dual_is_antitone (F G : Family α) : F ⊆ G → G* ⊆ F* :=
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

--thm_de_morgan_union_v1
--∀ (B : Set α), B ∈ F → (A ∩ B).Nonempty
theorem thm_de_morgan_union_v1 (F G : Family α) : (F ⋎ G)* = (F* ⋏ G*) :=
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
      rw [thm_dual_is_involution] at hC
      exact h C hC B hB
    · intro h C hC B hB
      change ∀ B ∈ F**, A ∩ B ∈ G* at h
      rw [thm_dual_is_involution] at h
      exact h C hC B hB
  have final_equiv : (∀ B ∈ F ⋎ G, A ∩ B ≠ ∅) ↔ A ∈ F* ⋏ G* :=
    Iff.trans (Iff.trans equiv23 equiv34) equiv45
  change (∀ B ∈ ↑F ⋎ ↑G, (A ∩ B).Nonempty) ↔ A ∈ (↑F)* ⋏ (↑G)*
  simp_rw [Set.nonempty_iff_ne_empty]
  exact final_equiv


theorem thm_de_morgan_v1_dual (F G : Family α) : (F ⋏ G)* = (F* ⋎ G*) :=
  by
  -- h : (F* ⋎ G*)* = F** ⋏ G**
  have h := thm_de_morgan_union_v1 F* G*
  repeat rw [thm_dual_is_involution] at h
  rw [← h]
  rw [thm_dual_is_involution]

end DeMorgan



section Join


--familyJoinIsAssociative
theorem thm_familyJoinIsAssociative (F G H : Family α) : (F ⋎ (G ⋎ H)) = ((F ⋎ G) ⋎ H) :=
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

--familyJoinIsCommutative
--thm_classcap_commutative
theorem thm_familyJoinIsCommutative (F G : Family α) : F ⋎ G = G ⋎ F :=
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

--thm_classcap_monotone
--  *****for all F1, F2, G1, G2 ∈ Fam(S), if F1 ⊆ G1 and F2 ⊆ G2, then F1 ⋎ G1 ⊆ F2 ⋎ G2.
theorem thm_familyJoinIsMonotone (F G H : Family α) : F ⊆ G → (F ⋎ H) ⊆ (G ⋎ H) :=
  by
  intro h_sub A hA
  change A ∈ { h | ∃ A ∈ F.sets, ∃ B ∈ H.sets, h = A ∩ B } at hA
  change A ∈ { h | ∃ A ∈ G.sets, ∃ B ∈ H.sets, h = A ∩ B }
  rcases hA with ⟨C, hC, D, hD, rfl⟩
  have hC_in_G : C ∈ G.sets := h_sub hC
  exact ⟨C, hC_in_G, D, hD, rfl⟩


--familyContainedInFamilyJoin
-- UPDATED STATEMENT
theorem thm_familyJoinContainsUnion (F G : Family α) : G ≠ emptyFam α → F ⊆ (F ⋎ G) :=
  by
  intro h A hA
  sorry

--emptyFamilyJoinCondition
-- NEW ***
theorem thm_famJoinEmptyIfEitherEmpty (F G : Family α) : F ⋎ G = emptyFam α ↔ F = emptyFam α ∨ G =
emptyFam α :=
by sorry

--fullFamilyJoinCondition
theorem thm_famJoinIsFullFamIffFnotinGDual (F G : Family α) : F ⋎ G = fullFam α ↔ ¬(F ⊆ G*) :=
by sorry


end Join


section Meet

--familyMeetIsAssociative
--thm_classcapdual_associative
theorem thm_familyMeetIsAssociative (F G H : Family α) : (F ⋏ (G ⋏ H)) = ((F ⋏ G) ⋏ H) :=
  by
  nth_rw 1 [← thm_dual_is_involution (F ⋏ (G ⋏ H))]
  rw [thm_de_morgan_v1_dual]
  rw [thm_de_morgan_v1_dual]
  rw [thm_familyJoinIsAssociative]
  repeat rw [thm_de_morgan_union_v1]
  repeat rw [thm_dual_is_involution]

--familyMeetIsCommutative
--thm_classcapdual_commutative
theorem thm_familyMeetIsCommutative (F G : Family α) :  F ⋏ G = G ⋏ F :=
  by
  have h_dual_meet : F** ⋏ G** = G** ⋏ F** := by
      ext A
      rw [← thm_de_morgan_union_v1 (F*) (G*)]
      rw [← thm_de_morgan_union_v1 (G*) (F*)]
      rw [thm_familyJoinIsCommutative (F*) (G*)]
  simp_rw [thm_dual_is_involution] at h_dual_meet
  exact h_dual_meet

--familyMeetIsMonotonic
--thm_classcapdual_monotone ***
-- follow more general version as seen above join
theorem thm_familyMeetIsMonotone (F G H : Family α) : F ⊆ G → (F ⋏ H) ⊆ (G ⋏ H) :=
  by sorry
  -- intro hFG S hS
  -- rcases hS with ⟨f, hf, h, hh, rfl⟩
  -- have hfG : f ∈ G := hFG hf
  -- use f, hfG, h, hh

--familyMeetContainedInIntersection
--thm_classcapdual_contained_in_intersection *** UPDATED
theorem thm_familyMeetIsContainedInIntersection (F G : Family α) : G ≠ fullFam α → F ⋏ G ⊆ F :=
  by sorry








--fullFamilyMeetCondition
theorem thm_famMeetFullIfEitherFull (F G : Family α) : F ⋏ G = fullFam α ↔ F = fullFam α ∨ G =
fullFam α := by
  change Family.famMeet F G = fullFam α ↔ F = fullFam α ∨ G = fullFam α
  constructor
  · intro h
    sorry
  · intro h
    sorry

--emptyFamilyMeetCondition
theorem thm_famMeetIsEmptyFamIffFnotinGDual (F G : Family α) : F ⋎ G = emptyFam α ↔ ¬(F* ⊆ G) :=
by sorry

end Meet

section Filters_and_PR

theorem thm_familyIsPRIffDualIsFilter (P : Family α) : isIntersectionClosed (P.sets)* ↔
  partitionRegularTwoSets (P.sets) :=
  by sorry

--thm_family_classcap_dual_is_partition_regular

theorem thm_familyJoinIsPartitionRegular (F : Family α) : isPRTwoSets (F ⋎ F*) :=
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


--thm_family_classcapdual_dual_is_filter &&&&&&&&& WORK ON THIS

theorem thm_familyMeetIsFilter (F : Family α) : isFilterFamily (F ⋏ F*) :=
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


-- F ⋏ F = F ↔ isPRFamily F
theorem thm_familyMeetIsIdempotentAtPRFamilies (F : Family α) :
  F ⋏ F = F ↔ isPRFamily F := by sorry
-- H* ⊆ F ⋏ (F* ⋎ G*) ↔ F ⋏ G ⊆ F ⋏ H
-- H* ⊆ (F ⋏ ((F* ⋎ G*)))** ↔ F ⋏ G ⊆ F ⋏ H
-- H* ⊆ (F* ⋎ (F* ⋎ G*)\*)* ↔ F ⋏ G ⊆ F ⋏ H
-- H* ⊆ (F* ⋎ (F ⋏ G)**)* ↔ F ⋏ G ⊆ F ⋏ H
-- H* ⊆ (F* ⋎ (F ⋏ G))* ↔ F ⋏ G ⊆ F ⋏ H
--thm_combo_algebra_statement_one

end Filters_and_PR

section PartialModAndConsequences


theorem thm_partialModularity (F G H : Family α) : (F ⋎ (G ⋏ H)) ⊆ (F ⋎ G) ⋏ H := by sorry
theorem thm_partialDistrubityivty (F G H : Family α) : (F ⋏ G) ⋎ (F ⋏ H) ⊆ F ⋏ (G ⋎ H) := by sorry
theorem thm_identityOne (F G : Family α) : F ⊆ (F ⋎ G) ⋏ G* := by sorry
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

theorem thm_identityTwo (F G H : Family α) : F ⋎ G ⊆ H ↔ F ⊆ H ⋏ G* := by sorry
theorem thm_familyMeetIsIdempotentAtPRFamiliesnew (F : Family α) : F ⋏ F = F ↔ isPRFamily F := by
  constructor
  · intro h
    unfold isPRFamily
    intro A hA n c
    sorry
  · intro h
    unfold isPRFamily at h
    sorry
theorem thm_combo_algebra_statement_one (F G H : Family α) : H* ⊆ F ⋏ (F* ⋎ G*) ↔ F ⋏ G ⊆ F ⋏ H :=
by
  nth_rw 1 [← thm_dual_is_involution (F ⋏ (F* ⋎ G*))]
  rw [thm_de_morgan_v1_dual]
  rw [thm_de_morgan_union_v1]
  repeat rw [thm_dual_is_involution]
  rw [← thm_de_morgan_v1_dual]
  have step : H* ⊆ F⋏(F⋏G)* ↔ ((H* ⊆ F) ∧ (H* ⊆ (F ⋏ G)*)) := by sorry
  rw [step]
  constructor
  · intro h
    have h2 : H* ⊆ (F ⋏ G)* := h.2
    have h_anti := thm_dual_is_antitone _ _ h2
    rw [thm_dual_is_involution, thm_dual_is_involution] at h_anti
    intro A hA
    have hmono : (F ⋏ G) ⋏ F ⊆ H ⋏ F :=
      thm_familyMeetIsMonotone (F ⋏ G) H F h_anti
    have h2 : (F ⋏ G) ⋏ F = F ⋏ G := by
      rw [←thm_familyMeetIsAssociative]
      rw [thm_familyMeetIsCommutative G F]
      rw [thm_familyMeetIsAssociative]
      sorry
    have h3 : H ⋏ F = F ⋏ H := by
      rw [thm_familyMeetIsCommutative]
    have h4 : F ⋏ G ⊆ F ⋏ H := by
      rw [← h2]
      rw [←h3]
      exact hmono
    exact h4 hA
  · intro h
    rw [←step] at ⊢
    rw [thm_de_morgan_v1_dual]

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



theorem thm_de_morgan_union_v1old (F G : Family α) : (F ⋎ G)* = (F* ⋏ G*) :=
  by sorry
  /-ext A
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
      change B ∈ famJoin F G at hBinFuG
      unfold _root_.famJoin at hBinFuG
      by_cases hF : F.sets = ∅
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
  sorry -/


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
