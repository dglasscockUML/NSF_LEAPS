import NSFLEAPS._03_Family_algebra.FA_Defs

variable (fam famB: Family S)
#check fam
#check fam* = fam
variable (α : Type _) (J K L : Set (Set α))
#check J
#check J*
#check J** = J
#check J
#check K

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

--added this to get ext A to work, not sure why mine wasn't working but angelina's was
-- @[ext]
-- lemma Family.ext {α} {F G : Family α}
--   (h : F.sets = G.sets) : F = G := by
--   cases F
--   cases G
--   cases h
--   rfl

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

theorem dual_dual_smth_smth (F : Family α) : F** = F := by
  ext A
  rw [mem_dual_alt]      -- 'A ∈ F**'
  rw [mem_dual_alt]      -- 'Aᶜ ∈ F*' inside the negation
  rw [compl_compl]
  push_neg
  rfl

-- theorem dual_dual_smth_smth (F : Family α) : F** = F := by
-- -- famDualAlt is a set equality lemma and ext requires membership based ones
--   apply SetLike.coe_injective
--   rw [famDualAlt (F*)]
--   ext A
--   dsimp
--   have h_inner : ∀ (X : Set α), X ∈ F* ↔ Xᶜ ∉ F := Set.ext_iff.mp (famDualAlt F)
--   rw [h_inner Aᶜ]
--   push_neg
--   rw [compl_compl]
--   rfl


theorem thm_dual_is_involution (F : Family α) : F** = F := by
ext A
constructor
-- F** ⊆ F
· intro h
  by_contra hA
  have h1 : Aᶜ ∉ F* := by
    --rw [famDualAlt] at h
    sorry
  have h2 : Aᶜ ∈ F* := by
    have : (Aᶜ)ᶜ ∉ F := by
      simpa [compl_compl] using hA
    sorry
  exact h1 h2

-- F ⊆ F**
· intro hA B hB
  specialize hB A hA
  exact Set.inter_nonempty_iff_exists_right.mpr hB



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

-- theorem thm_dual_is_antitone (F G : Family α) : F.sets ⊆ G.sets → (F*).sets ⊆ (G*).sets :=
--  by sorry

theorem thm_dual_is_antitone (F G : Family α) : F ⊆ G → G* ⊆ F* :=
 by
  intro h A hAinF
  rw [famDualAlt] at hAinF
  rw [famDualAlt]
  simp only [Set.mem_setOf_eq] at hAinF ⊢
  -- hAinF is: Aᶜ ∉ F
  -- Goal is: Aᶜ ∉ G
  intro hAcinG
  apply hAinF
  exact h hAcinG
  /-
  intro h A hAinF
  -- rewrite F* membership using characterization
  rw [famDualAlt] at hAinF
  -- want: A ∈ G* ↔ Aᶜ ∉ G
  rw [famDualAlt]
  -- prove by contradiction
  intro hAcinG
  -- F ⊆ G means if Aᶜ ∈ F then Aᶜ ∈ G, so contrapositive: if Aᶜ ∉ G then Aᶜ ∉ F
  have hAcinF_not : Aᶜ ∉ F := by
    intro hAcinF'
    have hAcinG' : Aᶜ ∈ G := h hAcinF'
    contradiction
  exact hAinF (by
    -- Prove by contradiction using the forward inclusion
    by_contra h_contra
    -- If Aᶜ ∉ F is false, then Aᶜ ∈ F
    have h_in_G := h h_contra
    exact hAcinG h_in_G
  )
  sorry -/

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
3. for all C ∈ F and D ∈ G, A ∩ C ∩ D̸ = ∅
– definition
4. for all C ∈ F, A ∩ C ∈ G∗
– definition
5. A ∈ F∗ ⋏ G∗-/
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
      sorry
    · intro h B hBinFuG
      sorry
  have equiv34 : CDinter ↔ CinterAinGdual := by sorry
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
  by sorry

--thm_classcap_contains_union
theorem thm_familyJoinContainsUnion (F G : Family α) : (F ∪ G) ⊆ (F ⋎ G)  :=
  by sorry
-- need to define what a subset of Fam is

--thm_classcap_commutative
theorem thm_familyJoinIsCommutative (F G : Family α) : (F ⋎ G) = (G ⋎ F) :=
  by
    ext A
    constructor
    · intro h
      sorry
    · intro h
      sorry

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
theorem thm_familyJoinIsAssociative (F G H : Family α) : (F ⋎ (G ⋎ H)) = ((F ⋎ G) ⋎ H) :=
  by
    ext A
    by_cases hF : F.sets = ∅
    · by_cases hG : G.sets = ∅
      · by_cases hH : H.sets = ∅
        · sorry  -- All empty
        · sorry  -- F and G empty, H nonempty
      · by_cases hH : H.sets = ∅
        · sorry  -- F and H empty, G nonempty
        · sorry  -- F empty, G and H nonempty
    · by_cases hG : G.sets = ∅
      · by_cases hH : H.sets = ∅
        · sorry  -- F and H nonempty, G empty
        · sorry  -- F nonempty, G and H nonempty
      · by_cases hH : H.sets = ∅
        · sorry  -- F and G nonempty, H empty
        · -- All nonempty: F, G, H all nonempty
          simp only [_root_.famJoin, hF, hG, hH, if_false]
          constructor
          · intro ⟨a, ha, b, ⟨c, hc, d, hd, hab_eq⟩, rfl⟩
            exact ⟨a ∩ c, ⟨a, ha, c, hc, rfl⟩, d, hd, by rw [Set.inter_assoc, hab_eq]⟩
          · intro ⟨⟨a, ha, c, hc, rfl⟩, b, hb, rfl⟩
            exact ⟨a, ha, c ∩ b, ⟨c, hc, b, hb, rfl⟩, by rw [Set.inter_assoc]⟩

--thm_classcap_monotone
theorem thm_familyJoinIsMonotone (F G H : Family α) : F ⊆ G → (F ⋎ H) ⊆ (G ⋎ H) :=
  by sorry

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
--thm_classcapdual_associative
theorem thm_familyMeetIsAssociative (F G H : Family α) : (F ⋏ (G ⋏ H)) = ((F ⋏ G) ⋏ H) :=
  by sorry

--thm_classcapdual_monotone ***
theorem thm_familyMeetIsMonotone (F G H : Family α) : F ⊆ G → (F ⋏ H) ⊆ (G ⋏ H) :=
  by sorry
--thm_family_classcapdual_dual_is_filter
theorem thm_familyMeetIsFilter (F : Family α) : isFilterFamily (F ⋏ F*) :=
  by sorry
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
