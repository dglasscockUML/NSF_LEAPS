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
 --complement of A in S not in F}

--added this to get ext A to work, not sure why mine wasn't working but angelina's was
@[ext]
lemma Family.ext {α} {F G : Family α}
  (h : F.sets = G.sets) : F = G := by
  cases F
  cases G
  cases h
  rfl

/- @[simp]
lemma dual_sets (F : Family α) :
  (F* : Set (Set α)) = {A : Set α | Aᶜ ∉ F} :=
by
  simpa using thm_equiv_dual_formulation (F := F) -/

#check famDualAlt
/-have dualEquivForm : (F*).sets = {A : Set S | Aᶜ ∉ syndeticFamily S} :=
    thm_equiv_dual_formulation (F)
  rw [dualEquivForm]-/
@[simp]
theorem Family.coe_sets (F : Family α) :
    (↑F : Set (Set α)) = F.sets :=
  rfl

theorem thm_dual_is_involution (F : Family α) : F** = F := by
ext A
constructor
-- F** ⊆ F
· intro h
  by_contra hA
  have h1 : Aᶜ ∉ F* := by
    simp [famDualAlt] at h
    sorry
  have h2 : Aᶜ ∈ F* := by
    have : (Aᶜ)ᶜ ∉ F := by
      simpa [compl_compl] using hA
    sorry
  exact h1 h2

-- F ⊆ F**
· intro hA
  by_contra h
  have h1 : Aᶜ ∈ F* := by
    sorry
  have h2 : Aᶜ ∉ F* := by
    intro hAc
    have : A ∉ F := by
      sorry
    exact sorry
  exact h2 h1
/- theorem thm_dual_is_involution (F : Family α) : F** = F := by
  ext A
  constructor
  -- F** ⊆ F
  · intro h
    have h1 : Aᶜ ∉ (F*) := by
      intro hAc
      have hAc' : Aᶜ ∈ {A | Aᶜ ∉ F} := by
        rw [←famDualAlt]
        exact hAc
      have hAc'' : (Aᶜ)ᶜ ∉ F := by
        rw [Set.mem_setOf] at hAc'
        exact hAc'
      have : (Aᶜ)ᶜ = A := by
        simp only [compl_compl]
      rw [this] at hAc''
      have : Aᶜ ∈ (F* : Set (Set α)) := by
        have : (Aᶜ)ᶜ ∉ F := by
          simpa [compl_compl] using hAc''
        simpa [←famDualAlt]
          using this
      contradiction
  · intro h3
    have h1 : Aᶜ ∉ F := by
      intro hAc
      have hAc' : Aᶜ ∈ {A | Aᶜ ∉ F} := by
        rw [←famDualAlt]
        exact hAc
      have hAc'' : (Aᶜ)ᶜ ∉ F := by
        rw [Set.mem_setOf] at hAc'
        exact hAc'
      have : (Aᶜ)ᶜ = A := by
        simp only [compl_compl]
      rw [this] at hAc''
      have : Aᶜ ∈ (F* : Set (Set α)) := by
        have : (Aᶜ)ᶜ ∉ F := by
          simpa [compl_compl] using hAc''
        simpa [←famDualAlt]
      contradiction
 -/

  --F ⊆ F**

 -- F** ⊆ F
 -- F ⊆ F**

--maybe funky
theorem thm_dual_is_bijection_on_fams (dual : Family α → Family α)
  (h : ∀ (F: Family α), dual (dual F) = F) : Function.Bijective dual :=
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
theorem thm_dual_is_antitone (F G : Family α) : F ⊆ G → F* ⊆ G* :=
 by
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
  exact hAcinF_not sorry

theorem thm_pr_iff_dual_is_filter (P : Family α) : isIntersectionClosed (P.sets)* ↔ partitionRegularTwoSets (P.sets) :=
 by sorry

--thm_family_equal_to_dual_iff_ultrafilter
--theorem thm_family_equal_to_dual_iff_ultrafilter (F : Family α) : F* = F ↔ UltrafilterFamily F :=
 -- by sorry

--thm_de_morgan_union_v1
theorem thm_de_morgan_union_v1 (F G : Family α) : (F ⋎ G)* = (F* ⋏ G*) :=
  by
    ext A
    sorry
    /- constructor
    · intro h
    -- want: A ∈ F* ⋏ G* ↔ Aᶜ ∉ F.sets ∧ Aᶜ ∉ G.sets
      constructor
      · intro hF
      -- hF : Aᶜ ∈ F.sets → contradiction with h
        exact h (Or.inl hF)
      · intro hG
        exact h (Or.inr hG)
    · intro h
    -- h : ¬Aᶜ ∈ F.sets ∧ ¬Aᶜ ∈ G.sets
      intro hOr
      cases hOr with
      | inl hF => exact h.left hF
      | inr hG => exact h.right hG
 -/

--thm_de_morgan_union_v2
theorem thm_de_morgan_union_v2 (F G : Family α) : (F ∪ G)* = (F* ∩ G*) :=
 by sorry

--thm_de_morgan_v1_dual
theorem thm_de_morgan_v1_dual (F G : Family α) : (F ⋏ G)* = (F* ⋎ G*) :=
  by sorry

--thm_classcap_contains_union
theorem thm_classcap_contains_union (F G : Family α) : (F ∪ G) ⊆ (F ⋎ G)  :=
  by sorry
-- need to define what a subset of Fam is

--thm_classcap_commutative
theorem thm_classcap_commutative (F G : Family α) : (F ⋎ G) = (G ⋎ F) :=
  by sorry

--thm_classcap_associative
theorem thm_classcap_associative (F G H : Family α) : (F ⋎ (G ⋎ H)) = ((F ⋎ G) ⋎ H) :=
  by sorry

--thm_classcap_monotone
theorem thm_classcap_monotone (F G H : Family α) : F ⊆ G → (F ⋎ H) ⊆ (G ⋎ H) :=
  by sorry

--thm_family_classcap_dual_is_partition_regular
theorem thm_family_classcap_dual_is_partition_regular (F : Family α) : isPRTwoSets (F ⋎ F*) :=
  by sorry

--thm_classcap_idempotent_at_filters

--thm_family_classcapdual_is_family don't need
--theorem thm_family_classcapdual_is_family (F : Family α) : Family (F ⋎ F*) :=
--  by sorry

--thm_classcapdual_contained_in_intersection ***
theorem thm_classcapdual_contained_in_intersection (F G : Family α) : (F ⋏ G) ⊆ (F ∩ G) :=
  by sorry


--thm_classcapdual_commutative
theorem thm_classcapdual_commutative (F G : Family α) : (F ⋏ G) = (G ⋏ F) :=
  by sorry
--thm_classcapdual_associative
theorem thm_classcapdual_associative (F G H : Family α) : (F ⋏ (G ⋏ H)) = ((F ⋏ G) ⋏ H) :=
  by sorry

--thm_classcapdual_monotone ***
theorem thm_classcapdual_monotone (F G H : Family α) : F ⊆ G → (F ⋏ H) ⊆ (G ⋏ H) :=
  by sorry
--thm_family_classcapdual_dual_is_filter
theorem thm_family_classcapdual_dual_is_filter (F : Family α) : isFilterFamily (F ⋏ F*) :=
  by sorry
-- F ⋏ F = F ↔ isPRFamily F
theorem thm_classcapdual_idempotent_at_pr_families (F : Family α) :
  F ⋏ F = F ↔ isPRFamily F := by sorry
--
--thm_combo_algebra_statement_one
theorem thm_combo_algebra_statement_one (F G H : Family α) : H* ⊆ F ⋏ (F* ⋎ G*) ↔ F ⋏ G ⊆ F ⋏ H :=
by
  classical
  constructor
  · intro h A hAG
    -- goal: A ∩ B ∈ H
    have h1 : A ∈ F ⋏ G := hAG
    -- unfold definition of F ⋏ G
    have h2 : ∀ C ∈ F*, A ∩ C ∈ G := sorry
    -- now use assumption h on H*
    -- need to show A ∩ B ∈ H* unfolding dual definition
    -- finish depending on definition of *
    sorry

  · intro h A hA
    -- goal: A ∩ B ∈ H*
    -- unfold H* membership and use inclusion h
    sorry
