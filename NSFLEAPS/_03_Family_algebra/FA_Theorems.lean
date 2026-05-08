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
@[ext]
lemma Family.ext {α} {F G : Family α}
  (h : F.sets = G.sets) : F = G := by
  cases F
  cases G
  cases h
  rfl


variable (F : Family α)
#check F**
theorem dualIsInvolutionOnFamilies (F : Family α) : F** = F := by
have coerce: ↑F** = (F**).sets := by
  exact Set.Subset.antisymm (fun ⦃a⦄ a_1 ↦ a_1) fun ⦃a⦄ a_1 ↦ a_1
have coerce2: ↑F* = (F*).sets := by
  exact Set.Subset.antisymm (fun ⦃a⦄ a_1 ↦ a_1) fun ⦃a⦄ a_1 ↦ a_1
ext A
constructor
-- F** ⊆ F
· rw [←coerce]
  rw [famDualAlt F*]
  intro h
  have h1 : Aᶜ ∉ (F*).sets := by
    exact h
  rw [←coerce2] at h1
  rw [famDualAlt F] at h1
  simp only [Set.mem_setOf_eq, compl_compl, not_not] at h1
  exact h1
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

theorem thm_pr_iff_dual_is_filter (P : Family α) : isIntersectionClosed (P.sets)* ↔
  partitionRegularTwoSets (P.sets) :=
 by sorry

--thm_family_equal_to_dual_iff_ultrafilter
--theorem thm_family_equal_to_dual_iff_ultrafilter (F : Family α) : F* = F ↔ UltrafilterFamily F :=
 -- by sorry

--thm_de_morgan_union_v1
theorem thm_de_morgan_union_v1 (F G : Family α) : (F ⋎ G)* = (F* ⋏ G*) :=
  by
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
