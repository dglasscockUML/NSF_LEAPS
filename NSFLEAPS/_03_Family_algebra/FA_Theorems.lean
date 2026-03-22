import NSFLEAPS._03_Family_algebra.FA_Defs

variable (fam : Family S)
#check fam
#check fam*
variable (α : Type _) (J K L : Set (Set α))
#check J
#check J*
#check J** = J
#check J
#check K

theorem thm_equiv_dual_formulation {α} (F : Family α) :
(F*).sets = {A : Set α | Aᶜ ∉ F.sets} :=
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

theorem thm_dual_is_involution (F : Family α) : F** = F :=
  by
  ext A
  constructor
  · -- F** ⊆ F
    intro AinDualDual --have some F**
    by_contra h --assume F** not in F
    have AinDual : A ∈ (F*).sets := by
      intro B BinF
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
      sorry
    sorry
  · -- F ⊆ F**
    intro AinF
    by_contra h
    have AinDual : A ∈ (F*).sets := by
      intro B BinF
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
      sorry
    sorry
  --split into 2 cases,
 -- F** ⊆ F
 -- F ⊆ F**


theorem thm_dual_is_bijection_on_fams (dual : Family α → Family α)
  (h : ∀ F, dual (dual F) = F) : Function.Bijective dual :=
  by sorry

-- theorem thm_dual_is_antitone (F G : Family α) : F.sets ⊆ G.sets → (F*).sets ⊆ (G*).sets :=
--  by sorry
theorem thm_dual_is_antitone (F G : Family α) : F ⊆ G → F* ⊆ G* :=
 by sorry
-- need to define what a subset of Fam is

--theorem thm_pr_iff_dual_is_filter (P : PRFamily α) : FilterFamily (P.sets*) :=
--  by sorry

--thm_family_equal_to_dual_iff_ultrafilter
--theorem thm_family_equal_to_dual_iff_ultrafilter (F : Family α) : F* = F ↔ UltrafilterFamily F :=
 -- by sorry

--thm_de_morgan_union_v1
theorem thm_de_morgan_union_v1 (F G : Family α) : (F ⋎ G)* = (F* ⋏ G*) :=
  by sorry

--thm_de_morgan_union_v2
theorem thm_de_morgan_union_v2 (F G : Family α) : (F.sets ∪ G.sets)* = ((F*).sets ∩ (G*).sets) :=
 by sorry

--thm_de_morgan_v1_dual
theorem thm_de_morgan_v1_dual (F G : Family α) : (F ⋏ G)* = (F* ⋎ G*) :=
  by sorry

--thm_classcap_contains_union
--theorem thm_classcap_contains_union (F G : Family α) : F ⋎ G ⊇ F ∪ G :=
--  by sorry
-- need to define what a subset of Fam is

--thm_classcap_commutative
theorem thm_classcap_commutative (F G : Family α) : (F ⋎ G) = (G ⋎ F) :=
  by sorry

--thm_classcap_associative
theorem thm_classcap_associative (F G H : Family α) : (F ⋎ (G ⋎ H)) = ((F ⋎ G) ⋎ H) :=
  by sorry

--thm_classcap_monotone
theorem thm_classcap_monotone (F G H : Family α) : F.sets ⊆ G.sets → (F ⋎ H).sets ⊆ (G ⋎ H).sets :=
  by sorry

--thm_family_classcap_dual_is_partition_regular
theorem thm_family_classcap_dual_is_partition_regular (F : Family α) : isPRTwoSets (F ⋎ F*) :=
  by sorry

--thm_classcap_idempotent_at_filters

--thm_family_classcapdual_is_family
--theorem thm_family_classcapdual_is_family (F : Family α) : Family (F ⋎ F*) :=
 -- by sorry

--thm_classcapdual_contained_in_intersection
theorem thm_classcapdual_contained_in_intersection (F G : Family α) : (F ⋏ G).sets ⊆ F.sets ∩ G.sets :=
  by sorry
-- need to define what a subset of Fam is


--thm_classcapdual_commutative
theorem thm_classcapdual_commutative (F G : Family α) : (F ⋏ G) = (G ⋏ F) :=
  by sorry
--thm_classcapdual_associative
theorem thm_classcapdual_associative (F G H : Family α) : (F ⋏ (G ⋏ H)) = ((F ⋏ G) ⋏ H) :=
  by sorry

--thm_classcapdual_monotone
theorem thm_classcapdual_monotone (F G H : Family α) : F.sets ⊆ G.sets → (F ⋏ H).sets ⊆ (G ⋏ H).sets :=
  by sorry
--thm_family_classcapdual_dual_is_filter
--theorem thm_family_classcapdual_dual_is_filter (F : Family α) : FilterFamily (F ⋏ F*) :=
 -- by sorry

--thm_classcapdual_idempotent_at_pr_families
