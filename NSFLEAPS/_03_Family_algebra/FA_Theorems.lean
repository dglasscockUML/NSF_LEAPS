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
(F*).sets = {A : Set α | ¬ (Aᶜ ∈ F.sets)} :=
sorry --complement of A in S not in F}

theorem thm_dual_is_involution (F : Family α) : F** = F :=
  by sorry

theorem thm_dual_is_bijection (dual : Family α → Family α)
  (h : ∀ F, dual (dual F) = F) : Function.Bijective dual :=
  by sorry

theorem thm_dual_is_antitone (F G : Family α) : F ⊆ G → F* ⊆ G* :=
  by sorry
-- need to define what a subset of Fam is

theorem thm_pr_iff_dual_is_filter (P : PRFamily α) : FilterFamily (P*) :=
  by sorry

--thm_family_equal_to_dual_iff_ultrafilter

--thm_de_morgan_union_v1

--thm_de_morgan_union_v2

--thm_classcap_contains_union

--thm_classcap_commutative

--thm_classcap_associative

--thm_classcap_monotone

--thm_family_classcap_dual_is_partition_regular

--thm_classcap_idempotent_at_filters

--thm_family_classcapdual_is_family

--thm_classcapdual_contained_in_intersection

--thm_classcapdual_commutative

--thm_classcapdual_associative

--thm_classcapdual_monotone

--thm_family_classcapdual_dual_is_filter

--thm_classcapdual_idempotent_at_pr_families
