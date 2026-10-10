module

public import NSFLEAPS._03_Family_algebra.FA_Defs

/-!
# Furstenberg family theorems

This file develops the main abstract theorems governing the algebra
of Furstenberg families.
-/

public section

section Dual

/-- F* consists of all set A such that Aᶜ is not in F -/
theorem famDualAlt
{α : Type*} (F : Family α) :
F* = {A : Set α | Aᶜ ∉ F} := by
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

/-- A belongs to F* if and only if Aᶜ is not in F -/
lemma mem_dual_alt
{α : Type*} {F : Family α} {A : Set α} :
A ∈ F* ↔ Aᶜ ∉ F :=
  Set.ext_iff.mp (famDualAlt F) A

/-- Dual of dual of F is equal to F -/
theorem dualIsInvolutionOnFamilies
{α : Type*} (F : Family α) :
F** = F := by
  ext A
  rw [mem_dual_alt]      -- 'A ∈ F**'
  rw [mem_dual_alt]      -- 'Aᶜ ∈ F*' inside the negation
  rw [compl_compl]
  push Not
  rfl

/-- If F ⊆ G, then G* ⊆ F* -/
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

/-- First DeMorgan for family algebra -/
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

/-- Second DeMorgan's law for family algebra -/
theorem familyDeMorgan2
{α : Type*} (F G : Family α) :
(F ⋏ G)* = (F* ⋎ G*) :=
  by
  -- h : (F* ⋎ G*)* = F** ⋏ G**
  have h := familyDeMorgan1 F* G*
  repeat rw [dualIsInvolutionOnFamilies] at h
  rw [← h]
  rw [dualIsInvolutionOnFamilies]

/-- Dual of union of families is intersection of dual of families -/
theorem unionDeMorgan1
{α β : Type*} (F : β → Family α) :
(Family.iUnion F)* = Family.iInter (fun (b : β) ↦ (F b)*) := by
  ext A
  constructor
  · intro hA G hG
    simp only [Set.mem_range] at hG
    rcases hG with ⟨y, hy⟩
    simp only [HasFamDual.famDual, Family.famDual, famDual, Family.iUnion, Set.mem_iUnion,
      forall_exists_index] at hA
    rw [<- hy]
    intro B hB
    specialize hA B y hB
    exact hA
  · intro hA B hB
    simp only [Family.mem_iUnion] at hB
    rcases hB with ⟨i, hi⟩
    have hFi : ((F i)*).sets ∈ Set.range fun i ↦ ((fun b ↦ (F b)*) i).sets := by
      simp
    specialize hA (F i)* hFi
    simp only [HasFamDual.famDual, famDual, SetLike.mem_coe, Set.mem_ofPred_eq] at hA
    specialize hA B hi
    exact hA

/-- Dual of intersection of families is union of dual of families -/
theorem unionDeMorgan2
{α β : Type*} (F : β → Family α) :
(Family.iInter F)* = Family.iUnion (fun (b : β) ↦ (F b)*) := by
  ext A
  constructor
  · intro hA
    simp only [Family.iUnion]
    have hAIn : A ∈ ⋃ i : β, ((F i)*).sets := by
      simp only [Set.mem_iUnion]
      simp only [Family.iInter] at hA
      by_contra hContra
      simp only [not_exists] at hContra
      simp only [HasFamDual.famDual, Family.famDual, famDual, Set.mem_ofPred_eq, not_forall]
        at hContra
      choose f hf1 hf2 using hContra
      let B := ⋃ i : β, f i
      have hBin : B ∈ ⋂ i : β, (F i).sets := by
        simp only [Set.mem_iInter]
        intro i
        specialize hf1 i
        simp only [B]
        apply (F i).upward_closed (f i)
        · exact hf1
        · intro a ha
          simp only [Set.mem_iUnion]
          use i
      specialize hA B hBin
      have hABEmp : ¬ (A ∩ B).Nonempty := by
        simp only [Set.inter_iUnion, Set.nonempty_iUnion, not_exists, B]
        exact hf2
      exact hABEmp hA
    exact hAIn
  · intro hA B hB
    simp only [Family.mem_iInter] at hB
    simp only [Family.iUnion] at hA
    have hAIn : A ∈ ⋃ i : β, ((F i)*).sets := by
      exact hA
    simp only [Set.mem_iUnion] at hAIn
    rcases hAIn with ⟨i, hi⟩
    specialize hB i
    specialize hi B hB
    exact hi

end DeMorgan

section Join

/-- Family join is associative -/
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

/-- Family join is commutative -/
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

/-- Family join is monotonic -/
theorem familyJoinIsMonotonic
{α : Type*} {F1 G1 F2 G2 : Family α} :
F1 ⊆ G1 → F2 ⊆ G2 → (F1 ⋎ F2) ⊆ (G1 ⋎ G2) := by
  intro h1 h2
  simp only [HasFamJoin.famJoin, Family.famJoin, famJoin]
  intro B hB
  simp only [SetLike.mem_coe] at hB
  rcases hB with ⟨C, hC, D, hD, hB2⟩
  use C
  constructor
  · apply h1 hC
  · use D
    constructor
    · apply h2 hD
    · exact hB2

/-- Family join is monotonic slot 1 -/
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

/-- Family join is monotonic slot 2 -/
theorem familyJoinIsMonotonicSlot2
{α : Type*} (F : Family α) {G H : Family α} :
G ⊆ H → (F ⋎ G) ⊆ (F ⋎ H) := by
  intro GinH
  exact familyJoinIsMonotonic (Family.rfl F) GinH

/-- If G is not the empty family, then F ⊆ (F ⋎ G) -/
theorem familyContainedInFamilyJoin
{α : Type*} (F G : Family α) :
G ≠ emptyFam α → F ⊆ (F ⋎ G) := by
  intro hG A hA
  simp only [HasFamJoin.famJoin, Family.famJoin, famJoin, SetLike.mem_coe]
  use A
  constructor
  · exact hA
  · use Set.univ
    constructor
    · have hGSets : G.sets.Nonempty := by
        apply (notEmptyFam G).mp
        · exact hG
      simp only [Set.nonempty_def] at hGSets
      rcases hGSets with ⟨B, hB⟩
      apply G.upward_closed B
      · exact hB
      · simp
    · simp

/-- F ⋎ G = emptyFam α if and only if F = emptyFam α ∨ G = emptyFam α -/
theorem emptyFamilyJoinCondition
{α : Type*} (F G : Family α) :
F ⋎ G = emptyFam α ↔ F = emptyFam α ∨ G = emptyFam α := by
  constructor
  · intro hFG
    by_contra hContra1
    simp only [not_or] at hContra1
    rcases hContra1 with ⟨hF, hG⟩
    have hFNonEmp := (notEmptyFam F).mp hF
    have hGNonEmp := (notEmptyFam G).mp hG
    rcases hFNonEmp with ⟨A, hA⟩
    rcases hGNonEmp with ⟨B, hB⟩
    have hAB : A ∩ B ∈ F ⋎ G := by
      use A
      constructor
      · exact hA
      · use B
    rw [hFG] at hAB
    simp only [emptyFam] at hAB
    exact hAB
  · intro hFG
    rcases hFG with hF | hG
    · by_contra hContra
      have hFGNon := (notEmptyFam (F ⋎ G)).mp hContra
      rcases hFGNon with ⟨A, hA⟩
      simp only [HasFamJoin.famJoin, Family.famJoin, famJoin, Set.mem_ofPred_eq] at hA
      rcases hA with ⟨B, hB, C, hC, hBC⟩
      rcases hF
      exact hB
    · by_contra hContra
      have hFGNon := (notEmptyFam (F ⋎ G)).mp hContra
      rcases hFGNon with ⟨A, hA⟩
      simp only [HasFamJoin.famJoin, Family.famJoin, famJoin, Set.mem_ofPred_eq] at hA
      rcases hA with ⟨B, hB, C, hC, hBC⟩
      rcases hG
      exact hC

/-- F ⋎ G = fullFam α if and only if ¬(F ⊆ G*) -/
theorem fullFamilyJoinCondition
{α : Type*} (F G : Family α) :
F ⋎ G = fullFam α ↔ ¬(F ⊆ G*) := by
  constructor
  · intro hFG
    simp only [fullFam, fullCollection, Set.powerset_univ] at hFG
    have hFGSets : (F ⋎ G).sets = Set.univ := by
      rw [hFG]
    have hEmp : ∅ ∈ (F ⋎ G).sets := by
      rw [hFGSets]
      simp
    simp only [HasFamJoin.famJoin, Family.famJoin, famJoin, Set.mem_ofPred_eq] at hEmp
    rcases hEmp with ⟨A, hA, B, hB, hAB⟩
    by_contra hContra
    have hAG : A ∈ G* := by
      apply hContra hA
    simp only [HasFamDual.famDual, Family.famDual, famDual] at hAG
    specialize hAG B hB
    rw [<- hAB] at hAG
    rcases hAG with ⟨x, hx⟩
    exact hx
  · intro hFG
    apply Set.not_subset.mp at hFG
    rcases hFG with ⟨A, hA1, hA2⟩
    have hGoal : ∃ B ∈ G, A ∩ B = ∅ := by
      by_contra hContra
      simp only [not_exists, not_and] at hContra
      have hAinGStar : A ∈ G* := by
        intro B hB
        specialize hContra B hB
        simp only [← Set.not_nonempty_iff_eq_empty, not_not] at hContra
        exact hContra
      exact hA2 hAinGStar
    rcases hGoal with ⟨B, hB1, hB2⟩
    have hEmpFG : ∅ ∈ F ⋎ G := by
      simp only [HasFamJoin.famJoin, Family.famJoin, famJoin]
      use A
      constructor
      · exact hA1
      · use B
        constructor
        · exact hB1
        · rw [hB2]
    simp only [fullFam, fullCollection, Set.powerset_univ]
    have hFGUniv : (F ⋎ G).sets = Set.univ := by
      ext D
      constructor
      · intro hD
        simp
      · intro hD
        apply (F ⋎ G).upward_closed ∅
        · exact hEmpFG
        · simp
    ext C
    constructor
    · intro hC
      have hCUniv : C ∈ Set.univ := by
        simp
      exact hCUniv
    · intro hC
      have hCUniv : C ∈ (F ⋎ G).sets := by
        rw [hFGUniv]
        simp
      exact hCUniv

end Join

section Meet

/-- Family meet is associative -/
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

/-- Family meet is commutative -/
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

/-- Family meet is monotonic -/
theorem familyMeetIsMonotonic
{α : Type*} {F1 G1 F2 G2 : Family α} :
F1 ⊆ G1 → F2 ⊆ G2 → (F1 ⋏ F2) ⊆ (G1 ⋏ G2) := by
  intro h1 h2 A hA
  simp only [HasFamMeet.famMeet, Family.famMeet, famMeet]
  intro B hB
  have hBinF1star : B ∈ F1* := by
    have hG1F1 : G1* ⊆ F1* := by
      apply dualIsAntitone
      exact h1
    apply hG1F1 hB
  specialize hA B hBinF1star
  apply h2 hA

/-- Family meet is monotonic slot 1 -/
theorem familyMeetIsMonotonicSlot1
{α : Type*} {F G : Family α} (H : Family α) :
F ⊆ G → (F ⋏ H) ⊆ (G ⋏ H) := by
  intro hFG
  apply familyMeetIsMonotonic
  · exact hFG
  · intro t ht
    exact ht

/-- Family meet is monotonic slot 2 -/
theorem familyMeetIsMonotonicSlot2
{α : Type*} (F : Family α) {G H : Family α} :
G ⊆ H → (F ⋏ G) ⊆ (F ⋏ H) := by
  intro GinH
  exact familyMeetIsMonotonic (Family.rfl F) GinH

/-- If G is not fullFam, then F ⋏ G ⊆ F -/
theorem familyMeetContainedInIntersection
{α : Type*} (F G : Family α) :
G ≠ fullFam α → F ⋏ G ⊆ F := by
  intro hG A hA
  rw [familyMeetIsCommutative] at hA
  have hGstarNonEmp : Set.univ ∈ G* := by
    simp only [HasFamDual.famDual, Family.famDual, famDual]
    intro B hB
    have hBNonempty : B.Nonempty := by
      by_contra hContra
      simp only [Set.not_nonempty_iff_eq_empty] at hContra
      have hGFullFam : G = fullFam α := by
        ext C
        constructor
        · intro hC
          simp only [fullFam, fullCollection, Set.powerset_univ]
          have hCinUniv : C ∈ Set.univ := by
            simp
          exact hCinUniv
        · intro hC
          apply G.upward_closed ∅
          · rw [hContra] at hB
            exact hB
          · simp
      exact hG hGFullFam
    have hUnivB : Set.univ ∩ B = B := by
      simp
    rw [hUnivB]
    exact hBNonempty
  specialize hA Set.univ hGstarNonEmp
  simp only [Set.inter_univ] at hA
  exact hA

/-- Dual of fullFam is emptyFam -/
lemma fullFamDual
{α : Type*} : (fullFam α)* = emptyFam α := by
  simp only [HasFamDual.famDual, Family.famDual, famDual]
  ext A
  constructor
  · intro hA
    have hEmpFull : ∅ ∈ (fullFam α).sets := by
      simp [fullFam, fullCollection]
    specialize hA ∅ hEmpFull
    simp only [emptyFam]
    rcases hA with ⟨x, hx1, hx2⟩
    exact hx2
  · intro hA
    simp only [emptyFam] at hA
    have hAEmp : A ∈ (∅ : Set (Set α)) := by
      exact hA
    simp at hAEmp

/-- Dual of emptyFam is fullFam -/
lemma emptyFamDual
{α : Type*} : (emptyFam α)* = fullFam α := by
  simp only [HasFamDual.famDual, Family.famDual, famDual]
  ext A
  constructor
  · intro hA
    simp only [fullFam, fullCollection, Set.powerset_univ]
    have hAUniv : A ∈ Set.univ := by
      simp
    exact hAUniv
  · intro hA B hB
    simp [emptyFam] at hB

/-- F ⋏ G = fullFam α iff F = fullFam α ∨ G = fullFam α -/
theorem fullFamilyMeetCondition
{α : Type*} (F G : Family α) :
F ⋏ G = fullFam α ↔ F = fullFam α ∨ G = fullFam α := by
  constructor
  · intro hFG
    have hFGs : (F ⋏ G)* = (fullFam α)* := by
      rw [hFG]
    rw [familyDeMorgan2, fullFamDual] at hFGs
    have hFGstarOr : F* = emptyFam α ∨ G* = emptyFam α := by
      by_contra hContra
      simp only [not_or] at hContra
      rcases hContra with ⟨hContra1, hContra2⟩
      have hAFstar : ∃ A, A ∈ F* := by
        simp only [emptyFam] at hContra1
        have hFNonEmp : (F*).sets ≠ ∅:= by
          by_contra hCon1
          have hFEmp : F* = emptyFam α := by
            simp only [emptyFam]
            ext A
            constructor
            · intro hA
              have hAF : A ∈ (F*).sets := by
                exact hA
              rw [hCon1] at hAF
              exact hAF
            · intro hA
              have hAEmp : A ∈ (∅ : Set (Set α)) := by
                exact hA
              simp at hAEmp
          exact hContra1 hFEmp
        simp only [ne_eq, ← Set.nonempty_iff_ne_empty] at hFNonEmp
        rcases hFNonEmp with ⟨A, hA⟩
        use A
        exact hA
      have hBGstar : ∃ B, B ∈ G * := by
        simp only [emptyFam] at hContra1
        have hFNonEmp : (G*).sets ≠ ∅:= by
          by_contra hCon1
          have hFEmp : G* = emptyFam α := by
            simp only [emptyFam]
            ext A
            constructor
            · intro hA
              have hAF : A ∈ (G*).sets := by
                exact hA
              rw [hCon1] at hAF
              exact hAF
            · intro hA
              have hAEmp : A ∈ (∅ : Set (Set α)) := by
                exact hA
              simp at hAEmp
          exact hContra2 hFEmp
        simp only [ne_eq, ← Set.nonempty_iff_ne_empty] at hFNonEmp
        rcases hFNonEmp with ⟨A, hA⟩
        use A
        exact hA
      rcases hAFstar with ⟨A, hA⟩
      rcases hBGstar with ⟨B, hB⟩
      have hABFG : A ∩ B ∈ (F*) ⋎ (G*) := by
        simp only [HasFamJoin.famJoin, Family.famJoin, famJoin]
        use A
        constructor
        · exact hA
        · use B
          constructor
          · exact hB
          · rfl
      rw [hFGs] at hABFG
      simp only [emptyFam] at hABFG
      exact hABFG
    rcases hFGstarOr with h1 | h2
    · have hEq : (F*)* = (emptyFam α)* := by
        rw [h1]
      have hFfull : F = fullFam α := by
        rw [<- dualIsInvolutionOnFamilies F, hEq, emptyFamDual]
      simp [hFfull]
    · have hEq : (G*)* = (emptyFam α)* := by
        rw [h2]
      have hFfull : G = fullFam α := by
        rw [<- dualIsInvolutionOnFamilies G, hEq, emptyFamDual]
      simp [hFfull]
  · intro hFG
    rcases hFG with h1 | h2
    · ext A
      constructor
      · intro hA
        have hAUniv : A ∈ Set.univ := by
          simp
        simp only [fullFam, fullCollection, Set.powerset_univ]
        exact hAUniv
      · intro hA
        rw [familyMeetIsCommutative]
        intro B hB
        rw [h1]
        simp [fullFam, fullCollection]
    · ext A
      constructor
      · intro hA
        have hAUniv : A ∈ Set.univ := by
          simp
        simp only [fullFam, fullCollection, Set.powerset_univ]
        exact hAUniv
      · intro hA B hB
        rw [h2]
        simp [fullFam, fullCollection]

/-- F ⋏ G = emptyFam α iff ¬(F* ⊆ G) -/
theorem emptyFamilyMeetCondition
{α : Type*} (F G : Family α) :
F ⋏ G = emptyFam α ↔ ¬(F* ⊆ G) := by
  apply not_iff_not.mp
  constructor
  · intro h
    simp only [not_not]
    have hEx : ∃ A : Set α, A ∈ F ⋏ G := by
      simp only [emptyFam] at h
      have hFG : (F ⋏ G).sets ≠ ∅ := by
        by_contra hContra
        have hFGEmp : (F ⋏ G) = emptyFam α := by
          ext A
          constructor
          · intro hA
            have hAN : A ∈ (F ⋏ G).sets := by
              exact hA
            rw [hContra] at hAN
            exact hAN
          · intro hA
            simp only [emptyFam] at hA
            have hAN : A ∈ (∅ : Set (Set α)) := by
              exact hA
            have hEmpSub : ∅ ⊆ (F ⋏ G).sets := by
              simp
            apply hEmpSub hAN
        exact h hFGEmp
      simp only [ne_eq, ← Set.nonempty_iff_ne_empty] at hFG
      rcases hFG with ⟨A, hA⟩
      use A
      exact hA
    rcases hEx with ⟨A, hA⟩
    simp only [HasFamMeet.famMeet, Family.famMeet, famMeet] at hA
    intro B hB
    specialize hA B hB
    apply G.upward_closed (A ∩ B)
    · exact hA
    · simp
  · intro h
    simp only [not_not] at h
    simp only [emptyFam]
    have hUnivFG : Set.univ ∈ F ⋏ G := by
      intro B hB
      simp only [Set.univ_inter]
      apply h hB
    have hFGNonEmp : (F ⋏ G).sets ≠ ∅ := by
      simp only [ne_eq, ← Set.nonempty_iff_ne_empty]
      exact ⟨Set.univ, hUnivFG⟩
    by_contra hContra
    have hFGEmp : (F ⋏ G).sets = ∅ := by
      ext A
      constructor
      · intro hA
        rw [hContra] at hA
        exact hA
      · intro hA
        simp at hA
    exact hFGNonEmp hFGEmp

/-- Characterization of membership of (capFamily G f) ⋎ H -/
theorem memberOfCapFamJoinH
{α : Type*} (G H : Family α) (a f : Set α) :
a ∈ (capFamily G f) ⋎ H ↔
  (∃ g ∈ G, g ⊆ f ∧ (∃ b ∈ H, a ∩ g = b ∩ g)) :=
    by
    constructor
    · -- if `a = c ∩ b` with `c ∩ f ∈ G` and `b ∈ H`, then `g := f ∩ c` works
      rintro ⟨c, hc, b, hb, rfl⟩
      refine ⟨f ∩ c, hc, Set.inter_subset_left, b, hb, ?_⟩
      ext x
      constructor
      · rintro ⟨⟨-, hxb⟩, hxf, hxc⟩
        exact ⟨hxb, hxf, hxc⟩
      · rintro ⟨hxb, hxf, hxc⟩
        exact ⟨⟨hxc, hxb⟩, hxf, hxc⟩
    · -- if `a ∩ g = b ∩ g`, then `a = (g ∪ (a \ g)) ∩ (b ∪ (a \ g))`, where
      -- `(g ∪ (a \ g)) ∩ f ⊇ g` belongs to `G` and `b ∪ (a \ g) ⊇ b` belongs to `H`
      rintro ⟨g, hg, hgf, b, hb, hab⟩
      refine ⟨g ∪ (a ∩ gᶜ), ?_, b ∪ (a ∩ gᶜ), H.upward_closed b _ hb Set.subset_union_left, ?_⟩
      · exact G.upward_closed g _ hg fun x hx ↦ ⟨hgf hx, Or.inl hx⟩
      · ext x
        constructor
        · intro hxa
          by_cases hxg : x ∈ g
          · have hxb : x ∈ b ∩ g := by
              rw [← hab]
              exact ⟨hxa, hxg⟩
            exact ⟨Or.inl hxg, Or.inl hxb.1⟩
          · exact ⟨Or.inr ⟨hxa, hxg⟩, Or.inr ⟨hxa, hxg⟩⟩
        · rintro ⟨hxg | ⟨hxa, -⟩, hxb | ⟨hxa, -⟩⟩
          · have hxa : x ∈ a ∩ g := by
              rw [hab]
              exact ⟨hxb, hxg⟩
            exact hxa.1
          all_goals exact hxa

/-- Characterization of membership of (capFamily G f)* ⋏ H -/
theorem memberOfCapFamDualMeetH
{α : Type*} (G H : Family α) (a f : Set α) :
a ∈ (capFamily G f)* ⋏ H ↔
  (∀ g ∈ G, g ⊆ f → a ∩ g ∈ H) :=
    by
    -- `a ∈ (G∩f)* ⋏ H` if and only if `a ∩ c ∈ H` for all `c ∈ (G∩f)** = G∩f`
    have hmem : a ∈ (capFamily G f)* ⋏ H ↔ ∀ c ∈ capFamily G f, a ∩ c ∈ H := by
      change (∀ c ∈ (capFamily G f)**, a ∩ c ∈ H) ↔ _
      rw [dualIsInvolutionOnFamilies]
    rw [hmem]
    constructor
    · -- if `g ∈ G` and `g ⊆ f`, then `f ∩ g = g ∈ G`, so `g ∈ G∩f`
      intro h g hg hgf
      exact h g (show f ∩ g ∈ G by rwa [Set.inter_eq_right.mpr hgf])
    · -- if `f ∩ c ∈ G`, then `a ∩ c ⊇ a ∩ (f ∩ c) ∈ H`
      intro h c hc
      exact H.upward_closed _ _ (h (f ∩ c) hc Set.inter_subset_left)
        (Set.inter_subset_inter_right a Set.inter_subset_right)

/-- Characterization of Family.iInter (fun (f : F.sets) ↦ (capFamily G f) ⋎ H) -/
theorem iInterCapFamilyDescription
{α : Type*} (F G H : Family α) :
Family.iInter (fun (f : F.sets) ↦ (capFamily G f) ⋎ H) =
{a : Set α | ∀ f ∈ F, ∃ g ∈ G, g ⊆ f ∧ (∃ b ∈ H, a ∩ g = b ∩ g)} := by
  ext a
  refine (Family.mem_iInter _ a).trans ?_
  constructor
  · intro h f hf
    exact (memberOfCapFamJoinH G H a f).mp (h ⟨f, hf⟩)
  · rintro h ⟨f, hf⟩
    exact (memberOfCapFamJoinH G H a f).mpr (h f hf)

/-- Characterization of Family.iUnion (fun (f : F.sets) ↦ (capFamily G f)* ⋏ H) -/
theorem iUnionCapFamilyDualDescription
{α : Type*} (F G H : Family α) :
Family.iUnion (fun (f : F.sets) ↦ (capFamily G f)* ⋏ H) =
{a : Set α | ∃ f ∈ F, ∀ g ∈ G, g ⊆ f → a ∩ g ∈ H} := by
  ext a
  refine (Family.mem_iUnion _ a).trans ?_
  constructor
  · rintro ⟨⟨f, hf⟩, h⟩
    exact ⟨f, hf, (memberOfCapFamDualMeetH G H a f).mp h⟩
  · rintro ⟨f, hf, h⟩
    exact ⟨⟨f, hf⟩, (memberOfCapFamDualMeetH G H a f).mpr h⟩

end Meet

section Filters_and_PR

/-- F = fullFam α if andn only if ∅ ∈ F -/
lemma fullFamEquiv
{α : Type*} (F : Family α) :
F = fullFam α ↔ ∅ ∈ F := by
  constructor
  · intro hF
    rw [hF]
    simp only [fullFam, fullCollection, Set.powerset_univ]
    trivial
  · intro hF
    ext A
    constructor
    · intro hA
      simp only [fullFam, fullCollection, Set.powerset_univ]
      trivial
    · intro hA
      apply F.upward_closed ∅
      · exact hF
      · simp

/-- F ⋏ F = F iff F is partition regular or F = fullFam -/
theorem familyIsIdempotentForMeetIffPR
{α : Type*} (F : Family α) :
  F ⋏ F = F ↔ (isPRFamily F ∨ F = fullFam α) := by
  constructor
  · intro hF
    by_cases hFull : F = fullFam α
    · right
      exact hFull
    · left
      simp only [isPRFamily, ne_eq]
      constructor
      · exact hFull
      · intro A B hAB
        by_contra hContra
        simp only [not_or] at hContra
        rcases hContra with ⟨hC1, hC2⟩
        have hAstar : Aᶜ ∈ F* := by
          simp only [mem_dual_alt, compl_compl]
          exact hC1
        have hBstar : Bᶜ ∈ F* := by
          simp only [mem_dual_alt, compl_compl]
          exact hC2
        rw [<- hF] at hAB
        specialize hAB Aᶜ hAstar
        have hBF : B ∈ F := by
          apply F.upward_closed ((A ∪ B) ∩ Aᶜ)
          · exact hAB
          · apply Set.union_inter_compl_left_subset
        exact hC2 hBF
  · intro hF
    rcases hF with hF1 | hF2
    · simp only [isPRFamily, ne_eq] at hF1
      rcases hF1 with ⟨hF1a, hF1b⟩
      ext A
      constructor
      · intro hA
        have hUniFstar : Set.univ ∈ F* := by
          intro B hB
          simp only [Set.univ_inter]
          by_contra hContra
          simp only [Set.nonempty_iff_empty_ne, ne_eq, Decidable.not_not] at hContra
          rw [<- hContra] at hB
          have hFFull : F = fullFam α := by
            simp only [fullFamEquiv]
            exact hB
          exact hF1a hFFull
        specialize hA Set.univ hUniFstar
        simp only [Set.inter_univ] at hA
        exact hA
      · intro hA B hB
        specialize hF1b (A ∩ B) (A \ B)
        simp only [Set.inter_union_sdiff] at hF1b
        specialize hF1b hA
        rcases hF1b with hFAB | hFABm
        · exact hFAB
        · specialize hB (A \ B) hFABm
          simp at hB
    · simp only [fullFam, fullCollection, Set.powerset_univ] at hF2
      ext A
      constructor
      · intro hA
        have hAUniv : A ∈ F.sets := by
          rw [hF2]
          simp
        exact hAUniv
      · intro hA B hB
        rw [hF2]
        simp

/-- F ⋎ F = F iff F is a filter or F is the empty family -/
theorem familyIsIdempotentForJoinIffFilter
{α : Type*} (F : Family α) :
  F ⋎ F = F ↔ (isFilterFamily F ∨ F = emptyFam α) := by
  constructor
  · intro hF
    by_cases hFEmp : F = emptyFam α
    · right
      exact hFEmp
    · left
      unfold isFilterFamily
      constructor
      · exact hFEmp
      · intro A B hA hB
        rw [<- hF]
        use A
        constructor
        · exact hA
        · use B
          constructor
          · exact hB
          · rfl
  · intro hF
    rcases hF with hF1 | hF2
    · ext A
      unfold isFilterFamily at hF1
      rcases hF1 with ⟨hF1a, hF1b⟩
      constructor
      · intro hA
        rcases hA with ⟨B, hB, C, hC, hBC⟩
        specialize hF1b hB hC
        rw [hBC]
        exact hF1b
      · intro hA
        have hFF := familyContainedInFamilyJoin F F hF1a
        apply hFF hA
    · ext A
      constructor
      · intro hA
        rcases hA with ⟨B, hB, C, hC, hBC⟩
        rw [hF2] at hB
        simp [emptyFam] at hB
      · intro hA
        rw [hF2] at hA
        simp only [emptyFam] at hA
        have hAEmp : A ∈ (∅ : Set (Set α)) := by
          exact hA
        simp at hAEmp

/-- F is a filter iff F* is partition regular -/
theorem familyIsPRIffDualIsFilter
{α : Type*} (F : Family α) :
isFilterFamily F ↔ isPRFamily (F*) := by
  constructor
  · intro hF
    unfold isPRFamily
    unfold isFilterFamily at hF
    rcases hF with ⟨hF1, hF2⟩
    constructor
    · by_contra hContra
      have hFEmp : F = emptyFam α := by
        rw [<- dualIsInvolutionOnFamilies F, hContra, fullFamDual]
      exact hF1 hFEmp
    · intro A B hAB
      by_contra hContra
      simp only [not_or] at hContra
      rcases hContra with ⟨hA, hB⟩
      have hAF : Aᶜ ∈ F := by
        by_contra hContra2
        apply mem_dual_alt.mpr at hContra2
        exact hA hContra2
      have hBF : Bᶜ ∈ F := by
        by_contra hContra2
        apply mem_dual_alt.mpr at hContra2
        exact hB hContra2
      specialize hF2 hAF hBF
      apply mem_dual_alt.mp at hAB
      simp only [Set.compl_union] at hAB
      exact hAB hF2
  · intro hF
    unfold isFilterFamily
    unfold isPRFamily at hF
    rcases hF with ⟨hF1, hF2⟩
    constructor
    · by_contra hContra
      have hFstar : F* = (emptyFam α)* := by
        rw [hContra]
      rw [emptyFamDual] at hFstar
      exact hF1 hFstar
    · intro A B hA hB
      by_contra hContra2
      have hABc : A ∩ B = (Aᶜ ∪ Bᶜ)ᶜ := by
        simp
      rw [hABc] at hContra2
      apply mem_dual_alt.mpr at hContra2
      specialize hF2 Aᶜ Bᶜ hContra2
      rcases hF2 with hF2a | hF2b
      · apply mem_dual_alt.mp at hF2a
        simp only [compl_compl] at hF2a
        exact hF2a hA
      · apply mem_dual_alt.mp at hF2b
        simp only [compl_compl] at hF2b
        exact hF2b hB

/-- F* is filter iff  F ⋏ F* = F* -/
theorem dualFFilterIffFMeetDualFIsDualF
{α : Type*} (F : Family α) :
isFilterFamily (F*) ↔ F ⋏ F* = F* := by
  constructor
  · intro hF
    rcases hF with ⟨hF1, hF2⟩
    ext A
    constructor
    · intro hA
      rw [familyMeetIsCommutative] at hA
      have hFNotFull : F ≠ fullFam α := by
        by_contra hContra
        have hFstar : F* = (fullFam α)* := by
          rw [hContra]
        rw [fullFamDual] at hFstar
        exact hF1 hFstar
      have h1 := familyMeetContainedInIntersection F* F hFNotFull
      apply h1 hA
    · intro hA B hB
      specialize hF2 hA hB
      exact hF2
  · intro hF
    constructor
    · by_contra hContra
      rw [hContra] at hF
      simp only [emptyFamilyMeetCondition] at hF
      rw [hContra] at hF
      have hEmpSub : emptyFam α ⊆ emptyFam α := by
        intro A hA
        exact hA
      exact hF hEmpSub
    · intro A B hA hB
      rw [<- hF] at hA
      specialize hA B hB
      exact hA

/-- F ⋎ F* = F iff F ⋏ F* = F* -/
theorem FJoinDualFIsFIffFMeetDualFIsDualF
{α : Type*} (F : Family α) :
F ⋎ F* = F ↔ F ⋏ F* = F* := by
  constructor
  · intro hF
    have hFdual : (F ⋎ F*)* = F* := by
      rw [hF]
    rw [familyDeMorgan1, dualIsInvolutionOnFamilies, familyMeetIsCommutative] at hFdual
    exact hFdual
  · intro hF
    have hFdual : (F ⋏ F*)* = F** := by
      rw [hF]
    rw [familyDeMorgan2, dualIsInvolutionOnFamilies, familyJoinIsCommutative] at hFdual
    exact hFdual

/-- If F ≠ emptyFam α and F ⋏ F* = F*, then F* ⊆ F -/
theorem ifFMeetDualFIsDualFAndNonemptyThenDualFInF
{α : Type*} (F : Family α) :
F ≠ emptyFam α → F ⋏ F* = F* → F* ⊆ F := by
  intro hF1 hF2
  rw [<- hF2]
  have hFstarNotFull : F* ≠ fullFam α := by
    by_contra hContra
    have hFstar : F** = (fullFam α)* := by
      rw [hContra]
    rw [dualIsInvolutionOnFamilies, fullFamDual] at hFstar
    exact hF1 hFstar
  apply familyMeetContainedInIntersection
  · exact hFstarNotFull

/-- F ⋏ F* is always a filter -/
theorem meetOfFamilyAndDualIsFilter
{α : Type*} (F : Family α) :
isFilterFamily (F ⋏ F*) :=
  by
  unfold isFilterFamily
  constructor
  · by_contra hContra
    rw [familyMeetIsCommutative] at hContra
    have hF3 : (F* ⋏ F)* = (emptyFam α)* := by
      rw [hContra]
    rw [familyDeMorgan2, emptyFamDual, dualIsInvolutionOnFamilies] at hF3
    simp only [fullFamEquiv] at hF3
    rcases hF3 with ⟨A, hA, B, hB, hAB⟩
    apply (mem_famDual F B).mp at hB
    specialize hB A hA
    rw [Set.inter_comm, <- hAB] at hB
    rcases hB with ⟨x, hx⟩
    exact hx
  · intro A B hAinFFstar hBinFFstar
    change ∀ C ∈ F*, A ∩ C ∈ F* at hAinFFstar
    change ∀ C ∈ F*, B ∩ C ∈ F* at hBinFFstar
    change ∀ C ∈ F*, (A ∩ B) ∩ C ∈ F* at ⊢
    intro C hC
    have hBC : B ∩ C ∈ F* := hBinFFstar C hC
    have hABC : A ∩ (B ∩ C) ∈ F* := hAinFFstar (B ∩ C) hBC
    simpa [Set.inter_assoc]

/-- F ⋎ F* is always partition regular -/
theorem joinOfFamilyAndDualIsPR
{α : Type*} (F : Family α) :
isPRFamily (F ⋎ F*) := by
  have h1 : (F ⋎ F*) = (F* ⋏ F)* := by
    rw [familyDeMorgan2, dualIsInvolutionOnFamilies]
  rw [h1]
  apply (familyIsPRIffDualIsFilter (F*⋏F)).mp
  constructor
  · by_contra hContra
    have hF3 : (F* ⋏ F)* = (emptyFam α)* := by
      rw [hContra]
    rw [<- h1, emptyFamDual] at hF3
    simp only [fullFamEquiv] at hF3
    rcases hF3 with ⟨A, hA, B, hB, hAB⟩
    apply (mem_famDual F B).mp at hB
    specialize hB A hA
    rw [Set.inter_comm, <- hAB] at hB
    rcases hB with ⟨x, hx⟩
    exact hx
  · intro A B hA hB C hC
    simp only [Set.inter_assoc]
    specialize hB C hC
    specialize hA (B ∩ C)
    have hBC : B ∩ C ∈ F** := by
      rw [dualIsInvolutionOnFamilies]
      exact hB
    have hBC2 : B ∩ C ∈ (F*).sets* := by
      exact hBC
    specialize hA hBC2
    exact hA

end Filters_and_PR

section Some_useful_identities

/-- F ⋎ G ⊆ H iff F ⊆ H ⋏ G* -/
theorem familyUsefulIdentity
{α : Type*} (F G H : Family α) :
F ⋎ G ⊆ H ↔ F ⊆ H ⋏ G* := by
  constructor
  · intro hF A hA B hB C hC
    rw [Set.inter_right_comm]
    have hAC : A ∩ C ∈ F ⋎ G := by
      use A
      constructor
      · exact hA
      · use C
    specialize hF hAC
    rw [Set.inter_comm]
    apply (mem_famDual H B).mp hB
    exact hF
  · intro hF A hA
    rcases hA with ⟨B, hB, C, hC, hBC⟩
    have hHH : H = (H*)* := by
      rw [dualIsInvolutionOnFamilies]
    rw [hHH]
    intro D hD
    rw [hBC, Set.inter_assoc]
    nth_rw 2 [Set.inter_comm]
    rw [<- Set.inter_assoc]
    specialize hF hB D hD
    apply (mem_famDual G (B ∩ D)).mp
    · exact hF
    · exact hC

/-- H* ⊆ F ⋏ (F* ⋎ G*) iff F ⋏ G ⊆ F ⋏ H -/
theorem familyLocalImplicationEquivalence
{α : Type*} (F G H : Family α) :
H* ⊆ F ⋏ (F* ⋎ G*) ↔ F ⋏ G ⊆ F ⋏ H := by
  have hDual1 : (F ⋏ G) = (F* ⋎ G*)* := by
    rw [familyDeMorgan1, dualIsInvolutionOnFamilies, dualIsInvolutionOnFamilies]
  have hDual2 : (F ⋏ H) = (F* ⋎ H*)* := by
    rw [familyDeMorgan1, dualIsInvolutionOnFamilies, dualIsInvolutionOnFamilies]
  rw [hDual1, hDual2]
  have hAntiTone : (F*⋎G*)* ⊆ (F*⋎H*)* ↔ (F*⋎H*) ⊆ (F*⋎G*) := by
    constructor
    · intro h
      rw [<- dualIsInvolutionOnFamilies (F* ⋎ H*)]
      rw [<- dualIsInvolutionOnFamilies (F* ⋎ G*)]
      apply dualIsAntitone
      exact h
    · intro h
      apply dualIsAntitone
      exact h
  simp only [hAntiTone]
  constructor
  · intro h1 A hA
    rcases hA with ⟨B, hB, C, hC, hBC⟩
    specialize h1 hC B hB
    rw [hBC]
    rw [Set.inter_comm]
    exact h1
  · intro h2 A hA B hB
    have hAB : B ∩ A ∈ F*⋎H* := by
      use B
      constructor
      · exact hB
      use A
      constructor
      · exact hA
      simp
    specialize h2 hAB
    rw [Set.inter_comm]
    exact h2

end Some_useful_identities

end
