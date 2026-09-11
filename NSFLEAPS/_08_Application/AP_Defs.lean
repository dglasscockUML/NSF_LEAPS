import NSFLEAPS._06_Furstenberg_families.FF_Defs
import NSFLEAPS._07_RP.RP_Defs
import NSFLEAPS._08_Application.AP_Symbolic_system

/-! This is a module docstring -/


section Theorems_needed_from_FA_Theorems
-- This section contains theorems from FA_Theorems which are not stated yet
-- I state them here to use for theorems in this file
-- After we state corresponding theorems in FA_Theorems, the statements in this
-- section will be removed

/-- For families F and G, we have F ⋏ G ⊆ F ∩ G -/
-- This theorem will be moved to FA_Theorems later
theorem familyMeetContainedInIntersection
{S : Type*} (F G : Family S) : F ⋏ G ⊆ F ∩ G := by
  sorry

/-- Familymeet is monotone -/
-- We will move this theorem to FA_Theorems file later
theorem familyMeetIsMonotonic
{S : Type*} (F G H : Family S) (hGH : G ⊆ H) : F ⋏ G ⊆ F ⋏ H := by
  sorry

/-- This lemma helps us unfold the definition of FamilyMeet -/
-- This may be redundant eventually.
-- But for now, I am struggling to unfold the definition of FamilyMeet, so I use this lemma
lemma unfoldFamMeet
{S : Type*} (F G : Family S) (A : Set S) : A ∈ F ⋏ G ↔ ∀ B ∈ F*, A ∩ B ∈ G := by
  sorry

/-- For families F, G, H, we have H* ⊆ F ⋏ (F* ⋎ G*) ↔ F ⋏ G ⊆ F ⋏ H -/
-- This theorem should be also in FA_Theorems. I state it here since it's needed for this section
-- and the corresponding theorem in FA_Theorems is not there yet
theorem familyLocalImplicationEquivalence
{S : Type*} (F G H : Family S) : H* ⊆ F ⋏ (F* ⋎ G*) ↔ F ⋏ G ⊆ F ⋏ H := by
  sorry

end Theorems_needed_from_FA_Theorems

section Reduction_to_UR_sets

/-- A set `A ⊆ S` is uniformly recurrent if `1_A` is `S`-uniformly recurrent
in the symbolic system `{0,1}^S` -/
def isURSet
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
isUniformlyRecurrent (selfSymbolicSystem S) (indicator A)

/-- An UR set can be written as R(x, U) -/
theorem urSetIsRxU
{S : Type*} [Semigroup S] [Nonempty S] {A : Set S} (hA : isURSet A) :
∃ (U : Set (WithOne S → Bool)) (UClopen : IsClopen U) (UNonempty : U.Nonempty),
∃ (x : WithOne S → Bool) (xMin : isUniformlyRecurrent (monoidExtSymbolicSystem S) x),
A = visitTimeSet (monoidExtSymbolicSystem S) x U := by
  simp only [exists_prop]
  let U := {x : WithOne S → Bool | x none = true}
  use U
  constructor
  · sorry
  constructor
  · sorry
  let liftSet : Set S → Set (WithOne S) := fun A : Set S ↦ {s : WithOne S | ∃ t ∈ A, some t = s}
  let A_wOne := liftSet A
  classical
  let x0 := fun (s : WithOne S) ↦ if s ∈ A_wOne then true else false
  let x1 := fun (s : WithOne S) ↦ if s ∈ A_wOne ∪ {none} then true else false
  have h1 : isUniformlyRecurrent (monoidExtSymbolicSystem S) x0 ∨ isUniformlyRecurrent
    (monoidExtSymbolicSystem S) x0 := by
    sorry
  rcases h1 with hx0 | hx1
  · use x0
    use hx0
    ext s
    constructor
    · intro hs
      unfold visitTimeSet
      simp
      sorry
    sorry
  sorry

/-- Given a syndetic set `A` and a thick set `H`, there exists a
UR set `B` and a thick set `G` such that `A ∩ G = B ∩ G` -/
theorem syndSetIsUROnThickSet
{S : Type*} [Semigroup S] [Nonempty S]
(A : Set S) {_ : isSyndetic A}
(H : Set S) {hH : isThick H} :
∃ (B : Set S) (_ : isURSet B) (H' : Set S) (_ : isThick H') (_ : H' ⊆ H),
A ∩ H' = B ∩ H' := by
  have hExistp := minIdempotentWitnessesShiftIntersectionLargeness H hH
  rcases hExistp with ⟨p, hp1, hp2, hp3, hp4⟩
  let a := indicator (A ∩ H)
  let b := (ultraAction (selfSymbolicSystem S)).map p a
  have hUnifb : isUniformlyRecurrent (selfSymbolicSystem S) b := by
    simp only [b]
    apply minUltraImageIsUniformlyRecurrent
    exact hp2
  let T := {g : S | b g = a g}
  let H' := H ∩ T
  have hH'thick : isThick H' := by
    unfold isThick
    intro F hF
    let U := {(α, β) : (S → Bool) × (S → Bool) | ∀ f ∈ F, α f = β f}
    have hUContDiag : Set.diagonal (S → Bool) ⊆ U := by
      intro t ht
      simp only [Set.mem_diagonal_iff] at ht
      simp only [Set.mem_ofPred_eq, U]
      intro f hf
      rw [ht]
    have hUOpen : IsOpen U := by
      let V : S → Set ((S → Bool) × (S → Bool)) :=
        fun f ↦ {x : (S → Bool) × (S → Bool) | x.1 f = x.2 f}
      have hEachf : ∀ f : S, IsOpen (V f) := by
        intro f
        let V1a := {x : (S → Bool) × (S → Bool) | x.1 f = true}
        let V1b := {x : (S → Bool) × (S → Bool) | x.2 f = true}
        let V2a := {x : (S → Bool) × (S → Bool) | x.1 f = false}
        let V2b := {x : (S → Bool) × (S → Bool) | x.2 f = false}
        have hVf : V f = V1a ∩ V1b ∪ V2a ∩ V2b := by
          simp only [V, V1a, V1b, V2a, V2b]
          apply Set.Subset.antisymm_iff.mpr
          constructor
          · intro x hx
            simp only [Set.mem_ofPred_eq] at hx
            simp
            by_cases hTrue : (x.1 f) = true
            · rw [hTrue] at hx
              simp [hTrue, hx]
            · simp only [Bool.not_eq_true] at hTrue
              rw [hTrue] at hx
              simp [hTrue, hx]
          · intro x hx
            simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq] at hx
            simp only [Set.mem_ofPred_eq]
            rcases hx with ⟨hx1a, hx1b⟩ | ⟨hx2a, hx2b⟩
            · rw [hx1a, hx1b]
            · rw [hx2a, hx2b]
        have hV1aOpen : IsOpen V1a := by
          have hV1aRedef : V1a = Prod.fst ⁻¹' {t : (S → Bool) | t f = true} := by
            simp
            rfl
          rw [hV1aRedef]
          apply IsOpen.preimage
          · continuity
          · let ψ : (S → Bool) → Bool := fun t ↦ t f
            have hEq : {t : (S → Bool) | t f = true} = ψ ⁻¹' {true} := by
              rfl
            rw [hEq]
            apply IsOpen.preimage
            · continuity
            · simp
        have hV1bOpen : IsOpen V1b := by
          have hV1bRedef : V1b = Prod.snd ⁻¹' {t : (S → Bool) | t f = true} := by
            simp
            rfl
          rw [hV1bRedef]
          apply IsOpen.preimage
          · apply continuous_snd
          · let ψ : (S → Bool) → Bool := fun t ↦ t f
            have hEq : {t : (S → Bool) | t f = true} = ψ ⁻¹' {true} := by
              rfl
            rw [hEq]
            apply IsOpen.preimage
            · continuity
            · simp
        have hV2aOpen : IsOpen V2a := by
          have hV2aRedef : V2a = Prod.fst ⁻¹' {t : (S → Bool) | t f = false} := by
            simp
            rfl
          rw [hV2aRedef]
          apply IsOpen.preimage
          · apply continuous_fst
          · let ψ : (S → Bool) → Bool := fun t ↦ t f
            have hEq : {t : (S → Bool) | t f = false} = ψ ⁻¹' {false} := by
              rfl
            rw [hEq]
            apply IsOpen.preimage
            · continuity
            · simp
        have hV2bOpen : IsOpen V2b := by
          have hV2aRedef : V2b = Prod.snd ⁻¹' {t : (S → Bool) | t f = false} := by
            simp
            rfl
          rw [hV2aRedef]
          apply IsOpen.preimage
          · apply continuous_snd
          · let ψ : (S → Bool) → Bool := fun t ↦ t f
            have hEq : {t : (S → Bool) | t f = false} = ψ ⁻¹' {false} := by
              rfl
            rw [hEq]
            apply IsOpen.preimage
            · continuity
            · simp
        rw [hVf]
        apply IsOpen.union
        · apply IsOpen.inter
          · exact hV1aOpen
          · exact hV1bOpen
        · apply IsOpen.inter
          · exact hV2aOpen
          · exact hV2bOpen
      have hURedef : U = ⋂ f ∈ F, V f := by
        simp only [U, V]
        apply Set.Subset.antisymm_iff.mpr
        constructor
        · intro t ht
          simp only [Set.mem_ofPred_eq] at ht
          simp only [Set.mem_iInter, Set.mem_ofPred_eq]
          exact ht
        · intro t ht
          simp only [Set.mem_iInter, Set.mem_ofPred_eq] at ht
          simp only [Set.mem_ofPred_eq]
          exact ht
      rw [hURedef]
      apply Set.Finite.isOpen_biInter hF
      intro f hf
      specialize hEachf f
      exact hEachf
    let dDiag := diagDynamicalSystem (selfSymbolicSystem S) (selfSymbolicSystem S)
    have hVisit : visitTimeSet dDiag (b, a) U ∈ p := by
      apply visitTimeSetBelongsToUltrafilter
      · exact hUOpen
      · simp only [Set.mem_ofPred_eq, U]
        intro f hf
        have hEq1 : ((ultraAction dDiag).map p (b, a)).1 f
          = (ultraAction (selfSymbolicSystem S)).map p b f := by
          simp only [ultraAction, ultraLim, diagDynamicalSystem, Prod.map_apply, dDiag]
          let φ := fun s ↦ ((selfSymbolicSystem S).map s b, (selfSymbolicSystem S).map s a)
          have hφ : Filter.Tendsto φ (p : Filter _) (nhds (Ultrafilter.extend φ p)) := by
            exact ultrafilter_extend_eq_iff.mp rfl
          have hφ1 : Ultrafilter.extend (fun s ↦ (selfSymbolicSystem S).map s b) p
            = (Ultrafilter.extend φ p).1 := by
            exact ultrafilter_extend_eq_iff.mpr hφ.fst_nhds
          exact congrArg (fun x ↦ x f) hφ1.symm
        have hEq2 : ((ultraAction dDiag).map p (b, a)).2 f
          = (ultraAction (selfSymbolicSystem S)).map p a f := by
          simp only [ultraAction, ultraLim, diagDynamicalSystem, Prod.map_apply, dDiag]
          let φ := fun s ↦ ((selfSymbolicSystem S).map s b, (selfSymbolicSystem S).map s a)
          have hφ : Filter.Tendsto φ (p : Filter _) (nhds (Ultrafilter.extend φ p)) := by
            exact ultrafilter_extend_eq_iff.mp rfl
          have hφ1 : Ultrafilter.extend (fun s ↦ (selfSymbolicSystem S).map s a) p
            = (Ultrafilter.extend φ p).2 := by
            exact ultrafilter_extend_eq_iff.mpr hφ.snd_nhds
          exact congrArg (fun x ↦ x f) hφ1.symm
        rw [hEq1, hEq2]
        simp only [b]
        rw [<- (ultraAction (selfSymbolicSystem S)).mapMult p p a]
        rw [hp3]
    specialize hp4 F hF
    have hJoin : (⋂ f ∈ F, leftMult f ⁻¹' H) ∩ (visitTimeSet dDiag (b, a) U) ∈ p := by
      apply Filter.inter_mem hp4 hVisit
    have hNonempty : ((⋂ f ∈ F, leftMult f ⁻¹' H) ∩ (visitTimeSet dDiag (b, a) U)).Nonempty := by
      apply Ultrafilter.nonempty_of_mem hJoin
    apply Set.nonempty_def.mp at hNonempty
    rcases hNonempty with ⟨g, hg1, hg2⟩
    use g
    intro t ht
    simp only [Set.mem_image] at ht
    rcases ht with ⟨f, hf1, hf2⟩
    rw [<- hf2]
    simp only [Set.mem_inter_iff, H']
    constructor
    · simp only [Set.mem_iInter, Set.mem_preimage] at hg1
      specialize hg1 f hf1
      exact hg1
    · simp only [Set.mem_ofPred_eq, T]
      simp only [visitTimeSet, Set.preimage_ofPred_eq, Set.mem_ofPred_eq, U] at hg2
      specialize hg2 f hf1
      simp only [diagDynamicalSystem, selfSymbolicSystem, basicRightAction,
        Prod.map_apply, dDiag] at hg2
      exact hg2
  let B := {s : S | b s = true}
  have hBUR : isURSet B := by
    unfold isURSet
    have hEq : indicator B = b := by
      simp only [B]
      unfold indicator
      simp
    rw [hEq]
    exact hUnifb
  have hH'H : H' ⊆ H := by
    simp [H']
  use B
  use hBUR
  use H'
  use hH'thick
  use hH'H
  apply Set.Subset.antisymm_iff.mpr
  constructor
  · intro s hs
    simp only [Set.mem_inter_iff, H'] at hs
    rcases hs with ⟨hs1, hs2, hs3⟩
    simp only [Set.mem_inter_iff, H']
    constructor
    · simp only [Set.mem_ofPred_eq, T] at hs3
      simp only [Set.mem_ofPred_eq, B]
      rw [hs3]
      simp only [a]
      simp only [indicator, Set.mem_inter_iff, decide_eq_true_eq]
      constructor
      · exact hs1
      · exact hs2
    constructor
    · exact hs2
    · exact hs3
  · intro s hs
    simp only [Set.mem_inter_iff, H'] at hs
    rcases hs with ⟨hs1, hs2, hs3⟩
    simp only [Set.mem_inter_iff, H']
    constructor
    · simp only [Set.mem_ofPred_eq, T] at hs3
      simp only [Set.mem_ofPred_eq, B] at hs1
      rw [hs3] at hs1
      simp only [a] at hs1
      simp only [indicator, Set.mem_inter_iff, decide_eq_true_eq] at hs1
      rcases hs1 with ⟨hs1a, hs1b⟩
      exact hs1a
    constructor
    · exact hs2
    · exact hs3

/-- If the containment `S ⋏ F ⊆ S ⋏ G` holds for UR sets, then it holds
for all sets. -/
theorem urContainmentSufficesForFamilyContainment
{S : Type*} [Semigroup S] [Nonempty S]
(F G : Family S)
{hFG : ∀ (B H : Set S), isURSet B → isThick H → B ∩ H ∈ F → B ∩ H ∈ G} :
(syndeticFamily S) ⋏ F ⊆ (syndeticFamily S) ⋏ G := by
    intro A hA
    have h0 : isSyndetic A := by
      have h01 : syndeticFamily S ⋏ F ⊆ syndeticFamily S ∩ F := by
        apply familyMeetContainedInIntersection
      have h02 : A ∈ syndeticFamily S ∩ F := by
        exact h01 hA
      have h03 : A ∈ syndeticFamily S := by
        exact h02.1
      simpa
    have h1 : ∀ H : Set S, isThick H → A ∩ H ∈ G := by
      intro H hH
      have h11 : ∃ (B : Set S) (hB : isURSet B) (H' : Set S) (hH' : isThick H') (hHH' : H' ⊆ H),
      A ∩ H' = B ∩ H' := by
        apply syndSetIsUROnThickSet
        · exact h0
        exact hH
      obtain ⟨B, hB, H', hH', hHH', h2⟩ := h11
      have h12 : ∀ B ∈ (syndeticFamily S)*, A ∩ B ∈ F := by
        exact (unfoldFamMeet (syndeticFamily S) F A).mp hA
      have h13 : A ∩ H' ∈ F := by
        specialize h12 H'
        rw [dualSyndeticThick] at h12
        apply h12
        exact hH'
      have h14 : B ∩ H' ∈ F := by
        rw [<- h2]
        exact h13
      have h15 : B ∩ H' ∈ G := by
        apply hFG
        · exact hB
        · exact hH'
        exact h14
      have h16 : A ∩ H' ∈ G := by
        rw [h2]
        exact h15
      have h17 : A ∩ H' ⊆ A ∩ H := by
        apply Set.inter_subset_inter_right
        exact hHH'
      apply Family.upward_closed
      · exact h16
      exact h17
    simp only [SetLike.mem_coe] at hA
    simp only [SetLike.mem_coe]
    have h2 : (syndeticFamily S)* = (thickFamily S) := by
      exact dualSyndeticThick
    have h3 : (∀ H ∈ thickFamily S, A ∩ H ∈ G) → A ∈ syndeticFamily S⋏G := by
      rw [<- dualSyndeticThick]
      exact (unfoldFamMeet (syndeticFamily S) G A).mpr
    apply h3
    intro H hH2
    specialize h1 H hH2
    exact h1

end Reduction_to_UR_sets

section Delta_builder

/-- If (x, y) is in regional proximal relation in a minimal system X and V ∋ y,
then for all thick set H, R(x, V) ∩ H is a Delta set -/
theorem commVisitTimeSetForRPPairIsDelta
{S : Type*} [CommSemigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} {hMin : isMinimalSystem dSystem}
(x : X) {y : X}
(V : Set X) {hV : V ∈ nhds y} :
∀ (H : Set S), isThick H → isDelta ((visitTimeSet dSystem x V) ∩ H) :=
  by sorry

end Delta_builder

section Dynamical_sets_of_bohr_recurrence

/-- If B is a set of Bohr recurrence and a uniformly recurrent set,
then for all thick set H, B ∩ H is a Δ set -/
theorem commURSetsOfBohrRecurrenceAreDelta
{S : Type*} [CommSemigroup S] [Nonempty S]
(B : Set S) {hBur : isURSet B} {hBrec : isSetOfBohrRecurrence B} :
∀ (H : Set S), isThick H → isDelta (B ∩ H) :=
  by sorry

end Dynamical_sets_of_bohr_recurrence

section Application

/-- In a commutative semigroup, S ⋏ Δ = S ⋏ dcT_Bohr -/
theorem commSyndFamMeetDeltaIsSnydFamMeetSetOfBohrRecurrence
{S : Type*} [CommSemigroup S] [Nonempty S] :
syndeticFamily S ⋏ deltaFamily S = syndeticFamily S ⋏ setOfBohrRecurrenceFamily S:= by
    have h1 : syndeticFamily S ⋏ deltaFamily S
      ⊆ syndeticFamily S ⋏ setOfBohrRecurrenceFamily S := by
      apply familyMeetIsMonotonic
      have h11 : deltaFamily S ⊆ deltaZeroFamily S := by
        exact deltaFamilyContainedInDeltaZeroFamily
      have h12 : deltaZeroFamily S ⊆ setOfBohrRecurrenceFamily S := by
        exact commDeltaZeroImpliesSetOfBohrRecurrence
      intro x hx
      exact h12 (h11 hx)
    have h3 : ∀ (B H : Set S), isURSet B → isThick H →
    B ∩ H ∈ setOfBohrRecurrenceFamily S → B ∩ H ∈ deltaFamily S := by
      intro B H hB hH hBH
      have h32 : isSetOfBohrRecurrence B := by
        have h33 : B ∩ H ⊆ B := by
          simp
        apply setOfBohrRecurrenceIsMonotone hBH h33
      apply commURSetsOfBohrRecurrenceAreDelta
      · exact hB
      · exact h32
      exact hH
    have h2 : syndeticFamily S ⋏ setOfBohrRecurrenceFamily S
      ⊆ syndeticFamily S ⋏ deltaFamily S := by
      apply urContainmentSufficesForFamilyContainment
      exact h3
    simpa using Set.Subset.antisymm h1 h2

/-- In a commutative semigroup, S ⋏ Δ = S ⋏ Δ_0 -/
theorem commSyndFamMeetDeltaIsSnydFamMeetDeltaZero
{S : Type*} [CommSemigroup S] [Nonempty S] :
syndeticFamily S ⋏ deltaFamily S = syndeticFamily S ⋏ deltaZeroFamily S := by
  have h1 : syndeticFamily S ⋏ deltaFamily S ⊆ syndeticFamily S ⋏ deltaZeroFamily S := by
    apply familyMeetIsMonotonic
    exact deltaFamilyContainedInDeltaZeroFamily
  have h2 : syndeticFamily S ⋏ deltaZeroFamily S ⊆
  syndeticFamily S ⋏ setOfBohrRecurrenceFamily S := by
    apply familyMeetIsMonotonic
    exact commDeltaZeroImpliesSetOfBohrRecurrence
  have h3 : syndeticFamily S ⋏ setOfBohrRecurrenceFamily S = syndeticFamily S ⋏ deltaFamily S := by
    rw [commSyndFamMeetDeltaIsSnydFamMeetSetOfBohrRecurrence]
  have h4 : syndeticFamily S ⋏ deltaZeroFamily S ⊆ syndeticFamily S ⋏ deltaFamily S := by
    rw [<- h3]
    exact h2
  simpa using Set.Subset.antisymm h1 h4

/-- In a commutative semigroup, Δ* ⊆ S ⋏ (T ⋎ dcS_Bohr) -/
theorem commDeltaStarImpliesLocallyBohrZero
{S : Type*} [CommSemigroup S] [Nonempty S] :
(deltaFamily S)* ⊆ syndeticFamily S ⋏ (thickFamily S ⋎ bohrZeroFamily S) := by
  rw [<- dualSyndeticThick]
  have h1 : syndeticFamily S ⋏ (bohrZeroFamily S)* ⊆ syndeticFamily S ⋏ deltaFamily S := by
    rw [commSyndFamMeetDeltaIsSnydFamMeetSetOfBohrRecurrence]
    rw [dualBohrZeroSetsOfBohrRecurrence]
    intro x hx
    exact hx
  have h2 : (bohrZeroFamily S)** = bohrZeroFamily S := by
    apply thm_dual_is_involution
  rw [<- h2]
  exact (familyLocalImplicationEquivalence (syndeticFamily S)
  (bohrZeroFamily S)* (deltaFamily S)).mpr h1

end Application
