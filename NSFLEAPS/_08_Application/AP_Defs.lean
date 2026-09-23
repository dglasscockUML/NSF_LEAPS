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
-- Here's an easier-to-apply version of the arguments:  (F) {G H} : G ⊆ H → F ⋏ G ⊆ F ⋏ H
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

theorem familyJoinCommutative
{S : Type*} (F G : Family S) : F ⋎ G = G ⋎ F := by sorry

theorem familyJoinMonotoneSlot1
{S : Type*} {F G : Family S} (H : Family S) : F ⊆ G → F ⋎ H ⊆ G ⋎ H := by sorry

theorem familyJoinMonotoneSlot2
{S : Type*} (F : Family S) {G H : Family S} : G ⊆ H → F ⋎ G ⊆ F ⋎ H := by sorry

theorem dualIsAntitone
{S : Type*} {F G : Family S} : F ⊆ G → G* ⊆ F* := by sorry

theorem deMorganOverJoin
{S : Type*} {F G : Family S} : (F ⋎ G)* = F* ⋏ G* := by sorry

theorem deMorganOverMeet
{S : Type*} {F G : Family S} : (F ⋏ G)* = F* ⋎ G* := by sorry

end Theorems_needed_from_FA_Theorems

section Reduction_to_UR_sets

/-- A set `A ⊆ S` is uniformly recurrent if `1_A` is `S`-uniformly recurrent
in the symbolic system `{0,1}^S` -/
def isURSet
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
isUniformlyRecurrent (selfSymbolicSystem S) (indicator A)

/-- An UR set can be written as R(x, U) -/
theorem urSetIsRxU.{u}
{S : Type u} [Semigroup S] [Nonempty S] {A : Set S} (hA : isURSet A) :
∃ (X : Type u) (_ : TopologicalSpace X) (_ : CompactSpace X) (_ : T2Space X) (_ : Nonempty X),
∃ (dSystem : DynamicalSystem S X) (_ : isMinimalSystem dSystem),
∃ x : X, ∃ U : Set X, IsClopen U ∧ A = visitTimeSet dSystem x U := by
  let π : (WithOne S → Bool) → (S → Bool) := fun w ↦ (fun s ↦ w s)
  have hπFacMap : isFactorMap (monoidExtSymbolicSystem S) (selfSymbolicSystem S) π := by
    unfold isFactorMap
    constructor
    · continuity
    constructor
    · intro y
      let z : WithOne S → Bool := Option.elim' true y
      use z
      simp [π]
      rfl
    · unfold isEquivariant
      intro s
      rfl
  unfold isURSet at hA
  let hLiftUnif := liftUniformRecurrentPoint hπFacMap (indicator A) hA
  rcases hLiftUnif with ⟨w, hw1, hw2⟩
  let X := orbitClosure (monoidExtSymbolicSystem S) w
  have hXDef : X = orbitClosure (monoidExtSymbolicSystem S) w := by
    rfl
  have hMinSubset := orbitClosureOfURPointIsMinimalSubset (monoidExtSymbolicSystem S) hw2
  rw [<- hXDef] at hMinSubset
  have hMinCopy := hMinSubset
  rcases hMinCopy with ⟨h1, h2⟩
  have hXInv := h1
  rcases h1 with ⟨h1a, h1b, h1c, h1d⟩
  have hXCompact : CompactSpace X := by
    apply isCompact_iff_compactSpace.mp h1b
  have hXNonempty : Nonempty X := by
    apply Set.Nonempty.to_subtype h1a
  use X, inferInstance, isCompact_iff_compactSpace.mp h1b, h1c, Set.Nonempty.to_subtype h1a
  have hMinSubsystem :=
    (minimalSubsetIffMinimalSubsystem (monoidExtSymbolicSystem S) hXInv).mp hMinSubset
  let dSystemX := fromNonemptyCompactT2InvariantSubsetToSystem (monoidExtSymbolicSystem S) hXInv
  have hdSystemXDef :
    dSystemX = fromNonemptyCompactT2InvariantSubsetToSystem (monoidExtSymbolicSystem S) hXInv := by
    rfl
  rw [<- hdSystemXDef] at hMinSubsystem
  have hwInX : w ∈ X := by
    simp only [X]
    apply URPointBelongsToOrbitClosure
    exact hw2
  let U := cylinderSet (WithOne S) true none
  use dSystemX, hMinSubsystem, ⟨w, hwInX⟩, Subtype.val ⁻¹' U
  have hEquiInt : ∀ s : S, ∀ z : (WithOne S → Bool), ((monoidExtSymbolicSystem S).map s z) none
    = true ↔ z s = true := by
    intro s z
    constructor
    · intro h
      simp only [monoidExtSymbolicSystem, symbolicSystem, rightActionOfSOnMonoidExt] at h
      exact h
    · intro h
      simp only [monoidExtSymbolicSystem, symbolicSystem, rightActionOfSOnMonoidExt]
      exact h
  constructor
  · apply IsClopen.preimage
    · simp only [cylinderSet, U]
      apply (isClopen_discrete ({true} : Set Bool)).preimage
      apply continuous_apply none
    · continuity
  apply Set.Subset.antisymm_iff.mpr
  constructor
  · intro s hs
    simp only [visitTimeSet, cylinderSet, Set.preimage_ofPred_eq, Set.mem_ofPred_eq, U]
    have hEqMap : (dSystemX.map s ⟨w, hwInX⟩) = ((monoidExtSymbolicSystem S).map s w) := by
      rfl
    rw [hEqMap]
    apply (hEquiInt s w).mpr
    simp only [π] at hw1
    apply congr_fun at hw1
    specialize hw1 s
    rw [hw1]
    simp only [indicator, decide_eq_true_eq]
    exact hs
  · intro s hs
    simp only [visitTimeSet, cylinderSet, Set.preimage_ofPred_eq, Set.mem_ofPred_eq, U] at hs
    have hEqMap : (dSystemX.map s ⟨w, hwInX⟩) = ((monoidExtSymbolicSystem S).map s w) := by
      rfl
    rw [hEqMap] at hs
    simp only [hEquiInt] at hs
    simp only [π] at hw1
    apply congr_fun at hw1
    specialize hw1 s
    rw [hs] at hw1
    simp only [indicator, true_eq_decide_iff] at hw1
    exact hw1

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

-- /-- If the containment `S ⋏ F ⊆ S ⋏ G` holds for UR sets, then it holds
-- for all sets. -/ -- this is the old version. The new version is below
-- theorem urContainmentSufficesForFamilyContainment
-- {S : Type*} [Semigroup S] [Nonempty S]
-- (F G : Family S)
-- {hFG : ∀ (B H : Set S), isURSet B → isThick H → B ∩ H ∈ F → B ∩ H ∈ G} :
-- (syndeticFamily S) ⋏ F ⊆ (syndeticFamily S) ⋏ G := by
--     intro A hA
--     have h0 : isSyndetic A := by
--       have h01 : syndeticFamily S ⋏ F ⊆ syndeticFamily S ∩ F := by
--         apply familyMeetContainedInIntersection
--       have h02 : A ∈ syndeticFamily S ∩ F := by
--         exact h01 hA
--       have h03 : A ∈ syndeticFamily S := by
--         exact h02.1
--       simpa
--     have h1 : ∀ H : Set S, isThick H → A ∩ H ∈ G := by
--       intro H hH
--       have h11 : ∃ (B : Set S) (hB : isURSet B) (H' : Set S) (hH' : isThick H') (hHH' : H' ⊆ H),
--       A ∩ H' = B ∩ H' := by
--         apply syndSetIsUROnThickSet
--         · exact h0
--         exact hH
--       obtain ⟨B, hB, H', hH', hHH', h2⟩ := h11
--       have h12 : ∀ B ∈ (syndeticFamily S)*, A ∩ B ∈ F := by
--         exact (unfoldFamMeet (syndeticFamily S) F A).mp hA
--       have h13 : A ∩ H' ∈ F := by
--         specialize h12 H'
--         rw [dualSyndeticThick] at h12
--         apply h12
--         exact hH'
--       have h14 : B ∩ H' ∈ F := by
--         rw [<- h2]
--         exact h13
--       have h15 : B ∩ H' ∈ G := by
--         apply hFG
--         · exact hB
--         · exact hH'
--         exact h14
--       have h16 : A ∩ H' ∈ G := by
--         rw [h2]
--         exact h15
--       have h17 : A ∩ H' ⊆ A ∩ H := by
--         apply Set.inter_subset_inter_right
--         exact hHH'
--       apply Family.upward_closed
--       · exact h16
--       exact h17
--     simp only [SetLike.mem_coe] at hA
--     simp only [SetLike.mem_coe]
--     have h2 : (syndeticFamily S)* = (thickFamily S) := by
--       exact dualSyndeticThick
--     have h3 : (∀ H ∈ thickFamily S, A ∩ H ∈ G) → A ∈ syndeticFamily S⋏G := by
--       rw [<- dualSyndeticThick]
--       exact (unfoldFamMeet (syndeticFamily S) G A).mpr
--     apply h3
--     intro H hH2
--     specialize h1 H hH2
--     exact h1

theorem urContainmentSufficesForFamilyContainment
{S : Type*} [Semigroup S] [Nonempty S]
(F G : Family S)
{hFG : ∀ (B H : Set S) (_ : isURSet B) (_ : isThick H),
  (∀ (H' : Set S) (_ : H' ⊆ H) (_ : isThick H'), (B ∩ H' ∈ F))
    → (∀ (H' : Set S) (_ : H' ⊆ H) (_ : isThick H'), (B ∩ H' ∈ G))} :
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
    intro H hHThick
    have h11 : ∃ (B : Set S) (hB : isURSet B) (H' : Set S) (hH' : isThick H') (hHH' : H' ⊆ H),
    A ∩ H' = B ∩ H' := by
      apply syndSetIsUROnThickSet
      · exact h0
      · exact hHThick
    obtain ⟨B, hB, H', hH', hHH', h2⟩ := h11
    have h12 : ∀ H'' ⊆ H', isThick H'' → B ∩ H'' ∈ F := by
      intro H'' hH'' hH''Thick
      have hABH'' : B ∩ H'' = A ∩ H'' := by
        have hAB0 : H' ∩ H'' = H'' := by
          exact Set.inter_eq_self_of_subset_right hH''
        have hAB1 : B ∩ H'' = B ∩ H' ∩ H'' := by
          nth_rw 1 [<- hAB0]
          rw [Set.inter_assoc]
        have hAB2 : A ∩ H'' = A ∩ H' ∩ H'' := by
          nth_rw 1 [<- hAB0]
          rw [Set.inter_assoc]
        rw [hAB1, hAB2, h2]
      rw [hABH'']
      apply (unfoldFamMeet (syndeticFamily S) F A).mp hA
      rw [dualSyndeticThick]
      exact hH''Thick
    have hH'Triv : H' ⊆ H' := by
      simp
    specialize hFG B H' hB hH' h12 H' hH'Triv hH'
    rw [<- h2] at hFG
    have hSub : A ∩ H' ⊆ A ∩ H := by
      intro a ha
      simp only [Set.mem_inter_iff] at ha
      rcases ha with ⟨ha1, ha2⟩
      simp only [Set.mem_inter_iff]
      constructor
      · exact ha1
      · apply hHH' ha2
    apply G.upward_closed (A ∩ H') (A ∩ H) hFG hSub
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

-- Next three definitions and the three lemmas below were written by ChatGPT.
-- The definitions help with product on commutative semigroups and the lemmas
-- provide simple equalities regarding these definitions
-- These supporting lemmas are needed for commVisitTimeSetForRPPairIsDelta below

-- Product of f over a nonempty finset.
noncomputable def prodNonempty
{S : Type*} [CommSemigroup S] [Nonempty S]
{ι : Type*} (t : Finset ι) (ht : t.Nonempty) (f : ι → S) : S := by
  classical
  let a : ι := Classical.choose ht
  exact (t.erase a).fold (· * ·) (f a) f

-- Product over all indices in Fin N.
noncomputable def prodAll
{S : Type*} [CommSemigroup S] [Nonempty S]
{N : ℕ} (hN : N ≥ 2) (s : Fin N → S) : S :=
  prodNonempty (Finset.univ : Finset (Fin N)) (by
    apply Finset.card_pos.mp
    simp only [Finset.card_univ, Fintype.card_fin]
    omega) s

-- Product over all indices in Fin N except i.
noncomputable def prodExcept
{S : Type*} [CommSemigroup S] [Nonempty S]
{N : ℕ} (hN : N ≥ 2) (s : Fin N → S) (i : Fin N) : S :=
prodNonempty ((Finset.univ : Finset (Fin N)).erase i) (by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega) s

lemma mul_prodNonempty_erase
    {I S : Type*} [DecidableEq I] [CommSemigroup S] [Nonempty S]
    (t : Finset I) (ht : t.Nonempty) (f : I → S)
    (i : I) (hi : i ∈ t) (he : (t.erase i).Nonempty) :
    (f i) * prodNonempty (t.erase i) he f =
      prodNonempty t ht f := by
  classical
  let : Std.Commutative (fun x y : S ↦ x * y) :=
    ⟨fun x y ↦ mul_comm x y⟩
  let : Std.Associative (fun x y : S ↦ x * y) :=
    ⟨fun x y z ↦ mul_assoc x y z⟩
  -- Swap an outside factor with the starting value of a fold.
  have hswap (u : Finset I) (x y : S) :
      x * u.fold (· * ·) y f =
        y * u.fold (· * ·) x f := by
    induction u using Finset.induction_on with
    | empty =>
        simpa only [Finset.fold_empty] using mul_comm x y
    | @insert k u hk ih =>
        simp only [Finset.fold_insert hk]
        rw [
          mul_left_comm x (f k),
          ih,
          mul_left_comm (f k) y
        ]
  -- Separate one indexed factor from a fold.
  have hsplit (u : Finset I) (a : I)
      (ha : a ∈ u) (b : S) :
      u.fold (· * ·) b f =
        (f a) * (u.erase a).fold (· * ·) b f := by
    simpa only [Finset.insert_erase ha] using
      (Finset.fold_insert
        (op := (· * ·)) (b := b) (f := f)
        (by simp : a ∉ u.erase a))
  -- Any member can be used as the starting factor.
  have hanchor (u : Finset I) (hu : u.Nonempty)
      (a : I) (ha : a ∈ u) :
      prodNonempty u hu f =
        (u.erase a).fold (· * ·) (f a) f := by
    let c : I := Classical.choose hu
    have hc : c ∈ u := Classical.choose_spec hu
    have hdef :
        prodNonempty u hu f =
          (u.erase c).fold (fun x y : S => x * y) (f c) f := by
      unfold prodNonempty
      apply congrArg
        (fun t : Finset I =>
          t.fold (fun x y : S => x * y) (f c) f)
      ext k
      simp only [Finset.mem_erase, c]
    rw [hdef]
    by_cases hca : c = a
    · rw [hca]
    · rw [
        hsplit (u.erase c) a
          (Finset.mem_erase.mpr ⟨Ne.symm hca, ha⟩) (f c),
        hsplit (u.erase a) c
          (Finset.mem_erase.mpr ⟨hca, hc⟩) (f a),
        Finset.erase_right_comm
      ]
      exact hswap _ _ _
  -- Choose a common starting index from the remaining indices.
  let a : I := Classical.choose he
  have ha : a ∈ t.erase i := Classical.choose_spec he
  have hi' : i ∈ t.erase a :=
    Finset.mem_erase.mpr
      ⟨Ne.symm (Finset.mem_erase.mp ha).1, hi⟩
  -- Rewrite both products with starting factor f a,
  -- then separate the factor f i.
  rw [
    hanchor (t.erase i) he a ha,
    hanchor t ht a (Finset.mem_of_mem_erase ha),
    hsplit (t.erase a) i hi' (f a),
    Finset.erase_right_comm
  ]

lemma prodExcept_last_eq_prodAll
    {S : Type*} [CommSemigroup S] [Nonempty S]
    {N : ℕ}
    (hN : 2 ≤ N)
    (hNSucc : 2 ≤ N.succ)
    (s : Fin N.succ → S) :
    prodExcept hNSucc s (Fin.last N) =
      prodAll hN (fun k : Fin N ↦ s k.castSucc) := by
  classical
  -- A product over a singleton is its only factor.
  have hsingleton {I : Type}
      (a : I) (f : I → S)
      (h : ({a} : Finset I).Nonempty) :
      prodNonempty {a} h f = f a := by
    have hc : Classical.choose h = a :=
      Finset.mem_singleton.mp (Classical.choose_spec h)
    simp only [
      prodNonempty, hc,
      Finset.erase_singleton, Finset.fold_empty
    ]
  -- This is the step that uses mul_prodNonempty_erase.
  have hinsert {I : Type}
      (t : Finset I) (ht : t.Nonempty)
      (a : I) (ha : a ∉ t) (f : I → S)
      (h : (insert a t).Nonempty) :
      prodNonempty (insert a t) h f =
        (f a) * prodNonempty t ht f := by
    have he : ((insert a t).erase a).Nonempty := by
      simpa [ha] using ht
    simpa [ha] using
      (mul_prodNonempty_erase
        (insert a t) h f a
        (Finset.mem_insert_self a t) he).symm
  -- Reindex a nonempty product along an embedding.
  --
  -- We allow an explicit equality t.map e = u, so that
  -- the nonemptiness proofs are handled inside this helper.
  have hreindex {I J : Type}
      (e : I ↪ J)
      (t : Finset I) (u : Finset J)
      (he : t.map e = u)
      (ht : t.Nonempty) (hu : u.Nonempty)
      (f : J → S) :
      prodNonempty u hu f =
        prodNonempty t ht (fun k ↦ f (e k)) := by
    subst u
    revert ht hu
    induction t using Finset.induction_on with
    | empty =>
        intro ht
        simp at ht
    | @insert a t ha ih =>
        intro ht hu
        obtain rfl | ht' := t.eq_empty_or_nonempty
        · -- Singleton case.
          simp only [
            Finset.insert_empty,
            Finset.map_singleton,
            hsingleton
          ]
        · -- Insert into a nonempty finset.
          have hmt : (t.map e).Nonempty :=
            Finset.map_nonempty.mpr ht'
          have hea : e a ∉ t.map e := by
            simpa using ha
          -- Split off f (e a) on both sides, then use ih.
          simpa only [
            Finset.map_insert,
            hinsert t ht' a ha (fun k ↦ f (e k)),
            hinsert (t.map e) hmt (e a) hea f
          ] using
            congrArg
              (fun z : S ↦ (f (e a)) * z)
              (ih ht' hmt)
  -- castSucc maps the old univ onto the new univ
  -- with the last index erased.
  have hindex :
      (Finset.univ : Finset (Fin N)).map Fin.castSuccEmb =
        (Finset.univ : Finset (Fin N.succ)).erase
          (Fin.last N) := by
    rw [Finset.map_eq_image]
    change
      (Finset.univ : Finset (Fin N)).image
          (fun k : Fin N ↦ k.castSucc) =
        (Finset.univ : Finset (Fin N.succ)).erase
          (Fin.last N)
    rw [Fin.image_castSucc N]
    ext k
    simp
  have hU : (Finset.univ : Finset (Fin N)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hE :
      ((Finset.univ : Finset (Fin N.succ)).erase
        (Fin.last N)).Nonempty := by
    rw [← hindex]
    exact Finset.map_nonempty.mpr hU
  unfold prodExcept prodAll
  exact hreindex Fin.castSuccEmb
    Finset.univ _ hindex hU hE s

lemma prodExcept_castSucc_eq
    {S : Type*} [CommSemigroup S] [Nonempty S]
    {N : ℕ}
    (hN : 2 ≤ N) (hNSucc : 2 ≤ N.succ)
    (s : ℕ → S) (i : Fin N) :
    prodExcept hNSucc
        (fun k : Fin N.succ => s k.val) i.castSucc =
      (prodExcept hN
        (fun k : Fin N => s k.val) i) * s N := by
  classical
  -- A nonempty product over a singleton is its only factor.
  have hsingleton {I : Type}
      (a : I) (f : I → S)
      (h : ({a} : Finset I).Nonempty) :
      prodNonempty {a} h f = f a := by
    have hc : Classical.choose h = a :=
      Finset.mem_singleton.mp (Classical.choose_spec h)
    simp only [
      prodNonempty, hc,
      Finset.erase_singleton, Finset.fold_empty
    ]
  -- Derive an insertion rule from your existing lemma.
  have hinsert {I : Type}
      (t : Finset I) (ht : t.Nonempty)
      (a : I) (ha : a ∉ t) (f : I → S)
      (h : (insert a t).Nonempty) :
      prodNonempty (insert a t) h f =
        (f a) * prodNonempty t ht f := by
    have he : ((insert a t).erase a).Nonempty := by
      simpa [ha] using ht
    simpa [ha] using
      (mul_prodNonempty_erase
        (insert a t) h f a
        (Finset.mem_insert_self a t) he).symm
  -- Reindexing along an embedding preserves prodNonempty.
  -- All supporting work is local to this proof.
  have hreindex {I J : Type}
      (e : I ↪ J)
      (t : Finset I) (u : Finset J)
      (htu : t.map e = u)
      (ht : t.Nonempty) (hu : u.Nonempty)
      (f : J → S) :
      prodNonempty u hu f =
        prodNonempty t ht (fun k => f (e k)) := by
    subst u
    revert ht hu
    induction t using Finset.induction_on with
    | empty =>
        intro ht
        simp at ht
    | @insert a t ha ih =>
        intro ht hu
        obtain rfl | ht' := t.eq_empty_or_nonempty
        · -- Singleton case.
          simp only [
            Finset.insert_empty,
            Finset.map_singleton,
            hsingleton
          ]
        · -- Split off corresponding factors and use induction.
          have hmt : (t.map e).Nonempty :=
            Finset.map_nonempty.mpr ht'
          have hea : e a ∉ t.map e := by
            simpa using ha
          simpa only [
            Finset.map_insert,
            hinsert t ht' a ha (fun k => f (e k)),
            hinsert (t.map e) hmt (e a) hea f
          ] using
            congrArg
              (fun z : S => (f (e a)) * z)
              (ih ht' hmt)
  -- The old and enlarged index sets, each omitting i.
  let t : Finset (Fin N) :=
    Finset.univ.erase i
  let u : Finset (Fin N.succ) :=
    Finset.univ.erase i.castSucc
  have ht : t.Nonempty := by
    dsimp [t]
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  -- The new index belongs to u.
  have hlast : Fin.last N ∈ u := by
    exact Finset.mem_erase.mpr
      ⟨ne_of_gt (Fin.castSucc_lt_last i), Finset.mem_univ _⟩
  have hu : u.Nonempty :=
    ⟨Fin.last N, hlast⟩
  -- After removing the new index, u is exactly the image of t.
  have hindex :
      t.map Fin.castSuccEmb = u.erase (Fin.last N) := by
    dsimp [t, u]
    rw [
      Finset.map_erase,
      Finset.erase_right_comm,
      Fin.univ_castSuccEmb N,
      Finset.erase_cons
    ]
    rfl
  have he : (u.erase (Fin.last N)).Nonempty := by
    rw [← hindex]
    exact Finset.map_nonempty.mpr ht
  -- Identify the product over the remaining indices.
  have hrest :
      prodNonempty (u.erase (Fin.last N)) he
          (fun k : Fin N.succ => s k.val) =
        prodNonempty t ht
          (fun k : Fin N => s k.val) := by
    exact hreindex Fin.castSuccEmb
      t (u.erase (Fin.last N)) hindex ht he
      (fun k : Fin N.succ => s k.val)
  -- Unfold prodExcept, split off s N, and use hrest.
  change
    prodNonempty u hu (fun k : Fin N.succ => s k.val) =
      (prodNonempty t ht (fun k : Fin N => s k.val)) * s N
  rw [
    ← mul_prodNonempty_erase
      u hu (fun k : Fin N.succ => s k.val)
      (Fin.last N) hlast he,
    hrest
  ]
  exact mul_comm _ _

/-- If (x, y) is in regional proximal relation in a minimal system X and V ∋ y,
then for all thick set H, R(x, V) ∩ H is a Delta set -/
theorem commVisitTimeSetForRPPairIsDelta
{S : Type*} [CommSemigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (hMin : isMinimalSystem dSystem)
(x y : X) (hxyRP : (x, y) ∈ RP dSystem)
{V : Set X} (hV : V ∈ nhds y) :
∀ (H : Set S), isThick H → isDelta ((visitTimeSet dSystem x V) ∩ H) := by
  simp only [mem_nhds_iff] at hV
  rcases hV with ⟨V0, hV0a, hV0b, hV0c⟩
  intro H hHThick
  unfold isDelta
  -- instead of V, we work with an open set V0 ⊆ V such that y ∈ V0
  let C := (visitTimeSet dSystem x V0) ∩ H
  have hSNonempty : (Set.univ : Set S).Nonempty := by
    simp
  rcases (Set.nonempty_def.mp hSNonempty) with ⟨s0, hs0⟩
  -- build s1 by hand
  -- this is to avoid issue of empty product that appears for N = 1 in the general case below
  have hs1Exist : ∃ s1 : S, (s1 ∈ (fun x ↦ s0 * x) '' C) ∧
    ((dSystem.map s1) ⁻¹' V0 ∩ (dSystem.map s0) ⁻¹' V0).Nonempty := by
    let U := V0
    let G := H
    have hInterSynd := (xyInRPImpliesSyndeticVisitTimeIntersection hMin x y).1 hxyRP U V0
    have hUOpen : IsOpen U := by
      simp only [U]
      exact hV0b
    have hUNonempty : U.Nonempty := by
      simp only [U]
      exact ⟨y, hV0c⟩
    specialize hInterSynd hUOpen hV0b hUNonempty hV0c
    have hInterN : (visitTimeSet dSystem x U ∩ setVisitTimeSet dSystem V0 U ∩ G).Nonempty := by
      apply syndeticThickIntersect
      · exact hInterSynd
      · simp only [G]
        exact hHThick
    rcases (Set.inter_nonempty_iff_exists_right.mp hInterN) with ⟨t, ht1, ht2, ht3⟩
    let s1 := s0 * t
    use s1
    constructor
    · simp only [Set.mem_image, Set.mem_inter_iff, C]
      use t
    · have hExz : ∃ z ∈ V0, (dSystem.map t) z ∈ V0 := by
        simp only [setVisitTimeSet, Set.inter_nonempty_iff_exists_right, Set.mem_image,
          ↓existsAndEq, and_true, Set.mem_ofPred_eq] at ht3
        rcases ht3 with ⟨z, hz1, hz2⟩
        use z
      rcases hExz with ⟨z, hz1, hz2⟩
      have hSurj := minimalCommActionIsSurjective hMin
      unfold isSurjectiveSystem at hSurj
      specialize hSurj s0
      simp only [Function.Surjective] at hSurj
      specialize hSurj z
      rcases hSurj with ⟨a, ha⟩
      use a
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · simp only [s1]
        rw [CommSemigroup.mul_comm s0 t]
        rw [dSystem.mapMult t s0]
        rw [ha]
        exact hz2
      · rw [ha]
        exact hz1
  rcases hs1Exist with ⟨s1, hs1a, hs1b⟩
  -- build sN from the previous sn given N ≥ 2
  have hClaim : ∀ (N : ℕ) (hN : N ≥ 2), ∀ s : Fin N → S,
    ((∀ i j : Fin N, (i < j) →  s j ∈ (fun x ↦ (s i) * x) '' C) ∧
    (⋂ i : Fin N, (dSystem.map (prodExcept hN s i)) ⁻¹' V0).Nonempty)
    →
    (∃ r : S, (∀ i : Fin N, r ∈ (fun x ↦ (s i) * x) '' C) ∧
    (((⋂ i : Fin N, (dSystem.map ((prodExcept hN s i) * r)) ⁻¹' V0))
    ∩ (dSystem.map (prodAll hN s)) ⁻¹' V0).Nonempty) := by
    intro N hN s hs
    rcases hs with ⟨hs1, hs2⟩
    let U := (⋂ i : Fin N, (dSystem.map (prodExcept hN s i)) ⁻¹' V0)
    let G := ⋂ i : Fin N, ((prodExcept hN s i) * ·) ⁻¹' H
    have hUNonempty : U.Nonempty := by
      simp only [U]
      exact hs2
    have hUOpen : IsOpen U := by
      sorry
    have hGThick : isThick G := by
      simp [G, isThick]
      intro F hF
      sorry
    have hInterSynd := (xyInRPImpliesSyndeticVisitTimeIntersection hMin x y).1
      hxyRP U V0 hUOpen hV0b hUNonempty hV0c
    have hInterN : (visitTimeSet dSystem x U ∩ setVisitTimeSet dSystem V0 U ∩ G).Nonempty := by
      apply syndeticThickIntersect
      · exact hInterSynd
      · exact hGThick
    rcases (Set.inter_nonempty_iff_exists_right.mp hInterN) with ⟨t, ht1, ht2, ht3⟩
    simp only [visitTimeSet, Set.mem_preimage] at ht2 ht3
    simp only [setVisitTimeSet, Set.image_inter_nonempty_iff, Set.mem_ofPred_eq] at ht3
    let r := (prodAll hN s) * t
    use r
    constructor
    · intro i
      simp only [Set.mem_iInter, Set.mem_preimage, U] at ht2
      specialize ht2 i
      simp only [← dSystem.mapMult] at ht2
      simp only [Set.mem_image, Set.mem_inter_iff, C, r]
      use (prodExcept hN s i) * t
      constructor
      · constructor
        · simp only [visitTimeSet, Set.mem_preimage]
          exact ht2
        · simp only [Set.mem_iInter, Set.mem_preimage, G] at ht1
          specialize ht1 i
          exact ht1
      · simp only [← Semigroup.mul_assoc]
        have hEq : (s i) * prodExcept hN s i = prodAll hN s := by
          simp only [prodExcept, prodAll]
          have hUnivNon : (Finset.univ : Finset (Fin N)).Nonempty := by
            sorry
          apply mul_prodNonempty_erase
          simp
        rw [hEq]
    · have hExz : ∃ z ∈ V0, (dSystem.map t) z ∈ U := by
        simp only [Set.inter_nonempty_iff_exists_right] at ht3
        rcases ht3 with ⟨z, hz1, hz2⟩
        use z
        constructor
        · exact hz2
        · simp only [Set.mem_preimage] at hz1
          exact hz1
      rcases hExz with ⟨z, hz1, hz2⟩
      have hSurj := minimalCommActionIsSurjective hMin
      unfold isSurjectiveSystem at hSurj
      specialize hSurj (prodAll hN s)
      simp only [Function.Surjective] at hSurj
      specialize hSurj z
      rcases hSurj with ⟨a, ha⟩
      use a
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
      constructor
      · intro i
        simp only [Set.mem_iInter, Set.mem_preimage, U] at hz2
        specialize hz2 i
        simp only [← dSystem.mapMult] at hz2
        simp only [r]
        rw [<- ha] at hz2
        simp only [← dSystem.mapMult] at hz2
        simp only [CommSemigroup.mul_comm]
        simp only [← Semigroup.mul_assoc]
        exact hz2
      · rw [ha]
        exact hz1
  choose! pick hpick using hClaim
  let step : (N : ℕ) → ((k : ℕ) → k < N → S) → S := fun N prev ↦
    if N = 0 then s0
    else if N = 1 then s1
    else pick N (fun i : Fin N ↦ prev i.val i.isLt)
  -- define the sequence s
  let s : ℕ → S := Nat.strongRec step
  -- prove properties of the sequence s
  have hs_rec (N : ℕ) :
    s N =
      if N = 0 then s0
      else if N = 1 then s1
      else pick N (fun i : Fin N => s i.val) := by
    exact Nat.strongRec_eq step N
  have hs0 : s 0 = s0 := by
    simpa using hs_rec 0
  have hs1 : s 1 = s1 := by
    simpa using hs_rec 1
  have hs_step (N : ℕ) (hN : 2 ≤ N) : s N = pick N (fun i : Fin N => s i.val) := by
    have h0 : N ≠ 0 := by omega
    have h1 : N ≠ 1 := by omega
    simpa [h0, h1] using hs_rec N
  -- base cases
  have h01 : s 1 ∈ (fun x ↦ (s 0) * x) '' C := by
    rw [hs0, hs1]
    exact hs1a
  have hstart : ((dSystem.map (s 0) ⁻¹' V0) ∩ (dSystem.map (s 1) ⁻¹' V0)).Nonempty := by
    rw [hs0, hs1]
    simp only [Set.inter_nonempty_iff_exists_right, Set.mem_preimage]
    simp only [Set.inter_nonempty_iff_exists_right, Set.mem_preimage] at hs1b
    rcases hs1b with ⟨x, hx1, hx2⟩
    use x
  -- The two product identities needed for the base case.
  have hprodTwoZero : prodExcept (by decide : 2 ≤ 2) (fun k : Fin 2 ↦ s k.val) 0 = s 1 := by
    simp [prodExcept, prodNonempty]
    have hset : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by
      decide
    have hchoose (h : ((Finset.univ : Finset (Fin 2)).erase 0).Nonempty) :
      Classical.choose h = (1 : Fin 2) := by
      simpa only [hset, Finset.mem_singleton] using (Classical.choose_spec h)
    simp [hchoose]
    simp [hset]
  have hprodTwoOne : prodExcept (by decide : 2 ≤ 2) (fun k : Fin 2 ↦ s k.val) 1 = s 0 := by
    simp [prodExcept, prodNonempty]
    have hset : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by
      decide
    have hchoose (h : ((Finset.univ : Finset (Fin 2)).erase 1).Nonempty) :
      Classical.choose h = (0 : Fin 2) := by
      simpa only [hset, Finset.mem_singleton] using (Classical.choose_spec h)
    simp [hchoose]
    simp [hset]
  -- Prove BOTH prefix properties simultaneously.
  have hprefix_all : ∀ (N : ℕ) (hN : 2 ≤ N), (∀ a b : Fin N, a < b → s b.val
    ∈ (fun y ↦ (s a.val) * y) '' C) ∧
    (⋂ a : Fin N, dSystem.map (prodExcept hN (fun k : Fin N ↦ s k.val) a) ⁻¹' V0).Nonempty := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
        constructor
        · -- For a < b in Fin 2, necessarily a = 0 and b = 1.
          intro a b hab
          have hab' : a.val < b.val := hab
          have hb_lt : b.val < 2 := b.isLt
          have ha0 : a.val = 0 := by omega
          have hb1 : b.val = 1 := by omega
          simpa only [ha0, hb1] using h01
        · -- Use the common witness for the initial pair.
          rcases hstart with ⟨z, hz0, hz1⟩
          refine ⟨z, Set.mem_iInter.mpr ?_⟩
          intro a
          fin_cases a
          · simpa [hprodTwoZero] using hz1
          · simpa [hprodTwoOne] using hz0
    | succ N hN ih =>
        -- The induction hypothesis contains the full
        -- antecedent needed to apply hpick.
        rcases hpick N hN
            (fun k : Fin N ↦ s k.val) ih with
          ⟨hnew, z, hzold, hzall⟩
        -- The selected new term is s N.
        rw [← hs_step N hN] at hnew hzold
        constructor
        · -- Pairwise membership for the enlarged prefix.
          intro a b hab
          have hab' : a.val < b.val := hab
          by_cases hb : b.val < N
          · -- Both indices belong to the old prefix.
            exact ih.1
              ⟨a.val, lt_trans hab' hb⟩
              ⟨b.val, hb⟩
              hab'
          · -- The larger index is the new index N.
            have hbN : b.val = N := by
              have hb_lt := b.isLt
              omega
            have haN : a.val < N := by omega
            simpa only [hbN] using
              hnew ⟨a.val, haN⟩
        · -- Nonempty intersection for the enlarged prefix.
          -- The witness z supplied by hpick works.
          refine ⟨z, Set.mem_iInter.mpr ?_⟩
          intro a
          refine Fin.lastCases ?_ (fun i ↦ ?_) a
          · -- when the omitted index is the new index.
            have hNSucc : 2 ≤ N.succ := by
              omega
            have hEq : prodExcept hNSucc (fun k ↦ s k) (Fin.last N) = prodAll hN fun k ↦ s k := by
              apply prodExcept_last_eq_prodAll
            rw [hEq]
            exact hzall
          · -- when the omitted index is an old index.
            have hNSucc : 2 ≤ N.succ := by
              omega
            simp only [Set.mem_iInter] at hzold
            specialize hzold i
            have hEq : prodExcept hNSucc (fun k ↦ s k) i.castSucc
              = (prodExcept hN (fun k ↦ s ↑k) i) * s N := by
              apply prodExcept_castSucc_eq
            rw [hEq]
            exact hzold
  -- prove the sequence s satisfies the conclusion
  have hGoalV0 : ∃ s : ℕ → S, ∀ (i j : ℕ), i < j → s j
    ∈ (fun x ↦ (s i) * x) '' (visitTimeSet dSystem x V0 ∩ H) := by
    use s
    intro i j hij
    by_cases hj2 : j ≥ 2
    · specialize hs_step j hj2
      change s j ∈ (fun x ↦ (s i) * x) '' C
      rw [hs_step]
      refine (hpick j hj2 (fun k : Fin j ↦ s k.val) ?_).1 ⟨i, hij⟩
      constructor
      · exact (hprefix_all j hj2).1
      · exact (hprefix_all j hj2).2
    · have hjlesseq1 : j ≤ 1 := by
        omega
      have hjequal1 : j = 1 := by
        by_contra hContra
        have hjequal0 : j = 0 := by
          omega
        have hiatleast0 : i ≥ 0 := by
          omega
        have hjatleast1 : j ≥ 1 := by
          omega
        rw [hjequal0] at hjatleast1
        omega
      have hiequal0 : i = 0 := by
        omega
      rw [hjequal1, hiequal0, hs0, hs1]
      exact hs1a
  -- finish the proof by using the sequence s
  rcases hGoalV0 with ⟨s, hs⟩
  use s
  intro i j hij
  specialize hs i j hij
  simp only [Set.mem_image, Set.mem_inter_iff] at hs
  rcases hs with ⟨r, hr1, hr2⟩
  rcases hr1 with ⟨hr1a, hr1b⟩
  simp only [Set.mem_image, Set.mem_inter_iff]
  use r
  constructor
  · constructor
    · simp only [visitTimeSet, Set.mem_preimage]
      simp only [visitTimeSet, Set.mem_preimage] at hr1a
      apply hV0a hr1a
    · exact hr1b
  · exact hr2

end Delta_builder

section Dynamical_sets_of_bohr_recurrence

/-- If B is a set of Bohr recurrence and a uniformly recurrent set,
then for all thick set H, B ∩ H is a Δ set -/
theorem commURSetsOfBohrRecurrenceAreDelta
{S : Type*} [CommSemigroup S] [Nonempty S]
(B : Set S) {hBur : isURSet B} {hBrec : isSetOfBohrRecurrence B} :
∀ (H : Set S), isThick H → isDelta (B ∩ H) := by
  intro H hHThick
  rcases (urSetIsRxU hBur) with
    ⟨X, _, _, _, hXNonempty, dSystemX, hXMin, x, U, hUClopen, hBvis⟩
  have hBNonempty : B.Nonempty := by
    exact setOfBohrRecurrenceNonempty B hBrec
  have hBinBohr : B ∈ setOfBohrRecurrenceFamily S := by
    simp only [setOfBohrRecurrenceFamily]
    exact hBrec
  have hBohrPR : isPRFamily (setOfBohrRecurrenceFamily S) := by
    exact setOfBohrRecurrenceFamilyIsPR S
  have hUClosed : IsClosed U := by
    unfold IsClopen at hUClopen
    exact hUClopen.1
  have hUNonempty : U.Nonempty := by
    rcases Set.nonempty_def.mp hBNonempty with ⟨s, hs⟩
    rw [hBvis] at hs
    simp only [visitTimeSet, Set.mem_preimage] at hs
    exact ⟨dSystemX.map s x, hs⟩
  have hNew := visitTimeConcentrationForPRFamily dSystemX x U hUClosed hUNonempty
    (setOfBohrRecurrenceFamily S) hBohrPR
  rw [<- hBvis] at hNew
  specialize hNew hBinBohr
  rcases hNew with ⟨y, hyU, hy1⟩
  have hxyEQ : (x, y) ∈ equiStructureRelation dSystemX := by
    simp only [equiStructureRelation, Set.mem_sInter]
    intro I hI
    unfold setOfEquicontinuousICERS at hI
    rcases hI with ⟨hIicer, hIEq⟩
    simp only [setOfICERS, Set.mem_ofPred_eq] at hIicer
    have hGoal : (setToRelation I) x y := by
      have hIEquiRel : Equivalence (setToRelation I) := by
        unfold isICER at hIicer
        rcases hIicer with ⟨hIicer1, hIicer2, hIicer3⟩
        unfold isEquivalenceRelation at hIicer3
        exact hIicer3
      let K := Quotient ⟨setToRelation I, hIEquiRel⟩
      let dSystemK := quotientDynamicalSystem dSystemX hIicer
      let π : X → K := (Quotient.mk ⟨setToRelation I, hIEquiRel⟩)
      have hKT2 : T2Space K := by
        apply quotientOfCompactT2ByClosedIsT2
        · unfold isICER at hIicer
          rcases hIicer with ⟨hIicer1, hIicer2, hIicer3⟩
          exact hIicer2
      have hKNonempty : Nonempty K := by
        apply nonemptyQuotient X hIEquiRel
      apply (Equivalence.quot_mk_eq_iff hIEquiRel x y).mp
      have hπFactorMap : isFactorMap dSystemX dSystemK π := by
        apply quotientMapIsFactorMap
      have hFactor : isFactor dSystemK dSystemX := by
        unfold isFactor
        use π
      have hKMin : isMinimalSystem dSystemK := by
        apply factorOfMinimalIsMinimal hXMin hFactor
      have hKEquiC : isEquicontinuousSystem dSystemK := by
        unfold isEquicontinuousICER at hIEq
        exact hIEq
      have hπxy : π x = π y := by
        by_contra hContra
        let hSep := t2_separation hContra
        rcases hSep with ⟨V, W, hV1, hW1, hV2, hW2, hVW⟩
        let C := visitTimeSet dSystemK (π x) V
        have hCBohr : isBohrZero C := by
          apply equiReturnsAreBohrZero
          use K, inferInstance, inferInstance, inferInstance, inferInstance
          use dSystemK, hKEquiC, hKMin, π x, V
        have hWNeigh : π⁻¹' W ∈ nhds y := by
          apply mem_nhds_iff.mpr
          use π⁻¹' W
          constructor
          · simp
          constructor
          · apply IsOpen.preimage
            · unfold isFactorMap at hπFactorMap
              exact hπFactorMap.1
            · exact hW1
          · simp only [Set.mem_preimage]
            exact hW2
        specialize hy1 (π⁻¹' W) hWNeigh
        have hNonemptyInter : (visitTimeSet dSystemX x (π ⁻¹' W) ∩
          visitTimeSet dSystemK (π x) V).Nonempty := by
          apply (mem_famDual (bohrZeroFamily S) (visitTimeSet dSystemX x (π ⁻¹' W))).mp
          · exact hy1
          · simp only [bohrZeroFamily, SetLike.mem_coe]
            exact hCBohr
        apply Set.inter_nonempty.mp at hNonemptyInter
        rcases hNonemptyInter with ⟨s, hs1, hs2⟩
        simp only [visitTimeSet, Set.mem_preimage] at hs1
        simp only [visitTimeSet, Set.mem_preimage] at hs2
        rcases hπFactorMap with ⟨hπ1, hπ2, hπ3⟩
        simp only [isEquivariant] at hπ3
        specialize hπ3 s
        have hπ3x : (dSystemK.map s ∘ π) x = (π ∘ dSystemX.map s) x := by
          apply congr_fun hπ3
        have hπ3x1 : (dSystemK.map s ∘ π) x = dSystemK.map s (π x) := by
          rfl
        have hπ3x2 : (π ∘ dSystemX.map s) x = π (dSystemX.map s x) := by
          rfl
        rw [<- hπ3x2, <- hπ3x, hπ3x1] at hs1
        have hVWNotDisjoint : ¬Disjoint V W := by
          apply Set.not_disjoint_iff.mpr
          use dSystemK.map s (π x)
        exact hVWNotDisjoint hVW
      exact hπxy
    unfold setToRelation at hGoal
    exact hGoal
  have hxyRP : (x, y) ∈ RP dSystemX := by
    rw [RPisEquiStructureRelation hXMin]
    exact hxyEQ
  have hUNeigh : U ∈ nhds y := by
    apply mem_nhds_iff.mpr
    use U
    constructor
    · simp
    constructor
    · exact hUClopen.2
    · exact hyU
  have hDelta := commVisitTimeSetForRPPairIsDelta dSystemX hXMin x y hxyRP hUNeigh
  specialize hDelta H hHThick
  rw [hBvis]
  exact hDelta

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
        exact deltaZeroImpliesSetOfBohrRecurrence
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
      intro B H hBUR hHThick hCond H' hH'H hH'Thick
      specialize hCond H' hH'H hH'Thick
      specialize h3 B H' hBUR hH'Thick hCond
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
    exact deltaZeroImpliesSetOfBohrRecurrence
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
    intro x hx
    exact hx
  have h2 : (bohrZeroFamily S)** = bohrZeroFamily S := by
    apply dualIsInvolutionOnFamilies
  rw [<- h2]
  exact (familyLocalImplicationEquivalence (syndeticFamily S)
  (bohrZeroFamily S)* (deltaFamily S)).mpr h1

/-- In a countable, commutative semigroup S ⋏ IP = S ⋏ C -/
theorem strongIPIffStrongCentralInCountCommSemi
(S : Type*) [CommSemigroup S] [Nonempty S] [Countable S] :
(syndeticFamily S) ⋏ (IPFamily S) = (syndeticFamily S) ⋏ (centralFamily S) := by
  have contain1 : (syndeticFamily S) ⋏ (IPFamily S) ⊆ (syndeticFamily S) ⋏ (centralFamily S) := by
    apply urContainmentSufficesForFamilyContainment
    intro B H hB Hthick hypoth H' H'inH H'thick
    obtain ⟨X,_,_,_,_,dSystem,hMin,x,U,Uclopen,Bvisits⟩ := urSetIsRxU hB
    have applyPre := preStrongIPIffStrongCentralInCountCommSemi hMin x Uclopen H Hthick
    rw [Bvisits] at hypoth
    rw [Bvisits]
    exact applyPre hypoth H' H'inH H'thick
  have contain2 := familyMeetIsMonotonic (syndeticFamily S) (centralFamily S)
    (IPFamily S) (centralFamilyContainedInIPFamily S)
  ext A
  constructor
  · intro hA
    exact contain1 hA
  · intro hA
    exact contain2 hA

/-- A subset of a countable, commutative semigroup is central star if and only if
it is strongly piecewise IP*, if and only if it is strongly piecewise central* -/
theorem cStarIsStronglyPiecewiseIPStarAndCStar
(S : Type*) [CommSemigroup S] [Nonempty S] [Countable S] :
(centralFamily S)* = (syndeticFamily S) ⋏ ((IPFamily S)* ⋎ (thickFamily S)) ∧
(centralFamily S)* = (syndeticFamily S) ⋏ ((centralFamily S)* ⋎ (thickFamily S)) :=
by
  have contain0 : (syndeticFamily S) ⋏ (IPFamily S) ⊆ (syndeticFamily S) ⋏ (centralFamily S) := by
    rw [strongIPIffStrongCentralInCountCommSemi S]
    exact
      familyMeetIsMonotonic (syndeticFamily S) (centralFamily S) (centralFamily S) fun ⦃a⦄ a_1 ↦ a_1
  have contain1 : (centralFamily S)* ⊆
    (syndeticFamily S) ⋏ ((IPFamily S)* ⋎ (thickFamily S)) := by
      have := (familyLocalImplicationEquivalence (syndeticFamily S)
        (IPFamily S) (centralFamily S)).mpr contain0
      rw [familyJoinCommutative] at this
      rw [dualSyndeticThick] at this
      exact this
  have contain2 : (syndeticFamily S) ⋏ ((IPFamily S)* ⋎ (thickFamily S)) ⊆
    (syndeticFamily S) ⋏ ((centralFamily S)* ⋎ (thickFamily S)) := by
      have := dualIsAntitone (centralFamilyContainedInIPFamily S)
      have := familyJoinMonotoneSlot1 (thickFamily S) this
      exact familyMeetIsMonotonic (syndeticFamily S) ((IPFamily S)* ⋎ thickFamily S)
        ((centralFamily S)* ⋎ thickFamily S) this
  have contain3 : (syndeticFamily S) ⋏ ((centralFamily S)* ⋎ (thickFamily S)) ⊆
    (centralFamily S)* := by
      have := familyJoinMonotoneSlot2 (thickFamily S) (dcsIsSyndeticMeetCentral S)
      rw [familyJoinCommutative] at this
      rw [←centralIsdcSCapThick S] at this
      have := dualIsAntitone this
      rw [deMorganOverJoin] at this
      rw [deMorganOverMeet] at this
      rw [dualThickSyndetic] at this
      rw [dualSyndeticThick] at this
      exact this
  constructor
  · ext A
    constructor
    · intro hA
      exact contain1 hA
    · intro hA
      exact contain3 (contain2 hA)
  · ext A
    constructor
    · intro hA
      exact contain2 (contain1 hA)
    · intro hA
      exact contain3 hA

end Application
