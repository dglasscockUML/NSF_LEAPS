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

/-- If (x, y) is in regional proximal relation in a minimal system X and V ∋ y,
then for all thick set H, R(x, V) ∩ H is a Delta set -/
theorem commVisitTimeSetForRPPairIsDelta
{S : Type*} [CommSemigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) (hMin : isMinimalSystem dSystem)
(x y : X) (hxyRP : (x, y) ∈ RP dSystem)
{V : Set X} (hV : V ∈ nhds y) :
∀ (H : Set S), isThick H → isDelta ((visitTimeSet dSystem x V) ∩ H) := by
  intro H hHThick
  unfold isDelta
  let C := (visitTimeSet dSystem x V) ∩ H
  -- have hClaim : ∀ N : ℕ+, ∀ s : Fin N → S, ∀ i j : Fin N, (i < j) →  s j
  --    ∈ (fun x ↦ (s i) * x) '' C ∧
  --   (⋂ i : Fin N, (dSystem.map (∏ j : Fin N, ∏ (_ : j ≠ i), s j)) ⁻¹' V).Nonempty := by
  --   sorry
  sorry

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
    apply thm_dual_is_involution
  rw [<- h2]
  exact (familyLocalImplicationEquivalence (syndeticFamily S)
  (bohrZeroFamily S)* (deltaFamily S)).mpr h1

/-- In a countable, commutative semigroup S ⋏ IP = S ⋏ C -/
theorem strongIPIffStrongCentralInCountCommSemi
(S : Type*) [CommSemigroup S] [Nonempty S] [Countable S] :
(syndeticFamily S) ⋏ (IPFamily S) = (syndeticFamily S) ⋏ (centralFamily S) := by
-- Proof: by urContainmentSufficesForFamilyContainment, it suffices to consider UR sets only
-- For UR sets, this is proven in preStrongIPIffStrongCentralInCountCommSemi
-- Will wait to write proof until def of UR sets is fixed
  sorry

/-- A subset of a countable, commutative semigroup is central star if and only if
it is strongly piecewise IP*, if and only if it is strongly piecewise central* -/
theorem cStarIsStronglyPiecewiseIPStarAndCStar
(S : Type*) [CommSemigroup S] [Nonempty S] [Countable S] :
(centralFamily S)* = (syndeticFamily S) ⋏ ((IPFamily S)* ⋎ (thickFamily S)) ∧
(centralFamily S)* = (syndeticFamily S) ⋏ ((centralFamily S)* ⋎ (thickFamily S)) :=
by sorry -- Wait. Will rely on Furstenburg algebra.

end Application
