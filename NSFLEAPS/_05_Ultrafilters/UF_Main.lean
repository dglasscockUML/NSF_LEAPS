import NSFLEAPS._04_Dynamical_systems.DS_Main

/-!
# Ultrafilters as tools in topological dynamics

This file develops the machinery of ultrafilters as tools in topological dynamics.
-/

section Right_topological_semigroups

-- For def. of RightTopological, cf. Hindman-Strauss Def. 2.1
/-- A topological semigroup `S` is RightTopological if for all elements `s ∈ S`,
right multiplication by `s`, as a function from `S → S`, is continuous -/
class RightTopological (S : Type*) [Semigroup S] [TopologicalSpace S] where
  rightCont : ∀ (s : S), Continuous (· * s)

variable {S : Type*} [Semigroup S] [TopologicalSpace S]
  [CompactSpace S] [T2Space S] [hRT : RightTopological S]

/-- Compact, Hausdorff, right-topological semigroups contain an idempotent element -/
theorem compactT2RTSemigroupContainsIdempotent [Nonempty S] :
∃ (s : S), s * s = s :=
exists_idempotent_of_compact_t2_of_continuous_mul_left hRT.rightCont

/-- In a compact, Hausdorff, right-topological semigroup `S`, principal left ideals,
that is, sets of the form `Ss`, are closed -/
theorem principalLeftIdealClosed
(s : S) :
IsClosed ((· * s) '' Set.univ) := by
  have hCompact : IsCompact ((· * s) '' Set.univ) := by
    apply IsCompact.image
    · exact isCompact_univ
    · apply hRT.rightCont
  apply IsCompact.isClosed
  exact hCompact

/-- In a compact, Hausdorff, right-topological semigroup `S`, every left ideal
contains a closed left ideal -/
theorem leftIdealContainsClosedLeftIdeal
(L : Set S) {hL : isLeftIdeal L} :
∃ (M : Set S), isLeftIdeal M ∧ IsClosed M ∧ M ⊆ L := by
  rcases hL with ⟨hL1, hL2⟩
  rcases hL1 with ⟨s, hs⟩
  let M := (· * s) '' Set.univ
  use M
  constructor
  · unfold isLeftIdeal
    constructor
    · have hMNonempty : s * s ∈ M := by
        simp [M]
      exact ⟨s * s, hMNonempty⟩
    · intro r t ht
      simp only [Set.mem_image] at ht
      rcases ht with ⟨m, hm1, hm2⟩
      rw [<- hm2]
      rcases hm1 with ⟨n, hn1, hn2⟩
      simp only at hn2
      rw [<- hn2]
      have hEq : (r * n) * s = r * (n * s):= by
        apply Semigroup.mul_assoc
      rw [<- hEq]
      simp [M]
  constructor
  · apply principalLeftIdealClosed
  · intro x hx
    simp only [Set.image_univ, Set.mem_range, M] at hx
    rcases hx with ⟨y, hy⟩
    rw [<- hy]
    specialize hL2 y
    apply hL2
    simp only [Set.mem_image]
    use s

/-- In a compact, Hausdorff, right-topological semigroup `S`, every minimal left
ideal is compact -/
theorem minimalLeftIdealCompact
{L : Set S} (hL : isMinLeftIdeal L) :
IsCompact L := by
  rcases hL with ⟨hL1, hL2⟩
  have hM : ∃ (M : Set S), isLeftIdeal M ∧ IsClosed M ∧ M ⊆ L := by
    apply leftIdealContainsClosedLeftIdeal
    exact hL1
  rcases hM with ⟨M, hM1, hM2, hM3⟩
  specialize hL2 M hM1 hM3
  have hLClosed : IsClosed L := by
    rw [<- hL2]
    exact hM2
  apply IsClosed.isCompact
  exact hLClosed

/-- In a compact, Hausdorff, right-topological semigroup `S`, every left ideal
contains a minimal left ideal -/
theorem leftIdealContainsMinLeftIdeal
(L : Set S) {hL : isLeftIdeal L} :
∃ (M : Set S), isMinLeftIdeal M ∧ M ⊆ L := by
  have LContain : ∃ LC : Set S, isLeftIdeal LC ∧ IsClosed LC ∧ LC ⊆ L := by
    apply leftIdealContainsClosedLeftIdeal
    exact hL
  rcases LContain with ⟨LC, hLC1, hLC2, hLC3⟩
  let C := {I : Set S | IsClosed I ∧ isLeftIdeal I ∧ I ⊆ LC}
  have hChain : ∀ c ⊆ C, IsChain (· ⊆ ·) c → c.Nonempty → ∃ lb ∈ C, ∀ t ∈ c, lb ⊆ t := by
    intro c hc1 hc2 hc3
    let lb := c.sInter
    use lb
    constructor
    · simp only [Set.mem_ofPred_eq, C]
      constructor
      · apply isClosed_sInter
        intro t ht
        have htInC : t ∈ C := by
          apply hc1 ht
        simp only [Set.mem_ofPred_eq, C] at htInC
        rcases htInC with ⟨ht1, ht2, ht3⟩
        exact ht1
      constructor
      · apply nonemptyInterOfLeftIdealsIsLeftIdeal
        · intro t ht
          have htInC : t ∈ C := by
            apply hc1 ht
          simp only [Set.mem_ofPred_eq, C] at htInC
          rcases htInC with ⟨ht1, ht2, ht3⟩
          exact ht2
        have hcNonempty : Nonempty c := by
          simpa
        apply IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
        · simp only [DirectedOn]
          intro x hx y hy
          simp only [IsChain] at hc2
          specialize hc2 hx hy
          by_cases hxEqy : x = y
          · use x
            constructor
            · exact hx
            constructor
            · simp
            · rw [hxEqy]
          · specialize hc2 hxEqy
            rcases hc2 with hP | hQ
            · use x
            · use y
        · intro t ht
          have htInC : t ∈ C := by
            apply hc1 ht
          simp only [Set.mem_ofPred_eq, C] at htInC
          rcases htInC with ⟨ht1, ht2, ht3⟩
          rcases ht2 with ⟨ht2a, ht2b⟩
          exact ht2a
        · intro t ht
          have htInC : t ∈ C := by
            apply hc1 ht
          simp only [Set.mem_ofPred_eq, C] at htInC
          rcases htInC with ⟨ht1, ht2, ht3⟩
          apply IsClosed.isCompact ht1
        · intro t ht
          have htInC : t ∈ C := by
            apply hc1 ht
          simp only [Set.mem_ofPred_eq, C] at htInC
          rcases htInC with ⟨ht1, ht2, ht3⟩
          exact ht1
      simp only [lb]
      rcases hc3 with ⟨t, ht⟩
      have htInC : t ∈ C := by
        apply hc1 ht
      simp only [Set.mem_ofPred_eq, C] at htInC
      rcases htInC with ⟨ht1, ht2, ht3⟩
      have htInt : c.sInter ⊆ t := by
        apply Set.sInter_subset_of_mem ht
      exact htInt.trans ht3
    · intro t ht
      simp only [lb]
      apply Set.sInter_subset_of_mem ht
  have hLCinC : LC ∈ C := by
    simp only [Set.mem_ofPred_eq, subset_refl, and_true, C]
    constructor
    · exact hLC2
    · exact hLC1
  have hExistMin : ∃ M, M ⊆ LC ∧ Minimal (· ∈ C) M := by
    apply zorn_superset_nonempty
    · exact hChain
    · exact hLCinC
  rcases hExistMin with ⟨M, hM1, hM2⟩
  use M
  unfold Minimal at hM2
  rcases hM2 with ⟨hM2a, hM2b⟩
  constructor
  · constructor
    · simp only [Set.mem_ofPred_eq, C] at hM2a
      rcases hM2a with ⟨hMClosed, hMLeftIdeal, hMjunk⟩
      exact hMLeftIdeal
    · intro I hI1 hI2
      have hIContain : ∃ J : Set S, isLeftIdeal J ∧ IsClosed J ∧ J ⊆ I := by
        apply leftIdealContainsClosedLeftIdeal
        exact hI1
      rcases hIContain with ⟨J, hJ1, hJ2, hJ3⟩
      have hJinC : J ∈ C := by
        simp only [Set.mem_ofPred_eq, C]
        constructor
        · exact hJ2
        constructor
        · exact hJ1
        · exact (hJ3.trans hI2).trans hM1
      specialize hM2b hJinC (hJ3.trans hI2)
      have hMinI : M ⊆ I := by
        exact hM2b.trans hJ3
      apply subset_antisymm hI2 hMinI
  · exact hM1.trans hLC3

/-- Compact, right-topological semigroups contain minimal left ideals -/
theorem rightTopSemigroupContainsMinLeftIdeal [Nonempty S] :
∃ (L : Set S), isMinLeftIdeal L := by
  have hSleftIdeal : isLeftIdeal (Set.univ : Set S) := by
    unfold isLeftIdeal
    constructor
    · simp
    · simp
  have hExistLeftIdeal : ∃ (M : Set S), isMinLeftIdeal M ∧ M ⊆ Set.univ := by
    apply leftIdealContainsMinLeftIdeal
    exact hSleftIdeal
  rcases hExistLeftIdeal with ⟨L, hL1, hL2⟩
  use L

omit [CompactSpace S] in
/-- In a compact, Hausdorff, right-topological semigroup `S`, a compact
subsemigroup contains and idempotent element -/
theorem compactSubsemigroupContainsIdempotent
(T : Set S) {hTsemi : isSubsemigroup T}
{hTcompact : IsCompact T} {hTnonempty : T.Nonempty} :
∃ s ∈ T, s * s = s :=
exists_idempotent_in_compact_subsemigroup hRT.rightCont T hTnonempty hTcompact hTsemi

/-- In a compact, Hausdorff, right-topological semigroup `S`, a left ideal contains
an idempotent element -/
theorem leftIdealContainsIdempotent
(L : Set S) {hL : isLeftIdeal L} :
∃ s ∈ L, s * s = s := by
  have hContain : ∃ (M : Set S), isMinLeftIdeal M ∧ M ⊆ L := by
    apply leftIdealContainsMinLeftIdeal
    exact hL
  rcases hContain with ⟨M, hM1, hM2⟩
  have hMsemi : isSubsemigroup M := by
    unfold isSubsemigroup
    intro s hs t ht
    rcases hM1 with ⟨hM1a, hM1b⟩
    rcases hM1a with ⟨hM1a1, hM1a2⟩
    specialize hM1a2 s
    apply hM1a2
    simp only [Set.mem_image]
    use t
  have hMcompact : IsCompact M := by
    apply minimalLeftIdealCompact
    exact hM1
  rcases hM1 with ⟨hM1a, hM1b⟩
  rcases hM1a with ⟨hM1a1, hM1a2⟩
  have hMcontainIdem : ∃ s ∈ M, s * s = s := by
    apply compactSubsemigroupContainsIdempotent
    · exact hMsemi
    · exact hMcompact
    · exact hM1a1
  rcases hMcontainIdem with ⟨s, hs1, hs2⟩
  use s
  constructor
  · apply hM2
    exact hs1
  · exact hs2

end Right_topological_semigroups

section Semigroup_stuff

/-- `OurSemigroupAction S X` is, for each `s : S`, a map `s: X → X` such that
`st: X → X` is the composition of `s: X → X` and `t: X → X` -/
structure OurSemigroupAction
(S : Type*) [Semigroup S] (X : Type*) where
  map : S → X → X
  mapMult : ∀ s₁ s₂ x, map (s₁ * s₂) x = map s₁ (map s₂ x)

/-- The predicate that the map `φ : S → T` is a semigroup homomorphism -/
def isSemigroupHom
{S T : Type*} [Semigroup S] [Semigroup T] (φ : S → T) :
Prop :=
∀ (s1 s2 : S), φ (s1 * s2) = (φ s1) * (φ s2)

end Semigroup_stuff

section Generic_ultrafilter_lemmas

/-- The range of the lift of `f : S → X` to `βS → X` is equal to the
closure of the range of `f` -/
lemma ultraLiftMapsToClosure
{S} {X} [TopologicalSpace X] [CompactSpace X] [T2Space X]
(f : S → X) :
Set.range (Ultrafilter.extend f) = closure (Set.range f) := by
  have rangeDef : Set.range (Ultrafilter.extend f) = Ultrafilter.extend f '' Set.univ := by
    simp only [Set.image_univ]
  have setUnivIsClos : Set.univ = closure (Set.range (pure : S → Ultrafilter S)) := by
    have := denseRange_pure (α := S)
    unfold DenseRange at this
    exact (Dense.closure_eq this).symm
  have fImageDesc : Set.range (Ultrafilter.extend f) =
    (Ultrafilter.extend f) '' (closure (Set.range (pure : S → Ultrafilter S))) := by
      rw [rangeDef]
      rw [setUnivIsClos]
  have hThree : (Ultrafilter.extend f) '' closure (Set.range (pure : S → Ultrafilter S)) =
    closure ((Ultrafilter.extend f) '' (Set.range (pure : S → Ultrafilter S))) := by
      exact imageClosureIsClosureImage
        (continuous_ultrafilter_extend f) (Set.range (pure : S → Ultrafilter S))
  have imageOfPure : (Ultrafilter.extend f) '' (Set.range (pure : S → Ultrafilter S)) =
    f '' Set.univ := by
      ext x
      constructor
      · intro hx
        simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and,
          ultrafilter_extend_pure] at hx
        obtain ⟨s, hs⟩ := hx
        use s
        exact ⟨Set.mem_univ s,hs⟩
      · intro hx
        simp only [Set.image_univ, Set.mem_range] at hx
        obtain ⟨s, hs⟩ := hx
        use pure s
        constructor
        · simp only [Set.mem_range, exists_apply_eq_apply]
        · simp only [ultrafilter_extend_pure]
          exact hs
  rw [imageOfPure] at hThree
  rw [hThree] at fImageDesc
  simp only [Set.image_univ] at fImageDesc
  exact fImageDesc

@[simp]
lemma ultrafilter_extend_id {S} :
Ultrafilter.extend (pure : S → Ultrafilter S) = id := by
  apply Continuous.ext_on
    denseRange_pure
    (continuous_ultrafilter_extend pure)
    (continuous_id)
  intro x hx
  simp only [Set.mem_range] at hx
  obtain ⟨y,hy⟩ := hx
  rw [←hy]
  rw [ultrafilter_extend_pure]
  exact Ultrafilter.eq_of_le fun ⦃U⦄ a ↦ a

end Generic_ultrafilter_lemmas

section Ultrafilters_as_a_semigroup

/-- `leftMult s : S → S` is left multiplication by `s` -/
def leftMult
{S : Type*} [Semigroup S] (s : S) :
S → S :=
  (s * ·)

/-- `rightMult s : S → S` is right multiplication by `s` -/
def rightMult
{S : Type*} [Semigroup S] (s : S) :
S → S :=
  (· * s)

/-- This instance makes the semigroup structure on βS "canonical" by
making it available to typeclass inference -/
instance
{S : Type*} [Semigroup S] : Semigroup (Ultrafilter S) :=
  Ultrafilter.semigroup

/-- An equivalent, alternative description of the ultrafilter product -/
theorem ultraProductDescription
{S : Type*} [Semigroup S] (p q : Ultrafilter S) (A : Set S) :
A ∈ p * q ↔ {s : S | {t : S | s * t ∈ A} ∈ q} ∈ p :=
  Iff.rfl

/-- `leftMultUltra q : βS → βS` is left multiplication by `q` -/
def leftMultUltra
{S : Type*} [Semigroup S] (q : Ultrafilter S) :
Ultrafilter S → Ultrafilter S :=
  (q * ·)

/-- `rightMultUltra q : βS → βS` is right multiplication by `q` -/
def rightMultUltra
{S : Type*} [Semigroup S] (q : Ultrafilter S) :
Ultrafilter S → Ultrafilter S :=
(· * q)

/-- The canonical injection pure : S → βS is a semigroup homomorphism -/
theorem pureIsHom
{S : Type*} [Semigroup S] :
isSemigroupHom (pure : S → Ultrafilter S) :=
by
  unfold isSemigroupHom
  intro s t
  constructor

/-- Given `s ∈ S`, `B ⊆ S`, and `p ∈ βS`, `B ∈ sp` iff `s⁻¹B ∈ p` -/
theorem membershipInLeftMultByPrincipal
{S : Type*} [Semigroup S]
(s : S) (B : Set S) (p : Ultrafilter S) :
B ∈ leftMultUltra (pure s) p ↔ (leftMult s) ⁻¹' B ∈ p := by
  constructor
  · intro hB
    have h1 : leftMultUltra (pure s) p = (pure s) * p := by
      rfl
    rw [h1] at hB
    simp only [ultraProductDescription, Ultrafilter.mem_pure, Set.mem_ofPred_eq] at hB
    have h2 : {t | s * t ∈ B} = leftMult s ⁻¹' B := by
      rfl
    rw [<- h2]
    exact hB
  · intro hB
    simp only [leftMultUltra]
    simp only [ultraProductDescription, Ultrafilter.mem_pure, Set.mem_ofPred_eq]
    have h2 : {t | s * t ∈ B} = leftMult s ⁻¹' B := by
      rfl
    rw [h2]
    exact hB

/-- If ultrafilter `p ∈ closure of B`, then `B ∈ p` -/
lemma memClosurePureIff
{S : Type*} [Semigroup S]
(B : Set S) (p : Ultrafilter S) :
p ∈ closure (pure '' B) ↔ B ∈ p := by
  constructor
  · intro hp
    by_contra hBNotInp
    have hBCom : Bᶜ ∈ p := by
      apply Ultrafilter.compl_mem_iff_notMem.mpr hBNotInp
    let U := {u : Ultrafilter S | Bᶜ ∈ u}
    have hpInU : p ∈ U := by
      simp only [Set.mem_ofPred_eq, U]
      exact hBCom
    have hUOpen : IsOpen U := by
      apply ultrafilter_isOpen_basic
    have hpBInter : (U ∩ pure '' B).Nonempty := by
      apply mem_closure_iff.mp hp
      · exact hUOpen
      · exact hpInU
    rcases hpBInter with ⟨q, hq1, hq2⟩
    simp only [Set.mem_ofPred_eq, U] at hq1
    simp only [Set.mem_image] at hq2
    rcases hq2 with ⟨b, hb1, hb2⟩
    rw [<- hb2] at hq1
    simp only [Ultrafilter.mem_pure, Set.mem_compl_iff] at hq1
    exact hq1 hb1
  · intro hBinp
    apply mem_closure_iff.mpr
    intro U hU hpinU
    have hUNeigh : U ∈ nhds p := by
      apply mem_nhds_iff.mpr
      use U
    have hUCon : ∃ t ∈ ultrafilterBasis S, p ∈ t ∧ t ⊆ U := by
      apply (TopologicalSpace.IsTopologicalBasis.mem_nhds_iff ultrafilterBasis_is_basis).mp
      exact hUNeigh
    rcases hUCon with ⟨t, ht1, ht2, ht3⟩
    simp only [ultrafilterBasis, Set.mem_range] at ht1
    rcases ht1 with ⟨A, hA⟩
    have htIntB : (t ∩ pure '' B).Nonempty := by
      rw [<- hA] at ht2
      simp only [Set.mem_ofPred_eq] at ht2
      have hABinp : A ∩ B ∈ p := by
        apply Filter.inter_mem ht2 hBinp
      have hABNonempty : (A ∩ B).Nonempty := by
        apply Ultrafilter.nonempty_of_mem hABinp
      rcases hABNonempty with ⟨x, hx1, hx2⟩
      have hxB : (pure x : Ultrafilter S) ∈ (pure '' B : Set (Ultrafilter S) ):= by
        apply (Set.mem_image pure B (pure x)).mpr
        use x
      have hxt : pure x ∈ t := by
        rw [<- hA]
        simp only [Set.mem_ofPred_eq, Ultrafilter.mem_pure]
        exact hx1
      exact ⟨pure x, hxt, hxB⟩
    have hSubSet : t ∩ pure '' B ⊆ U ∩ pure '' B := by
      apply Set.inter_subset_inter
      · exact ht3
      · rfl
    apply Set.Nonempty.mono hSubSet htIntB

/-- Given `s ∈ S` and `B ⊆ S`, `closure(s⁻¹B) = s⁻¹closure(B)` -/
theorem preimageClosureDescription
{S : Type*} [Semigroup S]
(s : S) (B : Set S) :
closure ((pure : S → Ultrafilter S) '' ((leftMult s) ⁻¹' B)) =
(leftMultUltra (pure s)) ⁻¹' (closure ((pure : S → Ultrafilter S) '' B)) := by
  ext p
  constructor
  · intro hp
    simp only [memClosurePureIff] at hp
    simp only [← membershipInLeftMultByPrincipal] at hp
    simp only [← memClosurePureIff] at hp
    simp only [Set.mem_preimage]
    exact hp
  · intro hp
    simp only [Set.mem_preimage] at hp
    simp only [memClosurePureIff] at hp
    simp only [membershipInLeftMultByPrincipal] at hp
    simp only [← memClosurePureIff] at hp
    exact hp

/-- Given a minimal left ideal `L ⊆ βS` and an idempotent `u ∈ L`,
for all `p ∈ L`, `pu = p` -/
theorem minimalIdempotentsAreLeftIdentites
{S : Type*} [Semigroup S]
(L : Set (Ultrafilter S)) {hL : isMinLeftIdeal L}
(u : Ultrafilter S) {huL : u ∈ L} {huIdempotent : u * u = u}
(p : Ultrafilter S) :
p ∈ L → p * u = p := by
  intro hpL
  let Lu := (· * u) '' L
  rcases hL with ⟨hL1, hL2⟩
  unfold isLeftIdeal at hL1
  rcases hL1 with ⟨hL1a, hL1b⟩
  have hLuInL : Lu ⊆ L := by
    intro a ha
    simp only [Set.mem_image, Lu] at ha
    rcases ha with ⟨x, hx1, hx2⟩
    rw [<- hx2]
    specialize hL1b x
    apply hL1b
    simp only [Set.mem_image]
    use u
  have hLuLeftI : isLeftIdeal Lu := by
    constructor
    · rcases hL1a with ⟨l, hl⟩
      have hlIn : l * u ∈ Lu := by
        simp only [Set.mem_image, Lu]
        use l
      exact ⟨l * u, hlIn⟩
    · intro s a ha
      simp only [Set.mem_image] at ha
      rcases ha with ⟨x, hx1, hx2⟩
      simp only [Set.mem_image, Lu] at hx1
      rcases hx1 with ⟨y, hy1, hy2⟩
      rw [<- hy2] at hx2
      rw [<- hx2]
      have hsyu : (s * y) * u = s * (y * u):= by
        apply Semigroup.mul_assoc
      rw [<- hsyu]
      simp only [Set.mem_image, Lu]
      use s * y
      constructor
      · specialize hL1b s
        apply hL1b
        simp only [Set.mem_image]
        use y
      · rfl
  have hLuEqL : Lu = L := by
    exact hL2 Lu hLuLeftI hLuInL
  have hpLu : p ∈ Lu := by
    rw [hLuEqL]
    exact hpL
  simp only [Set.mem_image, Lu] at hpLu
  rcases hpLu with ⟨q, hq1, hq2⟩
  rw [<- hq2]
  have hquu : (q * u) * u = q * (u * u) := by
    apply Semigroup.mul_assoc
  rw [hquu]
  rw [huIdempotent]

/-- The predicate that the ultrafilter p on S is minimal, that is, belongs to
some minimal left ideal -/
def isMinimalUltrafilter
{S : Type*} [Semigroup S] (p : Ultrafilter S) :
Prop :=
∃ (L : Set (Ultrafilter S)), isMinLeftIdeal L ∧ (p ∈ L)

end Ultrafilters_as_a_semigroup

section Ultrafilters_as_topological_semigroups

-- The following proof is copied from the mathlib documentation
/-- For all `q ∈ βS`, `ultraRightMult q: βS → βS` is continuous -/
theorem rightMultUltraContinuous
{S : Type*} [Semigroup S] (q : Ultrafilter S) :
Continuous (rightMultUltra q) :=
ultrafilterBasis_is_basis.continuous_iff.2 <| Set.forall_mem_range.mpr fun A ↦
    ultrafilter_isOpen_basic { m : S | ∀ᶠ m' in q, m * m' ∈ A }

/-- This instance makes the RightTopological structure on βS "canonical" by
making it available to typeclass inference. -/
instance
{S : Type*} [Semigroup S] : RightTopological (Ultrafilter S) :=
  {
    rightCont := fun (q : Ultrafilter S) ↦ rightMultUltraContinuous q
  }

/-- For all `s ∈ S`, `ultraLeftMult (pure s): βS → βS` is continuous -/
theorem leftMultPrincipalUltraContinuous
{S : Type*} [Semigroup S] (s : S) :
Continuous (leftMultUltra (pure s)) :=
by
  simp only [ultrafilterBasis_is_basis.continuous_iff]
  intro U U_basis
  rw [ultrafilterBasis, Set.range] at U_basis
  rcases U_basis with ⟨A, U_desc⟩
  have heq : (leftMultUltra (pure s) ⁻¹' U) = {p | Set.preimage (leftMult s) A ∈ p} := by
    ext x
    rewrite [Set.preimage]
    rewrite [Set.preimage]
    rewrite [←U_desc]
    change A ∈ leftMultUltra (pure s) x ↔ {y | leftMult s y ∈ A} ∈ x
    simp only [leftMultUltra]
    simp only [leftMult]
    rewrite [ultraProductDescription (pure s) x A]
    simp only [Ultrafilter.mem_pure]
    exact Iff.rfl
  rewrite [heq]
  exact ultrafilter_isOpen_basic (Set.preimage (leftMult s) A)

theorem leftIdealInBetaSContainsMinIdempotent
{S : Type*} [Semigroup S] [Nonempty S] (L : Set (Ultrafilter S)) {hL : isLeftIdeal L} :
∃ (p : Ultrafilter S), (isMinimalUltrafilter p) ∧ (p * p = p) :=
by
  have := leftIdealContainsMinLeftIdeal (S := Ultrafilter S) L (hL := hL)
  obtain ⟨M, hM1, hM2⟩ := this
  have := leftIdealContainsIdempotent (S := Ultrafilter S) M (hL := hM1.1)
  obtain ⟨p, hp1, hp2⟩ := this
  use p
  constructor
  · unfold isMinimalUltrafilter
    use M
  · exact hp2

end Ultrafilters_as_topological_semigroups

section Ultrafilters_as_phase_space

/-- Given a semigroup `S`, `ultrafilterSystem S` is the dynamical system of `S`
acting on `βS` by left multiplication -/
def ultrafilterSystem
(S : Type*) [Semigroup S] [Nonempty S] :
DynamicalSystem S (Ultrafilter S) :=
{
  map := fun (s : S) ↦ leftMultUltra (pure s)
  mapMult := by
    intro s1 s2 p
    have := pureIsHom (S := S)
    simp only [pureIsHom (S := S) s1 s2]
    unfold leftMultUltra
    exact mul_assoc (pure s1) (pure s2) p
  mapCont := leftMultPrincipalUltraContinuous
}

/-- The subsystems of `ultrafilterSystem S` are precisely
the closed left ideals of `βS` -/
theorem ultraSubsystemIffClosedLeftIdeal
{S : Type*} [Semigroup S] [Nonempty S] (Z : Set (Ultrafilter S)) :
isNonemptyCompactT2InvariantSubset (ultrafilterSystem S) Z ↔
(IsClosed Z ∧ isLeftIdeal Z) :=
  by
    constructor
    · intro nct2IS
      unfold isNonemptyCompactT2InvariantSubset at nct2IS
      obtain ⟨hNonempty, hCompact, hT2, hInv⟩ := nct2IS
      constructor
      · exact IsCompact.isClosed hCompact
      · unfold isLeftIdeal
        constructor
        · exact hNonempty
        · have betaSisClosureOfImageOfPure : closure (Set.range pure)
            = Set.univ (α := Ultrafilter S) := by
            have := Dense.closure_eq (s := Set.range (pure : S → Ultrafilter S))
            exact this denseRange_pure
          have : ∀ (z : Ultrafilter S), z ∈ Z → (rightMultUltra z) ''
            (Set.univ (α := Ultrafilter S)) ⊆ Z := by
            intro z hz
            have := imageClosureIsClosureImage
              (rightMultUltraContinuous z) (Set.range pure)
            rw [← betaSisClosureOfImageOfPure]
            rw [this]
            have := IsClosed.closure_subset_iff (IsCompact.isClosed hCompact)
              (s := (rightMultUltra ↑z '' Set.range pure))
            apply this.mpr
            intro p hp
            unfold Set.image at hp
            obtain ⟨a, ha1, ha2⟩ := hp
            unfold rightMultUltra at ha2
            simp only [Set.mem_range] at ha1
            obtain ⟨s, hs⟩ := ha1
            rw [← hs] at ha2
            specialize hInv s
            unfold Set.MapsTo at hInv
            specialize hInv hz
            rw [←ha2]
            exact hInv
          intro p
          unfold Set.image
          simp only
          intro q hq
          obtain ⟨z, hz1, hz2⟩ := hq
          specialize this z hz1
          unfold Set.image at this
          unfold rightMultUltra at this
          apply this
          use p
          constructor
          · simp only [Set.mem_univ]
          · exact hz2
    · intro ⟨isClosed, isL⟩
      unfold isNonemptyCompactT2InvariantSubset
      constructor
      · exact isL.1
      · constructor
        · exact IsClosed.isCompact isClosed
        · constructor
          · infer_instance
          · unfold isInvariantSet
            unfold isLeftIdeal at isL
            intro s
            have := isL.2 (pure s)
            unfold ultrafilterSystem
            simp only
            exact Set.mapsTo_iff_image_subset.mpr this


/-- The minimal subsystems of `ultrafilterSystem S` are precisely
the minimal left ideals of `βS` -/
theorem ultraMinSubsystemIffMinLeftIdeal
{S : Type*} [Semigroup S] [Nonempty S] (Z : Set (Ultrafilter S)) :
isMinimalSubset (ultrafilterSystem S) Z ↔ isMinLeftIdeal Z :=
  by
    constructor
    · intro hMin
      unfold isMinLeftIdeal
      unfold isMinimalSubset at hMin
      have ZIsClosedandIsIdeal := (ultraSubsystemIffClosedLeftIdeal Z).mp hMin.1
      unfold isNonemptyCompactT2InvariantSubset at hMin
      rcases hMin with ⟨⟨ZNonempty,ZCompact,ZT2,ZInv⟩,ZMin⟩
      constructor
      · exact ZIsClosedandIsIdeal.2
      · intro M hM1 hM2
        obtain ⟨K,hK1,hK2,hK3⟩ := leftIdealContainsClosedLeftIdeal M (hL := hM1)
        obtain ⟨KNon,KComp,KT2,KInv⟩ := (ultraSubsystemIffClosedLeftIdeal K).mpr ⟨hK2,hK1⟩
        have KinZ : K ⊆ Z := by exact fun ⦃a⦄ a_1 ↦ hM2 (hK3 a_1)
        specialize ZMin K KinZ ⟨KNon,KComp,KT2,KInv⟩
        ext x
        constructor
        · intro hx
          exact hM2 hx
        · intro hx
          rw [ZMin] at hx
          exact hK3 hx
    · intro ZMinLeftIdeal
      have ZCompact := minimalLeftIdealCompact ZMinLeftIdeal
      have ZClosed := IsCompact.isClosed ZCompact
      unfold isMinLeftIdeal at ZMinLeftIdeal
      have ZSubsystem := (ultraSubsystemIffClosedLeftIdeal Z).mpr ⟨ZClosed,ZMinLeftIdeal.1⟩
      obtain ⟨ZleftIdeal,ZminProperty⟩ := ZMinLeftIdeal
      unfold isMinimalSubset
      constructor
      · exact ZSubsystem
      · intro Z1 Z1inZ hZ1
        obtain ⟨Z1Closed,Z1LeftIdeal⟩ := (ultraSubsystemIffClosedLeftIdeal Z1).mp hZ1
        exact (ZminProperty Z1 Z1LeftIdeal Z1inZ).symm

/-- An ultrafilter is minimal if and only if it is `S`-uniformly recurrent -/
theorem ultrafilterMinimalIffUnifRec
{S : Type*} [Semigroup S] [Nonempty S] (p : Ultrafilter S) :
isMinimalUltrafilter p ↔ isUniformlyRecurrent (ultrafilterSystem S) p :=
  by
    constructor
    · intro pMin
      unfold isMinimalUltrafilter at pMin
      obtain ⟨L,hL,pInL⟩ := pMin
      obtain ⟨Lpresubsys,Lmin⟩ := (ultraMinSubsystemIffMinLeftIdeal L).mpr hL
      have LCompact := minimalLeftIdealCompact hL
      have LMinSystem :=
        (minimalSubsetIffMinimalSubsystem (ultrafilterSystem S) Lpresubsys).mp ⟨Lpresubsys,Lmin⟩
      let : CompactSpace L := isCompact_iff_compactSpace.mp (Lpresubsys.2.1)
      let : Nonempty L := by
        rcases Lpresubsys.1 with ⟨y, hy⟩
        exact ⟨⟨y, hy⟩⟩
      let newsys := fromNonemptyCompactT2InvariantSubsetToSystem (ultrafilterSystem S) Lpresubsys
      have urInSubsys := minimalImpliesUniformlyRecurrent newsys (hMin := LMinSystem)
      specialize urInSubsys ⟨p,pInL⟩
      exact URInSubsystemImpliesURInSystem (ultrafilterSystem S) Lpresubsys ⟨p, pInL⟩ urInSubsys
    · intro pUR
      have pOrbClosIsMin := orbitClosureOfURPointIsMinimalSubset (ultrafilterSystem S) pUR
      let pOrbClos := orbitClosure (ultrafilterSystem S) p
      have pOrbClosIsMinIdeal := (ultraMinSubsystemIffMinLeftIdeal pOrbClos).mp pOrbClosIsMin
      have pInOrbClos : p ∈ pOrbClos := URPointBelongsToOrbitClosure (ultrafilterSystem S) pUR
      use pOrbClos

end Ultrafilters_as_phase_space

section Ultrafilters_as_acting_semigroup

/-- Given an ultrafilter `p` on a set `S` and a map `f : S → X` into a topological
space `X`, `ultraLim p f`, also written `lim_{s → p} f(s)` or `p-lim_s f(s)`, is the ultrafilter
limit of `f` along `p` -/
noncomputable
def ultraLim
{S : Type*} {X : Type*} [TopologicalSpace X]
(p : Ultrafilter S) (f : S → X) :
X :=
(Ultrafilter.extend f) p

/-- Given an ultrafilter `p` on a set `S` and a map `f : S → X` into a topological
space `X`, `ultraLim p f`, also written `lim_{s → p} f(s)` or `p-lim_s f(s)`, is the ultrafilter
limit of `f` along `p` -/
theorem ultraLimContinuousComp
{S : Type*}
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
{Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
(p : Ultrafilter S) {g : X → Y} (hgCont : Continuous g) (f : S → X) :
ultraLim p (g ∘ f) = g (ultraLim p f) := by
  unfold ultraLim
  have h1 : ∀ s : S, Ultrafilter.extend (g ∘ f) (pure s) = (g ∘ (Ultrafilter.extend f)) (pure s) :=
    by
      intro s
      simp only [ultrafilter_extend_pure, Function.comp_apply]
  have hGoal : Ultrafilter.extend (g ∘ f) = g ∘ (Ultrafilter.extend f) := by
    have h1Cont : Continuous (Ultrafilter.extend (g ∘ f)) := by
      apply continuous_ultrafilter_extend
    have h2Cont : Continuous (g ∘ (Ultrafilter.extend f)) := by
      apply Continuous.comp
      · exact hgCont
      · apply continuous_ultrafilter_extend
    have h30 : DenseRange (pure : S → Ultrafilter S) := by
      apply denseRange_pure
    let R : Set (Ultrafilter S) := Set.range pure
    have hDenseR : Dense R := by
      unfold DenseRange at h30
      simp only [R]
      exact h30
    apply Continuous.ext_on hDenseR h1Cont h2Cont
    unfold Set.EqOn
    intro p hpInR
    simp only [Set.mem_range, R] at hpInR
    rcases hpInR with ⟨s, hs⟩
    rw [<- hs]
    specialize h1 s
    exact h1
  simp [hGoal]

-- This is a lemma needed in the proof of iteratedUltraLims
lemma ultraSLeftExtension
{S} [Semigroup S] {X} [TopologicalSpace X] [CompactSpace X] [T2Space X]
(f : S → X) (s : S) :
Ultrafilter.extend (f ∘ (leftMult s)) =
  (Ultrafilter.extend f) ∘ (leftMultUltra (pure s)) :=
by
  let lhs := Ultrafilter.extend (f ∘ (leftMult s))
  let rhs := (Ultrafilter.extend f) ∘ (leftMultUltra (pure s))
  have lhs_continuous : Continuous lhs := continuous_ultrafilter_extend (f ∘ (leftMult s))
  have rhs_continuous : Continuous rhs :=
    Continuous.comp (continuous_ultrafilter_extend f) (leftMultPrincipalUltraContinuous s)
  have equal_on_dense : Set.EqOn lhs rhs (Set.range pure) := by
    rewrite [Set.EqOn]
    intro x x_in_range
    rewrite [Set.range] at x_in_range
    change ∃ y, pure y = x at x_in_range
    rcases x_in_range with ⟨t, pure_hypoth⟩
    simp only [← pure_hypoth]
    simp only [lhs, rhs]
    simp only [ultrafilter_extend_pure]
    simp only [Function.comp_apply]
    simp only [leftMultUltra]
    simp only [← pureIsHom s t]
    simp only [leftMult]
    simp only [ultrafilter_extend_pure]
  exact Continuous.ext_on denseRange_pure lhs_continuous rhs_continuous equal_on_dense

-- This is a technical lemma needed in the proof of ultra_technical_equality_cor
lemma ultraSRightExtension
{S} [Semigroup S] {X} [TopologicalSpace X] [CompactSpace X] [T2Space X]
(f : S → X) (q : Ultrafilter S) :
Ultrafilter.extend (fun (s : S) ↦ Ultrafilter.extend (f ∘ (leftMult s)) q) =
(Ultrafilter.extend f) ∘ (rightMultUltra q) := by
  let lhs := Ultrafilter.extend (fun (s : S) ↦ Ultrafilter.extend (f ∘ (leftMult s)) q)
  let rhs := (Ultrafilter.extend f) ∘ (rightMultUltra q)
  have lhs_continuous : Continuous lhs :=
    continuous_ultrafilter_extend (fun (s : S) ↦ Ultrafilter.extend (f ∘ (leftMult s)) q)
  have rhs_continuous : Continuous rhs :=
    Continuous.comp (continuous_ultrafilter_extend f) (rightMultUltraContinuous q)
  have equal_on_dense : Set.EqOn lhs rhs (Set.range pure) := by
    rewrite [Set.EqOn]
    intro x x_in_range
    rewrite [Set.range] at x_in_range
    change ∃ y, pure y = x at x_in_range
    rcases x_in_range with ⟨t, pure_hypoth⟩
    simp only [← pure_hypoth]
    simp only [lhs, rhs]
    simp only [ultrafilter_extend_pure]
    simp only [ultraSLeftExtension]
    simp only [Function.comp_apply]
    simp only [leftMultUltra]
    simp only [rightMultUltra]
  exact Continuous.ext_on denseRange_pure lhs_continuous rhs_continuous equal_on_dense

/-- The fact that `(pq)-lim f = p-lim_s (q-lim_t f(st))` -/
theorem iteratedUltraLims
{S : Type*} [Semigroup S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
(p q : Ultrafilter S) (f : S → X) :
ultraLim p (fun (s : S) ↦ ultraLim q (fun (t : S) ↦ f (s * t))) = ultraLim (p * q) f :=
by
  unfold ultraLim
  let lhs := Ultrafilter.extend (fun (s : S) ↦ Ultrafilter.extend (f ∘ (leftMult s)) q)
  let rhs := (Ultrafilter.extend f) ∘ (rightMultUltra q)
  have lhs_is_rhs_at_p : lhs p = rhs p := by
    simp only [lhs]
    simp only [rhs]
    rw [ultraSRightExtension f q]
  simp only [lhs] at lhs_is_rhs_at_p
  simp only [rhs] at lhs_is_rhs_at_p
  simp only [Function.comp_apply] at lhs_is_rhs_at_p
  simp only [rightMultUltra] at lhs_is_rhs_at_p
  exact lhs_is_rhs_at_p

/-- Given a dynamical system `dSystem : DynamicalSystem S X`, `ultraAction dSystem`
is the semigroup action of `βS` on `X` defined by `px = p-lim_s sx`. -/
noncomputable
def ultraAction
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X) :
OurSemigroupAction (Ultrafilter S) X :=
{
  map := fun (p : Ultrafilter S) (x : X) ↦ ultraLim p (fun (s : S) ↦ dSystem.map s x)
  mapMult := by
    intro p q x
    simp only [← iteratedUltraLims]
    simp only [dSystem.mapMult]
    have functionCompEquality (s : S) :
      (fun t ↦ dSystem.map s (dSystem.map t x)) =
      (dSystem.map s) ∘ (fun (t : S) ↦ dSystem.map t x) :=
      by rfl
    simp only [functionCompEquality]
    have nearlyGoal (s : S) :
    ultraLim q (dSystem.map s ∘ fun t ↦ dSystem.map t x) =
      dSystem.map s (ultraLim q fun t ↦ dSystem.map t x) :=
      by simp only [ultraLimContinuousComp q (dSystem.mapCont s) (fun (t : S) ↦ dSystem.map t x)]
    simp only [nearlyGoal]
}

/-- Ultrafilter action via diagonal system is coordinate-wise -/
lemma ultraDiagAction
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X)
(p : Ultrafilter S) (x y : X) :
(ultraAction (diagDynamicalSystem dSystem dSystem)).map p ⟨x,y⟩ =
  ⟨(ultraAction dSystem).map p x, (ultraAction dSystem).map p y⟩ := by
    let π1 : X × X → X := fun x ↦ x.1
    have π1cts : Continuous π1 := continuous_fst
    let π2 : X × X → X := fun x ↦ x.2
    have π2cts : Continuous π2 := continuous_snd
    unfold ultraAction diagDynamicalSystem
    simp only
    have firststep :=
      ultraLimContinuousComp p π1cts (fun s ↦ Prod.map (dSystem.map s) (dSystem.map s) (x, y))
    unfold Prod.map π1 at firststep
    simp only at firststep
    have : ((fun x ↦ x.1) ∘ fun s ↦ (dSystem.map s x, dSystem.map s y)) =
      fun s ↦ dSystem.map s x := by
        ext s
        simp only [Function.comp_apply]
    rw [this] at firststep
    have secondstep :=
      ultraLimContinuousComp p π2cts (fun s ↦ Prod.map (dSystem.map s) (dSystem.map s) (x, y))
    unfold Prod.map π2 at secondstep
    simp only at secondstep
    have : ((fun x ↦ x.2) ∘ fun s ↦ (dSystem.map s x, dSystem.map s y)) =
      fun s ↦ dSystem.map s y := by
        ext s
        simp only [Function.comp_apply]
    rw [this] at secondstep
    exact Prod.ext (id (Eq.symm firststep)) (id (Eq.symm secondstep))

end Ultrafilters_as_acting_semigroup

section Ultrafilter_action_theorems

variable {S : Type*} [Semigroup S] [Nonempty S]
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
variable (dSystem : DynamicalSystem S X)

/-- Given a dynamical system `dSystem : DynamicalSystem S X` and a point
`x : X`, the map `βS → X` given by `p ↦ px` is continuous -/
theorem ultraActionWithFixedxIsContinuous
(x : X) :
Continuous (fun (p : Ultrafilter S) ↦ (ultraAction dSystem).map p x) :=
by
  unfold ultraAction ultraLim
  simp only
  exact continuous_ultrafilter_extend fun s ↦ dSystem.map s x

theorem ultraFactorMap
{x : X} (xDense : Dense (orbit dSystem x)) :
isFactorMap (ultrafilterSystem S) dSystem
  (fun (p : Ultrafilter S) ↦ (ultraAction dSystem).map p x) :=
by
  constructor
  · exact ultraActionWithFixedxIsContinuous dSystem x
  · constructor
    · have ultraLiftFact := ultraLiftMapsToClosure (fun (s : S) ↦ (dSystem.map s) x)
      have denseOrbit : closure (Set.range fun s ↦ dSystem.map s x) = Set.univ (α := X) := by
        apply dense_iff_closure_eq.mp
        exact xDense
      rw [denseOrbit] at ultraLiftFact
      exact Set.range_eq_univ.mp ultraLiftFact
    · unfold isEquivariant
      intro s
      ext p
      unfold ultrafilterSystem
      simp only
      have : ((fun p ↦ (ultraAction dSystem).map p x) ∘ leftMultUltra (pure s)) p =
        (ultraAction dSystem).map ((pure s) * p) x := by
          exact Function.comp_apply
      rw [this]
      rw [(ultraAction dSystem).mapMult]
      have : (ultraAction dSystem).map (pure s) = dSystem.map s := by
        unfold ultraAction ultraLim
        simp only [ultrafilter_extend_pure]
      rw [this]
      simp only [Function.comp_apply]

/-- Given a dynamical system `dSystem : DynamicalSystem S X`, a point
`x : X`, and `p : βS`, the point `px` belongs to the orbit closure of `x` -/
theorem ultraActionInOrbitClosure
(p : Ultrafilter S) (x : X) :
(ultraAction dSystem).map p x ∈ orbitClosure dSystem x :=
by
  unfold ultraAction ultraLim
  simp only
  have ultraLiftRange := ultraLiftMapsToClosure (fun s ↦ dSystem.map s x)
  have : Set.range (Ultrafilter.extend fun s ↦ dSystem.map s x) ⊆
    closure (Set.range fun s ↦ dSystem.map s x) := by
    exact subset_of_subset_of_eq (fun ⦃a⦄ a_1 ↦ a_1) ultraLiftRange
  exact (Set.range_subset_iff).mp this p

/-- Given a factor map `π : X → Y` of dynamical systems and `p : βS`,
the action of `p` intertwines with the factor map: `p ∘ π = π ∘ p` -/
theorem ultraActionIntertwinesWithFactor
{Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemY : DynamicalSystem S Y)
{π : X → Y} (hπ : isFactorMap dSystem dSystemY π)
(p : Ultrafilter S) :
((ultraAction dSystemY).map p) ∘ π = π ∘ (ultraAction dSystem).map p := by
  ext x
  simp only [Function.comp_apply]
  simp only [ultraAction]
  unfold isFactorMap at hπ
  rcases hπ with ⟨hπ1, hπ2, hπ3⟩
  have h1 : (fun s ↦ dSystemY.map s (π x)) = fun s ↦ π (dSystem.map s x) := by
    ext s
    unfold isEquivariant at hπ3
    specialize hπ3 s
    have hπ3New : (dSystemY.map s ∘ π) x = (π ∘ dSystem.map s) x := by
      apply congrFun hπ3
    exact hπ3New
  rw [h1]
  apply ultraLimContinuousComp
  · exact hπ1

/-- Given a dynamical system `dSystem : DynamicalSystem S X`, a point
`x : X`, an open set `U ⊆ X`, and `p : βS`, if `px ∈ U`, then `R(x,U) ∈ p` -/
theorem visitTimeSetBelongsToUltrafilter
(x : X) (U : Set X) {hU : IsOpen U} (p : Ultrafilter S) :
(ultraAction dSystem).map p x ∈ U → visitTimeSet dSystem x U ∈ p :=
by
  intro pxInU
  unfold ultraAction ultraLim at pxInU
  simp only at pxInU
  let c := Ultrafilter.extend (fun s ↦ dSystem.map s x) p
  have defofc : c = Ultrafilter.extend (fun s ↦ dSystem.map s x) p := by trivial
  have UinNhdsc : U ∈ nhds c := by
    exact IsOpen.mem_nhds hU pxInU
  have ultraImageContainsNbhsOfC :=
    (ultrafilter_extend_eq_iff (f := (fun s ↦ dSystem.map s x)) (b := p) (c := c)).mp defofc
  have : U ∈ (Ultrafilter.map (fun s ↦ dSystem.map s x) p) := by
    exact Ultrafilter.mem_map.mpr (ultraImageContainsNbhsOfC UinNhdsc)
  unfold visitTimeSet
  exact this

/-- Given a dynamical system `dSystem : DynamicalSystem S X`, a point
`x : X`, a set `U ⊆ X`, and `p : βS`, if `R(x,U) ∈ p`, then `px ∈ closure U` -/
theorem visitTimeSetInUltraImpliesUltraActInClosure
(x : X) (U : Set X) (p : Ultrafilter S) :
visitTimeSet dSystem x U ∈ p → (ultraAction dSystem).map p x ∈ closure U :=
by
  contrapose
  intro pxNotInClosure
  let V := Set.compl (closure U)
  have UcapVempty : U ∩ V = ∅ := by
    unfold V
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hx
    apply subset_closure at hx
    exact (Set.notMem_compl_iff).mpr hx
  have pxInV : (ultraAction dSystem).map p x ∈ V := by
    exact Set.mem_preimage.mp pxNotInClosure
  have VIsOpen : IsOpen V := by
    unfold V
    have := isClosed_closure (s := U)
    exact IsClosed.isOpen_compl
  have visitTimeVinp := visitTimeSetBelongsToUltrafilter dSystem x V p (hU := VIsOpen) pxInV
  have : (visitTimeSet dSystem x V) ∩ (visitTimeSet dSystem x U) = ∅ := by
    by_contra h
    apply Set.nonempty_iff_ne_empty.mpr at h
    obtain ⟨s, hs1, hs2⟩ := h
    unfold visitTimeSet at hs1
    simp only [Set.mem_preimage] at hs1
    unfold visitTimeSet at hs2
    simp only [Set.mem_preimage] at hs2
    have UcapVnonempty : (U ∩ V).Nonempty := by
      use dSystem.map s x
      exact ⟨hs2,hs1⟩
    rw [UcapVempty] at UcapVnonempty
    exact Set.not_nonempty_empty UcapVnonempty
  have visitTimeUnotinp : visitTimeSet dSystem x U ∉ p := by
    by_contra h
    have visitTimeOfIntersection : visitTimeSet dSystem x (U ∩ V) ∈ p := by
      have : visitTimeSet dSystem x (U ∩ V) =
        visitTimeSet dSystem x U ∩ visitTimeSet dSystem x V := by
          exact Set.Subset.antisymm (fun ⦃a⦄ a_1 ↦ a_1) fun ⦃a⦄ a_1 ↦ a_1
      rw [this]
      apply Filter.inter_mem_iff.mpr
      exact ⟨h,visitTimeVinp⟩
    rw [UcapVempty] at visitTimeOfIntersection
    have emptyVisits : visitTimeSet dSystem x (∅ : Set X) = (∅ : Set S) := by
      unfold visitTimeSet
      exact Set.preimage_empty
    rw [emptyVisits] at visitTimeOfIntersection
    exact Ultrafilter.empty_notMem visitTimeOfIntersection
  exact visitTimeUnotinp

/-- Given a minimal dynamical system `dSystem : DynamicalSystem S X`,
a minimal left ideal `L ⊆ βS`, and points `x, y ∈ X`, there exists `p ∈ L`
such that `px = y` -/
theorem minLeftIdealSurjectsOntoMinSystem
(hdSystemMin : isMinimalSystem dSystem)
{L : Set (Ultrafilter S)} (hLMin : isMinLeftIdeal L)
(x y : X) :
∃ p ∈ L, (ultraAction dSystem).map p x = y :=
by
  let π := fun p ↦ (ultraAction dSystem).map p x
  have isultrafactormap : isFactorMap (ultrafilterSystem S) dSystem π :=
    ultraFactorMap dSystem ((minimalIffDenseOrbits dSystem).mp hdSystemMin x)
  have LisMinSubset := (ultraMinSubsystemIffMinLeftIdeal L).mpr hLMin
  have imageofLIsInvSet := imageOfSubsystemIsSubsystem (ultrafilterSystem S)
    dSystem π L (hA := LisMinSubset.1) (hEqui := isultrafactormap.2.2) (hπ := isultrafactormap.1)
  have imageofLIsUniv := hdSystemMin (π '' L) imageofLIsInvSet
  have yInUniv : y ∈ Set.univ := Set.mem_univ y
  rw [←imageofLIsUniv] at yInUniv
  simp only [Set.mem_image] at yInUniv
  exact yInUniv

/-- Given a minimal dynamical system `dSystem : DynamicalSystem S X`,
a minimal left ideal `L ⊆ βS`, and a point `x ∈ X`, there exists an idempotent
ultrafilter `p ∈ L` such that `px = x` -/
theorem everyPointInMinFixedBySomeIdempotentUltrafilter
(hdSystemMin : isMinimalSystem dSystem)
{L : Set (Ultrafilter S)} (hLMin : isMinLeftIdeal L)
(x : X) :
∃ p ∈ L, (p * p = p) ∧ (ultraAction dSystem).map p x = x :=
by
  let A : Set (Ultrafilter S) := { q : Ultrafilter S | (ultraAction dSystem).map q x = x}
  have AcapLisNonempty : (A ∩ L).Nonempty := by
    obtain ⟨p,hp1,hp2⟩ := minLeftIdealSurjectsOntoMinSystem dSystem hdSystemMin hLMin x x
    use p
    exact ⟨hp2,hp1⟩
  have AcapLisCompact : IsCompact (A ∩ L) := by
    have AisClosed : IsClosed A := by
      let f := fun p ↦ (ultraAction dSystem).map p x
      have fcts : Continuous f := ultraActionWithFixedxIsContinuous dSystem x
      have descOfA : A = Set.preimage f (Set.singleton x) := by
        exact Eq.symm (Set.Subset.antisymm (fun ⦃a⦄ a_1 ↦ a_1) fun ⦃a⦄ a_1 ↦ a_1)
      rw [descOfA]
      have singleIsClosed : IsClosed (Set.singleton x) := isClosed_singleton
      exact IsClosed.preimage fcts singleIsClosed
    have := minimalLeftIdealCompact hLMin
    exact IsCompact.inter_left this AisClosed
  have AcapLisSubsemi : isSubsemigroup (A ∩ L) := by
    intro p hp q hq
    constructor
    · unfold A
      simp only [Set.mem_ofPred_eq]
      rw [(ultraAction dSystem).mapMult]
      rw [hq.1]
      exact hp.1
    · unfold isMinLeftIdeal isLeftIdeal at hLMin
      have leftMultImageInL := hLMin.1.2 p
      have imageofPtInSet := Set.mem_image_of_mem (fun x ↦ p * x) hq.2
      exact Set.mem_preimage.mp (leftMultImageInL imageofPtInSet)
  have existsIdemp := compactSubsemigroupContainsIdempotent (A ∩ L)
    (hTnonempty := AcapLisNonempty) (hTcompact := AcapLisCompact) (hTsemi := AcapLisSubsemi)
  obtain ⟨p, hp1, hp2⟩ := existsIdemp
  use p
  refine ⟨hp1.2,hp2,hp1.1⟩

/-- Given a dynamical system `dSystem : DynamicalSystem S X`, `p ∈ βS`, and a
point `x ∈ X`, the points `x` and `px` are proximal -/
theorem pointAndUltraImageAreProximal
(x : X) {p : Ultrafilter S} (pIdempotent : p * p = p) :
proximal dSystem x ((ultraAction dSystem).map p x) :=
by
  unfold proximal
  let px := (ultraAction dSystem).map p x
  let diagOrb := orbit (diagDynamicalSystem dSystem dSystem) ⟨x,px⟩
  let diagOrbClos := orbitClosure (diagDynamicalSystem dSystem dSystem) ⟨x,px⟩
  have p_xpxIspxpx :
    (ultraAction (diagDynamicalSystem dSystem dSystem)).map p ⟨x,px⟩ = ⟨px,px⟩ := by
    rw [ultraDiagAction dSystem p x px]
    unfold px
    rw [←(ultraAction dSystem).mapMult]
    rw [pIdempotent]
  have pxpxindiag : ⟨px,px⟩ ∈ Set.diagonal X := by trivial
  have ultraActinOrbClos :
    (ultraAction (diagDynamicalSystem dSystem dSystem)).map p ⟨x,px⟩ ∈ diagOrbClos := by
      exact ultraActionInOrbitClosure (diagDynamicalSystem dSystem dSystem) p ⟨x,px⟩
  have pxpxInOrbClosxpx : ⟨px,px⟩ ∈ diagOrbClos := by
    rw [p_xpxIspxpx] at ultraActinOrbClos
    exact ultraActinOrbClos
  intro α hα
  obtain ⟨U,hU1,hU2,hU3⟩ := mem_nhdsSet_iff_exists.mp hα
  have diagOrbClosHitsU : (diagOrbClos ∩ U).Nonempty := by
    use ⟨px,px⟩
    exact ⟨pxpxInOrbClosxpx, hU2 pxpxindiag⟩
  have diagOrbHitsU : (diagOrb ∩ U).Nonempty := by
    exact (closure_inter_open_nonempty_iff hU1).mp diagOrbClosHitsU
  obtain ⟨y,hy1,hy2⟩ := diagOrbHitsU
  unfold diagOrb orbit diagDynamicalSystem at hy1
  simp only [Prod.map_apply, Set.mem_range] at hy1
  obtain ⟨s,hs⟩ := hy1
  rw [←hs] at hy2
  use s
  exact hU3 hy2

/-- Given a dynamical system `dSystem : DynamicalSystem S X`, a minimal ultrafilter
`p ∈ βS`, and a point `x ∈ X`, the point `px` is `S`-uniformly recurrent -/
theorem minUltraImageIsUniformlyRecurrent
(x : X) {p : Ultrafilter S} (hp : isMinimalUltrafilter p) :
isUniformlyRecurrent dSystem ((ultraAction dSystem).map p x) :=
by
  unfold isUniformlyRecurrent
  intro U hU
  let px := (ultraAction dSystem).map p x
  have hU2 : U ∈ nhdsSet {px} := by
    rw [nhdsSet_singleton]
    exact hU
  obtain ⟨V, VOpen, Vhaspx, closureVInU⟩ :=
    IsCompact.exists_isOpen_closure_subset (isCompact_singleton (x := px)) hU2
  let RxV := visitTimeSet dSystem x V
  let barRxV := {q : Ultrafilter S | RxV ∈ q}
  have barRxVisnhdsp : barRxV ∈ nhds p := by
    apply mem_nhds_iff.mpr
    use barRxV
    refine ⟨by trivial, ?_, ?_⟩
    · exact ultrafilter_isOpen_basic RxV
    · simp only [Set.singleton_subset_iff] at Vhaspx
      unfold px at Vhaspx
      exact visitTimeSetBelongsToUltrafilter dSystem x V (hU := VOpen) p Vhaspx
  have visitTimeContain :
    visitTimeSet (ultrafilterSystem S) p barRxV ⊆ visitTimeSet dSystem px U := by
      intro s hs
      unfold visitTimeSet ultrafilterSystem leftMultUltra barRxV at hs
      simp only [Set.preimage_ofPred_eq, Set.mem_ofPred_eq] at hs
      have := visitTimeSetInUltraImpliesUltraActInClosure dSystem x V (pure s * p) hs
      rw [(ultraAction dSystem).mapMult] at this
      change (ultraAction dSystem).map (pure s) px ∈ closure V at this
      unfold ultraAction ultraLim at this
      simp only at this
      rw [ultrafilter_extend_pure] at this
      exact closureVInU this
  have pUR := (ultrafilterMinimalIffUnifRec p).mp hp
  have lhsSynd := pUR barRxV barRxVisnhdsp
  exact syndeticIsMonotone lhsSynd visitTimeContain

/-- Given a dynamical minimal system `dSystem : DynamicalSystem S X`, a minimal
left ideal `L ⊆ βS`, and an ultrafilter `p ∈ L`, if `px = x`, then there exists
`q ∈ L` such that `pq` is idempotent and `qx = x` -/
theorem idempotentProductLifting
(x : X) {L : Set (Ultrafilter S)} (hLMin : isMinLeftIdeal L)
{p : Ultrafilter S} (hpL : p ∈ L) (hpFix : (ultraAction dSystem).map p x = x) :
∃ q ∈ L, ((p * q) * (p * q) = p * q) ∧ (ultraAction dSystem).map q x = x :=
by
  have LisMinimalSubset := (ultraMinSubsystemIffMinLeftIdeal L).mpr hLMin
  let Lsystem :=
    fromNonemptyCompactT2InvariantSubsetToSystem (ultrafilterSystem S) LisMinimalSubset.1
  let : CompactSpace ↑L := isCompact_iff_compactSpace.mp (LisMinimalSubset.1.2.1)
  let : Nonempty ↑L := (fun ⟨y, hy⟩ ↦ ⟨⟨y, hy⟩⟩) LisMinimalSubset.1.1
  have LsystemMin : isMinimalSystem Lsystem :=
    (minimalSubsetIffMinimalSubsystem (ultrafilterSystem S) LisMinimalSubset.1).mp LisMinimalSubset
  obtain ⟨u,hu1,hu2,hu3⟩ :=
    everyPointInMinFixedBySomeIdempotentUltrafilter Lsystem LsystemMin hLMin ⟨p,hpL⟩
  obtain ⟨q,hq1,hq2⟩ := minLeftIdealSurjectsOntoMinSystem Lsystem LsystemMin hLMin ⟨p,hpL⟩ ⟨u,hu1⟩
  obtain ⟨r,hr1,hr2⟩ := minLeftIdealSurjectsOntoMinSystem Lsystem LsystemMin hLMin ⟨q,hq1⟩ ⟨u,hu1⟩
  -- `L` is a left ideal, so it is closed under left multiplication by principal ultrafilters
  have hmulL : ∀ (s : S) {y : Ultrafilter S}, y ∈ L → pure s * y ∈ L :=
    fun s _ hy ↦ hLMin.1.2 (pure s) ⟨_, hy, rfl⟩
  -- the coercion from type L to type Ultrafilter S is continuous, hence commutes with
  -- Ultrafilter.extend; "hprojp" and "hprojq" are the two instances of this that we need
  have hproj (f : S → ↥L) (ℓ : Ultrafilter S) :
      ((Ultrafilter.extend f ℓ : ↥L) : Ultrafilter S)
        = Ultrafilter.extend (fun s ↦ ((f s : ↥L) : Ultrafilter S)) ℓ := by
    have heq : (fun y : ↥L ↦ (y : Ultrafilter S)) ∘ Ultrafilter.extend f
        = Ultrafilter.extend ((fun y : ↥L ↦ (y : Ultrafilter S)) ∘ f) := by
      refine Continuous.ext_on denseRange_pure
        (continuous_subtype_val.comp (continuous_ultrafilter_extend f))
        (continuous_ultrafilter_extend _) ?_
      rintro z ⟨s, rfl⟩
      simp only [Function.comp_def, ultrafilter_extend_pure]
    exact congrFun heq ℓ
  have hprojp (ℓ : Ultrafilter S) :
      ((Ultrafilter.extend (fun s ↦ (⟨pure s * p, hmulL s hpL⟩ : ↥L)) ℓ : ↥L) : Ultrafilter S)
        = Ultrafilter.extend (fun s ↦ pure s * p) ℓ := hproj _ ℓ
  have hprojq (ℓ : Ultrafilter S) :
      ((Ultrafilter.extend (fun s ↦ (⟨pure s * q, hmulL s hq1⟩ : ↥L)) ℓ : ↥L) : Ultrafilter S)
        = Ultrafilter.extend (fun s ↦ pure s * q) ℓ := hproj _ ℓ
  -- this equality holds in subtype form in hu3. the following gets the projection
  have upp : u * p = p := by
    unfold ultraAction Lsystem ultraLim
      fromNonemptyCompactT2InvariantSubsetToSystem ultrafilterSystem leftMultUltra at hu3
    simp only at hu3
    unfold Set.MapsTo.restrict Subtype.map at hu3
    simp only at hu3
    have hu3' := congrArg (fun x : L ↦ (x : Ultrafilter S)) hu3
    simp only at hu3'
    have hu4 : Ultrafilter.extend (fun s ↦ pure s * p) u = p := by
      rw [← hprojp u]
      exact hu3'
    have := rightMultUltraContinuous p
    have := ultraLimContinuousComp u (rightMultUltraContinuous p) pure
    unfold ultraLim rightMultUltra Function.comp at this
    simp only at this
    rw [this] at hu4
    simp only [ultrafilter_extend_id, id_eq] at hu4
    exact hu4
  -- this equality holds in subtype form in hq2. the following gets the projection
  have qpu : q * p = u := by
    unfold ultraAction Lsystem ultraLim
      fromNonemptyCompactT2InvariantSubsetToSystem ultrafilterSystem leftMultUltra at hq2
    simp only at hq2
    unfold Set.MapsTo.restrict Subtype.map at hq2
    simp only at hq2
    have hq2' := congrArg (fun x : L ↦ (x : Ultrafilter S)) hq2
    simp only at hq2'
    have hq4 : Ultrafilter.extend (fun s ↦ pure s * p) q = u := by
      rw [← hprojp q]
      exact hq2'
    have := rightMultUltraContinuous p
    have := ultraLimContinuousComp q (rightMultUltraContinuous p) pure
    unfold ultraLim rightMultUltra Function.comp at this
    simp only at this
    rw [this] at hq4
    simp only [ultrafilter_extend_id, id_eq] at hq4
    exact hq4
  -- this equality holds in subtype form in hr2. the following gets the projection
  have rqu : r * q = u := by
    unfold ultraAction Lsystem ultraLim
      fromNonemptyCompactT2InvariantSubsetToSystem ultrafilterSystem leftMultUltra at hr2
    simp only at hr2
    unfold Set.MapsTo.restrict Subtype.map at hr2
    simp only at hr2
    have hr2' := congrArg (fun x : L ↦ (x : Ultrafilter S)) hr2
    simp only at hr2'
    have hr4 : Ultrafilter.extend (fun s ↦ pure s * q) r = u := by
      rw [← hprojq r]
      exact hr2'
    have := rightMultUltraContinuous q
    have := ultraLimContinuousComp r (rightMultUltraContinuous q) pure
    unfold ultraLim rightMultUltra Function.comp at this
    simp only at this
    rw [this] at hr4
    simp only [ultrafilter_extend_id, id_eq] at hr4
    exact hr4
  let qx := (ultraAction dSystem).map q x
  let q_px := (ultraAction dSystem).map q ((ultraAction dSystem).map p x)
  let qp_x := (ultraAction dSystem).map (q * p) x
  let ux := (ultraAction dSystem).map u x
  let u_px := (ultraAction dSystem).map u ((ultraAction dSystem).map p x)
  let up_x := (ultraAction dSystem).map (u * p) x
  let px := (ultraAction dSystem).map p x
  have qxx : qx = x :=
    calc
      qx = q_px := by unfold q_px ; rw [hpFix]
      _ = qp_x := by unfold q_px ; rw [←(ultraAction dSystem).mapMult]
      _ = ux := by unfold qp_x ; rw [qpu]
      _ = u_px := by unfold ux ; unfold u_px ; rw [hpFix]
      _ = up_x := by unfold u_px ; rw [←(ultraAction dSystem).mapMult]
      _ = px := by unfold up_x ; rw [upp]
      _ = x := by unfold px ; rw [hpFix]
  have rur := minimalIdempotentsAreLeftIdentites
    L (hL := hLMin) u (huL := hu1) (huIdempotent := hu2) r hr1
  have pqu : p * q = u :=
    calc
      p * q = (u * p) * q := by rw [upp]
      _ = u * (p * q) := by exact mul_assoc u p q
      _ = (r * q) * (p * q) := by rw [rqu]
      _ = (r * (q * p)) * q := by rw [←mul_assoc (r * q) p q] ; rw [←mul_assoc r q p]
      _ = (r * u) * q := by rw [qpu]
      _ = r * q := by rw [rur]
      _ = u := by rw [rqu]
  use q
  refine ⟨hq1, by rw [pqu] ; exact hu2, qxx⟩

end Ultrafilter_action_theorems

section Semisimplicity_and_equicontinuity

variable {S : Type*} [Semigroup S] [Nonempty S]
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
variable (dSystem : DynamicalSystem S X)

/-- A system is semisimple if all points are uniformly recurrent -/
def isSemisimpleSystem
(dSystem : DynamicalSystem S X) :
Prop :=
∀ (x : X), isUniformlyRecurrent dSystem x

/-- A distal system is semisimple.
Let `p` be any minimal idempotent ultrafilter on `S`.  The point `p x` is uniformly recurrent
and proximal to `x`, so distality forces `p x = x` and `x` is uniformly recurrent. -/
lemma distalImpliesSemisimple
{dSys : DynamicalSystem S X} (hdistal : isDistalSystem dSys) :
isSemisimpleSystem dSys := by
  intro x
  obtain ⟨p, hpmin, hpidem⟩ :=
    leftIdealInBetaSContainsMinIdempotent (S := S) Set.univ
      (hL := ⟨Set.univ_nonempty, fun _ ↦ Set.subset_univ _⟩)
  have hprox := pointAndUltraImageAreProximal dSys x hpidem
  have hur := minUltraImageIsUniformlyRecurrent dSys x hpmin
  rwa [← hdistal x _ hprox] at hur

/-- A system `X` is distal iff the system `X^2` is semisimple -/
theorem distalIffDiagSemisimple
(dSystem : DynamicalSystem S X) :
isSemisimpleSystem (diagDynamicalSystem dSystem dSystem) ↔ isDistalSystem dSystem := by
  constructor
  · -- a proximal pair `(x,y)` is uniformly recurrent, so its orbit closure is minimal; it
    -- meets the diagonal at some `w`, and then `(x,y)` lies in the orbit closure of `w ∈ Δ`
    intro hss x y hprox
    obtain ⟨w, hwdiag, hwK⟩ := proximalOrbitClosureMeetsDiagonal hprox
    have hUR : isUniformlyRecurrent (diagDynamicalSystem dSystem dSystem) (x, y) := hss (x, y)
    have hmin := orbitClosureOfURPointIsMinimalSubset (diagDynamicalSystem dSystem dSystem) hUR
    have hwsub : orbitClosure (diagDynamicalSystem dSystem dSystem) w
        ⊆ orbitClosure (diagDynamicalSystem dSystem dSystem) (x, y) := by
      refine closure_minimal ?_ isClosed_closure
      rintro v ⟨s, rfl⟩
      exact hmin.1.2.2.2 s hwK
    have hKeq := hmin.2 _ hwsub
      (orbitClosureIsNonemptyCompactT2InvariantSubset (diagDynamicalSystem dSystem dSystem) w)
    have hxyK := URPointBelongsToOrbitClosure (diagDynamicalSystem dSystem dSystem) hUR
    rw [hKeq] at hxyK
    have hdiagsub : orbitClosure (diagDynamicalSystem dSystem dSystem) w ⊆ Set.diagonal X := by
      refine closure_minimal ?_ isClosed_diagonal
      rintro v ⟨s, rfl⟩
      have hw12 : w.1 = w.2 := hwdiag
      change dSystem.map s w.1 = dSystem.map s w.2
      rw [hw12]
    exact hdiagsub hxyK
  · intro hdistal
    exact distalImpliesSemisimple (diagOfDistalIsDistal hdistal)

/-- If `S` acts on an `S`-system surjectively and that system is equicontinuous,
then it is semisimple -/
theorem equiSurjectiveSystemsAreSemisimple
(dSystem : DynamicalSystem S X) (hSurject : isSurjectiveSystem dSystem) :
isEquicontinuousSystem dSystem → isSemisimpleSystem dSystem := by
  classical
  intro hequi x U hU
  obtain ⟨W, hWU, hWopen, hxW⟩ := mem_nhds_iff.mp hU
  refine syndeticIsMonotone (A := visitTimeSet dSystem x W) ?_ (fun t ht ↦ hWU ht)
  obtain ⟨α, hαopen, hαdiag, hαprop⟩ := existsDiagonalNbhdForcingMembership hWopen hxW
  obtain ⟨α₁, hα₁open, hα₁diag, hα₁symm, hα₁cube⟩ :=
    existsSymmetricCubeNbhdOfDiagonal hαopen hαdiag
  obtain ⟨γ₀, hγ₀open, hγ₀diag, hγ₀prop⟩ := hequi α₁ hα₁open hα₁diag
  -- cover `X` by sets small with respect to `γ₀ ∩ α₁`
  obtain ⟨F, V, hcover, hmemV, hVγ⟩ :=
    existsFiniteCoverBySmallSets (hγ₀open.inter hα₁open) (fun p hp ↦ ⟨hγ₀diag hp, hα₁diag hp⟩)
  -- `φ s y` names the piece of the cover that `s y` lands in
  choose φ hφF hφV using fun (s : S) (y : ↥F) ↦ hcover (dSystem.map s (y : X))
  set C : (↥F → ↥F) → Set S := fun v ↦ {s : S | ∀ y : ↥F, φ s y = (v y : X)} with hC
  have hCcover : ∀ s : S, ∃ v, s ∈ C v :=
    fun s ↦ ⟨fun y ↦ ⟨φ s y, hφF s y⟩, fun _ ↦ rfl⟩
  refine syndeticIsMonotone (unionOfRightQuotientSetsIsSyndeticOfFintype C hCcover) ?_
  rintro t ht
  simp only [Set.mem_iUnion] at ht
  obtain ⟨v, r, hrC, htrC⟩ := ht
  -- write `x = r y₀` and find the piece `V y₁` containing `y₀`
  obtain ⟨y₀, hy₀⟩ := hSurject r x
  obtain ⟨y₁, hy₁F, hy₁⟩ := hcover y₀
  have hpair : (y₀, (y₁ : X)) ∈ γ₀ := (hVγ y₁ ⟨hy₁, hmemV y₁⟩).1
  -- three `α₁`-steps from `r y₀` to `(t r) y₀`
  have hstep1 : (dSystem.map r y₀, dSystem.map r y₁) ∈ α₁ :=
    hγ₀prop r ⟨(y₀, (y₁ : X)), hpair, rfl⟩
  have hstep3 : (dSystem.map (t * r) y₀, dSystem.map (t * r) y₁) ∈ α₁ :=
    hγ₀prop (t * r) ⟨(y₀, (y₁ : X)), hpair, rfl⟩
  have hstep2 : (dSystem.map r y₁, dSystem.map (t * r) y₁) ∈ α₁ := by
    refine (hVγ ((v ⟨y₁, hy₁F⟩ : ↥F) : X) ⟨?_, ?_⟩).2
    · have h := hφV r ⟨y₁, hy₁F⟩
      rwa [hrC ⟨y₁, hy₁F⟩] at h
    · have h := hφV (t * r) ⟨y₁, hy₁F⟩
      rwa [htrC ⟨y₁, hy₁F⟩] at h
  have hcube := hα₁cube _ _ _ _ hstep1 hstep2
    (hα₁symm _ _ hstep3)
  rw [hy₀] at hcube
  rw [dSystem.mapMult, hy₀] at hcube
  exact hαprop _ hcube

/-- If a system is backward equicontinuous, then it is semisimple -/
theorem backEquiSystemsAreSemisimple
(dSystem : DynamicalSystem S X) :
isBackwardEquicontinuousSystem dSystem → isSemisimpleSystem dSystem := by
  classical
  intro hback x U hU
  obtain ⟨W, hWU, hWopen, hxW⟩ := mem_nhds_iff.mp hU
  refine syndeticIsMonotone (A := visitTimeSet dSystem x W) ?_ (fun t ht ↦ hWU ht)
  obtain ⟨α, hαopen, hαdiag, hαprop⟩ := existsDiagonalNbhdForcingMembership hWopen hxW
  obtain ⟨γ, hγopen, hγdiag, hγprop⟩ := hback α hαopen hαdiag
  -- `β = (α ∩ γ) ∪ S⁻¹γ` contains the open set `α ∩ γ ⊇ Δ`, sits inside `α`,
  -- and satisfies `S⁻¹β ⊆ β`
  set β : Set (X × X) :=
    (α ∩ γ) ∪ inverseSetOrbit (diagDynamicalSystem dSystem dSystem) γ with hβdef
  have hβα : β ⊆ α := by
    rintro p (hp | hp)
    · exact hp.1
    · simp only [inverseSetOrbit, Set.mem_iUnion, Set.mem_preimage] at hp
      obtain ⟨t, ht⟩ := hp
      exact hγprop t ht
  have hβinv : ∀ (t : S) (p : X × X),
      (diagDynamicalSystem dSystem dSystem).map t p ∈ β → p ∈ β := by
    intro t p hp
    refine Set.mem_union_right _ ?_
    simp only [inverseSetOrbit, Set.mem_iUnion, Set.mem_preimage]
    rcases hp with hp | hp
    · exact ⟨t, hp.2⟩
    · simp only [inverseSetOrbit, Set.mem_iUnion, Set.mem_preimage] at hp
      obtain ⟨r, hr⟩ := hp
      refine ⟨r * t, ?_⟩
      rw [(diagDynamicalSystem dSystem dSystem).mapMult]
      exact hr
  -- cover `X` by sets small with respect to the open set `α ∩ γ`
  obtain ⟨F, V, hcover, hmemV, hVβ⟩ :=
    existsFiniteCoverBySmallSets (hαopen.inter hγopen) (fun p hp ↦ ⟨hαdiag hp, hγdiag hp⟩)
  set C : ↥F → Set S := fun y ↦ {t : S | dSystem.map t x ∈ V (y : X)} with hC
  have hCcover : ∀ t : S, ∃ y : ↥F, t ∈ C y := by
    intro t
    obtain ⟨y, hyF, hy⟩ := hcover (dSystem.map t x)
    exact ⟨⟨y, hyF⟩, hy⟩
  refine syndeticIsMonotone (unionOfLeftQuotientSetsIsSyndeticOfFintype C hCcover) ?_
  rintro t ht
  simp only [Set.mem_iUnion] at ht
  obtain ⟨y, r, hrC, hrtC⟩ := ht
  have hmem : ((diagDynamicalSystem dSystem dSystem).map r) (x, dSystem.map t x) ∈ β := by
    refine Set.mem_union_left _ (hVβ (y : X) ⟨hrC, ?_⟩)
    change dSystem.map r (dSystem.map t x) ∈ V (y : X)
    rw [← dSystem.mapMult]
    exact hrtC
  exact hαprop _ (hβα (hβinv r _ hmem))



/-- If the square of a system is semisimple, then the forward and backward regionally
proximal relations coincide.  This is the case `A = B = S` of
`forwardBackwardSetOrbClosCoincideInBronsSys`. -/
lemma RPEqRPMOfDiagSemisimple
{dSys : DynamicalSystem S X}
(hss : isSemisimpleSystem (diagDynamicalSystem dSys dSys)) :
RP dSys = RPM dSys := by
  have hDense :
      Dense {(x, y) : X × X | isUniformlyRecurrent (diagDynamicalSystem dSys dSys) (x, y)} := by
    rintro ⟨x, y⟩
    exact subset_closure (hss (x, y))
  have hUnivThick : isThick (Set.univ : Set S) :=
    fun _ _ ↦ ⟨Classical.arbitrary S, Set.subset_univ _⟩
  -- along all of `S`, the orbit (resp. inverse orbit) of a set is the plain orbit
  have hfwd : ∀ W : Set (X × X),
      setOrbitAlongASet (diagDynamicalSystem dSys dSys) Set.univ W
        = setOrbit (diagDynamicalSystem dSys dSys) W := by
    intro W
    apply Set.Subset.antisymm
    · intro w hw
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hw
      obtain ⟨z, hz, hzw⟩ := hs
      exact ⟨((s : S), ⟨z, hz⟩), hzw⟩
    · intro w hw
      obtain ⟨⟨s, z⟩, hzw⟩ := hw
      exact Set.mem_iUnion.mpr ⟨⟨s, Set.mem_univ s⟩, ⟨(z : X × X), z.2, hzw⟩⟩
  have hbwd : ∀ W : Set (X × X),
      inverseSetOrbitAlongASet (diagDynamicalSystem dSys dSys) Set.univ W
        = inverseSetOrbit (diagDynamicalSystem dSys dSys) W := by
    intro W
    apply Set.Subset.antisymm
    · intro w hw
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hw
      exact Set.mem_iUnion.mpr ⟨(s : S), hs⟩
    · intro w hw
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hw
      exact Set.mem_iUnion.mpr ⟨⟨s, Set.mem_univ s⟩, hs⟩
  have hkey : ∀ W : Set (X × X), IsOpen W →
      setOrbitClosure (diagDynamicalSystem dSys dSys) W
        = closure (inverseSetOrbit (diagDynamicalSystem dSys dSys) W) := by
    intro W hW
    have h := forwardBackwardSetOrbClosCoincideInBronsSys dSys hDense Set.univ Set.univ
      hUnivThick hUnivThick W hW
    rwa [hfwd W, hbwd W] at h
  -- neighbourhoods of the diagonal may be shrunk to open ones
  have hinterior : ∀ α ∈ nhdsSet (Set.diagonal X), interior α ∈ nhdsSet (Set.diagonal X) := by
    intro α hα
    obtain ⟨V, hVα, hVopen, hVdiag⟩ := mem_nhdsSet.mp hα
    exact mem_nhdsSet.mpr ⟨interior α, subset_rfl, isOpen_interior,
      hVdiag.trans (interior_maximal hVα hVopen)⟩
  apply Set.Subset.antisymm
  · intro z hz
    simp only [RP, Set.mem_iInter] at hz
    simp only [RPM, Set.mem_iInter]
    intro α hα
    have h1 := hz (interior α) (hinterior α hα)
    rw [← hkey (interior α) isOpen_interior] at h1
    exact monotoneSetOrbitClosure _ _ _ interior_subset h1
  · intro z hz
    simp only [RPM, Set.mem_iInter] at hz
    simp only [RP, Set.mem_iInter]
    intro α hα
    have h1 := hz (interior α) (hinterior α hα)
    rw [hkey (interior α) isOpen_interior] at h1
    exact closure_mono (Set.iUnion_mono fun _ ↦ Set.preimage_mono interior_subset) h1

/- A dynamical system on `X` which acts by surjections is equicontinuous if and only
if the regionally proximal relation is contained in the diagonal of `X × X` -/
theorem equiSurjectiveIffBackEqui
(dSystem : DynamicalSystem S X) :
(isSurjectiveSystem dSystem ∧ isEquicontinuousSystem dSystem) ↔
  isBackwardEquicontinuousSystem dSystem := by
  constructor
  · -- `X × X` is surjective and equicontinuous, hence semisimple, so `RP = RPM ⊆ Δ`
    rintro ⟨hsurj, hequi⟩
    have hss : isSemisimpleSystem (diagDynamicalSystem dSystem dSystem) :=
      equiSurjectiveSystemsAreSemisimple (diagDynamicalSystem dSystem dSystem)
        (diagOfSurjectiveIsSurjective hsurj) (diagOfEquiIsEqui hequi)
    rw [backEquiSystemIffRPInDiag, RPEqRPMOfDiagSemisimple hss]
    exact (equiSystemIffRPMInDiag dSystem).mp hequi
  · -- `X × X` is backward equicontinuous, hence semisimple, so `RPM = RP ⊆ Δ`
    intro hback
    refine ⟨backEqImpliesSurjective dSystem hback, ?_⟩
    have hss : isSemisimpleSystem (diagDynamicalSystem dSystem dSystem) :=
      backEquiSystemsAreSemisimple (diagDynamicalSystem dSystem dSystem)
        (diagOfBackEquiIsBackEqui hback)
    rw [equiSystemIffRPMInDiag, ← RPEqRPMOfDiagSemisimple hss]
    exact (backEquiSystemIffRPInDiag dSystem).mp hback

/-- Summary theorem. If S acts on an S-system surjectively and the system is equicontinuous,
or if the system is backward equi, then any product system is equicontinuous,
backward equicontinuous, distal, semisimple, and S acts on them by homeomorphisms -/
theorem surjEquiOrBackEquiImpliesEquiBackEquiDistalSemisimpleHomeo
(dSystem : DynamicalSystem S X) :
((isSurjectiveSystem dSystem ∧ isEquicontinuousSystem dSystem) ∨
isBackwardEquicontinuousSystem dSystem) →
  isEquicontinuousSystem dSystem ∧
  isBackwardEquicontinuousSystem dSystem ∧
  isSemisimpleSystem dSystem ∧
  isDistalSystem dSystem ∧
  isHomeoSystem dSystem := by
  intro hhyp
  have hback : isBackwardEquicontinuousSystem dSystem := by
    rcases hhyp with h | h
    · exact (equiSurjectiveIffBackEqui dSystem).mp h
    · exact h
  obtain ⟨hsurj, hequi⟩ := (equiSurjectiveIffBackEqui dSystem).mpr hback
  have hss : isSemisimpleSystem dSystem :=
    equiSurjectiveSystemsAreSemisimple dSystem hsurj hequi
  have hssdiag : isSemisimpleSystem (diagDynamicalSystem dSystem dSystem) :=
    equiSurjectiveSystemsAreSemisimple (diagDynamicalSystem dSystem dSystem)
      (diagOfSurjectiveIsSurjective hsurj) (diagOfEquiIsEqui hequi)
  have hdistal : isDistalSystem dSystem := (distalIffDiagSemisimple dSystem).mp hssdiag
  refine ⟨hequi, hback, hss, hdistal, fun s ↦ ?_⟩
  -- distality gives injectivity: if `s x = s y` then `(x,y)` is a proximal pair
  have hinj : Function.Injective (dSystem.map s) := by
    intro a b hab
    refine hdistal a b fun α hα ↦ ⟨s, ?_⟩
    rw [hab]
    exact subset_of_mem_nhdsSet hα rfl
  exact isHomeomorph_iff_continuous_bijective.mpr ⟨dSystem.mapCont s, hinj, hsurj s⟩

/-- A dynamical system on `X` which acts by surjections is equicontinuous if and only
if the regionally proximal relation is contained in the diagonal of `X × X` -/
theorem equicontinuousIffRPTrivialAndSurjective
(dSystem : DynamicalSystem S X) :
RP dSystem ⊆ Set.diagonal X ↔
  (isSurjectiveSystem dSystem ∧ isEquicontinuousSystem dSystem) :=
    calc
      RP dSystem ⊆ Set.diagonal X ↔ isBackwardEquicontinuousSystem dSystem :=
        (backEquiSystemIffRPInDiag dSystem).symm
      _ ↔ isSurjectiveSystem dSystem ∧ isEquicontinuousSystem dSystem :=
        (equiSurjectiveIffBackEqui dSystem).symm

end Semisimplicity_and_equicontinuity
