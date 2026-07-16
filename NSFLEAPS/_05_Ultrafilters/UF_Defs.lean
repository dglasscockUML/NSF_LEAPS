import NSFLEAPS._04_Dynamical_systems.DS_Defs

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
  · simp only [Set.mem_setOf_eq, C]
    constructor
    · apply isClosed_sInter
      intro t ht
      have htInC : t ∈ C := by
        apply hc1 ht
      simp only [Set.mem_setOf_eq, C] at htInC
      rcases htInC with ⟨ht1, ht2, ht3⟩
      exact ht1
    constructor
    · apply nonemptyInterOfLeftIdealsIsLeftIdeal
      · intro t ht
        have htInC : t ∈ C := by
          apply hc1 ht
        simp only [Set.mem_setOf_eq, C] at htInC
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
        simp only [Set.mem_setOf_eq, C] at htInC
        rcases htInC with ⟨ht1, ht2, ht3⟩
        rcases ht2 with ⟨ht2a, ht2b⟩
        exact ht2a
      · intro t ht
        have htInC : t ∈ C := by
          apply hc1 ht
        simp only [Set.mem_setOf_eq, C] at htInC
        rcases htInC with ⟨ht1, ht2, ht3⟩
        apply IsClosed.isCompact ht1
      · intro t ht
        have htInC : t ∈ C := by
          apply hc1 ht
        simp only [Set.mem_setOf_eq, C] at htInC
        rcases htInC with ⟨ht1, ht2, ht3⟩
        exact ht1
    simp only [lb]
    rcases hc3 with ⟨t, ht⟩
    have htInC : t ∈ C := by
      apply hc1 ht
    simp only [Set.mem_setOf_eq, C] at htInC
    rcases htInC with ⟨ht1, ht2, ht3⟩
    have htInt : c.sInter ⊆ t := by
      apply Set.sInter_subset_of_mem ht
    exact htInt.trans ht3
  · intro t ht
    simp only [lb]
    apply Set.sInter_subset_of_mem ht
have hLCinC : LC ∈ C := by
  simp only [Set.mem_setOf_eq, subset_refl, and_true, C]
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
  · simp only [Set.mem_setOf_eq, C] at hM2a
    rcases hM2a with ⟨hMClosed, hMLeftIdeal, hMjunk⟩
    exact hMLeftIdeal
  · intro I hI1 hI2
    have hIContain : ∃ J : Set S, isLeftIdeal J ∧ IsClosed J ∧ J ⊆ I := by
      apply leftIdealContainsClosedLeftIdeal
      exact hI1
    rcases hIContain with ⟨J, hJ1, hJ2, hJ3⟩
    have hJinC : J ∈ C := by
      simp only [Set.mem_setOf_eq, C]
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

-- There is some basic semigroup stuff here that might be better in SG_Defs

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

end Generic_ultrafilter_lemmas

section Ultrafilters_as_a_semigroup

-- Was S_left_mult
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
B ∈ leftMultUltra (pure s) p ↔ (leftMult s) ⁻¹' B ∈ p :=
by sorry

/-- Given `s ∈ S` and `B ⊆ S`, `closure(s⁻¹B) = s⁻¹closure(B)` -/
theorem preimageClosureDescription
{S : Type*} [Semigroup S]
(s : S) (B : Set S) :
closure ((pure : S → Ultrafilter S) '' ((leftMult s) ⁻¹' B)) =
(leftMultUltra (pure s)) ⁻¹' (closure ((pure : S → Ultrafilter S) '' B)):=
by sorry

/-- Given a minimal left ideal `L ⊆ βS` and an idempotent `u ∈ L`,
for all `p ∈ L`, `pu = p` -/
theorem minimalIdempotentsAreLeftIdentites
{S : Type*} [Semigroup S]
(L : Set (Ultrafilter S)) {hL : isMinLeftIdeal L}
(u : Ultrafilter S) {huL : u ∈ L} {huIdempotent : u * u = u}
(p : Ultrafilter S) :
p ∈ L → p * u = p :=
by sorry

/-- The predicate that the ultrafilter p on S is minimal, that is, belongs to
some minimal left ideal -/
def isMinimalUltrafilter
{S : Type*} [Semigroup S] (p : Ultrafilter S) :
Prop :=
∃ (L : Set (Ultrafilter S)), isMinLeftIdeal L ∧ (p ∈ L)

end Ultrafilters_as_a_semigroup

section Ultrafilters_as_topological_semigroups

-- The following proof is copied from the mathlib documentation
-- Was: ultra_right_mult_continuous
/-- For all `q ∈ βS`, `ultraRightMult q: βS → βS` is continuous -/
theorem rightMultUltraContinuous
{S : Type*} [Semigroup S] (q : Ultrafilter S) :
Continuous (rightMultUltra q) :=
ultrafilterBasis_is_basis.continuous_iff.2 <| Set.forall_mem_range.mpr fun A ↦
    ultrafilter_isOpen_basic { m : S | ∀ᶠ m' in q, m * m' ∈ A }

/- This instance makes the RightTopological structure on βS "canonical" by
making it available to typeclass inference. -/
instance
{S : Type*} [Semigroup S] : RightTopological (Ultrafilter S) :=
  {
    rightCont := fun (q : Ultrafilter S) ↦ rightMultUltraContinuous q
  }

-- Was: ultra_left_mult_by_principal_continuous
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
        · have betaSisClosureOfImageOfPure : closure (Set.range pure) = Set.univ (α := Ultrafilter S) := by
            have := Dense.closure_eq (s := Set.range (pure : S → Ultrafilter S))
            exact this denseRange_pure
          have : ∀ (z : Ultrafilter S), z ∈ Z → (rightMultUltra z) '' (Set.univ (α := Ultrafilter S)) ⊆ Z := by
            intro z hz
            have := imageClosureIsClosureImage
              (rightMultUltraContinuous z) (Set.range pure)
            rw [← betaSisClosureOfImageOfPure]
            rw [this]
            have := IsClosed.closure_subset_iff (IsCompact.isClosed hCompact) (s := (rightMultUltra ↑z '' Set.range pure))
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
        have KinZ : K ⊆ Z := by exact LE.le.subset fun ⦃a⦄ a_1 ↦ hM2 (hK3 a_1)
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
      letI : CompactSpace L := isCompact_iff_compactSpace.mp (Lpresubsys.2.1)
      letI : Nonempty L := by
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
noncomputable
def ultraLimContinuousComp
{S : Type*}
{X : Type*} [TopologicalSpace X] [CompactSpace X]
{Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
(p : Ultrafilter S) {g : X → Y} (hπ : Continuous g) (f : S → X) :
ultraLim p (g ∘ f) = g (ultraLim p f) :=
by sorry

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
  have : Set.range (Ultrafilter.extend fun s ↦ dSystem.map s x) ⊆ closure (Set.range fun s ↦ dSystem.map s x) := by
    exact subset_of_subset_of_eq (fun ⦃a⦄ a_1 ↦ a_1) ultraLiftRange
  exact (Set.range_subset_iff).mp this p

/-- Given a factor map `π : X → Y` of dynamical systems and `p : βS`,
the action of `p` intertwines with the factor map: `p ∘ π = π ∘ p` -/
theorem ultraActionIntertwinesWithFactor
{Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(dSystemY : DynamicalSystem S Y)
{π : X → Y} (hπ : isFactorMap dSystem dSystemY π)
(p : Ultrafilter S) :
((ultraAction dSystemY).map p) ∘ π = π ∘ (ultraAction dSystem).map p :=
by sorry

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

/-- Given a minimal dynamical system `dSystem : DynamicalSystem S X`,
a minimal left ideal `L ⊆ βS`, and points `x, y ∈ X`, there exists `p ∈ L`
such that `px = y` -/
theorem minLeftIdealSurjectsOntoMinSystem
(hdSystemMin : isMinimalSystem dSystem)
{L : Set (Ultrafilter S)} (hLMin : isMinLeftIdeal L)
(x y : X) :
∃ p ∈ L, (ultraAction dSystem).map p x = y :=
by sorry

/-- Given a minimal dynamical system `dSystem : DynamicalSystem S X`,
a minimal left ideal `L ⊆ βS`, and a point `x ∈ X`, there exists an idempotent
ultrafilter `p ∈ L` such that `px = x` -/
theorem everyPointInMinFixedBySomeIdempotentUltrafilter
(hdSystemMin : isMinimalSystem dSystem)
{L : Set (Ultrafilter S)} (hLMin : isMinLeftIdeal L)
(x : X) :
∃ p ∈ L, (p * p = p) ∧ (ultraAction dSystem).map p x = x :=
by sorry

/-- Given a dynamical system `dSystem : DynamicalSystem S X`, `p ∈ βS`, and a
point `x ∈ X`, the points `x` and `px` are proximal -/
theorem pointAndUltraImageAreProximal
(x : X) {p : Ultrafilter S} (pIdempotent : p * p = p) :
proximal dSystem x ((ultraAction dSystem).map p x) :=
by sorry

/-- Given a dynamical system `dSystem : DynamicalSystem S X`, a minimal ultrafilter
`p ∈ βS`, and a point `x ∈ X`, the point `px` is `S`-uniformly recurrent -/
theorem minUltraImageIsUniformlyRecurrent
(x : X) {p : Ultrafilter S} (hp : isMinimalUltrafilter p) :
isUniformlyRecurrent dSystem ((ultraAction dSystem).map p x) :=
by sorry

/-- Given a dynamical minimal system `dSystem : DynamicalSystem S X`, a minimal
left ideal `L ⊆ βS`, and an ultrafilter `p ∈ L`, if `px = x`, then there exists
`q ∈ L` such that `pq` is idempotent and `qx = x` -/
theorem idempotentProductLifting
(hdSystemMin : isMinimalSystem dSystem) (x : X)
{L : Set (Ultrafilter S)} (hLMin : isMinLeftIdeal L)
{p : Ultrafilter S} (hpL : p ∈ L) (hpFix : (ultraAction dSystem).map p x = x) :
∃ q ∈ L, ((p * q) * (p * q) = p * q) ∧ (ultraAction dSystem).map q x = x :=
by sorry

end Ultrafilter_action_theorems
