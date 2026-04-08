import NSFLEAPS._04_Dynamical_systems.DS_Defs

section Right_topological_semigroups

/-- A topological semigroup `S` is RightTopological if for all elements `s ∈ S`,
right multiplication by `s`, as a function from `S → S`, is continuous -/
class RightTopological (S : Type*) [Semigroup S] [TopologicalSpace S] where
  rightCont : ∀ (s : S), Continuous (· * s)

variable {S : Type*} [Nonempty S] [Semigroup S] [TopologicalSpace S]
  [CompactSpace S] [T2Space S] [hRT : RightTopological S]

/-- Compact, Hausdorff, right-topological semigroups contain an idempotent element -/
theorem compactT2RTSemigroupContainsIdempotent :
∃ (s : S), s * s = s :=
exists_idempotent_of_compact_t2_of_continuous_mul_left hRT.rightCont

/-- In a compact, Hausdorff, right-topological semigroup `S`, principal left ideals,
that is, sets of the form `Ss`, are closed -/
theorem principalLeftIdealClosed
(s : S) :
IsClosed ((· * s) '' Set.univ) :=
by sorry

/-- In a compact, Hausdorff, right-topological semigroup `S`, every left ideal
contains a closed left ideal -/
theorem leftIdealContainsClosedLeftIdeal
(L : Set S) {hL : isLeftIdeal L} :
∃ (M : Set S), isLeftIdeal M ∧ IsClosed M ∧ M ⊆ L :=
by sorry

/-- In a compact, Hausdorff, right-topological semigroup `S`, every minimal left
ideal is compact -/
theorem minimalLeftIdealCompact
(L : Set S) {hL : isMinLeftIdeal L} :
IsCompact L :=
by sorry

/-- In a compact, Hausdorff, right-topological semigroup `S`, every left ideal
contains a minimal left ideal -/
theorem leftIdealContainsMinLeftIdeal
(L : Set S) {hL : isLeftIdeal L} :
∃ (M : Set S), isMinLeftIdeal M ∧ M ⊆ L :=
by sorry

omit [Nonempty S] [CompactSpace S] in
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
∃ s ∈ L, s * s = s :=
by sorry

end Right_topological_semigroups

section Ultrafilters_as_topological_semigroups

-- There is some basic semigroup stuff here that might be better in SG_Defs

-- Was: semigroup_action
/-- `semigroupAction S X` is, for each `s : S`, a map `s: X → X` such that
`st: X → X` is the composition of `s: X → X` and `t: X → X` -/
structure semigroupAction
(S : Type*) [Semigroup S] (X : Type*) where
  map : S → X → X
  mapMult : ∀ s₁ s₂ x, map (s₁ * s₂) x = map s₁ (map s₂ x)

-- Was: ultra_semigroup
/- This instance makes the semigroup structure on βS "canonical" by
making it available to typeclass inference. -/
instance
{S : Type*} [Semigroup S] : Semigroup (Ultrafilter S) :=
  Ultrafilter.semigroup

-- Was: ultra_alt_prod_desc
/-- An equivalent, alternative description of the ultrafilter product -/
theorem ultraProductDescription
{S : Type*} [Semigroup S] (p q : Ultrafilter S) (A : Set S) :
A ∈ p * q ↔ {s : S | {t : S | s * t ∈ A} ∈ q} ∈ p :=
  Iff.rfl

-- Was S_left_mult
/-- `leftMult s : S → S` is left multiplication by `s` -/
def leftMult
{S: Type*} [Semigroup S] (s : S) :
S → S :=
  (s * ·)

/-- `rightMult s : S → S` is right multiplication by `s` -/
def rightMult
{S: Type*} [Semigroup S] (s : S) :
S → S :=
  (· * s)

-- Was: ultra_left_mult
/-- `leftMultUltra q : βS → βS` is left multiplication by `q` -/
def leftMultUltra
{S: Type*} [Semigroup S] (q : Ultrafilter S) :
Ultrafilter S → Ultrafilter S :=
  (q * ·)

-- Was: ultra_right_mult
/-- `rightMultUltra q : βS → βS` is right multiplication by `q` -/
def rightMultUltra
{S: Type*} [Semigroup S] (q : Ultrafilter S) :
Ultrafilter S → Ultrafilter S :=
(· * q)

/-- The predicate that the map `φ : S → T` is a semigroup homomorphism -/
def isSemigroupHom
{S T : Type*} [Semigroup S] [Semigroup T] (φ : S → T) :
Prop :=
∀ (s1 s2 : S), φ (s1 * s2) = (φ s1) * (φ s2)

-- Was: pure_is_hom (s t : S)
-- Was: (pure s : Ultrafilter S) * (pure t : Ultrafilter S) = pure (s * t)
/-- The canonical injection pure : S → βS is a semigroup homomorphism -/
theorem pureIsHom
{S : Type*} [Semigroup S] :
isSemigroupHom (pure : S → Ultrafilter S) :=
by
  unfold isSemigroupHom
  intro s t
  constructor

-- The following proof is copied from the mathlib documentation
-- Was: ultra_right_mult_continuous
/-- For all `q ∈ βS`, `ultraRightMult q: βS → βS` is continuous -/
theorem rightMultUltraContinuous
{S : Type*} [Semigroup S] (q : Ultrafilter S) :
Continuous (rightMultUltra q) :=
ultrafilterBasis_is_basis.continuous_iff.2 <| Set.forall_mem_range.mpr fun A ↦
    ultrafilter_isOpen_basic { m : S | ∀ᶠ m' in q, m * m' ∈ A }

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

end Ultrafilters_as_topological_semigroups
