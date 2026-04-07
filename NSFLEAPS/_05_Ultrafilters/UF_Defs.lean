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

section Ultrafilters_as_semigroups

-- This section very much still under construction

structure semigroupAction
(S : Type*) [Semigroup S] (X : Type*) where
  map : S → X → X
  mapMult : ∀ s₁ s₂ x, map (s₁ * s₂) x = map s₁ (map s₂ x)

instance ultra_semigroup {S} [Semigroup S] : Semigroup (Ultrafilter S) :=
  Ultrafilter.semigroup

  -- This is an alternative description of ultrafilter multiplication
theorem ultra_alt_prod_desc {S} [Semigroup S] (p q : Ultrafilter S) (A : Set S) :
    A ∈ p * q ↔ {s : S | {t : S | s * t ∈ A} ∈ q} ∈ p :=
  Iff.rfl

def ultra_right_mult {S} [Semigroup S] (q : Ultrafilter S) :
Ultrafilter S → Ultrafilter S := (· * q)

def ultra_left_mult {S} [Semigroup S] (q : Ultrafilter S) :
Ultrafilter S → Ultrafilter S := (q * ·)

def S_left_mult {S} [Semigroup S] (s : S) :
S → S := (s * ·)

-- The function pure : S → βS is a semigroup homomorphism
theorem pure_is_hom {S} [Semigroup S] (s t : S) :
(pure s : Ultrafilter S) * (pure t : Ultrafilter S) = pure (s * t) := by
  constructor

end Ultrafilters_as_semigroups
