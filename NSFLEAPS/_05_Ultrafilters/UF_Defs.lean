import NSFLEAPS._04_Dynamical_systems.DS_Defs

section Right_topological_semigroups

-- For def. of RightTopological, cf. Hindman-Strauss Def. 2.1
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

omit [Nonempty S]

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
∃ (M : Set S), isMinLeftIdeal M ∧ M ⊆ L :=
by sorry

/-- Compact, right-topological semigroups contain minimal left ideals -/
theorem rightTopSemigroupContainsMinLeftIdeal :
∃ (L : Set S), isMinLeftIdeal L :=
by sorry -- Just apply leftIdealContainsMinLeftIdeal with left ideal S

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

section Ultrafilters_as_a_semigroup

-- Was S_left_mult
/-- `leftMult s : S → S` is left multiplication by `s` -/
def leftMult
{S: Type*} [Semigroup S] (s : S) :
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
{S : Type*} [Semigroup S] (L : Set (Ultrafilter S)) {hL : isLeftIdeal L} :
∃ (p : Ultrafilter S), (isMinimalUltrafilter p) ∧ (p * p = p) :=
by sorry

end Ultrafilters_as_topological_semigroups

section Ultrafilters_as_phase_space

/-- Given a semigroup `S`, `ultrafilterSystem S` is the dynamical system of `S`
acting on `βS` by left multiplication -/
def ultrafilterSystem
(S : Type*) [Semigroup S] [Nonempty S] :
DynamicalSystem S (Ultrafilter S) :=
by sorry

/-- The subsystems of `ultrafilterSystem S` are precisely
the closed left ideals of `βS` -/
theorem ultraSubsystemIffClosedLeftIdeal
{S : Type*} [Semigroup S] [Nonempty S] (Z : Set (Ultrafilter S)) :
isNonemptyCompactT2InvariantSubset (ultrafilterSystem S) Z ↔
(IsClosed Z ∧ isLeftIdeal Z) :=
  by sorry

/-- The minimal subsystems of `ultrafilterSystem S` are precisely
the minimal left ideals of `βS` -/
theorem ultraMinSubsystemIffMinLeftIdeal
{S : Type*} [Semigroup S] [Nonempty S] (Z : Set (Ultrafilter S)) :
isMinimalSubset (ultrafilterSystem S) Z ↔ isMinLeftIdeal Z :=
  by sorry

/-- An ultrafilter is minimal if and only if it is `S`-uniformly recurrent -/
theorem ultrafilterMinimalIffUnifRec
{S : Type*} [Semigroup S] [Nonempty S] (p : Ultrafilter S) :
isMinimalUltrafilter p ↔ isUniformlyRecurrent (ultrafilterSystem S) p :=
  by sorry

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
by sorry

/-- Given a dynamical system `dSystem : DynamicalSystem S X`, a point
`x : X`, and `p : βS`, the point `px` belongs to the orbit closure of `x` -/
theorem ultraActionInOrbitClosure
(p : Ultrafilter S) (x : X) :
(ultraAction dSystem).map p x ∈ orbitClosure dSystem x :=
by sorry

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
by sorry

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
