import NSFLEAPS._00_Imports.IM_Base

/- Useful commands (for copy-pasting)
Cartesian product of sets: A ×ˢ B
  This gives Set (X × Y) from A : Set X and B : Set Y
-/

-- Continuous.isProperMap
-- IsProperMap.isClosedMap
-- IsCompact.image: continuous image of compact is compact
-- isCompact.isClosed: compact implies closed

/-- The image of the closure of a set `A` under a
continuous map `f` is the closure of the image of `A` -/
theorem imageClosureIsClosureImage
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X]
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
(f : X → Y) {fc : Continuous f} (A : Set X) :
f '' (closure A) = closure (f '' A) := by
have h1 : IsProperMap f := by apply Continuous.isProperMap fc
have h2 : IsClosedMap f := by apply IsProperMap.isClosedMap h1
rw [<- IsClosedMap.closure_image_eq_of_continuous h2 fc]

/-- Given an entourage `α` of `X` and a point `x ∈ X`
there exists an open neighborhood `U` of `x` such that
the closure of `U × U` is a subset of `α` -/
theorem openClosureProductInEntourage
{X} [UniformSpace X] (x : X)
(α : Set (X × X)) {ha : α ∈ uniformity X} :
∃ U ∈ nhds x, IsOpen U ∧ ((closure U) ×ˢ (closure U) ⊆ α) :=
sorry

-- The following is an alternative to openClosureProductInEntourage using nbhds of diagonal
/-- Given an entourage `α` of `X` and a point `x ∈ X`
there exists an open neighborhood `U` of `x` such that
the closure of `U × U` is a subset of `α` -/
theorem openClosureProductInNhdDiag
{X} [TopologicalSpace X]
(x : X) (α : Set (X × X)) {ha : α ∈ nhdsSet (Set.diagonal X)} :
∃ U ∈ nhds x, IsOpen U ∧ ((closure U) ×ˢ (closure U) ⊆ α) :=
sorry

/-- If every neighborhood of a set A intersects B, then A intersects closure of B -/
theorem closureIntersect
{X} [TopologicalSpace X]
{A B : Set X} (hInt : ∀ U ∈ nhdsSet A, (U ∩ B).Nonempty) :
(A ∩ closure B).Nonempty := by
by_contra h
have h1 : A ⊆ (closure B)ᶜ := by
  intro x hxA
  by_contra hxB
  have hxB2 : x ∈ closure B := by simpa using hxB
  apply h
  exact ⟨x, ⟨hxA, hxB2⟩⟩
have hopen : IsOpen (closure B)ᶜ :=
    isOpen_compl_iff.mpr isClosed_closure
have h2 : (closure B)ᶜ ∈ nhdsSet A := by
  refine mem_nhdsSet_iff_forall.mpr ?_
  intro x hx
  apply hopen.mem_nhds
  exact h1 hx
specialize hInt (closure B)ᶜ
apply hInt at h2
rcases h2 with ⟨w, hw⟩
have h3 : w ∈ closure B := by
  apply subset_closure
  exact hw.2
exact hw.1 h3

/-- The image of an entourage `α` of `X` under a continuous
surjection `π: X → Y` contains a set of the form `U × U`
where `U` is an open subset of `Y` -/
theorem openProductInEntourageImage
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X]
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
(π : X → Y) {hc : Continuous π} {hs : Function.Surjective π}
(α : Set (X × X)) {ha : α ∈ nhdsSet (Set.diagonal X)} :
∃ (U : Set Y), IsOpen U ∧ ((U ×ˢ U) ⊆ ((Prod.map π π) '' α)) := sorry
