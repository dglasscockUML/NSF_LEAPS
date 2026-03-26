import NSFLEAPS._00_Imports.IM_Base

/- Useful commands (for copy-pasting)
Cartesian product of sets: A ×ˢ B
  This gives Set (X × Y) from A : Set X and B : Set Y
-/

/-- The image of the closure of a set `A` under a
continuous map `f` is the closure of the image of `A` -/
theorem imageClosureIsClosureImage
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X]
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
(f : X → Y) {fc : Continuous f} (A : Set X) :
f '' (closure A) = closure (f '' A) :=
sorry

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

theorem closureIntersect
{X} [TopologicalSpace X]
{A B : Set X} (hInt : ∀ U ∈ nhdsSet A, (U ∩ B).Nonempty) :
(A ∩ closure B).Nonempty :=
by sorry

/-- The image of an entourage `α` of `X` under a continuous
surjection `π: X → Y` contains a set of the form `U × U`
where `U` is an open subset of `Y` -/
theorem openProductInEntourageImage
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X]
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
(π : X → Y) {hc : Continuous π} {hs : Function.Surjective π}
(α : Set (X × X)) {ha : α ∈ nhdsSet (Set.diagonal X)} :
∃ (U : Set Y), IsOpen U ∧ ((U ×ˢ U) ⊆ ((Prod.map π π) '' α)) := sorry
