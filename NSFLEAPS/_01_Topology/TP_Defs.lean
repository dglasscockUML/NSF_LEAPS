import NSFLEAPS._00_Imports.IM_Base

/- Useful commands (for copy-pasting)
Cartesian product of sets: A ×ˢ B
  This gives Set (X × Y) from A : Set X and B : Set Y
-/

theorem imageClosureIsClosureImage {X} [TopologicalSpace X] [CompactSpace X] [T2Space X]
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
(f : X → Y) {fc : Continuous f} (A : Set X) :
f '' (closure A) = closure (f '' A) :=
sorry

theorem openClosureProductInEntourage {X} [UniformSpace X] (x : X)
(α : Set (X × X)) {ha : α ∈ uniformity X} :
∃ U ∈ nhds x, IsOpen U ∧ ((closure U) ×ˢ (closure U) ⊆ α) :=
sorry

theorem openProductInEntourageImage {X} [TopologicalSpace X] [CompactSpace X] [T2Space X]
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
(π : X → Y) {hc : Continuous π} {hs : Function.Surjective π}
(α : Set (X × X)) {ha : α ∈ nhdsSet (Set.diagonal X)} :
∃ (U : Set Y), IsOpen U ∧ ((U ×ˢ U) ⊆ ((Prod.map π π) '' α)) := sorry
