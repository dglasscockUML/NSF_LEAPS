import NSFLEAPS._00_Imports.IM_Base

import Mathlib.Data.Set.Defs
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UniformSpace.Defs

/- Useful commands (for copy-pasting)
Cartesian product of sets: A ×ˢ B
  This gives Set (X × Y) from A : Set X and B : Set Y
-/

theorem imageClosureIsClosureImage {X} [TopologicalSpace X] [CompactSpace X]
[T2Space X] {Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
(f : X → Y) {fc : Continuous f} (A : Set X) :
f '' (closure A) = closure (f '' A) :=
sorry

theorem openClosureProductInEntourage {X} [UniformSpace X] (x : X) {α}
(ha : α ∈ uniformity X) :
∃ U ∈ nhds x, IsOpen U ∧ ((closure U) ×ˢ (closure U) ⊆ α) :=
sorry

theorem openProductInEntourageImage {X} [TopologicalSpace X] [CompactSpace X]
[T2Space X] {Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
(π : X → Y) {hc : Continuous π} {hs : Function.Surjective π} {α}
(ha : α ∈ uniformity X) : 1=1 := sorry
-- typeclass is not understanding compact hausdorff spaces automatically as uniform spaces
-- ∃ U open subset of Y, U ×ˢ U in image of alpha under pi times pi
