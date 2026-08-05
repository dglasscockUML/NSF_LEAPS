import NSFLEAPS._00_Imports.IM_Base

import Mathlib.Topology.UniformSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.OfCompactT2

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
{f : X → Y} (fc : Continuous f) (A : Set X) :
f '' (closure A) = closure (f '' A) :=
  by
    have h1 : IsProperMap f := by apply Continuous.isProperMap fc
    have h2 : IsClosedMap f := by apply IsProperMap.isClosedMap h1
    rw [<- IsClosedMap.closure_image_eq_of_continuous h2 fc]

/-- Given an entourage `α` of `X` and a point `x ∈ X`
there exists an open neighborhood `U` of `x` such that
the closure of `U × U` is a subset of `α` -/
theorem openClosureProductInEntourage
{X} [UniformSpace X] (x : X)
(α : Set (X × X)) {ha : α ∈ uniformity X} :
∃ U ∈ nhds x, IsOpen U ∧ ((closure U) ×ˢ (closure U) ⊆ α) := by
-- Show that there exists a neighborhood V of x such that V × V ⊆ α
have hV0 : ∃ V ∈ nhds x, V ×ˢ V ⊆ α := by
  rcases comp_mem_uniformity_sets ha with ⟨γ, hγ1, hγ2⟩
  let β := γ ∩ Prod.swap ⁻¹' γ
  have hβ_symmetric : β = Prod.swap ⁻¹' β := by
    unfold β
    simp only [Set.preimage_inter]
    have hb4 : Prod.swap ⁻¹' (Prod.swap ⁻¹' γ) = γ := by
      ext p
      constructor
      · intro hp
        simpa [Set.preimage, Prod.swap] using hp
      · intro hp
        simpa [Set.preimage, Prod.swap] using hp
    rw [hb4]
    apply Set.inter_comm
  have hProdSwap: Prod.swap ⁻¹' γ ∈ uniformity X := by
    apply UniformSpace.symm
    exact hγ1
  have hβ_uniformity : β ∈ uniformity X := by
    apply (uniformity X).inter_mem
    ·exact hγ1
    exact hProdSwap
  have β_subset_γ : β ⊆ γ := by
    apply Set.inter_subset_left
  have hβ_SetRel_γ : SetRel.comp β β ⊆ SetRel.comp γ γ := by
    apply SetRel.comp_subset_comp β_subset_γ β_subset_γ
  have hβ_α: SetRel.comp β β ⊆ α := by
    exact (hβ_SetRel_γ.trans) hγ2
  refine ⟨UniformSpace.ball x β, UniformSpace.ball_mem_nhds x hβ_uniformity, ?_⟩
  intro p hp
  rcases hp with ⟨hy, hz⟩
  have hp1: (x, p.1) ∈ β := by
    simpa [UniformSpace.ball] using hy
  have hp1x : (p.1, x) ∈ β := by
    have hx' : (p.1, x) ∈ Prod.swap ⁻¹' β := by
      simpa using hp1
    rw [hβ_symmetric]
    exact hx'
  exact hβ_α ⟨x, by simpa [UniformSpace.ball] using hp1x,
    by simpa [UniformSpace.ball] using hz⟩
-- end of proof of hV0
obtain ⟨V, hV1, hV2⟩ := hV0
obtain ⟨W, hW⟩ := exists_mem_nhds_isClosed_subset hV1
obtain ⟨hW1, hW2, hW3⟩ := hW
rcases mem_nhds_iff.mp hW1 with ⟨U, hUsub, hUopen, hxU⟩
have hUW : closure U ⊆ W := by
  have hWclosure: closure W = W := by
    apply IsClosed.closure_eq
    exact hW2
  rw [<- hWclosure]
  exact closure_mono hUsub
have h1 : closure U ×ˢ closure U ⊆ W ×ˢ W := by
  exact Set.prod_mono hUW hUW
have h2 : W ×ˢ W ⊆ V ×ˢ V := by
  exact Set.prod_mono hW3 hW3
have h4 : closure U ×ˢ closure U ⊆ α :=
  (h1.trans h2).trans hV2
use U
constructor
· apply IsOpen.mem_nhds
  · exact hUopen
  · exact hxU
constructor
· exact hUopen
exact h4

-- The following is an alternative to openClosureProductInEntourage using nbhds of diagonal
--/-- Given an entourage `α` of `X` and a point `x ∈ X`
--there exists an open neighborhood `U` of `x` such that
--the closure of `U × U` is a subset of `α` -/
-- Since we already proved openClosureProductInEntourage, this theorem is no longer needed
-- theorem openClosureProductInNhdDiag
-- {X} [TopologicalSpace X]
-- (x : X) (α : Set (X × X)) {ha : α ∈ nhdsSet (Set.diagonal X)} :
-- ∃ U ∈ nhds x, IsOpen U ∧ ((closure U) ×ˢ (closure U) ⊆ α) :=
-- sorry

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
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
(π : X → Y) {hc : Continuous π} {hs : Function.Surjective π}
(α : Set (X × X)) {ha : α ∈ nhdsSet (Set.diagonal X)} :
∃ (U : Set Y), U.Nonempty ∧ IsOpen U ∧ ((U ×ˢ U) ⊆ ((Prod.map π π) '' α)) := by
letI : UniformSpace X := uniformSpaceOfCompactR1
have h1 : ∀ x : X, ∃ Ux ∈ nhds x, IsOpen Ux ∧ ((closure Ux) ×ˢ (closure Ux) ⊆ α) := by
  intro x
  apply openClosureProductInEntourage
  simp only [← nhdsSet_diagonal_eq_uniformity]
  exact ha
have h2 : ∀ x : X, ∃ Ux : Set X, x ∈ Ux ∧ IsOpen Ux ∧ ((closure Ux) ×ˢ (closure Ux) ⊆ α) := by
  intro x
  specialize h1 x
  rcases h1 with ⟨Ux, hUx1, hUx2⟩
  have hxInUx : x ∈ Ux := by
    apply mem_of_mem_nhds
    exact hUx1
  use Ux
choose U hU1 hU2 hU3 using h2
have hCover : Set.univ ⊆ ⋃ x ∈ Set.univ, U x := by
  intro y hy
  simp only [Set.mem_univ, Set.iUnion_true, Set.mem_iUnion]
  use y
  specialize hU1 y
  exact hU1
have hExistFinite : ∃ F ⊆ Set.univ, Set.Finite F ∧ Set.univ ⊆ ⋃ x ∈ F, U x := by
  apply IsCompact.elim_finite_subcover_image
  · apply isCompact_univ
  · intro x hx
    specialize hU2 x
    exact hU2
  · exact hCover
rcases hExistFinite with ⟨F, hF1, hF2, hF3⟩
have hClosure : Set.univ ⊆ ⋃ x ∈ F, closure (U x) := by
  have hGoal : ⋃ x ∈ F, U x ⊆ ⋃ x ∈ F, closure (U x) := by
    simp only [Set.iUnion_subset_iff]
    intro x hx t ht
    simp only [Set.mem_iUnion, exists_prop]
    use x
    constructor
    · exact hx
    · apply subset_closure
      exact ht
  exact hF3.trans hGoal
have hImage1 : Set.univ ⊆ π '' (Set.univ) := by
  unfold Function.Surjective at hs
  intro y hy
  specialize hs y
  rcases hs with ⟨x, hx⟩
  simp only [Set.image_univ, Set.mem_range]
  use x
have hImage2 : π '' (Set.univ) ⊆ π '' (⋃ x ∈ F, closure (U x)) := by
  apply Set.image_mono
  exact hClosure
have hImage : Set.univ ⊆ π '' (⋃ x ∈ F, closure (U x)) := by
  exact hImage1.trans hImage2
have hFull : π '' (⋃ x ∈ F, closure (U x)) = Set.univ := by
  apply subset_antisymm
  · simp
  · exact hImage
have hEqual : π '' (⋃ x ∈ F, closure (U x)) = ⋃ x ∈ F, π '' (closure (U x)) := by
  ext t
  constructor
  · intro ht
    simp only [Set.mem_iUnion, Set.mem_image, exists_prop]
    simp only [Set.mem_image, Set.mem_iUnion, exists_prop] at ht
    rcases ht with ⟨x, hx1, hx2⟩
    rcases hx1 with ⟨w, hw1, hw2⟩
    use w
    constructor
    · exact hw1
    · use x
  · intro ht
    simp only [Set.mem_image, Set.mem_iUnion, exists_prop]
    simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at ht
    rcases ht with ⟨x, hx1, w, hw1, hw2⟩
    use w
    constructor
    · use x
    · exact hw2
have hClosed : ∀ x ∈ F, IsClosed (π '' (closure (U x))) := by
  intro x hx
  apply IsCompact.isClosed
  apply IsCompact.image
  · apply IsClosed.isCompact
    apply isClosed_closure
  · exact hc
let V : F → Set Y := fun x ↦ π '' (closure (U x))
letI hFCountable : Countable F := by
  simp only [Set.countable_coe_iff]
  apply Set.Finite.countable
  exact hF2
have hInteriorNonEmpty : ∃ x : F, (interior (V x)).Nonempty := by
  letI : BaireSpace Y := by apply BaireSpace.of_t2Space_locallyCompactSpace
  apply nonempty_interior_of_iUnion_of_closed
  · intro x
    simp only [V]
    specialize hClosed x
    have hxF : Subtype.val x ∈ F := by
      simp
    apply hClosed hxF
  · simp only [Set.iUnion_coe_set, V]
    rw [<- hEqual]
    exact hFull
rcases hInteriorNonEmpty with ⟨x, hx⟩
rcases hx with ⟨y, hy⟩
have hWExist : ∃ W ⊆ V x, IsOpen W ∧ y ∈ W := by
  apply mem_interior.mp
  exact hy
rcases hWExist with ⟨W, hW1, hW2, hW3⟩
use W
constructor
· exact Set.nonempty_of_mem hW3
constructor
· exact hW2
· have hWV : W ×ˢ W ⊆ (V x) ×ˢ (V x) := by
    apply Set.prod_mono
    · exact hW1
    · exact hW1
  have hVx : (V x) ×ˢ (V x) ⊆ Prod.map π π '' α := by
    simp only [V]
    have hUx : (π '' closure (U ↑x)) ×ˢ (π '' closure (U ↑x))
      = Prod.map π π '' (closure (U ↑x)) ×ˢ closure (U ↑x) := by
      unfold Prod.map
      simp only
      ext z
      constructor
      · intro hz
        simp only [Set.mem_image, Set.mem_prod, Prod.exists]
        simp only [Set.mem_prod, Set.mem_image] at hz
        rcases hz with ⟨hx1, hx2⟩
        rcases hx1 with ⟨x1, hx1a, hx1b⟩
        rcases hx2 with ⟨x2, hx2a, hx2b⟩
        use x1
        use x2
        constructor
        · constructor
          · exact hx1a
          · exact hx2a
        · simp [hx1b, hx2b]
      · intro hz
        simp only [Set.mem_prod, Set.mem_image]
        simp only [Set.mem_image, Set.mem_prod, Prod.exists] at hz
        rcases hz with ⟨y, u, hyu1, hyu2⟩
        rcases hyu1 with ⟨hya, hza⟩
        rcases hyu2 with ⟨hz1n, hz2n⟩
        constructor
        · use y
        · use u
    rw [hUx]
    apply Set.image_mono
    specialize hU3 x
    exact hU3
  exact hWV.trans hVx

/-- If π : X → Y is continuous surjection of compact Hausdorff spaces, y ∈ Y, W ⊆ X
such that π ⁻¹' {y} ⊆ W, then there exists an open U ⊇ y such that π ⁻¹' U ⊆ W -/
theorem existOpenNeighborhoodPreImageContainedIn
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X]
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
(π : X → Y) {hc : Continuous π}
(y : Y) (W : Set X) (hWOpen : IsOpen W) (hyW : π ⁻¹' {y} ⊆ W) :
∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ π ⁻¹' U ⊆ W := by
have h1 : IsClosed (π '' (Wᶜ)) := by
  apply IsCompact.isClosed
  apply IsCompact.image
  · apply IsClosed.isCompact
    apply IsOpen.isClosed_compl
    exact hWOpen
  · exact hc
have h2 : y ∉ π '' Wᶜ := by
  simp only [Set.mem_image, Set.mem_compl_iff, not_exists, not_and]
  by_contra hContra
  simp only [not_forall, not_not] at hContra
  rcases hContra with ⟨x, hx1, hx2⟩
  have hxComp : x ∈ π ⁻¹' {y} := by
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact hx2
  have hxW : x ∈ W := by
    apply hyW
    exact hxComp
  exact hx1 hxW
let U := (π '' Wᶜ)ᶜ
have hUCont : y ∈ U := by
  unfold U
  apply (Set.mem_compl_iff (π '' Wᶜ) y).mpr
  exact h2
have hUPre : π ⁻¹' U ⊆ W := by
  unfold U
  intro x hx
  simp only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage, Set.mem_image, not_exists,
    not_and] at hx
  by_contra hContra
  specialize hx x hContra
  have hx2 : π x = π x := rfl
  exact hx hx2
have hUOpen : IsOpen U := by
  apply isOpen_compl_iff.mpr
  exact h1
use U
