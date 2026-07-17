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
{Y} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
(π : X → Y) {hc : Continuous π} {hs : Function.Surjective π}
(α : Set (X × X)) {ha : α ∈ nhdsSet (Set.diagonal X)} :
∃ (U : Set Y), IsOpen U ∧ ((U ×ˢ U) ⊆ ((Prod.map π π) '' α)) := sorry
