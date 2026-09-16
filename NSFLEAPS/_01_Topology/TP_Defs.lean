import NSFLEAPS._00_Imports.IM_Base

import Mathlib.Topology.UniformSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.OfCompactT2

/-! This is a module docstring. -/

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
  let : UniformSpace X := uniformSpaceOfCompactR1
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
  let hFCountable : Countable F := by
    simp only [Set.countable_coe_iff]
    apply Set.Finite.countable
    exact hF2
  have hInteriorNonEmpty : ∃ x : F, (interior (V x)).Nonempty := by
    let : BaireSpace Y := by apply BaireSpace.of_t2Space_locallyCompactSpace
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

/-- If `U ⊆ X` is open and `y ∈ U`, there is an open `V ∋ y` and an open `α ⊆ X^2` containing
the diagonal such that if `(x,z) ∈ α` and `z ∈ V`, then `x ∈ U`. -/
theorem nbhdOfDiagForcesOtherSetContainment
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
{y : X} {U : Set X} (hUOpen : IsOpen U) (hyU : y ∈ U) :
∃ (V : Set X) (_ : IsOpen V) (_ : y ∈ V),
∃ (α : Set (X × X)) (_ : IsOpen α) (_ : Set.diagonal X ⊆ α),
∀ (x z : X), ⟨x,z⟩ ∈ α → z ∈ V → x ∈ U := by
  -- by regularity, an open `V ∋ y` whose closure is inside `U`
  obtain ⟨T, hTnhds, hTclosed, hTU⟩ := exists_mem_nhds_isClosed_subset (hUOpen.mem_nhds hyU)
  have hclosureV : closure (interior T) ⊆ U :=
    (closure_mono interior_subset).trans (hTclosed.closure_subset.trans hTU)
  refine ⟨interior T, isOpen_interior, mem_interior_iff_mem_nhds.mpr hTnhds,
    (Uᶜ ×ˢ closure (interior T))ᶜ,
    (hUOpen.isClosed_compl.prod isClosed_closure).isOpen_compl, ?_, ?_⟩
  · -- the diagonal misses `K ×ˢ closure V`, since `closure V ⊆ U`
    rintro ⟨x, z⟩ hxz
    have hxz' : x = z := hxz
    subst hxz'
    simp only [Set.mem_compl_iff, Set.mem_prod, not_and]
    exact fun hxK hxV ↦ hxK (hclosureV hxV)
  · -- if `(x,z) ∉ K ×ˢ closure V` and `z ∈ V ⊆ closure V`, then `x ∉ K`, that is, `x ∈ U`
    intro x z hxz hzV
    simp only [Set.mem_compl_iff, Set.mem_prod, not_and] at hxz
    by_contra hxU
    exact hxz hxU (subset_closure hzV)

-- DGG: this may be the same as nbhdOfDiagForcesOtherSetContainment
/-- The open neighbourhood of the diagonal that detects membership in `W` from `x`:
`α = (X × X) \ ({x} × Wᶜ)` -/
lemma existsDiagonalNbhdForcingMembership
{Z : Type*} [TopologicalSpace Z] [T1Space Z] {x : Z} {W : Set Z}
(hWOpen : IsOpen W) (hxW : x ∈ W) :
∃ α : Set (Z × Z), IsOpen α ∧ Set.diagonal Z ⊆ α ∧ ∀ w : Z, (x, w) ∈ α → w ∈ W := by
  refine ⟨(({x} : Set Z) ×ˢ Wᶜ)ᶜ, (isClosed_singleton.prod hWOpen.isClosed_compl).isOpen_compl,
    ?_, ?_⟩
  · rintro ⟨a, b⟩ hab
    have hab' : a = b := hab
    subst hab'
    intro hmem
    exact hmem.2 (by rw [show a = x from hmem.1]; exact hxW)
  · intro w hw
    by_contra hwW
    exact hw ⟨rfl, hwW⟩

/-- A point of the diagonal has a square neighbourhood inside any neighbourhood of the
diagonal -/
lemma existsSquareNbhdInDiagonalNbhd
{Z : Type*} [TopologicalSpace Z] {α : Set (Z × Z)} (hαOpen : IsOpen α)
(hαDiag : Set.diagonal Z ⊆ α) (x : Z) :
∃ V : Set Z, IsOpen V ∧ x ∈ V ∧ V ×ˢ V ⊆ α := by
  obtain ⟨u, v, hu, hv, hxu, hxv, huv⟩ := isOpen_prod_iff.mp hαOpen x x (hαDiag rfl)
  exact ⟨u ∩ v, hu.inter hv, ⟨hxu, hxv⟩, fun p hp ↦ huv ⟨hp.1.1, hp.2.2⟩⟩

/-- A compact Hausdorff space is covered by finitely many sets that are "small" with respect
to a given neighbourhood of the diagonal.  This is the "partition `X` into `∪ Uᵢ`" step of
the proofs below. -/
lemma existsFiniteCoverBySmallSets
{Z : Type*} [TopologicalSpace Z] [CompactSpace Z] {β : Set (Z × Z)}
(hβOpen : IsOpen β) (hβDiag : Set.diagonal Z ⊆ β) :
∃ (F : Finset Z) (V : Z → Set Z), (∀ x : Z, ∃ y ∈ F, x ∈ V y) ∧
  (∀ y : Z, y ∈ V y) ∧ (∀ y : Z, V y ×ˢ V y ⊆ β) := by
  classical
  choose V hVopen hxV hVβ using existsSquareNbhdInDiagonalNbhd hβOpen hβDiag
  obtain ⟨F, hF⟩ := CompactSpace.elim_nhds_subcover V (fun x ↦ (hVopen x).mem_nhds (hxV x))
  refine ⟨F, V, fun x ↦ ?_, hxV, hVβ⟩
  have hx : x ∈ (⊤ : Set Z) := trivial
  rw [← hF] at hx
  simpa using hx

/-- The "square root" of a neighbourhood of the diagonal, by hand: for every open
neighbourhood `α` of the diagonal of a compact Hausdorff space there is an open symmetric
neighbourhood `β` of the diagonal with `β ∘ β ⊆ α`.

For each `x` pick open `V x ∋ x` with `V x ×ˢ V x ⊆ α` and open `W x ∋ x` with
`closure (W x) ⊆ V x`, and take a finite subcover by the `W y`.  Then
`β = ⋂ y, (V y ×ˢ V y) ∪ (closure (W y))ᶜ ×ˢ (closure (W y))ᶜ` works: given `(a,b), (b,c) ∈ β`,
the middle point `b` lies in some `W y`, which rules out the second alternative at `y`, so
`a, b, c ∈ V y`. -/
lemma existsSymmetricSquareNbhdOfDiagonal
{Z : Type*} [TopologicalSpace Z] [CompactSpace Z] [T2Space Z] {α : Set (Z × Z)}
(hαOpen : IsOpen α) (hαDiag : Set.diagonal Z ⊆ α) :
∃ β : Set (Z × Z), IsOpen β ∧ Set.diagonal Z ⊆ β ∧
  (∀ a b : Z, (a, b) ∈ β → (b, a) ∈ β) ∧
  (∀ a b c : Z, (a, b) ∈ β → (b, c) ∈ β → (a, c) ∈ α) := by
  classical
  choose V hVopen hxV hVα using existsSquareNbhdInDiagonalNbhd hαOpen hαDiag
  have hW : ∀ x : Z, ∃ W : Set Z, IsOpen W ∧ x ∈ W ∧ closure W ⊆ V x := by
    intro x
    obtain ⟨T, hTnhds, hTclosed, hTV⟩ :=
      exists_mem_nhds_isClosed_subset ((hVopen x).mem_nhds (hxV x))
    exact ⟨interior T, isOpen_interior, mem_interior_iff_mem_nhds.mpr hTnhds,
      (closure_mono interior_subset).trans (hTclosed.closure_subset.trans hTV)⟩
  choose W hWopen hxW hWV using hW
  obtain ⟨F, hF⟩ := CompactSpace.elim_nhds_subcover W (fun x ↦ (hWopen x).mem_nhds (hxW x))
  refine ⟨⋂ y ∈ F, ((V y ×ˢ V y) ∪ ((closure (W y))ᶜ ×ˢ (closure (W y))ᶜ)), ?_, ?_, ?_, ?_⟩
  · exact F.finite_toSet.isOpen_biInter fun y _ ↦
      ((hVopen y).prod (hVopen y)).union
        (isClosed_closure.isOpen_compl.prod isClosed_closure.isOpen_compl)
  · rintro ⟨a, b⟩ hab
    have hab' : a = b := hab
    subst hab'
    simp only [Set.mem_iInter]
    intro y _
    by_cases hy : a ∈ V y
    · exact Set.mem_union_left _ ⟨hy, hy⟩
    · exact Set.mem_union_right _ ⟨fun h ↦ hy (hWV y h), fun h ↦ hy (hWV y h)⟩
  · intro a b hab
    simp only [Set.mem_iInter] at hab ⊢
    intro y hy
    rcases hab y hy with h | h
    · exact Set.mem_union_left _ ⟨h.2, h.1⟩
    · exact Set.mem_union_right _ ⟨h.2, h.1⟩
  · intro a b c hab hbc
    have hb : b ∈ (⊤ : Set Z) := trivial
    rw [← hF] at hb
    simp only [Set.mem_iUnion] at hb
    obtain ⟨y, hyF, hbW⟩ := hb
    simp only [Set.mem_iInter] at hab hbc
    have hbcl : b ∈ closure (W y) := subset_closure hbW
    have hab' : a ∈ V y ∧ b ∈ V y := by
      rcases hab y hyF with h | h
      · exact h
      · exact absurd hbcl h.2
    have hbc' : b ∈ V y ∧ c ∈ V y := by
      rcases hbc y hyF with h | h
      · exact h
      · exact absurd hbcl h.1
    exact hVα y ⟨hab'.1, hbc'.2⟩

/-- Iterating `existsSymmetricSquareNbhdOfDiagonal` gives a "cube root": an open symmetric
`β ∋ Δ` with `β ∘ β ∘ β ⊆ α`. -/
lemma existsSymmetricCubeNbhdOfDiagonal
{Z : Type*} [TopologicalSpace Z] [CompactSpace Z] [T2Space Z] {α : Set (Z × Z)}
(hαOpen : IsOpen α) (hαDiag : Set.diagonal Z ⊆ α) :
∃ β : Set (Z × Z), IsOpen β ∧ Set.diagonal Z ⊆ β ∧
  (∀ a b : Z, (a, b) ∈ β → (b, a) ∈ β) ∧
  (∀ a b c d : Z, (a, b) ∈ β → (b, c) ∈ β → (c, d) ∈ β → (a, d) ∈ α) := by
  obtain ⟨γ, hγopen, hγdiag, hγsymm, hγcomp⟩ :=
    existsSymmetricSquareNbhdOfDiagonal hαOpen hαDiag
  obtain ⟨β, hβopen, hβdiag, hβsymm, hβcomp⟩ :=
    existsSymmetricSquareNbhdOfDiagonal hγopen hγdiag
  refine ⟨β, hβopen, hβdiag, hβsymm, fun a b c d hab hbc hcd ↦ ?_⟩
  exact hγcomp a c d (hβcomp a b c hab hbc) (hβcomp c d d hcd (hβdiag rfl))

/-- In a compact Hausdorff space, a point off the diagonal is avoided by the closure of some
open neighbourhood of the diagonal -/
lemma existsOpenNbhdDiagonalNotMemClosure
{Z : Type*} [TopologicalSpace Z] [CompactSpace Z] [T2Space Z] {z : Z × Z}
(hz : z ∉ Set.diagonal Z) :
∃ γ : Set (Z × Z), IsOpen γ ∧ Set.diagonal Z ⊆ γ ∧ z ∉ closure γ := by
  obtain ⟨G, H, hG, hH, hΔ, hzH, hGH⟩ :=
    normal_separation isClosed_diagonal isClosed_singleton
      (Set.disjoint_singleton_right.mpr hz)
  refine ⟨G, hG, hΔ, fun hzG ↦ ?_⟩
  have hGHc : closure G ⊆ Hᶜ :=
    closure_minimal (Set.disjoint_left.mp hGH) hH.isClosed_compl
  exact hGHc hzG (hzH rfl)

/-- A neighbourhood `α` of the diagonal of `Z × Z` contains a "box" built from a single
neighbourhood `γ` of the diagonal of `Z`: if the first coordinates of a pair are `γ`-close
and its second coordinates are `γ`-close, then the pair lies in `α`.

This is the step that makes squares of (backward) equicontinuous systems (backward)
equicontinuous.  The swap `((a,b),(c,d)) ↦ ((a,c),(b,d))` carries the diagonal of `Z × Z`
onto `Δ_Z ×ˢ Δ_Z`, and the generalized tube lemma then produces the box. -/
lemma existsDiagonalBoxInDiagonalNbhd
{Z : Type*} [TopologicalSpace Z] [CompactSpace Z] [T2Space Z]
{α : Set ((Z × Z) × (Z × Z))} (hαOpen : IsOpen α) (hαDiag : Set.diagonal (Z × Z) ⊆ α) :
∃ γ : Set (Z × Z), IsOpen γ ∧ Set.diagonal Z ⊆ γ ∧
  ∀ p : (Z × Z) × (Z × Z), (p.1.1, p.2.1) ∈ γ → (p.1.2, p.2.2) ∈ γ → p ∈ α := by
  have hσcont : Continuous
      (fun p : (Z × Z) × (Z × Z) ↦ ((p.1.1, p.2.1), (p.1.2, p.2.2))) :=
    ((continuous_fst.comp continuous_fst).prodMk
      (continuous_fst.comp continuous_snd)).prodMk
      ((continuous_snd.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd))
  have hpre : Set.diagonal Z ×ˢ Set.diagonal Z ⊆
      (fun p : (Z × Z) × (Z × Z) ↦ ((p.1.1, p.2.1), (p.1.2, p.2.2))) ⁻¹' α := by
    rintro ⟨⟨a, a'⟩, ⟨b, b'⟩⟩ ⟨ha, hb⟩
    have ha' : a = a' := ha
    have hb' : b = b' := hb
    subst ha'
    subst hb'
    exact hαDiag (rfl : ((a, b) : Z × Z) = (a, b))
  obtain ⟨u, v, hu, hv, hΔu, hΔv, huv⟩ :=
    generalized_tube_lemma isClosed_diagonal.isCompact isClosed_diagonal.isCompact
      (hαOpen.preimage hσcont) hpre
  refine ⟨u ∩ v, hu.inter hv, fun z hz ↦ ⟨hΔu hz, hΔv hz⟩, ?_⟩
  rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ h1 h2
  exact huv (Set.mk_mem_prod h1.1 h2.2)

/-- The "box" neighbourhood of the diagonal of a product `∀ i, Z i` determined by the finitely
many coordinates in `F` and, in each of those coordinates, a neighbourhood `γ i` of the
diagonal of `Z i`, is open -/
lemma isOpenDiagonalBoxOfPi
{I : Type*} {Z : I → Type*} [∀ i, TopologicalSpace (Z i)]
{F : Set I} (hF : F.Finite) {γ : ∀ i, Set (Z i × Z i)} (hγ : ∀ i, IsOpen (γ i)) :
IsOpen {p : (∀ i, Z i) × (∀ i, Z i) | ∀ i ∈ F, (p.1 i, p.2 i) ∈ γ i} := by
  have hEq : {p : (∀ i, Z i) × (∀ i, Z i) | ∀ i ∈ F, (p.1 i, p.2 i) ∈ γ i}
      = ⋂ i ∈ F, (fun p : (∀ i, Z i) × (∀ i, Z i) ↦ (p.1 i, p.2 i)) ⁻¹' γ i := by
    ext p
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq]
  rw [hEq]
  refine hF.isOpen_biInter fun i _ ↦ (hγ i).preimage ?_
  exact ((continuous_apply i).comp continuous_fst).prodMk
    ((continuous_apply i).comp continuous_snd)

/-- A box built from neighbourhoods of the diagonals of the factors is a neighbourhood of the
diagonal of the product -/
lemma diagonalSubsetDiagonalBoxOfPi
{I : Type*} {Z : I → Type*} [∀ i, TopologicalSpace (Z i)]
{F : Set I} {γ : ∀ i, Set (Z i × Z i)} (hγ : ∀ i, Set.diagonal (Z i) ⊆ γ i) :
Set.diagonal (∀ i, Z i) ⊆ {p : (∀ i, Z i) × (∀ i, Z i) | ∀ i ∈ F, (p.1 i, p.2 i) ∈ γ i} := by
  rintro ⟨x, y⟩ hxy
  have hxy' : x = y := hxy
  subst hxy'
  exact fun i _ ↦ hγ i rfl

/-- In a product of compact Hausdorff spaces, the boxes of the previous two lemmas form a
neighbourhood basis of the diagonal: every neighbourhood `α` of the diagonal of `∀ i, Z i`
contains a box determined by finitely many coordinates.

The proof covers the product by boxes `N z` with `N z × N z ⊆ α`, shrinks each of them
coordinatewise to a box `M z` with `closure (M z)ᵢ ⊆ (N z)ᵢ`, and extracts a finite subcover
`M z`, `z ∈ t`.  The `i`-th neighbourhood of the diagonal is then
`γ i = ⋂ z ∈ t, {q | q.1 ∈ closure (M z)ᵢ → q.2 ∈ (N z)ᵢ}`: if `x` lies in `M z` and `(x, y)`
is `γ`-close in every relevant coordinate, then both `x` and `y` lie in `N z`. -/
lemma existsFiniteBoxInDiagonalNbhdOfPi
{I : Type*} {Z : I → Type*} [∀ i, TopologicalSpace (Z i)] [∀ i, CompactSpace (Z i)]
[∀ i, T2Space (Z i)] {α : Set ((∀ i, Z i) × (∀ i, Z i))} (hαOpen : IsOpen α)
(hαDiag : Set.diagonal (∀ i, Z i) ⊆ α) :
∃ F : Set I, F.Finite ∧ ∃ γ : ∀ i, Set (Z i × Z i),
  (∀ i, IsOpen (γ i)) ∧ (∀ i, Set.diagonal (Z i) ⊆ γ i) ∧
  {p : (∀ i, Z i) × (∀ i, Z i) | ∀ i ∈ F, (p.1 i, p.2 i) ∈ γ i} ⊆ α := by
  classical
  -- around each point `z`, a box `E.pi O` whose square sits in `α`, together with a shrinking
  have key : ∀ z : (∀ i, Z i), ∃ (E : Set I) (O O' : ∀ i, Set (Z i)), E.Finite ∧
      (∀ i, IsOpen (O i)) ∧ (∀ i, IsOpen (O' i)) ∧ (∀ i, z i ∈ O' i) ∧
      (∀ i, closure (O' i) ⊆ O i) ∧ (E.pi O) ×ˢ (E.pi O) ⊆ α := by
    intro z
    have hmem : α ∈ nhds ((z, z) : (∀ i, Z i) × (∀ i, Z i)) := hαOpen.mem_nhds (hαDiag rfl)
    rw [nhds_prod_eq, Filter.mem_prod_iff] at hmem
    obtain ⟨U, hU, V, hV, hUV⟩ := hmem
    have hW : U ∩ V ∈ nhds z := Filter.inter_mem hU hV
    rw [nhds_pi, Filter.mem_pi] at hW
    obtain ⟨E, hEfin, O₀, hO₀, hO₀sub⟩ := hW
    have hshrink : ∀ i, ∃ O O' : Set (Z i), IsOpen O ∧ IsOpen O' ∧ z i ∈ O' ∧
        closure O' ⊆ O ∧ O ⊆ O₀ i := by
      intro i
      obtain ⟨A, hAsub, hAopen, hzA⟩ := mem_nhds_iff.mp (hO₀ i)
      obtain ⟨T, hTnhds, hTclosed, hTA⟩ := exists_mem_nhds_isClosed_subset (hAopen.mem_nhds hzA)
      exact ⟨A, interior T, hAopen, isOpen_interior, mem_interior_iff_mem_nhds.mpr hTnhds,
        (closure_mono interior_subset).trans (hTclosed.closure_subset.trans hTA), hAsub⟩
    choose O O' hO hO' hzO' hclos hOO₀ using hshrink
    refine ⟨E, O, O', hEfin, hO, hO', hzO', hclos, ?_⟩
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    have hsub : E.pi O ⊆ U ∩ V := (Set.pi_mono fun i _ ↦ hOO₀ i).trans hO₀sub
    exact hUV (Set.mk_mem_prod (hsub ha).1 (hsub hb).2)
  choose E O O' hEfin hO hO' hzO' hclos hbox using key
  -- the shrunken boxes cover the product
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (fun z ↦ (E z).pi (O' z))
    (fun z ↦ (isOpen_set_pi (hEfin z) fun i _ ↦ hO' z i).mem_nhds fun i _ ↦ hzO' z i)
  refine ⟨⋃ z ∈ t, E z, t.finite_toSet.biUnion fun z _ ↦ hEfin z,
    fun i ↦ ⋂ z ∈ t, ((closure (O' z i))ᶜ ×ˢ (Set.univ : Set (Z i))
      ∪ (Set.univ : Set (Z i)) ×ˢ O z i), fun i ↦ ?_, fun i ↦ ?_, ?_⟩
  · exact t.finite_toSet.isOpen_biInter fun z _ ↦
      (isClosed_closure.isOpen_compl.prod isOpen_univ).union (isOpen_univ.prod (hO z i))
  · rintro ⟨u, v⟩ huv
    have huv' : u = v := huv
    subst huv'
    simp only [Set.mem_iInter]
    intro z _
    by_cases hu : u ∈ closure (O' z i)
    · exact Set.mem_union_right _ ⟨trivial, hclos z i hu⟩
    · exact Set.mem_union_left _ ⟨hu, trivial⟩
  · intro p hp
    have hp1 : p.1 ∈ (⊤ : Set (∀ i, Z i)) := trivial
    rw [← ht] at hp1
    simp only [Set.mem_iUnion] at hp1
    obtain ⟨z, hzt, hpz⟩ := hp1
    refine hbox z ⟨fun i hi ↦ hclos z i (subset_closure (hpz i hi)), fun i hi ↦ ?_⟩
    have hmem : (p.1 i, p.2 i) ∈ (⋂ z ∈ t, ((closure (O' z i))ᶜ ×ˢ (Set.univ : Set (Z i))
        ∪ (Set.univ : Set (Z i)) ×ˢ O z i)) :=
      hp i (Set.mem_biUnion hzt hi)
    simp only [Set.mem_iInter] at hmem
    rcases hmem z hzt with h | h
    · exact absurd (subset_closure (hpz i hi)) h.1
    · exact h.2

/-- A neighbourhood of the diagonal of a closed subspace `Z ⊆ X` extends to a neighbourhood of
the diagonal of `X`: the extension is `U ∪ (Z ×ˢ Z)ᶜ`, where `U` is any open subset of `X × X`
cutting out `α` in `Z × Z`.  Pairs of points of `Z` lying in the extension lie in `α`. -/
lemma existsDiagonalNbhdExtendingSubspaceDiagonalNbhd
{X : Type*} [TopologicalSpace X] {Z : Set X} (hZClosed : IsClosed Z)
{α : Set (↥Z × ↥Z)} (hαOpen : IsOpen α) (hαDiag : Set.diagonal ↥Z ⊆ α) :
∃ U : Set (X × X), IsOpen U ∧ Set.diagonal X ⊆ U ∧
  ∀ z w : ↥Z, ((z : X), (w : X)) ∈ U → (z, w) ∈ α := by
  obtain ⟨V, hVopen, hVα⟩ :=
    (Topology.IsInducing.subtypeVal.prodMap Topology.IsInducing.subtypeVal).isOpen_iff.mp hαOpen
  refine ⟨V ∪ (Z ×ˢ Z)ᶜ, hVopen.union (hZClosed.prod hZClosed).isOpen_compl, ?_, ?_⟩
  · rintro ⟨x, y⟩ hxy
    have hxy' : x = y := hxy
    subst hxy'
    by_cases hx : x ∈ Z
    · refine Set.mem_union_left _ ?_
      have hmem : ((⟨x, hx⟩ : ↥Z), (⟨x, hx⟩ : ↥Z)) ∈ α := hαDiag rfl
      rw [← hVα] at hmem
      exact hmem
    · exact Set.mem_union_right _ fun hmem ↦ hx hmem.1
  · rintro z w (h | h)
    · rw [← hVα]
      exact h
    · exact absurd (Set.mk_mem_prod z.2 w.2) h

/-- The quotient of a compact Hausdorff space by a closed equivalence relation, endowed with
the quotient topology, is a compact Hausdorff space.

Compactness is immediate from continuity and surjectivity of the quotient map `π`.  For the
Hausdorff property, the fibres `π⁻¹{y}` and `π⁻¹{z}` of two distinct points are disjoint
closed sets, so normality of `X` separates them by disjoint open sets `U` and `V`; the sets
`(π Uᶜ)ᶜ` and `(π Vᶜ)ᶜ` then separate `y` and `z`.  These are open because `π` is a closed
map: the saturation of a closed set `K` is `Prod.snd '' ((K ×ˢ univ) ∩ R)`, which is compact,
hence closed. -/
theorem quotientByCERIsCompactHausdorff
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
{R : X → X → Prop} (hEquiv : Equivalence R)
(hClosed : IsClosed {p : X × X | R p.1 p.2}) :
CompactSpace (Quotient ⟨R, hEquiv⟩) ∧ T2Space (Quotient ⟨R, hEquiv⟩) := by
  set π : X → Quotient ⟨R, hEquiv⟩ := Quotient.mk ⟨R, hEquiv⟩ with hπdef
  have hπcont : Continuous π := continuous_quot_mk
  have hπsurj : Function.Surjective π := Quot.mk_surjective
  have hπeq : ∀ a b : X, π a = π b ↔ R a b := fun a b ↦ Equivalence.quot_mk_eq_iff hEquiv a b
  refine ⟨hπsurj.compactSpace hπcont, ?_⟩
  -- `π` is a closed map
  have hπclosedmap : IsClosedMap π := by
    intro K hK
    have hpre : π ⁻¹' (π '' K)
        = Prod.snd '' ((K ×ˢ (Set.univ : Set X)) ∩ {p : X × X | R p.1 p.2}) := by
      ext x
      constructor
      · rintro ⟨k, hk, hkx⟩
        exact ⟨(k, x), ⟨⟨hk, Set.mem_univ x⟩, (hπeq k x).mp hkx⟩, rfl⟩
      · rintro ⟨⟨k, x'⟩, ⟨⟨hk, -⟩, hR⟩, rfl⟩
        exact ⟨k, hk, (hπeq k x').mpr hR⟩
    have hcompact : IsCompact (π ⁻¹' (π '' K)) := by
      rw [hpre]
      exact ((hK.isCompact.prod isCompact_univ).inter_right hClosed).image continuous_snd
    have hquot : Topology.IsQuotientMap π := isQuotientMap_quot_mk
    exact ((Topology.isQuotientMap_iff_isClosed.mp hquot).2 (π '' K)).mpr hcompact.isClosed
  -- the fibres of distinct points are disjoint closed sets
  have hfibre : ∀ a : X, IsClosed (π ⁻¹' {π a}) := by
    intro a
    have hEq : π ⁻¹' {π a} = (fun x ↦ (x, a)) ⁻¹' {p : X × X | R p.1 p.2} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      exact hπeq x a
    rw [hEq]
    exact hClosed.preimage (continuous_id.prodMk continuous_const)
  rw [t2Space_iff]
  intro y z hyz
  obtain ⟨a, rfl⟩ := hπsurj y
  obtain ⟨b, rfl⟩ := hπsurj z
  have hdisj : Disjoint (π ⁻¹' {π a}) (π ⁻¹' {π b}) := by
    refine Set.disjoint_left.mpr fun w hwa hwb ↦ hyz ?_
    have h1 : π w = π a := hwa
    have h2 : π w = π b := hwb
    rw [← h1, h2]
  obtain ⟨U, V, hUopen, hVopen, hUa, hVb, hUV⟩ :=
    normal_separation (hfibre a) (hfibre b) hdisj
  refine ⟨(π '' Uᶜ)ᶜ, (π '' Vᶜ)ᶜ, (hπclosedmap Uᶜ hUopen.isClosed_compl).isOpen_compl,
    (hπclosedmap Vᶜ hVopen.isClosed_compl).isOpen_compl, ?_, ?_, ?_⟩
  · rintro ⟨w, hwU, hwa⟩
    exact hwU (hUa hwa)
  · rintro ⟨w, hwV, hwb⟩
    exact hwV (hVb hwb)
  · refine Set.disjoint_left.mpr fun w hwU hwV ↦ ?_
    obtain ⟨x, rfl⟩ := hπsurj w
    have hxU : x ∈ U := by
      by_contra hx
      exact hwU ⟨x, hx, rfl⟩
    have hxV : x ∈ V := by
      by_contra hx
      exact hwV ⟨x, hx, rfl⟩
    exact Set.disjoint_left.mp hUV hxU hxV
