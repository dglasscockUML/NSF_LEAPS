module

public import NSFLEAPS._00_Imports.IM_Main

/-!
# Cylinder neighbourhoods of the diagonal

Throughout this project neighbourhoods of the diagonal are used in place of entourages of a
uniform structure; on a compact Hausdorff space the two notions coincide.  This file supplies
the one fact about them that is not immediate, namely that on a closed subspace `W` of a
product `Γ → X` every neighbourhood of the diagonal contains a *cylinder* neighbourhood: one
that constrains only finitely many coordinates, and constrains each of them by a single
neighbourhood `α₀` of the diagonal of `X`.

This is the concrete form of the statement that the product uniformity has a basis of
cylinders, proved here without introducing a `UniformSpace` structure.
(This file was written by Claude Opus 5.)
-/

public section

/-- In a compact Hausdorff space, a pair of distinct points is avoided by some closed
neighbourhood of the diagonal. -/
theorem existsClosedNhdDiagonalNotMem
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] {a b : X} (hab : a ≠ b) :
∃ α₀ : Set (X × X), IsClosed α₀ ∧ Set.diagonal X ⊆ interior α₀ ∧ (a, b) ∉ α₀ := by
  have hdisj : Disjoint (Set.diagonal X) ({(a, b)} : Set (X × X)) := by
    rw [Set.disjoint_singleton_right]
    exact fun h ↦ hab h
  obtain ⟨G, H, hGopen, hHopen, hΔG, habH, hGH⟩ :=
    normal_separation isClosed_diagonal isClosed_singleton hdisj
  refine ⟨Hᶜ, hHopen.isClosed_compl, ?_, ?_⟩
  · exact hΔG.trans (interior_maximal (Set.subset_compl_iff_disjoint_right.mpr hGH) hGopen)
  · simp only [Set.mem_compl_iff, not_not]
    exact habH rfl

/-- Every neighbourhood `α` of the diagonal of a closed subspace `W ⊆ (Γ → X)` contains a
cylinder neighbourhood: there are a finite set `F` of coordinates and an open neighbourhood
`α₀` of the diagonal of `X` such that any two points of `W` agreeing to within `α₀` on `F`
form a pair belonging to `α`. -/
theorem existsCylinderSubsetNhdsSetDiagonal
{Γ : Type*} {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
{W : Set (Γ → X)} (hW : IsClosed W)
{α : Set (↥W × ↥W)} (hα : α ∈ nhdsSet (Set.diagonal ↥W)) :
∃ (F : Finset Γ) (α₀ : Set (X × X)), IsOpen α₀ ∧ Set.diagonal X ⊆ α₀ ∧
  {p : ↥W × ↥W | ∀ f ∈ F, ((p.1 : Γ → X) f, (p.2 : Γ → X) f) ∈ α₀} ⊆ α := by
  classical
  have hWcompact : CompactSpace ↥W := isCompact_iff_compactSpace.mp hW.isCompact
  obtain ⟨U, hUsub, hUopen, hUdiag⟩ := mem_nhdsSet.mp hα
  -- the closed cylinders, indexed by a finite set of coordinates and a closed neighbourhood
  -- of the diagonal of `X`
  set C : Finset Γ × {α₀ : Set (X × X) // IsClosed α₀ ∧ Set.diagonal X ⊆ interior α₀}
      → Set (↥W × ↥W) := fun i ↦
    {p | ∀ f ∈ i.1, ((p.1 : Γ → X) f, (p.2 : Γ → X) f) ∈ (i.2 : Set (X × X))} with hC
  have hCclosed : ∀ i, IsClosed (C i) := by
    intro i
    have heq : C i = ⋂ f ∈ i.1,
        (fun p : ↥W × ↥W ↦ ((p.1 : Γ → X) f, (p.2 : Γ → X) f)) ⁻¹' (i.2 : Set (X × X)) := by
      ext p
      simp [hC]
    rw [heq]
    refine isClosed_biInter fun f _ ↦ IsClosed.preimage ?_ i.2.2.1
    exact ((continuous_apply f).comp (continuous_subtype_val.comp continuous_fst)).prodMk
      ((continuous_apply f).comp (continuous_subtype_val.comp continuous_snd))
  -- the cylinders meet exactly in the diagonal
  have hCinter : (⋂ i, C i) = Set.diagonal ↥W := by
    apply Set.Subset.antisymm
    · intro p hp
      simp only [Set.mem_iInter] at hp
      refine Subtype.ext (funext fun f ↦ ?_)
      by_contra hne
      obtain ⟨α₀, hclosed, hnhd, hnotmem⟩ := existsClosedNhdDiagonalNotMem hne
      exact hnotmem (hp ({f}, ⟨α₀, hclosed, hnhd⟩) f (Finset.mem_singleton_self f))
    · intro p hp
      simp only [Set.mem_iInter]
      intro i f _
      have hp12 : (p.1 : Γ → X) = (p.2 : Γ → X) := by rw [hp]
      rw [hp12]
      exact interior_subset (i.2.2.2 (rfl : ((p.2 : Γ → X) f) = ((p.2 : Γ → X) f)))
  -- compactness produces a single cylinder inside `U`
  have hdisj : Disjoint (Uᶜ : Set (↥W × ↥W)) (⋂ i, C i) := by
    rw [hCinter]
    exact Set.disjoint_compl_left_iff_subset.mpr hUdiag
  obtain ⟨u, hu⟩ := (isClosed_compl_iff.mpr hUopen).isCompact.elim_finite_subfamily_closed
    C hCclosed hdisj
  refine ⟨u.biUnion (fun i ↦ i.1), ⋂ i ∈ u, interior (i.2 : Set (X × X)),
    Set.Finite.isOpen_biInter u.finite_toSet (fun i _ ↦ isOpen_interior), ?_, ?_⟩
  · intro z hz
    simp only [Set.mem_iInter]
    exact fun i _ ↦ i.2.2.2 hz
  · intro p hp
    have hpu : p ∈ ⋂ i ∈ u, C i := by
      simp only [Set.mem_iInter]
      intro i hi f hf
      have hmem := hp f (Finset.mem_biUnion.mpr ⟨i, hi, hf⟩)
      simp only [Set.mem_iInter] at hmem
      exact interior_subset (hmem i hi)
    exact hUsub (by by_contra hpU; exact Set.disjoint_left.mp hu hpU hpu)

/-- A neighbourhood of a point of `↥W × ↥W`, for `W ⊆ (Γ → X)`, contains a basic
neighbourhood constraining only finitely many coordinates.  This is the companion of
`existsCylinderSubsetNhdsSetDiagonal` for neighbourhoods of a point rather than of the
diagonal. -/
theorem existsProdCylinderSubsetNhds
{Γ : Type*} {X : Type*} [TopologicalSpace X] {W : Set (Γ → X)}
{p : ↥W × ↥W} {𝒰 : Set (↥W × ↥W)} (h𝒰 : 𝒰 ∈ nhds p) :
∃ (F : Set Γ) (A B : Γ → Set X), F.Finite ∧
  (∀ f, A f ∈ nhds ((p.1 : Γ → X) f)) ∧ (∀ f, B f ∈ nhds ((p.2 : Γ → X) f)) ∧
  ∀ q : ↥W × ↥W, (∀ f ∈ F, (q.1 : Γ → X) f ∈ A f) → (∀ f ∈ F, (q.2 : Γ → X) f ∈ B f) →
    q ∈ 𝒰 := by
  rw [show p = (p.1, p.2) from rfl, nhds_prod_eq, Filter.mem_prod_iff] at h𝒰
  obtain ⟨S₁, hS₁, S₂, hS₂, hS⟩ := h𝒰
  rw [mem_nhds_subtype] at hS₁ hS₂
  obtain ⟨A', hA', hA'sub⟩ := hS₁
  obtain ⟨B', hB', hB'sub⟩ := hS₂
  rw [nhds_pi, Filter.mem_pi] at hA' hB'
  obtain ⟨F₁, hF₁fin, A, hA, hAsub⟩ := hA'
  obtain ⟨F₂, hF₂fin, B, hB, hBsub⟩ := hB'
  refine ⟨F₁ ∪ F₂, A, B, hF₁fin.union hF₂fin, hA, hB, fun q hq1 hq2 ↦ ?_⟩
  refine hS (Set.mk_mem_prod (hA'sub ?_) (hB'sub ?_))
  · exact hAsub fun f hf ↦ hq1 f (Set.mem_union_left _ hf)
  · exact hBsub fun f hf ↦ hq2 f (Set.mem_union_right _ hf)

end
