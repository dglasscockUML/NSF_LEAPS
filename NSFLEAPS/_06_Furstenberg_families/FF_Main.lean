import NSFLEAPS._03_Family_algebra.FA_Main
import NSFLEAPS._05_Ultrafilters.UF_Main
import NSFLEAPS._06_Furstenberg_families.FF_CXX
import NSFLEAPS._06_Furstenberg_families.FF_Pontryagin

/-!
# Furstenberg families

This file develops the machinery around concrete Furstenberg families:
syndetic sets, thick sets, Delta sets, Bohr sets, etc...
-/

section Abstract_results

/-- If `R(x,U) ∈ F` and `F` is a partition regular family, then there exists
`y ∈ U` such that for all neighborhoods `V ∋ y`, `R(x,V) ∈ F` -/
theorem visitTimeConcentrationForPRFamily
{S : Type*} [Semigroup S] [Nonempty S]
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
(dSystem : DynamicalSystem S X)
(x : X) (U : Set X) (hU : IsClosed U) (hU' : U.Nonempty)
(F : Family S) (hF : isPRFamily F) :
visitTimeSet dSystem x U ∈ F →
∃ (y : X), y ∈ U ∧ (∀ (V : Set X), V ∈ nhds y → visitTimeSet dSystem x V ∈ F) := by
  contrapose
  intro h1
  simp only [not_exists, not_and, not_forall] at h1
  have hU1 : IsCompact U := by
    apply hU.isCompact
  have h2 : ∀ y ∈ U, ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ visitTimeSet dSystem x W ∉ F := by
    intro y hy
    specialize h1 y hy
    obtain ⟨V, hV1, hV2⟩ := h1
    rcases (mem_nhds_iff.mp hV1) with ⟨W, hUsub, hUopen, hyU⟩
    use W
    constructor
    · exact hUopen
    constructor
    · exact hyU
    by_contra h
    have hUV_visitTime : visitTimeSet dSystem x W ⊆ visitTimeSet dSystem x V := by
      apply visitTimesMono
      exact hUsub
    have hV3 : visitTimeSet dSystem x V ∈ F := by
      apply F.upward_closed (visitTimeSet dSystem x W)
      · apply h
      · apply hUV_visitTime
    exact hV2 hV3
  choose f hf using h2
  let g : U → Set X := fun y ↦ f y y.2
  have hgOpen : ∀ y : U, IsOpen (g y) := by
    simp only [Subtype.forall, g]
    intro y hy
    specialize hf y hy
    exact hf.1
  have hExistFin : ∃ G : Finset U, U ⊆ ⋃ y ∈ G, g y := by
    apply IsCompact.elim_finite_subcover
    · exact hU1
    · exact hgOpen
    · intro x hxU
      simp only [Set.iUnion_coe_set, Set.mem_iUnion]
      use x
      use hxU
      simp only [g]
      specialize hf x hxU
      exact hf.2.1
  rcases hExistFin with ⟨G, hG⟩
  have hSub : visitTimeSet dSystem x U ⊆ ⋃ y : G, visitTimeSet dSystem x (g y) := by
    simp only [visitTimeSet]
    intro s hs
    simp only [Set.mem_preimage] at hs
    simp only [Set.mem_iUnion, Set.mem_preimage, Subtype.exists, exists_prop]
    have hSub1 := hG hs
    simp only [Set.iUnion_coe_set, Set.mem_iUnion, exists_prop] at hSub1
    rcases hSub1 with ⟨t, ht1, ht2, ht3⟩
    use t
    use ht1
  have hNo : ∀ y : G, visitTimeSet dSystem x (g y) ∉ F := by
    intro y
    simp only [g]
    specialize hf y y.1.2
    exact hf.2.2
  by_contra hContra
  have hGCard : G.card > 0 := by
    simp only [gt_iff_lt, Finset.card_pos]
    -- a point of `U` lies in some `g y` with `y ∈ G`
    obtain ⟨u, hu⟩ := hU'
    have hmem := hG hu
    simp only [Set.mem_iUnion, exists_prop] at hmem
    obtain ⟨y, hyG, -⟩ := hmem
    exact ⟨y, hyG⟩
  have hIn : ⋃ y : G, visitTimeSet dSystem x (g y) ∈ F := by
    apply F.upward_closed (visitTimeSet dSystem x U) (⋃ y : G, visitTimeSet dSystem x (g y))
    · exact hContra
    · exact hSub
  have hExistOne : ∃ y : G, visitTimeSet dSystem x (g y) ∈ F := by
    have hF := prFamilyIsMultiPR hF
    specialize hF (⋃ y : G, visitTimeSet dSystem x (g y)) hIn ⟨G.card, hGCard⟩
    classical
    have hGNonempty : Nonempty ↥G := ⟨G.equivFin.symm ⟨0, hGCard⟩⟩
    -- colour `s` by the index of some `y ∈ G` with `s ∈ R(x, g y)`
    choose! w hw using fun (s : S) (hs : s ∈ ⋃ y : G, visitTimeSet dSystem x (g y)) ↦
      Set.mem_iUnion.mp hs
    obtain ⟨i, hi⟩ := hF (fun s ↦ G.equivFin (w s))
    -- the monochromatic piece of color `i` sits inside `R(x, g (e.symm i))`
    refine ⟨G.equivFin.symm i, F.upward_closed _ _ hi ?_⟩
    rintro s ⟨hsUnion, hsColour⟩
    have hws : w s = G.equivFin.symm i := (Equiv.eq_symm_apply _).mpr hsColour
    rw [← hws]
    exact hw s hsUnion
  rcases hExistOne with ⟨y, hy⟩
  specialize hNo y
  exact hNo hy

end Abstract_results

section Syndetic_and_thick_sets

/-- The family of syndetic subsets of a semigroup -/
def syndeticFamily
(S : Type*) [Semigroup S] [Nonempty S] : Family S :=
{
  sets := {A : Set S | isSyndetic A}
  upward_closed := by
    intro A B hA hAB
    exact syndeticIsMonotone hA hAB
}

/-- The family of thick subsets of a semigroup -/
def thickFamily
(S : Type*) [Semigroup S] [Nonempty S] : Family S :=
{
  sets := {A : Set S | isThick A}
  upward_closed := by
    intro A B hA hAB
    exact thickIsMonotone hA hAB
}

/-- The families of syndetic sets and thick sets are dual -/
theorem dualSyndeticThick
{S : Type*} [Semigroup S] [Nonempty S] :
(syndeticFamily S)* = thickFamily S :=
  by
    ext A
    have this : Aᶜ ∉ syndeticFamily S ↔ A ∈ thickFamily S := (thickIffComplementNotSyndetic A).symm
    have that := mem_dual_alt (F := syndeticFamily S) (A := A)
    exact Iff.trans that this

/-- Dual of thick family is syndetic family -/
theorem dualThickSyndetic
{S : Type*} [Semigroup S] [Nonempty S] :
(thickFamily S)* = (syndeticFamily S) :=
  by
    ext A
    have this : Aᶜ ∉ thickFamily S ↔ A ∈ syndeticFamily S := by
      have := Iff.not (thickIffComplementNotSyndetic Aᶜ)
      simp only [compl_compl, not_not] at this
      exact this
    have that := mem_dual_alt (F := thickFamily S) (A := A)
    exact Iff.trans that this

/-- If `A` is a thick set and `K` is a finite set of a semigroup `S`,
then `⋂ k ∈ K, (k * ·) ⁻¹' A` is thick -/
theorem inverseDilateCapOfThickIsThick
{S} [Semigroup S] [Nonempty S]
(A : Set S) {hA : isThick A}
(K : Set S) {KIsFinite : K.Finite} :
isThick (⋂ k ∈ K, (k * ·) ⁻¹' A) := by
  intro F hF
  let E := (⋃ k ∈ K, (k * ·) '' F)
  have hFinite: ∀ k ∈ K, ((k * ·) '' F).Finite := by
    intro k hk
    apply hF.image (k * ·)
  have hEFinite: E.Finite := by
    apply KIsFinite.biUnion hFinite
  specialize hA E hEFinite
  obtain ⟨s, hs⟩ := hA
  use s
  intro a ha
  simp only [Set.mem_iInter]
  intro i hi
  simp only [Set.mem_preimage]
  obtain ⟨b, hb1, hb2⟩ := ha
  have hb3 : b * s = a:= by
    simp only at hb2
    exact hb2
  rw [<- hb3]
  apply hs
  unfold E
  simp only [Set.mem_image, Set.mem_iUnion, exists_prop, exists_exists_and_exists_and_eq_and]
  use i
  simp only [hi, true_and]
  use b
  simp only [hb1, true_and]
  apply Semigroup.mul_assoc

/-- This instance makes the semigroup structure on `βS` "canonical" by
making it available to typeclass inference -/
instance
{S : Type*} [Semigroup S] : Semigroup (Ultrafilter S) :=
  Ultrafilter.semigroup

/-- For `A ⊆ S`, the set `closure A ⊆ βS` contains a minimal left ideal
if and only if `A` is thick. -/
theorem thickIffClosureContainsMinLeftIdeal
{S : Type*} [Semigroup S] [Nonempty S]
{H : Set S} :
isThick H ↔
∃ (L : Set (Ultrafilter S)),
isMinLeftIdeal L ∧ L ⊆ closure ((pure : S → Ultrafilter S) '' H) :=
  by
  classical
  constructor
  · intro hH
    -- `L = closure H ∩ ⋂ s, closure (s⁻¹H)`; a point of `L` is an ultrafilter containing
    -- `H` and every `s⁻¹H`
    set L : Set (Ultrafilter S) :=
      closure ((pure : S → Ultrafilter S) '' H) ∩
        ⋂ s : S, closure ((pure : S → Ultrafilter S) '' ((leftMult s) ⁻¹' H)) with hLdef
    have hmem : ∀ p : Ultrafilter S,
        p ∈ L ↔ (H ∈ p ∧ ∀ s : S, (leftMult s) ⁻¹' H ∈ p) := by
      intro p
      simp only [hLdef, Set.mem_inter_iff, Set.mem_iInter, memClosurePureIff]
    -- thickness gives the finite intersection property, so `L` is non-empty
    have hLNonempty : L.Nonempty := by
      refine isClosed_closure.isCompact.inter_iInter_nonempty _ (fun _ ↦ isClosed_closure) ?_
      intro u
      obtain ⟨a⟩ : Nonempty S := inferInstance
      obtain ⟨r, hr⟩ := hH (insert a ((fun x : S ↦ x * a) '' (u : Set S)))
        ((u.finite_toSet.image _).insert _)
      -- `t = a * r` lies in `H`, and in `f⁻¹H` for every `f ∈ u`
      refine ⟨pure (a * r), ?_, ?_⟩
      · refine (memClosurePureIff H _).mpr ?_
        simp only [Ultrafilter.mem_pure]
        exact hr ⟨a, Set.mem_insert _ _, rfl⟩
      · simp only [Set.mem_iInter]
        intro f hf
        refine (memClosurePureIff _ _).mpr ?_
        simp only [Ultrafilter.mem_pure, Set.mem_preimage, leftMult]
        rw [← mul_assoc]
        exact hr ⟨f * a, Set.mem_insert_of_mem _ ⟨f, hf, rfl⟩, rfl⟩
    -- `L` is a left ideal of `βS`
    have hLIdeal : isLeftIdeal L := by
      refine ⟨hLNonempty, ?_⟩
      rintro q w ⟨p, hp, rfl⟩
      obtain ⟨hpH, hpS⟩ := (hmem p).mp hp
      refine (hmem (q * p)).mpr ⟨?_, fun s ↦ ?_⟩
      · rw [ultraProductDescription]
        exact Filter.univ_mem' fun u ↦ hpS u
      · rw [ultraProductDescription]
        refine Filter.univ_mem' fun u ↦ ?_
        have hset : {t : S | u * t ∈ (leftMult s) ⁻¹' H} = (leftMult (s * u)) ⁻¹' H := by
          ext t
          simp only [Set.mem_ofPred_eq, Set.mem_preimage, leftMult, mul_assoc]
        change {t : S | u * t ∈ (leftMult s) ⁻¹' H} ∈ p
        rw [hset]
        exact hpS (s * u)
    -- every left ideal contains a minimal left ideal
    obtain ⟨M, hMmin, hML⟩ := leftIdealContainsMinLeftIdeal (S := Ultrafilter S) L (hL := hLIdeal)
    refine ⟨M, hMmin, hML.trans ?_⟩
    rw [hLdef]
    exact Set.inter_subset_left
  · rintro ⟨L, hLmin, hLH⟩ F hF
    obtain ⟨p, hp⟩ := hLmin.1.1
    -- `L ⊆ f⁻¹L ⊆ f⁻¹(closure H)`, so every `f⁻¹H` belongs to `p`
    have hfp : ∀ f : S, (leftMult f) ⁻¹' H ∈ p := by
      intro f
      have hfpL : (pure f : Ultrafilter S) * p ∈ L := hLmin.1.2 (pure f) ⟨p, hp, rfl⟩
      exact (membershipInLeftMultByPrincipal f H p).mp ((memClosurePureIff H _).mp (hLH hfpL))
    -- a finite intersection of members of the ultrafilter `p` is non-empty
    obtain ⟨s, hs⟩ :=
      Ultrafilter.nonempty_of_mem ((Filter.biInter_mem hF).mpr fun f _ ↦ hfp f)
    refine ⟨s, ?_⟩
    rintro w ⟨f, hf, rfl⟩
    simp only [Set.mem_iInter] at hs
    exact hs f hf

/-- The closure in `βS` of a syndetic subset of a semigroup `S`
has non-empty intersection with every left ideal -/
theorem syndeticClosureMeetsEveryIdeal
{S : Type*} [Semigroup S] [Nonempty S]
{A : Set S} (hA : isSyndetic A) :
∀ (L : Set (Ultrafilter S)),
isLeftIdeal L → (L ∩ closure ((pure : S → Ultrafilter S) '' A)).Nonempty :=
  by
  intro L hL
  -- `B = S \ A` is not thick, since a syndetic set meets every thick set
  have hBNotThick : ¬ isThick (Aᶜ : Set S) := by
    intro hB
    obtain ⟨x, hxA, hxB⟩ := syndeticThickIntersect A Aᶜ hA hB
    exact hxB hxA
  -- so `closure B` contains no minimal left ideal, and hence no left ideal at all
  have hLNotSub : ¬ (L ⊆ closure ((pure : S → Ultrafilter S) '' (Aᶜ : Set S))) := by
    intro hsub
    obtain ⟨M, hMmin, hML⟩ := leftIdealContainsMinLeftIdeal (S := Ultrafilter S) L (hL := hL)
    exact hBNotThick (thickIffClosureContainsMinLeftIdeal.mpr ⟨M, hMmin, hML.trans hsub⟩)
  -- a point of `L` outside `closure B` contains `A`, so it lies in `closure A`
  rw [Set.not_subset] at hLNotSub
  obtain ⟨p, hpL, hpB⟩ := hLNotSub
  rw [memClosurePureIff] at hpB
  refine ⟨p, hpL, (memClosurePureIff A p).mpr ?_⟩
  by_contra hpA
  exact hpB (Ultrafilter.compl_mem_iff_notMem.mpr hpA)

/-- If `H ⊆ S` is thick, there exists a minimal idempotent `p ∈ βS` such that
for all finite `F ⊆ S`, `∩ f ∈ F, f⁻¹H ∈ p` -/
theorem minIdempotentWitnessesShiftIntersectionLargeness
{S : Type*} [Semigroup S] [Nonempty S]
(H : Set S) (hH : isThick H) :
∃ (p : Ultrafilter S), p ∈ closure ((pure : S → Ultrafilter S) '' H) ∧
isMinimalUltrafilter p ∧ p * p = p ∧ ∀ (F : Set S), F.Finite → (⋂ f ∈ F, (leftMult f) ⁻¹' H) ∈ p :=
  by
  -- `closure H` contains a minimal left ideal `L`, which contains an idempotent `p`
  obtain ⟨L, hLmin, hLH⟩ := thickIffClosureContainsMinLeftIdeal.mp hH
  obtain ⟨p, hpL, hpIdem⟩ := leftIdealContainsIdempotent (S := Ultrafilter S) L (hL := hLmin.1)
  refine ⟨p, hLH hpL, ⟨L, hLmin, hpL⟩, hpIdem, fun F hF ↦ ?_⟩
  -- `p ∈ L ⊆ closure (f⁻¹H)` for every `f`, and `p` is closed under finite intersections
  refine (Filter.biInter_mem hF).mpr fun f _ ↦ ?_
  have hfpL : (pure f : Ultrafilter S) * p ∈ L := hLmin.1.2 (pure f) ⟨p, hpL, rfl⟩
  exact (membershipInLeftMultByPrincipal f H p).mp ((memClosurePureIff H _).mp (hLH hfpL))

/-- Given a family `F`, a set `A` is strongly piecewise-`F` if
for all thick sets `H ⊆ S`, there exists a thick set `H' ⊆ S` and a
set `B ∈ F` such that `A ∩ H = B ∩ H'` -/
noncomputable
def stronglyPW
{S : Type*} [Semigroup S] [Nonempty S] (F : Family S) :
Family S :=
syndeticFamily S ⋏ (thickFamily S ⋎ F)

/-- Given a family `F`, a set `A` is very strongly piecewise-`F` if
for all thick sets `H ⊆ S`, there exists a thick set `H' ⊆ H` and a
set `B ∈ F` such that `A ∩ H' = B ∩ H'` -/
noncomputable
def veryStronglyPW
{S : Type*} [Semigroup S] [Nonempty S] (F : Family S) :
Family S :=
Family.iInter (fun (t : (thickFamily S).sets) ↦ (capFamily (thickFamily S) t) ⋎ F)

/-- If `H ⊆ S` is thick, then `(T∩H)* ⋏ F ⊆ F` for every family `F`, where `T∩H` is
the family of sets `A ⊆ S` for which `A ∩ H` is thick -/
lemma capThickDualMeetContained
{S : Type*} [Semigroup S] [Nonempty S] {H : Set S} (hH : isThick H) (F : Family S) :
(capFamily (thickFamily S) H)* ⋏ F ⊆ F := by
  -- `H ∈ T∩H`, so `T∩H ≠ ∅`, whereby `(T∩H)* ≠ P(S)`
  have hfull : (capFamily (thickFamily S) H)* ≠ fullFam S := by
    intro hfull
    obtain ⟨x, hx, -⟩ := (fullFamEquiv _).mp hfull H
      (show H ∩ H ∈ thickFamily S by rwa [Set.inter_self])
    simp at hx
  -- so Theorem 3.3 applies
  rw [familyMeetIsCommutative]
  exact familyMeetContainedInIntersection F _ hfull

end Syndetic_and_thick_sets


section Delta_sets

/-- A set `A ⊆ S` is Delta_0 if for all `n`, there exist `s_1, ..., s_n ∈ S`
such that for all `1 ≤ i < j ≤ k`, `s_j ∈ s_i A` -/
def isDeltaZero
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∀ (k : ℕ), ∃ (s : Fin k → S), ∀ (i j : Fin k), i < j → (s j) ∈ ((s i) * ·) '' A

/-- If `A ⊆ S` is Delta_0 and `A ⊆ B`, then `B` is Delta_0. -/
theorem deltaZeroIsMonotone
{S : Type*} [Semigroup S] [Nonempty S]
{A B : Set S} (hA : isDeltaZero A) (hAB : A ⊆ B) :
isDeltaZero B := by
  intro k
  specialize hA k
  obtain ⟨s, hs⟩ := hA
  use s
  intro i j hij
  specialize hs i j hij
  simp only [Set.mem_image] at hs
  obtain ⟨x, hx1, hx2⟩ := hs
  simp only [Set.mem_image]
  use x
  constructor
  · exact hAB hx1
  · exact hx2

/-- The family of Delta_0 subsets of a semigroup -/
def deltaZeroFamily
(S : Type*) [Semigroup S] [Nonempty S] : Family S :=
{
  sets := {A : Set S | isDeltaZero A}
  upward_closed := by
    intro A B hA hAB
    exact deltaZeroIsMonotone hA hAB
}

/-- A set `A ⊆ S` is Delta if there exist `s_1, s_2, ... ∈ S`
such that for all `1 ≤ i < j`, `s_j ∈ s_i A` -/
def isDelta
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∃ (s : ℕ → S), ∀ (i j : ℕ), i < j → (s j) ∈ ((s i) * ·) '' A

/-- If `A ⊆ S` is Delta and `A ⊆ B`, then `B` is Delta. -/
theorem deltaIsMonotone
{S : Type*} [Semigroup S] [Nonempty S]
{A B : Set S} (hA : isDelta A) (hAB : A ⊆ B) :
isDelta B := by
  obtain ⟨s, hs⟩ := hA
  use s
  intro i j hij
  specialize hs i j hij
  simp only [Set.mem_image] at hs
  obtain ⟨x, hx1, hx2⟩ := hs
  simp only [Set.mem_image]
  use x
  constructor
  · exact hAB hx1
  · exact hx2

/-- The family of Delta subsets of a semigroup -/
def deltaFamily
(S : Type*) [Semigroup S] [Nonempty S] : Family S :=
{
  sets := {A : Set S | isDelta A}
  upward_closed := by
    intro A B hA hAB
    exact deltaIsMonotone hA hAB
}

/-- In a semigroup S, Delta sets are Delta_0 -/
theorem deltaFamilyContainedInDeltaZeroFamily
{S : Type*} [Semigroup S] [Nonempty S] :
deltaFamily S ⊆ deltaZeroFamily S := by
  intro A hA
  obtain ⟨x, hx⟩ := hA
  simp only [SetLike.mem_coe]
  have reduce_goal: isDeltaZero A → A ∈ deltaZeroFamily S := by
    intro hA2
    simpa
  apply reduce_goal
  unfold isDeltaZero
  intro k
  let s : Fin k → S := fun i ↦ x (i)
  use s
  intro i j hij
  specialize hx i j hij
  simpa

end Delta_sets

section dcS_sets

/-- A subset `A` of a semigroup `S` is a dcS set (dynamically central syndetic)
if there exists a minimal ultrafilter `p` and an open set `U ⊆ βS` containing `p`
such that the times of visits of `p` to `U` is contained in `A` -/
def isdcSSet
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∃ (p : Ultrafilter S) (_ : isMinimalUltrafilter p),
∃ (U : Set (Ultrafilter S)) (_ : IsOpen U) (_ : p ∈ U),
visitTimeSet (ultrafilterSystem S) p U ⊆ A

/-- The property of being a `dcS` set is upward closed -/
theorem dcSIsMonotone
{S : Type*} [Semigroup S] [Nonempty S]
{A B : Set S} (hA : isdcSSet A) (hAB : A ⊆ B) :
isdcSSet B := by
  obtain ⟨p, hp, U, hU1, hU2, hU3⟩ := hA
  use p
  use hp
  use U
  use hU1
  use hU2
  exact Set.Subset.trans hU3 hAB

/-- The family of `dcS` sets -/
def dcSFamily
(S : Type*) [Semigroup S] [Nonempty S] :
Family S :=
{
  sets := {A : Set S | isdcSSet A}
  upward_closed := by
    intro A B hA hAB
    exact dcSIsMonotone hA hAB
}

/-- If a set `A ⊆ S` is a `dcS` set, then it contains the times of
returns of a point to a neighborhood of itself in a minimal `S`-system.
(Note that the compact Hausdorff space `X` has the same type as `S`.) -/
theorem isdcSSetImpliesVisitsFromCompactHausdorffSpace
{S : Type u} [Semigroup S] [Nonempty S] (A : Set S) :
isdcSSet A → ∃ (X : Type u) (_ : TopologicalSpace X)
(_ : CompactSpace X) (_ : T2Space X) (_ : Nonempty X)
(dSystem : DynamicalSystem S X) (_ : isMinimalSystem dSystem)
(x : X) (U : Set X) (_ : x ∈ U) (_ : IsOpen U),
visitTimeSet dSystem x U ⊆ A := by
  intro hdcSA
  obtain ⟨p, hp, U, hU1, hU2, hU3⟩ := hdcSA
  let X := orbitClosure (ultrafilterSystem S) p
  have Xprops := orbitClosureIsNonemptyCompactT2InvariantSubset (ultrafilterSystem S) p
  use X
  use inferInstance
  let csX : CompactSpace ↑X := isCompact_iff_compactSpace.mp Xprops.2.1
  use csX
  use inferInstance
  let nonX : Nonempty ↑X := Set.Nonempty.coe_sort Xprops.1
  use nonX
  let dSystem := fromNonemptyCompactT2InvariantSubsetToSystem (ultrafilterSystem S) Xprops
  use dSystem
  have XisMinSubset := orbitClosureOfURPointIsMinimalSubset
    (ultrafilterSystem S) ((ultrafilterMinimalIffUnifRec p).mp hp)
  have dSystemIsMin : isMinimalSystem dSystem :=
    (minimalSubsetIffMinimalSubsystem (ultrafilterSystem S) Xprops).mp XisMinSubset
  use dSystemIsMin
  have pinX : p ∈ X :=
    URPointBelongsToOrbitClosure (ultrafilterSystem S) ((ultrafilterMinimalIffUnifRec p).mp hp)
  use ⟨p, pinX⟩
  let V : Set ↑X := {x : ↑X | x.1 ∈ U}
  have Vnonempty : V.Nonempty := by
    use ⟨p, pinX⟩
    exact hU2
  use V
  use by exact hU2
  have Vopen : IsOpen V := hU1.preimage continuous_subtype_val
  use Vopen
  have visitInVisit : visitTimeSet dSystem ⟨p, pinX⟩ V ⊆
    visitTimeSet (ultrafilterSystem S) p U := by
      intro s hs
      unfold visitTimeSet at hs
      unfold visitTimeSet
      exact Set.mem_preimage.mpr hs
  exact Set.Subset.trans visitInVisit hU3

/-- If a set `A ⊆ S` contains the times of returns of a `UR` point to a
neighborhood of itself in an `S`-system, then it is a `dcS` set.
(Note that there are two universe-level metavariables here, one for `S`
and the other for `X`.) -/
theorem returnTimesImpliesdcS
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
(∃ (X : Type*) (_ : TopologicalSpace X)
(_ : CompactSpace X) (_ : T2Space X) (_ : Nonempty X)
(dSystem : DynamicalSystem S X) (x : X) (_ : isUniformlyRecurrent dSystem x)
(U : Set X) (_ : x ∈ U) (_ : IsOpen U),
visitTimeSet dSystem x U ⊆ A) → isdcSSet A := by
  intro hA
  obtain ⟨X,_,_,_,_,dSystem,x,xUR,U,xInU,Uopen,AhasVisits⟩ := hA
  let Z := orbitClosure dSystem x
  have xInZ := URPointBelongsToOrbitClosure dSystem xUR
  let V : Set ↑Z := {z : ↑Z | z.1 ∈ U}
  have Vnonempty : V.Nonempty := by
    use ⟨x, xInZ⟩
    exact xInU
  have Vopen : IsOpen V := Uopen.preimage continuous_subtype_val
  have Zpresystem : isNonemptyCompactT2InvariantSubset dSystem Z :=
    orbitClosureIsNonemptyCompactT2InvariantSubset dSystem x
  let dSystemZ := fromNonemptyCompactT2InvariantSubsetToSystem dSystem Zpresystem
  let _ : Nonempty ↥Z := (fun ⟨x, xInZ⟩ => ⟨⟨x, xInZ⟩⟩) Zpresystem.1
  let _ : CompactSpace ↥Z := isCompact_iff_compactSpace.mp Zpresystem.2.1
  have hZmin : isMinimalSystem dSystemZ := (minimalSubsetIffMinimalSubsystem
    dSystem Zpresystem).mp (orbitClosureOfURPointIsMinimalSubset dSystem xUR)
  have := (minimalIffDenseOrbits dSystemZ).mp hZmin ⟨x,xInZ⟩
  let fmap := fun p ↦ (ultraAction dSystemZ).map p ⟨x,xInZ⟩
  have uFactorMap : isFactorMap (ultrafilterSystem S) dSystemZ fmap :=
    ultraFactorMap dSystemZ ((minimalIffDenseOrbits dSystemZ).mp hZmin ⟨x,xInZ⟩)
  obtain ⟨p,hp,pUR⟩ :=liftUniformRecurrentPoint
    uFactorMap ⟨x,xInZ⟩ (minimalImpliesUniformlyRecurrent dSystemZ (hMin := hZmin) ⟨x,xInZ⟩)
  use p
  use (ultrafilterMinimalIffUnifRec p).mpr pUR
  use fmap ⁻¹' V
  use Continuous.isOpen_preimage uFactorMap.1 V Vopen
  have fmappinV : fmap p ∈ V := by
    rw [hp]
    exact xInU
  use fmappinV
  have preimageVisits := visitTimesThruFactorMap uFactorMap p V
  rw [hp] at preimageVisits
  rw [preimageVisits]
  exact AhasVisits


/-- A subset `A` of a semigroup `S` is a set of pointwise recurrence if it
has non-empty intersection with every `dcS` subset of `S` -/
def isdcTSet
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
A ∈ (dcSFamily S)*

/-- The family of dcT subsets of a semigroup -/
def dcTFamily
(S : Type*) [Semigroup S] [Nonempty S] :
Family S :=
(dcSFamily S)*

/-- If `A ⊆ S` is a set of pointwise recurrence and `A ⊆ B`, then `B`
is a set of pointwise recurrence. -/
theorem dcTIsMonotone
(S : Type*) [Semigroup S] [Nonempty S]
{A B : Set S} (hA : isdcTSet A) (hAB : A ⊆ B) :
isdcTSet B :=
(dcTFamily S).2 A B hA hAB

/-- If A is a dcT set, then A contains a time of return of any point
to any neighborhood of itself in any minimal system -/
theorem dcTImpliesTimeOfRecurrenceForMinSystems
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
isdcTSet A → ∀ (X : Type*) (_ : TopologicalSpace X)
(_ : CompactSpace X) (_ : T2Space X) (_ : Nonempty X)
(dSystem : DynamicalSystem S X) (_ : isMinimalSystem dSystem)
(x : X) (U : Set X) (_ : x ∈ U) (_ : IsOpen U), ∃ (s : S) (_ : s ∈ A),
dSystem.map s x ∈ U := by
  intro hA X Xtop Xcmpt XT2 XNon dSystem hMin x U xInU UOpen
  have : ∀ (B : Set S), ((∃ (X : Type u_2) (_ : TopologicalSpace X)
    (_ : CompactSpace X) (_ : T2Space X) (_ : Nonempty X)
    (dSystem : DynamicalSystem S X) (x : X) (_ : isUniformlyRecurrent dSystem x)
    (U : Set X) (_ : x ∈ U) (_ : IsOpen U),
    visitTimeSet dSystem x U ⊆ B) → isdcSSet B) := returnTimesImpliesdcS
  have visitdcS : isdcSSet (visitTimeSet dSystem x U) := by
    apply this (visitTimeSet dSystem x U)
    have xUR : isUniformlyRecurrent dSystem x :=
      minimalImpliesUniformlyRecurrent dSystem (hMin := hMin) x
    use X, Xtop, Xcmpt, XT2, XNon, dSystem, x, xUR, U, xInU, UOpen
  obtain ⟨s, hsA, hsV⟩ := hA (visitTimeSet dSystem x U) visitdcS
  use s, hsA, hsV

/-- If A contains a time of return of any point to any neighborhood
of itself in a minimal system (with phase space X : Type u, where S : Type u),
then A is a dcT set. -/
theorem timeOfRecurrenceForMinSystemsImpliesdcT
{S : Type u} [Semigroup S] [Nonempty S] (A : Set S) :
(∀ (X : Type u) (_ : TopologicalSpace X)
(_ : CompactSpace X) (_ : T2Space X) (_ : Nonempty X)
(dSystem : DynamicalSystem S X) (_ : isMinimalSystem dSystem)
(x : X) (U : Set X) (_ : x ∈ U) (_ : IsOpen U), ∃ (s : S) (_ : s ∈ A),
dSystem.map s x ∈ U) → isdcTSet A := by
  intro h B BdcS
  obtain ⟨X, Xtop, Xcmpt, XT2, XNon, dSystem, hMin,
    x, U, xInU, UOpen, visitsInB⟩ := isdcSSetImpliesVisitsFromCompactHausdorffSpace B BdcS
  obtain ⟨s,sinA,smap⟩ := h X Xtop Xcmpt XT2 XNon dSystem hMin x U xInU UOpen
  have sinB : s ∈ B := by
    apply visitsInB
    exact smap
  use s
  exact ⟨sinA, sinB⟩

end dcS_sets

section IP_sets

/-- A subset `A` of a semigroup `S` is an IP set if it belongs to an
idempotent ultrafilter on `S` -/
def isIP
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∃ (p : Ultrafilter S) (_ : p * p = p), A ∈ p

/-- The property of being an `IP` set is upward closed -/
theorem IPIsMonotone
{S : Type*} [Semigroup S] [Nonempty S]
{A B : Set S} (hA : isIP A) (hAB : A ⊆ B) :
isIP B := by
  obtain ⟨p, hip, rest⟩ := hA
  use p
  use hip
  exact Filter.mem_of_superset rest hAB

/-- The family of `IP` sets -/
def IPFamily
(S : Type*) [Semigroup S] [Nonempty S] :
Family S :=
{
  sets := {A : Set S | isIP A}
  upward_closed := by
    intro A B hA hAB
    exact IPIsMonotone hA hAB
}

end IP_sets

section central_sets

/-- A subset `A` of a semigroup `S` is a central set if it belongs to a
minimal idempotent ultrafilter on `S` -/
def isCentral
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
∃ (p : Ultrafilter S) (_ : isMinimalUltrafilter p) (_ : p * p = p), A ∈ p

/-- The property of being a `central` set is upward closed -/
theorem centralIsMonotone
{S : Type*} [Semigroup S] [Nonempty S]
{A B : Set S} (hA : isCentral A) (hAB : A ⊆ B) :
isCentral B := by
  obtain ⟨p, hp, hip, rest⟩ := hA
  use p
  use hp
  use hip
  exact Filter.mem_of_superset rest hAB

/-- The family of `central` sets -/
def centralFamily
(S : Type*) [Semigroup S] [Nonempty S] :
Family S :=
{
  sets := {A : Set S | isCentral A}
  upward_closed := by
    intro A B hA hAB
    exact centralIsMonotone hA hAB
}

/-- A `central` set is an `IP` set -/
theorem centralIsIP
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
isCentral A → isIP A := by
  intro hA
  obtain ⟨p,-,pIdemp,Ainp⟩ := hA
  use p

/-- The family of `central` sets is contained in the family of `IP` sets -/
theorem centralFamilyContainedInIPFamily
(S : Type*) [Semigroup S] [Nonempty S] :
centralFamily S ⊆ IPFamily S := by
  intro A hA
  exact centralIsIP A hA

/- The following theorems taken together show that TFAE:
  1. A is central
  2. A = R(x,U), where x is proximal to an S-uniformly recurrent point in the open set U
  3. A contains the intersection of a dcS set with a thick set -/

/-- If `A ⊆ S` is central, then `A = R(x,U)` where `x` is proximal
to an `S`-uniformly recurrent point in the open set `U` -/
theorem centralSetsAreVisitsOfPtToProxURPoint
{S : Type u} [Semigroup S] [Nonempty S] (A : Set S) :
isCentral A → ∃ (X : Type u) (_ : TopologicalSpace X)
(_ : CompactSpace X) (_ : T2Space X) (_ : Nonempty X)
(dSystem : DynamicalSystem S X) (x y : X) (_ : isUniformlyRecurrent dSystem y)
(_ : proximal dSystem x y) (U : Set X) (_ : y ∈ U) (_ : IsOpen U),
visitTimeSet dSystem x U = A := by
  intro hA
  obtain ⟨p,pMin,pIdemp,Ainp⟩ := hA
  let : SemigroupHom (WithOne.coe : S → WithOne S) :=
  {
    hom_prop := fun s1 s2 ↦ WithOne.coe_mul s1 s2
  }
  let dSystemMS := homDynamicalSystem (WithOne.coe : S → WithOne S) (ultrafilterSystem (WithOne S))
  let de := (pure : WithOne S → Ultrafilter (WithOne S)) (1 : WithOne S)
  let pde := (ultraAction dSystemMS).map p de
  have deProxpde : proximal dSystemMS de pde := pointAndUltraImageAreProximal dSystemMS de pIdemp
  have pdeIsUR : isUniformlyRecurrent dSystemMS pde :=
    minUltraImageIsUniformlyRecurrent dSystemMS de pMin
  let iAbar := {q : Ultrafilter (WithOne S) | WithOne.coe '' A ∈ q}
  have visitsToiAisA : visitTimeSet dSystemMS de iAbar = A := by
    ext s
    calc
      s ∈ visitTimeSet dSystemMS de iAbar ↔ dSystemMS.map s de ∈ iAbar := Eq.to_iff rfl
      _ ↔ (pure : WithOne S → Ultrafilter (WithOne S)) (WithOne.coe s) ∈ iAbar := by
        have : dSystemMS.map s de = pure ↑s := by
          unfold de dSystemMS
          exact Ultrafilter.eq_of_le fun ⦃U⦄ a ↦ a
        rw [this]
      _ ↔ WithOne.coe s ∈ WithOne.coe '' A := by
        unfold iAbar
        exact Set.MapsTo.mem_iff (fun ⦃x⦄ a ↦ a) fun ⦃x⦄ a ↦ a
      _ ↔ s ∈ A := Function.Injective.mem_set_image WithOne.coe_injective
  have sufficient := visitTimeSetInUltraImpliesUltraActInClosure dSystemMS de iAbar p
  have iAbarclosed : iAbar = closure iAbar := by
    have := ultrafilter_isClosed_basic (WithOne.coe '' A)
    exact (closure_eq_iff_isClosed.mpr this).symm
  have iAbaropen : IsOpen iAbar := ultrafilter_isOpen_basic (WithOne.coe '' A)
  rw [←iAbarclosed] at sufficient
  have pdeIniAbar : pde ∈ iAbar := by
    apply sufficient
    rw [visitsToiAisA]
    exact Ainp
  use Ultrafilter (WithOne S)
  use by infer_instance
  use by infer_instance
  use by infer_instance
  use by infer_instance
  use dSystemMS
  use de
  use pde
  use pdeIsUR
  use deProxpde
  use iAbar

/-- If `A = R(x,U)` where `x` is proximal to an `S`-uniformly
recurrent point in the open set `U`, then `A` contains `dcS` intersect `thick` -/
theorem visitsOfPtToProxURPointAredcSCapThick
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
(∃ (X : Type*) (_ : TopologicalSpace X)
(_ : CompactSpace X) (_ : T2Space X) (_ : Nonempty X)
(dSystem : DynamicalSystem S X) (x y : X) (_ : isUniformlyRecurrent dSystem y)
(_ : proximal dSystem x y) (U : Set X) (_ : y ∈ U) (_ : IsOpen U),
visitTimeSet dSystem x U = A) → (∃ (B : Set S) (_ : isdcSSet B),
∃ (H : Set S) (_ : isThick H), B ∩ H ⊆ A) := by
  intro hA
  obtain ⟨X,Xts,Xcs,Xt2,Xnon,dSystem,x,y,yIsUR,xyProx,U,yInU,UIsOpen,visitTimesIsA⟩ := hA
  obtain ⟨V,VIsOpen,yInV,α,αIsOpen,αContainsDiag,VαProp⟩ :=
    nbhdOfDiagForcesOtherSetContainment UIsOpen yInU
  let yToV := visitTimeSet dSystem y V
  use yToV
  have yToVisdcS : isdcSSet yToV := by
    apply returnTimesImpliesdcS
    use X, Xts, Xcs, Xt2, Xnon, dSystem, y, yIsUR, V, yInV, VIsOpen
  use yToVisdcS
  let xyToα := visitTimeSet (diagDynamicalSystem dSystem dSystem) ⟨x,y⟩ α
  use xyToα
  have xyToαThick : isThick xyToα :=
    proxPairVisitsDiagAlongThickSet dSystem xyProx α αIsOpen αContainsDiag
  use xyToαThick
  let xToU := visitTimeSet dSystem x U
  have visitContainment : yToV ∩ xyToα ⊆ xToU := by
    intro s ⟨hs1,hs2⟩
    apply VαProp (dSystem.map s x) (dSystem.map s y)
    · exact hs2
    · exact hs1
  rw [←visitTimesIsA]
  exact visitContainment

/-- A `dcS` subset of `S` belongs to a syndetic, idempotent filter on `S` -/
lemma dcSBelongsToSyndeticIdempotentFilter
{S : Type*} [Semigroup S] [Nonempty S] {A : Set S} (hA : isdcSSet A) :
∃ (F : Set (Set S)) (_ : F.Nonempty)
(_ : ∀ (A B : Set S), A ∈ F → B ∈ F → A ∩ B ∈ F)
(_ : ∀ (A B : Set S), A ∈ F → A ⊆ B → B ∈ F)
(_ : ∀ (A : Set S), A ∈ F → isSyndetic A)
(_ : ∀ (A : Set S), A ∈ F → {s : S | (s * ·) ⁻¹' A ∈ F} ∈ F),
A ∈ F := by --Define F to be up-closure of all R(x,U), where V is open nbhd of p
  obtain ⟨p,pMin,U,UOpen,pInU,visitsInA⟩ := hA
  let F := {B : Set S | ∃ (V : Set (Ultrafilter S)) (_ : IsOpen V)
    (_ : p ∈ V), visitTimeSet (ultrafilterSystem S) p V ⊆ B}
  use F
  have AinF : A ∈ F := by
    use U
  use Set.nonempty_of_mem AinF
  have Ffilt : ∀ (A B : Set S), A ∈ F → B ∈ F → A ∩ B ∈ F := by
    intro A B hA hB
    obtain ⟨V1,V1Open,pInV1,visitsInA⟩ := hA
    obtain ⟨V2,V2Open,pInV2,visitsInB⟩ := hB
    let V := V1 ∩ V2
    have Vopen : IsOpen V := by
      exact IsOpen.inter V1Open V2Open
    have pinV : p ∈ V := by
      exact Set.mem_inter pInV1 pInV2
    have interrw : (visitTimeSet (ultrafilterSystem S) p V1) ∩
      (visitTimeSet (ultrafilterSystem S) p V2) =
        visitTimeSet (ultrafilterSystem S) p V := by
          exact Eq.symm (Set.Subset.antisymm (fun ⦃a⦄ a_1 ↦ a_1) fun ⦃a⦄ a_1 ↦ a_1)
    have easy : (visitTimeSet (ultrafilterSystem S) p V1) ∩
      (visitTimeSet (ultrafilterSystem S) p V2) ⊆ A ∩ B := by
        exact Set.inter_subset_inter visitsInA visitsInB
    rw [interrw] at easy
    use V
  use Ffilt
  have Fup : ∀ (A B : Set S), A ∈ F → A ⊆ B → B ∈ F := by
    intro A B hA hAB
    obtain ⟨V,VOpen,pInV,visitsInA⟩ := hA
    use V
    use VOpen
    use pInV
    use subset_trans visitsInA hAB
  use Fup
  have Fsynd : ∀ A ∈ F, isSyndetic A := by
    intro A hA
    obtain ⟨V,VOpen,pInV,visitsInA⟩ := hA
    have pUR := (ultrafilterMinimalIffUnifRec p).mp pMin
    specialize pUR V (IsOpen.mem_nhds VOpen pInV)
    exact syndeticIsMonotone pUR visitsInA
  use Fsynd
  have Fidemp : ∀ A ∈ F, {s | (fun x ↦ s * x) ⁻¹' A ∈ F} ∈ F := by
    intro A hA
    obtain ⟨V,VOpen,pInV,visitsInA⟩ := hA
    have visitsinF : visitTimeSet (ultrafilterSystem S) p V ∈ F := by use V
    have visitsInpreset : visitTimeSet (ultrafilterSystem S) p V ⊆
      {s | (fun x ↦ s * x) ⁻¹' A ∈ F} := by
        intro s hs
        simp only [Set.mem_ofPred_eq]
        let invV := ((ultrafilterSystem S).map s) ⁻¹' V
        have invVopen : IsOpen invV := by
          exact Continuous.isOpen_preimage ((ultrafilterSystem S).mapCont s) V VOpen
        have pininvV : p ∈ invV := by
          exact Set.mem_preimage.mpr hs
        use invV, invVopen, pininvV
        rw [← visitsToPreimages (ultrafilterSystem S) p V s]
        exact Set.preimage_mono visitsInA
    exact Fup (visitTimeSet (ultrafilterSystem S) p V)
      {s | (fun x ↦ s * x) ⁻¹' A ∈ F} visitsinF visitsInpreset
  use Fidemp

/-- Sets of the form `dcS` intersect `thick` are central -/
theorem dcSCapThickIsCentral
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
(∃ (B : Set S) (_ : isdcSSet B),
∃ (H : Set S) (_ : isThick H), B ∩ H ⊆ A) → isCentral A := by
  intro iA
  obtain ⟨B,BisdcS,H,HisThick,BcapHinA⟩ := iA
  obtain ⟨F,FNonempty,FFilter,FUpclosed,Fsyndetic,Fidemp,BinF⟩ :=
    dcSBelongsToSyndeticIdempotentFilter BisdcS
  let Fclos := ⋂ (A ∈ F), {p : Ultrafilter S | A ∈ p}
  have FclosClosed : IsClosed Fclos := by
    refine isClosed_biInter ?_
    intro A hA
    exact ultrafilter_isClosed_basic A
  have FclosCompact : IsCompact Fclos := IsClosed.isCompact FclosClosed
  have Fsubsemi : isSubsemigroup Fclos := by
    intro p hp q hq
    unfold Fclos
    apply Set.mem_iInter.mpr
    intro A hA hA2
    simp only [Set.mem_range, exists_prop] at hA2
    rw [←hA2.2]
    specialize Fidemp A hA2.1
    apply (ultraProductDescription p q A).mpr
    have : ∀ (s : S), (fun x ↦ s * x) ⁻¹' A ∈ F → (fun x ↦ s * x) ⁻¹' A ∈ q := by
      intro s hs
      unfold Fclos at hq
      have := Set.mem_iInter.mp hq ((fun x ↦ s * x) ⁻¹' A)
      have := Set.mem_iInter.mp this hs
      exact this
    have h9 : {s | (fun x ↦ s * x) ⁻¹' A ∈ F} ⊆ {s | (fun x ↦ s * x) ⁻¹' A ∈ q} := by
      exact Set.ofPred_subset_ofPred_of_imp this
    have h10 : {s | (fun x ↦ s * x) ⁻¹' A ∈ q} ∈ F := FUpclosed
      {s | (fun x ↦ s * x) ⁻¹' A ∈ F} {s | (fun x ↦ s * x) ⁻¹' A ∈ q} Fidemp h9
    have := Set.mem_iInter.mp hp {s | (fun x ↦ s * x) ⁻¹' A ∈ q}
    exact Set.mem_iInter.mp this h10
  obtain ⟨L,LminIdeal,LinHclos⟩ := thickIffClosureContainsMinLeftIdeal.mp HisThick
  let FcapL := Fclos ∩ L
  let FcapL2 := L ∩ Fclos
  have FcapL2nonempety : FcapL2.Nonempty := by
    unfold FcapL2 Fclos
    apply IsCompact.inter_iInter_nonempty
    · exact minimalLeftIdealCompact LminIdeal
    · intro A
      refine isClosed_iInter ?_
      intro AinF
      exact ultrafilter_isClosed_basic A
    · intro FiniteSubsetS
      let C := ⋂ i ∈ FiniteSubsetS, ⋂ (_ : i ∈ F), i
      let filterF : Filter S :=
      {
        sets := F
        univ_sets := by -- F is nonempty together with upclosed.
          obtain ⟨a,ha⟩ := FNonempty
          exact FUpclosed a Set.univ ha (Set.subset_univ a)
        sets_of_superset := by --FUpclosed
          intro x y hx hxy
          exact FUpclosed x y hx hxy
        inter_sets := by -- FFilter
          intro x y hx hy
          exact FFilter x y hx hy
      }
      have CinF : C ∈ F := by
        apply (Filter.mem_sets (f := filterF)).mpr
        unfold C
        refine (Filter.biInter_finset_mem (f := filterF) FiniteSubsetS).2 ?_
        intro i hi
        refine (Filter.iInter_mem (f := filterF)).2 ?_
        intro hiF
        apply Filter.mem_sets.mp
        exact hiF
      have hC : {p | C ∈ p} ⊆ -- NOTE: THIS IS AN EQUALITY BUT REVERSE IS NOT NEEDED AND IS ANNOYING
        ⋂ i ∈ FiniteSubsetS, ⋂ (_ : i ∈ F), {p : Ultrafilter S | i ∈ p} := by
          intro p
          simp only [Set.mem_iInter, Set.mem_ofPred_eq]
          intro hp G hG GinF
          have : ⋂ i ∈ FiniteSubsetS, ⋂ (_ : i ∈ F), i ⊆ G := by
            apply Set.iInter_subset_of_subset G
            exact
              Set.iInter₂_subset_of_subset hG (FUpclosed G G GinF fun ⦃a⦄ a_1 ↦ a_1) fun ⦃a⦄ a_1 ↦
                a_1
          exact Filter.mem_of_superset hp this
      have : isSyndetic C := Fsyndetic C CinF
      have hsubset : (L ∩ {p | C ∈ p}) ⊆
        (L ∩ ⋂ i ∈ FiniteSubsetS, ⋂ (_ : i ∈ F), {p | i ∈ p}) := by
          exact Set.inter_subset_inter (fun ⦃a⦄ a_1 ↦ a_1) hC
      apply Set.Nonempty.mono (ht := hsubset)
      have rwclospure :
        closure ((pure : S → Ultrafilter S) '' C) = {p | C ∈ p} := by
          rw [superset_antisymm_iff]
          constructor
          · intro p hp
            rw [TopologicalSpace.IsTopologicalBasis.mem_closure_iff ultrafilterBasis_is_basis]
            intro U hU pinU
            obtain ⟨E,hE⟩ := hU
            have CcapEinp : C ∩ E ∈ p := by
              rw [←hE] at pinU
              simp only [Set.mem_ofPred_eq] at pinU
              simp only [Set.mem_ofPred_eq] at hp
              exact Filter.inter_mem hp pinU
            obtain ⟨t,htC,htE⟩ := Ultrafilter.nonempty_of_mem CcapEinp
            have ptinU : pure t ∈ U := by
              rw [←hE]
              exact Set.mem_ofPred.mpr htE
            have ptinC : pure t ∈ (pure : S → Ultrafilter S) '' C := by
              exact Set.mem_image_of_mem pure htC
            use pure t
            exact ⟨ptinU,ptinC⟩
          · apply closure_minimal
            · intro d hd
              obtain ⟨s,hs1,hs2⟩ := hd
              exact Set.mem_of_eq_of_mem (id (Eq.symm hs2)) hs1
            · exact ultrafilter_isClosed_basic C
      rw [←rwclospure]
      exact syndeticClosureMeetsEveryIdeal this L LminIdeal.1
  have FcapLnonempty : FcapL.Nonempty := Set.inter_nonempty_iff_exists_right.mpr FcapL2nonempety
  have FcapLcompact : IsCompact FcapL := by
    have := minimalLeftIdealCompact LminIdeal
    exact IsCompact.inter_left this FclosClosed
  have FcapLsubsemi: isSubsemigroup FcapL := by
    intro p hp q hq
    refine ⟨?_,?_⟩
    · exact Fsubsemi p hp.1 q hq.1
    · have := LminIdeal.1.2 p
      apply this
      exact Set.mem_image_of_mem (fun x ↦ p * x) hq.2
  obtain ⟨p,pInFcapL,pIdemp⟩ := compactSubsemigroupContainsIdempotent FcapL
    (hTsemi := FcapLsubsemi) (hTcompact := FcapLcompact) (hTnonempty := FcapLnonempty)
  have BcapHinp : B ∩ H ∈ p := by
    have := Set.mem_iInter.mp pInFcapL.1 B
    have BinP := Set.mem_iInter.mp this BinF
    have pinHclos : p ∈ closure (pure '' H) := LinHclos pInFcapL.2
    have HinP : H ∈ p := by
      exact (memClosurePureIff H p).mp pinHclos
    exact Filter.inter_mem BinP HinP
  have Ainp : A ∈ p := by
    exact Filter.mem_of_superset BcapHinp BcapHinA
  have pMin : isMinimalUltrafilter p := by
    use L
    constructor
    · exact LminIdeal
    · exact pInFcapL.2
  use p, pMin, pIdemp


/-- central is dcs family join thick. -/
theorem centralIsdcSCapThick
(S : Type*) [Semigroup S] [Nonempty S] :
centralFamily S = (dcSFamily S) ⋎ (thickFamily S) := by
  ext A
  constructor
  · intro Acentral
    have centralConsequence := centralSetsAreVisitsOfPtToProxURPoint A Acentral
    have : (∃ (X : Type u_1) (_ : TopologicalSpace X) (_ : CompactSpace X)
      (_ : T2Space X) (_ : Nonempty X) (dSystem : DynamicalSystem S X) (x y : X)
        (_ : isUniformlyRecurrent dSystem y) (_ : proximal dSystem x y) (U : Set X)
          (_ : y ∈ U) (_ : IsOpen U), visitTimeSet dSystem x U = A) →
            (∃ (B : Set S) (_ : isdcSSet B), ∃ (H : Set S) (_ : isThick H), B ∩ H ⊆ A) :=
              visitsOfPtToProxURPointAredcSCapThick A
    obtain ⟨B, dcSB, H, thickH, intersectionContain⟩ := this centralConsequence
    have BcapHinJoin : B ∩ H ∈ dcSFamily S ⋎ thickFamily S := by
      use B, dcSB, H, thickH
    exact (dcSFamily S ⋎ thickFamily S).2 (B ∩ H) A BcapHinJoin intersectionContain
  · intro hA
    obtain ⟨B, dcSB, H, thickH, intersectionEqual⟩ := hA
    apply dcSCapThickIsCentral A
    use B, dcSB, H, thickH
    exact le_of_eq_of_le (id (Eq.symm intersectionEqual)) fun ⦃a⦄ a_1 ↦ a_1

/-- dcS sets are central along every thick set -/
theorem dcsIsSyndeticMeetCentral
(S : Type*) [Semigroup S] [Nonempty S] :
dcSFamily S ⊆ (centralFamily S) ⋏ (syndeticFamily S) :=
  by
    have := (centralIsdcSCapThick S).symm
    have : dcSFamily S ⋎ thickFamily S ⊆ centralFamily S := by
      change (dcSFamily S ⋎ thickFamily S).sets ⊆ (centralFamily S).sets
      have : (dcSFamily S ⋎ thickFamily S).sets = (centralFamily S).sets := by
        exact Filter.principal_eq_iff_eq.mp (congrArg Filter.principal (congrArg Family.sets this))
      exact this.le
    have := (familyUsefulIdentity (dcSFamily S) (thickFamily S) (centralFamily S)).mp this
    rw [dualThickSyndetic] at this
    exact this

/-- Central * is syndetic ⋏ dcSyndetic* -/
theorem cStarIsSyndeticMeetdcThick
(S : Type*) [Semigroup S] [Nonempty S] :
(centralFamily S)* =(dcTFamily S) ⋏ (syndeticFamily S) := by
  have := centralIsdcSCapThick S
  have : (centralFamily S)* = (dcSFamily S⋎thickFamily S)* := congrArg Family.famDual this
  have deMorg := familyDeMorgan1 (dcSFamily S) (thickFamily S)
  rw [deMorg] at this
  rw [dualThickSyndetic] at this
  exact this

/-- A set `A ⊆ S` is Central* if and only if it is a set of recurrence
along all thick sets -/
theorem cStarIffSetOfRecAlongAllThick
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
A ∈ (centralFamily S)* ↔ ∀ (H : Set S), isThick H → A ∩ H ∈ dcTFamily S := by
  rw [cStarIsSyndeticMeetdcThick S]
  have hEqu : A ∈ dcTFamily S⋏syndeticFamily S ↔ ∀ B ∈ (syndeticFamily S)*, A ∩ B ∈ dcTFamily S :=
    by
    rw [familyMeetIsCommutative]
    exact mem_famMeet (syndeticFamily S) (dcTFamily S) A
  rw [dualSyndeticThick] at hEqu
  exact hEqu

/-- A set `A ⊆ S` is Central* if and only if `R(x,U) ∩ A` is syndetic for all
`x ∈ U` in any minimal system -/
theorem cStarIffSyndeticAlongdcS
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
A ∈ (centralFamily S)* ↔ ∀ (H : Set S), isdcSSet H → A ∩ H ∈ syndeticFamily S := by
  rw [cStarIsSyndeticMeetdcThick S]
  have := mem_famMeet (dcTFamily S) (syndeticFamily S) A
  unfold dcTFamily at this
  rw [dualIsInvolutionOnFamilies (dcSFamily S)] at this
  exact this
-- (∀ (X : Type*) (_ : TopologicalSpace X)
-- (_ : CompactSpace X) (_ : T2Space X) (_ : Nonempty X)
-- (dSystem : DynamicalSystem S X) (hMin : isMinimalSystem dSystem) (x : X)
-- (U : Set X) (_ : x ∈ U) (_ : IsOpen U),
-- isSyndetic (A ∩ (visitTimeSet dSystem x U)))


theorem thickIndicatorLemmaInCountCommSemi
{S : Type*} [CommSemigroup S] [Nonempty S] [Countable S]
{H : Set S} (Hthick : isThick H) :
∃ (G : Set S), G ⊆ H ∧ isThick G ∧ (∀ (B : Set S) (L : Set (Ultrafilter S)),
  isLeftIdeal L → L ⊆ (closure ((pure : S → Ultrafilter S) '' B)) →
    (L ∩ (closure ((pure : S → Ultrafilter S) '' G))).Nonempty → isThick (B ∩ H)) :=
by
  classical
  -- enumerate `S` as `e 0, e 1, ...` and put `F n = {e 0, ..., e n}`
  obtain ⟨e, he⟩ := exists_surjective_nat S
  set F : ℕ → Set S := fun n ↦ e '' (Set.Iic n) with hFdef
  have hFfin : ∀ n, (F n).Finite := fun n ↦ (Set.finite_Iic n).image e
  have hFmono : ∀ {m n : ℕ}, m ≤ n → F m ⊆ F n :=
    fun hmn ↦ Set.image_mono (Set.Iic_subset_Iic.mpr hmn)
  have hFcovers : ∀ K : Set S, K.Finite → ∃ n, K ⊆ F n := by
    intro K hK
    choose g hg using he
    obtain ⟨n, hn⟩ := (hK.image g).bddAbove
    exact ⟨n, fun k hk ↦ ⟨g k, hn ⟨k, hk, rfl⟩, hg k⟩⟩
  -- thickness of `H` applied to the finite set `F n ∪ (F n * F n)` gives `t n` with
  -- `F n * t n ⊆ H` and `F n * F n * t n ⊆ H`
  have hprod : ∀ n : ℕ, ∃ t : S, ∀ f ∈ F n, ∀ g ∈ F n, f * t ∈ H ∧ (f * g) * t ∈ H := by
    intro n
    obtain ⟨t, ht⟩ := Hthick ((F n) ∪ ((fun q : S × S ↦ q.1 * q.2) '' ((F n) ×ˢ (F n))))
      ((hFfin n).union (((hFfin n).prod (hFfin n)).image _))
    exact ⟨t, fun f hf g hg ↦
      ⟨ht ⟨f, Set.mem_union_left _ hf, rfl⟩,
        ht ⟨f * g, Set.mem_union_right _ ⟨(f, g), Set.mk_mem_prod hf hg, rfl⟩, rfl⟩⟩⟩
  choose t ht using hprod
  refine ⟨⋃ n, (fun x ↦ x * t n) '' (F n), ?_, ?_, ?_⟩
  · -- `G ⊆ H` holds by construction, since `F n * t n ⊆ H`
    rintro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    obtain ⟨f, hf, rfl⟩ := hn
    exact (ht n f hf f hf).1
  · -- `G` is thick: a finite set sits inside some `F n`, and `F n * t n ⊆ G`
    intro K hK
    obtain ⟨n, hn⟩ := hFcovers K hK
    refine ⟨t n, ?_⟩
    rintro w ⟨k, hk, rfl⟩
    exact Set.mem_iUnion.mpr ⟨n, ⟨k, hn hk, rfl⟩⟩
  · rintro B L hLideal hLB ⟨p, hpL, hpG⟩
    have hGp : (⋃ n, (fun x ↦ x * t n) '' (F n)) ∈ p := (memClosurePureIff _ p).mp hpG
    -- `L ⊆ closure B` and `L` is a left ideal, so every `f⁻¹B` belongs to `p`
    have hBp : ∀ f : S, (leftMult f) ⁻¹' B ∈ p := fun f ↦
      (membershipInLeftMultByPrincipal f B p).mp
        ((memClosurePureIff B _).mp (hLB (hLideal.2 (pure f) ⟨p, hpL, rfl⟩)))
    by_cases hprin : ∃ a : S, p = pure a
    · -- Case 1: `p = pure a`.  Then `S a ⊆ B`, and `a (a⁻¹H) ⊆ B ∩ H` is thick
      obtain ⟨a, rfl⟩ := hprin
      have hSa : ∀ f : S, f * a ∈ B := by
        intro f
        have := hBp f
        rwa [Ultrafilter.mem_pure] at this
      have hinv : isThick ((leftMult a) ⁻¹' H) := by
        have := inverseDilateCapOfThickIsThick (S := S) H (hA := Hthick) {a}
          (KIsFinite := Set.finite_singleton a)
        rwa [Set.biInter_singleton] at this
      refine thickIsMonotone (rightTransOfThickIsThick hinv a) ?_
      rintro w ⟨h, hh, rfl⟩
      have hhH : a * h ∈ H := hh
      refine ⟨hSa h, ?_⟩
      rwa [mul_comm h a]
    · -- Case 2: `p` is not principal, so it contains no finite set
      -- `G \ s⁻¹H` is finite for every `s`, hence `s⁻¹H ∈ p`
      have hHp : ∀ s : S, (leftMult s) ⁻¹' H ∈ p := by
        intro s
        by_contra hs
        obtain ⟨m, hm⟩ := he s
        have hsF : s ∈ F m := ⟨m, Set.mem_Iic.mpr le_rfl, hm⟩
        have hsub : (⋃ n, (fun x ↦ x * t n) '' (F n)) ∩ ((leftMult s) ⁻¹' H)ᶜ
            ⊆ ⋃ n ∈ Set.Iio m, (fun x ↦ x * t n) '' (F n) := by
          rintro x ⟨hxG, hxH⟩
          obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxG
          obtain ⟨f, hf, rfl⟩ := hn
          refine Set.mem_biUnion (Set.mem_Iio.mpr ?_) ⟨f, hf, rfl⟩
          by_contra hnm
          push Not at hnm
          refine hxH ?_
          change s * (f * t n) ∈ H
          rw [← mul_assoc]
          exact (ht n s (hFmono hnm hsF) f hf).2
        have hfin : ((⋃ n, (fun x ↦ x * t n) '' (F n)) ∩ ((leftMult s) ⁻¹' H)ᶜ).Finite :=
          Set.Finite.subset ((Set.finite_Iio m).biUnion fun n _ ↦ (hFfin n).image _) hsub
        obtain ⟨x, -, hpx⟩ := Ultrafilter.eq_pure_of_finite_mem hfin
          (Filter.inter_mem hGp (Ultrafilter.compl_mem_iff_notMem.mpr hs))
        exact hprin ⟨x, hpx⟩
      -- every finite intersection of shifts of `B ∩ H` belongs to `p`, hence is non-empty
      intro K hK
      have hmem : (⋂ f ∈ K, (leftMult f) ⁻¹' (B ∩ H)) ∈ p :=
        (Filter.biInter_mem hK).mpr fun f _ ↦ Filter.inter_mem (hBp f) (hHp f)
      obtain ⟨x, hx⟩ := Ultrafilter.nonempty_of_mem hmem
      refine ⟨x, ?_⟩
      rintro w ⟨f, hf, rfl⟩
      simp only [Set.mem_iInter] at hx
      exact hx f hf


/-- A set `A` is strongly piecewise-`F` if and only if for all thick sets `H ⊆ S`,
there exists a set `B ∈ F` and a thick set `T ⊆ S` such that `A ∩ H = B ∩ T` -/
theorem memStronglyPWIff
{S : Type*} [Semigroup S] [Nonempty S] (F : Family S) (A : Set S) :
A ∈ stronglyPW F ↔ ∀ (H : Set S), isThick H →
  ∃ (B : Set S), B ∈ F ∧ ∃ (T : Set S), isThick T ∧ A ∩ H = B ∩ T := by
  have hdual : ∀ H : Set S, H ∈ (syndeticFamily S)* ↔ isThick H := fun H ↦ by
    rw [dualSyndeticThick]
    rfl
  constructor
  · intro h H hH
    have h' : ∀ H ∈ (syndeticFamily S)*, A ∩ H ∈ thickFamily S ⋎ F := h
    obtain ⟨T, hT, B, hB, hEq⟩ := h' H ((hdual H).mpr hH)
    exact ⟨B, hB, T, hT, hEq.trans (Set.inter_comm T B)⟩
  · intro h
    change ∀ H ∈ (syndeticFamily S)*, A ∩ H ∈ thickFamily S ⋎ F
    intro H hH
    obtain ⟨B, hB, T, hT, hEq⟩ := h H ((hdual H).mp hH)
    exact ⟨T, hT, B, hB, hEq.trans (Set.inter_comm B T)⟩

/-- In countable, commutative semigroups `S`, if `F` is a family of
syndetic subsets of `S`, then the families of strongly piecewise-`F` and
very strongly piecewise-`F` sets coincide -/
theorem inCommCountSemiStrongPWandVeryStrongPWCoincide
{S : Type*} [CommSemigroup S] [Nonempty S] [Countable S]
(F : Family S) (hFSyndetic : ∀ A ∈ F, isSyndetic A) :
stronglyPW F = veryStronglyPW F := by
  ext A
  constructor
  · -- strongly piecewise-`F` sets are very strongly piecewise-`F`
    intro hA
    change A ∈ (veryStronglyPW F : Set (Set S))
    rw [veryStronglyPW, iInterCapFamilyDescription]
    intro H hH
    -- Lemma `thickIndicatorLemmaInCountCommSemi` produces a thick set `G ⊆ H`
    obtain ⟨G, -, hGthick, hGprop⟩ := thickIndicatorLemmaInCountCommSemi hH
    -- `A ∩ G = B ∩ T` with `B ∈ F` and `T` thick
    obtain ⟨B, hBF, T, hTthick, hAGBT⟩ := (memStronglyPWIff F A).mp hA G hGthick
    -- `B' = B ∪ (A ∩ T) ∈ F` since `F` is upward closed
    set B' := B ∪ (A ∩ T) with hB'def
    have hB'F : B' ∈ F := F.upward_closed B B' hBF Set.subset_union_left
    -- `T` is thick, so there is a left ideal `L ⊆ closure T`
    obtain ⟨L, hLmin, hLT⟩ := thickIffClosureContainsMinLeftIdeal.mp hTthick
    -- `L` meets `closure B` since `B` is syndetic, and `closure T ∩ closure B ⊆ closure G`
    have hLG : (L ∩ closure ((pure : S → Ultrafilter S) '' G)).Nonempty := by
      obtain ⟨p, hpL, hpB⟩ := syndeticClosureMeetsEveryIdeal (hFSyndetic B hBF) L hLmin.1
      have hBT : B ∩ T ∈ p :=
        Filter.inter_mem ((memClosurePureIff B p).mp hpB) ((memClosurePureIff T p).mp (hLT hpL))
      rw [← hAGBT] at hBT
      exact ⟨p, hpL, (memClosurePureIff G p).mpr
        (Filter.mem_of_superset hBT Set.inter_subset_right)⟩
    -- so `H' = T ∩ H` is thick
    have hH'thick : isThick (T ∩ H) := hGprop T L hLmin.1 hLT hLG
    refine ⟨T ∩ H, hH'thick, Set.inter_subset_right, B', hB'F, ?_⟩
    -- `A ∩ H' = B' ∩ H'`, since `B ∩ T ∩ H = A ∩ G ∩ T ∩ H ⊆ A ∩ T ∩ H`
    ext x
    constructor
    · rintro ⟨hxA, hxT, hxH⟩
      exact ⟨Or.inr ⟨hxA, hxT⟩, hxT, hxH⟩
    · rintro ⟨hxB | ⟨hxA, -⟩, hxT, hxH⟩
      · have hxAG : x ∈ A ∩ G := by
          rw [hAGBT]
          exact ⟨hxB, hxT⟩
        exact ⟨hxAG.1, hxT, hxH⟩
      · exact ⟨hxA, hxT, hxH⟩
  · -- very strongly piecewise-`F` sets are strongly piecewise-`F`
    intro hA
    refine (memStronglyPWIff F A).mpr fun H hH ↦ ?_
    obtain ⟨C, hC, D, hD, rfl⟩ := (Family.mem_iInter _ A).mp hA ⟨H, hH⟩
    refine ⟨D, hD, H ∩ C, hC, ?_⟩
    ext x
    constructor
    · rintro ⟨⟨hxC, hxD⟩, hxH⟩
      exact ⟨hxD, hxH, hxC⟩
    · rintro ⟨hxD, hxH, hxC⟩
      exact ⟨⟨hxC, hxD⟩, hxH⟩


/-- Precursor to result in AP_Defs: In countable, commutative semigroups,
(syndeticFamily S) ⋏ (IPFamily S) = (syndeticFamily S) ⋏ (centralFamily S) -/
theorem preStrongIPIffStrongCentralInCountCommSemi
{S : Type*} [CommSemigroup S] [Nonempty S] [Countable S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{dSystem : DynamicalSystem S X} (hMin : isMinimalSystem dSystem)
(x : X) {U : Set X} (UClopen : IsClopen U)
(H : Set S) (_Hthick : isThick H) :
(∀ (H' : Set S), H' ⊆ H → isThick H' → visitTimeSet dSystem x U ∩ H' ∈ IPFamily S) →
  (∀ (H' : Set S), H' ⊆ H → isThick H' → visitTimeSet dSystem x U ∩ H' ∈ centralFamily S) := by
  intro hIP H' hH'H hH'thick
  -- Lemma 4.3 produces a thick set `G ⊆ H'` with the stipulated property
  obtain ⟨G, hGH', hGthick, hGprop⟩ := thickIndicatorLemmaInCountCommSemi (H := H') hH'thick
  -- `G ⊆ H' ⊆ H` is thick, so `R(x,U) ∩ G` is an IP set: it lies in an idempotent `p`
  obtain ⟨p, hpidem, hpRG⟩ := hIP G (hGH'.trans hH'H) hGthick
  have hRp : visitTimeSet dSystem x U ∈ p := Filter.mem_of_superset hpRG Set.inter_subset_left
  have hGp : G ∈ p := Filter.mem_of_superset hpRG Set.inter_subset_right
  -- `p x ∈ U` is uniformly recurrent (the system is minimal) and proximal to `x`
  set y := (ultraAction dSystem).map p x with hy
  have hyU : y ∈ U := by
    have hcl := visitTimeSetInUltraImpliesUltraActInClosure dSystem x U p hRp
    rwa [UClopen.1.closure_eq] at hcl
  have hyUR : isUniformlyRecurrent dSystem y :=
    minimalImpliesUniformlyRecurrent dSystem (hMin := hMin) y
  have hpy : (ultraAction dSystem).map p y = y := by
    rw [hy, ← (ultraAction dSystem).mapMult p p x, hpidem]
  -- Lemma 2.1: `R((x,y),α) ∩ R(y,V) ⊆ R(x,U)`
  obtain ⟨V, hVopen, hyV, α, hαopen, hαdiag, hVα⟩ :=
    nbhdOfDiagForcesOtherSetContainment UClopen.2 hyU
  -- `L = {p} ∪ βS p` is a left ideal meeting `closure G` and contained in `closure R((x,y),α)`
  set L : Set (Ultrafilter S) := {r | r = p ∨ ∃ q : Ultrafilter S, q * p = r} with hLdef
  have hLideal : isLeftIdeal L := by
    refine ⟨⟨p, Or.inl rfl⟩, ?_⟩
    rintro s w ⟨r, hr, rfl⟩
    rcases hr with rfl | ⟨q, rfl⟩
    · exact Or.inr ⟨s, rfl⟩
    · exact Or.inr ⟨s * q, mul_assoc s q p⟩
  have hLdiag : ∀ r ∈ L, visitTimeSet (diagDynamicalSystem dSystem dSystem) (x, y) α ∈ r := by
    intro r hr
    refine visitTimeSetBelongsToUltrafilter (diagDynamicalSystem dSystem dSystem) (x, y) α
      (hU := hαopen) r ?_
    rw [ultraDiagAction]
    refine hαdiag ?_
    change (ultraAction dSystem).map r x = (ultraAction dSystem).map r y
    rcases hr with rfl | ⟨q, rfl⟩
    · rw [hpy]
    · rw [(ultraAction dSystem).mapMult q p x, (ultraAction dSystem).mapMult q p y, hpy, ← hy]
  have hLsub : L ⊆ closure ((pure : S → Ultrafilter S) ''
      (visitTimeSet (diagDynamicalSystem dSystem dSystem) (x, y) α)) :=
    fun r hr ↦ (memClosurePureIff _ r).mpr (hLdiag r hr)
  have hLmeet : (L ∩ closure ((pure : S → Ultrafilter S) '' G)).Nonempty :=
    ⟨p, Or.inl rfl, (memClosurePureIff G p).mpr hGp⟩
  have hthick : isThick (visitTimeSet (diagDynamicalSystem dSystem dSystem) (x, y) α ∩ H') :=
    hGprop _ L hLideal hLsub hLmeet
  -- `R(y,V)` is a dcS set, so Theorem 4.1 applies
  have hdcS : isdcSSet (visitTimeSet dSystem y V) :=
    returnTimesImpliesdcS _ ⟨X, inferInstance, inferInstance, inferInstance, inferInstance,
      dSystem, y, hyUR, V, hyV, hVopen, subset_rfl⟩
  refine dcSCapThickIsCentral _ ⟨visitTimeSet dSystem y V, hdcS,
    visitTimeSet (diagDynamicalSystem dSystem dSystem) (x, y) α ∩ H', hthick, ?_⟩
  rintro s ⟨hsV, hsα, hsH'⟩
  exact ⟨hVα (dSystem.map s x) (dSystem.map s y) hsα hsV, hsH'⟩



end central_sets

section Bohr_prelims

/-- In a compact submonoid of a topological monoid
with the property that "idempotent implies unit", every
element has a two-sided inverse -/
theorem existsTwoSidedInvInCompactSubmonoid
{T : Type*} [Monoid T] [TopologicalSpace T] [T2Space T] [ContinuousMul T]
(S : Submonoid T) (hSComp : IsCompact (S : Set T))
(hSIdemp : ∀ (x : S), x * x = x → x = 1) :
∀ (x : S), ∃ (y : S), (x * y = 1) ∧ (y * x = 1) := by
  intro x
  let P : Subsemigroup T :=
    { carrier := {y | ∃ n : ℕ, 2 ≤ n ∧ y = (x : T) ^ n}
      mul_mem' := by
        intro a b ha hb
        rcases ha with ⟨m, hm, rfl⟩
        rcases hb with ⟨n, hn, rfl⟩
        refine ⟨m + n, ?_, ?_⟩
        · omega
        · rw [pow_add] }
  have hPsubS : (P : Set T) ⊆ S := by
    intro y hy
    rcases hy with ⟨n, hn, rfl⟩
    exact S.pow_mem x.property n
  have hPnonempty : (P : Set T).Nonempty := by
    refine ⟨(x : T) ^ 2, ?_⟩
    exact ⟨2, le_rfl, rfl⟩
  let A := P.topologicalClosure
  have hAcompact : IsCompact (A : Set T) := by
    rw [Subsemigroup.coe_topologicalClosure]
    exact hSComp.closure_of_subset hPsubS
  have hAnonempty : (A : Set T).Nonempty := by
    rcases hPnonempty with ⟨a, ha⟩
    exact ⟨a, subset_closure ha⟩
  have hAmul :
      ∀ a ∈ (A : Set T), ∀ b ∈ (A : Set T), a * b ∈ (A : Set T) := by
    intro a ha b hb
    exact A.mul_mem ha hb
  obtain ⟨e, heA, heidem⟩ :=
    exists_idempotent_in_compact_subsemigroup
      (fun r : T => continuous_id.mul continuous_const)
      (A : Set T)
      hAnonempty
      hAcompact
      hAmul
  have heS : e ∈ S := by
    have hAS : (A : Set T) ⊆ S := by
      rw [Subsemigroup.coe_topologicalClosure]
      exact closure_minimal hPsubS hSComp.isClosed
    exact hAS heA
  have eheSisIdemp : (⟨e, heS⟩ : S) * (⟨e, heS⟩ : S) = (⟨e, heS⟩ : S) := by
    apply Subtype.ext
    change e * e = e
    exact heidem
  have heone : e = 1 := by
    have h : (⟨e, heS⟩ : S) = 1 := hSIdemp ⟨e, heS⟩ eheSisIdemp
    exact congrArg (fun z : S => (z : T)) h
  let L : Set T :=
    (fun y : T => (x : T) * y) '' (S : Set T)
  have hLcompact : IsCompact L := by
    exact hSComp.image (continuous_const.mul continuous_id)
  have hLclosed : IsClosed L :=
    hLcompact.isClosed
  have hPL : (P : Set T) ⊆ L := by
    intro y hy
    rcases hy with ⟨n, hn, rfl⟩
    have hn1 : 1 ≤ n := by omega
    refine ⟨(x : T) ^ (n - 1), S.pow_mem x.property (n - 1), ?_⟩
    rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ']
    simp only [add_tsub_cancel_right]
  have hAL : (A : Set T) ⊆ L := by
    rw [Subsemigroup.coe_topologicalClosure]
    exact closure_minimal hPL hLclosed
  have heL : e ∈ L := by
    exact hAL (by simpa [heone] using heA)
  obtain ⟨s₁, hs₁S, hs₁⟩ := heL
  have hs₁eq : (x : T) * s₁ = 1 := by
    rw [heone] at hs₁
    exact hs₁
  let R : Set T :=
    (fun y : T => y * (x : T)) '' (S : Set T)
  have hRcompact : IsCompact R := by
    exact hSComp.image (continuous_id.mul continuous_const)
  have hRclosed : IsClosed R :=
    hRcompact.isClosed
  have hPR : (P : Set T) ⊆ R := by
    intro y hy
    rcases hy with ⟨n, hn, rfl⟩
    have hn1 : 1 ≤ n := by omega
    refine ⟨(x : T) ^ (n - 1), S.pow_mem x.property (n - 1), ?_⟩
    rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
    simp only [add_tsub_cancel_right]
  have hAR : (A : Set T) ⊆ R := by
    rw [Subsemigroup.coe_topologicalClosure]
    exact closure_minimal hPR hRclosed
  have heR : e ∈ R := by
    exact hAR (by simpa [heone] using heA)
  obtain ⟨s₂, hs₂S, hs₂⟩ := heR
  have hs₂eq : s₂ * (x : T) = 1 := by
    rw [heone] at hs₂
    exact hs₂
  have hs₁s₂ : s₁ = s₂ := by
    calc
      s₁ = 1 * s₁ := by rw [one_mul]
      _ = (s₂ * (x : T)) * s₁ := by rw [hs₂eq]
      _ = s₂ * ((x : T) * s₁) := by rw [mul_assoc]
      _ = s₂ * 1 := by rw [hs₁eq]
      _ = s₂ := by rw [mul_one]
  refine ⟨⟨s₁, hs₁S⟩, ?_, ?_⟩
  · apply Subtype.ext
    exact hs₁eq
  · apply Subtype.ext
    change s₁ * (x : T) = 1
    rw [hs₁s₂]
    exact hs₂eq

/-- An inverse for compact submonoid of a topological monoid
with the property that "idempotent implies unit" -/
@[instance_reducible]
noncomputable
def invFromCompactSubmonoid
{T : Type*} [Monoid T] [TopologicalSpace T] [T2Space T] [ContinuousMul T]
(S : Submonoid T) (hSComp : IsCompact (S : Set T))
(hSIdemp : ∀ (x : S), x * x = x → x = 1) :
Inv S :=
{
  inv x :=
  Classical.choose
    (existsTwoSidedInvInCompactSubmonoid S hSComp hSIdemp x)
}

/-- A group structure for compact submonoid of a topological monoid
with the property that "idempotent implies unit" -/
@[instance_reducible]
noncomputable
def groupFromCompactSubmonoid
{T : Type*} [Monoid T] [TopologicalSpace T] [T2Space T] [ContinuousMul T]
(S : Submonoid T) (hSComp : IsCompact (S : Set T))
(hSIdemp : ∀ (x : S), x * x = x → x = 1) :
Group S := by
  letI : Inv S := invFromCompactSubmonoid S hSComp hSIdemp
  exact Group.ofLeftAxioms
    mul_assoc
    one_mul
    (by
      intro x
      exact
        (Classical.choose_spec
          (existsTwoSidedInvInCompactSubmonoid S hSComp hSIdemp x)).2)


/-- Closed graph implies continuous function -/
lemma continuous_of_isClosed_graph_of_compact
{X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
[TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
(f : X → Y) (hgraph : IsClosed {p : X × Y | p.2 = f p.1}) :
Continuous f := by
  rw [continuous_iff_isClosed]
  intro C hC
  let K : Set (X × Y) := {p | p.2 = f p.1 ∧ p.2 ∈ C}
  have hKclosed : IsClosed K := by
    change IsClosed ({p : X × Y | p.2 = f p.1} ∩ Prod.snd ⁻¹' C)
    exact hgraph.inter (hC.preimage continuous_snd)
  have hKcompact : IsCompact K := hKclosed.isCompact
  have hprojclosed : IsClosed (Prod.fst '' K) :=
    (hKcompact.image continuous_fst).isClosed
  have hpre : f ⁻¹' C = Prod.fst '' K := by
    ext x
    constructor
    · intro hx
      refine ⟨(x, f x), ?_, rfl⟩
      change f x = f x ∧ f x ∈ C
      exact ⟨rfl, hx⟩
    · rintro ⟨p, hp, rfl⟩
      change (p.2 = f p.1 ∧ p.2 ∈ C) at hp
      change f p.1 ∈ C
      rw [← hp.1]
      exact hp.2
  rw [hpre]
  exact hprojclosed


/-- A compact Hausdorff group with a continuous multiplication has
a continuous inverse -/
theorem continuousInv_of_compactSpace
{G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
[ContinuousMul G] :
ContinuousInv G := by
  refine ⟨?_⟩
  apply continuous_of_isClosed_graph_of_compact (f := fun x : G => x⁻¹)
  have hmul : Continuous (fun p : G × G => p.1 * p.2) :=
    continuous_fst.mul continuous_snd
  have h : IsClosed {p : G × G | p.1 * p.2 = 1} :=
    isClosed_eq hmul continuous_const
  simpa only [mul_eq_one_iff_eq_inv'] using h

/- The group above has a continuous inverse.  This is a standard fact: any
compact Hausdorff group with a continuous multiplication has a continuous
inverse. -/
theorem groupFromCompactSubmonoidHasContinuousInv
{T : Type*} [Monoid T] [TopologicalSpace T] [T2Space T] [ContinuousMul T]
(S : Submonoid T) (hSComp : IsCompact (S : Set T))
(hSIdemp : ∀ (x : S), x * x = x → x = 1) :
letI : Group S := groupFromCompactSubmonoid S hSComp hSIdemp
ContinuousInv S := by
  let : Group S := groupFromCompactSubmonoid S hSComp hSIdemp
  let hComp : CompactSpace S := isCompact_iff_compactSpace.mp hSComp
  let hMul : ContinuousMul S := Submonoid.continuousMul S
  exact
    @continuousInv_of_compactSpace
      S
      (groupFromCompactSubmonoid S hSComp hSIdemp)
      inferInstance
      hComp
      inferInstance
      hMul

/- A compact submonoid of a topological monoid with the property
that "idempotent implies unit" is a compact Hausdorff group. -/
theorem groupFromCompactSubmonoidIsTopologicalGroup
{T : Type*} [Monoid T] [TopologicalSpace T] [T2Space T] [ContinuousMul T]
(S : Submonoid T) (hSComp : IsCompact (S : Set T))
(hSIdemp : ∀ (x : S), x * x = x → x = 1) :
letI : Group S := groupFromCompactSubmonoid S hSComp hSIdemp
IsTopologicalGroup S := by
  let : Group S := groupFromCompactSubmonoid S hSComp hSIdemp
  let hComp : CompactSpace S := isCompact_iff_compactSpace.mp hSComp
  let hMul : ContinuousMul S := Submonoid.continuousMul S
  let hInv : ContinuousInv S :=
    @continuousInv_of_compactSpace
      S
      (groupFromCompactSubmonoid S hSComp hSIdemp)
      inferInstance
      hComp
      inferInstance
      hMul
  exact
    { continuous_mul := hMul.continuous_mul
      continuous_inv := hInv.continuous_inv }

-- theorem: if A ⊆ C(X,X) consists of surjections, then so does its closure
theorem surjectiveSetImpliesSurjectiveClosure
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{S : Set (ContinuousMap.End X)}
(hSsurject : ∀ (ϕ : (ContinuousMap.End X)), ϕ ∈ S → Function.Surjective ϕ) :
∀ (ϕ : (ContinuousMap.End X)), ϕ ∈ closure S → Function.Surjective ϕ := by
  let Z := TopologicalSpace.NonemptyCompacts X
  let XZelt : Z := {
    carrier := Set.univ (α := X)
    isCompact' := isCompact_univ
    nonempty' := Set.univ_nonempty
  }
  let ψ : (ContinuousMap.End X) → Z :=
    fun (f : ContinuousMap.End X) ↦ TopologicalSpace.NonemptyCompacts.map
      f.toContinuousMap f.toContinuousMap.continuous XZelt
  -- {
  --   carrier := f.toContinuousMap '' (Set.univ (α := X))
  --   isCompact' := IsCompact.image (isCompact_univ) f.toContinuousMap.continuous
  --   nonempty' := Set.image_nonempty.mpr (Set.univ_nonempty)
  -- }
  have ψCont : Continuous ψ := by
    apply Continuous.nonemptyCompacts_map'
    · exact continuous_const
    · change Continuous (fun p : (ContinuousMap.End X) × X => p.1.toContinuousMap p.2)
      fun_prop
  let constX : (ContinuousMap.End X) → Z := fun (f : ContinuousMap.End X) ↦ XZelt
  have constXCont : Continuous constX := by
    exact continuous_const
  have eqonS : Set.EqOn ψ constX S := by
    intro x hx
    have := hSsurject x hx
    refine TopologicalSpace.NonemptyCompacts.ext_iff.mpr ?_
    unfold constX XZelt ψ
    simp only [TopologicalSpace.NonemptyCompacts.coe_mk, TopologicalSpace.Compacts.coe_mk]
    exact Set.image_univ_of_surjective (hSsurject x hx)
  have eqonclosS : Set.EqOn ψ constX (closure S) := by
    exact Set.EqOn.closure eqonS ψCont constXCont
  intro x hx
  apply Set.range_eq_univ.mp
  have := congrArg (fun z => z.1.1) (eqonclosS hx)
  unfold ψ constX XZelt at this
  simp only [TopologicalSpace.NonemptyCompacts.toCompacts_map,
    TopologicalSpace.Compacts.carrier_eq_coe, TopologicalSpace.Compacts.coe_map,
    TopologicalSpace.Compacts.coe_mk, Set.image_univ] at this
  exact this

-- theorem: if S ⊆ C(X,X) is a subsemigroup, then so is its closure
theorem closureOfSubsemiIsSubsemi
{T : Type*} [semi : Semigroup T] [TopologicalSpace T] [T2Space T] [CM : ContinuousMul T]
{S : Set T} (hSsubsemi : ∀ (ϕ ψ : T), ϕ ∈ S → ψ ∈ S → ϕ * ψ ∈ S) :
∀ (ϕ ψ : T), ϕ ∈ closure S → ψ ∈ closure S → ϕ * ψ ∈ closure S := by
  let M : T × T → T := fun p => semi.mul p.1 p.2
  have hMcont : Continuous M := by
    exact CM.continuous_mul
  have imgMinS : M '' (Set.prod S S) ⊆ S := by
    intro x hx
    obtain ⟨y,hy1,hy2⟩ := hx
    rw [←hy2]
    unfold M
    exact hSsubsemi y.1 y.2 hy1.1 hy1.2
  have cprod : Set.prod (closure S) (closure S) = closure (Set.prod S S) := closure_prod_eq.symm
  have closInv : M '' (Set.prod (closure S) (closure S)) ⊆ closure S :=
    calc
      M '' (Set.prod (closure S) (closure S)) ⊆ M '' (closure (Set.prod S S)) := by rw [cprod]
      _ ⊆ closure (M '' Set.prod S S) := image_closure_subset_closure_image hMcont
      _ ⊆ closure S := closure_mono imgMinS
  intro x y hx hy
  have prodInImg : x * y ∈ M '' (Set.prod (closure S) (closure S)) := by
    unfold M
    simp only [Set.mem_image, Prod.exists]
    use x
    use y
    exact ⟨⟨hx,hy⟩,rfl⟩
  exact closInv prodInImg

-- theorem: if the maps in A ⊆ C(X,X) commute, then the maps in its closure commute
theorem closureOfCommSetIsCommSet
{T : Type*} [semi : Semigroup T] [TopologicalSpace T] [T2Space T] [CM : ContinuousMul T]
{S : Set T} (hScomm : ∀ (ϕ ψ : T), ϕ ∈ S → ψ ∈ S → ϕ * ψ = ψ * ϕ) :
∀ (ϕ ψ : T), ϕ ∈ closure S → ψ ∈ closure S → ϕ * ψ = ψ * ϕ := by
  let M : T × T → T := fun p => semi.mul p.1 p.2
  have hMcont : Continuous M := by
    exact CM.continuous_mul
  let swap : T × T → T × T := fun ⟨x,y⟩ ↦ ⟨y,x⟩
  have hswapcont : Continuous swap := by
    refine continuous_prodMk.mpr ?_
    exact ⟨continuous_snd,continuous_fst⟩
  let N : T × T → T := M.comp swap
  have Ncont : Continuous N := by
    exact Continuous.comp hMcont hswapcont
  have eqonS : Set.EqOn M N (Set.prod S S) := by
    intro x hx
    exact hScomm x.1 x.2 hx.1 hx.2
  have eqonSclos : Set.EqOn M N (Set.prod (closure S) (closure S)) := by
    have cprod : Set.prod (closure S) (closure S) = closure (Set.prod S S) := closure_prod_eq.symm
    rw [cprod]
    exact Set.EqOn.closure eqonS hMcont Ncont
  intro x y hx hy
  unfold Set.EqOn at eqonSclos
  exact eqonSclos (x := ⟨x,y⟩) ⟨hx, hy⟩

-- theorem: if S ⊆ C(X,X) is a subsemigroup and consists of surjections,
-- then any idempotent it contains is equal to Id_X
theorem surjectiveSubsemiUniqueIdempotent
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{S : Set (ContinuousMap.End X)}
(hSsurject : ∀ (ϕ : (ContinuousMap.End X)), ϕ ∈ S → Function.Surjective ϕ) :
∀ (ϕ : (ContinuousMap.End X)), ϕ ∈ S → ϕ * ϕ = ϕ → ϕ = 1 := by
  intro φ hφ φIdemp
  apply ContinuousMap.End.ext
  intro x
  obtain ⟨y,hy⟩ := hSsurject φ hφ x
  simp only [ContinuousMap.End.one_apply]
  calc
    φ.toContinuousMap x = φ.toContinuousMap (φ.toContinuousMap y) := by rw [hy.symm]
    _ = (φ * φ).toContinuousMap y := by
      simp only [ContinuousMap.End.mul_apply]
    _ = φ.toContinuousMap y := by
      rw [φIdemp]
    _ = x := hy

-- theorem: if S ⊆ C(X,X) is a subsemigroup and consists of surjections,
-- then it contains Id_X
theorem surjectiveSubsemiContainsId
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{S : Set (ContinuousMap.End X)}
(nonemptyS : S.Nonempty)
(hSsubsemi : ∀ (ϕ ψ : (ContinuousMap.End X)), ϕ ∈ S → ψ ∈ S → ϕ * ψ ∈ S)
(hSsurject : ∀ (ϕ : (ContinuousMap.End X)), ϕ ∈ S → Function.Surjective ϕ)
(hScompactclos : IsCompact (closure S)) :
(1 : ContinuousMap.End X) ∈ closure S := by
  let cm : ContinuousMul (ContinuousMap.End X) := inferInstance
  have contmul := cm.continuous_mul
  have contleftmul :
    ∀ (r : ContinuousMap.End X), Continuous fun (x : ContinuousMap.End X) => x * r := by
      exact fun r ↦ Continuous.uncurry_right r contmul
  have csNon : (closure S).Nonempty := closure_nonempty_iff.mpr nonemptyS
  have csub : ∀ x ∈ (closure S), ∀ y ∈ (closure S), x * y ∈ (closure S) := by
    intro x hx y hy
    exact closureOfSubsemiIsSubsemi hSsubsemi x y hx hy
  have idempsource := exists_idempotent_in_compact_subsemigroup
    contleftmul
    (closure S)
    csNon
    hScompactclos
    csub
  obtain ⟨i, hi, iIdemp⟩ := idempsource
  have := surjectiveSubsemiUniqueIdempotent
    (surjectiveSetImpliesSurjectiveClosure hSsurject) i hi iIdemp
  rw [←this]
  exact hi

-- def: given S ⊆ C(X,X) is a subsemigroup consists of surjections with,
-- overline S compact, get group (overline S) with 1 = id_X
-- def: given S ⊆ C(X,X) is a commutative subsemigroup consists of surjections with,
-- overline S compact, get commgroup (overline S)
@[instance_reducible]
noncomputable
def commGroupFromSurjectiveSubsemiOfCXX
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{S : Set (ContinuousMap.End X)}
(nonemptyS : S.Nonempty)
(hSsurject : ∀ (ϕ : (ContinuousMap.End X)), ϕ ∈ S → Function.Surjective ϕ)
(hSsubsemi : ∀ (ϕ ψ : (ContinuousMap.End X)), ϕ ∈ S → ψ ∈ S → ϕ * ψ ∈ S)
(hScomm : ∀ (ϕ ψ : (ContinuousMap.End X)), ϕ ∈ S → ψ ∈ S → ϕ * ψ = ψ * ϕ)
(hScompactclos : IsCompact (closure S)) :
CommGroup (closure S) := by
  let cSSubMonoid : Submonoid (ContinuousMap.End X) :=
  {
    carrier := closure S
    mul_mem' {x y} := closureOfSubsemiIsSubsemi hSsubsemi x y
    one_mem' := surjectiveSubsemiContainsId nonemptyS hSsubsemi hSsurject hScompactclos
  }
  have hSIdemp : ∀ (x : cSSubMonoid), x * x = x → x = 1 := by
    intro x xIdemp
    have x1Idemp : x.1 * x.1 = x.1 := by
      rw [←Submonoid.coe_mul cSSubMonoid x x]
      exact congrArg (fun z => z.1) xIdemp
    have cSisSubsemi := closureOfSubsemiIsSubsemi hSsubsemi
    have cSisSurjective := surjectiveSetImpliesSurjectiveClosure hSsurject
    apply Subtype.ext
    exact surjectiveSubsemiUniqueIdempotent (S := closure S) cSisSurjective x x.2 x1Idemp
  have cSSubMonoidCmpt : IsCompact cSSubMonoid.carrier := hScompactclos
  letI : IsMulCommutative cSSubMonoid :=
    ⟨by
      exact
        {
          comm := by
            intro φ ψ
            apply Subtype.ext
            exact (closureOfCommSetIsCommSet hScomm) φ.1 ψ.1 φ.2 ψ.2
        }
    ⟩
  letI : Group cSSubMonoid := groupFromCompactSubmonoid cSSubMonoid cSSubMonoidCmpt hSIdemp
  letI : CommGroup cSSubMonoid := IsMulCommutative.instCommGroup
  simpa [cSSubMonoid] using
    (inferInstance : CommGroup cSSubMonoid)


-- theorem: given S ⊆ C(X,X) is a commutative subsemigroup consists of surjections with,
-- overline S compact, get ContinuousInv (overline S)
theorem groupFromPrecompactSubsemiHasContinuousInv
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{S : Set (ContinuousMap.End X)}
(nonemptyS : S.Nonempty)
(hSsurject : ∀ (ϕ : (ContinuousMap.End X)), ϕ ∈ S → Function.Surjective ϕ)
(hSsubsemi : ∀ (ϕ ψ : (ContinuousMap.End X)), ϕ ∈ S → ψ ∈ S → ϕ * ψ ∈ S)
(hScomm : ∀ (ϕ ψ : (ContinuousMap.End X)), ϕ ∈ S → ψ ∈ S → ϕ * ψ = ψ * ϕ)
(hScompactclos : IsCompact (closure S)) :
letI : CommGroup (closure S) :=
  commGroupFromSurjectiveSubsemiOfCXX nonemptyS hSsurject hSsubsemi hScomm hScompactclos
ContinuousInv (closure S) := by
  let : CommGroup (closure S) :=
    commGroupFromSurjectiveSubsemiOfCXX nonemptyS hSsurject hSsubsemi hScomm hScompactclos
  let hComp : CompactSpace (closure S) := isCompact_iff_compactSpace.mp hScompactclos
  let cSSubMonoid : Submonoid (ContinuousMap.End X) :=
  {
    carrier := closure S
    mul_mem' {x y} := closureOfSubsemiIsSubsemi hSsubsemi x y
    one_mem' := surjectiveSubsemiContainsId nonemptyS hSsubsemi hSsurject hScompactclos
  }
  have continuousMulForSubMonoid := Submonoid.continuousMul cSSubMonoid
  let hMul : ContinuousMul (closure S) := by
    change ContinuousMul cSSubMonoid
    exact continuousMulForSubMonoid
  exact
    @continuousInv_of_compactSpace
      (closure S)
      (commGroupFromSurjectiveSubsemiOfCXX
        nonemptyS hSsurject hSsubsemi hScomm hScompactclos).toGroup
      inferInstance
      hComp
      inferInstance
      hMul

-- theorem: given S ⊆ C(X,X) is a commutative subsemigroup consists of surjections with,
-- overline S compact, get IsTopologicalGroup (overline S)
theorem isTopologicalGroupFromSurjectiveSubsemiOfCXX
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
{S : Set (ContinuousMap.End X)}
(nonemptyS : S.Nonempty)
(hSsurject : ∀ (ϕ : (ContinuousMap.End X)), ϕ ∈ S → Function.Surjective ϕ)
(hSsubsemi : ∀ (ϕ ψ : (ContinuousMap.End X)), ϕ ∈ S → ψ ∈ S → ϕ * ψ ∈ S)
(hScomm : ∀ (ϕ ψ : (ContinuousMap.End X)), ϕ ∈ S → ψ ∈ S → ϕ * ψ = ψ * ϕ)
(hScompactclos : IsCompact (closure S)) :
letI : CommGroup (closure S) :=
  commGroupFromSurjectiveSubsemiOfCXX nonemptyS hSsurject hSsubsemi hScomm hScompactclos
IsTopologicalGroup (closure S) := by
  let commGroupcS : CommGroup (closure S) :=
    commGroupFromSurjectiveSubsemiOfCXX nonemptyS hSsurject hSsubsemi hScomm hScompactclos
  let cSSubMonoid : Submonoid (ContinuousMap.End X) :=
  {
    carrier := closure S
    mul_mem' {x y} := closureOfSubsemiIsSubsemi hSsubsemi x y
    one_mem' := surjectiveSubsemiContainsId nonemptyS hSsubsemi hSsurject hScompactclos
  }
  have continuousMulForSubMonoid := Submonoid.continuousMul cSSubMonoid
  let hMul : ContinuousMul (closure S) := by
    change ContinuousMul cSSubMonoid
    exact continuousMulForSubMonoid
  let hComp : CompactSpace (closure S) := isCompact_iff_compactSpace.mp hScompactclos
  let hInv : ContinuousInv (closure S) :=
    groupFromPrecompactSubsemiHasContinuousInv nonemptyS hSsurject hSsubsemi hScomm hScompactclos
  exact
    { continuous_mul := hMul.continuous_mul
      continuous_inv := hInv.continuous_inv }

/-- The open neighborhoods of 1 in a compact Hausdorff group
  are generated by finite intersections of neighborhoods of 1 by characters.
-/
theorem openPreimageInOpenSubsetTopCommGroup
{X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [CommGroup X]
[IsTopologicalGroup X] {W : Set X} (hW : IsOpen W) (hWone : (1 : X) ∈ W) :
∃ (d : ℕ) (φ : X → (Fin d → Circle)) (_ : ∀ (x y : X), φ (x * y) = (φ x) * (φ y))
(U : Set (Fin d → Circle)) (_ : IsOpen U) (_ : (1 : Fin d → Circle) ∈ U),
φ ⁻¹' U ⊆ W := by
  classical
  have hWcComp : IsCompact Wᶜ :=
    hW.isClosed_compl.isCompact
  have hchar :
      ∀ x : (Wᶜ : Set X),
        ∃ χ : PontryaginDual X, χ x.1 ≠ 1 := by
    intro x
    apply PontryaginDual.exists_apply_ne_one
    intro hx
    apply x.2
    simpa [hx] using hWone
  choose χ hχ using hchar
  have hnbr :
      ∀ x : (Wᶜ : Set X),
        ∃ V C : Set Circle,
          IsOpen V ∧
          (1 : Circle) ∈ V ∧
          V ⊆ C ∧
          IsClosed C ∧
          x.1 ∉ χ x ⁻¹' C := by
    intro x
    have h1 :
        (1 : Circle) ∈ ({χ x x.1}ᶜ : Set Circle) := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact Ne.intro fun a ↦ hχ x (id (Eq.symm a))
    have hnhd :
        ({χ x x.1}ᶜ : Set Circle) ∈ nhds (1 : Circle) :=
      IsOpen.mem_nhds isOpen_compl_singleton h1
    obtain ⟨C, hCnhd, hCclosed, hCsubset⟩ :=
      exists_mem_nhds_isClosed_subset hnhd
    obtain ⟨V, hVC, hVopen, hVone⟩ :=
      mem_nhds_iff.mp hCnhd
    refine ⟨V, C, hVopen, hVone, hVC, hCclosed, ?_⟩
    intro hx
    have h' := hCsubset hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_true_eq_false] at h'
  choose V C hVopen hVone hVC hCclosed hCmiss using hnbr
  let O : (Wᶜ : Set X) → Set X :=
    fun x => (χ x ⁻¹' C x)ᶜ
  have hOopen : ∀ x : (Wᶜ : Set X), IsOpen (O x) := by
    intro x
    dsimp [O]
    exact (hCclosed x).preimage (χ x).continuous |>.isOpen_compl
  have hOcover : Wᶜ ⊆ ⋃ x : (Wᶜ : Set X), O x := by
    intro x hx
    apply Set.mem_iUnion.mpr
    exact ⟨⟨x, hx⟩, by
      dsimp [O]
      exact hCmiss ⟨x, hx⟩⟩
  obtain ⟨F, hF⟩ :=
    hWcComp.elim_finite_subcover O hOopen hOcover
  let d : ℕ := F.card
  let e : F ≃ Fin d := F.equivFin
  let zsel : Fin d → (Wᶜ : Set X) :=
    fun j => (e.symm j).1
  let φ : X → (Fin d → Circle) :=
    fun x j => χ (zsel j) x
  have φHom :
      ∀ x y : X, φ (x * y) = (φ x) * (φ y) := by
    intro x y
    funext j
    exact map_mul (χ (zsel j)) x y
  let U : Set (Fin d → Circle) :=
    ⋂ j : Fin d, (Function.eval j) ⁻¹' V (zsel j)
  have hUopen : IsOpen U := by
    dsimp [U]
    exact isOpen_iInter_of_finite fun j =>
      (hVopen (zsel j)).preimage (continuous_apply j)
  have hUone : (1 : Fin d → Circle) ∈ U := by
    simp only [U, Set.mem_iInter, Set.mem_preimage]
    intro j
    exact hVone (zsel j)
  refine ⟨d, φ, φHom, U, hUopen, hUone, ?_⟩
  intro y hy
  by_contra hyW
  have hyWc : y ∈ Wᶜ := hyW
  have hycover := hF hyWc
  rcases Set.mem_iUnion.mp hycover with ⟨z, hycover⟩
  rcases Set.mem_iUnion.mp hycover with ⟨hzF, hyzO⟩
  let j : Fin d := e ⟨z, hzF⟩
  have hyV : χ z y ∈ V z := by
    have h := Set.mem_iInter.mp hy j
    simpa [φ, zsel, j] using h
  have hyC : χ z y ∈ C z :=
    hVC z hyV
  have hyPre : y ∈ χ z ⁻¹' C z := by
    exact hyC
  have hyzO' : y ∉ χ z ⁻¹' C z := by
    simpa [O] using hyzO
  exact hyzO' hyPre

/- This is the application of ArzelaAscoli that we need.  ArzelaAscoli is stated in
general terms in Mathlib. -/
theorem compactClosureOfUniformEquicontinuous
    {X S : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
    (i : S → ContinuousMap.End X) (hi : UniformEquicontinuous fun s x => (i s).1 x) :
    IsCompact (closure (Set.range i)) := by
      let 𝔖 : Set (Set X) := {K | IsCompact K}
      let CXXEnd := ContinuousMap.End X
      apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
          (𝔖 := 𝔖)
          (F := fun f : CXXEnd => (f.1 : X → X))
          (s := Set.range i)
      · intro K hK
        exact hK
      · have hclembCXX :
        Topology.IsClosedEmbedding
          (ContinuousMap.toUniformOnFunIsCompact :
            C(X,X) → UniformOnFun X X {K : Set X | IsCompact K}) := by
              constructor
              · exact
                  ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding
              · rw [ContinuousMap.range_toUniformOnFunIsCompact]
                exact
                  UniformOnFun.isClosed_setOfPred_continuous
                    CompactlyCoherentSpace.isCoherentWith
        have hEnd :
            Topology.IsClosedEmbedding
              (ContinuousMap.End.toContinuousMap :
                CXXEnd → C(X,X)) := by
          exact
            ContinuousMap.End.homeomorphContinuousMap.isHomeomorph.isClosedEmbedding
        have hclemb :
            Topology.IsClosedEmbedding
              (ContinuousMap.toUniformOnFunIsCompact ∘
                ContinuousMap.End.toContinuousMap :
                CXXEnd → UniformOnFun X X {K : Set X | IsCompact K}) := by
          exact hclembCXX.comp hEnd
        change Topology.IsClosedEmbedding
          (ContinuousMap.toUniformOnFunIsCompact ∘ ContinuousMap.End.toContinuousMap :
            CXXEnd → UniformOnFun X X {K : Set X | IsCompact K})
        exact hclemb
      · intro K hK
        have hrange : Equicontinuous (fun f : ↥(Set.range i) => (f.1 : X → X)) :=
          by
            classical
            let j : ↥(Set.range i) → S :=
              fun f => Classical.choose f.property
            have hj (f : ↥(Set.range i)) : i (j f) = f.1 :=
              Classical.choose_spec f.property
            have hfamily :
              ((fun s x => (i s).1 x) ∘ j)
                =
              (fun f : ↥(Set.range i) => (f.1 : X → X)) := by
                funext f x
                change (i (j f)).1 x = f.1 x
                rw [hj f]
            rw [← hfamily]
            exact hi.equicontinuous.comp j
        exact hrange.equicontinuousOn K
      · intro K hK x hx
        refine ⟨Set.univ, isCompact_univ, ?_⟩
        intro f hf
        simp

end Bohr_prelims


section Bohr_sets

/-- A subset `A ⊆ S` is Bohr_0 if there exists a semigroup homomorphism
`ϕ : S → T^d` and an open set `U ⊆ T^d` containing `0` such that `A ⊇ ϕ ⁻¹ U`. -/
def isBohrZero
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop := ∃ (d : ℕ) (φ : S → (Fin d → Circle))
  (_ : ∀ (s t : S), φ (s * t) = (φ s) * (φ t)) (U : Set (Fin d → Circle))
  (_ : IsOpen U) (_ : 1 ∈ U),
  Set.preimage φ U ⊆ A

/-- If `A ⊆ S` is Bohr_0 and `A ⊆ B`, then `B` is Bohr_0. -/
theorem bohrZeroIsMonotone
{S : Type*} [Semigroup S] [Nonempty S]
{A B : Set S} (hA : isBohrZero A) (hAB : A ⊆ B) :
isBohrZero B := by
  unfold isBohrZero
  unfold isBohrZero at hA
  rcases hA with ⟨k, φ, h1, h2, h3, h4, h5⟩
  use k
  use φ
  use h1
  use h2
  use h3
  use h4
  apply Set.Subset.trans h5 hAB

/-- The family of Bohr_0 subsets of a semigroup -/
def bohrZeroFamily
(S : Type*) [Semigroup S] [Nonempty S] : Family S :=
{
  sets := {A : Set S | isBohrZero A}
  upward_closed := by
    intro A B hA hAB
    exact bohrZeroIsMonotone hA hAB
}

/-- The `d`-torus acting on itself. -/
noncomputable
def torusDynamicalSystem
(d : ℕ) :
DynamicalSystem (Fin d → Circle) (Fin d → Circle) :=
{
  map := by
    intro s x
    exact s * x
  mapMult := by
    intro s t x
    exact mul_assoc s t x
  mapCont := by
    exact fun s ↦ (uniformContinuous_mul_left s).continuous
}

lemma easyAlgebraLemma
{G : Type*} [CommGroup G] (x y z : G) :
(z * x)⁻¹ * (z * y) = x⁻¹ * y := by --aesop also works!
  have stepone : (z * x)⁻¹ = x⁻¹ * z⁻¹ := by
    exact DivisionMonoid.mul_inv_rev z x
  have steptwo : (z * x)⁻¹ * (z * y) = (x⁻¹ * z⁻¹) * (z * y) := by
    rw [stepone]
  have stepthree : (x⁻¹ * z⁻¹) * (z * y) = ((x⁻¹ * z⁻¹) * z) * y := by
    exact Eq.symm (mul_assoc (x⁻¹ * z⁻¹) z y)
  have stepfour : (x⁻¹ * z⁻¹) * z = x⁻¹ * (z⁻¹ * z) := by
    exact mul_assoc x⁻¹ z⁻¹ z
  have stepfive : ((x⁻¹ * z⁻¹) * z) * y = (x⁻¹ * (z⁻¹ * z)) * y := by
    rw [stepfour]
  have stepsix : z⁻¹ * z = 1 := by
    exact inv_mul_cancel z
  have : (z * x)⁻¹ * (z * y) = x⁻¹ * y := by
    rw [steptwo]
    rw [stepthree]
    rw [stepfive]
    rw [stepsix]
    simp only [mul_one]
  rw [this]

theorem torusDSIsEquicontinuous
(d : ℕ) :
isEquicontinuousSystem (torusDynamicalSystem d) :=
by
  let T := Fin d → Circle
  intro α αOpen αDiagonal
  -- on a compact space, an open neighbourhood of the diagonal is an entourage
  have αUniformity : α ∈ uniformity T := by
    rw [← nhdsSet_diagonal_eq_uniformity]
    exact mem_nhdsSet.mpr ⟨α, subset_rfl, αOpen, αDiagonal⟩
  rw [uniformity_eq_comap_inv_mul_nhds_one] at αUniformity
  obtain ⟨V, hV, hVsub⟩ := αUniformity
  let β : Set (T × T) := {p | p.1⁻¹ * p.2 ∈ interior V}
  have βOpen : IsOpen β :=
    isOpen_interior.preimage (continuous_fst.inv.mul continuous_snd)
  have βDiagonal : Set.diagonal T ⊆ β := by
    rintro ⟨a, b⟩ hab
    have hab' : a = b := hab
    subst hab'
    change a⁻¹ * a ∈ interior V
    rw [inv_mul_cancel a]
    exact mem_interior_iff_mem_nhds.mpr hV
  refine ⟨β, βOpen, βDiagonal, ?_⟩
  rintro i q ⟨p, hp, rfl⟩
  apply hVsub
  have hp' : p.1⁻¹ * p.2 ∈ interior V := hp
  change (i * p.1)⁻¹ * (i * p.2) ∈ V
  rw [easyAlgebraLemma p.1 p.2 i]
  exact interior_subset hp'

-- theorem torusDSIsEquicontinuousOrig
-- (d : ℕ) :
-- isEquicontinuousSystem (torusDynamicalSystem d) :=
-- by -- needs to be updated to equiv2
--   let T := Fin d → Circle
--   intro α αUniformity filterOnProd temp
--   simp only [Set.mem_image, Set.mem_diagonal_iff, Prod.exists, exists_eq_left'] at temp
--   obtain ⟨a, ha⟩ := temp
--   rw [←ha]
--   simp only [Set.mem_ofPred_eq]
--   rw [uniformity_eq_comap_inv_mul_nhds_one] at αUniformity
--   obtain ⟨V, hV, hVsub⟩ := αUniformity
--   let β : Set (T × T) := {p | p.1⁻¹ * p.2 ∈ V}
--   have hβu : β ∈ uniformity T := by
--     rw [uniformity_eq_comap_inv_mul_nhds_one]
--     exact Filter.mem_comap.mpr ⟨V, hV, subset_rfl⟩
--   have βSubset : β ⊆ {x | ∀ (i : T),
--     ((torusDynamicalSystem d).map i x.1, (torusDynamicalSystem d).map i x.2) ∈ α} := by
--     intro p hp i
--     apply hVsub
--     change (i * p.1)⁻¹ * (i * p.2) ∈ V
--     rw [easyAlgebraLemma p.1 p.2 i]
--     exact hp
--   have βInNhds : β ∈ nhds (a, a) := by
--     exact (nhds_le_uniformity a) hβu
--   exact Filter.mem_of_superset βInNhds βSubset

theorem torusDSIsDistal
(d : ℕ) :
isDistalSystem (torusDynamicalSystem d) := by
  intro x y hxy
  apply inv_mul_eq_one.mp
  apply pure_le_nhds_iff.mp
  have closetoone : ∀ U ∈ nhds 1, x⁻¹ * y ∈ U := by
    intro U hU
    let T := Fin d → Circle
    let β : Set (T × T) := {p | p.1⁻¹ * p.2 ∈ U}
    have hβu : β ∈ uniformity T := by
      rw [uniformity_eq_comap_inv_mul_nhds_one]
      simp only [Filter.mem_comap]
      use U
      exact ⟨hU, by trivial⟩
    have := hxy β
    have hβn : β ∈ nhdsSet (Set.diagonal T) := nhdsSet_diagonal_le_uniformity hβu
    obtain ⟨s, hs⟩ := hxy β hβn
    unfold torusDynamicalSystem β at hs
    simp only at hs
    change (s * x)⁻¹ * (s * y) ∈ U at hs
    rw [easyAlgebraLemma x y s] at hs
    exact hs
  exact closetoone

/-- If `A ⊆ S` is Bohr_0, then there exists a minimal, equicontinuous dynamical
system `X`, a point `x`, and an open set `U` containing `x` so that `R(x,U) ⊆ A`. -/
theorem bohrZeroSetsContainEquiReturns
{S : Type*} [CommSemigroup S] [SNonempty : Nonempty S] (A : Set S) :
isBohrZero A → ∃ (X : Type) (_ : TopologicalSpace X)
(_ : CompactSpace X) (_ : T2Space X) (_ : Nonempty X)
(dSystem : DynamicalSystem S X) (_ : isEquicontinuousSystem dSystem)
(_ : isMinimalSystem dSystem) (x : X) (U : Set X) (_ : x ∈ U) (_ : IsOpen U),
visitTimeSet dSystem x U ⊆ A :=
by
  intro hBZA
  obtain ⟨d,φ,φHom,U,UisOpen,oneinU,preimageUinA⟩ := hBZA
  have φSemiHom : SemigroupHom φ :=
  {
    hom_prop := φHom
  }
  let torusDS := torusDynamicalSystem d
  let homTorusDS := homDynamicalSystem φ torusDS
  have homTorusDSisEqui :=
    homSystemOfEquicontinuousSystemIsEquicontinuous φ (torusDSIsEquicontinuous d)
  have homTorusDSisDistal : isDistalSystem homTorusDS :=
    homSystemOfDistalSystemIsDistal φ (torusDSIsDistal d)
  let x : Fin d → Circle := 1
  let X := orbitClosure homTorusDS x
  let V := {z : X | z.1 ∈ U}
  have VisOpen : IsOpen V := UisOpen.preimage continuous_subtype_val
  have orbClosPresystem := orbitClosureIsNonemptyCompactT2InvariantSubset homTorusDS x
  let dSystem := fromNonemptyCompactT2InvariantSubsetToSystem homTorusDS orbClosPresystem
  have : CompactSpace ↑(orbitClosure homTorusDS x) := by
    apply isCompact_iff_compactSpace.mp
    apply IsClosed.isCompact
    apply isClosed_closure
  have : Nonempty ↑(orbitClosure homTorusDS x) := by
    apply Set.Nonempty.to_subtype
    have SNonempty2 : Nonempty S := SNonempty
    obtain ⟨s⟩ := SNonempty2
    have : homTorusDS.map s x ∈ orbitClosure homTorusDS x := by
      apply subset_closure
      use s
    exact ⟨homTorusDS.map s x, this⟩
  have xUR := distalImpliesSemisimple homTorusDSisDistal x
  have xInX : x ∈ X := URPointBelongsToOrbitClosure homTorusDS xUR
  have hMin : isMinimalSystem dSystem :=
    (minimalSubsetIffMinimalSubsystem homTorusDS orbClosPresystem).mp
      (orbitClosureOfURPointIsMinimalSubset homTorusDS xUR)
  have hEqui : isEquicontinuousSystem dSystem := by
     exact subsysOfEquiIsEqui homTorusDSisEqui orbClosPresystem
  have xInV : ⟨x,xInX⟩ ∈ V := by
    unfold V
    simp only [Set.mem_ofPred_eq]
    exact oneinU
  have visitTimesxToVinA : visitTimeSet dSystem ⟨x,xInX⟩ V ⊆ A :=
    calc
      visitTimeSet dSystem ⟨x,xInX⟩ V ⊆ visitTimeSet homTorusDS x U := by
        intro s hs
        unfold V visitTimeSet at hs
        simp only [Set.mem_preimage] at hs
        exact hs
      _ ⊆ φ ⁻¹' U := by
        intro t ht
        unfold visitTimeSet at ht
        simp only [Set.mem_preimage] at ht
        unfold homTorusDS homDynamicalSystem at ht
        simp only at ht
        unfold torusDS at ht
        unfold torusDynamicalSystem at ht
        simp only at ht
        unfold x at ht
        simp only [mul_one] at ht
        exact ht
      _ ⊆ A := preimageUinA
  use X
  use by infer_instance
  use by infer_instance
  use by infer_instance
  use by infer_instance
  use dSystem
  use hEqui
  use hMin
  use ⟨x,xInX⟩
  use V

/-- If `A ⊆ S` is a set containing a set of returns of a point to a neighborhood
in a minimal, equicontinuous system, then `A` is Bohr_0. -/
theorem equiReturnsAreBohrZero
{S : Type*} [CommSemigroup S] [Nonempty S] (A : Set S) :
(∃ (X : Type*) (_ : TopologicalSpace X) (_ : CompactSpace X) (_ : T2Space X)
(_ : Nonempty X) (dSystem : DynamicalSystem S X)
(_ : isEquicontinuousSystem dSystem) (_ : isMinimalSystem dSystem) (x : X)
(U : Set X) (_ : x ∈ U) (_ : IsOpen U), visitTimeSet dSystem x U ⊆ A) →
isBohrZero A := by
  intro h
  obtain ⟨X,_,_,_,_,dSystem,hEqui,hMin,x,U,xInU,UOpen,visitsxUinA⟩ := h
  let CXXEnd := ContinuousMap.End X
  let i : S → CXXEnd := fun (s : S) ↦ ⟨dSystem.map s, dSystem.mapCont s⟩
  have iHom : ∀ (s t : S), i (s * t) = (i s) * (i t) := by
    intro s t
    refine ContinuousMap.End.ext ?_
    intro x
    rw [ContinuousMap.End.mul_apply (i s) (i t) x]
    unfold i
    simp only [ContinuousMap.coe_mk]
    rw [dSystem.mapMult]
  let iS := Set.range i
  have dSystemSurjective := minimalCommActionIsSurjective hMin
  have iSSurjective : ∀ (f : CXXEnd), f ∈ iS → Function.Surjective f := by
    intro f hf
    obtain ⟨s, hs1, hs2⟩ := hf
    unfold i
    simp only [ContinuousMap.coe_mk]
    exact dSystemSurjective s
  have iSSemi : ∀ (f g : CXXEnd), f ∈ iS → g ∈ iS → f * g ∈ iS := by
    intro f g hf hg
    obtain ⟨s, hs1, hs2⟩ := hf
    obtain ⟨t, ht1, ht2⟩ := hg
    rw [←iHom s t]
    exact Set.mem_range_self (s * t)
  have iSComm : ∀ (f g : CXXEnd), f ∈ iS → g ∈ iS → f * g = g * f := by
    intro f g hf hg
    obtain ⟨s, hs1, hs2⟩ := hf
    obtain ⟨t, ht1, ht2⟩ := hg
    rw [←iHom s t]
    rw [←iHom t s]
    have Scomm : s * t = t * s := mul_comm s t
    exact congrArg i Scomm
  have iSEqui : UniformEquicontinuous (fun (s : S) ↦ (i s).1) := by
    unfold i
    simp only [ContinuousMap.coe_mk]
    -- on a compact space the uniformity is the neighbourhood filter of the diagonal, so an
    -- entourage `α` contains an open `α' ⊇ Δ`, to which `hEqui` applies
    intro α hα
    have hαNhds : α ∈ nhdsSet (Set.diagonal X) := by
      rw [nhdsSet_diagonal_eq_uniformity]
      exact hα
    obtain ⟨α', hα'sub, hα'open, hα'diag⟩ := mem_nhdsSet.mp hαNhds
    obtain ⟨β, hβopen, hβdiag, hβprop⟩ := hEqui α' hα'open hα'diag
    have hβUniformity : β ∈ uniformity X := by
      rw [← nhdsSet_diagonal_eq_uniformity]
      exact mem_nhdsSet.mpr ⟨β, subset_rfl, hβopen, hβdiag⟩
    refine Filter.mem_of_superset hβUniformity ?_
    intro p hp s
    exact hα'sub (hβprop s ⟨p, hp, rfl⟩)
  let iSClos := closure iS
  have iSClosCompact : IsCompact iSClos := compactClosureOfUniformEquicontinuous i iSEqui
  let : CompactSpace iSClos := isCompact_iff_compactSpace.mp iSClosCompact
  have nonemptyS : iS.Nonempty := Set.range_nonempty i
  let iSClosGroup :=
    commGroupFromSurjectiveSubsemiOfCXX nonemptyS iSSurjective iSSemi iSComm iSClosCompact
  have iSClosGroupIsTopGroup :=
    isTopologicalGroupFromSurjectiveSubsemiOfCXX nonemptyS iSSurjective iSSemi iSComm iSClosCompact
  have oneisonepre : iSClosGroup.one = (1 : CXXEnd) := by rfl
  have oneIniS : (1 : CXXEnd) ∈ iSClos := by
    rw [←oneisonepre]
    exact iSClosGroup.one.2
  have oneIsone : ⟨(1 : CXXEnd), oneIniS⟩ = (1 : iSClos) := by rfl
  let ξ : iSClos → X := fun (f : iSClos) ↦ f.1 x
  have ξCont : Continuous ξ := by
    let eval := fun (f : C(X,X)) ↦ f x
    let eval2 : CXXEnd → X := eval ∘ ContinuousMap.End.toContinuousMap
    have evalcont : Continuous eval := by
      exact continuous_eval_const x
    have eval2cont : Continuous eval2 := by
      refine Continuous.comp evalcont ContinuousMap.End.continuous_toContinuousMap
    exact eval2cont.comp continuous_subtype_val
  let W := ξ ⁻¹' U
  have WOpen : IsOpen W := ξCont.isOpen_preimage U UOpen
  have oneinW : (1 : iSClos) ∈ W := by
    rw [←oneIsone]
    unfold W
    simp only [Set.mem_preimage]
    unfold ξ
    have : (1 : CXXEnd).toContinuousMap x = x := by
      exact ContinuousMap.End.one_apply x
    rw [this]
    exact xInU
  have oneIsId : (1 : CXXEnd).toContinuousMap = ContinuousMap.id X := by --do we use this?
    exact ContinuousMap.ext (congrFun rfl)
  have invWinRxU : i ⁻¹' W ⊆ visitTimeSet dSystem x U := by
    intro s hs
    unfold W ξ i at hs
    simp only [Set.mem_preimage, Set.mem_image, Subtype.exists, exists_and_left, exists_prop,
      exists_eq_right_right, ContinuousMap.coe_mk] at hs
    exact hs.1
  obtain ⟨d,ψ,ψHom,V,VisOpen,oneInV,preimageVinW⟩ :=
    openPreimageInOpenSubsetTopCommGroup (X := iSClos) WOpen oneinW
  let j : S → iSClos :=
    fun (s : S) ↦ ⟨i s, subset_closure (Set.mem_range_self s)⟩
  have jHom : ∀ (s t : S), j (s * t) = (j s) * (j t) := by
    intro s t
    have : (j (s * t) : iSClos) = (j s : iSClos) * (j t : iSClos) := by
      unfold j
      exact SetCoe.ext (iHom s t)
    rw [this]
  let φ := ψ ∘ j
  have φHom : ∀ (s t : S), φ (s * t) = (φ s) * (φ t) := by
    unfold φ
    intro s t
    simp only [Function.comp_apply]
    rw [jHom]
    rw [ψHom]
  have φpreimInA : φ ⁻¹' V ⊆ A :=
    calc φ ⁻¹' V ⊆ j ⁻¹' (ψ ⁻¹' V) := by rfl
    _ ⊆ j ⁻¹' W := Set.preimage_mono preimageVinW
    _ ⊆ visitTimeSet dSystem x U := Set.preimage_subset_iff.mpr fun a a_1 ↦ a_1
    _ ⊆ A := visitsxUinA
  use d, φ, φHom, V, VisOpen, oneInV, φpreimInA

-- /-- A set `A ⊆ S` is a set of Bohr recurrence if for all minimal, equicontinuous
-- actions of `S` on a compact, Hausdorff space `X`, all points `x ∈ X` and
-- all neighborhoods `U` of `x`, `A ∩ R(x,U) ≠ ∅` -/
-- def isSetOfBohrRecurrence
-- {S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
-- Prop :=
-- by sorry

-- /-- If `A ⊆ S` is a set of Bohr recurrence and `A ⊆ B`, then `B`
-- is a set of Bohr recurrence. -/
-- theorem setOfBohrRecurrenceIsMonotone
-- {S : Type*} [Semigroup S] [Nonempty S]
-- {A B : Set S} (hA : isSetOfBohrRecurrence A) (hAB : A ⊆ B) :
-- isSetOfBohrRecurrence B :=
-- by sorry

-- /-- The family of Bohr_0 subsets of a semigroup -/
-- def setOfBohrRecurrenceFamily
-- (S : Type*) [Semigroup S] [Nonempty S] : Family S :=
-- {
--   sets := {A : Set S | isSetOfBohrRecurrence A}
--   upward_closed := by
--     intro A B hA hAB
--     exact setOfBohrRecurrenceIsMonotone hA hAB
-- }

/- The family of Bohr_0 sets is a filter -/
-- Here I've spelled out the requirement for a filter.
-- Later update with isFilterFamily (bohrZeroFamily S)
-- theorem bohrZeroFamilyIsFilter
-- {S : Type*} [CommSemigroup S] [Nonempty S] :
-- (bohrZeroFamily S).sets.Nonempty ∧ (∀ (A B : Set S), A ∈ (bohrZeroFamily S) →
--   B ∈ (bohrZeroFamily S) → A ∩ B ∈ (bohrZeroFamily S)) :=
-- by
--   constructor
--   · -- `S` is Bohr_0 in itself, via the trivial homomorphism into the `0`-dimensional torus
--     exact ⟨Set.univ, 0, fun _ ↦ 1, fun _ _ ↦ (one_mul 1).symm, Set.univ, isOpen_univ,
--       Set.mem_univ 1, Set.subset_univ _⟩
--   · rintro A B ⟨k, φ, hφ, U, hUopen, h1U, hUA⟩ ⟨l, ψ, hψ, V, hVopen, h1V, hVB⟩
--     -- `s ↦ (φ s, ψ s) : S → 𝕋^(k+l)` is a homomorphism and `U × V` is an open
--     -- neighbourhood of the identity of `𝕋^(k+l)`
--     refine ⟨k + l, fun s ↦ Fin.append (φ s) (ψ s), fun s t ↦ ?_,
--       (fun x : (Fin (k + l) → Circle) ↦ (fun i ↦ x (Fin.castAdd l i))) ⁻¹' U ∩
--         (fun x : (Fin (k + l) → Circle) ↦ (fun i ↦ x (Fin.natAdd k i))) ⁻¹' V, ?_, ?_, ?_⟩
--     · -- appending pointwise products is the pointwise product of the appended families
--       funext i
--       induction i using Fin.addCases with
--       | left i => simp only [Pi.mul_apply, Fin.append_left, hφ]
--       | right i => simp only [Pi.mul_apply, Fin.append_right, hψ]
--     · exact (hUopen.preimage (continuous_pi fun i ↦ continuous_apply (Fin.castAdd l i))).inter
--         (hVopen.preimage (continuous_pi fun i ↦ continuous_apply (Fin.natAdd k i)))
--     · exact ⟨h1U, h1V⟩
--     · -- `(φ ⊗ ψ)⁻¹ (U × V) = φ⁻¹ U ∩ ψ⁻¹ V ⊆ A ∩ B`
--       rintro s ⟨hsU, hsV⟩
--       have hφs : (fun i ↦ Fin.append (φ s) (ψ s) (Fin.castAdd l i)) = φ s := by
--         funext i
--         exact Fin.append_left _ _ i
--       have hψs : (fun i ↦ Fin.append (φ s) (ψ s) (Fin.natAdd k i)) = ψ s := by
--         funext i
--         exact Fin.append_right _ _ i
--       have hsU' : (fun i ↦ Fin.append (φ s) (ψ s) (Fin.castAdd l i)) ∈ U := hsU
--       have hsV' : (fun i ↦ Fin.append (φ s) (ψ s) (Fin.natAdd k i)) ∈ V := hsV
--       rw [hφs] at hsU'
--       rw [hψs] at hsV'
--       exact ⟨hUA hsU', hVB hsV'⟩

/-- The family of Bohr_0 sets is a filter -/
theorem bohrZeroFamilyIsFilter
{S : Type*} [Semigroup S] [Nonempty S] :
isFilterFamily (bohrZeroFamily S) :=
by
  constructor
  · -- `S` is Bohr_0 in itself, via the trivial homomorphism into the `0`-dimensional torus
    have : (bohrZeroFamily S).sets.Nonempty :=
      ⟨Set.univ, 0, fun _ ↦ 1, fun _ _ ↦ (one_mul 1).symm, Set.univ, isOpen_univ,
        Set.mem_univ 1, Set.subset_univ _⟩
    exact (notEmptyFam (bohrZeroFamily S)).mpr this
  · rintro A B ⟨k, φ, hφ, U, hUopen, h1U, hUA⟩ ⟨l, ψ, hψ, V, hVopen, h1V, hVB⟩
    -- `s ↦ (φ s, ψ s) : S → 𝕋^(k+l)` is a homomorphism and `U × V` is an open
    -- neighbourhood of the identity of `𝕋^(k+l)`
    refine ⟨k + l, fun s ↦ Fin.append (φ s) (ψ s), fun s t ↦ ?_,
      (fun x : (Fin (k + l) → Circle) ↦ (fun i ↦ x (Fin.castAdd l i))) ⁻¹' U ∩
        (fun x : (Fin (k + l) → Circle) ↦ (fun i ↦ x (Fin.natAdd k i))) ⁻¹' V, ?_, ?_, ?_⟩
    · -- appending pointwise products is the pointwise product of the appended families
      funext i
      induction i using Fin.addCases with
      | left i => simp only [Pi.mul_apply, Fin.append_left, hφ]
      | right i => simp only [Pi.mul_apply, Fin.append_right, hψ]
    · exact (hUopen.preimage (continuous_pi fun i ↦ continuous_apply (Fin.castAdd l i))).inter
        (hVopen.preimage (continuous_pi fun i ↦ continuous_apply (Fin.natAdd k i)))
    · exact ⟨h1U, h1V⟩
    · -- `(φ ⊗ ψ)⁻¹ (U × V) = φ⁻¹ U ∩ ψ⁻¹ V ⊆ A ∩ B`
      rintro s ⟨hsU, hsV⟩
      have hφs : (fun i ↦ Fin.append (φ s) (ψ s) (Fin.castAdd l i)) = φ s := by
        funext i
        exact Fin.append_left _ _ i
      have hψs : (fun i ↦ Fin.append (φ s) (ψ s) (Fin.natAdd k i)) = ψ s := by
        funext i
        exact Fin.append_right _ _ i
      have hsU' : (fun i ↦ Fin.append (φ s) (ψ s) (Fin.castAdd l i)) ∈ U := hsU
      have hsV' : (fun i ↦ Fin.append (φ s) (ψ s) (Fin.natAdd k i)) ∈ V := hsV
      rw [hφs] at hsU'
      rw [hψs] at hsV'
      exact ⟨hUA hsU', hVB hsV'⟩

/-- A subset `A` of a semigroup `S` is a set of Bohr recurrence if it has
non-empty intersection with every `Bohr_0` subset of `S` -/
def isSetOfBohrRecurrence
{S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
Prop :=
A ∈ (bohrZeroFamily S)*

/-- The family of Bohr_0 subsets of a semigroup -/
def setOfBohrRecurrenceFamily
(S : Type*) [Semigroup S] [Nonempty S] :
Family S :=
(bohrZeroFamily S)*

/-- A set of Bohr recurrence is nonempty -/
theorem setOfBohrRecurrenceNonempty
{S : Type*} [Semigroup S] [Nonempty S]
(A : Set S) (hABohrRec : isSetOfBohrRecurrence A) :
A.Nonempty := by
  simp only [isSetOfBohrRecurrence, HasFamDual.famDual] at hABohrRec
  unfold Family.famDual at hABohrRec
  simp only [famDual] at hABohrRec
  have hExist1 : ∃ B : Set S, isBohrZero B := by
    simp only [isBohrZero, exists_prop]
    use Set.univ
    use 0
    use fun _ ↦ 1
    constructor
    · intro s t
      simp
    · use Set.univ
      constructor
      · simp
      constructor
      · simp
      · simp
  have hExistBohrZero : ∃ B : Set S, B ∈ bohrZeroFamily S := by
    rcases hExist1 with ⟨B, hB⟩
    use B
    exact hB
  rcases hExistBohrZero with ⟨B, hB⟩
  specialize hABohrRec B hB
  apply Set.inter_nonempty.mp at hABohrRec
  rcases hABohrRec with ⟨x, hx1, hx2⟩
  exact ⟨x, hx1⟩

/-- If `A ⊆ S` is a set of Bohr recurrence and `A ⊆ B`, then `B`
is a set of Bohr recurrence. -/
theorem setOfBohrRecurrenceIsMonotone
{S : Type*} [Semigroup S] [Nonempty S]
{A B : Set S} (hA : isSetOfBohrRecurrence A) (hAB : A ⊆ B) :
isSetOfBohrRecurrence B :=
(setOfBohrRecurrenceFamily S).2 A B hA hAB

-- theorem bohrZeroiffCompNotSetOfRec
-- {S : Type*} [Semigroup S] [Nonempty S] (A : Set S) :
-- isSetOfBohrRecurrence A ↔ ¬(isBohrZero Aᶜ) :=
--   by sorry
  -- This should be easy logical consequence of the definitions

/- The families of Bohr_0 sets and sets of Bohr recurrence are dual -/
-- Something happens upstream regarding "dualEquivForm" that the proof no longer work
-- Need to fix
-- theorem dualBohrZeroSetsOfBohrRecurrence
-- {S : Type*} [Semigroup S] [Nonempty S] :
-- (bohrZeroFamily S)* = (setOfBohrRecurrenceFamily S) :=
-- by sorry
  -- ext A
  -- have dualEquivForm : ((bohrZeroFamily S)*).sets = {A : Set S | Aᶜ ∉ bohrZeroFamily S} :=
  --   famDualAlt (bohrZeroFamily S)
  -- rw [dualEquivForm]
  -- change A ∈ {A | Aᶜ ∉ (bohrZeroFamily S).sets} ↔ A ∈ (setOfBohrRecurrenceFamily S).sets
  -- unfold bohrZeroFamily
  -- unfold setOfBohrRecurrenceFamily
  -- simp only [Set.mem_ofPred_eq]
  -- exact Iff.symm (bohrZeroiffCompNotSetOfRec A)

/-- The family of sets of Bohr recurrence is partition regular -/
theorem setOfBohrRecurrenceFamilyIsPR
(S : Type*) [Semigroup S] [Nonempty S] :
isPRFamily (setOfBohrRecurrenceFamily S) :=
(familyIsPRIffDualIsFilter (bohrZeroFamily S)).mp bohrZeroFamilyIsFilter

/-- In a commutative semigroup, if set is a set of Bohr recurrence,
then it contains the time of return of a point to a neighborhood of itself
in a minimal dynamical system. -/
theorem setOfBohrRecurrenceImpliesTimeOfRecForMinEqui
{S : Type*} [CommSemigroup S] [Nonempty S] (A : Set S) :
isSetOfBohrRecurrence A → ∀ (X : Type*) (_ : TopologicalSpace X)
(_ : CompactSpace X) (_ : T2Space X) (_ : Nonempty X)
(dSystem : DynamicalSystem S X) (_ : isEquicontinuousSystem dSystem)
(_ : isMinimalSystem dSystem) (x : X) (U : Set X) (_ : x ∈ U) (_ : IsOpen U),
∃ (s : S) (_ : s ∈ A), dSystem.map s x ∈ U := by
  intro hA X Xtop Xcmpt XT2 XNon dSystem hEqui hMin x U xInU UOpen
  have : ∀ (B : Set S), ((∃ (X : Type u_2) (_ : TopologicalSpace X)
    (_ : CompactSpace X) (_ : T2Space X) (_ : Nonempty X)
    (dSystem : DynamicalSystem S X) (_ : isEquicontinuousSystem dSystem)
    (_ : isMinimalSystem dSystem) (x : X) (U : Set X) (_ : x ∈ U) (_ : IsOpen U),
    visitTimeSet dSystem x U ⊆ B) → isBohrZero B) := equiReturnsAreBohrZero
  have visitdcS : isBohrZero (visitTimeSet dSystem x U) := by
    apply this (visitTimeSet dSystem x U)
    use X, Xtop, Xcmpt, XT2, XNon, dSystem, hEqui, hMin, x, U, xInU, UOpen
  obtain ⟨s, hsA, hsV⟩ := hA (visitTimeSet dSystem x U) visitdcS
  use s, hsA, hsV

/-- In a commutative semigroup, if a set contains the time of return of
a point to a neighborhood of itself in any minimal equicontinuous system,
then it is a set of Bohr recurrence. -/
theorem timeOfRecurrenceForMinEquiImpliesSetOfBohrRecurrence
{S : Type u} [CommSemigroup S] [Nonempty S] (A : Set S) :
(∀ (X : Type) (_ : TopologicalSpace X)
(_ : CompactSpace X) (_ : T2Space X) (_ : Nonempty X)
(dSystem : DynamicalSystem S X) (_ : isEquicontinuousSystem dSystem)
(_ : isMinimalSystem dSystem) (x : X) (U : Set X) (_ : x ∈ U) (_ : IsOpen U),
∃ (s : S) (_ : s ∈ A), dSystem.map s x ∈ U) → isSetOfBohrRecurrence A := by
  intro h B BdcS
  obtain ⟨X, Xtop, Xcmpt, XT2, XNon, dSystem, hEqui, hMin,
    x, U, xInU, UOpen, visitsInB⟩ := bohrZeroSetsContainEquiReturns B BdcS
  obtain ⟨s,sinA,smap⟩ := h X Xtop Xcmpt XT2 XNon dSystem hEqui hMin x U xInU UOpen
  have sinB : s ∈ B := by
    apply visitsInB
    exact smap
  use s
  exact ⟨sinA, sinB⟩

/-- A Delta_0 set is a set of Bohr recurrence -/
theorem deltaZeroImpliesSetOfBohrRecurrence
{S : Type*} [CommSemigroup S] [Nonempty S] :
deltaZeroFamily S ⊆ setOfBohrRecurrenceFamily S :=
by
  classical
  intro A hA B hB
  obtain ⟨d, φ, hφ, U, hUopen, h1U, hUB⟩ := hB
  -- `W = {(x,y) | x⁻¹ y ∈ U}` is an open neighbourhood of the diagonal of the torus
  have hWopen : IsOpen
      ((fun p : (Fin d → Circle) × (Fin d → Circle) ↦ p.1⁻¹ * p.2) ⁻¹' U) :=
    hUopen.preimage (continuous_fst.inv.mul continuous_snd)
  have hWdiag : Set.diagonal (Fin d → Circle) ⊆
      (fun p : (Fin d → Circle) × (Fin d → Circle) ↦ p.1⁻¹ * p.2) ⁻¹' U := by
    rintro ⟨x, x'⟩ hx
    have hx' : x = x' := hx
    subst hx'
    change x⁻¹ * x ∈ U
    rw [inv_mul_cancel]
    exact h1U
  -- total boundedness: finitely many sets of "diameter" `U` cover the torus
  obtain ⟨F, V, hcover, hmemV, hVW⟩ := existsFiniteCoverBySmallSets hWopen hWdiag
  -- `A` is Delta_0, so there are `card F + 1` elements `s i` with `s j ∈ s i * A` for `i < j`
  obtain ⟨s, hs⟩ := hA (F.card + 1)
  choose y hyF hyV using fun i : Fin (F.card + 1) ↦ hcover (φ (s i))
  -- if two of the `φ (s i)` lie in a common piece of the cover, we are done
  have key : ∀ i j : Fin (F.card + 1), i < j → y i = y j → (A ∩ B).Nonempty := by
    intro i j hlt hyij
    obtain ⟨a, haA, hsa⟩ := hs i j hlt
    have hpair : (φ (s i), φ (s j)) ∈ V (y i) ×ˢ V (y i) :=
      Set.mk_mem_prod (hyV i) (hyij ▸ hyV j)
    have hmem : (φ (s i))⁻¹ * φ (s j) ∈ U := hVW (y i) hpair
    rw [← hsa, hφ (s i) a, inv_mul_cancel_left] at hmem
    exact ⟨a, haA, hUB hmem⟩
  -- pigeonhole: `card F + 1` points, `card F` pieces
  obtain ⟨i, j, hij, hyij⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i ↦ (⟨y i, hyF i⟩ : ↥F)) (by simp)
  have hyij' : y i = y j := congrArg Subtype.val hyij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact key i j hlt hyij'
  · exact key j i hgt hyij'.symm


end Bohr_sets
