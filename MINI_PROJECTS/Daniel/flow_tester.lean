import Mathlib.Data.Set.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Closure
import Mathlib.Algebra.Group.Defs

/-- A tds (topological dynamical system) is a compact Hausdorff space `X` together
with an action by a (discrete) monoid `S`. -/
class tds (S : Type*) [Monoid S]
(X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X] where
  /-- The map `S → X → X` underlying a flow of `S` on `X`. -/
  toFun : S → X → X
  cont' : ∀ s, Continuous (toFun s)
  map_mult' : ∀ s₁ s₂ x, toFun (s₁ * s₂) x = toFun s₁ (toFun s₂ x)
  map_one' : ∀ x, toFun 1 x = x

/-- The visit times under f : S → X → X of a point x to a set U is the subset
of elements of S that send x into U -/
def visit_time {S X : Type*} (f : S → X → X) (x : X) (U : Set X) : Set S :=
  { s : S | f s x ∈ U }
  -- This could also be written: Set.preimage (fun s => f s x) U

/-- The orbit of x under f : S → X → X is the image of x under S -/
def orbit {S X : Type*} (f : S → X → X) (x : X) : Set X :=
  Set.range (fun s : S => f s x)

/-- A map f : S → X → X is minimal if every point has a dense orbit -/
def is_minimal {S X : Type*} [TopologicalSpace X] (f : S → X → X) : Prop :=
∀ x : X, Dense (orbit f x)

/-- A minimal tds (topological dynamical system) is a compact Hausdorff space `X`
together with an action by a (discrete) monoid `S` in which every point
has a dense orbit -/
class minimal_tds (S : Type*) [Monoid S]
(X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X] extends tds S X where
  minimal' : is_minimal toFun

-- Definition of syndetic from Hindman-Strauss, Def. 4.38
/-- A subset A of a semigroup S is syndetic if there is a finite subset F of S such that
every element of S can be multiplied on the left by F to land in A -/
def syndetic {S : Type*} [Semigroup S] (A : Set S) : Prop :=
  ∃ F : Set S, F.Finite ∧ (∀ s : S, ∃ f ∈ F, f * s ∈ A)
-- Why I used finite sets instead of finsets:
-- Building a finset requires a proof of dupliates, which is annoying
-- We don't care about possible duplicates, so finite sets are enough

/-- A map f : S → X → X has syndetic visits if for all x and all non-empty, open U,
the set of visit times of x to U is syndetic -/
def syndetic_visits {S X : Type*} [τ : TopologicalSpace X] [Semigroup S] (f : S → X → X) : Prop :=
∀ x U, U.Nonempty → τ.IsOpen U → syndetic (visit_time f x U)

-- Note that if S is an empty type, then every element of Set S is (vacuously) syndetic
-- and hence syndetic_visits also holds vacuously.  That's why, in this theorem
-- we assume that S is a monoid: it has a "1".  We could just assume non-empty.
theorem syndetic_visits_implies_minimal {S : Type*} [mon : Monoid S] {X : Type*}
[τ : TopologicalSpace X] {f : S → X → X} : syndetic_visits f → is_minimal f := by
  intro syd_visits
  unfold is_minimal Dense orbit
  simp only [mem_closure_iff]
  intro x y U U_open y_in_U
  have U_nonempty : U.Nonempty := by use y
  unfold syndetic_visits at syd_visits
  have synd_x_U : syndetic (visit_time f x U) := syd_visits x U U_nonempty U_open
  unfold syndetic visit_time at synd_x_U
  rcases synd_x_U with ⟨F,synd_x_U_two⟩
  have synd_x_U_three : ∃ f2 ∈ F, f2 * 1 ∈ {s | f s x ∈ U} := synd_x_U_two.2 1
  simp only [mon.mul_one] at synd_x_U_three
  rcases synd_x_U_three with ⟨f2,synd_x_U_four⟩
  have f2_x_in_U : f f2 x ∈ U := synd_x_U_four.2
  have f2_image_in_U : f f2 x ∈ Set.range fun s : S ↦ f s x := by use f2
  use f f2 x
  exact ⟨f2_x_in_U, f2_image_in_U⟩

-- minimality implies syndetic visits.  In this version, we dont assume the structure
-- of a tds.  Instead, we just have the assumptions we need
theorem minimal_implies_syndetic_visits {S : Type*} [mon : Monoid S] {X : Type*}
[τ : TopologicalSpace X] [cs : CompactSpace X] {f : S → X → X}
{f_s_cont : ∀ s, Continuous (f s)} {f_mult : ∀ s₁ s₂ x, f (s₁ * s₂) x = f s₁ (f s₂ x)} :
is_minimal f → syndetic_visits f := by
  intro dense_orbits
  unfold is_minimal Dense orbit at dense_orbits
  simp only [mem_closure_iff] at dense_orbits
  unfold syndetic_visits
  intro x U U_nonempty U_open
  rcases U_nonempty with ⟨u, elt_of_U⟩
  have all_y_map_into_U : ∀ y : X, ∃ s : S, f s y ∈ U := by
    intro y
    have all_y_map_into_U_half : (U ∩ Set.range fun s ↦ f s y).Nonempty :=
    dense_orbits y u U U_open elt_of_U
    rcases all_y_map_into_U_half with ⟨u_two, u_two_in_image⟩
    rcases u_two_in_image.2 with ⟨s_witness, s_witness_info⟩
    simp at s_witness_info
    use s_witness
    simp only [s_witness_info]
    exact u_two_in_image.1
  let s_chooser : X → S := fun x : X => Classical.choose (all_y_map_into_U x)
  have s_chooser_property : ∀ x : X, f (s_chooser x) x ∈ U := by
    intro x
    exact Classical.choose_spec (all_y_map_into_U x)
  let V_chooser : X → Set X := fun x : X => Set.preimage (f (s_chooser x)) U
  have V_choice_has_x : ∀ x : X, x ∈ V_chooser x := by
    intro x
    unfold V_chooser
    exact s_chooser_property x
  have V_choice_open : ∀ x : X, τ.IsOpen (V_chooser x) := by
    intro x
    have cts_s_chooser : Continuous (f (s_chooser x)) := f_s_cont (s_chooser x)
    unfold V_chooser
    exact Continuous.isOpen_preimage cts_s_chooser U U_open
  have V_choice_covers : Set.univ ⊆ Set.iUnion V_chooser := by
    intro x x_in_X
    unfold V_chooser
    simp only [Set.mem_iUnion, Set.mem_preimage]
    use x
    exact s_chooser_property x
  have finite_cover : ∃ (Y : Finset X), Set.univ ⊆ ⋃ y ∈ Y, V_chooser y :=
    IsCompact.elim_finite_subcover cs.isCompact_univ V_chooser V_choice_open V_choice_covers
  rcases finite_cover with ⟨Y, cover_prop⟩
  have Yset_finite : (Y : Set X).Finite := Y.finite_toSet
  unfold syndetic
  use Set.image s_chooser (Y : Set X)
  have image_F_finite : (Set.image s_chooser (Y : Set X)).Finite :=
    Set.Finite.image s_chooser Yset_finite
  refine ⟨image_F_finite,?_⟩
  intro s
  have tofun_s_x_in_univ : f s x ∈ Set.univ := by simp
  have tofun_s_x_cover : f s x ∈ ⋃ y ∈ Y, V_chooser y := cover_prop tofun_s_x_in_univ
  rcases Set.mem_iUnion₂.mp tofun_s_x_cover with ⟨y, hyY, hxFy⟩
  have tofun_s_choose_tofun : f (s_chooser y) (f s x) ∈ U := by
    unfold V_chooser at hxFy
    exact hxFy
  have use_semigp_prop : f ((s_chooser y) * s) x ∈ U := by
    simp only [f_mult]
    exact tofun_s_choose_tofun
  have s_chooser_y_works : s_chooser y * s ∈ visit_time f x U := by
    unfold visit_time
    exact use_semigp_prop
  have s_chooser_y_clear: s_chooser y ∈ s_chooser '' (Y : Set X) := by
    simp only [Set.mem_image, SetLike.mem_coe]
    use y
  use s_chooser y

-- minimality iff syndetic visits using the tds class
theorem minimal_iff_syndetic_visits {S : Type*} [mon : Monoid S]
{X : Type*} [τ : TopologicalSpace X] [cs : CompactSpace X] [T2Space X] (sys : tds S X) :
syndetic_visits sys.toFun ↔ is_minimal (sys.toFun):= by
  constructor
  · unfold is_minimal Dense orbit
    simp only [mem_closure_iff]
    intro synd_rtns x y U U_open y_in_U
    have U_nonempty : U.Nonempty := by use y
    unfold syndetic_visits at synd_rtns
    have synd_x_U : syndetic (visit_time tds.toFun x U) := synd_rtns x U U_nonempty U_open
    unfold syndetic visit_time at synd_x_U
    rcases synd_x_U with ⟨F,synd_x_U_two⟩
    have synd_x_U_three : ∃ f ∈ F, f * 1 ∈ {s | tds.toFun s x ∈ U} := synd_x_U_two.2 1
    simp only [mon.mul_one] at synd_x_U_three
    rcases synd_x_U_three with ⟨f,synd_x_U_four⟩
    have f_x_in_U : tds.toFun f x ∈ U := synd_x_U_four.2
    have f_image_in_U : tds.toFun f x ∈ Set.range fun s : S ↦ tds.toFun s x := by use f
    use tds.toFun f x
    exact ⟨f_x_in_U, f_image_in_U⟩
  · intro dense_orbits
    unfold is_minimal Dense orbit at dense_orbits
    simp only [mem_closure_iff] at dense_orbits
    unfold syndetic_visits
    intro x U U_nonempty U_open
    rcases U_nonempty with ⟨u, elt_of_U⟩
    have all_y_map_into_U : ∀ y : X, ∃ s : S, sys.toFun s y ∈ U := by
      intro y
      have all_y_map_into_U_half : (U ∩ Set.range fun s ↦ tds.toFun s y).Nonempty :=
      dense_orbits y u U U_open elt_of_U
      rcases all_y_map_into_U_half with ⟨u_two, u_two_in_image⟩
      rcases u_two_in_image.2 with ⟨s_witness, s_witness_info⟩
      simp at s_witness_info
      use s_witness
      simp only [s_witness_info]
      exact u_two_in_image.1
    let s_chooser : X → S := fun x : X => Classical.choose (all_y_map_into_U x)
    have s_chooser_property : ∀ x : X, sys.toFun (s_chooser x) x ∈ U := by
      intro x
      exact Classical.choose_spec (all_y_map_into_U x)
    let V_chooser : X → Set X := fun x : X => Set.preimage (sys.toFun (s_chooser x)) U
    have V_choice_has_x : ∀ x : X, x ∈ V_chooser x := by
      intro x
      unfold V_chooser
      exact s_chooser_property x
    have V_choice_open : ∀ x : X, τ.IsOpen (V_chooser x) := by
      intro x
      have cts_s_chooser : Continuous (sys.toFun (s_chooser x)) := sys.cont' (s_chooser x)
      unfold V_chooser
      exact Continuous.isOpen_preimage cts_s_chooser U U_open
    have V_choice_covers : Set.univ ⊆ Set.iUnion V_chooser := by
      intro x x_in_X
      unfold V_chooser
      simp only [Set.mem_iUnion, Set.mem_preimage]
      use x
      exact s_chooser_property x
    have finite_cover : ∃ (Y : Finset X), Set.univ ⊆ ⋃ y ∈ Y, V_chooser y :=
      IsCompact.elim_finite_subcover cs.isCompact_univ V_chooser V_choice_open V_choice_covers
    rcases finite_cover with ⟨Y, cover_prop⟩
    have Yset_finite : (Y : Set X).Finite := Y.finite_toSet
    unfold syndetic
    use Set.image s_chooser (Y : Set X)
    have image_F_finite : (Set.image s_chooser (Y : Set X)).Finite :=
      Set.Finite.image s_chooser Yset_finite
    refine ⟨image_F_finite,?_⟩
    intro s
    have tofun_s_x_in_univ : sys.toFun s x ∈ Set.univ := by simp
    have tofun_s_x_cover : sys.toFun s x ∈ ⋃ y ∈ Y, V_chooser y := cover_prop tofun_s_x_in_univ
    rcases Set.mem_iUnion₂.mp tofun_s_x_cover with ⟨y, hyY, hxFy⟩
    have tofun_s_choose_tofun : sys.toFun (s_chooser y) (sys.toFun s x) ∈ U := by
      unfold V_chooser at hxFy
      exact hxFy
    have use_semigp_prop : sys.toFun ((s_chooser y) * s) x ∈ U := by
      simp only [sys.map_mult']
      exact tofun_s_choose_tofun
    have s_chooser_y_works : s_chooser y * s ∈ visit_time tds.toFun x U := by
      unfold visit_time
      exact use_semigp_prop
    have s_chooser_y_clear: s_chooser y ∈ s_chooser '' (Y : Set X) := by
      simp only [Set.mem_image, SetLike.mem_coe]
      use y
    use s_chooser y


--theorem factor_of_minimal_is_minimal {τ : Type u_1} [AddMonoid τ]
-- [TopologicalSpace τ] [ContinuousAdd τ]
--  {α : Type u_2} [TopologicalSpace α]
--  {β : Type u_3} [TopologicalSpace β]
--  {π : α → β} {ϕ : Flow τ α} {ψ : Flow τ β} {h : Flow.IsSemiconjugacy π ϕ ψ}:
--  ∀ x : α, ∀ y : β, AddAction.dense_orbit τ x → Dense (AddAction.orbit τ y) := by
