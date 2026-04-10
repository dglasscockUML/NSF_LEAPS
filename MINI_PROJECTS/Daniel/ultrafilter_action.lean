import Mathlib.Data.Set.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Defs.Ultrafilter
import Mathlib.Topology.Continuous
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Combinatorics.Hindman
import Mathlib.Algebra.Group.Defs

/-
In this file, given a tds S → X → X, we generate a semigroup action βS → X → X.
The difference between a tds and a semigroup action is continuity of X → X gotten by fixing s.
The main result is ultra_action, which given a tds S X, gives
  a construction of a semigroup action of βS on X
-/

structure semigroup_action (S : Type*) [Semigroup S] (X : Type*) where
  semi_toFun : S → X → X
  semi_map_mult' : ∀ s₁ s₂ x, semi_toFun (s₁ * s₂) x = semi_toFun s₁ (semi_toFun s₂ x)

/-- A tds (topological dynamical system) is a compact Hausdorff space `X` together
with an action by a (discrete) semigroup `S`. -/
class tds (S : Type*) [Semigroup S]
(X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X] where
  /-- The map `S → X → X` underlying a flow of `S` on `X`. -/
  toFun : S → X → X
  cont' : ∀ s, Continuous (toFun s)
  map_mult' : ∀ s₁ s₂ x, toFun (s₁ * s₂) x = toFun s₁ (toFun s₂ x)

/-
These "instance"s makes the multiplication and semigroup structure on βS "canonical" by
making it findable by the typeclass inference.
Alternatively, declare at the top of this file something like:
  attribute [local instance] Ultrafilter.mul
  attribute [local instance] Ultrafilter.semigroup
-/

instance ultra_mul {S} [Mul S] : Mul (Ultrafilter S) :=
  Ultrafilter.mul

instance ultra_semigroup {S} [Semigroup S] : Semigroup (Ultrafilter S) :=
  Ultrafilter.semigroup

/-
How is ultrafilter multiplication defined in Mathlib.Combinatorics.Hindman?
mul p q := ((· * ·) <$> p) <*> q
(· * ·) is shorthand for the function S × S → S given by fun s t ↦ s * t
Interpret this function as S → (S → S), in other words s ↦ (t ↦ s * t)
<$> in this case is just pushforward: see Ultrafilter.functor
So, (· * ·) <$> p is an ultrafilter on S → S
Eg: a set of functions F ∈ (· * ·) <$> p if and only if { s ∈ S : λ_s := (t ↦ s * t) ∈ F} \in p
set r = (· * ·) <$> p
Now we see r <*> q, which is described as follows:
In a monad, mf <*> mx is the same as do let f ← mf; x ← mx; pure (f x)
This evaluates the function first, then the argument, and applies one to the other.
Ultrafilter S is a monad (Ultrafilter.monad) and has a monaic bind (Ultrafilter.bind)
I don't fully understand it, but here's how it looks
For r ∈ β (S → S) and q ∈ β S, A ∈ r <*> q iff the following:
{φ : S → S | { t ∈ S | A ∈ pure (φ t)} ∈ q} ∈ r, where pure is the principal ultrafilter
As described above, membership in r is determined by λ_s.  So this happens iff
{s : S | { t ∈ S | A ∈ pure (λ_s t)} ∈ q} ∈ p, that is to say,
{s : S | { t ∈ S | s t ∈ A} ∈ q} ∈ p, which is precisely the usual definition.
This definition is proven in Ultrafilter.eventually_mul by the tactic Iff.rfl
In other words, lean sees this as defintionally equivalent!
-/

-- This is an alternative description of ultrafilter multiplication
theorem ultra_alt_prod_desc {S} [Semigroup S] (p q : Ultrafilter S) (A : Set S) :
    A ∈ p * q ↔ {s : S | {t : S | s * t ∈ A} ∈ q} ∈ p :=
  Iff.rfl

def ultra_right_mult {S} [Semigroup S] (q : Ultrafilter S) :
Ultrafilter S → Ultrafilter S := (· * q)

def ultra_left_mult {S} [Semigroup S] (q : Ultrafilter S) :
Ultrafilter S → Ultrafilter S := (q * ·)

def S_left_mult {S} [Semigroup S] (s : S) :
S → S := (s * ·)

-- The function pure : S → βS is a semigroup homomorphism
theorem pure_is_hom {S} [Semigroup S] (s t : S) :
(pure s : Ultrafilter S) * (pure t : Ultrafilter S) = pure (s * t) := by
  constructor


/-
Here are some useful functions from mathlib that are used many times below
  denseRange_pure says that pure : α -> Ultrafilter α has a dense range
  Ultrafilter.extend takes a function α -> X and gives Ultrafilter α -> X
  ultrafilter_extend_pure proves Ultrafilter.extend f (pure a) = f a
  continuous_ultrafilter_extend proves that the extension is continuous if X is compact
  Continuous.ext_on : If two continuous functions are equal on a dense set,
  then they are equal.
-/

-- Composition by a continuous function commutes with Stone-Cech lift
-- (this theorem may already be in mathlib)
theorem composition_extend {S X} [TopologicalSpace X] [CompactSpace X] [T2Space X]
(f : S → X) {g : X → X} (g_cont : Continuous g) :
Ultrafilter.extend (g ∘ f) = g ∘ Ultrafilter.extend f := by
  let lhs := Ultrafilter.extend (g ∘ f)
  let rhs := g ∘ Ultrafilter.extend f
  have lhs_continuous : Continuous lhs := continuous_ultrafilter_extend (g ∘ f)
  have rhs_continuous : Continuous rhs :=
    Continuous.comp (g_cont) (continuous_ultrafilter_extend f)
  have equal_on_dense : Set.EqOn lhs rhs (Set.range pure) := by
    rewrite [Set.EqOn]
    intro x x_in_range
    rewrite [Set.range] at x_in_range
    change ∃ y, pure y = x at x_in_range
    rcases x_in_range with ⟨t, pure_hypoth⟩
    simp only [← pure_hypoth]
    simp only [lhs, rhs]
    simp only [ultrafilter_extend_pure]
    simp only [Function.comp_apply]
    simp only [ultrafilter_extend_pure]
  exact Continuous.ext_on denseRange_pure lhs_continuous rhs_continuous equal_on_dense

-- Multiplication on the right by a fixed ultrafilter q is continuous map βS → βS
-- (this proof is copied from the mathlib documentation)
theorem ultra_right_mult_continuous {S} [Semigroup S] (q : Ultrafilter S) :
Continuous (ultra_right_mult q) :=
ultrafilterBasis_is_basis.continuous_iff.2 <| Set.forall_mem_range.mpr fun A ↦
    ultrafilter_isOpen_basic { m : S | ∀ᶠ m' in q, m * m' ∈ A }

-- Multiplication on the right by a fixed principal ultrafilter pure s is continuous map βS → βS
theorem ultra_left_mult_by_principal_continuous {S} [Semigroup S] (s : S) :
Continuous (ultra_left_mult (pure s)) := by
  simp only [ultrafilterBasis_is_basis.continuous_iff]
  intro U U_basis
  rw [ultrafilterBasis, Set.range] at U_basis
  rcases U_basis with ⟨A, U_desc⟩
  have heq : (ultra_left_mult (pure s) ⁻¹' U) = {p | Set.preimage (S_left_mult s) A ∈ p} := by
    ext x
    rewrite [Set.preimage]
    rewrite [Set.preimage]
    rewrite [←U_desc]
    change A ∈ ultra_left_mult (pure s) x ↔ {y | S_left_mult s y ∈ A} ∈ x
    simp only [ultra_left_mult]
    simp only [S_left_mult]
    rewrite [ultra_alt_prod_desc (pure s) x A]
    simp only [Ultrafilter.mem_pure]
    exact Iff.rfl
  rewrite [heq]
  exact ultrafilter_isOpen_basic (Set.preimage (S_left_mult s) A)

-- This is a lemma needed in the proof of ultra_technical_equality
theorem ultra_S_left_extension
{S} [Semigroup S] {X} [TopologicalSpace X] [CompactSpace X] [T2Space X]
(f : S → X) (s : S) :
Ultrafilter.extend (f ∘ (S_left_mult s)) =
  (Ultrafilter.extend f) ∘ (ultra_left_mult (pure s)) :=
by
  let lhs := Ultrafilter.extend (f ∘ (S_left_mult s))
  let rhs := (Ultrafilter.extend f) ∘ (ultra_left_mult (pure s))
  have lhs_continuous : Continuous lhs := continuous_ultrafilter_extend (f ∘ (S_left_mult s))
  have rhs_continuous : Continuous rhs :=
    Continuous.comp (continuous_ultrafilter_extend f) (ultra_left_mult_by_principal_continuous s)
  have equal_on_dense : Set.EqOn lhs rhs (Set.range pure) := by
    rewrite [Set.EqOn]
    intro x x_in_range
    rewrite [Set.range] at x_in_range
    change ∃ y, pure y = x at x_in_range
    rcases x_in_range with ⟨t, pure_hypoth⟩
    simp only [← pure_hypoth]
    simp only [lhs, rhs]
    simp only [ultrafilter_extend_pure]
    simp only [Function.comp_apply]
    simp only [ultra_left_mult]
    simp only [pure_is_hom]
    simp only [S_left_mult]
    simp only [ultrafilter_extend_pure]
  exact Continuous.ext_on denseRange_pure lhs_continuous rhs_continuous equal_on_dense

-- This is a technical lemma needed in the proof of ultra_technical_equality_cor
lemma ultra_technical_equality {S} [Semigroup S] {X} [TopologicalSpace X]
[CompactSpace X] [T2Space X] (f : S → X) (q : Ultrafilter S) :
Ultrafilter.extend (fun (s : S) ↦ Ultrafilter.extend (f ∘ (S_left_mult s)) q) =
(Ultrafilter.extend f) ∘ (ultra_right_mult q) := by
  let lhs := Ultrafilter.extend (fun (s : S) ↦ Ultrafilter.extend (f ∘ (S_left_mult s)) q)
  let rhs := (Ultrafilter.extend f) ∘ (ultra_right_mult q)
  have lhs_continuous : Continuous lhs :=
    continuous_ultrafilter_extend (fun (s : S) ↦ Ultrafilter.extend (f ∘ (S_left_mult s)) q)
  have rhs_continuous : Continuous rhs :=
    Continuous.comp (continuous_ultrafilter_extend f) (ultra_right_mult_continuous q)
  have equal_on_dense : Set.EqOn lhs rhs (Set.range pure) := by
    rewrite [Set.EqOn]
    intro x x_in_range
    rewrite [Set.range] at x_in_range
    change ∃ y, pure y = x at x_in_range
    rcases x_in_range with ⟨t, pure_hypoth⟩
    simp only [← pure_hypoth]
    simp only [lhs, rhs]
    simp only [ultrafilter_extend_pure]
    simp only [ultra_S_left_extension]
    simp only [Function.comp_apply]
    simp only [ultra_left_mult]
    simp only [ultra_right_mult]
  exact Continuous.ext_on denseRange_pure lhs_continuous rhs_continuous equal_on_dense

-- This theorem is a technical result needed in the proof of ultra_action
-- It gives an explicit formula for (Ultrafilter.extend f) (p * q) that ultimately
-- comes from the definition of ultrafilter multiplication
theorem ultra_technical_equality_cor
{S} [Semigroup S] {X} [TopologicalSpace X]
[CompactSpace X] [T2Space X] (f : S → X) (p q : Ultrafilter S) :
Ultrafilter.extend (fun (s : S) ↦ Ultrafilter.extend (f ∘ (S_left_mult s)) q) p =
(Ultrafilter.extend f) (p * q) :=
by
  let lhs := Ultrafilter.extend (fun (s : S) ↦ Ultrafilter.extend (f ∘ (S_left_mult s)) q)
  let rhs := (Ultrafilter.extend f) ∘ (ultra_right_mult q)
  have lhs_is_rhs_at_p : lhs p = rhs p := by
    simp only [lhs]
    simp only [rhs]
    rw [ultra_technical_equality f q]
  simp only [lhs] at lhs_is_rhs_at_p
  simp only [rhs] at lhs_is_rhs_at_p
  simp only [Function.comp_apply] at lhs_is_rhs_at_p
  simp only [ultra_right_mult] at lhs_is_rhs_at_p
  exact lhs_is_rhs_at_p

-- Given an action of S on X, S → X → X, we define βS → X → X by: (p,x) ↦ p-lim_s sx
noncomputable
def ultra_action_map {S X} [TopologicalSpace X]
(f : S → X → X) : (Ultrafilter S) → X → X :=
fun (p : Ultrafilter S) (x : X) => Ultrafilter.extend (fun (s : S) => f s x) p

-- This is the main result: given a term of type tds S X, it gives a construction of a
-- term of type semigroup_action (Ultrafilter S) X
noncomputable
def ultra_action {S} [Semigroup S]
{X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [sys : tds S X] :
semigroup_action (Ultrafilter S) X :=
{
  semi_toFun := ultra_action_map sys.toFun
  semi_map_mult' := by
    intro p q x
    simp only [ultra_action_map]
    rewrite [← ultra_technical_equality_cor (fun (s : S) ↦ sys.toFun s x) p q]
    have commutes : ∀ (s : S), (fun t ↦ sys.toFun t x) ∘ (S_left_mult s) =
      (sys.toFun s) ∘ (fun t ↦ sys.toFun t x) := by
        intro s
        ext t
        simp only [Function.comp_apply]
        simp only [S_left_mult]
        simp only [sys.map_mult']
    simp only [commutes]
    have comp_extend_application :
      ∀ (s : S), Ultrafilter.extend (sys.toFun s ∘ fun t ↦ sys.toFun t x) q =
      (sys.toFun s ∘ (Ultrafilter.extend fun t ↦ sys.toFun t x)) q := by
        intro s
        rewrite [composition_extend (fun t ↦ sys.toFun t x) (sys.cont' s)]
        rfl
    simp only [comp_extend_application]
    simp only [Function.comp_apply]
}
