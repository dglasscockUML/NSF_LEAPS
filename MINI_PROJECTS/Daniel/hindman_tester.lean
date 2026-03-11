import Mathlib.Data.Stream.Init
import Mathlib.Topology.Algebra.Semigroup
import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Filter

/-- Multiplication of ultrafilters given by `∀ᶠ m in U*V, p m ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m*m')`. -/
def Ultrafilter.mul {M} [Mul M] : Mul (Ultrafilter M) where mul U V := (· * ·) <$> U <*> V

attribute [local instance] Ultrafilter.mul

/- We could have taken this as the definition of `U * V`, but then we would have to prove that it
defines an ultrafilter. -/
theorem Ultrafilter.eventually_mul {M} [Mul M] (U V : Ultrafilter M) (p : M → Prop) :
    (∀ᶠ m in ↑(U * V), p m) ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m * m') :=
  Iff.rfl

/-- Semigroup structure on `Ultrafilter M` induced by a semigroup structure on `M`. -/
def Ultrafilter.semigroup {M} [Semigroup M] : Semigroup (Ultrafilter M) :=
  { Ultrafilter.mul with
    mul_assoc := fun U V W =>
      Ultrafilter.coe_inj.mp <|
        Filter.ext' fun p => by simp [Ultrafilter.eventually_mul, mul_assoc] }

attribute [local instance] Ultrafilter.semigroup

-- We don't prove `continuous_mul_right`, because in general it is false!
theorem Ultrafilter.continuous_mul_left {M} [Mul M] (V : Ultrafilter M) :
    Continuous (· * V) :=
  ultrafilterBasis_is_basis.continuous_iff.2 <| Set.forall_mem_range.mpr fun s ↦
    ultrafilter_isOpen_basic { m : M | ∀ᶠ m' in V, m * m' ∈ s }
