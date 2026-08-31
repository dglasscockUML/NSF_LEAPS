import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Algebra.Monoid.Defs

/- ChatGPT 5.6 Sol helped write the following -/

namespace ContinuousMap

structure End (X : Type*) [TopologicalSpace X] where
  toContinuousMap : C(X, X)

namespace End

variable {X : Type*} [TopologicalSpace X]

instance : CoeFun (End X) (fun _ => X → X) where
  coe f := f.toContinuousMap

@[ext]
theorem End.ext {f g : End X} (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk f =>
    cases g with
    | mk g =>
      congr
      ext x
      exact h x

instance : Monoid (End X) where
  one := ⟨ContinuousMap.id X⟩
  mul f g := ⟨f.toContinuousMap.comp g.toContinuousMap⟩
  one_mul f := by
    ext x
    rfl
  mul_one f := by
    ext x
    rfl
  mul_assoc f g h := by
    ext x
    rfl

@[simp]
theorem one_apply (x : X) :
    (1 : End X) x = x :=
  rfl

@[simp]
theorem mul_apply (f g : End X) (x : X) :
    (f * g) x = f (g x) :=
  rfl

instance : TopologicalSpace (End X) :=
  TopologicalSpace.induced
    (fun f : End X => f.toContinuousMap)
    inferInstance

theorem continuous_toContinuousMap :
    Continuous (fun f : End X => f.toContinuousMap) :=
  continuous_induced_dom

instance [T2Space X] : T2Space (End X) := by
  apply T2Space.of_injective_continuous
      (f := fun f : End X => f.toContinuousMap)
  · intro f g h
    cases f
    cases g
    cases h
    rfl
  · exact continuous_toContinuousMap

instance [LocallyCompactSpace X] : ContinuousMul (End X) where
  continuous_mul := by
    rw [continuous_induced_rng]
    simpa only [Function.comp_apply] using
      (continuous_toContinuousMap.comp continuous_fst).compCM
        (continuous_toContinuousMap.comp continuous_snd)

def homeomorphContinuousMap : End X ≃ₜ C(X, X) where
  toEquiv :=
  { toFun := fun f => f.toContinuousMap
    invFun := fun f => ⟨f⟩
    left_inv := by
      intro f
      cases f
      rfl
    right_inv := by
      intro f
      rfl }
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    rw [continuous_induced_rng]
    exact continuous_id

end End

end ContinuousMap
