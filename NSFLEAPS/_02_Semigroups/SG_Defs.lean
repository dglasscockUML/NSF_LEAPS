import NSFLEAPS._00_Imports.IM_Base

structure SemigroupLeftIdeal (S) [Semigroup S] where
  carrier : Set S
  nonempty' : carrier.Nonempty
  mul_closed' (s : S) {x : S} : x ∈ carrier → s * x ∈ carrier

--theorem intersectionOfLeftIdealsIsLeftIdeal {S : Type u} [Semigroup S]
--{s : Set (Set S)} (h : ∀ (t : Set X), t ∈ s → IsOpen t) :
--IsOpen (⋃₀ s)
