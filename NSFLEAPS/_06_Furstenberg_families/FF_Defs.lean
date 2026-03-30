import NSFLEAPS._03_Family_algebra.FA_Defs
-- Family_algebra has two files.  We may need to import the later one.
import NSFLEAPS._04_Dynamical_systems.DS_Defs


/-- A set `A ⊆ S` is thick if for all finite subsets `F ⊆ S`,
there exists `s ∈ S` such that `Fs ⊆ A` -/
def isThick
{S : Type*} [Semigroup S] (A : Set S) :
Prop :=
∀ F : Set S, F.Finite → ∃ s : S, (· * s) '' F ⊆ A

def syndeticFamily
(S : Type*) [Semigroup S] : Set (Set S) :=
{A : Set S | isSyndetic A}

def thickFamily
(S : Type*) [Semigroup S] : Set (Set S) :=
{A : Set S | isThick A}

theorem dualSyndeticThick
{S : Type*} [Semigroup S] :
(syndeticFamily S)* = (thickFamily S) :=
by
  ext A
  constructor
  · sorry
  · intro AisThick
    intro B BisSyndetic
    unfold thickFamily isThick at AisThick
    unfold syndeticFamily isSyndetic at BisSyndetic
    rcases BisSyndetic with ⟨F, Ffinite, BisSyndetic⟩
    specialize AisThick F Ffinite
    rcases AisThick with ⟨s, sMapsFintoA⟩
    specialize BisSyndetic s
    rcases BisSyndetic with ⟨f,fInF,fTimessinB⟩
    have fstarsInImage : f * s ∈ (fun x ↦ x * s) '' F := by sorry -- Finish
    exact Set.nonempty_of_mem ⟨sMapsFintoA fstarsInImage, fTimessinB⟩
