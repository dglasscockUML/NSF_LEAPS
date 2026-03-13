import NSFLEAPS._03_Family_algebra.FA_Defs

variable (fam : Family S)
#check fam
#check fam*
variable (α : Type _) (J K L : Set (Set α))
#check J
#check J*
#check J** = J
#check J
#check K

theorem thm_equiv_dual_formulation {α} (F : Family α) :
(F*).sets = {A : Set α | ¬ (Aᶜ ∈ F.sets)} :=
sorry --complement of A in S not in F}
