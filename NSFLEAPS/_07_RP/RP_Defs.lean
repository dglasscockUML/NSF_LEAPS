import NSFLEAPS._05_Ultrafilters.UF_Defs

variable {S} [CommSemigroup S] [Nonempty S]
variable {X} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
variable {dSystem : DynamicalSystem S X}

section Projection_and_injection_maps

/- Projection and injection maps -/
def π1 : X × X × X → X := fun w ↦ w.1
def π2 : X × X × X → X := fun w ↦ w.2.1
def π3 : X × X × X → X := fun w ↦ w.2.2
def π12 : X × X × X → X × X := fun w ↦ ⟨w.1,w.2.1⟩
def i21 : (X × X) × X → X × X × X := fun (w : (X × X) × X) ↦ ⟨w.1.1,w.1.2,w.2⟩

end Projection_and_injection_maps

section Corner_System_3

/-- Given an action of `S` on `X`, `leftMap3: X × X × X → X × X × X` is
defined by `s (x,y,z) = (sx, sy, z)` -/
def leftMap3 (s : S) :
X × X × X → X × X × X := by
  intro ⟨x, y, z⟩
  exact ⟨dSystem.map s x, dSystem.map s y, z⟩

/-- `leftMap3` is continuous -/
theorem leftMap3Continuous (s : S) :
Continuous (leftMap3 s (dSystem := dSystem)) :=
  by sorry

/-- Given an action of `S` on `X`, `rightMap3: X × X × X → X × X × X` is
defined by `s (x,y,z) = (x, sy, sz)` -/
def rightMap3 (s : S) :
X × X × X → X × X × X :=  by
  intro ⟨x, y, z⟩
  exact ⟨x, dSystem.map s y, dSystem.map s z⟩


/-- `rightMap3` is continuous -/
theorem rightMap3Continuous (s : S) :
Continuous (rightMap3 s (dSystem := dSystem)) :=
  by sorry

/-- Given an action of `S` on `X`, cornerSystem3 is an action of `S^2`
on `X^3` given by `(s,t)(x,y,z) = (sx,sty,tz)` -/
def cornerSystem3 :
DynamicalSystem (S × S) (X × X × X) :=
{
  map := fun ((s,t) : S × S)
    ↦ (fun (w : X × X × X)
    ↦ leftMap3 (dSystem := dSystem) s (rightMap3 (dSystem := dSystem) t w))

  mapMult := by
    intro s t w
    simp only
    unfold leftMap3
    unfold rightMap3
    simp only
    simp only [←dSystem.mapMult]
    nth_rw 4 [← mul_comm]
    nth_rw 8 [← mul_comm]
    nth_rw 1 [mul_assoc]
    nth_rw 2 [← mul_assoc]

  mapCont := by
    intro s
    simp only
    exact Continuous.comp (leftMap3Continuous s.1) (rightMap3Continuous s.2)
}

end Corner_System_3

section Corner_System_2

/-- Given an action of `S` on `X`, `leftMap2: X × X → X × X` is
defined by `s (x,y) = (sx, sy)` -/
def leftMap2 (s : S) :
X × X → X × X := by
  intro ⟨x, y⟩
  exact ⟨dSystem.map s x, dSystem.map s y⟩

/-- `leftMap2` is continuous -/
theorem leftMap2Continuous (s : S) :
Continuous (leftMap2 s (dSystem := dSystem)) :=
  by sorry

/-- Given an action of `S` on `X`, `rightMap2: X × X → X × X` is
defined by `s (x,y,z) = (x, sy)` -/
def rightMap2 (s : S) :
X × X → X × X :=  by
  intro ⟨x, y⟩
  exact ⟨x, dSystem.map s y⟩

/-- `rightMap2` is continuous -/
theorem rightMap2Continuous (s : S) :
Continuous (rightMap2 s (dSystem := dSystem)) :=
  by sorry

/-- Given an action of `S` on `X`, `cornerSystem2` is an action of `S^2`
on `X^2` given by `(s,t)(x,y,z) = (sx,sty,tz)` -/
def cornerSystem2 :
DynamicalSystem (S × S) (X × X) :=
{
  map := fun ((s,t) : S × S)
    ↦ (fun (w : X × X)
    ↦ leftMap2 (dSystem := dSystem) s (rightMap2 (dSystem := dSystem) t w))
  mapMult := by sorry
  mapCont := by
    intro s
    simp only
    exact Continuous.comp (leftMap2Continuous s.1) (rightMap2Continuous s.2)
}

/-- Projection `π12: X^3 → X^2` is a factor map of `cornerSystem3` to `cornerSystem2` -/
theorem pi12FromCorner3ToCorner2IsFactor :
isFactorMap (dSystemX := cornerSystem3 (dSystem := dSystem))
  (cornerSystem2 (dSystem := dSystem)) π12 :=
by sorry

/-- If `S` acts minimally on `X`, then `cornerSystem2` is minimal -/
theorem minimalSystemImpliesMinimalcornerSystem2 :
isMinimalSystem dSystem → isMinimalSystem (cornerSystem2 (dSystem := dSystem)) :=
by sorry

/-- If `(x,y,z)` is uniformly recurrent under `S^2`, then the cartesian product of
the closure of `S(x,y)` with `{z}` is contained in the closure of `S^2 (x,y,z)` -/
theorem liftTo3Right (x y z : X) :
isUniformlyRecurrent (cornerSystem3 (dSystem := dSystem)) ⟨x, y, z⟩ →
(Equiv.prodAssoc X X X) ''
(orbitClosure (diagDynamicalSystem dSystem dSystem) ⟨x, y⟩) ×ˢ ({z} : Set X) ⊆
orbitClosure (cornerSystem3 (dSystem := dSystem)) ⟨x, y, z⟩ :=
by sorry

/-- If `(x,y,z)` is uniformly recurrent under `S^2`, then the cartesian product of
`{x}` with the closure of `S(y,z)` is contained in the closure of `S^2 (x,y,z)` -/
theorem liftTo3Left (x y z : X) :
isUniformlyRecurrent (cornerSystem3 (dSystem := dSystem)) ⟨x, y, z⟩ →
({x} : Set X) ×ˢ (orbitClosure (diagDynamicalSystem dSystem dSystem) ⟨y, z⟩) ⊆
orbitClosure (cornerSystem3 (dSystem := dSystem)) ⟨x, y, z⟩ :=
by sorry

end Corner_System_2

section Corner_System_1

/-- Given an action of `S` on `X`, `leftMap1: X → X` is defined by `s z = z` -/
def leftMap1 (s : S) : X → X := id

theorem leftMap1Continuous (s : S) :
Continuous (leftMap1 s (X := X)) :=
  by sorry

/-- Given an action of `S` on `X`, `rightMap1: X → X` is defined by `s z = sz` -/
def rightMap1 (s : S) :
X → X := dSystem.map s

theorem rightMap1Continuous (s : S) :
Continuous (rightMap1 s (dSystem := dSystem)) :=
  by sorry

/-- Given an action of `S` on `X`, cornerSystem1 is an action of `S^2`
on `X` given by `(s,t)z = tz` -/
def cornerSystem1 :
DynamicalSystem (S × S) X :=
{
  map := fun ((s,t) : S × S)
    ↦ (fun (w : X)
    ↦ leftMap1 s (rightMap1 (dSystem := dSystem) t w))
  mapMult := by sorry
  mapCont := by
    intro s
    simp only
    exact Continuous.comp (leftMap1Continuous s.1) (rightMap1Continuous s.2)
}

/-- Projection `π3: X^3 → X` is a factor map of `cornerSystem3` to `cornerSystem1` -/
theorem pi3FromCorner3ToCorner1IsFactor :
isFactorMap (dSystemX := cornerSystem3 (dSystem := dSystem))
  (cornerSystem1 (dSystem := dSystem)) π3 :=
by sorry

/-- If `x` and `y` are proximal in `cornerSystem1`, then they are proximal in `dSystem` -/
theorem cornerProxImpliesProx (x y : X) :
proximal (cornerSystem1 (dSystem := dSystem)) x y → proximal dSystem x y :=
by sorry

end Corner_System_1

section Ultrafilters_and_the_corner_space

/-- Given an ultrafilter `p : β(S × S)`, `p (x,y,z) = (p(x,y), pz)` -/
theorem ultraActionOnX3
(p : Ultrafilter (S × S)) (x y z : X) :
(ultraAction (cornerSystem3 (dSystem := dSystem))).map p ⟨x,y,z⟩ =
  i21 ⟨(ultraAction (cornerSystem2 (dSystem := dSystem))).map p ⟨x,y⟩,
    (ultraAction (cornerSystem1 (dSystem := dSystem))).map p x⟩ :=
by sorry

end Ultrafilters_and_the_corner_space


section RP_and_corner_dynamics

/-- If `S` acts minimally on `X`, then for all `x, y ∈ X`, the point
`(x,y,y)` is uniformly recurrent in `cornerSystem3` -/
theorem xyyUniformlyRecurrent (x y : X) :
isMinimalSystem dSystem →
isUniformlyRecurrent (cornerSystem3 (dSystem := dSystem)) ⟨x, y, y⟩ :=
by sorry

/-- If `S` acts minimally on `X`, then for all `x, y ∈ X`, the point
`(x,x,y)` is uniformly recurrent in `cornerSystem3` -/
theorem xxyUniformlyRecurrent (x y : X) :
isMinimalSystem dSystem →
isUniformlyRecurrent (cornerSystem3 (dSystem := dSystem)) ⟨x, x, y⟩ :=
by sorry

/-- If `S` acts minimally on `X`, then for all `x, y ∈ X`, the point
`(x,y) ∈ RP` if and only if `(x,y,y)` is in the `S^2` orbit closure of `(y,y,y)` -/
theorem xyInRPIffxyyInyyyOrbClosure (x y : X) :
isMinimalSystem dSystem →
(x,y) ∈ RP dSystem ↔
(x,y,y) ∈ orbitClosure (cornerSystem3 (dSystem := dSystem)) ⟨y,y,y⟩ :=
by sorry

end RP_and_corner_dynamics


section RP_is_EQ_relation

/-- If `S` acts minimally on `X`, then the regionally proximal relation is transitive -/
theorem minimalImpliesRPisTransitive :
isMinimalSystem dSystem → isTransitive (RP dSystem) :=
by sorry

/-- The regionally proximal relation of a minimal dynamical system
is an ICER -/
theorem RPisICER
(hMin : isMinimalSystem dSystem) :
isICER dSystem (RP dSystem) :=
by sorry

/-- The regionally proximal relation of a minimal dynamical system
is the equicontinuous structure relation -/
theorem RPisEquiStructureRelation
(hMin : isMinimalSystem dSystem) :
RP dSystem = equiStructureRelation dSystem :=
by sorry

end RP_is_EQ_relation

section Set_recurrence_corollary

/-- In a minimal system, for (x,y) ∈ RP and U, V ⊆ X open with y ∈ V,
the intersection R(x,U) ∩ R(V,U) is syndetic -/
theorem xyInRPImpliesSyndeticVisitTimeIntersection (x y : X) :
isMinimalSystem dSystem → (x,y) ∈ RP dSystem →
∀ (U V : Set X), IsOpen U → IsOpen V → U.Nonempty → y ∈ V →
isSyndetic ((visitTimeSet dSystem x U) ∩ (setVisitTimeSet dSystem V U)) :=
by sorry

end Set_recurrence_corollary
