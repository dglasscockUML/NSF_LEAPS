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
  by
    unfold leftMap3
    simp only [continuous_prodMk]
    refine ⟨?_,?_,?_⟩
    · exact Continuous.comp (dSystem.mapCont s) continuous_fst
    · exact (Continuous.comp (dSystem.mapCont s) (Continuous.comp continuous_fst continuous_snd))
    · exact (Continuous.comp continuous_snd continuous_snd)

/-- Given an action of `S` on `X`, `rightMap3: X × X × X → X × X × X` is
defined by `s (x,y,z) = (x, sy, sz)` -/
def rightMap3 (s : S) :
X × X × X → X × X × X :=  by
  intro ⟨x, y, z⟩
  exact ⟨x, dSystem.map s y, dSystem.map s z⟩


/-- `rightMap3` is continuous -/
theorem rightMap3Continuous (s : S) :
Continuous (rightMap3 s (dSystem := dSystem)) :=
  by
    unfold rightMap3
    simp only [continuous_prodMk]
    refine ⟨?_,?_,?_⟩
    · exact continuous_fst
    · exact (Continuous.comp (dSystem.mapCont s) (Continuous.comp continuous_fst continuous_snd))
    · exact (Continuous.comp (dSystem.mapCont s) (Continuous.comp continuous_snd continuous_snd))

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
  by
    unfold leftMap2
    simp only [continuous_prodMk]
    refine ⟨?_,?_⟩
    · exact Continuous.comp (dSystem.mapCont s) continuous_fst
    · exact Continuous.comp (dSystem.mapCont s) continuous_snd

/-- Given an action of `S` on `X`, `rightMap2: X × X → X × X` is
defined by `s (x,y,z) = (x, sy)` -/
def rightMap2 (s : S) :
X × X → X × X :=  by
  intro ⟨x, y⟩
  exact ⟨x, dSystem.map s y⟩

/-- `rightMap2` is continuous -/
theorem rightMap2Continuous (s : S) :
Continuous (rightMap2 s (dSystem := dSystem)) :=
  by
    unfold rightMap2
    simp only [continuous_prodMk]
    refine ⟨?_,?_⟩
    · exact continuous_fst
    · exact Continuous.comp (dSystem.mapCont s) continuous_snd

/-- Given an action of `S` on `X`, `cornerSystem2` is an action of `S^2`
on `X^2` given by `(s,t)(x,y,z) = (sx,sty,tz)` -/
def cornerSystem2 :
DynamicalSystem (S × S) (X × X) :=
{
  map := fun ((s,t) : S × S)
    ↦ (fun (w : X × X)
    ↦ leftMap2 (dSystem := dSystem) s (rightMap2 (dSystem := dSystem) t w))
  mapMult := by
    intro s t x
    simp only
    unfold leftMap2
    unfold rightMap2
    simp only
    simp only [←dSystem.mapMult]
    nth_rw 1 [mul_assoc]
    nth_rw 2 [← mul_assoc]
    nth_rw 4 [← mul_comm]
    nth_rw 1 [mul_assoc]
  mapCont := by
    intro s
    simp only
    exact Continuous.comp (leftMap2Continuous s.1) (rightMap2Continuous s.2)
}

/-- Projection `π12: X^3 → X^2` is a factor map of `cornerSystem3` to `cornerSystem2` -/
theorem pi12FromCorner3ToCorner2IsFactor :
isFactorMap (dSystemX := cornerSystem3 (dSystem := dSystem))
  (cornerSystem2 (dSystem := dSystem)) π12 :=
by
  unfold isFactorMap
  unfold π12
  refine ⟨?_,?_,?_⟩
  · simp only [continuous_prodMk]
    refine ⟨?_,?_,⟩
    · exact continuous_fst
    · exact Continuous.comp continuous_fst continuous_snd
  · unfold Function.Surjective
    intro ⟨w,z⟩
    use ⟨w,z,z⟩
  · unfold isEquivariant
    intro ⟨s,t⟩
    unfold cornerSystem2
    unfold cornerSystem3
    unfold leftMap2
    unfold rightMap2
    unfold leftMap3
    unfold rightMap3
    simp only
    exact Eq.symm (Function.Semiconj.comp_eq (congrFun rfl))

/-- If `S` acts minimally on `X`, then `cornerSystem2` is minimal -/
theorem minimalSystemImpliesMinimalcornerSystem2
(hMin : isMinimalSystem dSystem) :
isMinimalSystem (cornerSystem2 (dSystem := dSystem)) :=
by
  have allPtsHaveDenseOrbit :
    ∀ (x : X × X), Dense (orbit (cornerSystem2 (dSystem := dSystem)) x) :=
      by
        intro x
        simp only [dense_iff_inter_open]
        intro U UisOpen UisNonempty
        rcases UisNonempty with ⟨⟨u1, u2⟩, hxy⟩
        rcases (isOpen_prod_iff.mp UisOpen) u1 u2 hxy with ⟨V, W, hVopen, hWopen, hxV, hyW, hVW⟩
        rcases (minimalImpliesNonemptySetVisits hMin x.1 hVopen) with ⟨s, hs⟩
        rcases (minimalImpliesNonemptySetVisits hMin (dSystem.map s x.2) hWopen) with ⟨t, ht⟩
        have stxInVtimesW : (cornerSystem2 (dSystem := dSystem)).map ⟨s,t⟩ x ∈ V ×ˢ W :=
          by
            unfold cornerSystem2
            simp only
            unfold leftMap2
            unfold rightMap2
            simp only
            constructor
            · simp only
              exact hs
            · simp only
              simp only [← dSystem.mapMult]
              nth_rw 1 [← mul_comm]
              simp only [dSystem.mapMult]
              exact ht
        use (cornerSystem2 (dSystem := dSystem)).map ⟨s,t⟩ x
        constructor
        · exact hVW stxInVtimesW
        · use ⟨s,t⟩
  exact (minimalIffDenseOrbits cornerSystem2).mpr allPtsHaveDenseOrbit

/-- If `(x,y,z)` is uniformly recurrent under `S^2`, then the cartesian product of
the closure of `S(x,y)` with `{z}` is contained in the closure of `S^2 (x,y,z)` -/
theorem liftTo3Right
(x y z : X) :
isUniformlyRecurrent (cornerSystem3 (dSystem := dSystem)) ⟨x,y,z⟩ →
(Equiv.prodAssoc X X X) ''
(orbitClosure (diagDynamicalSystem dSystem dSystem) ⟨x,y⟩) ×ˢ ({z} : Set X) ⊆
orbitClosure (cornerSystem3 (dSystem := dSystem)) ⟨x,y,z⟩ :=
by sorry

/-- If `(x,y,z)` is uniformly recurrent under `S^2`, then the cartesian product of
`{x}` with the closure of `S(y,z)` is contained in the closure of `S^2 (x,y,z)` -/
theorem liftTo3Left
(x : X) {y z : X}
(hUR : isUniformlyRecurrent (cornerSystem3 (dSystem := dSystem)) ⟨x, y, z⟩) :
({x} : Set X) ×ˢ (orbitClosure (diagDynamicalSystem dSystem dSystem) ⟨y,z⟩) ⊆
orbitClosure (cornerSystem3 (dSystem := dSystem)) ⟨x,y,z⟩ :=
by sorry

end Corner_System_2

section Corner_System_1

/-- Given an action of `S` on `X`, `leftMap1: X → X` is defined by `s z = z` -/
def leftMap1 (s : S) : X → X := id

/-- `leftMap1 : X → X` is continuous -/
theorem leftMap1Continuous
(s : S) :
Continuous (leftMap1 s (X := X)) :=
  by
    unfold leftMap1
    exact continuous_id

/-- Given an action of `S` on `X`, `rightMap1: X → X` is defined by `s z = sz` -/
def rightMap1 (s : S) :
X → X := dSystem.map s

/-- `rightMap1 : X → X` is continuous -/
theorem rightMap1Continuous
(s : S) :
Continuous (rightMap1 s (dSystem := dSystem)) :=
  by
    unfold rightMap1
    exact dSystem.mapCont s

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
theorem xyyUniformlyRecurrent
(hMin : isMinimalSystem dSystem) (x y : X) :
isUniformlyRecurrent (cornerSystem3 (dSystem := dSystem)) ⟨x,y,y⟩ :=
by
  have corner2IsMin := minimalSystemImpliesMinimalcornerSystem2 hMin
  let xxx : X × X × X := ⟨x,x,x⟩
  let xyy : X × X × X := ⟨x,y,y⟩
  let xx: X × X := ⟨x,x⟩
  rcases (rightTopSemigroupContainsMinLeftIdeal (S := Ultrafilter (S × S))) with ⟨L,LMin⟩
  rcases (everyPointInMinFixedBySomeIdempotentUltrafilter cornerSystem2 corner2IsMin LMin xx)
    with ⟨p,pInL,pIdemp,pFixesxx⟩
  let px := (ultraAction (cornerSystem1 (dSystem := dSystem))).map p x
  let xpx : X × X := ⟨x,px⟩
  let xxpx : X × X × X := ⟨x,x,px⟩
  have pIsMin : isMinimalUltrafilter p := by use L
  have imageOfpxxx := ultraActionOnX3 (dSystem := dSystem) p x x x
  have xxxpxxxAreProx := pointAndUltraImageAreProximal (cornerSystem3 (dSystem := dSystem)) xxx p
  have imagesAreProxpre := imageOfProxByFactorIsProx pi3FromCorner3ToCorner1IsFactor xxxpxxxAreProx
  have imagesAreProx : proximal dSystem x px :=
    by
      unfold xxx at imagesAreProxpre
      simp only [imageOfpxxx] at imagesAreProxpre
      unfold π3 at imagesAreProxpre
      unfold i21 at imagesAreProxpre
      simp only at imagesAreProxpre
      exact (cornerProxImpliesProx x px) imagesAreProxpre
  have xxInOrbClospx :=
    (minSystemOrbitClosProxPairContainsDiag hMin imagesAreProx) (Set.mem_diagonal x)
  have xxpxIsURpre :=
    minUltraImageIsUniformlyRecurrent (cornerSystem3 (dSystem := dSystem)) xxx pIsMin
  have xxpxIsUR : isUniformlyRecurrent (cornerSystem3 (dSystem := dSystem)) xxpx :=
    by
      unfold xxx at xxpxIsURpre
      simp only [imageOfpxxx] at xxpxIsURpre
      unfold xx at pFixesxx
      simp only [pFixesxx] at xxpxIsURpre
      unfold i21 at xxpxIsURpre
      simp only at xxpxIsURpre
      exact xxpxIsURpre
  have xxxInOrbClosxxpx :
    xxx ∈ orbitClosure (cornerSystem3 (dSystem := dSystem)) xxpx :=
      by
        have xTimesOrbClosxpxInOrbClosxxx := liftTo3Left x xxpxIsUR
        have xxxInxTimesOrbClosxpx :
          xxx ∈ {x} ×ˢ orbitClosure (diagDynamicalSystem dSystem dSystem) (x, px) :=
            by
              constructor
              · unfold xxx
                simp only [Set.mem_singleton_iff]
              · exact xxInOrbClospx
        exact xTimesOrbClosxpxInOrbClosxxx xxxInxTimesOrbClosxpx
  have xxxIsUR :=
    inOrbitClosOfURPointImpliesUR (cornerSystem3 (dSystem := dSystem)) xxpxIsUR xxxInOrbClosxxpx
  have yyInOrbitClosxx :
    (y,y) ∈ orbitClosure (diagDynamicalSystem dSystem dSystem) xx :=
      diagonalOrbitVisits x y
        ((subset_of_eq (minimalImpliesFullOrbitClosure hMin x).symm) (Set.mem_univ x))
  have xOrbClosxxInOrbClosxxx:= liftTo3Left x xxxIsUR
  have xyyInxOrbClosxx :
    xyy ∈ {x} ×ˢ orbitClosure (diagDynamicalSystem dSystem dSystem) xx :=
      by
        constructor
        · unfold xyy
          simp only [Set.mem_singleton_iff]
        · exact yyInOrbitClosxx
  have xyyInOrbClosxxx := xOrbClosxxInOrbClosxxx xyyInxOrbClosxx
  exact inOrbitClosOfURPointImpliesUR (cornerSystem3 (dSystem := dSystem)) xxxIsUR xyyInOrbClosxxx

/-- If `S` acts minimally on `X`, then for all `x, y ∈ X`, the point
`(x,x,y)` is uniformly recurrent in `cornerSystem3` -/
theorem xxyUniformlyRecurrent
(hMin : isMinimalSystem dSystem) (x y : X) :
isUniformlyRecurrent (cornerSystem3 (dSystem := dSystem)) ⟨x,x,y⟩ :=
by sorry

/-- If `S` acts minimally on `X`, then for all `x, y ∈ X`, the point
`(x,y) ∈ RP` if and only if `(x,y,y)` is in the `S^2` orbit closure of `(y,y,y)` -/
theorem xyInRPIffxyyInyyyOrbClosure
(hMin : isMinimalSystem dSystem) (x y : X) :
(x,y) ∈ RP dSystem ↔
(x,y,y) ∈ orbitClosure (cornerSystem3 (dSystem := dSystem)) ⟨y,y,y⟩ :=
by sorry

end RP_and_corner_dynamics


section RP_is_EQ_relation

/-- If `S` acts minimally on `X`, then the regionally proximal relation is transitive -/
theorem minimalImpliesRPisTransitive
(hMin : isMinimalSystem dSystem) :
isTransitive (RP dSystem) :=
by
  unfold isTransitive
  unfold setToRelation
  exact {
    trans := by
      intro x y z xyInRP yzInRP
      have yzzInOrbitCloszzz :
        (y,z,z) ∈ orbitClosure cornerSystem3 (z,z,z) :=
          (xyInRPIffxyyInyyyOrbClosure hMin y z).mp yzInRP
      have yyInOrbitCloszz :
        (y,y) ∈ orbitClosure (diagDynamicalSystem dSystem dSystem) (z,z) :=
          diagonalOrbitVisits z y
            ((subset_of_eq (minimalImpliesFullOrbitClosure hMin z).symm) (Set.mem_univ z))
      have yyyInyTimesOrbitCloszz :
        (y,y,y) ∈ ({y} : Set X) ×ˢ (orbitClosure (diagDynamicalSystem dSystem dSystem) ⟨z,z⟩) :=
          by
            constructor
            · simp only [Set.mem_singleton_iff]
            · exact yyInOrbitCloszz
      have yyyInOrbitClosyzz :
        (y,y,y) ∈ orbitClosure cornerSystem3 (y,z,z) :=
          (liftTo3Left y (xyyUniformlyRecurrent hMin y z)) yyyInyTimesOrbitCloszz
      have xyyInOrbitClosyyy :
        (x,y,y) ∈ orbitClosure cornerSystem3 (y,y,y) :=
          (xyInRPIffxyyInyyyOrbClosure hMin x y).mp xyInRP
      have zzInOrbitClosyy :
        (z,z) ∈ orbitClosure (diagDynamicalSystem dSystem dSystem) (y,y) :=
          diagonalOrbitVisits y z
            ((subset_of_eq (minimalImpliesFullOrbitClosure hMin y).symm) (Set.mem_univ y))
      have xzzInxTimesOrbitClosyy :
        (x,z,z) ∈ ({x} : Set X) ×ˢ (orbitClosure (diagDynamicalSystem dSystem dSystem) ⟨y,y⟩) :=
          by
            constructor
            · simp only [Set.mem_singleton_iff]
            · exact zzInOrbitClosyy
      have xzzInOrbitClosxyy :
        (x,z,z) ∈ orbitClosure cornerSystem3 (x,y,y) :=
          (liftTo3Left x (xyyUniformlyRecurrent hMin x y)) xzzInxTimesOrbitClosyy
      have xzzInOrbitCloszzz :
        (x,z,z) ∈ orbitClosure cornerSystem3 (z,z,z) :=
          orbitTransitivity (orbitTransitivity (orbitTransitivity yzzInOrbitCloszzz yyyInOrbitClosyzz) xyyInOrbitClosyyy) xzzInOrbitClosxyy
      exact (xyInRPIffxyyInyyyOrbClosure hMin x z).symm.mp xzzInOrbitCloszzz
  }

/-- The regionally proximal relation of a minimal dynamical system
is an ICER -/
theorem RPisICER
(hMin : isMinimalSystem dSystem) :
isICER dSystem (RP dSystem) :=
by
  unfold isICER
  unfold isEquivalenceRelation
  simp only [(equivalenceRelationSetForm (RP dSystem))]
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact RPisInvariant dSystem
  · exact RPisClosed dSystem
  · exact RPisReflexiveIfNondegen dSystem (minimalImpliesNondegen hMin)
  · exact RPisSymmetric dSystem
  · exact minimalImpliesRPisTransitive hMin

/-- The regionally proximal relation of a minimal dynamical system
is the equicontinuous structure relation -/
theorem RPisEquiStructureRelation
(hMin : isMinimalSystem dSystem) :
RP dSystem = equiStructureRelation dSystem :=
by
  ext x
  constructor
  · intro hx
    exact (minimalICEREquicontinuousIffRPInICER hMin (equiStructureRelationIsICER dSystem)).mp
      (equiStructureRelationIsEquiICER dSystem) hx
  · intro hx
    have RPisEquiICER : isEquicontinuousICER dSystem (RPisICER hMin) :=
      (minimalICEREquicontinuousIffRPInICER hMin (RPisICER hMin)).symm.mp subset_rfl
    have RPinSetOfEquiICERS : RP dSystem ∈ setOfEquicontinuousICERS dSystem := by
      unfold setOfEquicontinuousICERS
      use RPisICER hMin
    unfold equiStructureRelation at hx
    simp only [Set.mem_sInter] at hx
    exact hx (RP dSystem) RPinSetOfEquiICERS

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
