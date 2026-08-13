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
        rcases (minimalImpliesNonemptySetVisits hMin x.1 hVopen (Set.nonempty_of_mem hxV))
          with ⟨s, hs⟩
        rcases (minimalImpliesNonemptySetVisits hMin (dSystem.map s x.2)
          hWopen (Set.nonempty_of_mem hyW)) with ⟨t, ht⟩
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
{x y : X} (z : X)
(hUR : isUniformlyRecurrent (cornerSystem3 (dSystem := dSystem)) ⟨x, y, z⟩) :
(Equiv.prodAssoc X X X) ''
(orbitClosure (diagDynamicalSystem dSystem dSystem) ⟨x,y⟩) ×ˢ ({z} : Set X) ⊆
orbitClosure (cornerSystem3 (dSystem := dSystem)) ⟨x,y,z⟩ :=
by
  have goalWithoutClosure : (Equiv.prodAssoc X X X) ''
    (orbit (diagDynamicalSystem dSystem dSystem) ⟨x,y⟩) ×ˢ ({z} : Set X) ⊆
    orbitClosure (cornerSystem3 (dSystem := dSystem)) ⟨x,y,z⟩ :=
      by
        intro w hw
        unfold Set.image at hw
        rcases hw with ⟨⟨a,b⟩,hb,hb2⟩
        rcases hb with ⟨ha,hb⟩
        simp only at hb
        simp only [Set.mem_singleton_iff] at hb
        unfold orbit at ha
        simp only at ha
        rcases ha with ⟨s,hs⟩
        unfold diagDynamicalSystem Prod.map at hs
        simp only at hs
        have wdesc : w = ⟨dSystem.map s x, dSystem.map s y, z⟩ :=
          by
            rw [←hs] at hb2
            rw [hb] at hb2
            exact
              Prod.ext (congrArg Prod.fst (id (Eq.symm hb2)))
                (congrArg Prod.snd (id (Eq.symm hb2)))
        rw [wdesc]
        unfold orbitClosure
        simp only [mem_closure_iff]
        intro W WisOpen WcontainsPt
        have leftmapprimageofWIsNhdOfxyz :
          (leftMap3 (dSystem := dSystem) s) ⁻¹' W ∈ nhds ⟨x,y,z⟩ :=
            by
              simp only [mem_nhds_iff]
              use (leftMap3 (dSystem := dSystem) s) ⁻¹' W
              refine ⟨?_,?_,?_⟩
              · rfl
              · exact WisOpen.preimage (leftMap3Continuous s)
              · simp only [Set.mem_preimage]
                unfold leftMap3
                simp only
                exact WcontainsPt
        specialize hUR ((leftMap3 (dSystem := dSystem) s) ⁻¹' W) leftmapprimageofWIsNhdOfxyz
        rcases hUR with ⟨F,hF,hF2⟩
        rcases (inferInstance : Nonempty (S × S)) with ⟨t⟩
        specialize hF2 t
        rcases hF2 with ⟨f,hf,hf2⟩
        unfold visitTimeSet at hf2
        simp only [Set.mem_preimage] at hf2
        use (leftMap3 (dSystem := dSystem)) s ((cornerSystem3 (dSystem := dSystem)).map
          (f * t) (x, y, z))
        constructor
        · exact hf2
        · use ⟨s * f.1 * t.1, f.2 * t.2⟩
          unfold cornerSystem3 leftMap3 rightMap3
          simp only
          simp [←dSystem.mapMult]
          simp [mul_assoc]
  have applyClosure := closure_mono goalWithoutClosure
  have lem (A : Set (X × X)) (B : Set X) :
    closure ((Equiv.prodAssoc X X X) '' A ×ˢ B) = (Equiv.prodAssoc X X X) '' (closure (A ×ˢ B)) :=
      (imageClosureIsClosureImage (Homeomorph.prodAssoc X X X).continuous (A ×ˢ B)).symm
  have closureSimp :
  closure ((Equiv.prodAssoc X X X) '' orbit (diagDynamicalSystem dSystem dSystem) (x, y) ×ˢ {z}) =
    (Equiv.prodAssoc X X X) ''
      (closure (orbit (diagDynamicalSystem dSystem dSystem) (x, y)) ×ˢ {z}) :=
      by
        simp only [lem (orbit (diagDynamicalSystem dSystem dSystem) (x, y)) ({z})]
        simp only [closure_prod_eq]
        simp only [isClosed_singleton.closure_eq]
  simp only [closureSimp] at applyClosure
  unfold orbitClosure at applyClosure
  unfold orbitClosure
  simp only [closure_closure] at applyClosure
  exact applyClosure

/-- If `(x,y,z)` is uniformly recurrent under `S^2`, then the cartesian product of
`{x}` with the closure of `S(y,z)` is contained in the closure of `S^2 (x,y,z)` -/
theorem liftTo3Left
(x : X) {y z : X}
(hUR : isUniformlyRecurrent (cornerSystem3 (dSystem := dSystem)) ⟨x, y, z⟩) :
({x} : Set X) ×ˢ (orbitClosure (diagDynamicalSystem dSystem dSystem) ⟨y,z⟩) ⊆
orbitClosure (cornerSystem3 (dSystem := dSystem)) ⟨x,y,z⟩ :=
by
  have goalWithoutClosure :
  ({x} : Set X) ×ˢ (orbit (diagDynamicalSystem dSystem dSystem) ⟨y,z⟩) ⊆
    orbitClosure (cornerSystem3 (dSystem := dSystem)) ⟨x,y,z⟩ :=
      by
        intro ⟨b,a⟩ hw
        rcases hw with ⟨hb,ha⟩
        simp only at hb
        simp only [Set.mem_singleton_iff] at hb
        unfold orbit at ha
        simp only at ha
        rcases ha with ⟨s,hs⟩
        unfold diagDynamicalSystem Prod.map at hs
        simp only at hs
        rw [hb]
        rw [←hs]
        unfold orbitClosure
        simp only [mem_closure_iff]
        intro W WisOpen WcontainsPt
        have rightmapprimageofWIsNhdOfxyz :
          (rightMap3 (dSystem := dSystem) s) ⁻¹' W ∈ nhds ⟨x,y,z⟩ :=
            by
              simp only [mem_nhds_iff]
              use (rightMap3 (dSystem := dSystem) s) ⁻¹' W
              refine ⟨?_,?_,?_⟩
              · rfl
              · exact WisOpen.preimage (rightMap3Continuous s)
              · simp only [Set.mem_preimage]
                unfold rightMap3
                simp only
                exact WcontainsPt
        specialize hUR ((rightMap3 (dSystem := dSystem) s) ⁻¹' W) rightmapprimageofWIsNhdOfxyz
        rcases hUR with ⟨F,hF,hF2⟩
        rcases (inferInstance : Nonempty (S × S)) with ⟨t⟩
        specialize hF2 t
        rcases hF2 with ⟨f,hf,hf2⟩
        unfold visitTimeSet at hf2
        simp only [Set.mem_preimage] at hf2
        use (rightMap3 (dSystem := dSystem)) s ((cornerSystem3 (dSystem := dSystem)).map
          (f * t) (x, y, z))
        constructor
        · exact hf2
        · use ⟨f.1 * t.1, f.2 * t.2 * s⟩
          unfold cornerSystem3 leftMap3 rightMap3
          simp only
          simp only [←dSystem.mapMult]
          simp only [Prod.mk.injEq, true_and]
          simp only [mul_assoc]
          constructor
          · nth_rw 5 [← mul_comm]
            nth_rw 3 [← mul_assoc]
            nth_rw 2 [← mul_assoc]
            nth_rw 1 [← mul_assoc]
          · nth_rw 3 [mul_comm]
            nth_rw 1 [← mul_assoc]
  have applyClosure := closure_mono goalWithoutClosure
  simp only [closure_prod_eq] at applyClosure
  simp only [isClosed_singleton.closure_eq] at applyClosure
  unfold orbitClosure at applyClosure
  unfold orbitClosure
  simp only [closure_closure] at applyClosure
  exact applyClosure

end Corner_System_2

section Corner_System_1

omit [CommSemigroup S] [Nonempty S] [CompactSpace X] [T2Space X] [Nonempty X] in
/-- Given an action of `S` on `X`, `leftMap1: X → X` is defined by `s z = z` -/
def leftMap1 (s : S) : X → X := id

omit [CommSemigroup S] [Nonempty S] [CompactSpace X] [T2Space X] [Nonempty X] in
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
  mapMult := by
    intro s t x
    simp only
    unfold leftMap1
    unfold rightMap1
    simp only [dSystem.mapMult]
    exact rfl
  mapCont := by
    intro s
    simp only
    exact Continuous.comp (leftMap1Continuous s.1) (rightMap1Continuous s.2)
}

/-- Projection `π3: X^3 → X` is a factor map of `cornerSystem3` to `cornerSystem1` -/
theorem pi3FromCorner3ToCorner1IsFactor :
isFactorMap (dSystemX := cornerSystem3 (dSystem := dSystem))
  (cornerSystem1 (dSystem := dSystem)) π3 :=
by
  unfold isFactorMap
  unfold π3
  refine ⟨?_,?_,?_⟩
  · exact Continuous.comp continuous_snd continuous_snd
  · unfold Function.Surjective
    intro w
    use ⟨w,w,w⟩
  · unfold isEquivariant
    intro ⟨s,t⟩
    unfold cornerSystem1
    unfold cornerSystem3
    unfold leftMap1
    unfold rightMap1
    unfold leftMap3
    unfold rightMap3
    simp only
    exact Eq.symm (Function.Semiconj.comp_eq (congrFun rfl))

/-- If `x` and `y` are proximal in `cornerSystem1`, then they are proximal in `dSystem` -/
theorem cornerProxImpliesProx (x y : X) :
proximal (cornerSystem1 (dSystem := dSystem)) x y → proximal dSystem x y :=
by
  intro hProx
  unfold proximal
  intro α αNbhd
  specialize hProx α αNbhd
  rcases hProx with ⟨s,sProp⟩
  unfold cornerSystem1 at sProp
  unfold leftMap1 at sProp
  unfold rightMap1 at sProp
  unfold id at sProp
  simp only at sProp
  use s.2

end Corner_System_1

section Ultrafilters_and_the_corner_space

/-- Given an ultrafilter `p : β(S × S)`, `p (x,y,z) = (p(x,y), pz)` -/
theorem ultraActionOnX3
(p : Ultrafilter (S × S)) (x y z : X) :
(ultraAction (cornerSystem3 (dSystem := dSystem))).map p ⟨x,y,z⟩ =
  i21 ⟨(ultraAction (cornerSystem2 (dSystem := dSystem))).map p ⟨x,y⟩,
    (ultraAction (cornerSystem1 (dSystem := dSystem))).map p z⟩ :=
by
  let xyz : X × X × X := ⟨x,y,z⟩
  let xy : X × X := ⟨x,y⟩
  let pxyz : X × X × X := (ultraAction (cornerSystem3 (dSystem := dSystem))).map p ⟨x,y,z⟩
  let pxy : X × X := (ultraAction (cornerSystem2 (dSystem := dSystem))).map p ⟨x,y⟩
  let pz : X := (ultraAction (cornerSystem1 (dSystem := dSystem))).map p z
  have π12pxyzIspxy : π12 pxyz = pxy :=
    by
      have pCommutesWithπ12 :=
        (congr_fun (ultraActionIntertwinesWithFactor
          (cornerSystem3 (dSystem := dSystem))
          (cornerSystem2) (pi12FromCorner3ToCorner2IsFactor) p) xyz).symm
      unfold Function.comp at pCommutesWithπ12
      exact pCommutesWithπ12
  have π3pxyzIspz : π3 pxyz = pz :=
    by
      have pCommutesWithπ3 :=
        (congr_fun (ultraActionIntertwinesWithFactor
          (cornerSystem3 (dSystem := dSystem))
          (cornerSystem1) (pi3FromCorner3ToCorner1IsFactor) p) xyz).symm
      unfold Function.comp at pCommutesWithπ3
      exact pCommutesWithπ3
  have pxyzIsπ12π3 (w : X × X × X) : w = i21 ⟨π12 w, π3 w⟩ :=
    by
      unfold i21 π12 π3
      simp only
  specialize pxyzIsπ12π3 pxyz
  simp only [π12pxyzIspxy] at pxyzIsπ12π3
  simp only [π3pxyzIspz] at pxyzIsπ12π3
  unfold pxy at pxyzIsπ12π3
  unfold pz at pxyzIsπ12π3
  exact pxyzIsπ12π3

end Ultrafilters_and_the_corner_space


section RP_and_corner_dynamics

/-- If `S` acts minimally on `X`, then for all `x, y ∈ X`, the point
`(x,x,x)` is uniformly recurrent in `cornerSystem3` -/
theorem xxxUniformlyRecurrent
(hMin : isMinimalSystem dSystem) (x : X) :
isUniformlyRecurrent (cornerSystem3 (dSystem := dSystem)) ⟨x,x,x⟩ :=
by
  have corner2IsMin := minimalSystemImpliesMinimalcornerSystem2 hMin
  let xxx : X × X × X := ⟨x,x,x⟩
  let xx: X × X := ⟨x,x⟩
  rcases (rightTopSemigroupContainsMinLeftIdeal (S := Ultrafilter (S × S))) with ⟨L,LMin⟩
  rcases (everyPointInMinFixedBySomeIdempotentUltrafilter cornerSystem2 corner2IsMin LMin xx)
    with ⟨p,pInL,pIdemp,pFixesxx⟩
  let px := (ultraAction (cornerSystem1 (dSystem := dSystem))).map p x
  let xpx : X × X := ⟨x,px⟩
  let xxpx : X × X × X := ⟨x,x,px⟩
  have pIsMin : isMinimalUltrafilter p := by use L
  have imageOfpxxx := ultraActionOnX3 (dSystem := dSystem) p x x x
  have xxxpxxxAreProx :=
    pointAndUltraImageAreProximal (cornerSystem3 (dSystem := dSystem)) xxx pIdemp
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
  exact xxxIsUR


/-- If `S` acts minimally on `X`, then for all `x, y ∈ X`, the point
`(x,y,y)` is uniformly recurrent in `cornerSystem3` -/
theorem xyyUniformlyRecurrent
(hMin : isMinimalSystem dSystem) (x y : X) :
isUniformlyRecurrent (cornerSystem3 (dSystem := dSystem)) ⟨x,y,y⟩ :=
by
  have xxxIsUR := xxxUniformlyRecurrent hMin x
  let xx: X × X := ⟨x,x⟩
  let xyy : X × X × X := ⟨x,y,y⟩
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
by
  have yyyIsUR := xxxUniformlyRecurrent hMin y
  let yy: X × X := ⟨y,y⟩
  let xxy : X × X × X := ⟨x,x,y⟩
  have xxInOrbitClosyy :
    (x,x) ∈ orbitClosure (diagDynamicalSystem dSystem dSystem) yy :=
      diagonalOrbitVisits y x
        ((subset_of_eq (minimalImpliesFullOrbitClosure hMin y).symm) (Set.mem_univ y))
  have OrbClosyyThenyInOrbClosyyy := liftTo3Right y yyyIsUR
  have xxyInOrbClosyyTheny :
    xxy ∈ (Equiv.prodAssoc X X X) ''
      (orbitClosure (diagDynamicalSystem dSystem dSystem) yy ×ˢ {y}) :=
        by
          unfold xxy
          unfold yy
          simp only [Equiv.prodAssoc_apply, Set.mem_image, Set.mem_prod, Set.mem_singleton_iff,
            Prod.mk.injEq, Prod.exists, ↓existsAndEq, and_true, exists_eq_right_right,
            exists_eq_right]
          exact xxInOrbitClosyy
  have xxyInOrbClosyyy := OrbClosyyThenyInOrbClosyyy xxyInOrbClosyyTheny
  exact inOrbitClosOfURPointImpliesUR (cornerSystem3 (dSystem := dSystem)) yyyIsUR xxyInOrbClosyyy

/-- If `S` acts minimally on `X`, then for all `x, y ∈ X`, the point
`(x,y) ∈ RP` if and only if `(x,y,y)` is in the `S^2` orbit closure of `(y,y,y)` -/
theorem xyInRPIffxyyInyyyOrbClosure
(hMin : isMinimalSystem dSystem) (x y : X) :
((x,y) ∈ RP dSystem ↔
(x,y,y) ∈ orbitClosure (cornerSystem3 (dSystem := dSystem)) ⟨y,y,y⟩)
∧
((x,y) ∈ RPM dSystem ↔
(x,y,y) ∈ orbitClosure (cornerSystem3 (dSystem := dSystem)) ⟨y,y,y⟩) :=
by
  have RPMgoal : (x,y) ∈ RPM dSystem ↔
(x,y,y) ∈ orbitClosure (cornerSystem3 (dSystem := dSystem)) ⟨y,y,y⟩ :=
  by
    constructor
    · intro xyInRP
      let f1 : (X × X) × S → (X × X) × (X × X) :=
        fun (⟨a,s⟩ : (X × X) × S) ↦ (a, (diagDynamicalSystem dSystem dSystem).map s a)
      rcases (xyInRPMIffUltraToSomewwxy dSystem x y).mp xyInRP with ⟨w,F,hf1Ftendstowwxy⟩
      --(fun x ↦ match x with | (a, s) => (a, (diagDynamicalSystem dSystem dSystem).map s a))
      let ww : X × X := ⟨w,w⟩
      rcases (rightTopSemigroupContainsMinLeftIdeal (S := Ultrafilter (S × S))) with ⟨L,LMin⟩
      have wwMapsToAnyab (a : X × X) :
        ∃ (p : Ultrafilter (S × S)), p ∈ L ∧
          (ultraAction (cornerSystem2 (dSystem := dSystem))).map p ww = a :=
            minLeftIdealSurjectsOntoMinSystem (cornerSystem2 (dSystem := dSystem))
              (minimalSystemImpliesMinimalcornerSystem2 hMin) LMin ww a
      let f2 : (X × X) × S → Ultrafilter (S × S) :=
        fun (⟨a,s⟩ : (X × X) × S) => Classical.choose (wwMapsToAnyab a)
      have f2_property :
        ∀ (as : (X × X) × S), (f2 as ∈ L) ∧
          (ultraAction (cornerSystem2 (dSystem := dSystem))).map (f2 as) ww = as.1 :=
            by
              intro as
              exact Classical.choose_spec (wwMapsToAnyab as.1)
      have ultraSSisCompact := isCompact_univ (X := Ultrafilter (S × S))
      have LisCompact : IsCompact L := minimalLeftIdealCompact LMin
      have f2FonL : L ∈ Ultrafilter.map f2 F :=
        by
          rw [Ultrafilter.mem_map]
          have hpre : f2 ⁻¹' L = Set.univ := by
            ext as
            constructor
            · intro has
              trivial
            · simp [Set.preimage]
              simp only [f2_property as]
          rw [hpre]
          exact Filter.univ_mem
      rcases (IsCompact.ultrafilter_le_nhds LisCompact) (Ultrafilter.map f2 F)
        (Filter.le_principal_iff.mpr f2FonL) with ⟨p,pInL,f2FTendsTop⟩
      let f3 : Ultrafilter (S × S) → X × X :=
        fun (q : Ultrafilter (S × S)) ↦
          (ultraAction (cornerSystem2 (dSystem := dSystem))).map q ww
      have f3continuous : Continuous f3 :=
        ultraActionWithFixedxIsContinuous (cornerSystem2 (dSystem := dSystem)) ww
      let π : (X × X) × (X × X) → X × X := Prod.fst
      have πContinuous : Continuous π := continuous_fst
      have f3f2ispif1 : f3 ∘ f2 = π ∘ f1 :=
        by
          ext pt
          · simp only [Function.comp_apply]
            unfold f1 f3 π
            simp only [(f2_property pt).2]
          · simp only [Function.comp_apply]
            unfold f1 f3 π
            simp only
            simp only [(f2_property (pt)).2]
      have f3f2FTendsToww : Filter.Tendsto (f3 ∘ f2) F (nhds ww) :=
        by
          simp only [f3f2ispif1]
          exact Filter.Tendsto.comp (πContinuous.tendsto ⟨ww,⟨x,y⟩⟩) hf1Ftendstowwxy
      let pww : X × X := (ultraAction (cornerSystem2 (dSystem := dSystem))).map p ww
      have f3f2FTendsTopww : Filter.Tendsto (f3 ∘ f2) F (nhds pww) :=
        Filter.Tendsto.comp (f3continuous.tendsto p) f2FTendsTop
      have pwwIsww : pww = ww := tendsto_nhds_unique f3f2FTendsTopww f3f2FTendsToww
      rcases (idempotentProductLifting (cornerSystem2 (dSystem := dSystem))
        ww LMin pInL pwwIsww)
          with ⟨q,qInL,pqIdempotent,qFixesww⟩
      let f4 : (X × X) × S → X × X × X :=
        fun (⟨a,s⟩ : (X × X) × S) ↦
          (Equiv.prodAssoc X X X)
            ⟨(diagDynamicalSystem dSystem dSystem).map s a,
              (ultraAction (cornerSystem1 (dSystem := dSystem))).map ((f2 ⟨a,s⟩) * q) y⟩
      let pqy : X := (ultraAction (cornerSystem1 (dSystem := dSystem))).map (p * q) y
      let xypqy : X × X × X := ⟨x,⟨y,pqy⟩⟩
      let wwy : X × X × X := ⟨w,⟨w,y⟩⟩
      have f4TendsToxypqy : Filter.Tendsto f4 F (nhds xypqy) :=
        by
          unfold f4 xypqy
          simp only
          simp only [Prod.mk.eta, Equiv.prodAssoc_apply]
          let p3 : (X × X) × (X × X) → X := Prod.fst ∘ Prod.snd
          have p3cts : Continuous p3 := Continuous.comp continuous_fst continuous_snd
          let p4 : (X × X) × (X × X) → X := Prod.snd ∘ Prod.snd
          have p4cts : Continuous p4 := Continuous.comp continuous_snd continuous_snd
          refine Filter.Tendsto.prodMk_nhds ?_ ?_
          · have := Filter.Tendsto.comp (p3cts.tendsto ⟨ww,⟨x,y⟩⟩) hf1Ftendstowwxy
            exact this
          · refine Filter.Tendsto.prodMk_nhds ?_ ?_
            · have := Filter.Tendsto.comp (p4cts.tendsto ⟨ww,⟨x,y⟩⟩) hf1Ftendstowwxy
              exact this
            · let maprTorstarqy : Ultrafilter (S × S) → X :=
                fun r ↦ (ultraAction (cornerSystem1 (dSystem := dSystem))).map (r * q) y
              have maprTorstarqyCts : Continuous maprTorstarqy :=
                by
                  unfold maprTorstarqy
                  simp only [(ultraAction (cornerSystem1 (dSystem := dSystem))).mapMult]
                  exact ultraActionWithFixedxIsContinuous
                    (cornerSystem1 (dSystem := dSystem)) (((ultraAction cornerSystem1).map q y))
              exact Filter.Tendsto.comp (maprTorstarqyCts.tendsto p) f2FTendsTop
      let oCwwy := orbitClosure (cornerSystem3 (dSystem := dSystem)) wwy
      have f4MapsToOrbitClosOfwwy :
        Set.MapsTo f4 (Set.univ) oCwwy :=
          by
            unfold Set.MapsTo
            intro ⟨⟨a,b⟩,s⟩ absInSetUniv
            unfold f4
            simp only
            let pabqy :=
              (ultraAction (cornerSystem1 (dSystem := dSystem))).map (f2 ((a, b), s) * q) y
            let pabqwwy :=
              (ultraAction (cornerSystem3 (dSystem := dSystem))).map (f2 ((a, b), s) * q) wwy
            have rewriteEquality :
              (Equiv.prodAssoc X X X)
                ((diagDynamicalSystem dSystem dSystem).map s (a, b), pabqy) =
                  leftMap3 (dSystem := dSystem) s pabqwwy :=
                    by
                      unfold pabqy pabqwwy leftMap3
                      simp only [ultraActionOnX3 (f2 ⟨⟨a,b⟩,s⟩ * q)]
                      unfold i21 wwy
                      simp only [Equiv.prodAssoc_apply, Prod.mk.injEq]
                      simp only [(ultraAction (cornerSystem2 (dSystem := dSystem))).mapMult]
                      unfold ww at qFixesww
                      simp only [qFixesww]
                      have pabwwIsab :
                        (ultraAction (cornerSystem2 (dSystem := dSystem))).map
                          (f2 ⟨⟨a,b⟩,s⟩) ⟨w,w⟩ = ⟨a,b⟩ := (f2_property ⟨⟨a,b⟩,s⟩).2
                      simp only [pabwwIsab]
                      unfold diagDynamicalSystem
                      simp only [Prod.map_apply, and_self]
            unfold pabqy at rewriteEquality
            simp only [rewriteEquality]
            have pabqwwyInOrbCloswwy :
              (ultraAction cornerSystem3).map (f2 ((a, b), s) * q) wwy ∈ oCwwy :=
                ultraActionInOrbitClosure
                  (cornerSystem3 (dSystem := dSystem)) (f2 ((a, b), s) * q) wwy
            have leftMap3spabqwwyInleftMap3sOrbCloswwy :
              leftMap3 (dSystem := dSystem) s
                ((ultraAction (cornerSystem3 (dSystem := dSystem))).map (f2 ((a, b), s) * q) wwy) ∈
                  (leftMap3 (dSystem := dSystem) s) '' oCwwy :=
                    Set.mem_image_of_mem (leftMap3 (dSystem := dSystem) s) pabqwwyInOrbCloswwy
            have ocInvariance : (leftMap3 (dSystem := dSystem) s) '' oCwwy ⊆ oCwwy :=
              by
                let owwy := orbit (cornerSystem3 (dSystem := dSystem)) wwy
                have leftMapOrbClosIsClosLeftMapOrb :=
                  imageClosureIsClosureImage (leftMap3Continuous (dSystem := dSystem) s) owwy
                have orbitIsInv : (leftMap3 (dSystem := dSystem) s) '' owwy ⊆ owwy :=
                  by
                    unfold owwy orbit
                    intro ptx ptxInImage
                    simp only [Set.mem_image, Set.mem_range, Prod.exists,
                      exists_exists_exists_and_eq] at ptxInImage
                    rcases ptxInImage with ⟨s2,t2,hst⟩
                    have leftMapIntoCornerMult :
                      (leftMap3 (dSystem := dSystem) s)
                        ((cornerSystem3 (dSystem := dSystem)).map (s2, t2) wwy) =
                          (cornerSystem3 (dSystem := dSystem)).map (s * s2, t2) wwy :=
                            by
                              unfold cornerSystem3 leftMap3
                              simp only
                              simp only [dSystem.mapMult]
                    rw [leftMapIntoCornerMult] at hst
                    rw [← hst]
                    simp only [Set.mem_range, exists_apply_eq_apply]
                unfold oCwwy orbitClosure
                unfold owwy at leftMapOrbClosIsClosLeftMapOrb
                rw [leftMapOrbClosIsClosLeftMapOrb]
                apply closure_mono
                exact orbitIsInv
            have := ocInvariance leftMap3spabqwwyInleftMap3sOrbCloswwy
            exact this
      have xypqyInOrbitClosOfwwy :
        xypqy ∈ oCwwy :=
          by
            have goalwithclos : xypqy ∈ closure oCwwy :=
              by
                apply mem_closure_of_tendsto f4TendsToxypqy
                filter_upwards [Filter.univ_mem] with z
                intro hz
                exact f4MapsToOrbitClosOfwwy hz
            have oCIsClosed : IsClosed oCwwy := isClosed_closure
            simpa [oCIsClosed.closure_eq] using goalwithclos
      let yy : X × X := ⟨y,y⟩
      have yyyIsUR := xxxUniformlyRecurrent hMin y
      have wwInOrbitClosyy :
        ww ∈ orbitClosure (diagDynamicalSystem dSystem dSystem) yy :=
          diagonalOrbitVisits y w
            ((subset_of_eq (minimalImpliesFullOrbitClosure hMin y).symm) (Set.mem_univ y))
      have OrbClosyyThenyInOrbClosyyy := liftTo3Right y yyyIsUR
      have wwyInOrbClosyyTheny :
        wwy ∈ (Equiv.prodAssoc X X X) ''
          (orbitClosure (diagDynamicalSystem dSystem dSystem) yy ×ˢ {y}) :=
            by
              unfold wwy
              unfold yy
              simp only [Equiv.prodAssoc_apply, Set.mem_image, Set.mem_prod, Set.mem_singleton_iff,
                Prod.mk.injEq, Prod.exists, ↓existsAndEq, and_true, exists_eq_right_right,
                exists_eq_right]
              exact wwInOrbitClosyy
      have wwyInOrbClosyyy :=
        OrbClosyyThenyInOrbClosyyy wwyInOrbClosyyTheny
      have xypqyInOrbClosyyy :=
        orbitTransitivity wwyInOrbClosyyy xypqyInOrbitClosOfwwy
      have xypqyIsUR :=
        inOrbitClosOfURPointImpliesUR (cornerSystem3 (dSystem := dSystem)) yyyIsUR xypqyInOrbClosyyy
      have yProxUnderS2Topqy :=
        pointAndUltraImageAreProximal (cornerSystem1 (dSystem := dSystem)) y pqIdempotent
      have yProxUnderSTopqy :=
        cornerProxImpliesProx y pqy yProxUnderS2Topqy
      have yyInOrbClosypqy :=
        (minSystemOrbitClosProxPairContainsDiag hMin yProxUnderSTopqy) (Set.mem_diagonal y)
      have xOrbClosypqyInOrbClosxypqy := liftTo3Left x xypqyIsUR
      let xyy : X × X × X := ⟨x,⟨y,y⟩⟩
      let ypqy : X × X := ⟨y,pqy⟩
      have xyyInxOrbClosypqy :
        xyy ∈ {x} ×ˢ orbitClosure (diagDynamicalSystem dSystem dSystem) ypqy :=
          by
            constructor
            · unfold xyy
              simp only [Set.mem_singleton_iff]
            · exact yyInOrbClosypqy
      have xyyInOrbClosxypqy :
        xyy ∈ orbitClosure (cornerSystem3 (dSystem := dSystem)) xypqy :=
          xOrbClosypqyInOrbClosxypqy xyyInxOrbClosypqy
      exact orbitTransitivity xypqyInOrbClosyyy xyyInOrbClosxypqy
    · intro xxyInOrbClosyyy
      unfold RPM
      intro α hα
      simp only [Set.mem_range] at hα
      rcases hα with ⟨β, hβ⟩
      rw [← hβ]
      simp only [Set.mem_iInter]
      intro βnbhd
      unfold setOrbitClosure
      simp only [mem_closure_iff]
      intro U UOpen xyInU
      let βSlice := {z | ⟨y,z⟩ ∈ β}
      have βSliceIsNhdOfy : βSlice ∈ nhds y :=
        by
          have βnhdOfyy := (mem_nhdsSet_iff_forall.mp βnbhd) ⟨y, y⟩ (Set.mem_diagonal y)
          rw [mem_nhds_prod_iff] at βnhdOfyy
          rcases βnhdOfyy with ⟨V1, hV1, V2, hV2, V1V2inβ⟩
          have hslice : V2 ⊆ βSlice := by
            intro z hz
            have yzInV1V2 : ⟨y,z⟩ ∈ V1 ×ˢ V2 := by
              simp only [Set.mem_prod]
              exact ⟨mem_of_mem_nhds hV1, hz⟩
            unfold βSlice
            simp only [Set.mem_setOf_eq]
            exact V1V2inβ yzInV1V2
          exact Filter.mem_of_superset hV2 hslice
      rcases mem_nhds_iff.mp βSliceIsNhdOfy with ⟨W,WinβSlice,WOpen,yInW⟩
      let UβSlice := (Equiv.prodAssoc X X X) '' U ×ˢ βSlice
      have UβSliceIsnhdOfxyy : UβSlice ∈ nhds ⟨x,y,y⟩ :=
        by
          unfold UβSlice
          apply mem_nhds_iff.mpr
          use (Equiv.prodAssoc X X X) '' U ×ˢ W
          constructor
          · apply Set.image_mono
            exact Set.prod_mono (fun ⦃a⦄ a_1 ↦ a_1) WinβSlice
          · constructor
            · have UWOpen : IsOpen (U ×ˢ W) :=
                by
                  exact IsOpen.prod UOpen WOpen
              exact (Homeomorph.prodAssoc X X X).isOpenMap (U ×ˢ W) UWOpen
            · simp only [Equiv.prodAssoc_apply, Set.mem_image, Set.mem_prod, Prod.mk.injEq,
              Prod.exists, ↓existsAndEq, and_true, exists_eq_right_right, exists_eq_right]
              exact ⟨xyInU,yInW⟩
      have orbitPtLandsInUβSlice :
        ∃ (s : S × S), (cornerSystem3 (dSystem := dSystem)).map s ⟨y,y,y⟩ ∈ UβSlice :=
          by
            rcases mem_nhds_iff.mp UβSliceIsnhdOfxyy with ⟨V,VinUβSlice,VOpen,xyyInV⟩
            unfold orbitClosure at xxyInOrbClosyyy
            simp only [mem_closure_iff] at xxyInOrbClosyyy
            specialize xxyInOrbClosyyy V VOpen xyyInV
            rcases xxyInOrbClosyyy with ⟨pt,hpt1,hpt2⟩
            unfold orbit at hpt2
            simp only [Set.range] at hpt2
            rcases hpt2 with ⟨s7,hs7⟩
            use s7
            rw [hs7]
            exact VinUβSlice hpt1
      rcases orbitPtLandsInUβSlice with ⟨s, hs⟩
      have ys2yInβ : ⟨y,dSystem.map s.2 y⟩ ∈ β :=
        by
          unfold UβSlice cornerSystem3 leftMap3 rightMap3 at hs
          simp only at hs
          simp only [Equiv.prodAssoc_apply, Set.mem_image, Set.mem_prod, Prod.mk.injEq, Prod.exists,
            ↓existsAndEq, and_true, exists_eq_right_right, exists_eq_right] at hs
          rcases hs with ⟨hs1,hs2⟩
          unfold βSlice at hs2
          exact hs2
      have s1ToPairInU :
        (diagDynamicalSystem dSystem dSystem).map s.1 ⟨y,dSystem.map s.2 y⟩ ∈ U :=
          by
            unfold UβSlice cornerSystem3 leftMap3 rightMap3 at hs
            simp only at hs
            simp only [Equiv.prodAssoc_apply, Set.mem_image, Set.mem_prod, Prod.mk.injEq, Prod.exists,
              ↓existsAndEq, and_true, exists_eq_right_right, exists_eq_right] at hs
            rcases hs with ⟨hs1,hs2⟩
            unfold diagDynamicalSystem Prod.map
            simp only
            exact hs1
      have s1ToPairInOrbit :
        (diagDynamicalSystem dSystem dSystem).map s.1 ⟨y,dSystem.map s.2 y⟩ ∈
          setOrbit (diagDynamicalSystem dSystem dSystem) β :=
            by
              have applyDiags1 :=
                Set.mem_image_of_mem ((diagDynamicalSystem dSystem dSystem).map s.1) ys2yInβ
              have diags1βInβOrbit :
                (diagDynamicalSystem dSystem dSystem).map s.1 '' β ⊆
                  setOrbit (diagDynamicalSystem dSystem dSystem) β :=
                    by
                      intro xpt hxpt
                      unfold setOrbit Set.range
                      simp only
                      simp only [Set.mem_image] at hxpt
                      rcases hxpt with ⟨bpt,hbpt1,hbpt2⟩
                      use ⟨s.1,bpt,hbpt1⟩
              exact diags1βInβOrbit applyDiags1
            -- ys2yInβ : ⟨y,dSystem.map s.2 y⟩ in β
            -- hit with (diagDynamicalSystem dSystem dSystem).map s.1 to see that
            -- (diagDynamicalSystem dSystem dSystem).map s.1 ⟨y,dSystem.map s.2 y⟩ in
            --- set orbit of β
      use (diagDynamicalSystem dSystem dSystem).map s.1 ⟨y,dSystem.map s.2 y⟩
      exact ⟨s1ToPairInU,s1ToPairInOrbit⟩
  refine ⟨?_, ?_⟩
  · sorry --finish this with forwardEqualsBackwardRPInMinCommSystem and RPMGoal
  · exact RPMgoal

end RP_and_corner_dynamics


section RP_is_EQ_relation

/-- If `S` acts minimally on `X`, then the regionally proximal relation is transitive -/
theorem minimalImpliesRPisTransitive
(hMin : isMinimalSystem dSystem) :
isTransitive (RP dSystem) :=
by
  unfold isTransitive
  unfold setToRelation
  intro x y z xyInRP yzInRP
  have yzzInOrbitCloszzz :
    (y,z,z) ∈ orbitClosure cornerSystem3 (z,z,z) :=
      (xyInRPIffxyyInyyyOrbClosure hMin y z).1.mp yzInRP
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
      (xyInRPIffxyyInyyyOrbClosure hMin x y).1.mp xyInRP
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
      orbitTransitivity (orbitTransitivity (orbitTransitivity
        yzzInOrbitCloszzz yyyInOrbitClosyzz) xyyInOrbitClosyyy) xzzInOrbitClosxyy
  exact (xyInRPIffxyyInyyyOrbClosure hMin x z).1.symm.mp xzzInOrbitCloszzz

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
  · exact RPInCommSemiIsInvariant dSystem
  · exact RPisClosed dSystem
  · exact RPisReflexive dSystem
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
    exact (minimalICEREquicontinuousIffRPInICER hMin (equiStructureRelationIsICER dSystem)).2.mp
      (equiStructureRelationIsEquiICER dSystem hMin) hx
  · intro hx
    have RPisEquiICER : isEquicontinuousICER dSystem (RPisICER hMin) :=
      (minimalICEREquicontinuousIffRPInICER hMin (RPisICER hMin)).2.symm.mp subset_rfl
    have RPinSetOfEquiICERS : RP dSystem ∈ setOfEquicontinuousICERS dSystem := by
      unfold setOfEquicontinuousICERS
      use RPisICER hMin
    unfold equiStructureRelation at hx
    simp only [Set.mem_sInter] at hx
    exact hx (RP dSystem) RPinSetOfEquiICERS
end RP_is_EQ_relation

section Corollaries

/-- In a minimal system, for `(x,y) ∈ RP` and `U, V ⊆ X` open with `y ∈ V`,
the intersection `R(x,U) ∩ R(V,U)` is a syndetic subset of `S` -/
theorem xyInRPImpliesSyndeticVisitTimeIntersection
(hMin : isMinimalSystem dSystem) {x y : X} :
((x, y) ∈ RP dSystem → ∀ (U V : Set X), IsOpen U → IsOpen V → U.Nonempty → y ∈ V →
isSyndetic ((visitTimeSet dSystem x U) ∩ (setVisitTimeSet dSystem V U)))
∧
((x, y) ∈ RPM dSystem → ∀ (U V : Set X), IsOpen U → IsOpen V → U.Nonempty → y ∈ V →
isSyndetic ((visitTimeSet dSystem x U) ∩ (setVisitTimeSet dSystem V U))) :=
by
  have RPgoal : (x, y) ∈ RP dSystem → ∀ (U V : Set X), IsOpen U → IsOpen V → U.Nonempty → y ∈ V →
isSyndetic ((visitTimeSet dSystem x U) ∩ (setVisitTimeSet dSystem V U)) := by
    intro hxyInRP U V UIsOpen VIsOpen UIsNonempty yinV
    let ϕ : S × S → S := Prod.snd
    have imageOfVisitsIsSyndetic :
      isSyndetic (ϕ '' visitTimeSet (cornerSystem3 (dSystem := dSystem)) ⟨x,x,x⟩ (V ×ˢ U ×ˢ U)) :=
      by
        rcases UIsNonempty with ⟨z,hz⟩
        have yxInRP := (RPisSymmetric dSystem) hxyInRP
        have yxxInOrbClosxxx :
          ⟨y,x,x⟩ ∈ orbitClosure (cornerSystem3 (dSystem := dSystem)) ⟨x,x,x⟩ :=
            (xyInRPIffxyyInyyyOrbClosure hMin y x).1.mp yxInRP
        have yxxIsUR : isUniformlyRecurrent (cornerSystem3 (dSystem := dSystem)) ⟨y,x,x⟩ :=
          inOrbitClosOfURPointImpliesUR (cornerSystem3 (dSystem := dSystem))
            (xxxUniformlyRecurrent hMin x) yxxInOrbClosxxx
        let xx: X × X := ⟨x,x⟩
        let zz: X × X := ⟨z,z⟩
        let yzz : X × X × X := ⟨y,z,z⟩
        have zzInOrbitClosxx :
          (z,z) ∈ orbitClosure (diagDynamicalSystem dSystem dSystem) xx :=
            diagonalOrbitVisits x z
              ((subset_of_eq (minimalImpliesFullOrbitClosure hMin x).symm) (Set.mem_univ x))
        have yzzInyOrbClosxx :
          yzz ∈ {y} ×ˢ orbitClosure (diagDynamicalSystem dSystem dSystem) xx :=
            by
              constructor
              · unfold yzz
                simp only [Set.mem_singleton_iff]
              · exact zzInOrbitClosxx
        have yzzInOrbClosyxx :
          yzz ∈ orbitClosure (cornerSystem3 (dSystem := dSystem)) ⟨y,x,x⟩ :=
            liftTo3Left y yxxIsUR yzzInyOrbClosxx
        have yzzInOrbClosxxx := orbitTransitivity yxxInOrbClosxxx yzzInOrbClosyxx
        have xxxIsUR := xxxUniformlyRecurrent hMin x
        let VUU := V ×ˢ U ×ˢ U
        have VUUIsOpen : IsOpen VUU :=
          by
            refine IsOpen.prod VIsOpen ?_
            exact IsOpen.prod UIsOpen UIsOpen
        have xxxVisitsVUU :
          (visitTimeSet (cornerSystem3 (dSystem := dSystem)) ⟨x,x,x⟩ VUU).Nonempty :=
            by
              have VUUnhdOfyzz : yzz ∈ VUU :=
                by
                  unfold yzz VUU
                  simp only [Set.mem_prod, and_self]
                  exact ⟨yinV,hz⟩
              have orbitVisitsVUU :
                (VUU ∩ (orbit (cornerSystem3 (dSystem := dSystem)) ⟨x,x,x⟩)).Nonempty :=
                  (mem_closure_iff.mp yzzInOrbClosxxx) VUU VUUIsOpen VUUnhdOfyzz
              unfold visitTimeSet
              rcases orbitVisitsVUU with ⟨u,hu,hu2⟩
              unfold orbit at hu2
              simp only [Set.mem_range, Prod.exists] at hu2
              rcases hu2 with ⟨s1,s2,hs12⟩
              use ⟨s1,s2⟩
              simp only [Set.mem_preimage]
              rw [hs12]
              exact hu
        have VUUIsNonempty : VUU.Nonempty :=
          by
            unfold VUU
            simp only [Set.prod_nonempty_iff, and_self]
            exact ⟨Set.nonempty_of_mem yinV,Set.nonempty_of_mem hz⟩
        have xxxVisitsVUUSyndetically :=
          nonemptyVisitsOfURPointImpliesSyndetic (cornerSystem3 (dSystem := dSystem))
            xxxIsUR xxxVisitsVUU (UOpen := VUUIsOpen)
        have ϕsurj : Function.Surjective ϕ :=
          by
            unfold ϕ
            intro y
            exact ⟨(Classical.arbitrary S, y), rfl⟩
        letI : SemigroupHom ϕ :=
          {
            hom_prop :=
              by
                intro s1 s2
                unfold ϕ
                simp only [Prod.snd_mul]
          }
        exact surjImgOfSyndeticIsSyndetic ϕ ϕsurj xxxVisitsVUUSyndetically
    have imageOfVisitsIsContainedInTarget :
      ϕ '' visitTimeSet (cornerSystem3 (dSystem := dSystem)) ⟨x,x,x⟩ (V ×ˢ U ×ˢ U) ⊆
        (visitTimeSet dSystem x U) ∩ (setVisitTimeSet dSystem V U) :=
          by
            intro s rInSet
            simp only [Set.mem_image] at rInSet
            rcases rInSet with ⟨⟨g,r⟩,hg,hg2⟩
            unfold visitTimeSet cornerSystem3 leftMap3 rightMap3 at hg
            simp only at hg
            simp only [Set.mem_preimage, Set.mem_prod, ←dSystem.mapMult, mul_comm g r] at hg
            have gInRxV : g ∈ visitTimeSet dSystem x V := hg.1
            have rInRxU : r ∈ visitTimeSet dSystem x U := hg.2.2
            have rgInRxU : r * g ∈ visitTimeSet dSystem x U := hg.2.1
            have rInRVUpre : r ∈ ⋃ a ∈ visitTimeSet dSystem x V,
              ((· * a) ⁻¹' (visitTimeSet dSystem x U)) :=
              by
                simp only [Set.mem_iUnion, Set.mem_preimage, exists_prop]
                use g
            rw [← setVisitsAsQuotientSet hMin x V U] at rInRVUpre
            · unfold ϕ at hg2
              simp only at hg2
              rw [← hg2]
              exact ⟨rInRxU,rInRVUpre⟩
            · exact VIsOpen
            · exact UIsOpen
    exact syndeticIsMonotone imageOfVisitsIsSyndetic imageOfVisitsIsContainedInTarget
  refine ⟨?_, ?_⟩
  · exact RPgoal
/- The remaining statement can be derived easily from
forwardEqualsBackwardRPInMinCommSystem and RPgoal -/
  · sorry

/-- In a minimal commutative system, the equicontinuous structure relation
is strongly `S`-invariant -/
theorem equiStructureRelationIsStrongSInvariant
(hMin : isMinimalSystem dSystem) :
equiStructureRelation dSystem =
  inverseSetOrbit (diagDynamicalSystem dSystem dSystem) (equiStructureRelation dSystem) :=
  by sorry

/-- In a minimal commutative system, `RP` and `RPM` are strongly `S`-invariant -/
theorem RPIsStrongSInvariant
(hMin : isMinimalSystem dSystem) :
(RP dSystem = inverseSetOrbit (diagDynamicalSystem dSystem dSystem) (RP dSystem))
∧
(RPM dSystem = inverseSetOrbit (diagDynamicalSystem dSystem dSystem) (RP dSystem)) := by
  have RPgoal : RP dSystem = inverseSetOrbit (diagDynamicalSystem dSystem dSystem) (RP dSystem) := by
    sorry
  refine ⟨?_, ?_⟩
  · exact RPgoal
  · sorry

end Corollaries

section Natural_extensions

-- Under construction

/-- When `X` is both a minimal S and T system and actions commute, `RP_S = RP_T` -/
theorem forTwoMinCommActionsRPsAreSame
{T} [CommSemigroup T] [Nonempty T] {dSystemT : DynamicalSystem T X}
(hMin : isMinimalSystem dSystem) (hMinT : isMinimalSystem dSystemT) :
∀ (s : S) (t : T), (dSystem.map s) ∘ (dSystemT.map t) = (dSystemT.map t) ∘ (dSystem.map s) →
  RP dSystem = RP dSystemT := by sorry

--def grothendieckGroup := Algebra.GrothendieckGroup (WithOne S)

/- The Grothendieck group of a commutative semigroup S -/
-- theorem theGrothendieckGroupExists :
-- ∃ (G : Type*) [CommGroup G]

end Natural_extensions
