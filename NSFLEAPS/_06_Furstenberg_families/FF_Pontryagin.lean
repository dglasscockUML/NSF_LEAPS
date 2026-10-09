module

import NSFLEAPS._00_Imports.IM_Main

/-!
# Characters separate points on a compact abelian group

The main result of this file is `PontryaginDual.exists_apply_ne_one`: on a compact Hausdorff
abelian topological group `X`, for every `x ≠ 1` there is a continuous character
`χ : X → Circle` with `χ x ≠ 1`.  Equivalently, the Pontryagin dual of `X` separates points.

This is the abelian case of the Peter–Weyl theorem, and it is not available in Mathlib, so it is
proved here from scratch.  The argument is the classical one, arranged so as to use only tools
that are available in Mathlib.

## Outline of the proof

Write `μ` for the normalised Haar measure on `X` and `H = L²(X, μ)`.

* `CAPW.transl`: translation `transl μ a f = f (a * ·)` is a linear isometry of `H`, and
  `a ↦ transl μ a` is an action of `X` by unitaries.
* `CAPW.Top`: for `φ : C(X, ℂ)` the *smoothing operator* `T_φ` is defined by
  `T_φ f = (y ↦ ⟪Fmap φ y, f⟫)`, where `Fmap φ y ∈ H` is the translate `z ↦ φ (y⁻¹ * z)`.
  Concretely `T_φ` is convolution by `φ`, but writing it this way makes it manifest that
  `T_φ f` is a *continuous* function, so no Fubini theorem is needed anywhere.
  - `CAPW.Top_transl`: `T_φ` commutes with every translation.
  - `CAPW.Top_isCompactOperator`: `T_φ` is a compact operator.  Since `y ↦ Fmap φ y` is a
    continuous map from a compact space, its range is totally bounded; projecting onto the span
    of a finite `ε`-net exhibits `T_φ` as a norm limit of finite-rank operators.
  - `CAPW.eq_zero_of_forall_Top_eq_zero`: the operators `T_φ` have trivial common kernel,
    because `Fmap φ 1 = φ` and continuous functions are dense in `L²`.
* `CAPW.Aop`: `A_φ = T_φ^* T_φ` is compact, self-adjoint, has the same kernel as `T_φ`, and still
  commutes with all translations.  (Passing to `T_φ^* T_φ` is what avoids having to prove that
  `T_φ` itself is self-adjoint, which would require a Fubini theorem on `X × X` — unavailable
  here since `X` need not be second countable.)
* `CAPW.exists_eigenvector_moved`: if translation by `x` is not the identity on `H`, then some
  eigenvector of some `A_φ`, for a nonzero eigenvalue, is moved by `x`.  This uses the spectral
  theorem for compact self-adjoint operators, applied to the compression of `A_φ` to the
  orthogonal complement of the fixed space of `transl μ x`.
* `CAPW.exists_character`: the eigenspace is finite dimensional and translation invariant; a
  minimal nonzero invariant subspace `M` of it carries a common eigenvector for the commuting
  unitaries `transl μ a`, whose eigenvalues form the desired character.  Continuity of the
  character is read off from the continuous function `Lop φ v₀`.

(This file was written by Claude Opus 5.)
-/

/- A list of imports just for this file:
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.UrysohnsLemma
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace CAPW

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [CommGroup X] [IsTopologicalGroup X] [MeasurableSpace X] [BorelSpace X]


variable (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
  [μ.IsOpenPosMeasure] [μ.Regular]

/-- Translation by `a` acting on `L²(X, μ)`, as a linear isometry. -/
noncomputable def transl (a : X) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun z => a * z) (measurePreserving_mul_left μ a)

lemma coeFn_transl (a : X) (f : Lp ℂ 2 μ) :
    ⇑(transl μ a f) =ᵐ[μ] fun z => f (a * z) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_left μ a)

lemma transl_toLp (a : X) (g : C(X, ℂ)) :
    transl μ a (ContinuousMap.toLp 2 μ ℂ g) =
      ContinuousMap.toLp 2 μ ℂ (g.comp ⟨fun z => a * z, continuous_const.mul continuous_id⟩) := by
  rw [Lp.ext_iff]
  have h1 := coeFn_transl μ a (ContinuousMap.toLp 2 μ ℂ g)
  have h2 : (fun z => ((ContinuousMap.toLp 2 μ ℂ g : Lp ℂ 2 μ) : X → ℂ) (a * z))
      =ᵐ[μ] fun z => g (a * z) :=
    (measurePreserving_mul_left μ a).quasiMeasurePreserving.ae
      (ContinuousMap.coeFn_toLp (𝕜 := ℂ) μ g)
  have h3 := (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (E := ℂ) (p := 2) μ
      (g.comp ⟨fun z => a * z, continuous_const.mul continuous_id⟩))
  filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
  rw [hz1, hz2, hz3]
  rfl

lemma transl_one (f : Lp ℂ 2 μ) : transl μ (1 : X) f = f := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_transl μ 1 f] with z hz
  simpa using hz

lemma transl_transl (a b : X) (f : Lp ℂ 2 μ) :
    transl μ b (transl μ a f) = transl μ (a * b) f := by
  rw [Lp.ext_iff]
  have h1 := coeFn_transl μ b (transl μ a f)
  have h2 : (fun z => ((transl μ a f : Lp ℂ 2 μ) : X → ℂ) (b * z)) =ᵐ[μ] fun z => f (a * (b * z)) :=
    (measurePreserving_mul_left μ b).quasiMeasurePreserving.ae (coeFn_transl μ a f)
  have h3 := coeFn_transl μ (a * b) f
  filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
  rw [hz1, hz2, hz3, mul_assoc]

lemma inner_transl (a : X) (f g : Lp ℂ 2 μ) :
    inner ℂ (transl μ a f) g = inner ℂ f (transl μ a⁻¹ g) := by
  conv_lhs => rw [show g = transl μ a (transl μ a⁻¹ g) by
    rw [transl_transl, inv_mul_cancel, transl_one]]
  exact (transl μ a).inner_map_map _ _

/-! ### The smoothing operator -/

/-- `trMap φ y` is the translate `z ↦ φ (y⁻¹ * z)` of `φ`. -/
noncomputable def trMap (φ : C(X, ℂ)) : C(X, C(X, ℂ)) :=
  ContinuousMap.curry ⟨fun p : X × X => φ (p.1⁻¹ * p.2),
    φ.continuous.comp ((continuous_inv.comp continuous_fst).mul continuous_snd)⟩

@[simp] lemma trMap_apply (φ : C(X, ℂ)) (y z : X) : trMap φ y z = φ (y⁻¹ * z) := rfl

/-- The `L²`-valued family of translates of `φ`. -/
noncomputable def Fmap (φ : C(X, ℂ)) : C(X, Lp ℂ 2 μ) :=
  ⟨fun y => ContinuousMap.toLp 2 μ ℂ (trMap φ y),
    (ContinuousMap.toLp (E := ℂ) 2 μ ℂ).continuous.comp (trMap φ).continuous⟩

@[simp] lemma Fmap_apply (φ : C(X, ℂ)) (y : X) :
    Fmap μ φ y = ContinuousMap.toLp 2 μ ℂ (trMap φ y) := rfl

lemma Fmap_one (φ : C(X, ℂ)) : Fmap μ φ 1 = ContinuousMap.toLp 2 μ ℂ φ := by
  simp only [Fmap_apply]
  congr 1
  ext z
  simp

lemma transl_Fmap (φ : C(X, ℂ)) (a y : X) :
    transl μ a (Fmap μ φ y) = Fmap μ φ (a⁻¹ * y) := by
  simp only [Fmap_apply, transl_toLp]
  congr 1
  ext z
  simp [mul_assoc, mul_comm, mul_left_comm]

/-- The linear map `f ↦ (y ↦ ⟪Fmap φ y, f⟫)` from `L²` to `C(X, ℂ)`. -/
noncomputable def Lopₗ (φ : C(X, ℂ)) : Lp ℂ 2 μ →ₗ[ℂ] C(X, ℂ) where
  toFun f := ⟨fun y => inner ℂ (Fmap μ φ y) f,
    Continuous.inner (Fmap μ φ).continuous continuous_const⟩
  map_add' f g := by ext y; simp [inner_add_right]
  map_smul' c f := by ext y; simp [inner_smul_right]

/-- `Lop φ` as a continuous linear map. -/
noncomputable def Lop (φ : C(X, ℂ)) : Lp ℂ 2 μ →L[ℂ] C(X, ℂ) :=
  (Lopₗ μ φ).mkContinuous ‖Fmap μ φ‖ (fun f => by
    refine (ContinuousMap.norm_le _ (by positivity)).2 fun y => ?_
    calc ‖inner ℂ (Fmap μ φ y) f‖ ≤ ‖Fmap μ φ y‖ * ‖f‖ := norm_inner_le_norm _ _
      _ ≤ ‖Fmap μ φ‖ * ‖f‖ :=
          mul_le_mul_of_nonneg_right ((Fmap μ φ).norm_coe_le_norm y) (norm_nonneg f))

@[simp] lemma Lop_apply (φ : C(X, ℂ)) (f : Lp ℂ 2 μ) (y : X) :
    Lop μ φ f y = inner ℂ (Fmap μ φ y) f := rfl

/-- The smoothing operator `T_φ` on `L²(X, μ)`. -/
noncomputable def Top (φ : C(X, ℂ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (ContinuousMap.toLp (E := ℂ) 2 μ ℂ).comp (Lop μ φ)

lemma Top_apply (φ : C(X, ℂ)) (f : Lp ℂ 2 μ) :
    Top μ φ f = ContinuousMap.toLp 2 μ ℂ (Lop μ φ f) := rfl

/-- `T_φ` commutes with every translation. -/
lemma Top_transl (φ : C(X, ℂ)) (a : X) (f : Lp ℂ 2 μ) :
    Top μ φ (transl μ a f) = transl μ a (Top μ φ f) := by
  rw [Top_apply, Top_apply, transl_toLp]
  congr 1
  ext y
  simp only [Lop_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  have h := inner_transl μ a⁻¹ (Fmap μ φ y) f
  rw [inv_inv] at h
  rw [← h, transl_Fmap, inv_inv]


lemma toLp_eq_zero_iff (g : C(X, ℂ)) : ContinuousMap.toLp 2 μ ℂ g = 0 ↔ g = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have hz : ⇑(ContinuousMap.toLp (2 : ℝ≥0∞) μ ℂ g) =ᵐ[μ] (0 : X → ℂ) := by
    rw [h]; exact Lp.coeFn_zero ℂ 2 μ
  have h1 : (⇑g) =ᵐ[μ] (0 : X → ℂ) :=
    (ContinuousMap.coeFn_toLp (𝕜 := ℂ) μ g).symm.trans hz
  have := (g.continuous.ae_eq_iff_eq μ continuous_const).1 h1
  exact ContinuousMap.ext (congrFun this)

/-- The operators `T_φ` have trivial common kernel. -/
lemma eq_zero_of_forall_Top_eq_zero {f : Lp ℂ 2 μ} (h : ∀ φ : C(X, ℂ), Top μ φ f = 0) :
    f = 0 := by
  have key : ∀ φ : C(X, ℂ), inner ℂ (ContinuousMap.toLp 2 μ ℂ φ) f = (0 : ℂ) := by
    intro φ
    have h0 : Lop μ φ f = 0 := (toLp_eq_zero_iff μ _).1 (h φ)
    have h1 := congrFun (congrArg (fun (g : C(X, ℂ)) => ⇑g) h0) (1 : X)
    simp only [Lop_apply, ContinuousMap.coe_zero, Pi.zero_apply] at h1
    rwa [Fmap_one] at h1
  have hd : DenseRange (fun g : C(X, ℂ) => ContinuousMap.toLp (2 : ℝ≥0∞) μ ℂ g) :=
    ContinuousMap.toLp_denseRange (p := 2) ℂ μ ℂ (by simp)
  have hcont : Continuous fun v : Lp ℂ 2 μ => (inner ℂ v f : ℂ) :=
    Continuous.inner continuous_id continuous_const
  have heq : (fun v : Lp ℂ 2 μ => (inner ℂ v f : ℂ)) = fun _ => 0 :=
    hd.equalizer hcont continuous_const (funext key)
  have := congrFun heq f
  simpa [inner_self_eq_zero] using this

/-! ### Compactness of the smoothing operator -/

/-- `T_φ` is approximated in operator norm by finite-rank (hence compact) operators. -/
lemma exists_compactOperator_approx (φ : C(X, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ, IsCompactOperator ⇑S ∧ ‖Top μ φ - S‖ ≤ ε := by
  set C : ℝ := ‖(ContinuousMap.toLp (E := ℂ) (2 : ℝ≥0∞) μ ℂ : C(X, ℂ) →L[ℂ] Lp ℂ 2 μ)‖ with hCdef
  have hC0 : (0 : ℝ) ≤ C := norm_nonneg _
  set δ : ℝ := ε / (C + 1) with hδdef
  have hδ : 0 < δ := div_pos hε (by linarith)
  obtain ⟨t, ht, htsub⟩ :=
    Metric.totallyBounded_iff.1 (isCompact_range (Fmap μ φ).continuous).totallyBounded δ hδ
  have : FiniteDimensional ℂ (Submodule.span ℂ t) := FiniteDimensional.span_of_finite ℂ ht
  have hFP : ∀ y : X,
      ‖Fmap μ φ y - (Submodule.span ℂ t).starProjection (Fmap μ φ y)‖ ≤ δ := by
    intro y
    obtain ⟨v, hvt, hvd⟩ : ∃ v ∈ t, Fmap μ φ y ∈ Metric.ball v δ := by
      simpa using htsub (Set.mem_range_self y)
    have hvV : v ∈ Submodule.span ℂ t := Submodule.subset_span hvt
    rw [Submodule.starProjection_minimal]
    refine le_of_lt (lt_of_le_of_lt (ciInf_le ⟨0, ?_⟩ (⟨v, hvV⟩ : Submodule.span ℂ t)) ?_)
    · rintro r ⟨x, rfl⟩; exact norm_nonneg _
    · rw [← dist_eq_norm]; exact hvd
  refine ⟨(Top μ φ).comp (Submodule.span ℂ t).starProjection, ?_, ?_⟩
  · have : FiniteDimensional ℂ (Submodule.span ℂ (⇑(Top μ φ) '' t)) :=
      FiniteDimensional.span_of_finite ℂ (ht.image _)
    have hmem : ∀ f, ((Top μ φ).comp (Submodule.span ℂ t).starProjection) f ∈
        Submodule.span ℂ (⇑(Top μ φ) '' t) := by
      intro f
      have h1 : (Submodule.span ℂ t).starProjection f ∈ Submodule.span ℂ t := by
        simp only [Submodule.starProjection_apply]; exact SetLike.coe_mem _
      have h2 := Submodule.mem_map_of_mem
        (f := (Top μ φ : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ)) h1
      rw [Submodule.map_span] at h2
      simpa using h2
    exact (isCompactOperator_of_locallyCompactSpace_dom
      (((Top μ φ).comp (Submodule.span ℂ t).starProjection).codRestrict _ hmem)).clm_comp
        (Submodule.span ℂ (⇑(Top μ φ) '' t)).subtypeL
  · refine ContinuousLinearMap.opNorm_le_bound _ hε.le fun f => ?_
    have hsub : (Top μ φ - (Top μ φ).comp (Submodule.span ℂ t).starProjection) f =
        Top μ φ (f - (Submodule.span ℂ t).starProjection f) := by
      simp [map_sub]
    have hLop : ‖Lop μ φ (f - (Submodule.span ℂ t).starProjection f)‖ ≤ δ * ‖f‖ := by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun y => ?_
      have hy : (Lop μ φ (f - (Submodule.span ℂ t).starProjection f)) y =
          inner ℂ (Fmap μ φ y - (Submodule.span ℂ t).starProjection (Fmap μ φ y)) f := by
        simp only [Lop_apply]
        rw [inner_sub_right, inner_sub_left,
          Submodule.inner_starProjection_left_eq_right]
      rw [hy]
      exact le_trans (norm_inner_le_norm _ _)
        (mul_le_mul_of_nonneg_right (hFP y) (norm_nonneg f))
    rw [hsub, Top_apply]
    calc ‖ContinuousMap.toLp (2 : ℝ≥0∞) μ ℂ (Lop μ φ (f - (Submodule.span ℂ t).starProjection f))‖
        ≤ C * ‖Lop μ φ (f - (Submodule.span ℂ t).starProjection f)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * (δ * ‖f‖) := by
          exact mul_le_mul_of_nonneg_left hLop hC0
      _ ≤ ε * ‖f‖ := by
          rw [← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg f)
          rw [hδdef, mul_div_assoc']
          rw [div_le_iff₀ (by linarith)]
          nlinarith

/-- `T_φ` is a compact operator. -/
lemma Top_isCompactOperator (φ : C(X, ℂ)) : IsCompactOperator ⇑(Top μ φ) := by
  choose S hS1 hS2 using fun n : ℕ =>
    exists_compactOperator_approx μ φ (ε := 1 / (n + 1)) (by positivity)
  refine isCompactOperator_of_tendsto (l := atTop) (F := S) ?_ (.of_forall hS1)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  rw [norm_sub_rev]
  exact hS2 n

/-! ### The associated positive compact operator -/

/-- `A_φ = T_φ^* T_φ`: a compact, self-adjoint operator commuting with all translations. -/
noncomputable def Aop (φ : C(X, ℂ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (ContinuousLinearMap.adjoint (Top μ φ)).comp (Top μ φ)

lemma Aop_isCompactOperator (φ : C(X, ℂ)) : IsCompactOperator ⇑(Aop μ φ) := by
  have h := (Top_isCompactOperator μ φ).clm_comp (ContinuousLinearMap.adjoint (Top μ φ))
  simpa [Aop, ContinuousLinearMap.coe_comp] using h

lemma Aop_isSymmetric (φ : C(X, ℂ)) :
    ((Aop μ φ : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ).IsSymmetric := by
  intro u v
  simp only [Aop, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]

lemma Top_eq_zero_of_Aop_eq_zero (φ : C(X, ℂ)) {v : Lp ℂ 2 μ} (h : Aop μ φ v = 0) :
    Top μ φ v = 0 := by
  have h2 : (inner ℂ (Top μ φ v) (Top μ φ v) : ℂ) = inner ℂ (Aop μ φ v) v :=
    (ContinuousLinearMap.adjoint_inner_left (Top μ φ) v (Top μ φ v)).symm
  rw [h, inner_zero_left] at h2
  exact inner_self_eq_zero.1 h2

lemma adjoint_Top_transl (φ : C(X, ℂ)) (a : X) (u : Lp ℂ 2 μ) :
    ContinuousLinearMap.adjoint (Top μ φ) (transl μ a u) =
      transl μ a (ContinuousLinearMap.adjoint (Top μ φ) u) := by
  refine ext_inner_right ℂ fun v => ?_
  have e1 := ContinuousLinearMap.adjoint_inner_left (Top μ φ) v (transl μ a u)
  have e2 := inner_transl μ a u (Top μ φ v)
  have e3 := Top_transl μ φ a⁻¹ v
  have e4 := ContinuousLinearMap.adjoint_inner_left (Top μ φ) (transl μ a⁻¹ v) u
  have e5 := inner_transl μ a (ContinuousLinearMap.adjoint (Top μ φ) u) v
  rw [e1, e2, ← e3, ← e4, ← e5]

lemma Aop_transl (φ : C(X, ℂ)) (a : X) (u : Lp ℂ 2 μ) :
    Aop μ φ (transl μ a u) = transl μ a (Aop μ φ u) := by
  simp only [Aop, ContinuousLinearMap.comp_apply]
  rw [Top_transl, adjoint_Top_transl]

/-! ### Finding an eigenvector that is moved by `x` -/

/-- If translation by `x` is not the identity on `L²`, then some eigenvector of some `A_φ`,
for a nonzero eigenvalue, is moved by translation by `x`. -/
theorem exists_eigenvector_moved {x : X} (hx : ∃ f : Lp ℂ 2 μ, transl μ x f ≠ f) :
    ∃ (φ : C(X, ℂ)) (c : ℂ) (v : Lp ℂ 2 μ),
      c ≠ 0 ∧ Aop μ φ v = c • v ∧ transl μ x v ≠ v := by
  by_contra hcon
  push Not at hcon
  set N : Submodule ℂ (Lp ℂ 2 μ) :=
    LinearMap.ker ((transl μ x).toLinearMap - LinearMap.id) with hNdef
  have hNmem : ∀ f : Lp ℂ 2 μ, f ∈ N ↔ transl μ x f = f := by
    intro f
    simp [hNdef, LinearMap.mem_ker, sub_eq_zero]
  have hNclosed : IsClosed (N : Set (Lp ℂ 2 μ)) := by
    have hset : (N : Set (Lp ℂ 2 μ)) = {f | transl μ x f = f} := by
      ext f; simpa using hNmem f
    rw [hset]
    exact isClosed_eq (transl μ x).continuous continuous_id
  have : CompleteSpace N := hNclosed.completeSpace_coe
  -- `N` is invariant under every `A_φ`
  have hAN : ∀ (φ : C(X, ℂ)) (u : Lp ℂ 2 μ), u ∈ N → Aop μ φ u ∈ N := by
    intro φ u hu
    rw [hNmem] at hu ⊢
    rw [← Aop_transl, hu]
  -- hence so is `Nᗮ`
  have hAK : ∀ (φ : C(X, ℂ)) (v : Lp ℂ 2 μ), v ∈ Nᗮ → Aop μ φ v ∈ Nᗮ := by
    intro φ v hv
    rw [Submodule.mem_orthogonal] at hv ⊢
    intro u hu
    have hsym : (inner ℂ (Aop μ φ u) v : ℂ) = inner ℂ u (Aop μ φ v) := Aop_isSymmetric μ φ u v
    rw [← hsym]
    exact hv _ (hAN φ u hu)
  have hNoo : Nᗮᗮ = N := Submodule.orthogonal_orthogonal N
  -- the orthogonal projection onto `Nᗮ` commutes with `A_φ`
  have hQA : ∀ (φ : C(X, ℂ)) (v : Lp ℂ 2 μ),
      Nᗮ.starProjection (Aop μ φ v) = Aop μ φ (Nᗮ.starProjection v) := by
    intro φ v
    have h1 : Aop μ φ (Nᗮ.starProjection v) ∈ Nᗮ :=
      hAK φ _ (Submodule.starProjection_apply_mem _ _)
    have h2 : v - Nᗮ.starProjection v ∈ N := by
      have h2' := Submodule.sub_starProjection_mem_orthogonal (K := Nᗮ) v
      rwa [hNoo] at h2'
    have h3 : Aop μ φ (v - Nᗮ.starProjection v) ∈ Nᗮᗮ := by
      rw [hNoo]; exact hAN φ _ h2
    have h4 : Nᗮ.starProjection (Aop μ φ (v - Nᗮ.starProjection v)) = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff Nᗮ).2 h3
    have h5 : Aop μ φ v =
        Aop μ φ (Nᗮ.starProjection v) + Aop μ φ (v - Nᗮ.starProjection v) := by
      rw [← map_add]; congr 1; abel
    rw [h5, map_add, h4, add_zero, Submodule.starProjection_eq_self_iff.2 h1]
  -- the compressed operator has no nonzero eigenvalue, hence vanishes
  have hzero : ∀ (φ : C(X, ℂ)) (v : Lp ℂ 2 μ), v ∈ Nᗮ → Aop μ φ v = 0 := by
    intro φ
    set B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := (Aop μ φ).comp Nᗮ.starProjection with hB
    have hBcpt : IsCompactOperator ⇑B := (Aop_isCompactOperator μ φ).comp_clm _
    have hBsym : ((B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ).IsSymmetric := by
      intro u v
      simp only [hB, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
      have s1 : (inner ℂ (Aop μ φ (Nᗮ.starProjection u)) v : ℂ)
          = inner ℂ (Nᗮ.starProjection u) (Aop μ φ v) := Aop_isSymmetric μ φ _ _
      have s2 : (inner ℂ (Nᗮ.starProjection u) (Aop μ φ v) : ℂ)
          = inner ℂ u (Nᗮ.starProjection (Aop μ φ v)) :=
        Submodule.inner_starProjection_left_eq_right Nᗮ u (Aop μ φ v)
      rw [s1, s2, hQA]
    have hBeig : ∀ c : ℂ, Module.End.HasEigenvalue
        ((B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) c → c = 0 := by
      intro c hc
      by_contra hc0
      obtain ⟨v, hv, hv0⟩ := hc.exists_hasEigenvector
      rw [Module.End.mem_eigenspace_iff] at hv
      have hvK : v ∈ Nᗮ := by
        have : v = c⁻¹ • (Aop μ φ (Nᗮ.starProjection v)) := by
          rw [← show B v = Aop μ φ (Nᗮ.starProjection v) from rfl]
          simp only [ContinuousLinearMap.coe_coe] at hv
          rw [hv, smul_smul, inv_mul_cancel₀ hc0, one_smul]
        rw [this]
        exact Submodule.smul_mem _ _ (hAK φ _ (Submodule.starProjection_apply_mem _ _))
      have hQv : Nᗮ.starProjection v = v := Submodule.starProjection_eq_self_iff.2 hvK
      have hAv : Aop μ φ v = c • v := by
        have : B v = c • v := by simpa using hv
        rwa [hB, ContinuousLinearMap.comp_apply, hQv] at this
      have hfix : transl μ x v = v := hcon φ c v hc0 hAv
      have : v ∈ N ⊓ Nᗮ := ⟨(hNmem v).2 hfix, hvK⟩
      rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at this
      exact hv0 this
    have hB0 : B = 0 :=
      (ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hBcpt hBsym).1 hBeig
    intro v hv
    have hQv : Nᗮ.starProjection v = v := Submodule.starProjection_eq_self_iff.2 hv
    have : B v = 0 := by rw [hB0]; rfl
    rwa [hB, ContinuousLinearMap.comp_apply, hQv] at this
  -- so `Nᗮ` is trivial and `N = ⊤`
  have hKbot : Nᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    exact eq_zero_of_forall_Top_eq_zero μ fun φ =>
      Top_eq_zero_of_Aop_eq_zero μ φ (hzero φ v hv)
  have hNtop : N = ⊤ := Submodule.orthogonal_eq_bot_iff.1 hKbot
  obtain ⟨f, hf⟩ := hx
  exact hf ((hNmem f).1 (by rw [hNtop]; trivial))

/-! ### Construction of the character -/

lemma exists_transl_ne {x : X} (hx : x ≠ 1) : ∃ f : Lp ℂ 2 μ, transl μ x f ≠ f := by
  obtain ⟨g, hg0, hg1, -⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_singleton (x := (1 : X))) (isClosed_singleton (x := x))
    (Set.disjoint_singleton.2 (Ne.symm hx))
  set gC : C(X, ℂ) := ⟨fun z => (g z : ℂ), Complex.continuous_ofReal.comp g.continuous⟩ with hgC
  refine ⟨ContinuousMap.toLp 2 μ ℂ gC, fun hEq => ?_⟩
  rw [transl_toLp] at hEq
  have h0 : ContinuousMap.toLp (2 : ℝ≥0∞) μ ℂ
      ((gC.comp ⟨fun z => x * z, continuous_const.mul continuous_id⟩) - gC) = 0 := by
    rw [map_sub, hEq, sub_self]
  have hAB := sub_eq_zero.1 ((toLp_eq_zero_iff μ _).1 h0)
  have h1 := congrFun (congrArg (fun (h : C(X, ℂ)) => ⇑h) hAB) (1 : X)
  have hgx : g x = 1 := by simpa using hg1 (Set.mem_singleton x)
  have hg1' : g 1 = 0 := by simpa using hg0 (Set.mem_singleton (1 : X))
  simp only [hgC, ContinuousMap.comp_apply, ContinuousMap.coe_mk, mul_one] at h1
  rw [hgx, hg1'] at h1
  norm_num at h1

include μ in
/-- **Peter–Weyl for compact abelian groups**, analytic core: a point `x ≠ 1` of a compact
Hausdorff abelian group is detected by a continuous unimodular character. -/
theorem exists_character {x : X} (hx : x ≠ 1) :
    ∃ χ : X → ℂ, Continuous χ ∧ χ 1 = 1 ∧ (∀ a b, χ (a * b) = χ a * χ b) ∧
      (∀ a, ‖χ a‖ = 1) ∧ χ x ≠ 1 := by
  obtain ⟨φ, c, v, hc0, hAv, hxv⟩ := exists_eigenvector_moved μ (exists_transl_ne μ hx)
  set E : Submodule ℂ (Lp ℂ 2 μ) :=
    Module.End.eigenspace ((Aop μ φ : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
      Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) c with hE
  have hmemE : ∀ w : Lp ℂ 2 μ, w ∈ E ↔ Aop μ φ w = c • w := by
    intro w; rw [hE]; exact Module.End.mem_eigenspace_iff
  have hEfd : FiniteDimensional ℂ E :=
    ContinuousLinearMap.finite_dimensional_eigenspace (Aop_isCompactOperator μ φ) c hc0
  have hEinv : ∀ (a : X) (w : Lp ℂ 2 μ), w ∈ E → transl μ a w ∈ E := by
    intro a w hw
    rw [hmemE] at hw ⊢
    rw [Aop_transl, hw, map_smul]
  set Nx : Submodule ℂ (Lp ℂ 2 μ) :=
    LinearMap.ker ((transl μ x).toLinearMap - LinearMap.id) with hNx
  have hmemN : ∀ f : Lp ℂ 2 μ, f ∈ Nx ↔ transl μ x f = f := by
    intro f; simp [hNx, LinearMap.mem_ker, sub_eq_zero]
  have hNinv : ∀ (a : X) (w : Lp ℂ 2 μ), w ∈ Nx → transl μ a w ∈ Nx := by
    intro a w hw
    rw [hmemN] at hw ⊢
    rw [transl_transl, mul_comm, ← transl_transl, hw]
  set F : Submodule ℂ (Lp ℂ 2 μ) := Nx ⊓ E with hF
  have hFE : F ≤ E := inf_le_right
  have : FiniteDimensional ℂ F := Submodule.finiteDimensional_of_le hFE
  have hFinv : ∀ (a : X) (w : Lp ℂ 2 μ), w ∈ F → transl μ a w ∈ F := fun a w hw =>
    Submodule.mem_inf.2 ⟨hNinv a w (Submodule.mem_inf.1 hw).1,
      hEinv a w (Submodule.mem_inf.1 hw).2⟩
  set E' : Submodule ℂ (Lp ℂ 2 μ) := Fᗮ ⊓ E with hE'
  have hsup : F ⊔ E' = E := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hFE
  have hE'ne : E' ≠ ⊥ := by
    intro h
    rw [h, sup_bot_eq] at hsup
    have hvE : v ∈ E := (hmemE v).2 hAv
    rw [← hsup] at hvE
    exact hxv ((hmemN v).1 (Submodule.mem_inf.1 hvE).1)
  have hE'inv : ∀ (a : X) (w : Lp ℂ 2 μ), w ∈ E' → transl μ a w ∈ E' := by
    intro a w hw
    refine Submodule.mem_inf.2 ⟨?_, hEinv a w (Submodule.mem_inf.1 hw).2⟩
    rw [Submodule.mem_orthogonal]
    intro u hu
    have h2 := (Submodule.mem_orthogonal F w).1 (Submodule.mem_inf.1 hw).1 _ (hFinv a⁻¹ u hu)
    rw [inner_transl, inv_inv] at h2
    exact h2
  -- a minimal nonzero translation-invariant subspace of `E'`
  set 𝒮 : Set (Submodule ℂ (Lp ℂ 2 μ)) :=
    {M | M ≤ E' ∧ M ≠ ⊥ ∧ ∀ (a : X) (w : Lp ℂ 2 μ), w ∈ M → transl μ a w ∈ M} with h𝒮
  have hE'mem : E' ∈ 𝒮 := ⟨le_refl _, hE'ne, hE'inv⟩
  have hnonempty : ((fun M : Submodule ℂ (Lp ℂ 2 μ) => Module.finrank ℂ M) '' 𝒮).Nonempty :=
    ⟨_, E', hE'mem, rfl⟩
  obtain ⟨M, hM𝒮, hMrank⟩ := Nat.sInf_mem hnonempty
  have hMmin : ∀ M' ∈ 𝒮, Module.finrank ℂ M ≤ Module.finrank ℂ M' := by
    intro M' hM'
    have h1 : Module.finrank ℂ M =
        sInf ((fun M : Submodule ℂ (Lp ℂ 2 μ) => Module.finrank ℂ M) '' 𝒮) := hMrank
    rw [h1]
    exact Nat.sInf_le ⟨M', hM', rfl⟩
  have hMfd : FiniteDimensional ℂ M :=
    Submodule.finiteDimensional_of_le (le_trans hM𝒮.1 (inf_le_right : E' ≤ E))
  have hMnt : Nontrivial M := Submodule.nontrivial_iff_ne_bot.2 hM𝒮.2.1
  -- every translation acts on `M` by a scalar
  have hscal : ∀ a : X, ∃ ca : ℂ, ∀ w ∈ M, transl μ a w = ca • w := by
    intro a
    have hinv : ∀ w ∈ M, (transl μ a).toLinearMap w ∈ M := fun w hw => hM𝒮.2.2 a w hw
    obtain ⟨ca, hca⟩ := Module.End.exists_eigenvalue
      (LinearMap.restrict (transl μ a).toLinearMap hinv)
    obtain ⟨w, hw, hw0⟩ := hca.exists_hasEigenvector
    rw [Module.End.mem_eigenspace_iff] at hw
    have hwM : (w : Lp ℂ 2 μ) ∈ M := w.2
    have hwe : transl μ a (w : Lp ℂ 2 μ) = ca • (w : Lp ℂ 2 μ) := by
      have h := congrArg (Subtype.val) hw
      simpa [LinearMap.restrict_apply] using h
    have hw0' : (w : Lp ℂ 2 μ) ≠ 0 := by simpa using hw0
    refine ⟨ca, ?_⟩
    set Ma : Submodule ℂ (Lp ℂ 2 μ) :=
      M ⊓ LinearMap.ker ((transl μ a).toLinearMap - ca • LinearMap.id) with hMa
    have hMamem : ∀ u : Lp ℂ 2 μ, u ∈ Ma ↔ (u ∈ M ∧ transl μ a u = ca • u) := by
      intro u; simp [hMa, LinearMap.mem_ker, sub_eq_zero]
    have hMane : Ma ≠ ⊥ := by
      intro h
      rw [Submodule.eq_bot_iff] at h
      exact hw0' (h _ ((hMamem _).2 ⟨hwM, hwe⟩))
    have hMainv : ∀ (b : X) (u : Lp ℂ 2 μ), u ∈ Ma → transl μ b u ∈ Ma := by
      intro b u hu
      rw [hMamem] at hu ⊢
      refine ⟨hM𝒮.2.2 b u hu.1, ?_⟩
      rw [transl_transl, mul_comm, ← transl_transl, hu.2, map_smul]
    have hMa𝒮 : Ma ∈ 𝒮 := ⟨le_trans inf_le_left hM𝒮.1, hMane, hMainv⟩
    have hMaM : Ma = M := by
      by_contra hne'
      have hlt : Ma < M := lt_of_le_of_ne inf_le_left hne'
      have hrk := Submodule.finrank_lt_finrank_of_lt hlt
      have := hMmin Ma hMa𝒮
      omega
    intro w' hw'
    rw [← hMaM] at hw'
    exact ((hMamem w').1 hw').2
  choose χ hχ using hscal
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : M)
  set v₀ : Lp ℂ 2 μ := (w₀ : Lp ℂ 2 μ) with hv₀def
  have hv₀M : v₀ ∈ M := w₀.2
  have hv₀0 : v₀ ≠ 0 := by simpa [hv₀def] using hw₀
  have hmul : ∀ a b, χ (a * b) = χ a * χ b := by
    intro a b
    have h1 : transl μ (a * b) v₀ = χ (a * b) • v₀ := hχ (a * b) v₀ hv₀M
    have h2 : transl μ (a * b) v₀ = (χ a * χ b) • v₀ := by
      rw [← transl_transl, hχ a v₀ hv₀M, map_smul, hχ b v₀ hv₀M, smul_smul]
    have h3 : (χ (a * b) - χ a * χ b) • v₀ = 0 := by rw [sub_smul, ← h1, h2, sub_self]
    rcases smul_eq_zero.1 h3 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hv₀0
  have hnorm : ∀ a, ‖χ a‖ = 1 := by
    intro a
    have h1 : ‖transl μ a v₀‖ = ‖v₀‖ := (transl μ a).norm_map v₀
    rw [hχ a v₀ hv₀M, norm_smul] at h1
    exact mul_right_cancel₀ (norm_ne_zero_iff.2 hv₀0) (by rw [one_mul]; exact h1)
  have hone : χ 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    have hne0 : χ 1 ≠ 0 := norm_ne_zero_iff.1 (by rw [hnorm 1]; norm_num)
    exact (mul_left_cancel₀ hne0 (by rw [mul_one]; exact h)).symm
  have hxne : χ x ≠ 1 := by
    intro h
    have hMF : M ≤ F := by
      intro w hw
      exact Submodule.mem_inf.2 ⟨(hmemN w).2 (by rw [hχ x w hw, h, one_smul]),
        (Submodule.mem_inf.1 (hM𝒮.1 hw)).2⟩
    have hMbot : M ≤ F ⊓ Fᗮ :=
      le_inf hMF (fun w hw => (Submodule.mem_inf.1 (hM𝒮.1 hw)).1)
    rw [Submodule.inf_orthogonal_eq_bot, le_bot_iff] at hMbot
    exact hM𝒮.2.1 hMbot
  -- continuity, via the continuous function `Lop φ v₀`
  have hv₀E : v₀ ∈ E := (Submodule.mem_inf.1 (hM𝒮.1 hv₀M)).2
  have hTv : Top μ φ v₀ ≠ 0 := by
    intro h0
    have hz : Aop μ φ v₀ = 0 := by
      simp only [Aop, ContinuousLinearMap.comp_apply, h0, map_zero]
    have hEv : Aop μ φ v₀ = c • v₀ := (hmemE v₀).1 hv₀E
    rw [hz] at hEv
    rcases smul_eq_zero.1 hEv.symm with h | h
    · exact hc0 h
    · exact hv₀0 h
  have hLne : Lop μ φ v₀ ≠ 0 := fun h0 => hTv (by rw [Top_apply, h0, map_zero])
  obtain ⟨y₀, hy₀⟩ : ∃ y : X, (Lop μ φ v₀) y ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hLne (ContinuousMap.ext fun y => by simp [hall y])
  have hkey : ∀ a y : X, (Lop μ φ v₀) (a * y) = χ a * (Lop μ φ v₀) y := by
    intro a y
    have e2 : Fmap μ φ (a * y) = transl μ a⁻¹ (Fmap μ φ y) := by
      rw [transl_Fmap, inv_inv]
    have e3 : (inner ℂ (transl μ a⁻¹ (Fmap μ φ y)) v₀ : ℂ)
        = inner ℂ (Fmap μ φ y) (transl μ a v₀) := by
      rw [inner_transl, inv_inv]
    rw [Lop_apply, Lop_apply, e2, e3, hχ a v₀ hv₀M, inner_smul_right]
  have hcont : Continuous χ := by
    have hform : χ = fun a => (Lop μ φ v₀) (a * y₀) / (Lop μ φ v₀) y₀ := by
      funext a
      rw [hkey a y₀, mul_div_assoc, div_self hy₀, mul_one]
    rw [hform]
    exact ((Lop μ φ v₀).continuous.comp (continuous_id.mul continuous_const)).div_const _
  exact ⟨χ, hcont, hone, hmul, hnorm, hxne⟩

end CAPW

open MeasureTheory in
theorem PontryaginDual.exists_apply_ne_one
    {X : Type*}
    [TopologicalSpace X]
    [CompactSpace X]
    [T2Space X]
    [CommGroup X]
    [IsTopologicalGroup X]
    {x : X}
    (hx : x ≠ 1) :
    ∃ χ : PontryaginDual X, χ x ≠ 1 := by
  borelize X
  set K₀ : TopologicalSpace.PositiveCompacts X := ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ with hK₀
  set μ : Measure X := Measure.haarMeasure K₀ with hμ
  have : IsProbabilityMeasure μ :=
    ⟨by simpa [hK₀] using (Measure.haarMeasure_self (K₀ := K₀))⟩
  have : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure K₀
  obtain ⟨χ, hcont, hone, hmul, hnorm, hne⟩ := CAPW.exists_character μ hx
  refine ⟨({ toFun := fun a => (⟨χ a, mem_sphere_zero_iff_norm.2 (hnorm a)⟩ : Circle)
             map_one' := Circle.ext hone
             map_mul' := fun a b => Circle.ext (hmul a b)
             continuous_toFun := Continuous.subtype_mk hcont _ } :
      ContinuousMonoidHom X Circle), fun h => hne ?_⟩
  exact congrArg (fun z : Circle => (z : ℂ)) h
