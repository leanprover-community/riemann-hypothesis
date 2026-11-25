module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwistIntersection
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.PenHost
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSmoothWeightConstNearEmbeddings
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionLocConstTrivial
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionNumberMetricChange
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.MetricLocal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UnitRatioDivisorSupportEq
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PBoundedSectionTransfer
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsConjInvariant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegrableOfResolutionStatement
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingPieces
import Development.WeilBound.CoreStatements.FlagImmersions.PointsIntegralSectionSnoc
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.LengthLocQuotEqZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatementStatement
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPiecesAdditive

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicSpectrum.Proofs.AdelicProofs.UnitLogOrthogonalWeightConstant, Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralZeroOfLocallyConstant, Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralIndependentOfMetric, Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralConjugationSymmetry, Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralUniqueEmbedding, Development.AutomorphicSpectrum.Proofs.MetricProofs.SumOverEmbeddingsUnitInvariance, Development.AutomorphicSpectrum.Proofs.MetricProofs.PieceDegreeOfIntersectionAndResolution, Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddingPiecesOfIntersectionAndResolution

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.AdelicProofs.UnitLogOrthogonalWeightConstant =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.AdelicProofs.UnitLogOrthogonalWeightConstant", "h": "module\n\npublic import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings\nimport Mathlib.Algebra.Order.Archimedean.Real.Hom\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\npublic import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic\npublic import Mathlib.NumberTheory.NumberField.Units.Basic\n\n"}
section -- clump:auto
@[expose] public section

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

open NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem in
theorem const_of_orthogonal_log_units : ∀ (F : Type) [Field F] [NumberField F] (m : (F →+* ℂ) → ℝ),
    (∀ sg, m (ComplexEmbedding.conjugate sg) = m sg) →
    (∀ θ : (𝓞 F)ˣ, ∑ sg : F →+* ℂ, Real.log ‖sg ((θ : 𝓞 F) : F)‖ * m sg = 0) →
    ∀ sg sg', m sg = m sg' := by
  open NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem in
  intro F _ _ m hconj horth
  classical

  have hdesc : ∀ sg sg' : F →+* ℂ, InfinitePlace.mk sg = InfinitePlace.mk sg' → m sg = m sg' := by
    intro sg sg' h
    rcases InfinitePlace.mk_eq_iff.mp h with h | h
    · rw [h]
    · rw [← h, hconj]
  set mw : InfinitePlace F → ℝ := fun w => m w.embedding with hmw
  have hmk : ∀ sg : F →+* ℂ, m sg = mw (InfinitePlace.mk sg) := by
    intro sg
    exact hdesc _ _ (by simp [InfinitePlace.mk_embedding])

  have hplace : ∀ θ : (𝓞 F)ˣ,
      ∑ w : InfinitePlace F, (mult w : ℝ) * Real.log (w ((θ : 𝓞 F) : F)) * mw w = 0 := by
    intro θ
    rw [← horth θ, ← Finset.sum_fiberwise Finset.univ (fun sg : F →+* ℂ => InfinitePlace.mk sg)]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hfib : ∀ sg ∈ Finset.univ.filter (fun sg : F →+* ℂ => InfinitePlace.mk sg = w),
        Real.log ‖sg ((θ : 𝓞 F) : F)‖ * m sg = Real.log (w ((θ : 𝓞 F) : F)) * mw w := by
      intro sg hsg
      have hsg' : InfinitePlace.mk sg = w := (Finset.mem_filter.mp hsg).2
      rw [hmk sg, hsg', ← hsg', InfinitePlace.apply]
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul,
      mul_assoc]

  let L : logSpace F →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ w, x w * (mw w.1 - mw w₀)
      map_add' := fun x y => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.mul_sum, mul_assoc] }
  have hLunit : ∀ θ : (𝓞 F)ˣ, L (logEmbedding F (Additive.ofMul θ)) = 0 := by
    intro θ
    have h1 : ∑ w : InfinitePlace F, (mult w : ℝ) * Real.log (w ((θ : 𝓞 F) : F)) = 0 := by
      exact_mod_cast sum_mult_mul_log θ
    have h2 : ∑ w : InfinitePlace F,
        (mult w : ℝ) * Real.log (w ((θ : 𝓞 F) : F)) * (mw w - mw w₀) = 0 := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, hplace θ, ← Finset.sum_mul, h1]
      simp
    rw [Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace F)] at h2
    simpa [L, logEmbedding_component] using h2
  have hL : L = 0 := by
    refine LinearMap.ext fun x => ?_
    have hx : x ∈ Submodule.span ℝ (unitLattice F : Set (logSpace F)) := by
      rw [unitLattice_span_eq_top]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, -, rfl⟩ := hy
      exact hLunit (Additive.toMul a)
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul c y _ hy => simp [hy]
  have hconst : ∀ w : InfinitePlace F, mw w = mw w₀ := by
    intro w
    by_cases hw : w = w₀
    · rw [hw]
    · have := LinearMap.congr_fun hL (Pi.single ⟨w, hw⟩ 1)
      have h3 : mw w - mw w₀ = 0 := by
        simpa [L, Pi.single_apply, Finset.sum_ite_eq] using this
      linarith
  intro sg sg'
  rw [hmk sg, hmk sg', hconst (InfinitePlace.mk sg), hconst (InfinitePlace.mk sg')]

end GlobalTheory.CompanionTheory.Ar.Giv
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.AdelicProofs.UnitLogOrthogonalWeightConstant =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralZeroOfLocallyConstant =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralZeroOfLocallyConstant", "h": "module\n\nimport Development.WeilBound.CoreStatements.FlagImmersions.PointsIntegralSectionSnoc\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily\npublic import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwistIntersection\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs\n\n"}
section -- clump:auto
@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem cxHessian_zero {D : ℕ} (z : Fin D → ℂ) : cxHessian (fun _ => (0 : ℝ)) z = 0 := by
  have h : fderiv ℝ (fderiv ℝ (fun _ : Fin D → ℂ => (0 : ℝ))) z = 0 := by
    have h1 : fderiv ℝ (fun _ : Fin D → ℂ => (0 : ℝ)) = fun _ => 0 := by
      funext x
      exact fderiv_const_apply 0
    rw [h1]
    exact fderiv_const_apply 0
  ext a b
  simp [cxHessian]

theorem sheetDensity_update_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (j : Fin e)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ (Function.update φ j 0) g y w = 0 := by
  unfold sheetDensity
  split_ifs with hγ
  · have hm : mixedDisc (fun k => cxHessian
        (fun y' => Function.update φ j 0 k (hγ.choose y')) y) = 0 := by
      refine RootFieldNumerics.mixedDisc_eq_zero _ j ?_
      simpa using cxHessian_zero y
    simp [maDensity, hm]
  · rfl

theorem ptsIntegral_eq_zero_of_locConst :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
      (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (j : Fin e),
      (∀ z ∈ mcPts P, ∃ c : ℝ, φ j =ᶠ[𝓝 z] fun _ => c) → ptsIntegral P φ g = 0 := by
  intro K _ ι _ P e φ g j hj
  have hshift : ∀ i, ∀ z ∈ mcPts P, ∃ c : ℝ,
      ∀ᶠ u in 𝓝 z, φ i u = Function.update φ j 0 i u + c := by
    intro i z hz
    by_cases hi : i = j
    · subst hi
      obtain ⟨c, hc⟩ := hj z hz
      refine ⟨c, hc.mono fun u hu => ?_⟩
      simpa using hu
    · exact ⟨0, Eventually.of_forall fun u => by simp [Function.update_of_ne hi]⟩
  rw [GroundTheory.Heights₂.Heights.HilbertSamuel.TwistIntersection.ptsIntegral_add_locConst P hshift g]
  unfold ptsIntegral
  split_ifs
  · simp [ptsIntegralAt, sheetDensity_update_zero]
  · rfl

end GlobalTheory.CompanionTheory.Ar.Giv
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralZeroOfLocallyConstant =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralIndependentOfMetric =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralIndependentOfMetric", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.PenHost\npublic import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSmoothWeightConstNearEmbeddings\npublic import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionLocConstTrivial\npublic import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionNumberMetricChange\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily\npublic import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralZeroOfLocallyConstant\npublic import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.MetricLocal\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

section FactorChange

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem snoc_update_comp_swap {D : ℕ} (W : Fin D → HermLine ι) (m : Fin D) (X B : HermLine ι) :
    (Fin.snoc (Function.update W m X) B : Fin (D + 1) → HermLine ι) ∘
        Equiv.swap m.castSucc (Fin.last D) =
      Fin.snoc (Function.update W m B) X := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Function.comp_apply, Equiv.swap_apply_right, Fin.snoc_castSucc, Function.update_self, Fin.snoc_last]
  · by_cases hi : i = m
    · subst hi
      rw [Function.comp_apply, Equiv.swap_apply_left, Fin.snoc_last, Fin.snoc_castSucc, Function.update_self]
    · have h1 : i.castSucc ≠ m.castSucc := fun h => hi (Fin.castSucc_injective _ h)
      have h2 : i.castSucc ≠ Fin.last D := (Fin.castSucc_lt_last i).ne
      rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.snoc_castSucc, Fin.snoc_castSucc,
        Function.update_of_ne hi, Function.update_of_ne hi]

theorem smooth_update {D : ℕ} {W : Fin D → HermLine ι} (hW : ∀ j, IsSmoothHerm (W j)) (m : Fin D)
    {X : HermLine ι} (hX : IsSmoothHerm X) (j : Fin D) : IsSmoothHerm (Function.update W m X j) := by
  by_cases hj : j = m
  · subst hj
    simpa using hX
  · simpa [Function.update_of_ne hj] using hW j

theorem smooth_snoc {D : ℕ} {W : Fin D → HermLine ι} (hW : ∀ j, IsSmoothHerm (W j)) {X : HermLine ι}
    (hX : IsSmoothHerm X) (j : Fin (D + 1)) :
    IsSmoothHerm ((Fin.snoc W X : Fin (D + 1) → HermLine ι) j) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Fin.snoc_last]
    exact hX
  · rw [Fin.snoc_castSucc]
    exact hW i

theorem position_change (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) (P : Ideal (MRing ι)) {D : ℕ} (hP : IsArithVar P (D + 1))
    (W : Fin D → HermLine ι) (hW : ∀ j, IsSmoothHerm (W j)) (m : Fin D) (A A' B : HermLine ι)
    (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A') (hB : IsSmoothHerm B) (hab : A'.a = A.a)
    (hloc : ∀ z ∈ mcPts P, ∃ c : ℝ, B.h =ᶠ[𝓝 z] fun _ => c) :
    I P (D + 1) (Fin.snoc (Function.update W m A) B) =
      I P (D + 1) (Fin.snoc (Function.update W m A') B) := by
  have hM := smooth_update hW m hB
  have hswap : ∀ X : HermLine ι, IsSmoothHerm X →
      I P (D + 1) (Fin.snoc (Function.update W m X) B) = I P (D + 1) (Fin.snoc (Function.update W m B) X) := by
    intro X hX
    rw [← snoc_update_comp_swap W m X B]
    exact (hI.1 P (D + 1) _ _ hP (smooth_snoc (smooth_update hW m hX) hB)).symm
  rw [hswap A hA, hswap A' hA',
    GlobalTheory.CompanionTheory.Ar.Tele.step GroundTheory.Heights₂.Heights.ForSecondHalf.MetricLocal.full I hI P D _ A A' hP hM hA hA' hab,
    _root_.GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegral_eq_zero_of_locConst K ι P D (pot (Function.update W m B)) _ m ?_, sub_zero]
  intro z hz
  obtain ⟨c, hc⟩ := hloc z hz
  refine ⟨Real.log c, ?_⟩
  filter_upwards [hc] with x hx
  simp [pot, hx]

theorem word_change (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) (P : Ideal (MRing ι)) {D : ℕ} (hP : IsArithVar P (D + 1))
    (L L' : Fin D → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) (hL' : ∀ j, IsSmoothHerm (L' j))
    (ha : ∀ j, (L j).a = (L' j).a) (B : HermLine ι) (hB : IsSmoothHerm B)
    (hloc : ∀ z ∈ mcPts P, ∃ c : ℝ, B.h =ᶠ[𝓝 z] fun _ => c) :
    I P (D + 1) (Fin.snoc L B) = I P (D + 1) (Fin.snoc L' B) := by
  let Wd : ℕ → Fin D → HermLine ι := fun m j => if (j : ℕ) < m then L' j else L j
  have hWd : ∀ m j, IsSmoothHerm (Wd m j) := by
    intro m j
    by_cases h : (j : ℕ) < m
    · simpa [Wd, h] using hL' j
    · simpa [Wd, h] using hL j
  have key : ∀ m, m ≤ D → I P (D + 1) (Fin.snoc L B) = I P (D + 1) (Fin.snoc (Wd m) B) := by
    intro m
    induction m with
    | zero =>
      intro _
      have : Wd 0 = L := by
        funext j
        simp [Wd]
      rw [this]
    | succ m ih =>
      intro hm
      let i : Fin D := ⟨m, hm⟩
      have e0 : Function.update (Wd m) i (L i) = Wd m := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [Wd, i]
        · simp [Function.update_of_ne hj]
      have e1 : Function.update (Wd m) i (L' i) = Wd (m + 1) := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [Wd, i]
        · have hne : (j : ℕ) ≠ m := fun h => hj (Fin.ext h)
          have hiff : (j : ℕ) < m + 1 ↔ (j : ℕ) < m := by omega
          simp [Function.update_of_ne hj, Wd, hiff]
      rw [ih (by omega), ← e1]
      conv_lhs => rw [← e0]
      exact position_change I hI P hP (Wd m) (hWd m) i (L i) (L' i) B (hL i) (hL' i) hB (ha i).symm hloc
  have hD : Wd D = L' := by
    funext j
    simp [Wd]
  rw [key D le_rfl, hD]

end FactorChange

theorem mass_eq_of_degrees : ArithIntersectionSystemStatement → PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L L' : Fin D → HermLine ι) (sg : F →+* ℂ), IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSmoothHerm (L' j)) → (∀ j, (L j).a = (L' j).a) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) = ptsIntegral (mCoordIdeal y) (pot L') ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) := by
  intro hA hInt K _ ι _ Ω _ F _ _ _ y D L L' sg hP hL hL' ha hex
  classical
  obtain ⟨II, hII, -⟩ := hA
  let Λ : (F →+* ℂ) → ℝ := fun s => if s = sg then Real.exp 1 else 1
  have hΛ : ∀ s, 0 < Λ s := by
    intro s
    by_cases h : s = sg
    · simp [Λ, h, Real.exp_pos]
    · simp [Λ, h]
  obtain ⟨B, hB0, hBs, hBloc⟩ :=
    exists_smooth_weight_const_near_embeddings K ι Ω F y Λ hΛ hex
  have mass : ∀ M : Fin D → HermLine ι, (∀ j, IsSmoothHerm (M j)) →
      II K ι (mCoordIdeal y) (D + 1) (Fin.snoc M B) =
        ptsIntegral (mCoordIdeal y) (pot M) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) := by
    intro M hM
    rw [intersection_locConst_trivial hInt K ι Ω F y D M B Λ II hII hP hM hB0 hBs hex hBloc,
      Finset.sum_eq_single sg]
    · simp [Λ]
    · intro s _ hs
      simp [Λ, hs]
    · intro h
      exact absurd (Finset.mem_univ sg) h
  rw [← mass L hL, ← mass L' hL']
  refine word_change (II K ι) (hII K ι) _ hP L L' hL hL' ha B hBs ?_
  intro z hz
  obtain ⟨s, hs, -⟩ := hex z hz
  exact ⟨Λ s, hBloc z hz s hs⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralIndependentOfMetric =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralConjugationSymmetry =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralConjugationSymmetry", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.LocallyConvex.AbsConvexOpen\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs\n\n"}
section -- clump:auto
@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MeasureTheory

section Hess

variable {D : ℕ}

theorem hess_comp_star (φ : (Fin D → ℂ) → ℝ) (z u v : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ (fun y => φ (star y))) z u v =
      fderiv ℝ (fderiv ℝ φ) (star z) (star u) (star v) := by
  let σ : (Fin D → ℂ) ≃L[ℝ] (Fin D → ℂ) := starL' ℝ
  let T : ((Fin D → ℂ) →L[ℝ] ℝ) ≃L[ℝ] ((Fin D → ℂ) →L[ℝ] ℝ) :=
    σ.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  have h1 : fderiv ℝ (fun y => φ (star y)) = T ∘ ((fderiv ℝ φ) ∘ σ) := by
    funext y
    have := σ.comp_right_fderiv (f := φ) (x := y)
    exact this
  rw [h1, T.comp_fderiv, σ.comp_right_fderiv]
  rfl

theorem cxHessian_comp_star (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    cxHessian (fun y => φ (star y)) z = (cxHessian φ (star z)).map (starRingEnd ℂ) := by
  ext i j
  have hs : ∀ i : Fin D, star (Pi.single i 1 : Fin D → ℂ) = Pi.single i 1 := fun i => by
    ext l; by_cases h : l = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have hI : ∀ i : Fin D, star (Complex.I • (Pi.single i 1 : Fin D → ℂ)) =
      -(Complex.I • (Pi.single i 1 : Fin D → ℂ)) := fun i => by
    rw [star_smul, hs]; simp
  simp only [cxHessian, Matrix.map_apply, hess_comp_star, hs, hI, map_neg,
    ContinuousLinearMap.neg_apply, neg_neg]
  simp only [map_div₀, map_add (f := _), map_mul, Complex.conj_ofReal, Complex.conj_I]
  have h4 : starRingEnd ℂ (4 : ℂ) = 4 := map_ofNat _ 4
  simp [h4]
  ring

end Hess

end GlobalTheory.CompanionTheory.Ar.Giv
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralConjugationSymmetry =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralUniqueEmbedding =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralUniqueEmbedding", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.PenHost\npublic import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSmoothWeightConstNearEmbeddings\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound\npublic import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralConjugationSymmetry\npublic import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed\nimport GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
open GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight

section SlopeTestRemainingChoices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

noncomputable def conjugateProjection {e : ℕ} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) where
  toFun w := star (Ψ (star w))
  map_add' a b := by simp only [star_add, map_add (f := _)]
  map_smul' c w := by
    simp only [star_smul, map_smul, RingHom.id_apply, star_star]

open Classical in
theorem logNorm_one_eq_indicator {Ω F : Type} [Field Ω] [Field F] [Algebra F Ω] {y : (Σ k, ι k) → Ω}
    {P : Ideal (MRing ι)} {tg : F →+* ℂ} {B : HermLine ι}
    (huniq : ∀ z ∈ mcPts P, ∃! s : F →+* ℂ, LiesOver y s z)
    (hB : ∀ z ∈ mcPts P, ∀ s : F →+* ℂ, LiesOver y s z → B.h z = if s = tg then Real.exp (-1) else 1) :
    ∀ z ∈ mcPts P, logNorm B 1 z = ({z | LiesOver y tg z}.indicator fun _ => (1 : ℝ)) z := by
  classical
  intro z hz
  obtain ⟨s, hs, hs'⟩ := huniq z hz
  have hone : ‖eval z (map (Int.castRingHom ℂ) (1 : MRing ι))‖ = 1 := by simp
  unfold logNorm
  rw [hone, hB z hz s hs]
  by_cases hst : s = tg
  · subst hst
    rw [Set.indicator_of_mem (show z ∈ {z | LiesOver y s z} from hs), ite_eq_left rfl, one_div,
      Real.log_inv, Real.log_exp, neg_neg]
  · rw [Set.indicator_of_notMem (fun h => hst (hs' tg h).symm), ite_eq_right hst]
    simp

end SlopeTestRemainingChoices

end GlobalTheory.CompanionTheory.Ar.Giv
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralUniqueEmbedding =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.MetricProofs.SumOverEmbeddingsUnitInvariance =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.MetricProofs.SumOverEmbeddingsUnitInvariance", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.PenHost\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound\npublic import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UnitRatioDivisorSupportEq\npublic import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSmoothWeightConstNearEmbeddings\npublic import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionLocConstTrivial\npublic import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PBoundedSectionTransfer\nimport GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.LengthLocQuotEqZero\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.MetricProofs.SumOverEmbeddingsUnitInvariance =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.MetricProofs.PieceDegreeOfIntersectionAndResolution =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.MetricProofs.PieceDegreeOfIntersectionAndResolution", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes\npublic import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree\npublic import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings\npublic import Development.AutomorphicSpectrum.Proofs.AdelicProofs.UnitLogOrthogonalWeightConstant\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.PenHost\npublic import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralIndependentOfMetric\npublic import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralUniqueEmbedding\npublic import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumOverEmbeddingsUnitInvariance\npublic import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsConjInvariant\nimport GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.LengthLocQuotEqZero\n\n"}
section -- clump:auto
@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

noncomputable section

def fsOfDegree {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι) : HermLine ι :=
  HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) A.a

end

end GlobalTheory.CompanionTheory.Ar.Giv
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.MetricProofs.PieceDegreeOfIntersectionAndResolution =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddingPiecesOfIntersectionAndResolution =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddingPiecesOfIntersectionAndResolution", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement\npublic import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes\npublic import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree\npublic import Development.AutomorphicSpectrum.Proofs.MetricProofs.PieceDegreeOfIntersectionAndResolution\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt\npublic import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegrableOfResolutionStatement\npublic import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingPieces\nimport Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatementStatement\nimport GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPiecesAdditive\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddingPiecesOfIntersectionAndResolution =====
