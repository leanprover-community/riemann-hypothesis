module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
public import Development.AutomorphicSpectrum.PublishedTheorems.Jets₂.IsPermissibleOfCentre
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieAlgebraOfLinearGroupClosed
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionAdditive
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionOfSmoothVector
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothVectorsInvariantSubspace
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.RealPlaceAnalysis.StatementA
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionCommutator, Development.AutomorphicSpectrum.Proofs.GlobalProofs.NelsonExistsWordGrowthConstant, Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianFormLieWordGrowth, Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieBasisCoordinateGrowthBound, Development.AutomorphicSpectrum.Proofs.GlobalProofs.LinearIndependentCoefficientNormBound, Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothVectorHermitianFormGrowth, Development.AutomorphicSpectrum.Proofs.GlobalProofs.WordBoundOfDelta

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionCommutator =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionCommutator", "h": "module\n\npublic import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec\npublic import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional\npublic import Development.AutomorphicSpectrum.PublishedTheorems.Jets₂.IsPermissibleOfCentre\npublic import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieAlgebraOfLinearGroupClosed\npublic import Mathlib.Analysis.Calculus.FDeriv.Symmetric\nimport Mathlib.Algebra.Order.Archimedean.Real.Hom\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Calculus.Deriv.Prod\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum\nimport Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Bracket

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def rightMul (Y : Matrix (Fin n) (Fin n) ℂ) : (Fin n → Fin n → ℂ) →L[ℝ] (Fin n → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => Matrix.of.symm (Matrix.of z * Y)
      map_add' := fun x y => by
        ext a b
        simp [Matrix.mul_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        ext a b
        simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc] }

theorem rightMul_apply (Y : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → Fin n → ℂ) :
    rightMul Y z = Matrix.of.symm (Matrix.of z * Y) := rfl

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_entry (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X)) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_curve (z : Fin n → Fin n → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => (Matrix.of.symm (Matrix.of z * NormedSpace.exp (t • X)) : Fin n → Fin n → ℂ))
      (rightMul X z) 0 := by
  rw [hasDerivAt_pi]
  intro a
  rw [hasDerivAt_pi]
  intro b
  simp only [rightMul_apply, Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
  exact HasDerivAt.fun_sum (fun c _ => (hasDerivAt_entry X c b).const_mul (z a c))

def one : Fin n → Fin n → ℂ := Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)

theorem of_one : Matrix.of (one (n := n)) = 1 := by exact Matrix.of.apply_symm_apply _

section Smooth

variable {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {v : H}
  {F : (Fin n → Fin n → ℂ) → H}

theorem hasDerivAt_along (hG : IsLinRed G) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) {z : Fin n → Fin n → ℂ} (hz : Matrix.of z ∈ G) :
    HasDerivAt (fun t : ℝ => π (Matrix.of z * NormedSpace.exp (t • X)) v)
      (fderiv ℝ F z (rightMul X z)) 0 := by
  have hd : HasFDerivAt F (fderiv ℝ F z) (Matrix.of.symm (Matrix.of z * NormedSpace.exp ((0 : ℝ) • X))) := by
    have : (Matrix.of.symm (Matrix.of z * NormedSpace.exp ((0 : ℝ) • X)) : Fin n → Fin n → ℂ) = z := by
      simp
    rw [this]
    exact (hF.differentiable (by simp) z).hasFDerivAt
  have h := hd.comp_hasDerivAt (0 : ℝ) (hasDerivAt_curve z X)
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have hm : Matrix.of z * NormedSpace.exp (t • X) ∈ G := hG.mul_mem _ hz _ (hX t)
  have := hFv (Matrix.of.symm (Matrix.of z * NormedSpace.exp (t • X))) (by simpa only [Matrix.of.apply_symm_apply] using hm)
  simpa only [Matrix.of.apply_symm_apply, Function.comp_def] using this

theorem hasDerivAt_exp_along (hG : IsLinRed G) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) :
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (fderiv ℝ F one (rightMul X one)) 0 := by
  have h := hasDerivAt_along hG hF hFv hX (z := one) (by rw [of_one]; exact hG.one_mem)
  simpa [of_one] using h

theorem dRep_eq (hG : IsLinRed G) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) : dRep π X v = fderiv ℝ F one (rightMul X one) :=
  (hasDerivAt_exp_along hG hF hFv hX).deriv

theorem rep_dRep (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) {z : Fin n → Fin n → ℂ} (hz : Matrix.of z ∈ G) :
    π (Matrix.of z) (dRep π X v) = fderiv ℝ F z (rightMul X z) := by
  have h1 := hasDerivAt_exp_along hG hF hFv hX
  have h2 := ((π (Matrix.of z)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h3 := hasDerivAt_along hG hF hFv hX hz
  rw [dRep_eq hG hF hFv hX]
  refine HasDerivAt.unique ?_ h3
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have := hrep.2 _ hz _ (hX t)
  simp [this]

theorem dRep_dRep (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G) :
    dRep π X (dRep π Y v) =
      fderiv ℝ (fderiv ℝ F) one (rightMul X one) (rightMul Y one) +
        fderiv ℝ F one (rightMul Y (rightMul X one)) := by
  have hF1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_cast)
  have hdF : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) one) one :=
    (hF1.differentiable (by simp) one).hasFDerivAt
  have hG1 := hdF.clm_apply (rightMul Y).hasFDerivAt
  have hc := hasDerivAt_curve (one (n := n)) X
  have h0 : (Matrix.of.symm (Matrix.of (one (n := n)) * NormedSpace.exp ((0 : ℝ) • X)) : Fin n → Fin n → ℂ) = one := by
    simp [one]
  have h := hG1.comp_hasDerivAt_of_eq (0 : ℝ) hc h0.symm
  have h' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) (dRep π Y v)) _ 0 :=
    h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
      have := rep_dRep hG hrep hF hFv hY (z := Matrix.of.symm (NormedSpace.exp (t • X)))
        (by simpa only [Matrix.of.apply_symm_apply] using hX t)
      simpa only [Matrix.of.apply_symm_apply, of_one, one_mul, Function.comp_def] using this)
  refine h'.deriv.trans ?_
  simp [add_comm]

end Smooth

theorem dRep_bracket {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G) :
    dRep π (X * Y - Y * X) v = dRep π X (dRep π Y v) - dRep π Y (dRep π X v) := by
  obtain ⟨F, hF, hFv⟩ := hv
  have hZ : X * Y - Y * X ∈ HCSS.lieOf G := (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.lieOf_isLieSubalgebra hG).2.2.1 X Y hX hY
  have hsymm : IsSymmSndFDerivAt ℝ F one :=
    (hF.contDiffAt).isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 le_top)
  rw [dRep_dRep hG hrep hF hFv hX hY, dRep_dRep hG hrep hF hFv hY hX, dRep_eq hG hF hFv hZ,
    hsymm.eq (rightMul X one) (rightMul Y one), add_sub_add_left_eq_sub, ← map_sub]
  congr 1
  simp only [rightMul_apply, Matrix.of.apply_symm_apply, of_one, one_mul]
  ext a b
  rfl

theorem smooth_bracket : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G), dRep π (X * Y - Y * X) v = dRep π X (dRep π Y v) - dRep π Y (dRep π X v) :=
  fun hG hrep _ hv _ _ hX hY => dRep_bracket hG hrep hv hX hY

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Bracket

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionCommutator =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.GlobalProofs.NelsonExistsWordGrowthConstant =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.GlobalProofs.NelsonExistsWordGrowthConstant", "h": "module\n\npublic import Mathlib.Analysis.CStarAlgebra.Module.Constructions\npublic import Mathlib.LinearAlgebra.FiniteDimensional.Defs\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\nimport Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum\nimport Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional\nimport Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule\nimport Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec\nimport Development.AutomorphicSpectrum.PublishedTheorems.Jets₂.IsPermissibleOfCentre\nimport Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange\nimport Formalism.RealPlaceAnalysis.StatementA\nimport Formalism.SharpRestriction.CuspSpanNormBounds.Point\npublic import Mathlib.Topology.Algebra.Module.FiniteDimension\n\n"}
section -- clump:auto
@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Nelson

variable {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {d : ℕ}

private theorem list_bound_lemma (X : Fin d → Module.End ℂ M) (V : Submodule ℂ M)
    [FiniteDimensional ℂ V] (l : List (Fin d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ V, ‖(l.map X).prod u‖ ≤ C * ‖u‖ :=
  ⟨‖LinearMap.toContinuousLinearMap (((l.map X).prod).comp V.subtype)‖,
    ContinuousLinearMap.opNorm_nonneg _,
    fun u hu => (LinearMap.toContinuousLinearMap (((l.map X).prod).comp V.subtype)).le_opNorm ⟨u, hu⟩⟩

theorem exists_word_bound (X : Fin d → Module.End ℂ M) (V : Submodule ℂ M)
    [FiniteDimensional ℂ V] (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ l : List (Fin d), l.length = k → ∀ u ∈ V,
      ‖(l.map X).prod u‖ ≤ B * ‖u‖ := by
  choose C hC0 hC using fun l : List (Fin d) => list_bound_lemma X V l
  have hfin : {l : List (Fin d) | l.length = k}.Finite :=
    (Set.finite_range (fun v : List.Vector (Fin d) k => v.1)).subset fun l hl => ⟨⟨l, hl⟩, rfl⟩
  refine ⟨∑ l ∈ hfin.toFinset, C l, Finset.sum_nonneg fun l _ => hC0 l, fun l hl u hu => ?_⟩
  refine (hC l u hu).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg u))
  exact Finset.single_le_sum (fun l _ => hC0 l) (hfin.mem_toFinset.2 hl)

theorem exists_least_word_bound (X : Fin d → Module.End ℂ M) (V : Submodule ℂ M)
    [FiniteDimensional ℂ V] (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ l : List (Fin d), l.length = k → ∀ u ∈ V,
      ‖(l.map X).prod u‖ ≤ B * ‖u‖) ∧
      ∀ B' : ℝ, 0 ≤ B' → (∀ l : List (Fin d), l.length = k → ∀ u ∈ V,
        ‖(l.map X).prod u‖ ≤ B' * ‖u‖) → B ≤ B' := by
  obtain ⟨B₀, hB₀0, hB₀⟩ := exists_word_bound X V k
  let S : Set ℝ := {B' | 0 ≤ B' ∧ ∀ l : List (Fin d), l.length = k → ∀ u ∈ V,
      ‖(l.map X).prod u‖ ≤ B' * ‖u‖}
  have hne : S.Nonempty := ⟨B₀, hB₀0, hB₀⟩
  have hbdd : BddBelow S := ⟨0, fun B' hB' => hB'.1⟩
  refine ⟨sInf S, le_csInf hne fun B' hB' => hB'.1, fun l hl u hu => ?_,
    fun B' hB'0 hB' => csInf_le hbdd ⟨hB'0, hB'⟩⟩
  rcases (norm_nonneg u).eq_or_lt with h0 | hpos
  · have hu0 : u = 0 := norm_eq_zero.1 h0.symm
    simp [hu0]
  · rw [← div_le_iff₀ hpos]
    exact le_csInf hne fun B' hB' => (div_le_iff₀ hpos).2 (hB'.2 l hl u hu)

theorem comm_sumSq (X : Fin d → Module.End ℂ M) (c : Fin d → Fin d → Fin d → ℂ)
    (hc : ∀ i j, X i * X j - X j * X i = ∑ l, c i j l • X l) (j : Fin d) :
    (∑ i, X i * X i) * X j - X j * (∑ i, X i * X i) =
      ∑ i, ∑ m, c i j m • (X i * X m + X m * X i) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h : X i * X i * X j - X j * (X i * X i) =
      X i * (X i * X j - X j * X i) + (X i * X j - X j * X i) * X i := by noncomm_ring
  rw [h, hc i j, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [mul_smul_comm, smul_mul_assoc, smul_add]

theorem comm_word_bound (X : Fin d → Module.End ℂ M) (c : Fin d → Fin d → Fin d → ℂ)
    (hc : ∀ i j, X i * X j - X j * X i = ∑ l, c i j l • X l) (V : Submodule ℂ M)
    (k : ℕ) (B γ : ℝ) (hB0 : 0 ≤ B)
    (hγ : ∀ j, ∑ i, ∑ m, 2 * ‖c i j m‖ ≤ γ)
    (hB : ∀ l : List (Fin d), l.length = k + 1 → ∀ u ∈ V, ‖(l.map X).prod u‖ ≤ B * ‖u‖) :
    ∀ (l p : List (Fin d)), p.length + l.length = k → ∀ u ∈ V,
      ‖((p.map X).prod * ((∑ i, X i * X i) * (l.map X).prod -
        (l.map X).prod * (∑ i, X i * X i))) u‖ ≤ l.length * γ * B * ‖u‖ := by
  intro l
  induction l with
  | nil =>
    intro p _ u _
    simp
  | cons j l ih =>
    intro p hpl u hu
    have hlen : (p ++ [j]).length + l.length = k := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hpl ⊢
      omega
    have hw : ∀ i m, ‖((p.map X).prod * (X i * X m) * (l.map X).prod) u‖ ≤ B * ‖u‖ := by
      intro i m
      have h := hB (p ++ i :: m :: l) (by
        simp only [List.length_append, List.length_cons] at hpl ⊢
        omega) u hu
      simpa [List.map_append, List.prod_append, mul_assoc] using h
    have hexp : ((p.map X).prod * ((∑ i, X i * X i) * X j - X j * (∑ i, X i * X i)) *
        (l.map X).prod) u =
        ∑ i, ∑ m, c i j m • (((p.map X).prod * (X i * X m) * (l.map X).prod) u +
          ((p.map X).prod * (X m * X i) * (l.map X).prod) u) := by
      rw [comm_sumSq X c hc j]
      simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, mul_add, add_mul,
        LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply]
    have h1 : ‖((p.map X).prod * ((∑ i, X i * X i) * X j - X j * (∑ i, X i * X i)) *
        (l.map X).prod) u‖ ≤ γ * B * ‖u‖ := by
      rw [hexp]
      calc _ ≤ ∑ i, ∑ m, ‖c i j m‖ * (B * ‖u‖ + B * ‖u‖) := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
            rw [norm_smul]
            exact mul_le_mul_of_nonneg_left
              ((norm_add_le _ _).trans (add_le_add (hw i m) (hw m i))) (norm_nonneg _)
        _ = (∑ i, ∑ m, 2 * ‖c i j m‖) * (B * ‖u‖) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun m _ => ?_
            ring
        _ ≤ γ * (B * ‖u‖) := mul_le_mul_of_nonneg_right (hγ j) (mul_nonneg hB0 (norm_nonneg u))
        _ = γ * B * ‖u‖ := by ring
    have h2 := ih (p ++ [j]) hlen u hu
    have key : (p.map X).prod * ((∑ i, X i * X i) * ((j :: l).map X).prod -
        ((j :: l).map X).prod * (∑ i, X i * X i)) =
        (p.map X).prod * ((∑ i, X i * X i) * X j - X j * (∑ i, X i * X i)) * (l.map X).prod +
        ((p ++ [j]).map X).prod * ((∑ i, X i * X i) * (l.map X).prod -
          (l.map X).prod * (∑ i, X i * X i)) := by
      simp only [List.map_cons, List.prod_cons, List.map_append, List.prod_append, List.map_nil,
        List.prod_nil, mul_one]
      noncomm_ring
    rw [key, LinearMap.add_apply]
    calc _ ≤ γ * B * ‖u‖ + l.length * γ * B * ‖u‖ := (norm_add_le _ _).trans (add_le_add h1 h2)
      _ = ((j :: l).length : ℝ) * γ * B * ‖u‖ := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring

theorem energy_le (X : Fin d → Module.End ℂ M) (a : ℝ)
    (hs : ∀ i u v, |(⟪X i u, v⟫_ℂ + ⟪u, X i v⟫_ℂ).re| ≤ a * ‖u‖ * ‖v‖) (x : M) :
    ∑ i, ‖X i x‖ ^ 2 ≤ ‖(∑ i, X i * X i) x‖ * ‖x‖ + a * (∑ i, ‖X i x‖) * ‖x‖ := by
  have hi : ∀ i, ‖X i x‖ ^ 2 ≤ -(⟪x, (X i * X i) x⟫_ℂ).re + a * ‖X i x‖ * ‖x‖ := by
    intro i
    have h := le_trans (le_abs_self _) (hs i x (X i x))
    have h1 : (⟪X i x, X i x⟫_ℂ).re = ‖X i x‖ ^ 2 := by
      rw [← RCLike.re_to_complex, inner_self_eq_norm_sq]
    rw [Complex.add_re, h1] at h
    rw [Module.End.mul_apply]
    nlinarith [h]
  have hsum : -(⟪x, (∑ i, X i * X i) x⟫_ℂ).re = ∑ i, -(⟪x, (X i * X i) x⟫_ℂ).re := by
    rw [LinearMap.sum_apply, inner_sum, Complex.re_sum, ← Finset.sum_neg_distrib]
  have hre : -(⟪x, (∑ i, X i * X i) x⟫_ℂ).re ≤ ‖(∑ i, X i * X i) x‖ * ‖x‖ := by
    have h := re_inner_le_norm (𝕜 := ℂ) (-x) ((∑ i, X i * X i) x)
    rw [inner_neg_left, map_neg, norm_neg, RCLike.re_to_complex] at h
    linarith [mul_comm ‖x‖ ‖(∑ i, X i * X i) x‖]
  calc ∑ i, ‖X i x‖ ^ 2 ≤ ∑ i, (-(⟪x, (X i * X i) x⟫_ℂ).re + a * ‖X i x‖ * ‖x‖) :=
        Finset.sum_le_sum fun i _ => hi i
    _ = -(⟪x, (∑ i, X i * X i) x⟫_ℂ).re + a * (∑ i, ‖X i x‖) * ‖x‖ := by
      rw [Finset.sum_add_distrib, hsum, Finset.mul_sum, Finset.sum_mul]
    _ ≤ _ := by linarith [hre]

theorem step_sq (X : Fin d → Module.End ℂ M) (c : Fin d → Fin d → Fin d → ℂ)
    (hc : ∀ i j, X i * X j - X j * X i = ∑ l, c i j l • X l) (a : ℝ) (ha : 0 ≤ a)
    (hs : ∀ i u v, |(⟪X i u, v⟫_ℂ + ⟪u, X i v⟫_ℂ).re| ≤ a * ‖u‖ * ‖v‖)
    (V : Submodule ℂ M) (hV : ∀ u ∈ V, (∑ i, X i * X i) u ∈ V)
    (k : ℕ) (A B γ s : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hγ0 : 0 ≤ γ)
    (hγ : ∀ j, ∑ i, ∑ m, 2 * ‖c i j m‖ ≤ γ)
    (hΔ : ∀ u ∈ V, ‖(∑ i, X i * X i) u‖ ≤ s ^ 2 * ‖u‖)
    (hA : ∀ l : List (Fin d), l.length = k → ∀ u ∈ V, ‖(l.map X).prod u‖ ≤ A * ‖u‖)
    (hB : ∀ l : List (Fin d), l.length = k + 1 → ∀ u ∈ V, ‖(l.map X).prod u‖ ≤ B * ‖u‖)
    (l : List (Fin d)) (hl : l.length = k) (i : Fin d) (u : M) (hu : u ∈ V) :
    ‖X i ((l.map X).prod u)‖ ^ 2 ≤
      (s ^ 2 * A ^ 2 + (k * γ + a * d) * A * B) * ‖u‖ ^ 2 := by
  have hu0 := norm_nonneg u
  have hx : ‖(l.map X).prod u‖ ≤ A * ‖u‖ := hA l hl u hu
  have hXi : ∀ j, ‖X j ((l.map X).prod u)‖ ≤ B * ‖u‖ := by
    intro j
    have h := hB (j :: l) (by simp [hl]) u hu
    simpa using h
  have hcomm : ‖((∑ i, X i * X i) * (l.map X).prod - (l.map X).prod * (∑ i, X i * X i)) u‖ ≤
      k * γ * B * ‖u‖ := by
    have h := comm_word_bound X c hc V k B γ hB0 hγ hB l [] (by simp [hl]) u hu
    simpa [hl] using h
  have hΔx : ‖(∑ i, X i * X i) ((l.map X).prod u)‖ ≤ (s ^ 2 * A + k * γ * B) * ‖u‖ := by
    have e : (∑ i, X i * X i) ((l.map X).prod u) = (l.map X).prod ((∑ i, X i * X i) u) +
        ((∑ i, X i * X i) * (l.map X).prod - (l.map X).prod * (∑ i, X i * X i)) u := by
      rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
      abel
    rw [e]
    have h1 : ‖(l.map X).prod ((∑ i, X i * X i) u)‖ ≤ A * (s ^ 2 * ‖u‖) :=
      (hA l hl _ (hV u hu)).trans (mul_le_mul_of_nonneg_left (hΔ u hu) hA0)
    calc _ ≤ A * (s ^ 2 * ‖u‖) + k * γ * B * ‖u‖ := (norm_add_le _ _).trans (add_le_add h1 hcomm)
      _ = (s ^ 2 * A + k * γ * B) * ‖u‖ := by ring
  have hE := energy_le X a hs ((l.map X).prod u)
  have hsumX : ∑ j, ‖X j ((l.map X).prod u)‖ ≤ d * (B * ‖u‖) := by
    calc ∑ j, ‖X j ((l.map X).prod u)‖ ≤ ∑ _j : Fin d, B * ‖u‖ :=
          Finset.sum_le_sum fun j _ => hXi j
      _ = d * (B * ‖u‖) := by simp
  have hsingle : ‖X i ((l.map X).prod u)‖ ^ 2 ≤ ∑ j, ‖X j ((l.map X).prod u)‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖X j ((l.map X).prod u)‖ ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have hLu0 := norm_nonneg ((l.map X).prod u)
  have hc1 : 0 ≤ (s ^ 2 * A + k * γ * B) * ‖u‖ :=
    mul_nonneg (add_nonneg (mul_nonneg (sq_nonneg s) hA0)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hγ0) hB0)) hu0
  have t1 := mul_le_mul hΔx hx hLu0 hc1
  have t2 : a * (∑ j, ‖X j ((l.map X).prod u)‖) * ‖(l.map X).prod u‖ ≤
      a * (d * (B * ‖u‖)) * (A * ‖u‖) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hsumX ha) hx hLu0
      (mul_nonneg ha (mul_nonneg (Nat.cast_nonneg d) (mul_nonneg hB0 hu0)))
  calc ‖X i ((l.map X).prod u)‖ ^ 2 ≤ ∑ j, ‖X j ((l.map X).prod u)‖ ^ 2 := hsingle
    _ ≤ _ := hE
    _ ≤ (s ^ 2 * A + k * γ * B) * ‖u‖ * (A * ‖u‖) + a * (d * (B * ‖u‖)) * (A * ‖u‖) :=
        add_le_add t1 t2
    _ = (s ^ 2 * A ^ 2 + (k * γ + a * d) * A * B) * ‖u‖ ^ 2 := by ring

theorem le_of_sq_le_quad (A B s E : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hs0 : 0 ≤ s) (hE0 : 0 ≤ E)
    (h : B ^ 2 ≤ s ^ 2 * A ^ 2 + E * A * B) : B ≤ (s + E) * A := by
  by_contra hc
  rw [not_le] at hc
  have hsA : s * A ≤ B := by nlinarith [mul_nonneg hE0 hA0]
  have hB : 0 < B := lt_of_le_of_lt (mul_nonneg (add_nonneg hs0 hE0) hA0) hc
  have h1 : (s + E) * A * B < B * B := mul_lt_mul_of_pos_right hc hB
  have h2 : s * A * (s * A) ≤ s * A * B := mul_le_mul_of_nonneg_left hsA (mul_nonneg hs0 hA0)
  nlinarith [h1, h2, h]

theorem next_word_bound (X : Fin d → Module.End ℂ M) (c : Fin d → Fin d → Fin d → ℂ)
    (hc : ∀ i j, X i * X j - X j * X i = ∑ l, c i j l • X l) (a : ℝ) (ha : 0 ≤ a)
    (hs : ∀ i u v, |(⟪X i u, v⟫_ℂ + ⟪u, X i v⟫_ℂ).re| ≤ a * ‖u‖ * ‖v‖)
    (V : Submodule ℂ M) [FiniteDimensional ℂ V] (hV : ∀ u ∈ V, (∑ i, X i * X i) u ∈ V)
    (k : ℕ) (A γ s : ℝ) (hA0 : 0 ≤ A) (hs0 : 0 ≤ s) (hγ0 : 0 ≤ γ)
    (hγ : ∀ j, ∑ i, ∑ m, 2 * ‖c i j m‖ ≤ γ)
    (hΔ : ∀ u ∈ V, ‖(∑ i, X i * X i) u‖ ≤ s ^ 2 * ‖u‖)
    (hA : ∀ l : List (Fin d), l.length = k → ∀ u ∈ V, ‖(l.map X).prod u‖ ≤ A * ‖u‖) :
    ∀ l : List (Fin d), l.length = k + 1 → ∀ u ∈ V,
      ‖(l.map X).prod u‖ ≤ (s + (k * γ + a * d)) * A * ‖u‖ := by
  have hE0 : 0 ≤ (k : ℝ) * γ + a * d :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg k) hγ0) (mul_nonneg ha (Nat.cast_nonneg d))
  obtain ⟨B, hB0, hBb, hBl⟩ := exists_least_word_bound X V (k + 1)
  have hQ0 : 0 ≤ s ^ 2 * A ^ 2 + ((k : ℝ) * γ + a * d) * A * B :=
    add_nonneg (mul_nonneg (sq_nonneg s) (sq_nonneg A)) (mul_nonneg (mul_nonneg hE0 hA0) hB0)
  have hsq : ∀ l : List (Fin d), l.length = k + 1 → ∀ u ∈ V,
      ‖(l.map X).prod u‖ ≤ Real.sqrt (s ^ 2 * A ^ 2 + ((k : ℝ) * γ + a * d) * A * B) * ‖u‖ := by
    intro l hl u hu
    cases l with
    | nil => simp at hl
    | cons i l =>
      have hl' : l.length = k := by simpa using hl
      have h := step_sq X c hc a ha hs V hV k A B γ s hA0 hB0 hγ0 hγ hΔ hA hBb l hl' i u hu
      have h2 := Real.sqrt_le_sqrt h
      rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hQ0, Real.sqrt_sq (norm_nonneg _)] at h2
      simpa using h2
  have hle : B ≤ Real.sqrt (s ^ 2 * A ^ 2 + ((k : ℝ) * γ + a * d) * A * B) :=
    hBl _ (Real.sqrt_nonneg _) hsq
  have hB2 : B ^ 2 ≤ s ^ 2 * A ^ 2 + ((k : ℝ) * γ + a * d) * A * B := by
    have h := mul_self_le_mul_self hB0 hle
    rw [Real.mul_self_sqrt hQ0] at h
    nlinarith [h]
  have hfin := le_of_sq_le_quad A B s _ hA0 hB0 hs0 hE0 hB2
  intro l hl u hu
  exact (hBb l hl u hu).trans (mul_le_mul_of_nonneg_right hfin (norm_nonneg u))

theorem nelson_word_growth_estimate (X : Fin d → Module.End ℂ M) (c : Fin d → Fin d → Fin d → ℂ)
    (hc : ∀ i j, X i * X j - X j * X i = ∑ l, c i j l • X l) (a : ℝ) (ha : 0 ≤ a)
    (hs : ∀ i u v, |(⟪X i u, v⟫_ℂ + ⟪u, X i v⟫_ℂ).re| ≤ a * ‖u‖ * ‖v‖)
    (V : Submodule ℂ M) [FiniteDimensional ℂ V] (hV : ∀ u ∈ V, (∑ i, X i * X i) u ∈ V)
    (γ s : ℝ) (hs0 : 0 ≤ s) (hγ0 : 0 ≤ γ)
    (hγ : ∀ j, ∑ i, ∑ m, 2 * ‖c i j m‖ ≤ γ)
    (hΔ : ∀ u ∈ V, ‖(∑ i, X i * X i) u‖ ≤ s ^ 2 * ‖u‖) (k : ℕ) :
    ∀ l : List (Fin d), l.length = k → ∀ u ∈ V,
      ‖(l.map X).prod u‖ ≤ (s + γ + a * d + 1) ^ k * k.factorial * ‖u‖ := by
  have hd0 : (0 : ℝ) ≤ a * d := mul_nonneg ha (Nat.cast_nonneg d)
  have hC0 : (0 : ℝ) ≤ s + γ + a * d + 1 := by linarith
  induction k with
  | zero =>
    intro l hl u hu
    cases l with
    | nil => simp
    | cons _ _ => simp at hl
  | succ k ih =>
    intro l hl u hu
    have hA0 : 0 ≤ (s + γ + a * d + 1) ^ k * (k.factorial : ℝ) :=
      mul_nonneg (pow_nonneg hC0 k) (Nat.cast_nonneg _)
    have h := next_word_bound X c hc a ha hs V hV k _ γ s hA0 hs0 hγ0 hγ hΔ ih l hl u hu
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg u))
    have hk : s + ((k : ℝ) * γ + a * d) ≤ ((k : ℝ) + 1) * (s + γ + a * d + 1) := by
      nlinarith [mul_nonneg (Nat.cast_nonneg k) hs0, mul_nonneg (Nat.cast_nonneg k) hd0,
        (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    calc (s + ((k : ℝ) * γ + a * d)) * ((s + γ + a * d + 1) ^ k * (k.factorial : ℝ))
        ≤ (((k : ℝ) + 1) * (s + γ + a * d + 1)) * ((s + γ + a * d + 1) ^ k * (k.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_right hk hA0
      _ = (s + γ + a * d + 1) ^ (k + 1) * (((k + 1).factorial : ℕ) : ℝ) := by
          push_cast [Nat.factorial_succ]
          ring

theorem exists_sq_bound (T : Module.End ℂ M) (V : Submodule ℂ M) [FiniteDimensional ℂ V] :
    ∃ s : ℝ, 0 ≤ s ∧ ∀ u ∈ V, ‖T u‖ ≤ s ^ 2 * ‖u‖ := by
  refine ⟨Real.sqrt ‖LinearMap.toContinuousLinearMap (T.comp V.subtype)‖, Real.sqrt_nonneg _,
    fun u hu => ?_⟩
  rw [Real.sq_sqrt (ContinuousLinearMap.opNorm_nonneg _)]
  exact (LinearMap.toContinuousLinearMap (T.comp V.subtype)).le_opNorm ⟨u, hu⟩

theorem word_growth : ∀ {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {d : ℕ} (X : Fin d → Module.End ℂ M) (c : Fin d → Fin d → Fin d → ℂ) (hc : ∀ i j, X i * X j - X j * X i = ∑ l, c i j l • X l) (a : ℝ) (ha : 0 ≤ a) (hs : ∀ i u v, |(⟪X i u, v⟫_ℂ + ⟪u, X i v⟫_ℂ).re| ≤ a * ‖u‖ * ‖v‖) (V : Submodule ℂ M) [FiniteDimensional ℂ V] (hV : ∀ u ∈ V, (∑ i, X i * X i) u ∈ V), ∃ C : ℝ, 0 < C ∧ ∀ (l : List (Fin d)), ∀ u ∈ V, ‖(l.map X).prod u‖ ≤ C ^ (l.length + 1) * l.length.factorial * ‖u‖ := by
  intro M _ _ d X c hc a ha hs V _ hV
  obtain ⟨s, hs0, hΔ⟩ := exists_sq_bound (∑ i, X i * X i) V
  obtain ⟨γ, hγ0, hγ⟩ : ∃ γ : ℝ, 0 ≤ γ ∧ ∀ j, ∑ i, ∑ m, 2 * ‖c i j m‖ ≤ γ :=
    ⟨∑ j, ∑ i, ∑ m, 2 * ‖c i j m‖,
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        mul_nonneg zero_le_two (norm_nonneg _),
      fun j => Finset.single_le_sum (f := fun j => ∑ i, ∑ m, 2 * ‖c i j m‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
          mul_nonneg zero_le_two (norm_nonneg _)) (Finset.mem_univ j)⟩
  have hd0 : (0 : ℝ) ≤ a * d := mul_nonneg ha (Nat.cast_nonneg d)
  refine ⟨s + γ + a * d + 1, by linarith, fun l u hu => ?_⟩
  have h := nelson_word_growth_estimate X c hc a ha hs V hV γ s hs0 hγ0 hγ hΔ l.length l rfl u hu
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg u))
  have hC1 : 1 ≤ s + γ + a * d + 1 := by linarith
  rw [pow_succ]
  exact mul_le_mul_of_nonneg_right
    (le_mul_of_one_le_right (pow_nonneg (by linarith) _) hC1) (Nat.cast_nonneg _)

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Nelson
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.GlobalProofs.NelsonExistsWordGrowthConstant =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianFormLieWordGrowth =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianFormLieWordGrowth", "h": "module\n\npublic import Mathlib.Analysis.CStarAlgebra.Module.Constructions\npublic import Mathlib.LinearAlgebra.FiniteDimensional.Defs\npublic import Development.AutomorphicSpectrum.Proofs.GlobalProofs.NelsonExistsWordGrowthConstant\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum\nimport Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional\nimport Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule\nimport Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec\nimport Development.AutomorphicSpectrum.PublishedTheorems.Jets₂.IsPermissibleOfCentre\nimport Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange\nimport Formalism.RealPlaceAnalysis.StatementA\nimport Formalism.SharpRestriction.CuspSpanNormBounds.Point\n\n"}
section -- clump:auto
@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.HCForm

theorem skew_of_diag {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : Module.End ℂ E) (A : ℝ) (hA : 0 ≤ A)
    (h : ∀ x, |(⟪T x, x⟫_ℂ + ⟪x, T x⟫_ℂ).re| ≤ A * ‖x‖ ^ 2) (u v : E) :
    |(⟪T u, v⟫_ℂ + ⟪u, T v⟫_ℂ).re| ≤ A * ‖u‖ * ‖v‖ := by
  set R : E → E → ℝ := fun u v => (⟪T u, v⟫_ℂ + ⟪u, T v⟫_ℂ).re with hR
  have hsym : ∀ u v, R v u = R u v := by
    intro u v
    simp only [hR, Complex.add_re]
    rw [← inner_conj_symm (T v) u, ← inner_conj_symm v (T u)]
    simp only [Complex.conj_re]
    ring
  have hpol : ∀ u v, 4 * R u v = R (u + v) (u + v) - R (u - v) (u - v) := by
    intro u v
    have := hsym u v
    simp only [hR, map_add (f := _), map_sub, inner_add_left, inner_add_right, inner_sub_left,
      inner_sub_right, Complex.add_re, Complex.sub_re] at this ⊢
    linarith
  have hhalf : ∀ u v, |R u v| ≤ A * (‖u‖ ^ 2 + ‖v‖ ^ 2) / 2 := by
    intro u v
    have h1 := abs_le.mp (h (u + v))
    have h2 := abs_le.mp (h (u - v))
    have hp := parallelogram_law_with_norm ℂ u v
    have e := hpol u v
    have hp' : ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by nlinarith
    have hb : A * ‖u + v‖ ^ 2 + A * ‖u - v‖ ^ 2 = 2 * A * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
      rw [← mul_add, hp']; ring
    change |R u v| ≤ _
    have g1 : R (u + v) (u + v) ≤ A * ‖u + v‖ ^ 2 := h1.2
    have g2 : -(A * ‖u + v‖ ^ 2) ≤ R (u + v) (u + v) := h1.1
    have g3 : R (u - v) (u - v) ≤ A * ‖u - v‖ ^ 2 := h2.2
    have g4 : -(A * ‖u - v‖ ^ 2) ≤ R (u - v) (u - v) := h2.1
    rw [abs_le]
    constructor <;> nlinarith
  change |R u v| ≤ _
  rcases eq_or_ne u 0 with rfl | hu
  · simp [hR]
  rcases eq_or_ne v 0 with rfl | hv
  · simp [hR]
  have hs : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have ht : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hscale : R (((‖v‖ : ℝ) : ℂ) • u) (((‖u‖ : ℝ) : ℂ) • v) = ‖v‖ * ‖u‖ * R u v := by
    simp only [hR, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have hb := hhalf (((‖v‖ : ℝ) : ℂ) • u) (((‖u‖ : ℝ) : ℂ) • v)
  rw [hscale, norm_smul, norm_smul, abs_mul, abs_of_pos (mul_pos ht hs)] at hb
  simp only [Complex.norm_real, norm_norm] at hb
  have hst : 0 < ‖v‖ * ‖u‖ := mul_pos ht hs
  have : ‖v‖ * ‖u‖ * |R u v| ≤ ‖v‖ * ‖u‖ * (A * ‖u‖ * ‖v‖) := by
    calc _ ≤ _ := hb
      _ = _ := by ring
  exact le_of_mul_le_mul_left this hst

theorem nelson_inner {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {d : ℕ}
    (X : Fin d → Module.End ℂ E) (c : Fin d → Fin d → Fin d → ℂ)
    (hc : ∀ i j, X i * X j - X j * X i = ∑ l, c i j l • X l) (A : ℝ) (hA : 0 ≤ A)
    (hs : ∀ i x, |2 * (⟪X i x, x⟫_ℂ).re| ≤ A * (⟪x, x⟫_ℂ).re)
    (V : Submodule ℂ E) [FiniteDimensional ℂ V] (hV : ∀ u ∈ V, (∑ i, X i * X i) u ∈ V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l : List (Fin d)), ∀ u ∈ V,
      Real.sqrt (⟪(l.map X).prod u, (l.map X).prod u⟫_ℂ).re ≤
        C ^ (l.length + 1) * l.length.factorial * Real.sqrt (⟪u, u⟫_ℂ).re := by
  have hsq : ∀ x : E, Real.sqrt (⟪x, x⟫_ℂ).re = ‖x‖ := by
    intro x
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
    exact Real.sqrt_sq (norm_nonneg x)
  have hskew : ∀ i u v, |(⟪X i u, v⟫_ℂ + ⟪u, X i v⟫_ℂ).re| ≤ A * ‖u‖ * ‖v‖ := by
    intro i
    refine skew_of_diag (X i) A hA ?_
    intro x
    have e : (⟪X i x, x⟫_ℂ + ⟪x, X i x⟫_ℂ).re = 2 * (⟪X i x, x⟫_ℂ).re := by
      rw [Complex.add_re, ← inner_conj_symm x (X i x), Complex.conj_re]
      ring
    have n : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [e, ← n]
    exact hs i x
  obtain ⟨C, hC, hb⟩ := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Nelson.word_growth X c hc A hA hskew V hV
  refine ⟨C, hC, fun l u hu => ?_⟩
  rw [hsq, hsq]
  exact hb l u hu

theorem nelson_form : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (Q : M → M → ℂ)
    (hadd : ∀ x y z, Q x (y + z) = Q x y + Q x z)
    (hsmul : ∀ (c : ℂ) x y, Q x (c • y) = c * Q x y)
    (hconj : ∀ x y, Q y x = star (Q x y))
    (hpos : ∀ x, x ≠ 0 → 0 < (Q x x).re) {d : ℕ} (X : Fin d → Module.End ℂ M)
    (c : Fin d → Fin d → Fin d → ℂ) (hc : ∀ i j, X i * X j - X j * X i = ∑ l, c i j l • X l)
    (A : ℝ) (hA : 0 ≤ A) (hs : ∀ i x, |2 * (Q (X i x) x).re| ≤ A * (Q x x).re)
    (V : Submodule ℂ M) [FiniteDimensional ℂ V] (hV : ∀ u ∈ V, (∑ i, X i * X i) u ∈ V),
    ∃ C : ℝ, 0 < C ∧ ∀ (l : List (Fin d)), ∀ u ∈ V,
      Real.sqrt (Q ((l.map X).prod u) ((l.map X).prod u)).re ≤
        C ^ (l.length + 1) * l.length.factorial * Real.sqrt (Q u u).re := by
  intro M _ _ Q hadd hsmul hconj hpos d X c hc A hA hs V _ hV
  have hzero : ∀ x, Q x 0 = 0 := by
    intro x
    have := hsmul 0 x 0
    simpa using this
  have hzero' : Q 0 0 = 0 := hzero 0
  let core : InnerProductSpace.Core ℂ M :=
    { inner := Q
      conj_inner_symm := fun x y => by
        change star (Q y x) = Q x y
        rw [hconj x y, star_star]
      re_inner_nonneg := fun x => by
        change 0 ≤ (Q x x).re
        rcases eq_or_ne x 0 with rfl | hx
        · simp [hzero']
        · exact (hpos x hx).le
      add_left := fun x y z => by
        change Q (x + y) z = Q x z + Q y z
        rw [hconj z (x + y), hadd, star_add, ← hconj, ← hconj]
      smul_left := fun x y r => by
        change Q (r • x) y = star r * Q x y
        rw [hconj y (r • x), hsmul, star_mul', ← hconj]
      definite := fun x hx => by
        by_contra hne
        have h0 : Q x x = 0 := hx
        have := hpos x hne
        simp [h0] at this }
  letI : NormedAddCommGroup M := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ M := InnerProductSpace.ofCore core.toCore
  exact nelson_inner X c hc A hA hs V hV

end GlobalTheory.CompanionTheory.HCForm
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianFormLieWordGrowth =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieBasisCoordinateGrowthBound =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieBasisCoordinateGrowthBound", "h": "module\n\npublic import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec\npublic import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional\npublic import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionAdditive\npublic import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionOfSmoothVector\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum\nimport Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule\n\n"}
section -- clump:auto
@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordExpand

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem isSmoothVec_add {u v : H} (hu : IsSmoothVec G π u) (hv : IsSmoothVec G π v) :
    IsSmoothVec G π (u + v) := by
  obtain ⟨F, hF, hF'⟩ := hu
  obtain ⟨K, hK, hK'⟩ := hv
  exact ⟨fun z => F z + K z, hF.add hK, fun z hz => by rw [map_add (f := _), hF' z hz, hK' z hz]⟩

theorem isSmoothVec_smul (c : ℂ) {v : H} (hv : IsSmoothVec G π v) :
    IsSmoothVec G π (c • v) := by
  obtain ⟨F, hF, hF'⟩ := hv
  exact ⟨fun z => c • F z, hF.const_smul c, fun z hz => by rw [map_smul, hF' z hz]⟩

theorem isSmoothVec_zero : IsSmoothVec G π (0 : H) :=
  ⟨fun _ => 0, contDiff_const, fun z _ => map_zero _⟩

theorem isSmoothVec_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → H)
    (hf : ∀ i, IsSmoothVec G π (f i)) : IsSmoothVec G π (∑ i ∈ s, c i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isSmoothVec_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isSmoothVec_add (isSmoothVec_smul _ (hf a)) ih

variable {d : ℕ} {b : Fin d → Matrix (Fin n) (Fin n) ℂ}

theorem word_smooth (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (hb : ∀ i, b i ∈ HCSS.lieOf G) (p : List (Fin d)) {w : H} (hw : IsSmoothVec G π w) :
    IsSmoothVec G π (p.foldr (fun i w => dRep π (b i) w) w) := by
  induction p with
  | nil => exact hw
  | cons i p ih => exact (hasDerivAt_dRep_and_isSmoothVec hG hrep ih (hb i)).2

theorem list_smooth (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ X ∈ l, X ∈ HCSS.lieOf G) {v : H}
    (hv : IsSmoothVec G π v) : IsSmoothVec G π (l.foldr (dRep π) v) := by
  induction l with
  | nil => exact hv
  | cons X l ih =>
    exact (hasDerivAt_dRep_and_isSmoothVec hG hrep
      (ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) (hl X List.mem_cons_self)).2

theorem word_add (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (hb : ∀ i, b i ∈ HCSS.lieOf G) (p : List (Fin d)) {u v : H} (hu : IsSmoothVec G π u)
    (hv : IsSmoothVec G π v) :
    p.foldr (fun i w => dRep π (b i) w) (u + v) =
      p.foldr (fun i w => dRep π (b i) w) u + p.foldr (fun i w => dRep π (b i) w) v := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact (SmoothLin.dRep_linear hG hrep (word_smooth hG hrep hb p hu)
      (word_smooth hG hrep hb p hv) (hb i) (hb i)).2.1

theorem word_smul (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (hb : ∀ i, b i ∈ HCSS.lieOf G) (p : List (Fin d)) (c : ℂ) {v : H}
    (hv : IsSmoothVec G π v) :
    p.foldr (fun i w => dRep π (b i) w) (c • v) =
      c • p.foldr (fun i w => dRep π (b i) w) v := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact (SmoothLin.dRep_linear hG hrep (word_smooth hG hrep hb p hv)
      (word_smooth hG hrep hb p hv) (hb i) (hb i)).2.2 c

theorem word_sum (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (hb : ∀ i, b i ∈ HCSS.lieOf G) (p : List (Fin d)) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (f : ι → H) (hf : ∀ i, IsSmoothVec G π (f i)) :
    p.foldr (fun i w => dRep π (b i) w) (∑ j ∈ s, c j • f j) =
      ∑ j ∈ s, c j • p.foldr (fun i w => dRep π (b i) w) (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := word_smul hG hrep hb p (0 : ℂ) (isSmoothVec_zero (G := G) (π := π) (H := H))
    simpa using h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      word_add hG hrep hb p (isSmoothVec_smul _ (hf a)) (isSmoothVec_sum s c f hf),
      word_smul hG hrep hb p _ (hf a), ih]

theorem mnorm_nonneg (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ mnorm X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem prod_mnorm_nonneg (l : List (Matrix (Fin n) (Fin n) ℂ)) : 0 ≤ (l.map mnorm).prod := by
  induction l with
  | nil => simp
  | cons X l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact mul_nonneg (mnorm_nonneg X) ih

theorem mixed_bound (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (hb : ∀ i, b i ∈ HCSS.lieOf G)
    (hsp : ∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i)
    (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ r : Fin d → ℝ, ∑ i, |r i| ≤ D * mnorm (∑ i, r i • b i))
    (hexp : ∀ (r : Fin d → ℝ) (w : H), IsSmoothVec G π w →
      dRep π (∑ i, r i • b i) w = ∑ i, (r i : ℂ) • dRep π (b i) w)
    {v : H} (hv : IsSmoothVec G π v) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ l : List (Fin d),
      ‖l.foldr (fun i w => dRep π (b i) w) v‖ ≤ C ^ (l.length + 1) * l.length.factorial)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ X ∈ l, X ∈ HCSS.lieOf G) (p : List (Fin d)) :
    ‖p.foldr (fun i w => dRep π (b i) w) (l.foldr (dRep π) v)‖ ≤
      C ^ (p.length + l.length + 1) * (p.length + l.length).factorial * D ^ l.length *
        (l.map mnorm).prod := by
  induction l generalizing p with
  | nil => simpa using hbound p
  | cons X l ih =>
    have hl' : ∀ Y ∈ l, Y ∈ HCSS.lieOf G := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    have hX : X ∈ HCSS.lieOf G := hl X List.mem_cons_self
    have hw : IsSmoothVec G π (l.foldr (dRep π) v) := list_smooth hG hrep l hl' hv
    obtain ⟨r, hr⟩ := hsp X hX
    have e1 : dRep π X (l.foldr (dRep π) v) =
        ∑ i, (r i : ℂ) • dRep π (b i) (l.foldr (dRep π) v) := by
      rw [hr]
      exact hexp r _ hw
    have hsm : ∀ i, IsSmoothVec G π (dRep π (b i) (l.foldr (dRep π) v)) := fun i =>
      (hasDerivAt_dRep_and_isSmoothVec hG hrep hw (hb i)).2
    have e2 : p.foldr (fun i w => dRep π (b i) w) (dRep π X (l.foldr (dRep π) v)) =
        ∑ i, (r i : ℂ) • (p ++ [i]).foldr (fun i w => dRep π (b i) w) (l.foldr (dRep π) v) := by
      rw [e1, word_sum hG hrep hb p _ _ _ hsm]
      simp [List.foldr_append]
    have hih : ∀ i, ‖(p ++ [i]).foldr (fun i w => dRep π (b i) w) (l.foldr (dRep π) v)‖ ≤
        C ^ (p.length + (l.length + 1) + 1) * (p.length + (l.length + 1)).factorial *
          D ^ l.length * (l.map mnorm).prod := by
      intro i
      have h := ih hl' (p ++ [i])
      rw [List.length_append, List.length_singleton,
        show p.length + 1 + l.length = p.length + (l.length + 1) by omega] at h
      exact h
    have hK : 0 ≤ C ^ (p.length + (l.length + 1) + 1) * (p.length + (l.length + 1)).factorial *
        D ^ l.length * (l.map mnorm).prod :=
      mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hC.le _) (Nat.cast_nonneg _))
        (pow_nonneg hD0 _)) (prod_mnorm_nonneg l)
    have hsum : ∑ i, |r i| ≤ D * mnorm X := by
      rw [hr]
      exact hD r
    show ‖p.foldr (fun i w => dRep π (b i) w) (dRep π X (l.foldr (dRep π) v))‖ ≤ _
    rw [e2]
    calc ‖∑ i, (r i : ℂ) • (p ++ [i]).foldr (fun i w => dRep π (b i) w) (l.foldr (dRep π) v)‖
        ≤ ∑ i, |r i| * (C ^ (p.length + (l.length + 1) + 1) *
            (p.length + (l.length + 1)).factorial * D ^ l.length * (l.map mnorm).prod) := by
          refine norm_sum_le_of_le _ fun i _ => ?_
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hih i) (abs_nonneg _)
      _ = (∑ i, |r i|) * (C ^ (p.length + (l.length + 1) + 1) *
            (p.length + (l.length + 1)).factorial * D ^ l.length * (l.map mnorm).prod) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ (D * mnorm X) * (C ^ (p.length + (l.length + 1) + 1) *
            (p.length + (l.length + 1)).factorial * D ^ l.length * (l.map mnorm).prod) :=
          mul_le_mul_of_nonneg_right hsum hK
      _ = _ := by
          simp only [List.length_cons, List.map_cons, List.prod_cons]
          ring

theorem wordBound_of_basis {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {d : ℕ}
    (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ HCSS.lieOf G)
    (hsp : ∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i)
    (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ r : Fin d → ℝ, ∑ i, |r i| ≤ D * mnorm (∑ i, r i • b i))
    (hexp : ∀ (r : Fin d → ℝ) (w : H), IsSmoothVec G π w →
      dRep π (∑ i, r i • b i) w = ∑ i, (r i : ℂ) • dRep π (b i) w)
    {v : H} (hv : IsSmoothVec G π v) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ l : List (Fin d),
      ‖l.foldr (fun i w => dRep π (b i) w) v‖ ≤ C ^ (l.length + 1) * l.length.factorial) :
    WordBound G π v := by
  have hD1 : (1 : ℝ) ≤ D + 1 := by linarith
  refine ⟨C * (D + 1), by positivity, fun l hl => ?_⟩
  have h := mixed_bound hG hrep hb hsp D hD0 hD hexp hv C hC hbound l hl []
  simp only [List.foldr_nil, List.length_nil, Nat.zero_add] at h
  refine h.trans ?_
  have hP := prod_mnorm_nonneg l
  have hpow : D ^ l.length ≤ (D + 1) ^ (l.length + 1) :=
    (pow_le_pow_left₀ hD0 (by linarith) _).trans (pow_le_pow_right₀ hD1 (Nat.le_succ _))
  have hCk : 0 ≤ C ^ (l.length + 1) := pow_nonneg hC.le _
  have hf : (0 : ℝ) ≤ l.length.factorial := Nat.cast_nonneg _
  rw [mul_pow]
  calc C ^ (l.length + 1) * l.length.factorial * D ^ l.length * (l.map mnorm).prod
      = (C ^ (l.length + 1) * l.length.factorial * (l.map mnorm).prod) * D ^ l.length := by ring
    _ ≤ (C ^ (l.length + 1) * l.length.factorial * (l.map mnorm).prod) *
          (D + 1) ^ (l.length + 1) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg (mul_nonneg hCk hf) hP)
    _ = _ := by ring

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordExpand

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieBasisCoordinateGrowthBound =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.GlobalProofs.LinearIndependentCoefficientNormBound =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.GlobalProofs.LinearIndependentCoefficientNormBound", "h": "module\n\npublic import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum\nimport Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional\nimport Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule\n\n"}
section -- clump:auto
@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord

theorem sum_abs_coord_le_mnorm {n d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hli : LinearIndependent ℝ b) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ r : Fin d → ℝ, ∑ i, |r i| ≤ D * mnorm (∑ i, r i • b i) := by
  let L : (Fin d → ℝ) →ₗ[ℝ] (Fin n → Fin n → ℂ) :=
    { toFun := fun r a c => ∑ i, r i • b i a c
      map_add' := fun r s => by
        funext a c
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun t r => by
        funext a c
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul] }
  have hL : ∀ r a c, L r a c = (∑ i, r i • b i) a c := by
    intro r a c
    simp [L, Matrix.sum_apply, Matrix.smul_apply]
  have hker : LinearMap.ker L = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr fun r hr => ?_
    have hsum : ∑ i, r i • b i = 0 := by
      ext a c
      have h := congrFun (congrFun hr a) c
      rw [hL] at h
      simpa using h
    funext i
    exact Fintype.linearIndependent_iff.mp hli r hsum i
  obtain ⟨K, -, hK⟩ := L.exists_antilipschitzWith hker
  refine ⟨(d : ℝ) * K, by positivity, fun r => ?_⟩
  have h1 : ‖r‖ ≤ K * ‖L r‖ := by
    have h := hK.le_mul_dist r 0
    simpa [dist_zero_right] using h
  have hN : 0 ≤ GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm (∑ i, r i • b i) := by
    unfold GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h2 : ‖L r‖ ≤ GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm (∑ i, r i • b i) := by
    refine (pi_norm_le_iff_of_nonneg hN).mpr fun a => ?_
    refine (pi_norm_le_iff_of_nonneg hN).mpr fun c => ?_
    rw [hL]
    unfold GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm
    calc ‖(∑ i, r i • b i) a c‖ ≤ ∑ c', ‖(∑ i, r i • b i) a c'‖ :=
          Finset.single_le_sum (f := fun c' => ‖(∑ i, r i • b i) a c'‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ c)
      _ ≤ ∑ a', ∑ c', ‖(∑ i, r i • b i) a' c'‖ :=
          Finset.single_le_sum (f := fun a' => ∑ c', ‖(∑ i, r i • b i) a' c'‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  have h3 : ∑ i, |r i| ≤ d * ‖r‖ := by
    calc ∑ i, |r i| ≤ ∑ _i : Fin d, ‖r‖ :=
          Finset.sum_le_sum fun i _ => by
            rw [← Real.norm_eq_abs]
            exact norm_le_pi_norm r i
      _ = d * ‖r‖ := by simp
  calc ∑ i, |r i| ≤ d * ‖r‖ := h3
    _ ≤ d * (K * ‖L r‖) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
    _ ≤ d * (K * GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm (∑ i, r i • b i)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 K.coe_nonneg) (Nat.cast_nonneg _)
    _ = d * K * GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm (∑ i, r i • b i) := by ring

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.GlobalProofs.LinearIndependentCoefficientNormBound =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothVectorHermitianFormGrowth =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothVectorHermitianFormGrowth", "h": "module\n\npublic import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec\npublic import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional\npublic import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionOfSmoothVector\npublic import Mathlib.Analysis.Calculus.Deriv.Prod\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum\nimport Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule\n\n"}
section -- clump:auto
@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

theorem deriv_nonneg_of_nonneg_right {e : ℝ → ℝ} {e' : ℝ} (h : HasDerivAt e e' 0) (h0 : e 0 = 0)
    (hpos : ∀ t, 0 < t → 0 ≤ e t) : 0 ≤ e' := by
  refine ge_of_tendsto h.tendsto_slope_zero_right ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [zero_add, h0, sub_zero, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr (le_of_lt ht)) (hpos t ht)

theorem isBoundedBilinearMap_re_form {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Q : H → H → ℂ) (Mb : ℝ) (hadd : ∀ x y z, Q x (y + z) = Q x y + Q x z)
    (hsmul : ∀ (c : ℂ) x y, Q x (c • y) = c * Q x y) (hconj : ∀ x y, Q y x = star (Q x y))
    (hbd : ∀ x y, ‖Q x y‖ ≤ Mb * ‖x‖ * ‖y‖) :
    IsBoundedBilinearMap ℝ (fun p : H × H => (Q p.1 p.2).re) := by
  have hsmulR : ∀ (c : ℝ) (x y : H), Q x (c • y) = (c : ℂ) * Q x y := fun c x y => by
    rw [← hsmul, Complex.coe_smul]
  have haddL : ∀ x₁ x₂ y, Q (x₁ + x₂) y = Q x₁ y + Q x₂ y := fun x₁ x₂ y => by
    rw [hconj, hadd, star_add, ← hconj, ← hconj]
  have hsmulL : ∀ (c : ℝ) (x y : H), Q (c • x) y = (c : ℂ) * Q x y := fun c x y => by
    rw [hconj, hsmulR, star_mul', ← hconj, show star (c : ℂ) = c from Complex.conj_ofReal c]
  refine ⟨fun x₁ x₂ y => ?_, fun c x y => ?_, fun x y₁ y₂ => ?_, fun c x y => ?_, ?_⟩
  · simp only [haddL, Complex.add_re]
  · simp only [hsmulL, Complex.re_ofReal_mul, smul_eq_mul]
  · simp only [hadd, Complex.add_re]
  · simp only [hsmulR, Complex.re_ofReal_mul, smul_eq_mul]
  · refine ⟨max Mb 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x y => ?_⟩
    rw [Real.norm_eq_abs]
    calc |(Q x y).re| ≤ ‖Q x y‖ := Complex.abs_re_le_norm _
      _ ≤ Mb * ‖x‖ * ‖y‖ := hbd x y
      _ ≤ max Mb 1 * ‖x‖ * ‖y‖ := by gcongr; exact le_max_left _ _

theorem abs_two_re_form_dRep_le : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (Q : H → H → ℂ) (Mb a : ℝ) (hadd : ∀ x y z, Q x (y + z) = Q x y + Q x z) (hsmul : ∀ (c : ℂ) x y, Q x (c • y) = c * Q x y) (hconj : ∀ x y, Q y x = star (Q x y)) (hbd : ∀ x y, ‖Q x y‖ ≤ Mb * ‖x‖ * ‖y‖) (hgrow : ∀ X ∈ HCSS.lieOf G, ∀ (t : ℝ) (x : H), (Q (π (NormedSpace.exp (t • X)) x) (π (NormedSpace.exp (t • X)) x)).re ≤ Real.exp (a * |t| * mnorm X) * (Q x x).re) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) {x : H} (hx : IsSmoothVec G π x), |2 * (Q (dRep π X x) x).re| ≤ a * mnorm X * (Q x x).re := by
  intro n G H _ _ π hG hrep Q Mb a hadd hsmul hconj hbd hgrow X hX x hx
  have hB := isBoundedBilinearMap_re_form Q Mb hadd hsmul hconj hbd
  have hv : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) x) (dRep π X x) 0 :=
    (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasDerivAt_dRep_and_isSmoothVec hG hrep hx hX).1
  have hv0 : π (NormedSpace.exp ((0 : ℝ) • X)) x = x := by
    rw [zero_smul, NormedSpace.exp_zero, hrep.1]
    rfl
  set d := dRep π X x with hd
  set f : ℝ → ℝ := fun t => (Q (π (NormedSpace.exp (t • X)) x) (π (NormedSpace.exp (t • X)) x)).re with hf_def
  have hf : HasDerivAt f (2 * (Q d x).re) 0 := by
    have h1 := (hB.hasFDerivAt (π (NormedSpace.exp ((0 : ℝ) • X)) x, π (NormedSpace.exp ((0 : ℝ) • X)) x)).comp_hasDerivAt
      (0 : ℝ) (hv.prodMk hv)
    rw [hB.deriv_apply] at h1
    simp only [hv0] at h1
    have e : (Q x d).re + (Q d x).re = 2 * (Q d x).re := by
      rw [hconj d x, Complex.star_def, Complex.conj_re]
      ring
    rw [e] at h1
    exact h1
  have hf0 : f 0 = (Q x x).re := by
    simp only [hf_def, hv0]
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (a * t * mnorm X) * (Q x x).re) (a * mnorm X * (Q x x).re) 0 := by
    have h2 : HasDerivAt (fun t : ℝ => a * t * mnorm X) (a * 1 * mnorm X) 0 :=
      ((hasDerivAt_id (0 : ℝ)).const_mul a).mul_const (mnorm X)
    have h3 := (h2.exp).mul_const (Q x x).re
    simpa using h3
  have up : 2 * (Q d x).re ≤ a * mnorm X * (Q x x).re := by
    have := deriv_nonneg_of_nonneg_right (hexp.sub hf) (by simp [hf0]) (fun t ht => by
      have := hgrow X hX t x
      rw [abs_of_pos ht] at this
      simp only [hf_def, Pi.sub_apply]
      linarith)
    linarith
  have hfn : HasDerivAt (fun t : ℝ => f (-t)) (2 * (Q d x).re * -1) 0 := by
    have hf' : HasDerivAt f (2 * (Q d x).re) (-(0 : ℝ)) := by rwa [neg_zero]
    exact hf'.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have low : -(a * mnorm X * (Q x x).re) ≤ 2 * (Q d x).re := by
    have := deriv_nonneg_of_nonneg_right (hexp.sub hfn) (by simp [hf0]) (fun t ht => by
      have := hgrow X hX (-t) x
      rw [abs_neg, abs_of_pos ht] at this
      simp only [hf_def, Pi.sub_apply]
      linarith)
    linarith
  rw [abs_le]
  exact ⟨low, up⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothVectorHermitianFormGrowth =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.GlobalProofs.WordBoundOfDelta =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.GlobalProofs.WordBoundOfDelta", "h": "module\n\npublic import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec\npublic import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional\npublic import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionAdditive\npublic import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionCommutator\npublic import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionOfSmoothVector\npublic import Mathlib.Analysis.Real.Sqrt\npublic import Mathlib.Basic.Complex.Basic\npublic import Mathlib.LinearAlgebra.FiniteDimensional.Defs\npublic import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianFormLieWordGrowth\npublic import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieBasisCoordinateGrowthBound\npublic import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LinearIndependentCoefficientNormBound\npublic import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothVectorHermitianFormGrowth\npublic import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothVectorsInvariantSubspace\nimport Development.AutomorphicSpectrum.PublishedTheorems.Jets₂.IsPermissibleOfCentre\nimport Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieAlgebraOfLinearGroupClosed\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum\nimport Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordDelta

theorem dRep_real_smul {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (r : ℝ) :
    dRep π (r • X) v = (r : ℂ) • dRep π X v := by
  have hrX : r • X ∈ HCSS.lieOf G := (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.lieOf_isLieSubalgebra hG).2.1 r X hX
  have h1 := (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasDerivAt_dRep_and_isSmoothVec hG hrep hv hX).1
  have h2 := (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasDerivAt_dRep_and_isSmoothVec hG hrep hv hrX).1
  have h3 : HasDerivAt (fun t : ℝ => r * t) r 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul r
  have h4 : HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((r * t) • X)) v) (r • dRep π X v) 0 := by
    have h1' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) (r * 0) := by
      simpa using h1
    exact HasDerivAt.scomp (0 : ℝ) h1' h3
  have h5 : (fun t : ℝ => π (NormedSpace.exp (t • (r • X))) v) = fun t : ℝ => π (NormedSpace.exp ((r * t) • X)) v := by
    funext t
    rw [smul_smul, mul_comm]
  rw [h5] at h2
  rw [h2.unique h4]
  exact (Complex.coe_smul r _).symm

theorem dRep_sum {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ HCSS.lieOf G) (r : Fin d → ℝ) {w : H} (hw : IsSmoothVec G π w) :
    dRep π (∑ i, r i • b i) w = ∑ i, (r i : ℂ) • dRep π (b i) w := by
  have hl := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.lieOf_isLieSubalgebra hG
  have key : ∀ s : Finset (Fin d), (∑ i ∈ s, r i • b i ∈ HCSS.lieOf G) ∧
      dRep π (∑ i ∈ s, r i • b i) w = ∑ i ∈ s, (r i : ℂ) • dRep π (b i) w := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨?_, ?_⟩
      · intro t
        simpa using hG.one_mem
      · simp [dRep]
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      have hri := hl.2.1 (r i) _ (hb i)
      refine ⟨hl.1 _ _ hri ih.1, ?_⟩
      rw [(_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin.dRep_linear hG hrep hw hw hri ih.1).1, ih.2, dRep_real_smul hG hrep hw (hb i)]
  exact (key Finset.univ).2

theorem word_bound_of_delta : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hc : ∀ v, ContinuousOn (fun g => π g v) G) (hQ : AlmostIsom G π) {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ HCSS.lieOf G) (hli : LinearIndependent ℝ b) (hsp : ∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i) (Y : Submodule ℂ H) [FiniteDimensional ℂ Y] (hYs : ∀ y ∈ Y, IsSmoothVec G π y) (hYd : ∀ y ∈ Y, ∑ i, dRep π (b i) (dRep π (b i) y) ∈ Y), ∀ v ∈ Y, WordBound G π v := by
  intro n G H _ _ _ π hG hrep _ hQ d b hb hli hsp Y _ hYs hYd v hv
  obtain ⟨Q, m, Mb, a, hm, hMb, ha, hadd, hsmul, hconj, hpos, hbd, hgrow⟩ := hQ
  obtain ⟨hsadd, hssmul, -⟩ := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.smooth_closed hG hrep
  have hvs := hYs v hv
  let S : Submodule ℂ H :=
    { carrier := {x | IsSmoothVec G π x}
      add_mem' := fun {x y} hx hy => hsadd x y hx hy
      zero_mem' := by simpa using hssmul 0 v hvs
      smul_mem' := fun c x hx => hssmul c x hx }
  let Xf : Fin d → Module.End ℂ S := fun i =>
    { toFun := fun x => ⟨dRep π (b i) x, (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasDerivAt_dRep_and_isSmoothVec hG hrep x.2 (hb i)).2⟩
      map_add' := fun x y => Subtype.ext (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin.dRep_linear hG hrep x.2 y.2 (hb i) (hb i)).2.1
      map_smul' := fun c x => Subtype.ext ((_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin.dRep_linear hG hrep x.2 x.2 (hb i) (hb i)).2.2 c) }
  have hXc : ∀ i (x : S), ((Xf i x : S) : H) = dRep π (b i) x := fun _ _ => rfl
  have hlie := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.lieOf_isLieSubalgebra hG
  choose r hr using fun (p : Fin d × Fin d) => hsp _ (hlie.2.2.1 (b p.1) (b p.2) (hb p.1) (hb p.2))
  have hcomm : ∀ i j, Xf i * Xf j - Xf j * Xf i = ∑ l, ((r (i, j) l : ℝ) : ℂ) • Xf l := by
    intro i j
    ext u
    have h1 := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Bracket.smooth_bracket hG hrep u.2 (hb i) (hb j)
    rw [show b i * b j - b j * b i = _ from hr (i, j), dRep_sum hG hrep b hb _ u.2] at h1
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, hXc]
    exact h1.symm
  have hQnn : ∀ x : H, 0 ≤ (Q x x).re := fun x =>
    le_trans (by positivity) (hpos x)
  let A : ℝ := a * ∑ i, mnorm (b i)
  have hmn : ∀ X : Matrix (Fin n) (Fin n) ℂ, 0 ≤ mnorm X := fun X =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hA : 0 ≤ A := mul_nonneg ha (Finset.sum_nonneg fun i _ => hmn _)
  have hs : ∀ i (x : S), |2 * (Q (Xf i x) x).re| ≤ A * (Q x x).re := by
    intro i x
    refine (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.abs_two_re_form_dRep_le hG hrep Q Mb a hadd hsmul hconj hbd hgrow (hb i) x.2).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (hQnn x)
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun i => mnorm (b i)) (fun i _ => hmn _) (Finset.mem_univ i)) ha
  let V : Submodule ℂ S := Y.comap S.subtype
  have hinj : Function.Injective (fun u : V => (⟨(u : S), u.2⟩ : Y)) := by
    intro u w h
    exact Subtype.ext (Subtype.ext (congrArg (fun y : Y => (y : H)) h))
  let f : V →ₗ[ℂ] Y :=
    { toFun := fun u => ⟨(u : S), u.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI : FiniteDimensional ℂ V := FiniteDimensional.of_injective f hinj
  have hV : ∀ u ∈ V, (∑ i, Xf i * Xf i) u ∈ V := by
    intro u hu
    have h1 := hYd (u : H) hu
    change (((∑ i, Xf i * Xf i) u : S) : H) ∈ Y
    simpa only [LinearMap.sum_apply, Module.End.mul_apply, Submodule.coe_sum, hXc] using h1
  obtain ⟨C, hC, hN⟩ := _root_.GlobalTheory.CompanionTheory.HCForm.nelson_form (fun x y : S => Q x y)
    (fun x y z => hadd x y z) (fun c x y => hsmul c x y) (fun x y => hconj x y)
    (fun x hx => lt_of_lt_of_le (by
      have : (x : H) ≠ 0 := fun h => hx (Subtype.ext h)
      positivity) (hpos x))
    Xf (fun i j l => ((r (i, j) l : ℝ) : ℂ)) hcomm A hA hs V hV
  have hword : ∀ (l : List (Fin d)) (u : S),
      (((l.map Xf).prod u : S) : H) = l.foldr (fun i w => dRep π (b i) w) (u : H) := by
    intro l u
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, hXc, List.foldr_cons, ih]
  let vS : S := ⟨v, hvs⟩
  have hvV : vS ∈ V := hv
  let K : ℝ := Real.sqrt (Q v v).re / Real.sqrt m
  have hK : 0 ≤ K := by positivity
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  refine _root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordExpand.wordBound_of_basis hG hrep b hb hsp _ (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord.sum_abs_coord_le_mnorm b hli).choose_spec.1 (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord.sum_abs_coord_le_mnorm b hli).choose_spec.2
    (fun r w hw => dRep_sum hG hrep b hb r hw) hvs (C * (K + 1)) (by positivity) ?_
  intro l
  have h1 := hN l vS hvV
  rw [show ((l.map Xf).prod vS : S) = ((l.map Xf).prod vS : S) from rfl] at h1
  set w : S := (l.map Xf).prod vS with hw
  have hwv : (w : H) = l.foldr (fun i w => dRep π (b i) w) v := hword l vS
  rw [← hwv]
  have h2 : Real.sqrt m * ‖(w : H)‖ ≤ Real.sqrt (Q w w).re := by
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, Real.sq_sqrt hm.le]
    exact hpos w
  have h3 : ‖(w : H)‖ ≤ C ^ (l.length + 1) * l.length.factorial * K := by
    have h4 : Real.sqrt m * ‖(w : H)‖ ≤ C ^ (l.length + 1) * l.length.factorial * Real.sqrt (Q v v).re := h2.trans h1
    have h5 : C ^ (l.length + 1) * l.length.factorial * K = (C ^ (l.length + 1) * l.length.factorial * Real.sqrt (Q v v).re) / Real.sqrt m := by
      simp only [K]; ring
    rw [h5, le_div_iff₀ hsm]
    linarith
  refine h3.trans ?_
  have h6 : K ≤ (K + 1) ^ (l.length + 1) := by
    have h7 : (K + 1) ^ 1 ≤ (K + 1) ^ (l.length + 1) := pow_le_pow_right₀ (by linarith) (by omega)
    linarith
  rw [mul_pow]
  have h8 : 0 ≤ C ^ (l.length + 1) * (l.length.factorial : ℝ) := by positivity
  calc C ^ (l.length + 1) * l.length.factorial * K ≤ C ^ (l.length + 1) * l.length.factorial * (K + 1) ^ (l.length + 1) :=
        mul_le_mul_of_nonneg_left h6 h8
    _ = C ^ (l.length + 1) * (K + 1) ^ (l.length + 1) * l.length.factorial := by ring

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordDelta

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.GlobalProofs.WordBoundOfDelta =====
