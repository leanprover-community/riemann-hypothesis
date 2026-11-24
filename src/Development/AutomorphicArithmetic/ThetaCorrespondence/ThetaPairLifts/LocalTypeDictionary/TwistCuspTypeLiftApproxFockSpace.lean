module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.End
public import Mathlib.Analysis.Normed.Group.Defs
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultTApplyRapidDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjThetaKOMulIntegrableOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaKernelGrowth
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelModerateGrowthBothVariables
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspFormApproxWeighted
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Mathlib.Tactic.Polynomial.Basic

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalTypePreserved, Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalFunctionBound, Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistUpperArrowApprox, Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalNonvanishing, Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistUpperCuspLiftApproxCusp, Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspTypeLiftApproxFockSpace

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalTypePreserved =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalTypePreserved", "h": "module\n\npublic import Mathlib.Algebra.BigOperators.Fin\npublic import Mathlib.Algebra.Group.End\npublic import Mathlib.Analysis.Normed.Group.Defs\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel\nimport Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CuspTypeApproxUp

theorem norm_sub_sum_sigma_lt {E : Type*} [SeminormedAddCommGroup E] {m : ℕ} (I : E) (L : Fin m → E) (n : Fin m → ℕ)
    (J : ∀ k, Fin (n k) → E) {δ : ℝ} (hδ : 0 < δ) (h1 : ‖I - ∑ k, L k‖ < δ / 2)
    (h2 : ∀ k, ‖L k - ∑ j, J k j‖ < δ / (2 * (m + 1))) :
    ‖I - ∑ l : Fin (∑ k, n k), J (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2‖ < δ := by
  have hs : ∑ l : Fin (∑ k, n k), J (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2 = ∑ k, ∑ j, J k j := by
    rw [Equiv.sum_comp finSigmaFinEquiv.symm (fun x => J x.1 x.2), Fintype.sum_sigma]
  have hd : I - ∑ k, ∑ j, J k j = (I - ∑ k, L k) + ∑ k, (L k - ∑ j, J k j) := by
    rw [Finset.sum_sub_distrib]; abel
  rw [hs, hd]
  have h3 : ‖∑ k, (L k - ∑ j, J k j)‖ ≤ m * (δ / (2 * (m + 1))) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖L k - ∑ j, J k j‖ ≤ ∑ _k : Fin m, δ / (2 * (m + 1)) := Finset.sum_le_sum fun k _ => (h2 k).le
      _ = m * (δ / (2 * (m + 1))) := by simp
  have h4 : (m : ℝ) * (δ / (2 * (m + 1))) ≤ δ / 2 := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc ‖(I - ∑ k, L k) + ∑ k, (L k - ∑ j, J k j)‖ ≤ ‖I - ∑ k, L k‖ + ‖∑ k, (L k - ∑ j, J k j)‖ := norm_add_le _ _
    _ < δ / 2 + δ / 2 := by linarith
    _ = δ := by ring

end GlobalTheory.CuspTypeApproxUp
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalTypePreserved =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalFunctionBound =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalFunctionBound", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel\nimport Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped ComplexConjugate

namespace GlobalTheory.UpArrowApprox

theorem ptF_eq_fock {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : GlobalTheory.Grid.Node D)
    (f : WO S.V T.V → ℂ) (p : GlobalTheory.Grid.Pol S T) :
    GlobalTheory.ChainFr.ptF ψ θ (GlobalTheory.PairLift.frSgn true (GlobalTheory.ChainFr.Fr.ofModel S.M)) (GlobalTheory.ChainFr.Fr.ofModel T.M) f p =
      GlobalTheory.Grid.fock ψ θ true S T f p := by
  have : (GlobalTheory.PairLift.frSgn true (GlobalTheory.ChainFr.Fr.ofModel S.M)).cart = GlobalTheory.Grid.cartS true S :=
    funext fun τ => GlobalTheory.PairLift.cart_frSgn true _ τ
  unfold GlobalTheory.ChainFr.ptF GlobalTheory.Grid.fock
  rw [this]
  rfl

theorem isFinVec_of_isVacF {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : GlobalTheory.Grid.Node D}
    {f : WO S.V T.V → ℂ}
    (h : GlobalTheory.ChainFr.IsVacF ψ θ (GlobalTheory.PairLift.frSgn true (GlobalTheory.ChainFr.Fr.ofModel S.M)) (GlobalTheory.ChainFr.Fr.ofModel T.M) f) :
    GlobalTheory.Grid.IsFinVec ψ θ true S T f :=
  ⟨h.1, fun τ => by have := h.2 τ; rwa [GlobalTheory.PairLift.cart_frSgn] at this⟩

end GlobalTheory.UpArrowApprox

namespace GlobalTheory.UpArrowApprox

end GlobalTheory.UpArrowApprox
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalFunctionBound =====

-- ===== clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistUpperArrowApprox =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistUpperArrowApprox", "h": "module\n\npublic import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible\npublic import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows\npublic import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultTApplyRapidDec\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjThetaKOMulIntegrableOn\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalFunctionBound\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaKernelGrowth\nimport Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel\nimport Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt\n\n"}
section -- clump:auto
@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped ComplexConjugate
namespace GlobalTheory.UpArrowApprox
end GlobalTheory.UpArrowApprox
namespace GlobalTheory.UpArrowApprox
theorem upperArrow_approx : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ F : (G.P i).Maps, F ∈ (G.P i).Cusp R.θ → ∀ v : SmT (G.P i).M, (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F v g) (G.mP i).fd (G.mP i).ν) → ∀ C : Set (GA D (G.P (i + 1)).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (f : Fin n → (WO (G.P (i + 1)).V (G.P i).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i)), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l)) ∧ ∀ h ∈ C, ‖(∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F v g ∂(G.mP i).ν) - ∑ l, ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l))) * F v g ∂(G.mP i).ν‖ < ε := by
  intro hLC hP D hSz G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ F hF v hint C hC ε hε
  have hθ : IsInfFam R.θ := hR.inf
  have hω := (hG.arrows.dn i hi).weil
  have hψ : IsStdChar D R.ψ (-1) := IsWeilDatumO.std hω
  have hm := (hG.meas.P i hi.le).2 (by omega)
  have hCA := hLC D hSz G₀ Pl0 T A Ks R G hR hG
  obtain ⟨-, -, hFr⟩ := GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP.cuspRapidDecay D _ _ _ R.θ hθ _ _ F hF v
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V
  obtain ⟨U, hU, hΦU, hdense⟩ := GlobalTheory.FockDensity.fockDense D _ _
    (GlobalTheory.PairLift.frSgn true (GlobalTheory.ChainFr.Fr.ofModel (G.P (i + 1)).M)) (GlobalTheory.ChainFr.Fr.ofModel (G.P i).M) R.θ R.ψ hψ hθ
    μ 𝓕 hμ Φ hΦ
  obtain ⟨a, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (GlobalTheory.Grid.neg (G.P (i + 1)).V).rank (G.P i).V.rank
  obtain ⟨K, hK0, hK⟩ := (H (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V rfl rfl).real R.ψ hθ hU
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ h ∈ C,
      GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) ((GlobalTheory.Grid.ofSgn true (G.P (i + 1)).V).symm h) ≤ M := by
    obtain ⟨M, hM⟩ := hC.bddAbove_image
      ((GlobalTheory.Grow.continuous_height _).comp (GlobalTheory.Grid.continuous_ofSgn_symm true _)).continuousOn
    exact ⟨M, fun h hh => hM ⟨h, hh, rfl⟩⟩
  obtain ⟨B, hB⟩ := hFr.decay a
  have hfin : (G.mP i).ν (G.mP i).fd < ⊤ := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hm.1.1 hm.2
  set L : ℝ := K * max M 1 ^ a * 2 ^ a * max B 0 * ((G.mP i).ν (G.mP i).fd).toReal with hL
  have hL0 : 0 ≤ L := by
    have : 0 ≤ max M 1 := le_trans zero_le_one (le_max_right _ _)
    have : 0 ≤ max B 0 := le_max_right _ _
    positivity
  have hδ : 0 < ε / (2 * (L + 1)) := div_pos hε (by linarith)
  obtain ⟨g₀, hg₀, hg₀U, hg₀d⟩ := hdense d (ENNReal.ofReal (ε / (2 * (L + 1)))) (ENNReal.ofReal_pos.2 hδ)
  obtain ⟨n, c, w, hw⟩ := Submodule.mem_span_set'.1 hg₀
  choose f₀ P hvac hlev hgeq using fun l => (w l).2
  refine ⟨n, f₀, fun l => c l • P l, fun l => isFinVec_of_isVacF (hvac l), fun h hh => ?_⟩
  have hsum : g₀ = ∑ l, GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f₀ l) (c l • P l) := by
    rw [← hw]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hgeq l, ← ptF_eq_fock]
    simp only [GlobalTheory.ChainFr.ptF, map_smul]
  have he : Φ - g₀ ∈ GlobalTheory.Size.thetaLevel R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V U := sub_mem hΦU hg₀U
  have hint' : ∀ l, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f₀ l) (c l • P l))) * F v g) (G.mP i).fd (G.mP i).ν :=
    fun l => ((hCA.up i hi (f₀ l) (isFinVec_of_isVacF (hvac l)) F hF).choose_spec.2 (c l • P l) v h).1
  have hlin : ∀ g, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F v g -
      ∑ l, starRingEnd ℂ (thetaKO (G.dn i).ω h g
        (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f₀ l) (c l • P l))) * F v g =
      starRingEnd ℂ (thetaKO (G.dn i).ω h g (Φ - g₀)) * F v g := by
    intro g
    rw [hsum]

    simp only [thetaKO, map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, sub_mul, Finset.sum_mul]
  rw [← integral_finsetSum _ fun l _ => hint' l, ← integral_sub (hint h) (integrable_finsetSum _ fun l _ => hint' l)]
  have e0 : (∫ g in (G.mP i).fd, (starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F v g -
      ∑ l, starRingEnd ℂ (thetaKO (G.dn i).ω h g
        (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f₀ l) (c l • P l))) * F v g) ∂(G.mP i).ν) =
      ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g (Φ - g₀)) * F v g ∂(G.mP i).ν := by
    congr 1
    funext g
    exact hlin g
  rw [e0]
  set s : ℝ := (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d (Φ - g₀)).toReal with hs
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  set h' := (GlobalTheory.Grid.ofSgn true (G.P (i + 1)).V).symm h with hh'
  have hpt : ∀ g, ‖starRingEnd ℂ (thetaKO (G.dn i).ω h g (Φ - g₀)) * F v g‖ ≤ K * max M 1 ^ a * 2 ^ a * max B 0 * s := by
    intro g
    have e1 : thetaKO (G.dn i).ω h g (Φ - g₀) = thetaKO ((G.dn i).ω.toSgn true) h' g (Φ - g₀) :=
      GlobalTheory.UpArrowConv.thetaKO_toSgn _ _ _ _
    have hbd : ∀ g, ‖thetaKO ((G.dn i).ω.toSgn true) h' g (Φ - g₀)‖ ≤
        (K * s * GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) h' ^ a) * GlobalTheory.Grow.height (G.P i).V g ^ a := fun g => by
      have := (hK _ _ _ hω μ 𝓕 hμ _ he).2 h' g
      rw [mul_pow, ← mul_assoc] at this
      exact this
    have hq := GlobalTheory.Grow.norm_le_quotHeight_pow (f := fun g => thetaKO ((G.dn i).ω.toSgn true) h' g (Φ - g₀))
      (GlobalTheory.UpArrowConv.thetaKO_left_snd hω he.1 h') hbd g
    rw [norm_mul, RCLike.norm_conj, e1]
    have hh1 : GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) h' ^ a ≤ max M 1 ^ a :=
      pow_le_pow_left₀ (GlobalTheory.Grow.height_pos _ _).le ((hM h hh).trans (le_max_left _ _)) a
    have hFB : ‖F v g‖ * GlobalTheory.Grow.quotHeight (G.P i).V g ^ a ≤ max B 0 := (hB g).trans (le_max_left _ _)
    have a0 : 0 ≤ K * s * GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) h' ^ a * 2 ^ a :=
      mul_nonneg (mul_nonneg (mul_nonneg hK0 hs0) (pow_nonneg (GlobalTheory.Grow.height_pos _ _).le _)) (by positivity)
    have a1 : K * s * GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) h' ^ a * 2 ^ a ≤ K * s * max M 1 ^ a * 2 ^ a :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh1 (mul_nonneg hK0 hs0)) (by positivity)
    calc ‖thetaKO ((G.dn i).ω.toSgn true) h' g (Φ - g₀)‖ * ‖F v g‖
        ≤ K * s * GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) h' ^ a * 2 ^ a *
            GlobalTheory.Grow.quotHeight (G.P i).V g ^ a * ‖F v g‖ := mul_le_mul_of_nonneg_right hq (norm_nonneg _)
      _ = K * s * GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) h' ^ a * 2 ^ a *
            (‖F v g‖ * GlobalTheory.Grow.quotHeight (G.P i).V g ^ a) := by ring
      _ ≤ K * s * max M 1 ^ a * 2 ^ a * max B 0 :=
          mul_le_mul a1 hFB (mul_nonneg (norm_nonneg _) (pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ _).le _))
            (a0.trans a1)
      _ = K * max M 1 ^ a * 2 ^ a * max B 0 * s := by ring
  refine (norm_setIntegral_le_of_norm_le_const hfin fun g _ => hpt g).trans_lt ?_
  have hslt : s < ε / (2 * (L + 1)) := ENNReal.toReal_lt_of_lt_ofReal hg₀d
  calc K * max M 1 ^ a * 2 ^ a * max B 0 * s * ((G.mP i).ν (G.mP i).fd).toReal = L * s := by rw [hL]; ring
    _ ≤ (L + 1) * s := by nlinarith
    _ < (L + 1) * (ε / (2 * (L + 1))) := mul_lt_mul_of_pos_left hslt (by linarith)
    _ = ε / 2 := by field_simp
    _ < ε := by linarith
end GlobalTheory.UpArrowApprox
end

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistUpperArrowApprox =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalNonvanishing =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalNonvanishing", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel\nimport Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped ComplexConjugate

namespace GlobalTheory.UpCuspApprox

theorem val_aut_cusp {D : D7} {θ : InfFam D} {N : GlobalTheory.Grid.Node D} {F : N.Maps} (hF : F ∈ N.Cusp θ)
    (v : SmT N.M) : IsAutFunSm θ N.V (F v) ∧ IsCuspFun N.V (F v) := by
  have hT := (GlobalTheory.MultMem.mem_mult_iff D θ N.V N.S N.M ∅ 1 _).1 ((Formalism.IndefR.Mult.mem_multT θ N.M ∅ 1 F).1 hF)
  have e : F = PiTensorProduct.lift (PiTensorProduct.lift.symm F) := (LinearEquiv.apply_symm_apply _ F).symm
  rw [e]
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [map_smul, PiTensorProduct.lift.tprod]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_smul c (hT.aut x), GlobalTheory.MultMem.isCuspFun_smul c (hT.cusp x)⟩
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add ha.1 hb.1, GlobalTheory.MultMem.isCuspFun_add ha.1.toIsAutFun hb.1.toIsAutFun ha.2 hb.2⟩

end GlobalTheory.UpCuspApprox

namespace GlobalTheory.UpCuspApprox

end GlobalTheory.UpCuspApprox
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalNonvanishing =====

-- ===== clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistUpperCuspLiftApproxCusp =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistUpperCuspLiftApproxCusp", "h": "module\n\npublic import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible\npublic import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelModerateGrowthBothVariables\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjThetaKOMulIntegrableOn\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalNonvanishing\npublic import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspFormApproxWeighted\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel\nimport Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt\n\n"}
section -- clump:auto
@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped ComplexConjugate
namespace GlobalTheory.UpCuspApprox
end GlobalTheory.UpCuspApprox
namespace GlobalTheory.UpCuspApprox
theorem upperCusp_lift_approx_cusp : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → ∀ C : Set (GA D (G.P (i + 1)).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (F : Fin n → (G.P i).Maps) (v : Fin n → SmT (G.P i).M), (∀ l, F l ∈ (G.P i).Cusp R.θ) ∧ (∀ l h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F l (v l) g) (G.mP i).fd (G.mP i).ν) ∧ ∀ h ∈ C, ‖(∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) - ∑ l, ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F l (v l) g ∂(G.mP i).ν‖ < ε := by
  intro _ hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ φ hφ hI0 C hC ε hε
  have hω := (hG.arrows.dn i hi).weil
  have hm := (hG.meas.P i hi.le).2 (by omega)
  have e : ∀ h g, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) =
      starRingEnd ℂ (thetaKO ((G.dn i).ω.toSgn true) ((GlobalTheory.Grid.ofSgn true _).symm h) g Φ) :=
    fun h g => by rw [GlobalTheory.UpArrowConv.thetaKO_toSgn]
  obtain ⟨C0, A0, hC0⟩ := GlobalTheory.Core.Rk.ThetaGrowthBoth.thetaKO_modGrowth₂ D R.ψ _ _ _ _ _ hω Φ hΦ
  obtain ⟨H, hH⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact _ (hC.image (GlobalTheory.Grid.continuous_ofSgn_symm true _))
  have hK : ∀ h ∈ C, ∀ g, ‖starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ)‖ ≤
      C0 * (max H 1) ^ A0 * 2 ^ A0 * GlobalTheory.Grow.quotHeight (G.P i).V g ^ A0 := by
    intro h hh g
    have hb : ∀ g, ‖starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ)‖ ≤ C0 * (max H 1) ^ A0 * GlobalTheory.Grow.height (G.P i).V g ^ A0 := by
      intro g
      rw [e, RCLike.norm_conj]
      refine (hC0 _ g).trans ?_
      have h1 := hH _ ⟨h, hh, rfl⟩
      have h0 := GlobalTheory.Grow.height_pos (GlobalTheory.Grid.neg (G.P (i + 1)).V) ((GlobalTheory.Grid.ofSgn true _).symm h)
      have hC00 : 0 ≤ C0 := le_trans (norm_nonneg _) ((hC0 1 1).trans (by simp))
      rw [mul_pow, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC00) (pow_nonneg (GlobalTheory.Grow.height_pos _ _).le _)
      exact pow_le_pow_left₀ h0.le (h1.trans (le_max_left _ _)) _
    exact GlobalTheory.Grow.norm_le_quotHeight_pow
      (fun γ hγ g => by rw [e, e, GlobalTheory.UpArrowConv.thetaKO_left_snd hω hΦ _ γ hγ g]) hb g
  set B := C0 * (max H 1) ^ A0 * 2 ^ A0 with hBdef
  have hfin : (G.mP i).ν (G.mP i).fd < ⊤ := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hm.1.1 hm.2
  set Vol := (G.mP i).ν.real (G.mP i).fd with hVol
  have hV0 : 0 ≤ Vol := measureReal_nonneg
  have hB1 : 0 < |B| + 1 := by positivity
  set δ := ε / (2 * ((|B| + 1) * (Vol + 1))) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨n, F, v, hF, happ⟩ := _root_.GlobalTheory.CuspApproxAll.cusp_form_approx_weighted D R.θ hR.inf hP (G.P i) φ hφ A0 δ hδ
  have hI : ∀ l h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F l (v l) g) (G.mP i).fd (G.mP i).ν := by
    intro l h
    have hv := val_aut_cusp (hF l) (v l)
    have e' : (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F l (v l) g) =
        fun g => starRingEnd ℂ (thetaKO ((G.dn i).ω.toSgn true) ((GlobalTheory.Grid.ofSgn true _).symm h) g Φ) * F l (v l) g :=
      funext fun g => by rw [e]
    rw [e']
    exact GlobalTheory.UpArrowConv.conj_thetaKO_mul_integrableOn hP.cuspRapidDecay hR.inf hω hΦ hm.1.1 hm.2 hv.1 hv.2 _
  refine ⟨n, F, v, hF, hI, fun h hh => ?_⟩
  rw [← integral_finsetSum _ (fun l _ => hI l h), ← integral_sub (hI0 h) (integrable_finsetSum _ fun l _ => hI l h)]
  have hpt : ∀ g ∈ (G.mP i).fd, ‖starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g -
      ∑ l, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F l (v l) g‖ ≤ |B| * δ := by
    intro g _
    rw [← Finset.mul_sum, ← mul_sub, norm_mul]
    have h1 := hK h hh g
    have h2 := happ g
    have hq := pow_nonneg (GlobalTheory.Grow.quotHeight_pos (G.P i).V g).le A0
    calc ‖starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ)‖ * ‖φ g - ∑ l, F l (v l) g‖
        ≤ (|B| * GlobalTheory.Grow.quotHeight (G.P i).V g ^ A0) * ‖φ g - ∑ l, F l (v l) g‖ :=
          mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self B) hq)) (norm_nonneg _)
      _ = |B| * (‖φ g - ∑ l, F l (v l) g‖ * GlobalTheory.Grow.quotHeight (G.P i).V g ^ A0) := by ring
      _ ≤ |B| * δ := mul_le_mul_of_nonneg_left h2 (abs_nonneg B)
  refine (norm_setIntegral_le_of_norm_le_const hfin hpt).trans_lt ?_
  have hε2 : |B| * δ * Vol ≤ ε / 2 := by
    rw [hδdef]
    have : |B| * Vol ≤ (|B| + 1) * (Vol + 1) := by nlinarith [abs_nonneg B]
    calc |B| * (ε / (2 * ((|B| + 1) * (Vol + 1)))) * Vol = (|B| * Vol) * (ε / (2 * ((|B| + 1) * (Vol + 1)))) := by ring
      _ ≤ ((|B| + 1) * (Vol + 1)) * (ε / (2 * ((|B| + 1) * (Vol + 1)))) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = ε / 2 := by field_simp
  linarith
end GlobalTheory.UpCuspApprox
end

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistUpperCuspLiftApproxCusp =====

-- ===== clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspTypeLiftApproxFockSpace =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspTypeLiftApproxFockSpace", "h": "module\n\npublic import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible\npublic import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalTypePreserved\npublic import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistUpperArrowApprox\npublic import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistUpperCuspLiftApproxCusp\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel\nimport Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt\n\n"}
section -- clump:auto
@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.CuspTypeApproxUp
theorem cuspType_lift_approx_fockSpace : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → ∀ C : Set (GA D (G.P (i + 1)).V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO (G.P (i + 1)).V (G.P i).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i)) (F : Fin n → (G.P i).Maps) (v : Fin n → SmT (G.P i).M), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l)) ∧ (∀ l, F l ∈ (G.P i).Cusp R.θ) ∧ ∀ h ∈ C, ‖(∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) - ∑ l, ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l))) * F l (v l) g ∂(G.mP i).ν‖ < δ := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG i hi Φ hΦ φ hφ hint C hC δ hδ
  obtain ⟨m, F, v, hF, hFi, hA⟩ := _root_.GlobalTheory.UpCuspApprox.upperCusp_lift_approx_cusp hL hP D hS G₀ Pl0 T A Ks R G hRB hG i hi Φ hΦ φ hφ hint C hC (δ / 2) (by positivity)
  have hB := fun k : Fin m => _root_.GlobalTheory.UpArrowApprox.upperArrow_approx hL hP D hS G₀ Pl0 T A Ks R G hRB hG i hi Φ hΦ (F k) (hF k) (v k) (hFi k) C hC
    (δ / (2 * (m + 1))) (by positivity)
  choose n f p hf hBk using hB
  refine ⟨∑ k, n k, fun l => f (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2,
    fun l => p (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2, fun l => F (finSigmaFinEquiv.symm l).1,
    fun l => v (finSigmaFinEquiv.symm l).1, fun l => hf _ _, fun l => hF _, fun h hh => ?_⟩
  exact norm_sub_sum_sigma_lt (J := fun k q => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f k q) (p k q))) * F k (v k) g ∂(G.mP i).ν) _ _ _ hδ
    (hA h hh) fun k => hBk k h hh
end GlobalTheory.CuspTypeApproxUp
end
end

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspTypeLiftApproxFockSpace =====
