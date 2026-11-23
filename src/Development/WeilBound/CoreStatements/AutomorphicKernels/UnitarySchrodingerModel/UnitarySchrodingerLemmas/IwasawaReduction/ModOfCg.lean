module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsAUNeZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureConjugationStatement
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.IwaRedHand

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

theorem mod_of_cg : ∀ (D : D7) (n : ℕ) (lam : Measure (PositivityTheory.GramSchwartzFunctions.BC.hermA D n)), lam.IsAddHaarMeasure → ∀ (a : GL (Fin n) (AE D)) (f : Mx D n n → ℂ), ∫ b, f b.1 ∂lam = ((GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ n * ∫ c, f (a.1 * c.1 * GlobalTheory.MixModel.adj a.1) ∂lam := by
  intro D n lam hlam a f
  have h := GlobalTheory.T.hermitian_measure_conjugation D n lam hlam a (fun c => f c.1)
  have hr0 : 0 < absA D (Matrix.GeneralLinearGroup.det a) :=
    pos_iff_ne_zero.2 (GlobalTheory.ResAniso.ResProp.absAU_ne_zero _)
  have e : ∫ c, f (a.1 * c.1 * adj a.1) ∂lam =
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(n : ℂ)) * ∫ b, f b.1 ∂lam := h
  have key : ((absA D (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ n *
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(n : ℂ)) = 1 := by
    have hne : ((absA D (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hr0.ne'
    unfold npow
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hne]
    simp
  rw [e, ← mul_assoc, key, one_mul]

end GlobalTheory.CompanionTheory.IwaRedHand
