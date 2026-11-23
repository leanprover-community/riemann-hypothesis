module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeRealLieHom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc

@[expose] public section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.right_derivative_real_lie_hom : ∀ (n : ℕ), (∀ X Y : Mat n, GlobalTheory.CompanionTheory.ModelS.DR (X + Y) = GlobalTheory.CompanionTheory.ModelS.DR X + GlobalTheory.CompanionTheory.ModelS.DR Y) ∧ (∀ (r : ℝ) (X : Mat n), GlobalTheory.CompanionTheory.ModelS.DR ((r : ℂ) • X) = (r : ℂ) • GlobalTheory.CompanionTheory.ModelS.DR X) ∧ (∀ X Y : Mat n, GlobalTheory.CompanionTheory.ModelS.DR (X * Y - Y * X) = GlobalTheory.CompanionTheory.ModelS.DR X * GlobalTheory.CompanionTheory.ModelS.DR Y - GlobalTheory.CompanionTheory.ModelS.DR Y * GlobalTheory.CompanionTheory.ModelS.DR X) := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.LieAct.DR_lie | exact GlobalTheory.CompanionTheory.ModelS.LieAct.DR_lie | (intros; apply GlobalTheory.CompanionTheory.ModelS.LieAct.DR_lie <;> assumption)
