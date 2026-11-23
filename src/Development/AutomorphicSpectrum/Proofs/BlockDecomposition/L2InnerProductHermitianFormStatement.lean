module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2InnerProductHermitianForm
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

theorem _root_.GlobalTheory.T.l2_inner_product_hermitian_form : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ] [κ.IsOpenPosMeasure], (∀ x y : GlobalTheory.CompanionTheory.ModelS.SmF n, conj (GlobalTheory.CompanionTheory.ModelS.ipK κ y x) = GlobalTheory.CompanionTheory.ModelS.ipK κ x y) ∧ (∀ x : GlobalTheory.CompanionTheory.ModelS.SmF n, 0 ≤ (GlobalTheory.CompanionTheory.ModelS.ipK κ x x).re) ∧ (∀ x y z : GlobalTheory.CompanionTheory.ModelS.SmF n, GlobalTheory.CompanionTheory.ModelS.ipK κ (x + y) z = GlobalTheory.CompanionTheory.ModelS.ipK κ x z + GlobalTheory.CompanionTheory.ModelS.ipK κ y z) ∧ (∀ (c : ℂ) (x y : GlobalTheory.CompanionTheory.ModelS.SmF n), GlobalTheory.CompanionTheory.ModelS.ipK κ (c • x) y = conj c * GlobalTheory.CompanionTheory.ModelS.ipK κ x y) ∧ ∀ x : GlobalTheory.CompanionTheory.ModelS.SmF n, GlobalTheory.CompanionTheory.ModelS.ipK κ x x = 0 → ∀ k : Matrix.unitaryGroup (Fin n) ℂ, x.1 k.1 = 0 :=
  @GlobalTheory.CompanionTheory.ModelS.L2InnerProduct.ipK_form
