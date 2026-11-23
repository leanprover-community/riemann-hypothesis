module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HolomorphicLeftInvariantDerivativeCalculusNearOn
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

theorem _root_.GlobalTheory.T.holomorphicLeftInvariantDerivative_calculus_near_one : ∀ (n : ℕ) (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (f : Matrix (Fin n) (Fin n) ℂ → B), AnalyticAt ℂ f 1 → (∀ Z, AnalyticAt ℂ (Rz Z f) 1) ∧ (∀ A Z, (fun z => Rz A (Rz Z f) z - Rz Z (Rz A f) z) =ᶠ[𝓝 1] Rz (A * Z - Z * A) f) ∧ ∀ Y Z : Matrix (Fin n) (Fin n) ℂ, (fun z => fderiv ℂ (Rz Z f) z (Y * z)) =ᶠ[𝓝 1] Rz Z (fun z => fderiv ℂ f z (Y * z)) := by
  first | exact @GlobalTheory.SphJetCalc.leftInvariant_calculus | exact GlobalTheory.SphJetCalc.leftInvariant_calculus | (intros; apply GlobalTheory.SphJetCalc.leftInvariant_calculus <;> assumption)
