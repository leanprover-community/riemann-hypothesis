module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryFlowCoeffEqOfTaylorSeries
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.RealPlaceAnalysis.StatementA
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

theorem _root_.GlobalTheory.T.unitaryFlow_coeff_eq_of_taylor_series : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (U : ℝ → (H →L[ℂ] H)) (x : ℕ → H) (y : H) (φ φ₀ : ℝ → ℂ), U 0 = 1 → (∀ s t, U (s + t) = U s * U t) → (∀ t v, ‖U t v‖ = ‖v‖) → (∀ m, HasDerivAt (fun t => U t (x m)) (x (m + 1)) 0) → AnalyticOnNhd ℝ φ Set.univ → AnalyticAt ℝ φ₀ 0 → (∀ m, iteratedDeriv m φ 0 = ⟪y, x m⟫_ℂ) → (∀ m, iteratedDeriv m φ₀ 0 = ⟪x 0, x m⟫_ℂ) → ∀ t, φ t = ⟪y, U t (x 0)⟫_ℂ := by
  first | exact @GlobalTheory.SphJet.unitaryFlow_coeff_eq_of_taylor | exact GlobalTheory.SphJet.unitaryFlow_coeff_eq_of_taylor | (intros; apply GlobalTheory.SphJet.unitaryFlow_coeff_eq_of_taylor <;> assumption)
