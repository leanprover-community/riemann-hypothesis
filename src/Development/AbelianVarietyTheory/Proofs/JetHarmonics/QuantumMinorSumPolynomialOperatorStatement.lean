module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatOpA
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorSumPolynomialOperator
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.quantumMinor_sum_polynomialOperator : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r m κ : ℕ) (ι : Type) [Fintype ι] (a b : ι → Fin m → Fin (2 * r + k + 1)) (u : ℂ) (co : ι → B.Mat k r → ℂ), (∀ i, U.IsPolyDeg κ (co i)) → ∃ Θ : B.DiffOp k r Wp Wq, Formalism.FourierDecayAlt.P.CutMP.PolyOp m κ Θ ∧ ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), ∀ g ∈ B.GV k r, ∀ V : Set (B.Mat k r), IsOpen V → g ∈ V → B.CkOn ⊤ (B.GV k r ∩ V) F → B.opApply Θ F g = ∑ i, co i g • qminorOp (EabH (Hpk k r)) (a i) (b i) u F g := by
  first | exact @GlobalTheory.HatNF.MinorPoly.minor_polyOp | exact GlobalTheory.HatNF.MinorPoly.minor_polyOp | (intros; apply GlobalTheory.HatNF.MinorPoly.minor_polyOp <;> assumption)
