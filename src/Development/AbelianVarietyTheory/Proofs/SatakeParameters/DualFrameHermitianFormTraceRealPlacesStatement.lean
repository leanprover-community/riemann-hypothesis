module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColR
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementKer
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualFrameHermitianFormTraceRealPlaces
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

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

theorem _root_.GlobalTheory.T.dualFrame_hermitian_form_trace_real_places : ∀ (D : D7) (X : Fields) (s : Seam D X) (L : PeriodPair) (Λ : AddSubgroup ℂ), L.lattice.toAddSubgroup = Λ → Function.Bijective (tauPl D) → ∀ (N N' : ℕ) (A B : Matrix (Fin N') (Fin N) D.host.E) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), ι (Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area Λ)⁻¹) (GlobalTheory.DFrame.vecF D s A) (GlobalTheory.DFrame.vecF D s B)) = ∑ z : Bool × HH D, GlobalTheory.DFrame.rho D ι z (∑ i, ∑ k, A i k * D.host.conj (B i k)) := by
  first | exact @GlobalTheory.DFrame.hOK_vecF | exact GlobalTheory.DFrame.hOK_vecF | (intros; apply GlobalTheory.DFrame.hOK_vecF <;> assumption)
