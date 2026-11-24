module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelBasisDeterminantAbsAtPlace
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions

theorem _root_.GlobalTheory.T.kernelBasis_determinant_abs_at_place : ∀ (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (O : GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) (T : GL3Columns.KFTie E O w), T.detB := by
  first | exact @GlobalTheory.SatakeUnitDeterminantBasis.detB | exact GlobalTheory.SatakeUnitDeterminantBasis.detB | (intros; apply GlobalTheory.SatakeUnitDeterminantBasis.detB <;> assumption)
