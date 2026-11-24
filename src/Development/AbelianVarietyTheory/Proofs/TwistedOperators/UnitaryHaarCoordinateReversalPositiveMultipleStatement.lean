module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryHaarCoordinateReversalPositiveMultiple
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitary_haar_coordinate_reversal_positive_multiple : ∀ (m : ℕ) (ε : Fin m → Bool), ∃ lam : ℝ, 0 < lam ∧
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Matrix (Fin m) (Fin m) ℂ → E),
    (Integrable (fun u : Formalism.REAL.UJ ε => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) (Formalism.REAL.muG ε) ↔
      Integrable (fun h : Formalism.REAL.UJ (fun a => ε a.rev) => F (Formalism.MainNotions.S.umat h)) (Formalism.REAL.muG (fun a => ε a.rev))) ∧
    ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG ε) =
      lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG (fun a => ε a.rev)) := by
  first | exact @GlobalTheory.HaarRev.haar_rev | exact GlobalTheory.HaarRev.haar_rev | (intros; apply GlobalTheory.HaarRev.haar_rev <;> assumption)
