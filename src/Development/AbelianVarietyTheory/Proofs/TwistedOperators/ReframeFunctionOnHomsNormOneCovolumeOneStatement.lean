module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReframeFunctionOnHomsNormOneCovolumeOne
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.reF_norm_one_of_norm_one_covolOne : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (f : WO S T → ℂ), AllSome (fun p : Measure (WO S T) × Set (WO S T) => IsCovolOne (ratL T S) p.1 p.2) (fun p => nrm2 p.1 p.2 f = 1) → AllSome (fun p : Measure (WO (reS S b) T) × Set (WO (reS S b) T) => IsCovolOne (ratL T (reS S b)) p.1 p.2) (fun p => nrm2 p.1 p.2 (reF S T b f) = 1) := by
  first | exact @GlobalTheory.AdSpan.ReVec.reframeFunctionOnHoms_norm_one_covolumeOne | exact GlobalTheory.AdSpan.ReVec.reframeFunctionOnHoms_norm_one_covolumeOne | (intros; apply GlobalTheory.AdSpan.ReVec.reframeFunctionOnHoms_norm_one_covolumeOne <;> assumption)
