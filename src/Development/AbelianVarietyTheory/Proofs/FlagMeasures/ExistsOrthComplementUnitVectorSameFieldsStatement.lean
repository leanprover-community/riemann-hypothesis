module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthComplementUnitVectorSameFields
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

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_orthComplement_unitVector_same_fields : ∀ (I I' : AutInst) (e : I'.E ≃+* I.E) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf), IsPerpInst I I' e s x A xf → ∃ (D : Sib I) (B : Matrix (Fin I.n) (Fin D.n) I.E), IsPerp D s x B xf ∧ ∀ (c : InfinitePlace I.F → ℝ) (μ : Measure D.inst.Gf) [SigmaFinite μ] [μ.IsHaarMeasure] (c' : InfinitePlace I'.F → ℝ) (μ' : Measure I'.Gf) [SigmaFinite μ'] [μ'.IsHaarMeasure], IsGaugeAll D.inst c → IsGaugeAll I' c' → gaugeVol D.inst c μ = gaugeVol I' c' μ' := by
  first | exact @GlobalTheory.PerpReduce.exists_sib | exact GlobalTheory.PerpReduce.exists_sib | (intros; apply GlobalTheory.PerpReduce.exists_sib <;> assumption)
