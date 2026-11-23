module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingOperatorsPolynomialEvalPderiv
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem _root_.GlobalTheory.T.commutingOperatorsPolynomialEval_pderiv : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [DecidableEq ι] (m d : ι → Module.End ℂ V)
    (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V), (∀ i j, d i * m j - m j * d i = if i = j then 1 else 0) →
    (∀ i, d i f₀ = 0) → ∀ (i : ι) (p : MvPolynomial ι ℂ),
      GlobalTheory.CCRFock.polEval m hm f₀ (MvPolynomial.pderiv i p) = d i (GlobalTheory.CCRFock.polEval m hm f₀ p) := by
  first | exact @GlobalTheory.CCRFock.polEval_pderiv | exact GlobalTheory.CCRFock.polEval_pderiv | (intros; apply GlobalTheory.CCRFock.polEval_pderiv <;> assumption)
