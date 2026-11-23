module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagSingleSingle
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.Foundations.ValuedAlgebraMapEqOne

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.Mem.Col2
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Col2.PinsCoord

theorem extTo_basis {E : Type} [Field E] (n N : ℕ) (a : Fin n) (b : Fin N) (h : (a:ℕ) = b) : DiagSp.extTo (E := E) n N (Pi.basisFun E (Fin n) a) = Pi.basisFun E (Fin N) b := by
  funext i
  simp only [Pi.basisFun_apply]
  show (if h : (i:ℕ) < n then (Pi.single a (1:E) : Fin n → E) ⟨i, h⟩ else 0) = _
  by_cases e : i = b
  · subst e
    have : (i:ℕ) < n := h ▸ a.2
    rw [dite_eq_left this, show (⟨i, this⟩ : Fin n) = a from Fin.ext h.symm]; simp
  · rw [Pi.single_eq_of_ne e]
    split_ifs with h1
    · exact Pi.single_eq_of_ne (fun e' => e (Fin.ext (by rw [← h, ← e']))) _
    · rfl

end GlobalTheory.Mem.Col2.PinsCoord
