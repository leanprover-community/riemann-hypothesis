module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT.FiberTwo

theorem eq_or_eq_of_under_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (w u u' : Pl E) (hu : u ≠ w)
    (h : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)))
    (h' : u'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) : u' = w ∨ u' = u := by
  have hr := Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E
  have hc := IsCMField.complexConj_ne_one (K := E)
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E) hr hc w u).1 h with h1 | h1
  · exact absurd h1 hu
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E) hr hc w u').1 h' with h2 | h2
  · exact Or.inl h2
  · exact Or.inr ((GlobalTheory.Mem.Chr.existsUnique_conjPl _ w).unique h2 h1)

end GlobalTheory.BCT.FiberTwo
