module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapRWordsOfParts
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

namespace ExponentialSymbolLetters

variable {k r : ℕ} (τ : B.Mat k r → ℂ) (u s : ℂ)

def phi (t : Polynomial ℂ × List (B.Mat k r)) : ℂ := t.1.eval u * s ^ t.2.length * (t.2.map τ).prod

theorem head (p : Polynomial ℂ) (l : List (Polynomial ℂ × List (B.Mat k r))) :
    ((l.map fun t => (p * t.1, t.2)).map (phi τ u s)).sum = p.eval u * (l.map (phi τ u s)).sum := by
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply, phi, Polynomial.eval_mul]
  ring

theorem letter (d : ℂ) (X : B.Mat k r) (l : List (Polynomial ℂ × List (B.Mat k r))) :
    ((l.map fun t => (Polynomial.C d * t.1, X :: t.2)).map (phi τ u s)).sum =
      (d * s * τ X) * (l.map (phi τ u s)).sum := by
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply, phi, Polynomial.eval_mul, Polynomial.eval_C, List.length_cons, pow_succ,
    List.map_cons, List.prod_cons]
  ring

theorem letters (L : List (ℂ × B.Mat k r)) (l : List (Polynomial ℂ × List (B.Mat k r))) :
    ((L.flatMap fun dX => l.map fun t => (Polynomial.C dX.1 * t.1, dX.2 :: t.2)).map (phi τ u s)).sum =
      s * (L.map fun dX => dX.1 * τ dX.2).sum * (l.map (phi τ u s)).sum := by
  induction L with
  | nil => simp
  | cons dX L ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, letter, ih, List.map_cons, List.sum_cons]
    ring

theorem all (gs : List (GenW k r)) : ((fexp gs).map (phi τ u s)).sum =
    (gs.map fun gn => gn.1.eval u + s * (gn.2.map fun dX => dX.1 * τ dX.2).sum).prod := by
  induction gs with
  | nil => simp [fexp, phi]
  | cons gn gs ih =>
    rw [fexp, List.map_append, List.sum_append, head, letters, List.map_cons, List.prod_cons, ← ih]
    ring

end ExponentialSymbolLetters

theorem exponential_symbol_holds : FExpSymb := by
  intro k r gens τ u s
  exact ExponentialSymbolLetters.all τ u s gens

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
