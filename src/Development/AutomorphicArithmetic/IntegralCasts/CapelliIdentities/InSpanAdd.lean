module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
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

theorem UpperTheory.Reformulated.B.Qj25.inSpan_add :
    ∀ {R : Formalism.BasicNotions.Ranks} {H : Formalism.BasicNotions.Host R} {what₂ : Formalism.BasicNotions.Rows.Data R}
    (N : Formalism.BasicNotions.NData R H what₂) {i : N.Loc} {X' : Type} (T' : Subalgebra (N.O i) (X' → N.O i))
    (rep : X' → Formalism.MainNotions.N.GE N →* Formalism.MainNotions.N.MatN N i) {a b : X' → Formalism.MainNotions.N.MatN N i},
    Formalism.MainNotions.N.InSpan N i T' rep a →
      Formalism.MainNotions.N.InSpan N i T' rep b →
        Formalism.MainNotions.N.InSpan N i T' rep
          (a +
            b) := by
  intro R H what₂ N i X' T' rep a b ha hb
  obtain ⟨m, f, g, hf, rfl⟩ := ha
  obtain ⟨n, f', g', hf', rfl⟩ := hb
  refine ⟨m + n, Fin.append f f', Fin.append g g', fun k => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · rw [Fin.append_left]; exact hf j
    · rw [Fin.append_right]; exact hf' j
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
