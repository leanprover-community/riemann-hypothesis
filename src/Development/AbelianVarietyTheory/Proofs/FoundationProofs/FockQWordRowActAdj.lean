module

public import Formalism.GradedWeylDivisibility.StatementE
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalB
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowDivAdj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory.FockAdj

theorem fockQ_applyWord : Formalism.GradedWeylDivisibility.FockQWordAdj := by
  intro r n w
  induction w with
  | nil => intro F G; rfl
  | cons x w ih =>
    intro F G
    have h1 : applyWord ℚ (x :: w) F = rowDiv ℚ x.1 x.2.1 x.2.2 (applyWord ℚ w F) := rfl
    have h2 : applyWord ℚ (transposeWord (x :: w)) G =
        applyWord ℚ (transposeWord w) (rowDiv ℚ x.2.1 x.1 x.2.2 G) := by
      simp [applyWord, transposeWord, List.foldr_append]
    rw [h1, h2, fockQRowDivAdj, ih]

theorem map_rowAct {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℚ) (f : MvPolynomial (Fin r × Fin n) ℚ) :
    map (Rat.castHom ℂ) (rowAct ℚ g f) =
      rowAct ℂ (g.map (Rat.castHom ℂ)) (map (Rat.castHom ℂ) f) := by
  have : (map (Rat.castHom ℂ)).comp (rowAct ℚ (n := n) g).toRingHom =
      (rowAct ℂ (n := n) (g.map (Rat.castHom ℂ))).toRingHom.comp (map (Rat.castHom ℂ)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rowAct]
    · intro v
      simp [rowAct]
  exact congrArg (fun φ => φ f) this

theorem fockQ_rowAct : Formalism.GradedWeylDivisibility.FockQRowAct := by
  intro r n g P Q
  have ht : (g.map (Rat.castHom ℂ)).conjTranspose = g.transpose.map (Rat.castHom ℂ) := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have h : ((fockQ (rowAct ℚ g P) Q : ℚ) : ℂ) = ((fockQ P (rowAct ℚ g.transpose Q) : ℚ) : ℂ) := by
    rw [lfockq_cast, lfockq_cast, map_rowAct, map_rowAct, fockRowAdj, ht]
  exact_mod_cast h

theorem fockQ_word_rowAct_adj : Formalism.GradedWeylDivisibility.FockQWordAdj ∧ Formalism.GradedWeylDivisibility.FockQRowAct :=
  ⟨fockQ_applyWord, fockQ_rowAct⟩

end GlobalTheory.FockAdj
