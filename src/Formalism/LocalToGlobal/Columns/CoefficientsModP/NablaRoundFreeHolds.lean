module

public import Formalism.GradedWeylDivisibility.StatementA
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions


variable {K : Type} [Field K] [NumberField K] {n : ℕ}


section Tensor

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem rd_rowAct_one (f : MvPolynomial (Fin n × Fin n) K) :
    Formalism.GradedWeylDivisibility.rowAct K (1 : Matrix (Fin n) (Fin n) K) f = f := by
  have h : Formalism.GradedWeylDivisibility.rowAct K (n := n) (1 : Matrix (Fin n) (Fin n) K) = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [Formalism.GradedWeylDivisibility.rowAct, aeval_X, Matrix.one_apply, AlgHom.id_apply]
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [h]; rfl

end Tensor

end Formalism.L2.DIV
