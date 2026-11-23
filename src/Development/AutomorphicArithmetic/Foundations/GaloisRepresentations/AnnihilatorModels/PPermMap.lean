module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.permMap_of :
    PermOfMap := by
  classical
  intro I I' P _ _ f g h
  have hc : ∀ p : P, Fintype.card {i // f i = p} = Fintype.card {j // g j = p} := by
    intro p
    have hp := congrArg (Multiset.count p) h
    simp only [Multiset.count_map] at hp
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa [Finset.card_def, Finset.filter_val, eq_comm] using hp
  let e : ∀ p, {i // f i = p} ≃ {j // g j = p} := fun p => Fintype.equivOfCardEq (hc p)
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv g)), ?_⟩
  intro i
  show f i = g ((e (f i)) ⟨i, rfl⟩).1
  exact ((e (f i)) ⟨i, rfl⟩).2.symm
