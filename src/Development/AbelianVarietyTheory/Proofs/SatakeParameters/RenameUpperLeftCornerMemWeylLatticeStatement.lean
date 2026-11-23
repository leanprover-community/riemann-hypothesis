module

public import Formalism.GradedWeylDivisibility.StatementA
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RenameUpperLeftCornerMemWeylLattice
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


theorem _root_.GlobalTheory.T.rename_upperLeftCorner_mem_weylLattice : ∀ (R : Type) [CommRing R] (a b : ℕ) (hab : a ≤ b) (ν : Fin a → ℕ) (ν' : Fin b → ℕ), (∀ j : Fin b, ν' j = if h : (j : ℕ) < a then ν ⟨j, h⟩ else 0) → ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R a a le_rfl ν, MvPolynomial.rename (fun v : Fin a × Fin a => ((Fin.castLE hab v.1, Fin.castLE hab v.2) : Fin b × Fin b)) f ∈ Formalism.GradedWeylDivisibility.weyl R b b le_rfl ν' := by
  first | exact @GlobalTheory.weyl_rename_castLE_mem | exact GlobalTheory.weyl_rename_castLE_mem | (intros; apply GlobalTheory.weyl_rename_castLE_mem <;> assumption)
