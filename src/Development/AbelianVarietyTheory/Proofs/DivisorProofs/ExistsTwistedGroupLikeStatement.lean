module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Bialgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedGroupLike
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_twisted_groupLike' : ∀ (K H : Type) [Field K] [IsAlgClosed K] [CommRing H] [Bialgebra K H] [Coalgebra.IsCocomm K H] [Module.Finite K H] (c : H ⊗[K] H), IsUnit c → c ⊗ₜ[K] (1 : H) * Algebra.TensorProduct.map (Bialgebra.comulAlgHom K H) (AlgHom.id K H) c = (Algebra.TensorProduct.assoc K K K H H H).symm ((1 : H) ⊗ₜ[K] c * Algebra.TensorProduct.map (AlgHom.id K H) (Bialgebra.comulAlgHom K H) c) → Algebra.TensorProduct.comm K H H c = c → ∃ u : H, u ≠ 0 ∧ c * Coalgebra.comul (R := K) u = u ⊗ₜ[K] u := by
  first | exact @GlobalTheory.exists_twisted_groupLike | exact GlobalTheory.exists_twisted_groupLike | (intros; apply GlobalTheory.exists_twisted_groupLike <;> assumption)
