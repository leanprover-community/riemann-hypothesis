module

public import Mathlib.RingTheory.Perfection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectionExistsUniqueSubMatrixFrobeniusEq
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


theorem _root_.GlobalTheory.T.perfection_existsUnique_sub_matrix_frobenius_eq : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p] (ι : Type) [Fintype ι] (Q : Matrix ι ι (Perfection S p)), (∀ n : ℕ, ∃ K : ℕ, ∀ z : ι → S, (fun w : ι → S => (Q.map (Perfection.coeff S p n)).mulVec fun k => frobenius S p (w k))^[K] z = 0) → ∀ c : ι → Perfection S p, ∃! x : ι → Perfection S p, x - Q.mulVec (fun k => frobenius (Perfection S p) p (x k)) = c := by
  first | exact @GlobalTheory.perfection_frobenius_solve | exact GlobalTheory.perfection_frobenius_solve | (intros; apply GlobalTheory.perfection_frobenius_solve <;> assumption)
