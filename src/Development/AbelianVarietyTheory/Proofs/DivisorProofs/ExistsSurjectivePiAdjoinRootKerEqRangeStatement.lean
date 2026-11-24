module

public import Mathlib.RingTheory.AdjoinRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjectivePiAdjoinRootKerEqRange
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

open Polynomial

theorem _root_.GlobalTheory.T.exists_surjective_pi_adjoinRoot_ker_eq_range' : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V) (f : F[X]) [Fact (Irreducible f)], ∃ (t : ℕ) (π : V →ₗ[F] (Fin t → AdjoinRoot f)), Function.Surjective π ∧ (∀ v, π (g v) = AdjoinRoot.root f • π v) ∧ LinearMap.ker π = LinearMap.range (aeval g f) ∧ Module.finrank F (LinearMap.ker (aeval g f)) = f.natDegree * t := by
  first | exact @GlobalTheory.exists_surjective_pi_adjoinRoot_ker_eq_range | exact GlobalTheory.exists_surjective_pi_adjoinRoot_ker_eq_range | (intros; apply GlobalTheory.exists_surjective_pi_adjoinRoot_ker_eq_range <;> assumption)
