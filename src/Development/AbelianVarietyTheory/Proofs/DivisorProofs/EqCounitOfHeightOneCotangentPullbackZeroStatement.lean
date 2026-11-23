module

public import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqCounitOfHeightOneCotangentPullbackZero
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
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.eq_counit_of_heightOne_cotangentPullback_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (D : Type) [CommRing D] [HopfAlgebra k D] [IsCocomm k D] [Module.Finite k D] (f : D →ₐc[k] C), (∀ a ∈ augIdeal k C, a ^ p = 0) → cotMap f = 0 → ∀ d, f d = algebraMap k C (counit (R := k) d) := by
  first | exact @GlobalTheory.HeightOneHom.eq_algebraMap_counit_of_cotMap_eq_zero | exact GlobalTheory.HeightOneHom.eq_algebraMap_counit_of_cotMap_eq_zero | (intros; apply GlobalTheory.HeightOneHom.eq_algebraMap_counit_of_cotMap_eq_zero <;> assumption)
