module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FibreRankCompOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveRankAtStalkOfConstFibreDim
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective

@[expose] public section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.projective_rankAtStalk_of_const_fibreDim : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] (n : ℕ), (∀ q : PrimeSpectrum O, fibreDim M q = n) → Module.Projective O M ∧ ∀ q : PrimeSpectrum O, Module.rankAtStalk M q = n := by
  first | exact @GlobalTheory.ConstFibreFree.projective_and_rankAtStalk_of_fibreDim | exact GlobalTheory.ConstFibreFree.projective_and_rankAtStalk_of_fibreDim | (intros; apply GlobalTheory.ConstFibreFree.projective_and_rankAtStalk_of_fibreDim <;> assumption)
