module

public import Mathlib.FieldTheory.Perfect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPerfectPartAlgHomFiniteAlgebra
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
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsCounitDerivationCounitComp
import Mathlib.CategoryTheory.Preadditive.EndoFunctor
import Mathlib.RingTheory.Bialgebra.Basic

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.exists_perfectPart_algHom_finiteAlgebra : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A], ∃ π : A →ₐ[k] A, ((∀ a : A, IsNilpotent (a - π a)) ∧ ∀ a : A, ∃ b : A, π a = π b ^ p) := by
  first | exact @GlobalTheory.exists_perfectPart_algHom | exact GlobalTheory.exists_perfectPart_algHom | (intros; apply GlobalTheory.exists_perfectPart_algHom <;> assumption)
