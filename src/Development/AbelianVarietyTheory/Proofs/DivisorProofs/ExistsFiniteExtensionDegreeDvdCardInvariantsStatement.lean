module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Invariant.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionDegreeDvdCardInvariants
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


theorem _root_.GlobalTheory.T.exists_finite_extension_degree_dvd_card_invariants : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (G : Type) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G], Function.Injective (algebraMap A B) → ∀ (k : Type) [Field k] [CharZero k] (ev : A →+* k), ∃ (K' : Type) (_ : Field K') (_ : Algebra k K') (β : B →+* K'), FiniteDimensional k K' ∧ Module.finrank k K' ∣ Nat.card G ∧ β.comp (algebraMap A B) = (algebraMap k K').comp ev := by
  first | exact @GlobalTheory.InvariantSpecialisation.exists_finite_extension_finrank_dvd | exact GlobalTheory.InvariantSpecialisation.exists_finite_extension_finrank_dvd | (intros; apply GlobalTheory.InvariantSpecialisation.exists_finite_extension_finrank_dvd <;> assumption)
