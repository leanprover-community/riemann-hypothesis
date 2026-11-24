module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionIsDomainAndIsIntegrallyClosed
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

open IsLocalRing

theorem _root_.GlobalTheory.T.adicCompletion_isDomain_and_isIntegrallyClosed : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A] [Algebra.EssFiniteType ℤ A], IsDomain (AdicCompletion (maximalIdeal A) A) ∧ IsIntegrallyClosed (AdicCompletion (maximalIdeal A) A) := by
  first | exact @GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed | exact GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed | (intros; apply GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed <;> assumption)
