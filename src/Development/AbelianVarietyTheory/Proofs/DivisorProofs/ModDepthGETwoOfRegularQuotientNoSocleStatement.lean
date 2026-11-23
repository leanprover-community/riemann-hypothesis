module

public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGETwoOfRegularQuotientNoSocle
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

open IsLocalRing TensorProduct Pointwise

theorem _root_.GlobalTheory.T.modDepthGE_two_of_regular_quotient_no_socle : ∀ (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] (M : Type) [AddCommGroup M] [Module S M] [Module.Finite S M] [Nontrivial M] (x : S), x ∈ maximalIdeal S → IsSMulRegular M x → (∀ u : M, (∀ a ∈ maximalIdeal S, a • u ∈ x • (⊤ : Submodule S M)) → u ∈ x • (⊤ : Submodule S M)) → ReciprocityTheory.CA.ModDepthGE S M 2 := by
  first | exact @GlobalTheory.modDepthGE_two_of_isSMulRegular_of_quotSMulTop | exact GlobalTheory.modDepthGE_two_of_isSMulRegular_of_quotSMulTop | (intros; apply GlobalTheory.modDepthGE_two_of_isSMulRegular_of_quotSMulTop <;> assumption)
