module

public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrdMulInertiaDegEqFinrankMulOrd
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


theorem _root_.GlobalTheory.T.finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord' : ∀ (A B : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B], Function.Injective (algebraMap A B) → ringKrullDim A = 1 → ∀ a : A, a ≠ 0 → ∑ᶠ Q ∈ {Q : PrimeSpectrum B | Q.asIdeal.comap (algebraMap A B) = IsLocalRing.maximalIdeal A}, ((Ring.ord (Localization.AtPrime Q.asIdeal) (algebraMap B _ (algebraMap A B a))).toNat : ℤ) * (Q.asIdeal.inertiaDeg A : ℤ) = (Module.finrank A B : ℤ) * ((Ring.ord A a).toNat : ℤ) := by
  first | exact @GlobalTheory.finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord | exact GlobalTheory.finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord | (intros; apply GlobalTheory.finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord <;> assumption)
