module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBundleIntersectionSymmetry
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

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.origin_ideal_unique_prime_over : ∀ (A S : Type) [CommRing A] [IsLocalRing A] [CommRing S] [IsLocalRing S] (f : A →+* S), f.IsIntegral →
    (Polynomial.mapRingHom f).IsIntegral ∧ (GlobalTheory.KeyOriginCut.originIdeal S).IsPrime ∧
    (GlobalTheory.KeyOriginCut.originIdeal S).comap (Polynomial.mapRingHom f) = GlobalTheory.KeyOriginCut.originIdeal A ∧
    ∀ 𝔔 : Ideal (Polynomial S), 𝔔.IsPrime → 𝔔.comap (Polynomial.mapRingHom f) = GlobalTheory.KeyOriginCut.originIdeal A → 𝔔 = GlobalTheory.KeyOriginCut.originIdeal S := by
  first | (exact @GlobalTheory.PolyOrigin.polyOrigin) | (exact GlobalTheory.PolyOrigin.polyOrigin) | (intros; apply GlobalTheory.PolyOrigin.polyOrigin  <;> assumption)
