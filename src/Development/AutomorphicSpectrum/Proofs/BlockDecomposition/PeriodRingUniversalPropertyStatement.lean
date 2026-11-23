module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.TwistAcrisZeroPreservesFiltration
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingUniversalProperty
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

theorem _root_.GlobalTheory.T.period_ring_universal_property : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) (B : Type) [CommRing B] (h : (base l).Acr n →+* B), (∀ g : A.A →+* B ⧸ ((base l).PFil n).map h, (∀ a : Ob l, g (A.s a) = Ideal.Quotient.mk _ (h ((base l).toAcr n (WittVector.teichmuller l a)))) → ∃ f : A.Acr n →+* B, f.comp (mapAcr A.fromBase n) = h ∧ ∀ a, Ideal.Quotient.mk _ (f (A.toAcr n (WittVector.teichmuller l a))) = g a) ∧ ∀ f f' : A.Acr n →+* B, f.comp (mapAcr A.fromBase n) = h → f'.comp (mapAcr A.fromBase n) = h → (∀ a, f (A.toAcr n (WittVector.teichmuller l a)) - f' (A.toAcr n (WittVector.teichmuller l a)) ∈ ((base l).PFil n).map h) → f = f' := by
  exact @GlobalTheory.CompanionTheory.AcrUniv.maps_out
