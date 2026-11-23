module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctorialityOfPeriodRingMaps
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.functoriality_of_period_ring_maps : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (B : PAlg l) (f : A ⟶ B), (∀ a, mapAcr f 1 (A.aTo1 a) = B.aTo1 (Hom.f f a)) ∧ (∀ c : ℕ →₀ A.A, mapAcr f 1 (A.expand c) = B.expand (c.mapRange (Hom.f f) (map_zero _))) ∧ (∀ a, mapU f (A.sharp a) = B.sharp (Hom.f f a)) ∧ (∀ a, mapUn f 1 (A.aToU1 a) = B.aToU1 (Hom.f f a)) ∧ (∀ n x, Ideal.Quotient.mk (B.Fil n 1) (mapAcr f n (A.toAcr n x)) = B.uToQ n (mapU f (A.th x))) ∧ ∀ x : Ainf l, algebraMap (Ainf l) (A.Acr 1) x = A.aTo1 (A.s (x.coeff 0)) := by
  first | exact @GlobalTheory.CompanionTheory.PAlgNat.expand_nat | exact GlobalTheory.CompanionTheory.PAlgNat.expand_nat | (intros; apply GlobalTheory.CompanionTheory.PAlgNat.expand_nat <;> assumption)
